{-#LANGUAGE ViewPatterns #-}

module Main where
  import Language.Pony
  import Language.Composite.IDL.StateMachines
  import Language.Composite.IDL
  import Language.Composite.IDL.SStubASM
  import qualified Prelude (foldl)
  import Prelude
  
  createSimpleStubCode :: String -> Fix Sem -> [Field] -> Maybe [Fix Sem] -> String -> [Fix Sem]
  createSimpleStubCode fnname (Fix VoidT) fs pres outName =
    let
      pres'   = case pres of 
        Nothing -> []
        Just xs -> xs
      assert  = disallowOthers pres'
      stateM  = concatMap (getMachine outName) pres'
      changes = concatMap stateChange pres'
      params  = arguments' $ map (\(t,n) -> variable' t (name' n) nil') fs
      fnname' = "__sg_" ++ fnname
      args    = map (\(_,n) -> name' n) fs
      call    = funcall' (name' fnname) args
      inst    = stateM ++ assert  ++ [call] ++ changes
      func    = function' (name' fnname') (Fix VoidT) params (program' inst)
    in
     [func]
  createSimpleStubCode fnname rtype fs pres outName =
    let
      pres'   = case pres of 
        Nothing -> []
        Just xs -> xs
      assert  = disallowOthers pres'
      stateM  = concatMap (getMachine outName) pres'
      changes = concatMap stateChange pres'
      params  = arguments' $ map (\(t,n) -> variable' t (name' n) nil') fs
      fnname' = "__sg_" ++ fnname
      args    = map (\(_,n) -> name' n) fs
      call    = funcall' (name' fnname) args
      retVar  = variable' rtype (name' "ret") call
      ret     = return' (name' "ret")
      inst    = stateM ++ assert  ++ [retVar] ++ changes ++ [ret]
    in
     [function' (name' fnname') rtype params (program' inst)]


  createStubCode :: String -> Fix Sem -> [Field] -> Maybe [Fix Sem] -> String -> [Fix Sem]
  createStubCode fnname rtype fs pres outName = 
    let
      pres'   = case pres of 
        Nothing -> []
        Just xs -> xs
      assert  = disallowOthers pres'
      stateM  = concatMap (getMachineSStub outName) pres'
      changes = concatMap stateChange pres'
      fnname' = "__sg_" ++ fnname
      structType = createStubStructName fnname
      (spdid, strLengs, fields) = getFields fs
      lenLength = fromIntegral $ length strLengs
      lenAry = array' (int' signed' []) (cint' lenLength)
      fields' = fields ++ [(lenAry, "len")]
      ustruct = createStubStruct fnname fields'
      lenChecks = lengthChecks fnname strLengs
      cbid = variable' (builtin' (name' "cbuf_t")) (name' "cbid") nil'
      len = variable' (int' signed' []) (name' "len") nil'
      spdList = case spdid of
        Nothing -> []
        Just spd -> 
          [variable' (builtin' (name' "spdid_t")) (name' "spdid") nil']
      params =  arguments' $ spdList ++ [cbid, len]
      retParams = getReturnParameters fs
      retFunCall = funcall' (name' fnname) retParams
      retVar = variable' rtype (name' "ret") retFunCall
      ret = return' (name' "ret")
      retError = return' $ cint' (-5)
      dataFromCbuf = funcall' (name' "cbuf2buf") [name' "cbid", name' "len"]
      instructions = [
                       variable' (pointer_to' structType) (name' "d") nil'
                     , binary' (name' "d") (name' "=") dataFromCbuf
                     , unlikely' (unary' (name' "!") (name' "d")) retError
                     ] ++ stateM ++ assert ++ lenChecks ++ [retVar] ++ changes ++ [ret]
    in
     [ ustruct
     , function' (name' fnname') rtype params (program' instructions)
     ]
     
  unlikely' :: Fix Sem -> Fix Sem -> Fix Sem
  unlikely' cond result = 
    let
      condition = funcall' (name' "unlikely") [cond]
    in 
     ifthen' condition result
     
  getReturnParameters :: [Field] -> [Fix Sem]
  getReturnParameters fs = 
    let
      (spdid, strLengs, fields) = getFields fs
      access s = binary' (name' "d") (name' "->") s
      accessLen n = access $ brackets' (name' "len") (cint' n)
      accessData n = (binary' (unary' (name' "&") (name' "d")) (name' "->") (brackets' (name' "data") (cint' n)))
      createCall n [] = []
      createCall n ((t, name) : xs) = if isCharStar t
                                      then accessData n : accessLen n : createCall (n+1) (tail xs)
                                      else access (name' name) : createCall n xs
      call = createCall 0 fs
    in
     case spdid of
       Nothing -> call
       Just spd -> (name' spd) : (tail call)
      
  lengthChecks :: String -> [StringLength] -> [Fix Sem]
  lengthChecks fnname strLens = 
    let 
      len n = binary' (name' "d") (name' "->") (brackets' (name' "len") (cint' . fromIntegral $ n))
      addN s n = binary' (len n) (name' "+") s
      unit = funcall' (name' "sizeof") $ [createStubStructName fnname]
      add = foldl addN unit [0 .. (length strLens - 1)]
      lengthCheck = unlikely' (binary' add (name' "!=") (name' "len")) (return' (cint' $ -4))
      sanityCheck = unlikely' (binary' (len (length strLens)) (name' "!=") (cint' 0)) (return' (cint' $ -2))
    in
     [sanityCheck, lengthCheck]
     
  prototypeToSStub :: String -> Fix Sem -> Fix Sem -> [Fix Sem]
  prototypeToSStub n t p = let params = getFieldsFromParameters p in 
    if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
    then createStubCode n t params Nothing ""
    else createSimpleStubCode n t params Nothing ""
      
  prototypeToSStub' :: String -> Fix Sem -> Fix Sem -> [Fix Sem] -> String -> [Fix Sem]
  prototypeToSStub' n t p pres s = 
    let params = getFieldsFromParameters p in
    if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
    then createStubCode n t params (Just pres) s
    else createSimpleStubCode n t params (Just pres) s


  getIncludes :: Fix Sem -> [Fix Sem]
  getIncludes sem = [include' $ "<" ++ s ++ ".h>" | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))])) <- universe sem]
    
  -- so that we don't end up with code after the return
  -- based on the idea that the code doesn't have a return -- should do better
  addBeforeRet :: [Fix Sem] -> [Fix Sem] -> [Fix Sem]
  addBeforeRet s (x : y : []) = x : (s ++ (y : []))
  addBeforeRet s (x : []) =   s ++ (x : [])
  addBeforeRet s (x : xs) = x : (addBeforeRet s xs)
  addBeforeRet _ ([]) = []

  addChecks :: String -> [Fix Sem] -> [Fix Sem]
  addChecks s ((µ -> Post commands) : xs) = addChecks' commands xs
    where addChecks' c ((µ -> Function n t a (Fix (Program comm))) : ys) =
            function' n t a (program' $ addBeforeRet c comm) : addChecks s ys
          addChecks' c ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : ys) = let stub = prototypeToSStub' n t p commands s in
            stub ++ addChecks s ys
          addChecks' c ((µ -> Pre commands) : ys) = addChecks' c ys
          addChecks' _ _ = addChecks s xs
  addChecks s ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : xs) = (prototypeToSStub n t p) ++ (addChecks s xs)
  addChecks s (_ : xs) = addChecks s xs
  addChecks _ [] = []

  headerToSStub :: Fix Sem -> Fix Sem
  headerToSStub s@(µ -> Program commands) = 
    let name = head [str | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr str))])) <- universe s] 
        includes  = getIncludes s
        stateM    = addStateMachine s
        commands' = addChecks name commands
        --prog      = map (machineInFunction name) commands'
    in
    program' $ includes ++ stateM ++ commands'
  headerToSStub x = x

  prototypeToASM :: Fix Sem -> IO ()
  prototypeToASM sem = 
      let
          include = "#include <cos_asm_server_stub.h>\n"
          text    = ".text\n"
      in
    writeSStub $ (++) (include ++ text) $ makeSStub $ [(n, createC p, hasSpdid p) | p@(Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = params})) <- universe sem]

  main :: IO ()
  main = run $ def {
      topDown = [headerToSStub]
    , arbitraryIO = [prototypeToASM]
    } 
