{-#LANGUAGE ViewPatterns #-}

module Main where
  import Language.Pony
  import Language.Composite.IDL.StateMachines
  import Language.Composite.IDL
  import Language.Composite.IDL.SStubASM
  import qualified Prelude (foldl)
  import Prelude
  
  createSimpleStubCode :: String -> Fix Sem -> [Field] -> [Fix Sem]
  createSimpleStubCode fnname rtype fs =
    let
      params  = arguments' $ map (\(t,n) -> variable' t (name' n) nil') fs
      fnname' = "__sg_" ++ fnname
      args    = map (\(_,n) -> name' n) fs
      call    = funcall' (name' fnname) args
      retVar  = variable' (name' "ret") rtype call
      ret     = return' (name' "ret")
    in
     [function' (name' fnname') rtype params (program' [retVar, ret])]


  createStubCode :: String -> Fix Sem -> [Field] -> [Fix Sem]
  createStubCode fnname rtype fs = 
    let
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
                     ] ++ lenChecks ++ [retVar, ret]
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
  prototypeToSStub n t p = let params = getFieldsFromParameters p
                               function = createStubCode n t params
                           in
                              if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                              then function
                              else []

  prototypeToSStub' :: String -> Fix Sem -> Fix Sem -> [Fix Sem]
  prototypeToSStub' n t p = let params = getFieldsFromParameters p
                                function = createStubCode n t params
                            in
                             if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                             then function
                             else createSimpleStubCode n t params


  getIncludes :: Fix Sem -> [Fix Sem]
  getIncludes sem = [include' $ "<" ++ s ++ ".h>" | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))])) <- universe sem]
    
  -- so that we don't end up with code after the return
  -- based on the idea that the code doesn't have a return -- should do better
  addBeforeRet :: [Fix Sem] -> [Fix Sem] -> [Fix Sem]
  addBeforeRet s (x : y : []) = x : (s ++ (y : []))
  addBeforeRet s (x : []) =   s ++ (x : [])
  addBeforeRet s (x : xs) = x : (addBeforeRet s xs)
  addBeforeRet _ ([]) = []

  addChecks :: [Fix Sem] -> [Fix Sem]
  addChecks ((µ -> Post commands) : xs) = addChecks' commands xs
    where addChecks' c ((µ -> Function n t a (Fix (Program comm))) : ys) =
            function' n t a (program' $ addBeforeRet c comm) : addChecks ys
          addChecks' c ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : ys) = let stub = prototypeToSStub' n t p in
            case stub of
              (x : y : zs) -> x : (addChecks' c ((y : zs) ++ ys))
              (y : _)      -> addChecks' c (stub ++ ys)
              []           -> addChecks xs
          addChecks' c ((µ -> Pre commands) : ys) = addChecks' c ys
          addChecks' _ _ = addChecks xs
  addChecks ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : xs) = (prototypeToSStub n t p) ++ (addChecks xs)
  addChecks (_ : xs) = addChecks xs
  addChecks [] = []

  headerToSStub :: Fix Sem -> Fix Sem
  headerToSStub s@(µ -> Program commands) = 
    let name = head [str | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr str))])) <- universe s] 
        includes  = getIncludes s
        stateM    = addStateMachine s
        commands' = addChecks commands
        prog      = map (machineInFunction name) commands'
    in
    program' $ includes ++ stateM ++ prog
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
