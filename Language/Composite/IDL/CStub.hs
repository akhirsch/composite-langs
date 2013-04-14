{-# LANGUAGE ViewPatterns #-}
module Main where 
  import Language.Pony
  import Language.Composite.IDL  
  import qualified Language.Composite.IDL.CVect as CVect (lookup)
  import Language.Composite.IDL.StateMachines
  import qualified Prelude(foldr, foldl)
  import Data.Char (toUpper)
  import Prelude

  createSimpleStubCode :: String -> Fix Sem -> [Field] -> Maybe [Fix Sem] ->String -> [Fix Sem]
  createSimpleStubCode fnname rtype fs pres outName = 
    let
      pres' = case pres of 
        Nothing -> []
        Just xs -> xs
      assert = disallowOthers pres'
      stateMachine = concatMap (getMachine outName) pres'
      changes = concatMap stateChange pres'
      usr_inv_cap = composite' struct' (name' "user_inv_cap") nil'
      structure = variable' (pointer_to' usr_inv_cap) (name' "uc") nil'
      paramToVar = \(t,n) -> variable' t (name' n) nil'
      params = arguments' $ structure : (map paramToVar fs)
      fnname' = fnname ++ "_call"
      asmParams = name' fnname : map (\(_,n) -> name' n) fs
      asmFun = name' $ "CSTUB_ASM_" ++ (show $ (length asmParams) - 1)
      asm  = funcall' asmFun asmParams
      intZero = cint' 0
      returnType = case rtype of
        Fix VoidT -> int' signed' []
        _         -> rtype
      returnValue = variable' returnType (name' "ret") nil'
      returnInst = return' (name' "ret")
      fault = variable' (int' signed' []) (name' "fault") intZero
      instructions = stateMachine ++ assert ++ changes ++
                     [fault, returnValue, asm, returnInst]
      
    in
     [function' (name' fnname') rtype params (program' instructions)]
  
  createStubCode :: String -> Fix Sem -> [Field] -> Maybe [Fix Sem] -> String -> [Fix Sem]
  createStubCode fnname rtype fs pres outName = 
    let 
      pres' = case pres of 
        Nothing -> []
        Just xs -> xs
      assert = disallowOthers pres'
      stateMachine = concatMap (getMachine outName) pres'
      changes = concatMap stateChange pres'
      structure = variable' (pointer_to' $ composite' struct' (name' "usr_inv_cap") nil') (name' "uc") nil'
      params = arguments' $ structure : (map (\(t, n) -> variable' t (name' n) nil') fs)
      fnname' = fnname ++ "_call"
      structType = createStubStructName fnname
      intZero = cint' 0
      intRet = cint' (-6)
      (spdid, strLengs, fields) = getFields fs
      asserts = stringAsserts strLengs
      placements = placeFields fields
      instructions1 = [
        variable' (int' signed' []) (name' "fault") intZero
        , variable' rtype (name' "ret") nil'
        , variable' (pointer_to' structType) (name' "d") nil'
        , variable' (builtin' (name' "cbuf_t")) (name' "cb") nil'
        , lengthInstruction fnname strLengs
        ]
      cbPtr = unary' (name' "&") (name' "cb")
      allocCall = funcall' (name' "cbuf_alloc") [name' "sz", cbPtr]
      instructions2 = [
        binary' (name' "d") (name' "=") allocCall
        , ifthen' (unary' (name' "!") (name' "d")) (return' intRet)
        ]
      spdList = case spdid of
        Nothing  -> []
        Just spd -> [name' spd]
      asmParams = [name' fnname] ++ spdList ++ [name' "cb", name' "sz"]
      asm = funcall' (name' $ "CSTUB_ASM_" ++ (show $ (length asmParams) - 1)) asmParams
      strings = (fillLengthArray strLengs) ++ (placeStrings strLengs)
      instructions3 = [
        asm
        , funcall' (name' "cbuf_free") [name' "d"]
        , return' (name' "ret")
        ]
      instructions = stateMachine ++ assert ++ changes
                     ++ instructions1 ++ asserts ++ instructions2  
                     ++ placements ++ strings ++ instructions3
      lenLength = fromIntegral $ length strLengs + 1
      lenAry = array' (int' signed' []) (cint' lenLength)
      fields' = fields ++ [(lenAry, "len")]
      ustruct = createStubStruct fnname fields'
                
    in
     [ ustruct
     , function' (name' fnname') rtype params (program' instructions)
     ]


  lengthInstruction :: String -> [StringLength] -> Fix Sem
  lengthInstruction name [] = let ustruct = createStubStructName name
                              in
                               unary' (name' "sizeof") ustruct
  lengthInstruction name lens = let ustruct = createStubStructName name 
                                    bin l r = binary' (name' l) (name' "+") r
                                    lengths = map snd lens
                                    csize = unary' (name' "sizeof") ustruct
                                    cexpr = Prelude.foldr bin csize lengths
                                in 
                                 variable' (int' signed' []) (name' "sz") cexpr
  

  stringAsserts :: [StringLength] -> [Fix Sem]
  stringAsserts [] = []
  stringAsserts ((str, len) : xs) = 
    let intZero = cint' $ 0
        charZero = cchar' '\0'
        bool1 = binary' (name' str) (name' "&&") (binary' (name' len) (name' ">=") intZero)
        bool2 = binary' (brackets' (name' str) (name' len)) (name' "==") charZero
        f1 = funcall' (name' "assert") [bool1]
        f2 = funcall' (name' "assert") [bool2]
    in
     [f1, f2] ++ stringAsserts xs
  
  getLengthStrings :: [String] -> Fix Sem
  getLengthStrings ls = 
    let intZero = cint' 0
        dPtr = unary' (name' "&") (name' "d")
        dataZero = brackets' (name' "data") intZero
        dData = binary' dPtr (name' "->") dataZero
        f = \o l -> binary' o (name' "+") (name' l)
    in 
     foldl f dData ls
     
  placeStrings :: [StringLength] -> [Fix Sem]
  placeStrings [] = []
  placeStrings strs = let
    placeStrings' :: [StringLength] -> [String] -> [Fix Sem]
    placeStrings' [] _ = []
    placeStrings' ((s,l) : xs) ls = 
      let dData = getLengthStrings ls
          memcpyParams = [dData, name' s, name' l]
          memcpyCall = funcall' (name' "memcpy") memcpyParams
      in
       memcpyCall : (placeStrings' xs (ls ++ [l])) 
    in
     placeStrings' strs []

  placeFields :: [Field] -> [Fix Sem]
  placeFields [] = []
  placeFields ((_, name) : xs) = 
    let d = name' "d"
        newName = name' name
        dName = binary' d (name' "->") newName
        assgn = binary' dName (name' "=") newName
    in 
     assgn : placeFields xs

  fillLengthArray :: [StringLength] -> [Fix Sem]
  fillLengthArray strs = let
    d = name' "d"
    lenAry = binary' d (name' "->") (name' "len")
    fillLenAry [] n = [binary' (brackets' lenAry (cint' n)) (name' "=") (cint' 0)]
    fillLenAry ((_, len) : xs) n = (binary' (brackets' lenAry (cint' n)) (name' "=") (name' len)) : fillLenAry xs (n + 1)
    in 
     fillLenAry strs 0

  prototypeToCStub :: String -> Fix Sem -> Fix Sem -> [Fix Sem]
  prototypeToCStub n t p = let params = getFieldsFromParameters p
                           in
                            if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                            then createStubCode n t params Nothing ""
                            else createSimpleStubCode n t params Nothing ""
                              
                              
  -- Should go ahead and add correct checks
  prototypeToCStub' :: String -> Fix Sem -> Fix Sem -> [Fix Sem] -> String -> [Fix Sem]
  prototypeToCStub' n t p pres s = let params = getFieldsFromParameters p
                                 in
                                  if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                                  then createStubCode n t params (Just pres) s
                                  else createSimpleStubCode n t params (Just pres) s

  getIncludes :: Fix Sem -> [Fix Sem]
  getIncludes sem = [ include' $ "<" ++ s ++ ".h>" | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))])) <- universe sem] 
                 ++ [include' "<cstub.h>", include' "<print.h>", include' "<cvect.h>"]
  
  addChecks :: String -> [Fix Sem] -> [Fix Sem]
  addChecks s ((µ -> Pre  commands) : xs) = addChecks' commands xs
    where addChecks' c ((µ -> Function n t a (Fix (Program comm))) : ys) = 
            (function' n t a (program' $ c ++ comm)) : addChecks s ys 
          addChecks' c ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : ys) = let stub = prototypeToCStub' n t p commands s in
            stub ++ addChecks s ys
          addChecks' c ((µ -> Post _) : ys) = addChecks' c ys
          addChecks' _ _ = addChecks s xs
  addChecks s ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : xs) = (prototypeToCStub n t p) ++ (addChecks s xs)
  addChecks s (_ : xs) = addChecks s xs
  addChecks _ [] = []

  headerToCStub :: Fix Sem -> Fix Sem
  headerToCStub s@(µ -> Program commands) =
    let name = head [str | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr str))])) <- universe s] 
        includes  = getIncludes s
        stateM    = addStateMachine s
        commands' = addChecks name commands
        --prog      = map (machineInFunction name) commands'
    in
     program' $ includes ++ stateM ++ commands'
  headerToCStub x = x

  main :: IO ()
  main = run $ def {
    topDown = [headerToCStub]
    }