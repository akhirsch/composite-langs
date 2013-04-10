{-# LANGUAGE ViewPatterns #-}
{- Implements the transformation for the IDL. Currently, this doesn't include
 - any sort of syntactic transformations. Instead, it just describes how to
 - create a stub from a header file. -}

module Language.Composite.IDL.CStub.Calls where
  import Language.Pony
  import Language.Composite.IDL
  import qualified Language.Composite.IDL.CVect as CVect (lookup)
  import Language.Composite.IDL.StateMachines
  import qualified Prelude(foldr, foldl) 
  import Data.Char (toUpper)
  import Prelude

  createSimpleStubCode :: String -> Fix Sem -> [Field] -> [Fix Sem]
  createSimpleStubCode fnname rtype fs =
    let
        structure = variable' (pointer_to' $ composite' struct' (name' "usr_inv_cap") nil') (name' "uc") nil'
        params = arguments' $ structure : (map (\(t,n) -> variable' t (name' n) nil') fs)
        fnname' = fnname ++ "_call"
        asmParams = name' fnname : map (\(_,n) -> name' n) fs
        asm  = funcall' (name' $ "CSTUB_ASM_" ++ (show $ (length asmParams) - 1)) asmParams
        intZero = cint' 0
        returnValue = [variable' (case rtype of 
                          Fix VoidT -> int' signed' []
                          _         -> rtype) (name' "ret") nil']
        returnInst = [return' (name' "ret")]

        instructions = [variable' (int' signed' []) (name' "fault") intZero] ++ returnValue ++ [asm] ++ returnInst
    in
      [function' (name' fnname') rtype params (program' instructions)]
  
  createStubCode :: String -> Fix Sem -> [Field] -> [Fix Sem]
  createStubCode fnname rtype fs = 
    let 
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
      instructions = instructions1 ++ asserts ++ instructions2 
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
                               function = createStubCode n t params
                           in
                            if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                            then function
                            else case t of 
                              Fix VoidT -> []
                              _         -> createSimpleStubCode n t params
                              
                              
  prototypeToCStub' :: String -> Fix Sem -> Fix Sem -> [Fix Sem]
  prototypeToCStub' n t p = let params = getFieldsFromParameters p
                                function = createStubCode n t params
                            in
                             if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                             then function
                             else createSimpleStubCode n t params

  getIncludes :: Fix Sem -> [Fix Sem]
  getIncludes sem = [ include' $ "<" ++ s ++ ".h>" | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))])) <- universe sem] ++ [include' "<cstub.h>", include' "<print.h>", include' "<cvect.h>"]
  
  addChecks :: [Fix Sem] -> [Fix Sem]
  addChecks ((µ -> Pre  commands) : xs) = addChecks' commands xs
    where addChecks' c ((µ -> Function n t a (Fix (Program comm))) : ys) = 
            (function' n t a (program' $ c ++ comm)) : addChecks ys
          addChecks' c ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : ys) = let stub = prototypeToCStub' n t p in
            case stub of 
              (x : y : zs) -> x : (addChecks' c ((y : zs) ++ ys))
              (_ : _)      -> addChecks' c (stub ++ ys)
              []           -> addChecks ys
          addChecks' c ((µ -> Post _) : ys) = addChecks' c ys
          addChecks' _ _ = addChecks xs
  addChecks ((µ -> Prototype {pname = Fix (Name n), ptype = t, pargs = p}) : xs) = (prototypeToCStub n t p) ++ (addChecks xs)
  addChecks (_ : xs) = addChecks xs
  addChecks [] = []

  headerToCStub :: Fix Sem -> Fix Sem
  headerToCStub s@(µ -> Program commands) =
    let name = head [str | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr str))])) <- universe s] 
        includes  = getIncludes s
        stateM    = addStateMachine s
        commands' = addChecks commands
        prog      = map (machineInFunction name) commands'
    in
    program' $ includes ++ stateM ++ prog
  headerToCStub x = x
  
  doCalls :: IO String
  doCalls = runAndReturn $ def {
    topDown = [headerToCStub]
    }
