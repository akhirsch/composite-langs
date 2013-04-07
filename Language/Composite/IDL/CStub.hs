{- Implements the transformation for the IDL. Currently, this doesn't include
 - any sort of syntactic transformations. Instead, it just describes how to
 - create a stub from a header file. -}

module Main where
  import Language.Pony
  import Language.Composite.IDL
  import qualified Prelude(foldr) 
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
        return = [return' (name' "ret")]

        instructions = [variable' (int' signed' []) (name' "fault") intZero] ++ returnValue ++ [asm] ++ return
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
                                    size = unary' (name' "sizeof") ustruct
                                    expr = Prelude.foldr bin size lengths
                                in 
                                 variable' (int' signed' []) (name' "sz") expr
  

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
    fillLenAry ((str, len) : xs) n = (binary' (brackets' lenAry (cint' n)) (name' "=") (name' len)) : fillLenAry xs (n + 1)
    in 
     fillLenAry strs 0

  prototypeToCStub :: Fix Sem -> Fix Sem
  prototypeToCStub sem = let
                f n t p = let params = getFieldsFromParameters p
                              function = createStubCode n t params
                          in
                            if createC (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = p}))
                            then function
                            else case t of 
                                   Fix VoidT -> []
                                   _         -> createSimpleStubCode n t params
                includes = [[ include' $ "<" ++ s ++ ".h>" | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))])) <- universe sem] ++ [include' "<cstub.h>", include' "<print.h>"]]
    in
    program' . concat $ includes ++ [f n t params | (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = params})) <- universe sem]
    --program' . concat $ [[name' n, t, params] | (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = params})) <- universe sem]
    
  main :: IO ()
  main = run $ def {
    topDown = [prototypeToCStub]
    ,bitwiseOperators = ["-->"]
    }
