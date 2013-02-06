{- Implements the transformation for the IDL. Currently, this doesn't include
 - any sort of syntactic transformations. Instead, it just describes how to
 - create a stub from a header file. -}

module Language.Composite.IDL.CStub where
  import Language.Pony
  import Language.Composite.IDL.Library
  
  lengthInstruction :: Name -> [StringLength] -> Local
  lengthInstruction name [] = let ustruct = SComposite (createStubStructName name) []
                              in
                               LStatement . ExpressionS $ (SizeOfSType ustruct)
  lengthInstruction name lens = let ustruct = createStubStructName name 
                                    t = SComposite ustruct []
                                    bin l r = Binary (Ident l) "+" r
                                    lengths = map snd lens
                                    expr = foldr bin (SizeOfSType t) lengths
                                    var = Variable "sz" unsignedInt (Just expr)
                                in 
                                 LDeclaration var
  
  createStubCode :: Name -> SType -> [(SType, String)] -> Function
  createStubCode fname rtype fs = 
    let 
      params = map (\(t, n) -> Parameter (Just n) t) fs
      fname' = fname ++ "_call"
      structType = SComposite (createStubStructName fname) []
      intZero = Literal . CInteger $ 0
      intRet = Literal . CInteger $ -6
      (spdid, strLengs, fields) = getCFields fs
      asserts = stringAsserts strLengs
      placements = placeCFields fields
      instructions1 = [
                        LDeclaration $ Variable "fault" longSignedInt (Just intZero)
                      , LDeclaration $ Variable "ret" rtype Nothing
                      , LDeclaration $ Variable "d" (SPointerTo structType []) Nothing
                      , LDeclaration $ Variable "cb" (SBuiltinType "cbuf" []) Nothing
                      , lengthInstruction fname strLengs
                      ]
      cbPtr = Unary "&" (Ident "cb")
      allocCall = FunctionCall (Ident "cbuf_alloc") [Ident "sz", cbPtr]
      instructions2 = [
                        LStatement . ExpressionS $ Binary (Ident "d") "=" allocCall
                      , LStatement $ IfThen (Unary "!" (Ident "d")) (Return $ Just intRet)
                      ]
      spdList = case spdid of
        Nothing -> []
        Just spd -> [Ident spd]
      asmParams = [Ident fname] ++ spdList ++ [Ident "cb", Ident "sz"]
      asm = FunctionCall (Ident $ "CSTUB_ASM_" ++ (show $ (length asmParams) - 1)) asmParams
      strings = placeStrings strLengs
      instructions3 = [LStatement . ExpressionS $ asm]
      instructions = instructions1 ++ asserts ++ instructions2 
                       ++ placements ++ strings ++ instructions3
                      
        
    in
     Function [] rtype fname' params instructions False

  stringAsserts :: [StringLength] -> [Local]
  stringAsserts [] = []
  stringAsserts ((str, len) : xs) = 
    let intZero = Literal . CInteger $ 0
        charZero = Ident "'\\0'"
        bool1 = Binary (Ident str) "&&" (Binary (Ident len) ">=" intZero)
        bool2 = Binary (Brackets (Ident str) (Ident len)) "==" charZero
        f = LStatement . ExpressionS
        f1 = f $ FunctionCall (Ident "assert") [bool1]
        f2 = f $ FunctionCall (Ident "assert") [bool2]
    in
     [f1, f2] ++ stringAsserts xs
  
  getLengthStrings :: [String] -> Expression
  getLengthStrings [] = 
    let intZero = Literal . CInteger $ 0
        dPtr = Unary "&" (Ident "d")
        dataZero = Brackets (Ident "data") intZero
        dData = Binary dPtr "->" dataZero
    in 
     dData
  getLengthStrings (l : ls) = 
    let others = getLengthStrings ls
    in Binary others "+" (Ident l)
     
  placeStrings :: [StringLength] -> [Local]
  placeStrings [] = []
  placeStrings strs = let
    placeStrings' :: [StringLength] -> [String] -> [Local]
    placeStrings' [] _ = []
    placeStrings' ((s,l) : xs) ls = 
      let dData = getLengthStrings ls
          memcpyParams = [dData, Ident s, Ident l]
          memcpyCall = FunctionCall (Ident "memcpy") memcpyParams
          memcpyL = LStatement . ExpressionS $ memcpyCall
      in
       memcpyL : (placeStrings' xs (ls ++ [l])) 
    in
     placeStrings' strs []

  placeCFields :: [CField] -> [Local]
  placeCFields [] = []
  placeCFields ((_, name) : xs) = 
    let d = Ident "d"
        name' = Ident name
        dName = Binary d "->" name'
        assgn = LStatement . ExpressionS $ Binary dName "=" name'
    in 
     assgn : placeCFields xs

  prototypeToCStub :: [SGlobal] -> [SGlobal]
  prototypeToCStub [] = []
  prototypeToCStub ((GFunctionPrototype t n params _) : xs) = 
    let params' = getCFieldsFromParameters params
        function = GFunction $ createStubCode n t params'
        ustruct = createStubStruct n (getCFieldList params')
    in
     [ustruct, function] ++ (prototypeToCStub xs)
  prototypeToCStub (x : xs) = x : (prototypeToCStub xs)
  
  cstubT :: GenericT
  cstubT = mkT prototypeToCStub
    
  main :: IO ()
  main = run $ pony {
    transformations = [MkTrans "cstub" TopDown cstubT]
    }