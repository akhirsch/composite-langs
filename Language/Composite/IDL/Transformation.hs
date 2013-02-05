{- Implements the transformation for the IDL. Currently, this doesn't include
 - any sort of syntactic transformations. Instead, it just describes how to
 - create a stub from a header file. -}

module Language.Composite.IDL.Transformation where
  import Language.Pony
  import Generics.Regular.Rewriting
  import Language.Pony.Rewriting
  
  type Spdid = Maybe Name
  type StringLength = (Name, Name)
  type CField = (SType, String)
  
  type CFields = (Spdid, [StringLength], [CField])

  createStubStructInfo' :: Name -> [CField] -> CompositeInfo
  createStubStructInfo' _ [] = CompositeInfo Struct Nothing []
  createStubStructInfo' fname fields = let name = "__sg_" ++ fname ++ "_data"
                                           fname' = Just name
                                           fn (t, n) = Field (Just n) t Nothing
                                           fields' = map fn fields
                                       in
                                        CompositeInfo Struct fname' fields'
                                        
  createStubStructInfo :: Name -> CompositeInfo
  createStubStructInfo fname = let name = "__sg_" ++ fname ++ "_data"
                                   fname' = Just name
                               in
                                CompositeInfo Struct fname' []

  createStubStruct :: Name -> [CField] -> SGlobal
  createStubStruct n cf = GComposite $ createStubStructInfo' n cf
  
  -- Assumes that every string has an integer following it that includes the length. 
  getStringLengths :: [(SType, String)] -> [StringLength]
  getStringLengths [] = []
  getStringLengths ((SPointerTo (SChar _ _) _, str) : (SInt _ _, len) : xs) = 
    (str, len) : getStringLengths xs
  getStringLengths ((SPointerTo (SChar _ _) _,  _) : _) = error "String without length (1)"
  getStringLengths (_ : xs) = getStringLengths xs
  
  getSpdid :: [(SType, String)] ->  Spdid
  getSpdid ((SBuiltinType "spdid_t" [], name) : xs) = Just name
  getSpdid _ = Nothing
  
  getCFieldList :: [(SType, String)] -> [CField]
  getCFieldList [] = []
  getCFieldList as@((t, _) : xs) = let
    -- Assumes that there is no spdid
    getCFieldList' :: [(SType, String)] -> [CField]
    getCFieldList' ((SPointerTo (SChar _ _) _, str) : (SInt _ _, len) : xs) = 
      getCFieldList' xs
    getCFieldList' (x : xs) = x : getCFieldList' xs
    getCFieldList' [] = []
    in
     if t == SBuiltinType "spdid_t" []
     then getCFieldList' xs
     else getCFieldList' as
  
  
  getCFields :: [(SType, String)] -> CFields
  getCFields fs =
    let spdid = getSpdid fs
        strLens = getStringLengths fs
        fieldL = getCFieldList fs
    in
     (spdid, strLens, fieldL)
  
  lengthInstruction :: Name -> [StringLength] -> Local
  lengthInstruction name [] = let struct = SComposite (createStubStructInfo name) []
  
                           in
                            LStatement . ExpressionS $ (SizeOfSType struct)
  lengthInstruction name lens = let struct = createStubStructInfo name 
                                    t = SComposite struct []
                                    bin l r = Binary (Ident l) "+" r
                                    lengths = map snd lens
                                    expr = foldr bin (SizeOfSType t) lengths
                                    var = Variable "sz" unsignedInt (Just expr)
                                in 
                                 LDeclaration var
  
  createStubCode :: Name -> SType -> [(SType, String)] -> Function
  createStubCode fname rtype fs = 
    let 
      params = map (\(t, n) -> Parameter (Just n) t) fields
      fname' = fname ++ "_call"
      structType = SComposite (createStubStructInfo fname) []
      intZero = Literal . CInteger $ 0
      intRet = Literal . CInteger $ -6
      f@(spdid, strLengs, fields) = getCFields fs
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
      dPtr = Unary "&" (Ident "d")
      dataZero = Brackets (Ident "data") intZero
      dData = Binary dPtr "->" dataZero
      spdList = case spdid of
        Nothing -> []
        Just spd -> [Ident spd]
      asmParams = [Ident fname] ++ spdList ++ [Ident "cb", Ident "sz"]
      memcpyCall = FunctionCall (Ident "memcpy") [dData, Ident "param", Ident "len"]
      asm = FunctionCall (Ident "CSTUB_ASM_3") asmParams
      instructions3 = [
                        LStatement . ExpressionS $ memcpyCall
                      , LStatement . ExpressionS $ asm
                      ]
                      
      instructions = instructions1 ++ asserts ++ instructions2 
                       ++ placements ++ instructions3
                      
        
    in
     Function [] rtype fname' params instructions False

  stringAsserts :: [StringLength] -> [Local]
  stringAsserts [] = []
  stringAsserts ((str, len) : xs) = 
    let intZero = Literal . CInteger $ 0
        bool1 = Binary (Ident str) "&&" (Binary (Ident len) ">=" intZero)
        bool2 = Binary (Brackets (Ident str) (Ident len)) "==" intZero
        f = LStatement . ExpressionS
        f1 = f $ FunctionCall (Ident "assert") [bool1]
        f2 = f $ FunctionCall (Ident "assert") [bool2]
    in
     [f1, f2] ++ stringAsserts xs
  
  placeCFields :: [CField] -> [Local]
  placeCFields [] = []
  placeCFields ((_, name) : xs) = 
    let d = Ident "d"
        name = Ident "name"
        dName = Binary d "->" name
        assgn = LStatement . ExpressionS $ Binary dName "=" name
    in 
     assgn : placeCFields xs
    
  getCFieldsFromParameters :: [Parameter] -> [(SType, String)]
  getCFieldsFromParameters [] = []
  getCFieldsFromParameters ((Parameter (Just n) t) : params) = (t, n) : getCFieldsFromParameters params  
  getCFieldsFromParameters ((Parameter Nothing t) : params) = (t, "") : getCFieldsFromParameters params

  prototypeToFunction :: [SGlobal] -> [SGlobal]
  prototypeToFunction [] = []
  prototypeToFunction ((GFunctionPrototype t n params _) : xs) = 
    let params' = getCFieldsFromParameters params
        function = GFunction $ createStubCode n t params'
        struct = GComposite $ createStubStructInfo' n (getCFieldList params')
    in
     [struct, function] ++ (prototypeToFunction xs)
  prototypeToFunction (x : xs) = x : (prototypeToFunction xs)

  prototypeT :: GenericT
  prototypeT = mkT prototypeToFunction
  
  main :: IO ()
  main = run $ pony {
    transformations = [MkTrans "prototype" TopDown prototypeT]
    }