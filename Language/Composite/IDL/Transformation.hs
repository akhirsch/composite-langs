{- Implements the transformation for the IDL. Currently, this doesn't include
 - any sort of syntactic transformations. Instead, it just describes how to
 - create a stub from a header file. -}

module Language.Composite.IDL.Transformation where
  import Language.Pony
  
  type Spdid = Maybe Name
  type StringLength = (Name, Name)
  type Field = (SType, String)
  
  type Fields = (Spdid, [StringLength], [Field])

  createStubStructInfo' :: Name -> [Field] -> CompositeInfo
  createStubStructInfo' _ [] = ConmpositeInfo Struct Nothing []
  createStubStructInfo' fname fields = let name = "__sg_" ++ fname ++ "_data"
                                           fname' = Just name
                                           fn t n = Field (Just n) t Nothing
                                           fields' = map fn fields
                                       in
                                        CompositeInfo Struct (Just fname') fields'
                                        
  createStubStructInfo :: Name -> CompositeInfo
  createStubStructInfo fname = let name = "__sg_" ++ fname ++ "_data"
                                   fname' = Just name
                               in
                                CompositeInfo Struct (Just fname') []

  createStubStruct :: Name -> [Field] -> GComposite
  createStubStruct = GComposite . createStubStructInfo'
  
  -- Assumes that every string has an integer following it that includes the length. 
  getStringLengths :: [(SType, String)] -> [StringLength]
  getStringLengths [] = []
  getStringLengths ((SPointerTo (SChar _), str) : (SInt _ _, len) : xs) = 
    (str, len) : getStringLengths xs
  getStringLengths ((SPointerTo (SChar _), _) : _) = error "String without length (1)"
  getStringLengths (_ : xs) = getStringLengths xs
  
  getSpdid :: [(SType, String)] ->  Spdid
  getSpdid ((SBuiltinType "spdid_t" [], name) : xs) = Just name
  getSpdid _ = Nothing
  
  getFieldList :: [(SType, String)] -> [Field]
  getFieldList [] = []
  getFieldList as@((t, _) : xs) = let
    -- Assumes that there is no spdid
    getFieldList' :: [(SType, String)] -> [Field]
    getFieldList' ((SPointerTo (SChar _), str) : (SInt _ _, len) : xs) = 
      getFieldList' xs
    getFieldList' (x : xs) = x : getFieldList' xs
    in
     if t == SBuiltinType "spdid_t"
     then getFieldList' xs
     else getFieldList' as
  
  lengthInstruction :: Name -> [StringLength] -> Local
  lengthInstruction name [] = let struct = createStubStructInfo name fields
                                  t = SComposite struct
                           in
                            (SizeofSType t)
  lengthInstruction name lens = let struct = createStubStructInfo name fields
                                    t = SComposite struct
                                    bin l r = Binary (Ident l) "+" (Ident r)
                                    lengths = map snd lens
                                    expr = foldr bin (SizeofSType t) length
                                    var = Variable "sz" unsignedInt (Just expr)
                                in 
                                 LDeclaration var
  
  createStubCode :: Name -> SType -> [(SType, String)] -> Function
  createStubCode fname rtype fields = 
    let 
      params = map (\(t, n) -> Parameter (Just n) t) fields
      fname' = fname ++ "_call"
      structType = SComposite $ createStubStructInfo fname fields
      intZero = Literal . CInteger $ 0
      asserts = stringAsserts fields
      placements = placeFields fields
      instructions1 = [
                        LDeclaration $ Variable "fault" longSignedInt (Just intZero)
                      , LDeclaration $ Variable "ret" rtype Nothing
                      , LDeclaration $ Variable "d" (SPointerTo structType) Nothing
                      , LDeclaration $ Variable "cb" (SBuiltinType "cbuf") Nothing
                      , lengthInstruction fname fields
                      ]
                      
      instructions2 = [
                      ]
      instructions = instructions1 ++ instructions2 ++ asserts ++ placements
                      
        
    in
     Function [] rtype fname' params instructions

  stringAsserts :: [StringLengths] -> [Local]
  stringAsserts [] = []
  stringAsserts ((SPointerTo (SChar _), str) : (SInt _ _, len) : xs) = 
    let intZero = Literal . CInteger $ 0
        bool1 = Binary (Ident str) "&&" (Binary (Ident len) ">=" intZero)
        bool2 = Binary (Brackets (Ident str) (Ident len)) "==" intZero
        f1 = FunctionCall (Ident "assert") [bool1]
        f2 = FunctionCall (Ident "assert") [bool2]
    in
     [f1, f2] ++ stringAsserts xs
  stringAsserts ((SPointerTo (SChar _), _) : _) = error "String without length (2)"
  stringAsserts (_ : xs) = stringAsserts xs
  
  placeFields :: Fields -> [Local]
  placeFields [] = []
  placeFields ((_, name) : xs) = 
    Binary (Binary (Ident "d") "->" (Ident name)) "=" (Ident name) : placeFields xs