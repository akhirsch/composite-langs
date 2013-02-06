module Language.Composite.IDL.Library (
    Spdid
  , StringLength
  , CField
  , CFields
  , getCFieldsFromParameters
  , getCFields
  , createStubStruct
  , createStubStructName  
  , getStringLengths
  , isSpdid
  , getSpdid
  , getCFieldList
  ) where
  import Language.Pony

  type Spdid = Maybe Name
  type StringLength = (Name, Name)
  type CField = (SType, String)
  type CFields = (Spdid, [StringLength], [CField])

  getCFieldsFromParameters :: [Parameter] -> [(SType, String)]
  getCFieldsFromParameters [] = []
  getCFieldsFromParameters ((Parameter (Just n) t) : params) = (t, n) : getCFieldsFromParameters params  
  getCFieldsFromParameters ((Parameter Nothing t) : params) = (t, "") : getCFieldsFromParameters params

  getCFields :: [(SType, String)] -> CFields
  getCFields fs =
    let spdid = getSpdid fs
        strLens = getStringLengths fs
        fieldL = getCFieldList fs
    in
     (spdid, strLens, fieldL)

  createStubStructInfo :: Name -> [CField] -> CompositeInfo
  createStubStructInfo _ [] = CompositeInfo Struct Nothing []
  createStubStructInfo fname fields = let name = "__sg_" ++ fname ++ "_data"
                                          fname' = Just name
                                          fn (t, n) = Field (Just n) t Nothing
                                          fields' = map fn fields
                                          intZero = Literal . CInteger $ 0
                                          ary = SArray (SChar Nothing []) (Just intZero) []
                                          aryField = Field (Just "data") ary Nothing
                                          fields'' = fields' ++ [aryField]
                                      in
                                       CompositeInfo Struct fname' fields''
                                        
  createStubStructName :: Name -> CompositeInfo
  createStubStructName fname = let name = "__sg_" ++ fname ++ "_data"
                                   fname' = Just name
                               in
                                CompositeInfo Struct fname' []

  createStubStruct :: Name -> [CField] -> SGlobal
  createStubStruct n cf = GComposite $ createStubStructInfo n cf
  
    -- Assumes that every string has an integer following it that includes the length. 
  getStringLengths :: [(SType, String)] -> [StringLength]
  getStringLengths [] = []
  getStringLengths ((SPointerTo (SChar _ _) _, str) : (SInt _ _, len) : xs) = 
    (str, len) : getStringLengths xs
  getStringLengths ((SPointerTo (SChar _ _) _,  _) : _) = error "String without length (1)"
  getStringLengths (_ : xs) = getStringLengths xs

  isSpdid :: SType -> Bool
  isSpdid (STypedef "spdid_t" _ _) = True
  isSpdid _ = False

  getSpdid :: [(SType, String)] ->  Spdid
  getSpdid (((STypedef "spdid_t" _ _), name) : _) = Just name
  getSpdid _ = Nothing
  
  getCFieldList :: [(SType, String)] -> [CField]
  getCFieldList [] = []
  getCFieldList as@((t, _) : ts) = let
    -- Assumes that there is no spdid
    getCFieldList' :: [(SType, String)] -> [CField]
    getCFieldList' ((SPointerTo (SChar _ _) _, _) : (SInt _ _, _) : xs) = 
      getCFieldList' xs
    getCFieldList' (x : xs) = x : getCFieldList' xs
    getCFieldList' [] = []
    in
     if isSpdid t
     then getCFieldList' ts
     else getCFieldList' as
  
  
