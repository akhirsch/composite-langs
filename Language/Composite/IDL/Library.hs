 {-# LANGUAGE ViewPatterns #-}
module Language.Composite.IDL.Library (
    Spdid
  , StringLength
  , Field
  , Fields
  , getFieldsFromParameters
  , getFields
  , createStubStruct
  , createStubStructName  
  , getStringLengths
  , isSpdid
  , getSpdid
  , getFieldList
  ) where
  import Language.Pony

  type Spdid = Maybe String
  type StringLength = (String, String)
  type Field = (Fix Sem, String)
  type Fields = (Spdid, [StringLength], [Field])

  getFieldsFromParameters :: Fix Sem -> [Field]
  getFieldsFromParameters sem = [(t, n) | (Fix (Variable t (Fix (Name n)) _)) <- universe sem]

  getFields :: [(Fix Sem, String)] -> Fields
  getFields fs =
    let spdid = getSpdid fs
        strLens = getStringLengths fs
        fieldL = getFieldList fs
    in
     (spdid, strLens, fieldL)

  createStubStruct :: String -> [Field] -> Fix Sem
  createStubStruct _ [] = composite' struct' nil' nil'
  createStubStruct fnname fields = let name = "__sg_" ++ fnname ++ "_data"
                                       fname' = name' name
                                       fn (t, n) = variable' t (name' n) nil'
                                       fields' = map fn fields
                                       ary = array' (char' nil') (cint' 0)
                                       aryField = variable' ary (name' "data") nil'
                                       fields'' = group' $ fields' ++ [aryField]
                                   in
                                    composite' struct' fname' fields''
                                        
  createStubStructName :: String -> Fix Sem
  createStubStructName fnname = let name = "__sg_" ++ fnname ++ "_data"
                                    fname' = name' name
                                in
                                 composite' struct' fname' nil'

    -- Assumes that every string has an integer following it that includes the length. 
  getStringLengths :: [Field] -> [StringLength]
  getStringLengths [] = []
  getStringLengths (((Fix (PointerToT (Fix (CharT _)))), str) : (Fix (IntT {isign = _, ibase = _}), len) : xs) = 
    (str, len) : getStringLengths xs
  getStringLengths (((Fix (PointerToT (Fix (CharT _)))),  _) : _) = error "String without length (1)"
  getStringLengths (_ : xs) = getStringLengths xs

  isSpdid :: Fix Sem -> Bool
  isSpdid (µ -> TypedefT (Fix (Name "spdid_t"))) = True
  isSpdid _ = False

  getSpdid :: [(Fix Sem, String)] ->  Spdid
  getSpdid ((Fix (TypedefT (Fix (Name "spdid_t"))), n) : _) = Just n
  getSpdid _ = Nothing
  
  getFieldList :: [Field] -> [Field]
  getFieldList [] = []
  getFieldList as@((t, _) : ts) = let
    -- Assumes that there is no spdid
    getFieldList' :: [Field] -> [Field]
    getFieldList' (((Fix (PointerToT (Fix (CharT _)))), _) : (Fix (IntT {isign = _, ibase = _}), _) : xs) =
      getFieldList' xs
    getFieldList' (x : xs) = x : getFieldList' xs
    getFieldList' [] = []
    in
     if isSpdid t
     then getFieldList' ts
     else getFieldList' as
  
  
