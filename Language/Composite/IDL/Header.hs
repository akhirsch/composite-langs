{-# LANGUAGE ViewPatterns #-}

module Main where
  import Language.Pony
  import Language.Composite.IDL
  
  importStatement :: Fix Sem -> [Fix Sem]
  importStatement (µ -> FunCall (Fix ( Name "cidl_import")) [(Fix (CStr str))]) = [include' str]
  importStatement (µ -> Typedef _ _) = []
  importStatement x = [x] 
  
  cidlToHeader :: Fix Sem -> Fix Sem
  cidlToHeader (µ -> Program  stmts) = program' (concatMap importStatement stmts)
  cidlToHeader x = x
  
  main :: IO ()
  main = run $ def {
    topDown = [cidlToHeader]
    }