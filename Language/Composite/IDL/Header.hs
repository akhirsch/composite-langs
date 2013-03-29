module Main where
  import Language.Pony
  import Language.Composite.IDL
  
  importStatement (µ -> FunCall (Fix ( Name "cidl_import")) args) = include' args
  importStatment x = x 
  
  cidlToHeader :: Fix Sem -> Fix Sem
  cidlToHeader sem = program' [importStatement s | s <- universe sem]
  
  main :: IO ()
  main = run $ def {
    topDown = [cidlToHeader]
    }