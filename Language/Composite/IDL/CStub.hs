module Main where 
  import Language.Pony
  import Language.Composite.IDL.CStub.Calls
  import Language.Composite.IDL.CStub.Checks
  
  
  main :: IO ()
  main = run $ def {
      topDown = [prototypeToCStub, addChecksToCStub]
    , bitwiseOperators = ["-->"]
    }