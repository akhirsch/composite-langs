{-# LANGUAGE ViewPatterns #-}
module Main where 
  import Language.Pony
  import Language.Composite.IDL.CStub.Calls
  

{-  FOR TESTING PURPOSES ONLY!!
  main :: IO ()
  main = do
    let test = addChecks [Fix (Pre [Fix (FunCall (Fix (Name "test_call")) [Fix (Name "nine")]),Fix (FunCall (Fix (Name "test_call")) [Fix (CInt 10)])]),Fix (Prototype {pname = Fix (Name "test"), ptype = Fix (IntT {isign = Fix Signed, ibase = Fix Empty}), pargs = Fix (Arguments [])})]
    mapM_ (print . prettyPrint) test
-}
  main :: IO ()
  main = run $ def {
      topDown = [headerToCStub]
    , bitwiseOperators = ["-->"]
    }