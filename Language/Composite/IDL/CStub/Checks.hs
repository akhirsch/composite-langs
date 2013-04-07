{-# LANGUAGE ViewPatterns #-}
module Language.Composite.IDL.CStub.Checks where
  import Language.Pony
  import Language.Composite.IDL
  
    
  addChecks :: [Fix Sem] -> [Fix Sem]
  addChecks ((µ -> Pre  commands) : xs) = addChecks' commands xs
    where addChecks' c ((µ -> Function n t a (Fix (Program comm))) : ys) = 
            (function' t n a (program' $ c ++ comm)) : addChecks ys
          addChecks' c ((µ -> Post _) : ys) = addChecks' c ys
          addChecks' _ _ = addChecks xs
  addChecks (x : xs) = x : (addChecks xs)
  addChecks [] = []
  
  addChecksToCStub :: Fix Sem -> Fix Sem
  addChecksToCStub (µ -> Program commands) = program' $ addChecks commands
  addChecksToCStub x = x
  
  doChecks :: IO String
  doChecks = runAndReturn $ def {
      topDown = [addChecksToCStub]
    , bitwiseOperators = ["-->"]
    }