{-# LANGUAGE ViewPatterns #-}

module Main where
  import Language.Pony
  import Language.Composite.IDL
  import Data.Char

  importStatement :: Fix Sem -> [Fix Sem]
  importStatement (µ -> FunCall (Fix (Name "cidl_import"))  [(Fix (CStr str))]) = [include' str]
  importStatement (µ -> FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))]) = [define' $ (map toUpper s) ++ "_H"]  
  importStatement (µ -> FunCall _ _) = []
  importStatement (µ -> Typedef {ttype=_, tname=_}) = []
  importStatement (µ -> Pre _) = []
  importStatement (µ -> Post _) = []
  importStatement x = [x] 
  

  outportStatement _ = []
  
  

  cidlToHeader :: Fix Sem -> Fix Sem
  cidlToHeader (µ -> Program  stmts) = let
                instrs = concatMap importStatement stmts
                instrs' = instrs ++ [endif']
           in
      program' instrs'
  cidlToHeader x = x
  
  main :: IO ()
  main = run $ def {
    topDown = [cidlToHeader]
    , bitwiseOperators = ["-->"]
    }