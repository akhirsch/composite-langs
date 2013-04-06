{-# LANGUAGE ViewPatterns #-}

module Main where
  import Language.Pony
  import Language.Composite.IDL
  
  importStatement :: Fix Sem -> [Fix Sem]
  importStatement (µ -> FunCall (Fix ( Name "cidl_import")) [(Fix (CStr str))]) = [include' str]
  importStatement (µ -> Typedef {ttype=_, tname=_}) = []
  importStatement (µ -> Pre _) = []
  importStatement (µ -> Post _) = []
  importStatement x = [x] 
  
  cidlToHeader :: Fix Sem -> Fix Sem
  cidlToHeader (µ -> Program  stmts) = let
                instrs = concatMap importStatement stmts
                instrs' = [define' "TORRENT_H"] ++ instrs ++ [endif']
           in
      program' instrs'
  cidlToHeader x = x
  
  main :: IO ()
  main = run $ def {
    topDown = [cidlToHeader]
    , bitwiseOperators = ["-->"]
    }