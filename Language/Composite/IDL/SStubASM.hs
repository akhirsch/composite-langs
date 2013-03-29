module Language.Composite.IDL.SStubASM where

  import Language.Pony
  import System.IO

  writeSStub :: String -> IO ()
  writeSStub s = writeFile "s_stub.S" s
  
  makeSStub :: [(String, Bool, Bool)] -> String
  makeSStub fns = foldl (flip (++)) "" (map makeFnCalls fns)
  
  makeFnCalls :: (String, Bool, Bool) -> String
  makeFnCalls (str, True, True) = let
    macrocall = "cos_asm_server_fn_stub_spdid"
    in
     macrocall ++ "(" ++ str ++ ", __sg_" ++ str ++ ")\n"
  makeFnCalls (str, True, False) = let
    macrocall = "cos_asm_server_fn_stub"
    in
     macrocall ++ "(" ++ str ++ ", __sg_" ++ str ++ ")\n"
  makeFnCalls (str, False, True) = let
    macrocall = "cos_asm_server_stub_spdid"
    in
     macrocall ++ "(" ++ str ++ ")\n"
  makeFnCalls (str, False, False) = let
    macrocall = "cos_asm_server_stub"
    in
     macrocall ++ "(" ++ str ++ ")\n"
