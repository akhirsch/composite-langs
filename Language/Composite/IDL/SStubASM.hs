module Language.Composite.IDL.SStubASM where

  import Language.Pony

  writeSStub :: String -> IO ()
  writeSStub = writeFile "s_stub.S"

  makeSStub :: [(String, Bool)] -> IO ()
  makeSStub fns = mapM_ writeSStub (map makeFnCalls fns)
  
  makeFnCalls :: (String, Bool) -> String
  makeFnCalls (str, True) = let
    macrocall = "cos_asm_server_fn_stub_spdid"
    in
     macrocall ++ "(" ++ str ++ ", __sg_" ++ str ++ ")\n"
  makeFnCalls (str, False) = let
    macrocall = "cos_asm_server_stub_spdid"
    in
     macrocall ++ "(" ++ str ++ ")\n"