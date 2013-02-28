module Main where

  import Language.Pony
  import Language.Composite.IDL.SStubASM
  
  createStubCode :: String -> Fix Sem -> [Field] -> [Fix Sem]
  createStubCode fnname rtype fs = 
    let
      fnname' = "__" ++ fnname
      structType = createStubStructName fnname
      (spdid, strLengs, fields) = getFields fs
      lenAry = array' (int' signed' []) (cint' lenLength)
      fields' = fields ++ [(lenAry, "len")]
      ustruct = createStubStruct fnname fields'
      lenChecks = lengthChecks strLengs
      cbid = variable' (builtin' (name' "cbuf_t") []) (name' "cbid")
      len = variable' (int' signed' []) (name' "len")
      spdList = case spdid of
        Nothing -> []
        Just spd -> 
          [variable' (buildin' (name' "spdid_t") []) (name' "spdid")]
      params =  spdList ++ [cbid, len]
      retParams = getReturnParameters fs
      retFunCall = funcall' (name' "fnname") retParams
      ret = return' retFunCall
      retError = return' cint' (-5)
      dataFromCbuf = funcall' (name' "cbuf2buf") [name' "cbid", name' "len"]
      instructions = [
                       variable' (pointer_to' structType) (name' "d") nil'
                     , binary' (name' "d") (name' "=") dataFromCbuf
                     , unlikely' (unary' (name' "!") (name' "d")) retError
                     ] ++ lenChecks ++ ret
    in
     [ ustruct
     , function' (name' fnname') rtype params (program' instructions)
     ]
     
  unlikely' :: Fix Sem -> Fix Sem -> Fix Sem
  unlikely' cond result = 
    let
      condition = funcall' (name' "unlikely") [cond]
    in 
     ifthen' condition result
     
  getReturnParameters :: [Field] -> [Fix Sem]
  getReturnParameters fs = 
    let
      (spdid, strLengs, fields) = getFields fs
      spdList = case spdid of
        Nothing -> []
        Just spd -> [name' spd]
      access n = binary' (name' "d") (name' "->") (name' n)
      
      