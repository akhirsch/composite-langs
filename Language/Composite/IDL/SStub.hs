module Main where

  import Language.Pony
  import Language.Composite.IDL
  import Language.Composite.IDL.SStubASM
  import qualified Prelude (foldl)
  import Prelude
  
  createStubCode :: String -> Fix Sem -> [Field] -> [Fix Sem]
  createStubCode fnname rtype fs = 
    let
      fnname' = "__" ++ fnname
      structType = createStubStructName fnname
      (spdid, strLengs, fields) = getFields fs
      lenLength = fromIntegral $ length strLengs
      lenAry = array' (int' signed' []) (cint' lenLength)
      fields' = fields ++ [(lenAry, "len")]
      ustruct = createStubStruct fnname fields'
      lenChecks = lengthChecks fnname strLengs
      cbid = variable' (builtin' (name' "cbuf_t")) (name' "cbid") nil'
      len = variable' (int' signed' []) (name' "len") nil'
      spdList = case spdid of
        Nothing -> []
        Just spd -> 
          [variable' (builtin' (name' "spdid_t")) (name' "spdid") nil']
      params =  arguments' $ spdList ++ [cbid, len]
      retParams = getReturnParameters fs
      retFunCall = funcall' (name' "fnname") retParams
      ret = return' retFunCall
      retError = return' $ cint' (-5)
      dataFromCbuf = funcall' (name' "cbuf2buf") [name' "cbid", name' "len"]
      instructions = [
                       variable' (pointer_to' structType) (name' "d") nil'
                     , binary' (name' "d") (name' "=") dataFromCbuf
                     , unlikely' (unary' (name' "!") (name' "d")) retError
                     ] ++ lenChecks ++ [ret]
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
      access s = binary' (name' "d") (name' "->") s
      accessLen n = access $ brackets' (name' "len") (cint' n)
      accessData n = (binary' (unary' (name' "&") (name' "d")) (name' "->") (brackets' (name' "data") (cint' n)))
      createCall n [] = []
      createCall n ((t, name) : xs) = if isCharStar t
                                      then accessData n : accessLen n : createCall (n+1) (tail xs)
                                      else access (name' name) : createCall n xs
      call = createCall 0 fs
    in
     case spdid of
       Nothing -> call
       Just spd -> (name' spd) : (tail call)
      
  lengthChecks :: String -> [StringLength] -> [Fix Sem]
  lengthChecks fnname strLens = 
    let 
      len n = binary' (name' "d") (name' "->") (brackets' (name' "len") (cint' . fromIntegral $ n))
      addN s n = binary' (len n) (name' "+") s
      unit = funcall' (name' "sizeof") $ [createStubStructName fnname]
      add = foldl addN unit [1 .. (length strLens)]
      lengthCheck = unlikely' (binary' add (name' "!=") (name' "len")) (return' (cint' $ -4))
      sanityCheck = unlikely' (binary' (len (length strLens - 1)) (name' "!=") (cint' 0)) (return' (cint' $ -2))
    in
     [sanityCheck, lengthCheck]
     
  prototypeToSStub :: Fix Sem -> Fix Sem
  prototypeToSStub sem = let
    f n t p = let params = getFieldsFromParameters p
                  function = createStubCode n t params
              in
               function
    in
     program' . concat $ [f n t params | (Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = params})) <- universe sem]
     
  prototypeToASM :: Fix Sem -> IO ()
  prototypeToASM sem = 
    writeSStub . makeSStub $ [(n, createC p, hasSpdid p) | p@(Fix (Prototype {pname = Fix (Name n), ptype = t, pargs = params})) <- universe sem]

  main :: IO ()
  main = run $ def {
      topDown = [prototypeToSStub]
    , arbitraryIO = [prototypeToASM]
    } 
