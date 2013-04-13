{-#LANGUAGE ViewPatterns #-}

module Language.Composite.IDL.StateMachines where
  import Language.Pony
  import Language.Composite.IDL
  import qualified Language.Composite.IDL.CVect as CVect (lookup, lookupStatic)
  import Data.Char (toUpper)

  stateChange :: Fix Sem -> [Fix Sem]
  stateChange (µ -> Binary s1 (Fix (Name "->")) s2) =
    let machineName = name' "__sg_m"
        curState    = binary' machineName (name' "->") (name' "cur")
        check       = binary' curState (name' "==") s1
        set         = binary' curState (name' "=") s2
    in
     [ifthen' check set]
  stateChange x = [x]
  
  addStateMachine :: Fix Sem -> [Fix Sem]
  addStateMachine sem = let name = head [s | (Fix (FunCall (Fix (Name "cidl_outport")) [(Fix (CStr s))])) <- universe sem]
                            states = [l | (Fix (FunCall (Fix (Name "states")) l)) <- universe sem]
                            args = map (\l -> case l of
                                           [Fix (CommaSep l')] -> l'
                                           []                  -> []
                                           _                   -> l) states
                            cvectName  = "__sg_" ++ name ++ "_sm_lookup"
                            cvect = createStatic (name' cvectName)
                            createMachine = flip createStateMachine name 
                         in
                            cvect : (concatMap createMachine args)
  
  getMachine :: String -> Fix Sem -> [Fix Sem]
  getMachine s (µ -> FunCall (Fix (Name "key")) [key@(Fix(Name _))]) = let
    machineName = name' "__sg_m"
    keyName = name' "__sg_k"
    machine = name' $ "__sg_" ++ s ++ "_sm"
    lookupMap = name' $ "__sg_" ++ s ++ "_sm_lookup"
    keyAssign = variable' (int' signed' [long']) keyName key
    machineVar = variable' (pointer_to' (builtin' machine)) machineName nil'
    findMachine = binary' machineName (name' "=") (CVect.lookupStatic lookupMap key)
     in
     [keyAssign, machineVar, findMachine]
  getMachine _ x = [x]
    
  machineInFunction :: String -> Fix Sem -> Fix Sem
  machineInFunction s (µ -> Function n t a (Fix (Program l))) = 
    let state = concatMap stateChange $ concatMap (getMachine s) l
        assert = disallowOthers l
        prog = assert ++ state
    in
    function' n t a (program' prog)
  machineInFunction _ x = x

  getStateName :: Fix Sem -> [Fix Sem]
  getStateName (µ -> Name s) = [name' $ map toUpper s]
  getStateName (µ -> FunCall _ [Fix (Name s)]) = [name' $ map toUpper s]
  getStateName _ = []

  getStart :: Fix Sem -> Fix Sem -> Fix Sem
  getStart (µ -> FunCall (Fix (Name "start")) [(Fix (Name a))]) _ = 
    name' $ map toUpper a
  getStart _ b = b
  
  getEnd :: Fix Sem -> Fix Sem -> Fix Sem
  getEnd (µ -> FunCall (Fix (Name "end")) [Fix (Name a)]) _ = 
    name' $ map toUpper a
  getEnd _ b = b

  getStateStruct :: String -> Fix Sem -> [Fix Sem]
  getStateStruct prefix (µ -> Name s) = 
    let start = variable' (int' signed' []) (name' "start") (cint' 0)
        end   = variable' (int' signed' []) (name' "end") (cint' 0)
        name  = prefix ++ (map toUpper s)
    in
     [composite' struct' (name' name) (group' [start, end])]
  getStateStruct prefix (µ -> FunCall (Fix (Name "start")) [Fix (Name s)]) =
    let start = variable' (int' signed' []) (name' "start") (cint' 1)
        end   = variable' (int' signed' []) (name' "end") (cint' 0)
        name  = prefix ++ (map toUpper s)
    in 
     [composite' struct' (name' name) (group' [start, end])]
  getStateStruct prefix (µ -> FunCall (Fix (Name "end")) [Fix (Name s)]) =
    let start = variable' (int' signed' []) (name' "start") (cint' 0)
        end   = variable' (int' signed' []) (name' "end") (cint' 1)
        name  = prefix ++ (map toUpper s)
    in 
     [composite' struct' (name' name) (group' [start, end])]
  getStateStruct _ _ = []

  createStateMachine :: [Fix Sem] -> String -> [Fix Sem]
  createStateMachine args n = 
    let structName = "__sg_" ++ n ++ "_sm"
        enumName   = "__sg_" ++ n ++ "_states"
        stateName  = "__sg_" ++ n ++ "_state_"
        stateNames = concatMap getStateName args
        enum = enumeration' (name' enumName) stateNames
        start = Prelude.foldr getStart nil' args
        curr = variable' (enumeration' (name' enumName) []) (name' "curr") start
        lookupMap = create (name' "lookup")
        struct = composite' struct' (name' structName) (group' [curr, lookupMap])
        structs = concatMap (getStateStruct stateName) args
    in
     structs ++ [enum, struct]

  acceptableBeginning :: Fix Sem -> [Fix Sem]
  acceptableBeginning (µ -> Binary s1 (Fix (Name "->")) _) = [s1]
  acceptableBeginning _ = []
  
  beginnings :: [Fix Sem] -> [Fix Sem]
  beginnings = concatMap acceptableBeginning
  
  disallowOthers :: [Fix Sem] -> [Fix Sem]
  disallowOthers [] = []
  disallowOthers progs = 
    let begs = beginnings progs in
    case begs of 
      [] -> []
      (b : bs) -> let 
        cur  = binary' (name' "__sg_m") (name' "->") (name' "cur")
        ne   = \s -> binary' cur "!=" s
        neqs = map ne bs
        cond = foldl (\a b -> binary' a (name' "&&") b) (ne b) neqs 
        in
         [funcall' (name' "assert") [cond]]
    

     