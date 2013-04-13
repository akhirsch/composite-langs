{-#LANGUAGE ViewPatterns #-}

module Language.Composite.IDL.StateMachines where
  import Language.Pony
  import Language.Composite.IDL
  import Data.Char (toUpper)

  stateChange :: Fix Sem -> [Fix Sem]
  stateChange (µ -> Binary (Fix (Name s1)) (Fix (Name "->")) (Fix (Name s2))) =
    let machineName = name' "__sg_m"
        curState    = binary' machineName (name' "->") (name' "cur")
        check       = binary' curState (name' "==") (name' $ map toUpper s1)
        set         = binary' curState (name' "=") (name' $ map toUpper s2)
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
    machineVar = variable' (pointer_to' (composite' struct' machine nil')) machineName nil'
    findMachine = binary' machineName (name' "=") (lookupStatic lookupMap key)
     in
     [keyAssign, machineVar, findMachine]
  getMachine _ x = [x]
  
  getMachineSStub :: String -> Fix Sem -> [Fix Sem]
  getMachineSStub s (µ -> FunCall (Fix (Name "key")) [key@(Fix(Name _))]) = let
    machineName = name' "__sg_m"
    keyName = name' "__sg_k"
    key' = (binary' (name' "d") (name' "->") key) 
    machine = name' $ "__sg_" ++ s ++ "_sm"
    lookupMap = name' $ "__sg_" ++ s ++ "_sm_lookup"
    keyAssign = variable' (int' signed' [long']) keyName key'
    machineVar = variable' (pointer_to' (composite' struct' machine nil')) machineName nil'
    findMachine = binary' machineName (name' "=") (lookupStatic lookupMap key')
    in
     [keyAssign, machineVar, findMachine]
  getMachineSStub _ x = [x]
    
  cbufQ (µ -> Variable {vtype = t, vname = _, vvalue = _}) = cbufQ' t
    where
      cbufQ' (µ -> (TypedefT (Fix (Name "cbuf_t")))) = True
      cbufQ' _ = False
  cbufQ _ = False
                        
  machineInFunction :: String -> Fix Sem -> Fix Sem
  machineInFunction s (µ -> Function n t (Fix (Arguments a)) (Fix (Program l))) = 
    let state1 = concatMap stateChange $ concatMap (getMachine s) l
        state2 = concatMap stateChange $ concatMap (getMachineSStub s) l
        assert = disallowOthers l
        exists p = (foldl (||) False) . (map p)
        prog = assert ++ if exists cbufQ a then state2 else state1
    in
    function' n t (arguments' a) (program' prog)

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

{-
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
-}
  createStateMachine :: [Fix Sem] -> String -> [Fix Sem]
  createStateMachine args n = 
    let structName = "__sg_" ++ n ++ "_sm"
        enumName   = "__sg_" ++ n ++ "_states"
        --stateName  = "__sg_" ++ n ++ "_state_"
        stateNames = concatMap getStateName args
        enum = enumeration' (name' enumName) stateNames
        start = Prelude.foldr getStart nil' args
        curr = variable' (enumeration' (name' enumName) []) (name' "curr") start
        lookupMap = create (name' "lookup")
        struct = composite' struct' (name' structName) (group' [curr, lookupMap])
        -- This code left in because it'll be necessary for advanced 
        -- state machines with arbitrary state parameters
        --structs = concatMap (getStateStruct stateName) args
    in
     {- structs ++ -} [enum, struct]

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
        ne   = \(Fix (Name s)) -> binary' cur "==" (name' $ map toUpper s)
        neqs = map ne bs
        cond = foldl (\alpha beta -> binary' alpha (name' "||") beta) (ne b) neqs 
        in
         [funcall' (name' "assert") [cond]]
    

     