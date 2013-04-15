{-#LANGUAGE ViewPatterns #-}

module Language.Composite.IDL.StateMachines where
  import Language.Pony
  import Language.Composite.IDL
  import Data.Char (toUpper)

  stateChange :: Fix Sem -> [Fix Sem]
  stateChange (µ -> Binary (Fix (Name s1)) (Fix (Name "->")) (Fix (Name s2))) =
    let machineName = name' "__sg_m"
        curState    = binary' machineName (name' "->") (name' "curr")
        check       = binary' curState (name' "==") (name' $ map toUpper s1)
        set         = binary' curState (name' "=") (name' $ map toUpper s2)
    in
     [ifthen' check set]
  stateChange _ = []
  
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
    keyName         = name' "__sg_k"
    machine         = name' $ "__sg_" ++ s ++ "_sm"
    machineInitName = name' $ "__sg_" ++ s ++ "_sm" ++ "_init"   
    lookupMap       = name' $ "__sg_" ++ s ++ "_sm_lookup"
    keyAssign       = variable' (int' signed' [long']) keyName key
    machineVar      = variable' (pointer_to' (composite' struct' machine nil')) machineName nil'
    findMachine     = binary' machineName (name' "=") (lookupStatic lookupMap key)
    nullMachine     = binary' machineName (name' "==") (name' "null")
    blankMachine    = funcall' (name' "malloc") [funcall' (name' "sizeof") [(composite' struct' machine nil')]]
    assignMachine   = binary' machineName (name' "=") blankMachine
    initMachine     = funcall' machineInitName [machine]
    addMachine      = addStatic lookupMap keyName machineName
    instructions    = Fix (Compound [assignMachine, initMachine, addMachine])
    ifNull          = ifthen' nullMachine instructions
     in
     [keyAssign, machineVar, findMachine, ifNull]
  getMachine _ _ = []
  
  getMachineSStub :: String -> Fix Sem -> [Fix Sem]
  getMachineSStub s (µ -> FunCall (Fix (Name "key")) [key@(Fix(Name _))]) = let
    machineName     = name' "__sg_m"
    keyName         = name' "__sg_k"
    key'            = (binary' (name' "d") (name' "->") key) 
    machine         = name' $ "__sg_" ++ s ++ "_sm"
    machineInitName = name' $ "__sg_" ++ s ++ "_sm" ++ "_init"   
    lookupMap       = name' $ "__sg_" ++ s ++ "_sm_lookup"
    keyAssign       = variable' (int' signed' [long']) keyName key'
    machineVar      = variable' (pointer_to' (composite' struct' machine nil')) machineName nil'
    findMachine     = binary' machineName (name' "=") (lookupStatic lookupMap key')    
    nullMachine     = binary' machineName (name' "==") (name' "null")
    blankMachine    = funcall' (name' "malloc") [funcall' (name' "sizeof") [(composite' struct' machine nil')]]
    assignMachine   = binary' machineName (name' "=") blankMachine
    initMachine     = funcall' machineInitName [machine]
    addMachine      = addStatic lookupMap keyName machineName
    instructions    = Fix (Compound [assignMachine, initMachine, addMachine])
    ifNull          = ifthen' nullMachine instructions
    in
     [keyAssign, machineVar, findMachine, ifNull]
  getMachineSStub _ _ = []

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
    let start      = variable' (int' signed' []) (name' "start") nil'
        end        = variable' (int' signed' []) (name' "end") nil'
        name       = prefix ++ (map toUpper s)
        initSName  = name' $ "state"
        initStart  = binary' initSName (name' "->") (name' "start")
        setStart   = binary' initStart (name' "=")  (cint' 0)
        initEnd    = binary' initSName (name' "->") (name' "end")
        setEnd     = binary' initEnd   (name' "=")  (cint' 0)
        initInst   = program' $ [setStart, setEnd]
        initStruct = variable' (pointer_to' $ composite' struct' (name' name) nil') initSName nil'
        initParams = arguments' $ [initStruct]
        initF      = function' (name' $ name ++ "_init") void' initParams initInst
    in
     [composite' struct' (name' name) (group' [start, end]), initF]
  getStateStruct prefix (µ -> FunCall (Fix (Name "start")) [Fix (Name s)]) =
    let start = variable' (int' signed' []) (name' "start") nil'
        end   = variable' (int' signed' []) (name' "end") nil'
        name  = prefix ++ (map toUpper s)
        initSName  = name' $ "state"
        initStart  = binary' initSName (name' "->") (name' "start")
        setStart   = binary' initStart (name' "=")  (cint' 1)
        initEnd    = binary' initSName (name' "->") (name' "end")
        setEnd     = binary' initEnd   (name' "=")  (cint' 0)
        initInst   = program' $ [setStart, setEnd]
        initStruct = variable' (pointer_to' $ composite' struct' (name' name) nil') initSName nil'
        initParams = arguments' $ [initStruct]
        initF      = function' (name' $ name ++ "_init") void' initParams initInst
    in 
     [composite' struct' (name' name) (group' [start, end]), initF]
  getStateStruct prefix (µ -> FunCall (Fix (Name "end")) [Fix (Name s)]) =
    let start = variable' (int' signed' []) (name' "start") nil'
        end   = variable' (int' signed' []) (name' "end") nil'
        name  = prefix ++ (map toUpper s)
        initSName  = name' $ "state"
        initStart  = binary' initSName (name' "->") (name' "start")
        setStart   = binary' initStart (name' "=")  (cint' 0)
        initEnd    = binary' initSName (name' "->") (name' "end")
        setEnd     = binary' initEnd   (name' "=")  (cint' 1)
        initInst   = program' $ [setStart, setEnd]
        initStruct = variable' (pointer_to' $ composite' struct' (name' name) nil') initSName nil'
        initParams = arguments' $ [initStruct]
        initF      = function' (name' $ name ++ "_init") void' initParams initInst
    in 
     [composite' struct' (name' name) (group' [start, end]), initF]
  getStateStruct _ _ = []
  
  createStateMachine :: [Fix Sem] -> String -> [Fix Sem]
  createStateMachine args n = 
    let structName = "__sg_" ++ n ++ "_sm"
        enumName   = "__sg_" ++ n ++ "_states"
        stateName  = "__sg_" ++ n ++ "_state_"
        stateNames = concatMap getStateName args
        enum = enumeration' (name' enumName) stateNames
        start = Prelude.foldr getStart nil' args
        curr = variable' (enumeration' (name' enumName) []) (name' "curr") nil'
        lookupMap = create (name' "lookup")
        struct = composite' struct' (name' structName) (group' [curr, lookupMap])
        localCurr = binary' (name' "sm") (name' "->") (name' "curr")        
        setCurr = binary' localCurr (name' "=") start
        smType = composite' struct' (name' structName) nil'
        localSM = variable' (pointer_to' smType) (name' "sm") nil'
        localLookup = binary' (name' "sm") (name' "->") (name' "lookup")
        initLookup = initialize localLookup
        initName = name' $ structName ++ "_init"
        startName = case getStateName start of
          [x] -> x
          _   -> name' ""
        startStructName = name' $ case startName of
          Fix (Name namae) -> "__sg_torrent_state_" ++ namae
          _                -> "" 
        startStruct = composite' struct' startStructName nil'
        startSize = funcall' (name' "sizeof") [startStruct]
        mallocBeginning = funcall' (name' "malloc") [startSize]
        createBeginning = variable' (pointer_to' startStruct) (name' "start") mallocBeginning        
        initStructFName = name' $ case startStructName of 
          Fix (Name namae) -> namae ++ "_init"
          _                -> "" 
        initBeginning = funcall' initStructFName [(name' "start")]
        addBeginning = add localLookup (name' "start") start
        instructions = program' [setCurr, initLookup, createBeginning, initBeginning, addBeginning]
        initStruct = function' initName (Fix VoidT) (arguments' [localSM]) instructions

        -- This code left in because it'll be necessary for advanced 
        -- state machines with arbitrary state parameters
        structs = concatMap (getStateStruct stateName) args
    in
     structs ++ [enum, struct, initStruct]

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
        cur  = binary' (name' "__sg_m") (name' "->") (name' "curr")
        ne   = \(Fix (Name s)) -> binary' cur "==" (name' $ map toUpper s)
        neqs = map ne bs
        cond = foldl (\alpha beta -> binary' alpha (name' "||") beta) (ne b) neqs 
        in
         [funcall' (name' "assert") [cond]]
    

     