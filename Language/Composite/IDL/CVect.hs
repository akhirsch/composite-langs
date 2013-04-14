module Language.Composite.IDL.CVect where
  import Language.Pony
  
  create :: Fix Sem -> Fix Sem  
  create name = variable' (pointer_to' $ typedef_t' "cvect_t") name nil' 

  createStatic :: Fix Sem -> Fix Sem
  createStatic name = 
    let cvectValue = name' "{.vect = {{.c.next = NULL}}}"
    in variable' (pointer_to' $ typedef_t' "cvect_t") name cvectValue
       
  initialize :: Fix Sem -> Fix Sem
  initialize name = funcall' (name' "cvect_init") [name]
  
  initializeStatic :: Fix Sem -> Fix Sem
  initializeStatic name = funcall' (name' "cvect_init_static") [name]
  
  add :: Fix Sem -> Fix Sem -> Fix Sem -> Fix Sem
  add name val id = funcall' (name' "cvect_add") [name, val, id]
  
  addStatic :: Fix Sem -> Fix Sem -> Fix Sem -> Fix Sem
  addStatic name val id = 
    let addr = unary' (name' "&") name in
    funcall' (name' "cvect_add") [addr, val, id]
    
  delete :: Fix Sem -> Fix Sem -> Fix Sem
  delete name id = funcall' (name' "cvect_del") [name, id]
  
  deleteStatic :: Fix Sem -> Fix Sem -> Fix Sem
  deleteStatic name id = 
    let addr = unary' (name' "&") name in
    funcall' (name' "cvect_del") [addr, id]
    
  lookup :: Fix Sem -> Fix Sem -> Fix Sem
  lookup name id = funcall' (name' "cvect_lookup") [name, id]
  
  lookupStatic :: Fix Sem -> Fix Sem -> Fix Sem
  lookupStatic name id = 
    let addr = unary' (name' "&") name in
    funcall' (name' "cvect_lookup") [addr, id]