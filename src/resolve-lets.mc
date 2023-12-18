lang TrellisResolveVariables = TrellisAst
  type VarDeclMap = Map Name ExprT
  type ResolveType a = VarDeclMap -> a -> (VarDeclMap, a)

  sem resolveLetVariables : Top -> Top
  sem resolveLetVariables =
  | Top1 t ->
    let emptyMap = mapEmpty nameCmp in
    match mapAccumL resolveVariablesDecl emptyMap t.d with (_, d) in
    Top1 {t with d = removeLetDeclarations d}

  sem removeLetDeclarations : [Decl] -> [Decl]
  sem removeLetDeclarations =
  | [FuncDecl {p = []}] ++ t -> removeLetDeclarations t
  | [h] ++ t -> cons h (removeLetDeclarations t)
  | [] -> []

  sem resolveVariablesDecl : ResolveType Decl
  sem resolveVariablesDecl m =
  | TypeDecl t ->
    match mapAccumL resolveVariablesConstrDecl m t.v with (m, v) in
    (m, TypeDecl {t with v = v})
  | AutomatonDecl t ->
    match mapAccumL resolveVariablesAutomatonProp m t.prop with (m, prop) in
    (m, AutomatonDecl {t with prop = prop})
  | FuncDecl (t & {fname = n, p = [], e = e}) ->
    let m = mapInsert n.v e m in
    (m, FuncDecl t)
  | FuncDecl t ->
    match resolveVariablesExpr m t.e with (m, e) in
    (m, FuncDecl {t with e = e})
  | ModelDecl t ->
    match mapAccumL resolveVariablesInModelDecl m t.indecl with (m, indecl) in
    (m, ModelDecl {t with indecl = indecl})
  | d -> (m, d)

  sem resolveVariablesConstrDecl : ResolveType ConstrDecl
  sem resolveVariablesConstrDecl m =
  | c ->
    smapAccumL_ConstrDecl_TypeT resolveVariablesType m c

  sem resolveVariablesAutomatonProp : ResolveType AutomatonProp
  sem resolveVariablesAutomatonProp m =
  | prop ->
    match smapAccumL_AutomatonProp_TypeT resolveVariablesType m prop with (m, prop) in
    smapAccumL_AutomatonProp_SetT resolveVariablesSet m prop

  sem resolveVariablesSet : ResolveType SetT
  sem resolveVariablesSet m =
  | s ->
    match smapAccumL_SetT_SetT resolveVariablesSet m s with (m, s) in
    smapAccumL_SetT_ExprT resolveVariablesExpr m s

  sem resolveVariablesInModelDecl : ResolveType InModelDecl
  sem resolveVariablesInModelDecl m =
  | indecl ->
    match smapAccumL_InModelDecl_TypeT resolveVariablesType m indecl with (m, indecl) in
    match smapAccumL_InModelDecl_ExprT resolveVariablesExpr m indecl with (m, indecl) in
    smapAccumL_InModelDecl_SetT resolveVariablesSet m indecl

  sem resolveVariablesType : ResolveType TypeT
  sem resolveVariablesType m =
  | ArrayTypeT t ->
    match resolveVariablesExpr m t.count with (m, count) in
    match count with IntegerExprT _ then
      (m, ArrayTypeT {t with count = count})
    else
      errorSingle [t.info] "Array size refers to non-constant value"
  | IntegerTypeT t ->
    match t.namedUb with Some n then
      match mapLookup n.v m with Some e then
        match e with IntegerExprT {i = i} then
          (m, IntegerTypeT {t with ub = Some i, namedUb = None ()})
        else
          errorSingle [t.info] "Integer upper bound refers to non-constant variable"
      else (m, IntegerTypeT t)
    else (m, IntegerTypeT t)
  | ty -> smapAccumL_TypeT_ExprT resolveVariablesExpr m ty

  sem resolveVariablesExpr : ResolveType ExprT
  sem resolveVariablesExpr m =
  | VariableExprT t ->
    match mapLookup t.v.v m with Some e then (m, e) else (m, VariableExprT t)
  | e -> smapAccumL_ExprT_ExprT resolveVariablesExpr m e
end
