-- Simplifies the Trellis AST by
-- 1. Inlining all let-bindings of values
-- 2. Translating constructor types to integer ranges and uses of the
--    constructors to integer literals.

include "name.mc"
include "option.mc"

include "ast.mc"

lang TrellisResolveConstants = TrellisAst
  type ConstDeclMap = Map Name TrellisExpr
  type ResolveType a = ConstDeclMap -> a -> (ConstDeclMap, a)

  sem resolveConstants : TrellisProgram -> TrellisProgram
  sem resolveConstants =
  | MainTrellisProgram t ->
    let emptyMap = mapEmpty nameCmp in
    match mapAccumL resolveConstantsDecl emptyMap t.d with (m, d) in
    match mapAccumL resolveConstantsInModelDecl m t.indecl with (_, indecl) in
    MainTrellisProgram {t with d = removeConstantDeclarations d, indecl = indecl}

  sem removeConstantDeclarations : [Decl] -> [Decl]
  sem removeConstantDeclarations =
  | [LetDecl _] ++ rest -> removeConstantDeclarations rest
  | [d] ++ rest -> cons d (removeConstantDeclarations rest)
  | [] -> []

  sem resolveConstantsDecl : ResolveType Decl
  sem resolveConstantsDecl m =
  | TypeDecl t -> (m, TypeDecl t)
  | LetDecl (t & {id = {v = id}, e = e}) ->
    match resolveConstantsExpr m e with (m, e) in
    (mapInsert id e m, LetDecl {t with e = e})

  sem resolveConstantsInModelDecl : ResolveType InModelDecl
  sem resolveConstantsInModelDecl m =
  | d ->
    match smapAccumL_InModelDecl_TrellisType resolveConstantsType m d with (m, d) in
    match smapAccumL_InModelDecl_TrellisExpr resolveConstantsExpr m d with (m, d) in
    smapAccumL_InModelDecl_TrellisSet resolveConstantsSet m d

  sem resolveConstantsSet : ResolveType TrellisSet
  sem resolveConstantsSet m =
  | s -> smapAccumL_TrellisSet_TrellisExpr resolveConstantsExpr m s

  sem resolveConstantsExpr : ResolveType TrellisExpr
  sem resolveConstantsExpr m =
  | VarTrellisExpr (t & {id = {v = id}}) ->
    match mapLookup id m with Some e then (m, e) else (m, VarTrellisExpr t)
  | e -> smapAccumL_TrellisExpr_TrellisExpr resolveConstantsExpr m e

  sem resolveConstantsType : ResolveType TrellisType
  sem resolveConstantsType m =
  | ArrayTTrellisType (t & {namedCount = Some {i = i, v = nc}, info = info}) ->
    match mapLookup nc m with Some e then
      match e with IntTrellisExpr {i = {v = v}} then
        (m, ArrayTTrellisType {t with count = Some {i = i, v = v}, namedCount = None ()})
      else
        errorSingle [info] "Array type with non-constant upper-bound is not supported"
    else
      (m, ArrayTTrellisType t)
  | IntRangeTrellisType (t & {namedUb = Some {i = i, v = nub}, info = info}) ->
    match mapLookup nub m with Some e then
      match e with IntTrellisExpr {i = {v = v}} then
        (m, IntRangeTrellisType {t with ub = Some {i = i, v = v}, namedUb = None ()})
      else
        errorSingle [info] "Range with non-constant upper-bound is not supported"
    else
      (m, IntRangeTrellisType t)
  | ty ->
    match smapAccumL_TrellisType_TrellisType resolveConstantsType m ty with (m, ty) in
    smapAccumL_TrellisType_TrellisExpr resolveConstantsExpr m ty
end

lang TrellisReplaceUserTypes = TrellisAst
  type ReplaceEnv = {
    -- Maps identifiers of user-defined types to an equivalent integer range
    -- type.
    types : Map Name TrellisType,

    -- Maps constructor identifiers to an integer constant.
    constrs : Map Name Int
  }

  sem replaceUserTypesWithInts : TrellisProgram -> TrellisProgram
  sem replaceUserTypesWithInts =
  | MainTrellisProgram t ->
    let initEnv = {types = mapEmpty nameCmp, constrs = mapEmpty nameCmp} in
    let env = foldl collectUserDeclaredTypeReplacements initEnv t.d in
    let indecl = map (smap_InModelDecl_TrellisType (replaceUserTypesType env)) t.indecl in
    let indecl = map (smap_InModelDecl_TrellisSet (replaceUserTypesSet env)) indecl in
    let indecl = map (smap_InModelDecl_ProbDecl (replaceUserTypesProbDecl env)) indecl in
    MainTrellisProgram {t with d = removeUserDeclaredTypes t.d,
                               indecl = indecl}

  sem collectUserDeclaredTypeReplacements : ReplaceEnv -> Decl -> ReplaceEnv
  sem collectUserDeclaredTypeReplacements env =
  | TypeDecl {id = {v = id}, constr = constr, info = info} ->
    let ub = subi (length constr) 1 in
    let intRangeTy = IntRangeTrellisType {
      lb = {i = info, v = 0}, ub = Some {i = info, v = ub}, namedUb = None (),
      info = info
    } in
    let constr = map (lam c. c.v) constr in
    let c = foldli (lam acc. lam i. lam c. mapInsert c i acc) env.constrs constr in
    {env with types = mapInsert id intRangeTy env.types, constrs = c}
  | _ -> env

  sem removeUserDeclaredTypes : [Decl] -> [Decl]
  sem removeUserDeclaredTypes =
  | [TypeDecl _] ++ rest -> removeUserDeclaredTypes rest
  | [d] ++ rest -> cons d (removeUserDeclaredTypes rest)
  | [] -> []

  sem replaceUserTypesType : ReplaceEnv -> TrellisType -> TrellisType
  sem replaceUserTypesType env =
  | ConcreteTrellisType {id = {v = id}, info = info} ->
    match mapLookup id env.types with Some ty then
      ty
    else errorSingle [info] "Failed to replace concrete type"
  | ty -> smap_TrellisType_TrellisType (replaceUserTypesType env) ty

  sem replaceUserTypesSet : ReplaceEnv -> TrellisSet -> TrellisSet
  sem replaceUserTypesSet env =
  | s ->
    let s = smap_TrellisSet_TrellisPat (replaceUserTypesPat env) s in
    smap_TrellisSet_TrellisExpr (replaceUserTypesExpr env) s

  sem replaceUserTypesPat : ReplaceEnv -> TrellisPat -> TrellisPat
  sem replaceUserTypesPat env =
  | ConTrellisPat {id = {i = i, v = id}, info = info} ->
    match mapLookup id env.constrs with Some constrIdx then
      IntPTrellisPat {i = {i = i, v = constrIdx}, info = info}
    else errorSingle [info] "Failed to replace constructor pattern"
  | p -> smap_TrellisPat_TrellisPat (replaceUserTypesPat env) p

  sem replaceUserTypesExpr : ReplaceEnv -> TrellisExpr -> TrellisExpr
  sem replaceUserTypesExpr env =
  | ConstrTrellisExpr {id = {i = i, v = id}, info = info} ->
    match mapLookup id env.constrs with Some constrIdx then
      IntTrellisExpr {i = {i = i, v = constrIdx}, info = info}
    else errorSingle [info] "Failed to replace constructor"
  | e -> smap_TrellisExpr_TrellisExpr (replaceUserTypesExpr env) e

  sem replaceUserTypesProbDecl : ReplaceEnv -> ProbDecl -> ProbDecl
  sem replaceUserTypesProbDecl env =
  | pd -> smap_ProbDecl_TrellisExpr (replaceUserTypesExpr env) pd
end

lang TrellisSimplify = TrellisResolveConstants + TrellisReplaceUserTypes
  sem simplifyTrellisProgram : TrellisProgram -> TrellisProgram
  sem simplifyTrellisProgram =
  | p ->
    let p = resolveConstants p in
    replaceUserTypesWithInts p
end
