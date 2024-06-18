include "map.mc"
include "name.mc"

include "ast.mc"
include "pprint.mc"

-- This language fragment defines a function that eliminates and replaces
-- top-level declarations, such that only the declarations in the model remain.
-- It does this by:
-- 1. Inlining the types bound to aliases.
-- 2. Inlining the expressions bound in let-bindings.
-- 3. Transforming user-defined types to integer range types, with each
--    constructor being replaced by an integer value.
-- 4. Simplifying constant expressions to values.
lang TrellisResolveDeclarations = TrellisAst
  type ResolveEnv = {
    -- Maps identifiers of aliases to the type they represent.
    aliases : Map Name TrellisType,

    -- Maps identifiers of constants to the expression bound to them.
    constants : Map Name TrellisExpr,

    -- Maps identifiers of types to an equivalent integer range type.
    types : Map Name TrellisType,

    -- Maps identifiers of constructors to an equivalent integer constant.
    constrs : Map Name Int
  }
  type Resolve a = ResolveEnv -> a -> a

  sem emptyResolveEnv : () -> ResolveEnv
  sem emptyResolveEnv =
  | _ ->
    { aliases = mapEmpty nameCmp, constants = mapEmpty nameCmp
    , types = mapEmpty nameCmp, constrs = mapEmpty nameCmp}

  sem resolveDeclarations : TrellisProgram -> [InModelDecl]
  sem resolveDeclarations =
  | MainTrellisProgram {d = d, indecl = indecl} ->
    let env = foldl collectDeclarations (emptyResolveEnv ()) d in
    let indecl = map (smap_InModelDecl_TrellisType (resolveTrellisType env)) indecl in
    map (smap_InModelDecl_ProbDecl (resolveProbDecl env)) indecl

  sem collectDeclarations : ResolveEnv -> Decl -> ResolveEnv
  sem collectDeclarations env =
  | TypeDecl {id = {v = id}, constr = constr, info = info} ->
    let ub = subi (length constr) 1 in
    let ty = IntRangeTrellisType {
      lb = {i = info, v = 0}, ub = Some {i = info, v = ub}, namedUb = None (),
      info = info
    } in
    let constr = map (lam c. c.v) constr in
    let c = foldli (lam acc. lam i. lam c. mapInsert c i acc) env.constrs constr in
    {env with types = mapInsert id ty env.types, constrs = c}
  | LetDecl {id = {v = id}, e = e} ->
    let e = constantFoldTrellisExpr (resolveTrellisExpr env e) in
    {env with constants = mapInsert id e env.constants}
  | AliasDecl {id = {v = id}, ty = ty} ->
    let ty = resolveTrellisType env ty in
    {env with aliases = mapInsert id ty env.aliases}

  sem resolveProbDecl : Resolve ProbDecl
  sem resolveProbDecl env =
  | pd ->
    let pd = smap_ProbDecl_TrellisExpr (resolveTrellisExpr env) pd in
    smap_ProbDecl_TrellisSet (resolveTrellisSet env) pd

  sem resolveTrellisSet : Resolve TrellisSet
  sem resolveTrellisSet env =
  | s ->
    let s = smap_TrellisSet_TrellisPat (resolveTrellisPat env) s in
    smap_TrellisSet_TrellisExpr (resolveTrellisExpr env) s

  sem resolveTrellisType : Resolve TrellisType
  sem resolveTrellisType env =
  | ConcreteTrellisType {id = {v = id}, info = info} ->
    match mapLookup id env.aliases with Some ty then ty
    else match mapLookup id env.types with Some ty then ty
    else errorSingle [info] "Definition of type was not found"
  | ArrayTTrellisType (t & {namedCount = Some {i = i, v = nc}}) ->
    let t = {t with left = resolveTrellisType env t.left} in
    match mapLookup nc env.constants with Some e then
      match e with IntTrellisExpr {i = {v = v}} then
        ArrayTTrellisType {t with count = Some {i = i, v = v}, namedCount = None ()}
      else errorSingle [t.info] "Array type must have constant length"
    else ArrayTTrellisType t
  | IntRangeTrellisType (t & {namedUb = Some {i = i, v = nub}}) ->
    match mapLookup nub env.constants with Some e then
      match e with IntTrellisExpr {i = {v = v}} then
        IntRangeTrellisType {t with ub = Some {i = i, v = v}, namedUb = None ()}
      else errorSingle [t.info] "Integer range type must have constant upper-bound"
    else IntRangeTrellisType t
  | ty -> smap_TrellisType_TrellisType (resolveTrellisType env) ty

  sem resolveTrellisPat : Resolve TrellisPat
  sem resolveTrellisPat env =
  | ConTrellisPat {id = {i = i, v = id}, info = info} ->
    match mapLookup id env.constrs with Some constrIdx then
      IntPTrellisPat {i = {i = i, v = constrIdx}, info = info}
    else errorSingle [info] "Definition of constructor was not found"
  | p -> smap_TrellisPat_TrellisPat (resolveTrellisPat env) p

  sem resolveTrellisExpr : Resolve TrellisExpr
  sem resolveTrellisExpr env =
  | VarTrellisExpr (t & {id = {v = id}}) ->
    match mapLookup id env.constants with Some e then e
    else VarTrellisExpr t
  | ConstrTrellisExpr {id = {i = i, v = id}, info = info} ->
    match mapLookup id env.constrs with Some constrIdx then
      IntTrellisExpr {i = {i = i, v = constrIdx}, info = info}
    else errorSingle [info] "Error when replacing constructor with integer"
  | e -> smap_TrellisExpr_TrellisExpr (resolveTrellisExpr env) e

  sem constantFoldTrellisExpr : TrellisExpr -> TrellisExpr
  sem constantFoldTrellisExpr =
  | AddTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. AddTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryArithOp default addi info l r
  | SubTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. SubTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryArithOp default subi info l r
  | MulTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. MulTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryArithOp default muli info l r
  | DivTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. DivTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryArithOp default divi info l r
  | EqTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. EqTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryCompareOp default eqi info l r
  | NeqTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. NeqTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryCompareOp default neqi info l r
  | LtTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. LtTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryCompareOp default lti info l r
  | GtTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. GtTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryCompareOp default gti info l r
  | LeqTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. LeqTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryCompareOp default leqi info l r
  | GeqTrellisExpr (t & {left = l, right = r, info = info}) ->
    let default = lam l. lam r. GeqTrellisExpr {t with left = l, right = r} in
    constantFoldBinaryCompareOp default geqi info l r
  | e -> smap_TrellisExpr_TrellisExpr constantFoldTrellisExpr e

  sem constantFoldBinaryArithOp
    : (TrellisExpr -> TrellisExpr -> TrellisExpr) -> (Int -> Int -> Int)
   -> Info -> TrellisExpr -> TrellisExpr -> TrellisExpr
  sem constantFoldBinaryArithOp default op info l =
  | r ->
    let left = constantFoldTrellisExpr l in
    let right = constantFoldTrellisExpr r in
    match (left, right) with (IntTrellisExpr l, IntTrellisExpr r) then
      IntTrellisExpr {i = {i = mergeInfo l.i.i r.i.i, v = op l.i.v r.i.v}, info = info}
    else default left right

  sem constantFoldBinaryCompareOp
    : (TrellisExpr -> TrellisExpr -> TrellisExpr) -> (Int -> Int -> Bool)
   -> Info -> TrellisExpr -> TrellisExpr -> TrellisExpr
  sem constantFoldBinaryCompareOp default op info l =
  | r ->
    let left = constantFoldTrellisExpr l in
    let right = constantFoldTrellisExpr r in
    match (left, right) with (IntTrellisExpr l, IntTrellisExpr r) then
      if op l.i.v r.i.v then TrueTrellisExpr {info = info}
      else FalseTrellisExpr {info = info}
    else default left right
end

mexpr

use TrellisResolveDeclarations in

let test = lam str.
  let indecls = resolveDeclarations (parseTrellisExn "" str) in
  let pprint = lam indecl.
    use TrellisPrettyPrint in
    match pprintTrellisInModelDecl 0 pprintEnvEmpty indecl with (_, s) in
    s
  in
  map pprint indecls
in
let ppStringSeqs = lam lhs. lam rhs.
  let asStr = lam strs. map (lam s. join ["\"", s, "\""]) strs in
  join [
    "    LHS: [", strJoin ", " (asStr lhs), "]\n",
    "    RHS: [", strJoin ", " (asStr rhs), "]"
  ]
in

let s = "
alias T = 1 .. 10
model {
  state = T
}
" in
utest test s with ["state = 1 .. 10"] using eqSeq eqString else ppStringSeqs in

let s = "
let n = 0.5
model {
  P(initial x) = n
}
" in
utest test s with ["P(initial x) = 0.5"] using eqSeq eqString else ppStringSeqs in

let s = "
type Nucleotide = {A, C, G, T}
let merlength = 5
let outlen = 1024
alias Kmer = Nucleotide[merlength]
alias Duration = 1 .. 16
alias ObsTy = 1 .. outlen
model {
  state = (Kmer, Duration)
  output = ObsTy
}
" in
utest test s with ["state = (0 .. 3[5], 1 .. 16)", "output = 1 .. 1024"]
using eqSeq eqString else ppStringSeqs in

()
