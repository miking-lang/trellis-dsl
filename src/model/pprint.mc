include "mexpr/pprint.mc"

include "ast.mc"

lang TrellisModelPrettyPrintBase =
  PrettyPrint + MExprIdentifierPrettyPrint

  type PprintType a = PprintEnv -> a -> (PprintEnv, String)
end

lang TrellisModelTypePrettyPrint =
  TrellisModelPrettyPrintBase + TrellisModelTypeAst

  sem pprintTrellisType : TType -> String
  sem pprintTrellisType =
  | TBool _ -> "Bool"
  | TInt {bounds = None _} -> "Int"
  | TInt {bounds = Some (lb, ub)} ->
    join [int2string lb, "..", int2string ub]
  | TProb _ -> "Probability"
  | TTuple {tys = tys} ->
    join ["(", strJoin ", " (map pprintTrellisType tys), ")"]
  | TTable {args = args, ret = ret} ->
    let args = map pprintTrellisType args in
    let ret = pprintTrellisType ret in
    join ["(", strJoin ", " args, ") : ", ret]
end

lang TrellisModelExprPrettyPrint =
  TrellisModelPrettyPrintBase + TrellisModelExprAst

  sem pprintTrellisExpr : PprintType TExpr
  sem pprintTrellisExpr env =
  | EBool {b = b} -> (env, if b then "true" else "false")
  | EVar {id = id} -> pprintVarName env id
  | EInt {i = i} -> (env, int2string i)
  | EProb {p = p} -> (env, float2string p)
  | ESlice {target = target, lo = lo, hi = hi} ->
    match pprintTrellisExpr env target with (env, target) in
    if eqi lo hi then
      (env, join [target, "[", int2string lo, "]"])
    else
      (env, join [target, "[", int2string lo, ":", int2string hi, "]"])
  | ETableAccess {table = table, args = args} ->
    match pprintVarName env table with (env, table) in
    match mapAccumL pprintTrellisExpr env args with (env, args) in
    (env, join [table, "(", strJoin ", " args, ")"])
  | EIf {cond = cond, thn = thn, els = els} ->
    match pprintTrellisExpr env cond with (env, cond) in
    match pprintTrellisExpr env thn with (env, thn) in
    match pprintTrellisExpr env els with (env, els) in
    (env, join ["if ", cond, " then ", thn, " else ", els])
  | EBinOp {op = op, lhs = lhs, rhs = rhs} ->
    match pprintTrellisExpr env lhs with (env, lhs) in
    match pprintTrellisExpr env rhs with (env, rhs) in
    (env, join ["(", lhs, " ", pprintBinOp op, " ", rhs, ")"])

  sem pprintBinOp : BOp -> String
  sem pprintBinOp =
  | OAdd _ -> "+"
  | OSub _ -> "-"
  | OMul _ -> "*"
  | ODiv _ -> "/"
  | OMod _ -> "%"
  | OEq _ -> "=="
  | ONeq _ -> "!="
  | OLt _ -> "<"
  | OGt _ -> ">"
  | OLeq _ -> "<="
  | OGeq _ -> ">="
  | OAnd _ -> "&&"
  | OOr _ -> "||"
end

lang TrellisModelSetPrettyPrint =
  TrellisModelPrettyPrintBase + TrellisModelSetAst +
  TrellisModelExprPrettyPrint

  sem pprintTrellisSet : PprintType TSet
  sem pprintTrellisSet env =
  | SAll _ -> (env, "{_ | true}")
  | SValueBuilder {x = x, conds = conds} ->
    match pprintVarName env x with (env, x) in
    match mapAccumL pprintTrellisExpr env conds with (env, conds) in
    (env, join ["{", x, " | ", strJoin ", " conds, "}"])
  | STransitionBuilder {x = x, y = y, conds = conds} ->
    match pprintVarName env x with (env, x) in
    match pprintVarName env y with (env, y) in
    match mapAccumL pprintTrellisExpr env conds with (env, conds) in
    (env, join ["{", x, " -> ", y, " | ", strJoin ", " conds, "}"])
end

lang TrellisModelPrettyPrint =
  TrellisModelPrettyPrintBase + TrellisModelTypePrettyPrint +
  TrellisModelExprPrettyPrint + TrellisModelSetPrettyPrint + TrellisModelAst

  sem pprintTable : PprintType (Name, TType)
  sem pprintTable env =
  | (tableId, tableType) ->
    match pprintVarName env tableId with (env, tableId) in
    let tableType = pprintTrellisType tableType in
    (env, join [pprintSpacing 2, "table ", tableId, tableType])

  sem pprintCase : PprintType Case
  sem pprintCase env =
  | {cond = cond, body = body} ->
    match pprintTrellisSet env cond with (env, cond) in
    match pprintTrellisExpr env body with (env, body) in
    (env, join [pprintSpacing 4, "| ", cond, " => ", body])

  sem pprintCases : PprintType [Case]
  sem pprintCases env =
  | [{cond = SAll _, body = body}] ->
    pprintTrellisExpr env body
  | cases ->
    match mapAccumL pprintCase env cases with (env, cases) in
    let cases = strJoin "\n" cases in
    (env, join ["{\n", cases, pprintNewline 2, "}"])

  sem pprintInitialProbDef : PprintType InitialProbDef
  sem pprintInitialProbDef env =
  | {x = x, cases = cases} ->
    match pprintVarName env x with (env, x) in
    match pprintCases env cases with (env, cases) in
    (env, join [pprintSpacing 2, "P(initial ", x, ") = ", cases])

  sem pprintOutputProbDef : PprintType OutputProbDef
  sem pprintOutputProbDef env =
  | {x = x, o = o, cases = cases} ->
    match pprintVarName env x with (env, x) in
    match pprintVarName env o with (env, o) in
    match pprintCases env cases with (env, cases) in
    (env, join [pprintSpacing 2, "P(output ", o, " | ", x, ") = ", cases])

  sem pprintTransitionProbDef : PprintType TransitionProbDef
  sem pprintTransitionProbDef env =
  | {x = x, y = y, cases = cases} ->
    match pprintVarName env x with (env, x) in
    match pprintVarName env y with (env, y) in
    match pprintCases env cases with (env, cases) in
    (env, join [pprintSpacing 2, "P(transition ", x, " ", y, ") = ", cases])

  sem pprintTrellisModel : TModel -> String
  sem pprintTrellisModel =
  | m ->
    let env = pprintEnvEmpty in
    let stateType = pprintTrellisType m.stateType in
    let outType = pprintTrellisType m.outType in
    match mapAccumL pprintTable env (mapBindings m.tables) with (env, tables) in
    match pprintInitialProbDef env m.initial with (env, initial) in
    match pprintOutputProbDef env m.output with (env, output) in
    match pprintTransitionProbDef env m.transition with (env, transition) in
    strJoin "\n" [
      "model {",
      join [pprintSpacing 2, "state = ", stateType],
      join [pprintSpacing 2, "output = ", outType],
      strJoin "\n" tables,
      initial,
      output,
      transition,
      "}"
    ]
end
