include "string.mc"
include "mexpr/pprint.mc"

include "ast.mc"

lang TrellisPrettyPrintBase =
  PrettyPrint + MExprIdentifierPrettyPrint + TrellisAst
end

lang TrellisPatPrettyPrint = TrellisPrettyPrintBase
  sem pprintTrellisPat : PprintEnv -> TrellisPat -> (PprintEnv, String)
  sem pprintTrellisPat env =
  | ConTrellisPat {id = {v = id}} -> pprintConName env id
  | VarPTrellisPat {id = {v = id}} -> pprintVarName env id
  | IntPTrellisPat {i = {v = i}} -> (env, int2string i)
  | TruePTrellisPat _ -> (env, "true")
  | FalsePTrellisPat _ -> (env, "false")
  | ArrayPTrellisPat {p = p} ->
    match mapAccumL pprintTrellisPat env p with (env, p) in
    (env, join ["[", strJoin ", " p, "]"])
  | TupPTrellisPat {p = p} ->
    match mapAccumL pprintTrellisPat env p with (env, p) in
    (env, join ["@(", strJoin ", " p, ")"])
  | DotsTrellisPat {left = left} ->
    match pprintTrellisPat env left with (env, left) in
    (env, join [left, "..."])
end

lang TrellisExprPrettyPrint = TrellisPrettyPrintBase
  sem pprintTrellisExpr : PprintEnv -> TrellisExpr -> (PprintEnv, String)
  sem pprintTrellisExpr env =
  | TrueTrellisExpr _ -> (env, "true")
  | FalseTrellisExpr _ -> (env, "false")
  | VarTrellisExpr {id = {v = id}} -> pprintVarName env id
  | ConstrTrellisExpr {id = {v = id}} -> pprintConName env id
  | IntTrellisExpr {i = {v = i}} -> (env, int2string i)
  | TupleProjTrellisExpr {left = left, idx = {v = idx}} ->
    match pprintTrellisExpr env left with (env, left) in
    (env, join [left, ".", int2string idx])
  | ArrayAccessTrellisExpr {left = left, e = e} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env e with (env, e) in
    (env, join [left, "[", e, "]"])
  | IfTrellisExpr {c = c, thn = thn, right = right} ->
    match pprintTrellisExpr env c with (env, c) in
    match pprintTrellisExpr env thn with (env, thn) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join ["if ", c, " then ", thn, " else ", right])
  | ArrayTrellisExpr {e = e} ->
    match mapAccumL pprintTrellisExpr env e with (env, e) in
    (env, join ["[", strJoin ", " e, "]"])
  | TupleTrellisExpr {e = e} ->
    match mapAccumL pprintTrellisExpr env e with (env, e) in
    (env, join ["@(", strJoin ", " e, ")"])
  | AddTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " + ", right])
  | SubTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " - ", right])
  | MulTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " * ", right])
  | DivTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " / ", right])
  | EqTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " == ", right])
  | NeqTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " != ", right])
  | LtTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " < ", right])
  | GtTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " > ", right])
  | LeqTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " <= ", right])
  | GeqTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " >= ", right])
  | AndTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " && ", right])
  | OrTrellisExpr {left = left, right = right} ->
    match pprintTrellisExpr env left with (env, left) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join [left, " || ", right])
end

lang TrellisTypePrettyPrint = TrellisPrettyPrintBase + TrellisExprPrettyPrint
  sem pprintTrellisType : PprintEnv -> TrellisType -> (PprintEnv, String)
  sem pprintTrellisType env =
  | ArrayTTrellisType {left = left, count = count, namedCount = nc, info = info} ->
    match pprintTrellisType env left with (env, left) in
    match
      match count with Some {v = i} then (env, int2string i)
      else match nc with Some {v = id} then pprintVarName env id
      else errorSingle [info] "Invalid array size type"
    with (env, count) in
    (env, join [left, "[", count, "]"])
  | ConcreteTrellisType {id = {v = id}} -> pprintTypeName env id
  | TupleTTrellisType {t = t} ->
    match mapAccumL pprintTrellisType env t with (env, t) in
    (env, join ["@(", strJoin ", " t, ")"])
  | IntRangeTrellisType {lb = {v = lb}, ub = ub, namedUb = namedUb, info = info} ->
    match
      match ub with Some {v = ub} then (env, int2string ub)
      else match namedUb with Some {v = id} then pprintVarName env id
      else errorSingle [info] "Invalid integer range type"
    with (env, upperBound) in
    (env, join [int2string lb, "..", upperBound])
  | BoolTrellisType _ -> (env, "Bool")
  | IntTTrellisType _ -> (env, "Int")
  | ProbTTrellisType _ -> (env, "Probability")
end

lang TrellisSetPrettyPrint =
  TrellisPrettyPrintBase + TrellisPatPrettyPrint + TrellisExprPrettyPrint

  sem pprintTrellisSet : PprintEnv -> TrellisSet -> (PprintEnv, String)
  sem pprintTrellisSet env =
  | BuilderTrellisSet {p = p, to = to, e = e, info = info} ->
    match
      match pprintTrellisPat env p with (env, p) in
      match to with Some to then
        match pprintTrellisPat env to with (env, to) in
        (env, join [p, " -> ", to])
      else (env, p)
    with (env, lhs) in
    match mapAccumL pprintTrellisExpr env e with (env, e) in
    (env, join ["{", lhs, " | ", strJoin ", " e, "}"])
  | LiteralTrellisSet {v = v, info = info} ->
    let pprintSetElement = lam env. lam elem.
      match pprintTrellisExpr env elem.e with (env, e) in
      match elem with {to = Some to} then
        match pprintTrellisExpr env to with (env, to) in
        (env, join [e, " -> ", to])
      else (env, e)
    in
    match mapAccumL pprintSetElement env v with (env, v) in
    (env, join ["@{", strJoin ", " v, "}"])
end

lang TrellisInModelDeclPrettyPrint = TrellisPrettyPrintBase
  sem pprintTrellisInModelDecl : Int -> PprintEnv -> InModelDecl -> (PprintEnv, String)
end

lang TrellisStatePropertyInModelDeclPrettyPrint =
  TrellisInModelDeclPrettyPrint + TrellisTypePrettyPrint

  sem pprintTrellisInModelDecl indent env =
  | StatePropertyInModelDecl {ty = ty} ->
    match pprintTrellisType env ty with (env, ty) in
    (env, join [pprintSpacing indent, "state = ", ty])
end

lang TrellisOutputPropertyInModelDeclPrettyPrint =
  TrellisInModelDeclPrettyPrint + TrellisTypePrettyPrint

  sem pprintTrellisInModelDecl indent env =
  | OutputPropertyInModelDecl {ty = ty} ->
    match pprintTrellisType env ty with (env, ty) in
    (env, join [pprintSpacing indent, "output = ", ty])
end

lang TrellisSetInModelDeclPrettyPrint =
  TrellisInModelDeclPrettyPrint + TrellisSetPrettyPrint

  sem pprintTrellisInModelDecl indent env =
  | SetInModelDecl {id = {v = id}, s = s} ->
    match pprintVarName env id with (env, id) in
    match pprintTrellisSet env s with (env, s) in
    (env, join [pprintSpacing indent, "set ", id, " = ", s])
end

lang TrellisTableInModelDeclPrettyPrint =
  TrellisInModelDeclPrettyPrint + TrellisTypePrettyPrint

  sem pprintTrellisInModelDecl indent env =
  | TableInModelDecl {id = {v = id}, dim = dim, ty = ty} ->
    match pprintVarName env id with (env, id) in
    match mapAccumL pprintTrellisType env dim with (env, dim) in
    match pprintTrellisType env ty with (env, ty) in
    (env, join [pprintSpacing indent, "table ", id, "(", strJoin ", " dim, ") : ", ty])
end

lang TrellisProbabilityInModelDeclPrettyPrint =
  TrellisInModelDeclPrettyPrint + TrellisExprPrettyPrint

  syn ProbKind =
  | Initial
  | Output
  | Transition

  sem pprintTrellisInModelDecl indent env =
  | ProbInModelDecl {init = init, out = out, trans = trans,
                     fst = {v = fst}, snd = snd, pd = pd, info = info} ->
    let kind =
      match init with Some _ then Initial ()
      else match out with Some _ then Output ()
      else match trans with Some _ then Transition ()
      else errorSingle [info] "Invalid probability declaration"
    in
    match pprintVarName env fst with (env, fst) in
    match pprintProbDecl indent env pd with (env, pd) in
    match kind with Initial _ then
      (env, join [pprintSpacing indent, "P(initial ", fst, ") = ", pd])
    else
      let snd =
        match snd with Some {v = snd} then snd
        else errorSingle [info] "Invalid probability declaration"
      in
      match pprintVarName env snd with (env, snd) in
      match kind with Output _ then
        (env, join [pprintSpacing indent, "P(output ", fst, " | ", snd, ") = ", pd])
      else
        (env, join [pprintSpacing indent, "P(transition ", fst, " ", snd, ") = ", pd])

  sem pprintProbDecl : Int -> PprintEnv -> ProbDecl -> (PprintEnv, String)
  sem pprintProbDecl indent env =
  | OneProbDecl {e = e} -> pprintTrellisExpr env e
  | CasesProbDecl {cases = cases} ->
    let pprintCase = lam env. lam c.
      match c with {set = {v = id}, e = e} in
      match pprintVarName env id with (env, id) in
      match pprintTrellisExpr env e with (env, e) in
      (env, join ["| ", id, " -> ", e])
    in
    match mapAccumL pprintCase env cases with (env, cases) in
    let ii = pprintIncr indent in
    (env, join [ "{", pprintNewline ii, strJoin (pprintNewline ii) cases,
                 pprintNewline indent, "}" ])
end

lang TrellisDeclPrettyPrint = TrellisPrettyPrintBase
  sem pprintTrellisDecl : PprintEnv -> Decl -> (PprintEnv, String)
end

lang TrellisTypeDeclPrettyPrint = TrellisDeclPrettyPrint
  sem pprintTrellisDecl env =
  | TypeDecl {id = {v = id}, constr = constr} ->
    recursive let pprintConstrs = lam env. lam constr.
      switch constr
      case [] then (env, "")
      case [c] then pprintConName env c.v
      case [c] ++ rest then
        match pprintConName env c.v with (env, s) in
        match pprintConstrs env rest with (env, rest) in
        (env, join [s, ", ", rest])
      end
    in
    match pprintTypeName env id with (env, id) in
    match pprintConstrs env constr with (env, constr) in
    (env, join ["type ", id, " = {", constr, "}"])
end

lang TrellisLetDeclPrettyPrint =
  TrellisDeclPrettyPrint + TrellisTypePrettyPrint + TrellisExprPrettyPrint

  sem pprintTrellisDecl env =
  | LetDecl {id = {v = id}, ty = ty, e = e} ->
    match pprintVarName env id with (env, id) in
    match
      match ty with Some t then
        match pprintTrellisType env t with (env, t) in
        (env, join [" : ", t])
      else (env, "")
    with (env, tystr) in
    match pprintTrellisExpr env e with (env, e) in
    (env, join ["let ", id, tystr, " = ", e])
end

lang TrellisPrettyPrint =
  TrellisTypePrettyPrint + TrellisPatPrettyPrint + TrellisSetPrettyPrint +
  TrellisExprPrettyPrint +

  -- In-model declarations
  TrellisStatePropertyInModelDeclPrettyPrint +
  TrellisOutputPropertyInModelDeclPrettyPrint +
  TrellisSetInModelDeclPrettyPrint + TrellisTableInModelDeclPrettyPrint +
  TrellisProbabilityInModelDeclPrettyPrint +

  -- Declarations
  TrellisTypeDeclPrettyPrint + TrellisLetDeclPrettyPrint +

  -- Trellis AST
  TrellisAst

  sem pprintTrellis : TrellisProgram -> String
  sem pprintTrellis =
  | MainTrellisProgram {d = d, indecl = indecl} ->
    match mapAccumL pprintTrellisDecl pprintEnvEmpty d with (env, d) in
    match mapAccumL (pprintTrellisInModelDecl 2) env indecl with (_, indecl) in
    join [strJoin "\n" d, "\nmodel {\n", strJoin "\n" indecl, "\n}"]
end
