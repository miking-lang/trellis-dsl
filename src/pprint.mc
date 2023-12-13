include "trellis.mc"

include "string.mc"
include "mexpr/pprint.mc"

lang TrellisPrettyPrintBase = MExprIdentifierPrettyPrint + TrellisBaseAst
  sem pprintExpr : PprintEnv -> ExprT -> (PprintEnv, String)
  sem pprintExpr env =
  | e -> errorSingle [get_ExprT_info e] "Unsupported expression"

  sem pprintType : PprintEnv -> TypeT -> (PprintEnv, String)
  sem pprintType env =
  | ty -> errorSingle [get_TypeT_info ty] "Unsupported type"

  sem pprintPat : PprintEnv -> PatT -> (PprintEnv, String)
  sem pprintPat env =
  | p -> errorSingle [get_PatT_info p] "Unsupported pattern"

  sem pprintSet : PprintEnv -> SetT -> (PprintEnv, String)
  sem pprintSet env =
  | s -> errorSingle [get_SetT_info s] "Unsupported set"

  sem pprintParam : PprintEnv -> Param -> (PprintEnv, String)
  sem pprintParam env =
  | p -> errorSingle [get_Param_info p] "Unsupported parameter"

  sem pprintConstrDecl : PprintEnv -> ConstrDecl -> (PprintEnv, String)
  sem pprintConstrDecl env =
  | cd -> errorSingle [get_ConstrDecl_info cd] "Unsupported constructor declaration"

  sem pprintAutomatonProp : PprintEnv -> AutomatonProp -> (PprintEnv, String)
  sem pprintAutomatonProp env =
  | ap -> errorSingle [get_AutomatonProp_info ap] "Unsupported automaton property"

  sem pprintModelComposition : PprintEnv -> ModelComposition -> (PprintEnv, String)
  sem pprintModelComposition env =
  | mc -> errorSingle [get_ModelComposition_info mc] "Unsupported model composition"

  sem pprintInModelDecl : PprintEnv -> InModelDecl -> (PprintEnv, String)
  sem pprintInModelDecl env =
  | md -> errorSingle [get_InModelDecl_info md] "Unsupported in-model declaration"

  sem pprintDecl : PprintEnv -> Decl -> (PprintEnv, String)
  sem pprintDecl env =
  | d -> errorSingle [get_Decl_info d] "Unsupported declaration"

  sem pprintTop : PprintEnv -> Top -> (PprintEnv, String)
  sem pprintTop env =
  | t -> errorSingle [get_Top_info t] "Unsupported top"
end

lang TrellisExprPrettyPrint =
  TrellisPrettyPrintBase + ApplicationExprTAst + PlusExprTAst + MinusExprTAst +
  MultipliedWithExprTAst + DividedByExprTAst + ProjectionAccessExprTAst +
  EqualExprTAst + NotEqualExprTAst + LessThanExprTAst + GreaterThanExprTAst +
  LessThanOrEqualExprTAst + GreaterThanOrEqualExprTAst + AndExprTAst +
  OrExprTAst + ArrayAccessExprTAst + IfExprTAst + InExprTAst + NotinExprTAst +
  UnionExprTAst + IntersectionExprTAst + SetMinusExprTAst + OutputExprTAst +
  TrueExprTAst + FalseExprTAst + VariableExprTAst + ConstructorExprTAst +
  IntegerExprTAst + SubSeqExprTAst + ArrayExprTAst + TupleExprTAst

  sem pprintExpr : PprintEnv -> ExprT -> (PprintEnv, String)
  sem pprintExpr env =
  | ApplicationExprT {left = left, a = a} ->
    match pprintExpr env left with (env, left) in
    match mapAccumL pprintExpr env a with (env, a) in
    (env, join [left, "(", strJoin ", " a, ")"])
  | PlusExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " + ", right])
  | MinusExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " - ", right])
  | MultipliedWithExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " * ", right])
  | DividedByExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " / ", right])
  | ProjectionAccessExprT {left = left, label = label, count = count, info = info} ->
    match pprintExpr env left with (env, left) in
    match label with Some l then
      (env, join [left, ".", l.v])
    else match count with Some c then
      (env, join [left, ".", int2string c.v])
    else errorSingle [info] "Invalid projection access expression"
  | EqualExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " == ", right])
  | NotEqualExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " != ", right])
  | LessThanExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " < ", right])
  | GreaterThanExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " > ", right])
  | LessThanOrEqualExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " <= ", right])
  | GreaterThanOrEqualExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " >= ", right])
  | AndExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " && ", right])
  | OrExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " || ", right])
  | ArrayAccessExprT {left = left, e = e} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env e with (env, e) in
    (env, join [left, "[", e, "]"])
  | IfExprT {c = c, e = e, right = right} ->
    match pprintExpr env c with (env, c) in
    match pprintExpr env e with (env, e) in
    match pprintExpr env right with (env, right) in
    (env, join ["if ", c, " then ", e, " else ", right])
  | InExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " \\in ", right])
  | NotinExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " \\notin ", right])
  | UnionExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " \\u ", right])
  | IntersectionExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " \\n ", right])
  | SetMinusExprT {left = left, right = right} ->
    match pprintExpr env left with (env, left) in
    match pprintExpr env right with (env, right) in
    (env, join [left, " \\setminus ", right])
  | OutputExprT _ -> (env, "output")
  | TrueExprT _ -> (env, "true")
  | FalseExprT _ -> (env, "false")
  | VariableExprT {v = v} -> pprintVarName env v.v
  | ConstructorExprT {c = c} -> pprintConName env c.v
  | IntegerExprT {i = i} -> (env, int2string i.v)
  | SubSeqExprT {left = left} ->
    match pprintExpr env left with (env, left) in
    (env, join [left, "..."])
  | ArrayExprT {e = e} ->
    match mapAccumL pprintExpr env e with (env, e) in
    (env, join ["[", strJoin ", " e, "]"])
  | TupleExprT {e = e} ->
    match mapAccumL pprintExpr env e with (env, e) in
    (env, join ["@(", strJoin ", " e, ")"])
end

lang TrellisPatPrettyPrint =
  TrellisPrettyPrintBase + ConPatTAst + VarPatTAst + WildPatTAst +
  DotsPatTAst + ArrayPatTAst + TupPatTAst + IntPatTAst + TruePatTAst +
  FalsePatTAst

  sem pprintPat : PprintEnv -> PatT -> (PprintEnv, String)
  sem pprintPat env =
  | ConPatT {c = c, p = p} ->
    match mapAccumL pprintPat env p with (env, p) in
    (env, join [c.v, "(", strJoin ", " p, ")"])
  | VarPatT {id = id} -> (env, id.v)
  | WildPatT _ -> (env, "_")
  | DotsPatT {left = left} ->
    match pprintPat env left with (env, left) in
    (env, concat left "...")
  | ArrayPatT {p = p} ->
    match mapAccumL pprintPat env p with (env, p) in
    (env, join ["[", strJoin ", " p, "]"])
  | TupPatT {p = p} ->
    match mapAccumL pprintPat env p with (env, p) in
    (env, join ["@(", strJoin ", " p, ")"])
  | IntPatT {i = i} -> (env, int2string i.v)
  | TruePatT _ -> (env, "true")
  | FalsePatT _ -> (env, "false")
end

lang TrellisSetPrettyPrint =
  TrellisExprPrettyPrint + TrellisPatPrettyPrint + SetUnionSetTAst +
  SetIntersectionSetTAst + SetTMinusSetTAst + NamedSetSetTAst + SetLitSetTAst +
  SetBuilderSetTAst + SetProjectionSetTAst

  sem pprintSet : PprintEnv -> SetT -> (PprintEnv, String)
  sem pprintSet env =
  | SetUnionSetT {left = left, right = right} ->
    match pprintSet env left with (env, left) in
    match pprintSet env right with (env, right) in
    (env, join [left, " \\u ", right])
  | SetIntersectionSetT {left = left, right = right} ->
    match pprintSet env left with (env, left) in
    match pprintSet env right with (env, right) in
    (env, join [left, " \\n ", right])
  | SetTMinusSetT {left = left, right = right} ->
    match pprintSet env left with (env, left) in
    match pprintSet env right with (env, right) in
    (env, join [left, " \\setminus ", right])
  | NamedSetSetT {name = name} -> (env, name.v)
  | SetLitSetT {mapping = mapping} ->
    let pprintMapping = lam env. lam m.
      match m with {e = e, to = to} in
      match pprintExpr env e with (env, e) in
      match
        match to with Some to then
          match pprintExpr env to with (env, to) in
          (env, join [" -> ", to])
        else (env, "")
      with (env, tostr) in
      (env, join [e, tostr])
    in
    match mapAccumL pprintMapping env mapping with (env, m) in
    (env, join ["{", strJoin ", " m, "}"])
  | SetBuilderSetT {p = p, to = to, e = e} ->
    match pprintPat env p with (env, p) in
    match
      match to with Some to then
        match pprintPat env to with (env, p) in
        (env, join [" -> ", p])
      else (env, "")
    with (env, tostr) in
    match mapAccumL pprintExpr env e with (env, e) in
    (env, join ["@{", p, tostr, " | ", strJoin ", " e, "}"])
  | SetProjectionSetT {left = left, lbl = lbl} ->
    match pprintSet env left with (env, left) in
    (env, join [left, ".", lbl.v])
end

lang TrellisTypePrettyPrint =
  TrellisExprPrettyPrint + TypeVarTypeTAst + ArrayTypeTAst + ConcreteTypeTAst +
  TupleTypeTAst + IntegerTypeTAst + BoolTypeTAst + IntTypeTAst +
  AutomatonStateTypeTAst

  sem pprintType : PprintEnv -> TypeT -> (PprintEnv, String)
  sem pprintType env =
  | TypeVarTypeT {n = n} -> pprintVarName env n.v
  | ArrayTypeT {left = left, count = count} ->
    match pprintType env left with (env, left) in
    match pprintExpr env count with (env, count) in
    (env, join [left, "[", count, "]"])
  | ConcreteTypeT {n = n, a = a} ->
    match pprintTypeName env n.v with (env, v) in
    match
      if null a then (env, "")
      else
        match mapAccumL pprintType env a with (env, a) in
        (env, join ["(", strJoin ", " a, ")"])
    with (env, str) in
    (env, join [v, str])
  | TupleTypeT {t = t} ->
    match mapAccumL pprintType env t with (env, t) in
    (env, join ["@(", strJoin ", " t, ")"])
  | IntegerTypeT {lb = lb, ub = ub, namedUb = namedUb, v = v} ->
    let pprintInner = lam env. lam ub. lam namedUb.
      match ub with Some {v = ubv} then
        (env, int2string ubv)
      else match namedUb with Some {v = nubv} then
        pprintVarName env nubv
      else error "Invalid integer range type"
    in
    let lb = int2string lb.v in
    match v with Some {v = v} then
      match pprintVarName env v with (env, v) in
      match pprintInner env ub namedUb with (env, innerV) in
      (env, join [lb, " <= ", v, " <= ", innerV])
    else
      match pprintInner env ub namedUb with (env, v) in
      (env, join [lb, "..", v])
  | BoolTypeT _ -> (env, "Bool")
  | IntTypeT _ -> (env, "Int")
  | AutomatonStateTypeT {automaton = a} ->
    match pprintVarName env a.v with (env, a) in
    (env, join ["state(", a, ")"])
end

lang TrellisParamPrettyPrint = TrellisTypePrettyPrint + ParamAst

  sem pprintParam : PprintEnv -> Param -> (PprintEnv, String)
  sem pprintParam env =
  | Param1 {n = n, ty = ty} ->
    match pprintType env ty with (env, ty) in
    (env, join [n.v, " : ", ty])
end

lang TrellisConstrDeclPrettyPrint = TrellisTypePrettyPrint + ConstrDeclAst

  sem pprintConstrDecl : PprintEnv -> ConstrDecl -> (PprintEnv, String)
  sem pprintConstrDecl env =
  | ConstrDecl1 {vName = n, param = p} ->
    match
      if null p then (env, "")
      else
        match mapAccumL pprintType env p with (env, params) in
        (env, join ["(", strJoin ", " params, ")"])
    with (env, params) in
    (env, join [nameGetStr n.v, params])
end

lang TrellisAutomatonPropPrettyPrint =
  TrellisSetPrettyPrint + StatePropAutomatonPropAst + SetPropAutomatonPropAst

  sem pprintAutomatonProp : PprintEnv -> AutomatonProp -> (PprintEnv, String)
  sem pprintAutomatonProp env =
  | StatePropAutomatonProp {ty = ty} ->
    match pprintType env ty with (env, ty) in
    (env, join ["state: ", ty])
  | SetPropAutomatonProp {name = name, initial = init, s = s} ->
    match
      match name with Some n then
        (env, n.v)
      else match init with Some _ then
        (env, "initial")
      else error "Invalid automaton property"
    with (env, initstr) in
    match pprintSet env s with (env, s) in
    (env, join [initstr, ": ", s])
end

lang TrellisModelCompositionPrettyPrint =
  TrellisPrettyPrintBase + ModelAtomModelCompositionAst + ModelNestingModelCompositionAst

  sem pprintModelComposition : PprintEnv -> ModelComposition -> (PprintEnv, String)
  sem pprintModelComposition env =
  | ModelAtomModelComposition {name = name, automaton = a} ->
    (env, join [name.v, " : ", a.v])
  | ModelNestingModelComposition {mc = mc} ->
    match pprintModelComposition env mc with (env, mc) in
    (env, join ["(", mc, ")"])
end

lang TrellisInModelDeclPrettyPrint =
  TrellisSetPrettyPrint + InferredFunctionInModelDeclAst + ProbInModelDeclAst

  sem pprintInModelDecl : PprintEnv -> InModelDecl -> (PprintEnv, String)
  sem pprintInModelDecl env =
  | InferredFunctionInModelDecl {f = f, p = p, ret = ret} ->
    match mapAccumL pprintType env p with (env, p) in
    match
      match ret with Some ty then
        match pprintType env ty with (env, ty) in
        (env, concat ": " ty)
      else (env, "")
    with (env, retstr) in
    (env, join ["table ", f.v, "(", strJoin ", " p, ")", retstr])
  | ProbInModelDecl {
      output = o, s = s, initial = init, transition = tr, from = from, to = to,
      e = e, cases = cases, info = info
    } ->
    let pprintCase = lam env. lam c.
      match c with {set = set, e2 = e2} in
      match pprintSet env set with (env, set) in
      match pprintExpr env e2 with (env, e2) in
      (env, join ["| ", set, " => ", e2])
    in
    match
      match (o, s) with (Some _, Some sid) then
        (env, concat "output | " sid.v)
      else match (init, s) with (Some _, Some sid) then
        (env, concat "initial " sid.v)
      else match (tr, from, to) with (Some _, Some from, Some to) then
        (env, join ["transition ", from.v, " ", to.v])
      else errorSingle [info] "Invalid probabilistic specification"
    with (env, pstr) in
    match
      match e with Some e then
        match pprintExpr env e with (env, e) in
        (env, join ["= ", e])
      else
        match mapAccumL pprintCase env cases with (env, cases) in
        let cases = join (map (lam c. join ["    ", c, "\n"]) cases) in
        (env, join ["{\n", cases, "  }"])
    with (env, tailstr) in
    (env, join ["P(", pstr, ") ", tailstr])
end

lang TrellisDeclPrettyPrint =
  TrellisTypePrettyPrint + TrellisExprPrettyPrint + TrellisParamPrettyPrint +
  TrellisConstrDeclPrettyPrint + TrellisAutomatonPropPrettyPrint +
  TrellisModelCompositionPrettyPrint + TrellisInModelDeclPrettyPrint +
  TypeDeclAst + AutomatonDeclAst + FuncDeclAst + ModelDeclAst

  sem pprintDecl : PprintEnv -> Decl -> (PprintEnv, String)
  sem pprintDecl env =
  | TypeDecl {name = n, param = p, v = v} ->
    let params =
      if null p then ""
      else join ["(", strJoin ", " (map (lam x. nameGetStr x.v) p), ")"]
    in
    match mapAccumL pprintConstrDecl env v with (env, decls) in
    let constrDecls = strJoin ", " decls in
    (env, join ["type ", nameGetStr n.v, params, " {", constrDecls, "}"])
  | AutomatonDecl {name = n, prop = prop} ->
    match mapAccumL pprintAutomatonProp env prop with (env, props) in
    let props = join (map (lam p. join ["  ", p, ",\n"]) props) in
    (env, join ["automaton ", nameGetStr n.v, " {\n", props, "}"])
  | FuncDecl {fname = n, p = p, ty = ty, e = e} ->
    match
      if null p then (env, "")
      else
        match mapAccumL pprintParam env p with (env, p) in
        (env, join ["(", strJoin ", " p, ") "])
    with (env, params) in
    match
      match ty with Some ty then
        match pprintType env ty with (env, ty) in
        (env, join [": ", ty, " "])
      else
        (env, "")
    with (env, ty) in
    match pprintExpr env e with (env, e) in
    (env, join ["let ", n.v, params, ty, " = ", e])
  | ModelDecl {name = n, mc = mc, indecl = indecl} ->
    match pprintConName env n.v with (env, n) in
    match pprintModelComposition env mc with (env, mc) in
    match mapAccumL pprintInModelDecl env indecl with (env, indecl) in
    (env, join ["model ", n, " = ", mc, " {\n", join (map (lam s. join ["  ", s, "\n"]) indecl), "}"])
end

lang TrellisTopPrettyPrint =
  TrellisDeclPrettyPrint + TopAst

  sem pprintTop : PprintEnv -> Top -> (PprintEnv, String)
  sem pprintTop env =
  | Top1 {d = d} ->
    match mapAccumL pprintDecl env d with (env, d) in
    (env, strJoin "\n" d)
end

lang TrellisPrettyPrint = TrellisTopPrettyPrint
  sem pprintTrellis : Top -> String
  sem pprintTrellis =
  | p -> match pprintTop pprintEnvEmpty p with (_, p) in p
end
