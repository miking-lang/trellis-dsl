include "string.mc"
include "mexpr/pprint.mc"

include "ast.mc"
include "../trellis-common.mc"

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
  | TuplePTrellisPat {p = p} ->
    match mapAccumL pprintTrellisPat env p with (env, p) in
    (env, join ["(", strJoin ", " p, ")"])
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
  | ProbTrellisExpr {p = {v = p}} -> (env, float2string p)
  | ProjTrellisExpr {left = left, idx = {v = idx}} ->
    match pprintTrellisExpr env left with (env, left) in
    (env, join [left, "[", int2string idx, "]"])
  | TableAccessTrellisExpr {left = left, e = e} ->
    match pprintTrellisExpr env left with (env, left) in
    match mapAccumL pprintTrellisExpr env e with (env, e) in
    (env, join [left, "(", strJoin ", " e, ")"])
  | IfTrellisExpr {c = c, thn = thn, right = right} ->
    match pprintTrellisExpr env c with (env, c) in
    match pprintTrellisExpr env thn with (env, thn) in
    match pprintTrellisExpr env right with (env, right) in
    (env, join ["if ", c, " then ", thn, " else ", right])
  | AddTrellisExpr {left = left, right = right} ->
    pprintOp env left right "+"
  | SubTrellisExpr {left = left, right = right} ->
    pprintOp env left right "-"
  | MulTrellisExpr {left = left, right = right} ->
    pprintOp env left right "*"
  | DivTrellisExpr {left = left, right = right} ->
    pprintOp env left right "/"
  | EqTrellisExpr {left = left, right = right} ->
    pprintOp env left right "=="
  | NeqTrellisExpr {left = left, right = right} ->
    pprintOp env left right "!="
  | LtTrellisExpr {left = left, right = right} ->
    pprintOp env left right "<"
  | GtTrellisExpr {left = left, right = right} ->
    pprintOp env left right ">"
  | LeqTrellisExpr {left = left, right = right} ->
    pprintOp env left right "<="
  | GeqTrellisExpr {left = left, right = right} ->
    pprintOp env left right ">="
  | AndTrellisExpr {left = left, right = right} ->
    pprintOp env left right "&&"
  | OrTrellisExpr {left = left, right = right} ->
    pprintOp env left right "||"

  -- TODO(larshum, 2024-01-22): Take operator precedence into consideration
  -- when deciding where to insert parentheses, to reduce the amount of
  -- parentheses that we insert.
  sem pprintOp : PprintEnv -> TrellisExpr -> TrellisExpr -> String -> (PprintEnv, String)
  sem pprintOp env lhs rhs =
  | op ->
    match pprintTrellisExpr env lhs with (env, lhs) in
    match pprintTrellisExpr env rhs with (env, rhs) in
    (env, join ["(", lhs, " ", op, " ", rhs, ")"])
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
    (env, join ["(", strJoin ", " t, ")"])
  | IntRangeTrellisType {lb = {v = lb}, ub = ub, namedUb = namedUb, info = info} ->
    match
      match ub with Some {v = ub} then (env, int2string ub)
      else match namedUb with Some {v = id} then pprintVarName env id
      else errorSingle [info] "Invalid integer range type"
    with (env, upperBound) in
    (env, join [int2string lb, " .. ", upperBound])
  | BoolTrellisType _ -> (env, "Bool")
  | IntTTrellisType _ -> (env, "Int")
  | ProbTTrellisType _ -> (env, "Probability")
end

lang TrellisSetPrettyPrint =
  TrellisPrettyPrintBase + TrellisPatPrettyPrint + TrellisExprPrettyPrint

  sem pprintTrellisSet : PprintEnv -> TrellisSet -> (PprintEnv, String)
  sem pprintTrellisSet env =
  | BuilderTrellisSet {p = p, to = to, e = e, info = info} ->
    match pprintTrellisPat env p with (env, p) in
    match
      match to with Some to then
        match pprintTrellisPat env to with (env, to) in
        (env, concat " -> " to)
      else (env, "")
    with (env, to) in
    match mapAccumL pprintTrellisExpr env e with (env, e) in
    (env, join ["{", p, to, " | ", strJoin ", " e, "}"])
  | LiteralTrellisSet {v = v, info = info} ->
    let pprintSetElement = lam env. lam elem.
      match pprintTrellisExpr env elem.e with (env, e) in
      match
        match elem.to with Some to then
          match pprintTrellisExpr env to with (env, to) in
          (env, concat " -> " to)
        else (env, "")
      with (env, to) in
      (env, join [e, to])
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
  TrellisInModelDeclPrettyPrint + TrellisSetPrettyPrint

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
      match c with {s = s, e = e} in
      match pprintTrellisSet env s with (env, s) in
      match pprintTrellisExpr env e with (env, e) in
      (env, join ["| ", s, " => ", e])
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
  | LetDecl {id = {v = id}, e = e} ->
    match pprintVarName env id with (env, id) in
    match pprintTrellisExpr env e with (env, e) in
    (env, join ["let ", id, " = ", e])
end

lang TrellisAliasDeclPrettyPrint =
  TrellisDeclPrettyPrint + TrellisTypePrettyPrint

  sem pprintTrellisDecl env =
  | AliasDecl {id = {v = id}, ty = ty} ->
    match pprintTypeName env id with (env, id) in
    match pprintTrellisType env ty with (env, ty) in
    (env, join ["alias ", id, " = ", ty])
end

lang TrellisPrettyPrint =
  TrellisTypePrettyPrint + TrellisPatPrettyPrint + TrellisSetPrettyPrint +
  TrellisExprPrettyPrint +

  -- In-model declarations
  TrellisStatePropertyInModelDeclPrettyPrint +
  TrellisOutputPropertyInModelDeclPrettyPrint +
  TrellisTableInModelDeclPrettyPrint +
  TrellisProbabilityInModelDeclPrettyPrint +

  -- Declarations
  TrellisTypeDeclPrettyPrint + TrellisLetDeclPrettyPrint +
  TrellisAliasDeclPrettyPrint +

  -- Trellis AST
  TrellisAst

  sem pprintTrellis : TrellisProgram -> String
  sem pprintTrellis =
  | MainTrellisProgram {d = d, indecl = indecl} ->
    match mapAccumL pprintTrellisDecl pprintEnvEmpty d with (env, d) in
    match mapAccumL (pprintTrellisInModelDecl 2) env indecl with (_, indecl) in
    let d = join (map (lam x. concat x "\n") d) in
    join [d, "model {\n", strJoin "\n" indecl, "\n}"]
end

mexpr

use TrellisPrettyPrint in

let i = trellisInfo "trellis-parser-pprint" in
let x = nameNoSym "x" in
let y = nameNoSym "y" in
let a = nameNoSym "A" in
let b = nameNoSym "B" in

-- Patterns
let pprintPat = lam p.
  match pprintTrellisPat pprintEnvEmpty p with (_, s) in
  s
in

let conPat = ConTrellisPat {id = {i = i, v = a}, info = i} in
utest pprintPat conPat with "A" using eqString else ppStrings in

let varPat = VarPTrellisPat {id = {i = i, v = x}, info = i} in
utest pprintPat varPat with "x" using eqString else ppStrings in

let intPat = IntPTrellisPat {i = {i = i, v = 7}, info = i} in
utest pprintPat intPat with "7" using eqString else ppStrings in

let truePat = TruePTrellisPat {info = i} in
utest pprintPat truePat with "true" using eqString else ppStrings in

let falsePat = FalsePTrellisPat {info = i} in
utest pprintPat falsePat with "false" using eqString else ppStrings in

let emptyArrayPat = ArrayPTrellisPat {p = [], info = i} in
utest pprintPat emptyArrayPat with "[]" using eqString else ppStrings in
let singletonArrayPat = ArrayPTrellisPat {p = [intPat], info = i} in
utest pprintPat singletonArrayPat with "[7]" using eqString else ppStrings in
let dotsPat = DotsTrellisPat {
  left = VarPTrellisPat {id = {i = i, v = y}, info = i},
  info = i
} in
let dotsArrayPat = ArrayPTrellisPat {p = [varPat, dotsPat, intPat], info = i} in
utest pprintPat dotsArrayPat with "[x, y..., 7]" using eqString else ppStrings in

let tupPat = TuplePTrellisPat {p = [conPat, truePat, dotsArrayPat], info = i} in
utest pprintPat tupPat with "(A, true, [x, y..., 7])" using eqString else ppStrings in

-- Types
let pprintType = lam ty.
  match pprintTrellisType pprintEnvEmpty ty with (_, s) in
  s
in

let boolType = BoolTrellisType {info = i} in
utest pprintType boolType with "Bool" using eqString else ppStrings in

let intType = IntTTrellisType {info = i} in
utest pprintType intType with "Int" using eqString else ppStrings in

let probType = ProbTTrellisType {info = i} in
utest pprintType probType with "Probability" using eqString else ppStrings in

let concreteType = ConcreteTrellisType {id = {i = i, v = a}, info = i} in
utest pprintType concreteType with "A" using eqString else ppStrings in

let constIntRangeType = IntRangeTrellisType {
  lb = {i = i, v = 2}, ub = Some {i = i, v = 7}, namedUb = None (), info = i
} in
utest pprintType constIntRangeType with "2 .. 7" using eqString else ppStrings in

let namedIntRangeType = IntRangeTrellisType {
  lb = {i = i, v = 0}, ub = None (), namedUb = Some {i = i, v = x}, info = i
} in
utest pprintType namedIntRangeType with "0 .. x" using eqString else ppStrings in

let constArrayType = ArrayTTrellisType {
  left = constIntRangeType, count = Some {i = i, v = 3}, namedCount = None (), info = i
} in
utest pprintType constArrayType with "2 .. 7[3]" using eqString else ppStrings in

let namedArrayType = ArrayTTrellisType {
  left = boolType, count = None (), namedCount = Some {i = i, v = x}, info = i
} in
utest pprintType namedArrayType with "Bool[x]" using eqString else ppStrings in

let tupleType = TupleTTrellisType {
  t = [probType, constIntRangeType, namedArrayType], info = i
} in
utest pprintType tupleType with "(Probability, 2 .. 7, Bool[x])" using eqString else ppStrings in

-- Expressions
let pprintExpr = lam e.
  match pprintTrellisExpr pprintEnvEmpty e with (_, s) in
  s
in

let varExpr = VarTrellisExpr {id = {i = i, v = x}, info = i} in
utest pprintExpr varExpr with "x" using eqString else ppStrings in

let trueExpr = TrueTrellisExpr {info = i} in
utest pprintExpr trueExpr with "true" using eqString else ppStrings in

let probExpr = ProbTrellisExpr {p = {i = i, v = 0.5}, info = i} in
utest pprintExpr probExpr with "0.5" using eqString else ppStrings in

let gtExpr = GtTrellisExpr {left = varExpr, right = probExpr, info = i} in
utest pprintExpr gtExpr with "(x > 0.5)" using eqString else ppStrings in

let andExpr = AndTrellisExpr {left = gtExpr, right = varExpr, info = i} in
utest pprintExpr andExpr with "((x > 0.5) && x)" using eqString else ppStrings in

let arithExpr = AddTrellisExpr {
  left = MulTrellisExpr {
    left = VarTrellisExpr {id = {i = i, v = x}, info = i},
    right = IntTrellisExpr {i = {i = i, v = 5}, info = i},
    info = i
  },
  right = SubTrellisExpr {
    left = ProjTrellisExpr {
      left = VarTrellisExpr {id = {i = i, v = y}, info = i},
      idx = {i = i, v = 2}, info = i
    },
    right = IfTrellisExpr {
      c = EqTrellisExpr {
        left = TrueTrellisExpr {info = i},
        right = OrTrellisExpr {
          left = FalseTrellisExpr {info = i},
          right = LeqTrellisExpr {
            left = VarTrellisExpr {id = {i = i, v = x}, info = i},
            right = IntTrellisExpr {i = {i = i, v = 2}, info = i},
            info = i
          },
          info = i
        },
        info = i
      },
      thn = IntTrellisExpr {i = {i = i, v = 1}, info = i},
      right = IntTrellisExpr {i = {i = i, v = 2}, info = i},
      info = i
    },
    info = i
  },
  info = i
} in
utest pprintExpr arithExpr with "((x * 5) + (y[2] - if (true == (false || (x <= 2))) then 1 else 2))" using eqString else ppStrings in

-- Sets
let pprintSet = lam s.
  match pprintTrellisSet pprintEnvEmpty s with (_, s) in
  s
in

let builderSetValue = BuilderTrellisSet {
  p = varPat, to = None (), e = [trueExpr], info = i
} in
utest pprintSet builderSetValue with "{x | true}" using eqString else ppStrings in

let builderSetTransition = BuilderTrellisSet {
  p = varPat, to = Some varPat, e = [trueExpr], info = i
} in
utest pprintSet builderSetTransition with "{x -> x | true}" using eqString else ppStrings in

let multiCondBuilderSet = BuilderTrellisSet {
  p = varPat, to = Some varPat, e = [andExpr, gtExpr], info = i
} in
utest pprintSet multiCondBuilderSet with "{x -> x | ((x > 0.5) && x), (x > 0.5)}"
using eqString else ppStrings in

let patBuilderSet = BuilderTrellisSet {
  p = dotsArrayPat, to = Some tupPat, e = [trueExpr], info = i
} in
utest pprintSet patBuilderSet with "{[x, y..., 7] -> (A, true, [x, y..., 7]) | true}"
using eqString else ppStrings in

()
