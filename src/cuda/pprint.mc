-- Pretty-printing of the CUDA extended parts of the AST. Extends the
-- pretty-printer from the C AST where applicable.

include "utest.mc"
include "c/pprint.mc"

include "ast.mc"

lang TrellisCudaPrettyPrint = TrellisCudaAst + CPrettyPrint
  sem printCType decl env =
  | CTyUChar _ -> (env, _joinSpace "unsigned char" decl)
  | CTyUShort _ -> (env, _joinSpace "unsigned short" decl)
  | CTyUInt _ -> (env, _joinSpace "unsigned int" decl)
  | CTyULongLong _ -> (env, _joinSpace "unsigned long long" decl)
  | CTyConst {ty = ty} ->
    match printCType decl env ty with (env, s) in
    (env, _joinSpace "const" s)
  | CTyEmpty _ -> (env, decl)

  sem printCExpr env =
  | CETernary {cond = cond, thn = thn, els = els} ->
    match printCExpr env cond with (env, cond) in
    match printCExpr env thn with (env, thn) in
    match printCExpr env els with (env, els) in
    (env, join [cond, " ? ", thn, " : ", els])

  sem printCTop indent env =
  | CTMacroDefine {id = id, value = value} ->
    match cPprintEnvGetStr env id with (env, id) in
    (env, join ["#define ", id, " ", value])

  -- New pretty-print functions for the CUDA-specific top-level declarations.
  sem printCudaAnnotation : CuAnnotation -> String
  sem printCudaAnnotation =
  | CuAHost () -> "__host__"
  | CuADevice () -> "__device__"
  | CuAGlobal () -> "__global__"

  sem printCudaTop : PprintEnv -> CuTop -> (PprintEnv, String)
  sem printCudaTop env =
  | {annotations = annot, top = ctop} ->
    let annots = strJoin " " (map printCudaAnnotation annot) in
    match printCTop 0 env ctop with (env, topstr) in
    (env, join [if null annots then annots else concat annots "\n", topstr])

  sem printCudaProgram : CuProgram -> String
  sem printCudaProgram =
  | {tops = tops} ->
    match mapAccumL printCudaTop pprintEnvEmpty tops with (_, tops) in
    strJoin "\n" tops
end

mexpr

use TrellisCudaPrettyPrint in

let ppstrs = lam l. lam r.
  let id = lam x. x in
  utestDefaultToString id id l r
in
let ppType = lam decl. lam ty.
  match printCType decl pprintEnvEmpty ty with (_, str) in
  str
in
let ppExpr = lam e.
  match printCExpr pprintEnvEmpty e with (_, str) in
  str
in
let ppTop = lam top.
  match printCudaTop pprintEnvEmpty top with (_, str) in
  str
in

let ty1 = CTyConst {ty = CTyInt ()} in
utest ppType "x" ty1 with "const int x" using eqString else ppstrs in

let ty2 = CTyConst {ty = CTyPtr {ty = CTyVoid ()}} in
utest ppType "x" ty2 with "const void (*x)" using eqString else ppstrs in

let ty3 = CTyEmpty () in
utest ppType "MACRO" ty3 with "MACRO" using eqString else ppstrs in

let ternary = CETernary {
  cond = CEBinOp {op = COEq (), lhs = CEVar {id = nameNoSym "a"}, rhs = CEInt {i = 2}},
  thn = CEInt {i = 1}, els = CEInt {i = 2}
} in
utest ppExpr ternary with "(a == 2) ? 1 : 2" using eqString else ppstrs in

let cutop = {
  annotations = [CuAHost (), CuADevice ()],
  top = CTFun {
    ret = CTyVar {id = nameNoSym "prob_t"},
    id = nameNoSym "init_prob",
    params = [
      (CTyVar {id = nameNoSym "state_t"}, nameNoSym "x"),
      (CTyEmpty (), nameNoSym "HMM_DECL_PARAMS")],
    body = [
      CSRet {val = Some (CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = nameNoSym "initp"},
        rhs = CEInt {i = 1}
      })}
    ]}
} in
utest ppTop cutop with
"__host__ __device__
prob_t init_prob(state_t x, HMM_DECL_PARAMS) {
  return (initp[1]);
}"
using eqString else ppstrs in

()
