-- Defines a bi-directional mapping between states and integers. The interface
-- consists of a function `cardinality` for computing the size of a type in a
-- given environment (at compile-time) and two functions for generating MExpr
-- code to convert a state to an integer (`stateToInt`) and (`intToState`) in a
-- given environment. The functions fail at compile-time if the size of a type
-- is unknown or infinite.
--
-- Before making use of these functions, all uses of names or expressions
-- within types (array sizes and upper bounds of integers) should be resolved
-- to constant values.

include "trellis.mc"
include "trellis-common.mc"

include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/eval.mc"
include "mexpr/pprint.mc"

lang Enumerate = TrellisBaseAst + MExprAst
  type EnumerateEnv = {
    -- Maps a concrete type to its parameters and the constructors with
    -- parameters.
    concreteTypes : Map Name ([Name], Map Name [TypeT]),

    -- Maps currently bound type variables to their concrete types.
    typeVars : Map Name TypeT,

    -- Maps bound names to the name of a concrete automaton type.
    automatons : Map Name Name,

    -- Maps an automaton to the type of its state.
    automatonStates : Map Name TypeT
  }

  sem enumerateEnvEmpty : () -> EnumerateEnv
  sem enumerateEnvEmpty =
  | () ->
    { concreteTypes = mapEmpty nameCmp
    , typeVars = mapEmpty nameCmp
    , automatons = mapEmpty nameCmp
    , automatonStates = mapEmpty nameCmp }

  -- Statically computes the number of possible values of a given type, or
  -- fails if the type is infinite.
  sem cardinality : EnumerateEnv -> TypeT -> Int

  -- Returns an MExpr expression which converts the state contained in the
  -- provided name to an integer value, assuming it has the provided type.
  -- The resulting integer is always strictly less than the cardinality of the
  -- type.
  sem stateToInt : EnumerateEnv -> Name -> TypeT -> Expr

  -- Returns an MExpr expression converting the integer stored in the provided
  -- name to a state it is assumed to encode. This integer must be strictly
  -- less than the cardinality of the type.
  sem intToState : EnumerateEnv -> Name -> TypeT -> Expr

  sem stateToIntTuple : EnumerateEnv -> Name -> [TypeT] -> Expr
  sem stateToIntTuple env target =
  | [] -> int_ 0
  | types ->
    let products = lam acc. lam x.
      let y = muli acc x in
      (y, y)
    in
    let cards = map (cardinality env) types in
    let ids = create (length types) (lam. nameSym "n") in
    let s = map (lam x. stateToInt env x.0 x.1) (zip ids types) in
    match mapAccumL products 1 cards with (_, prods) in
    let thn =
      foldl (lam acc. lam x.
        match x with (prod, s) in
        addi_ acc (mulLitExpr s prod))
      (head s) (zip prods (tail s))
    in
    match_ (nvar_ target) (ptuple_ (map npvar_ ids)) thn never_

  sem intToStateTuple : EnumerateEnv -> Name -> [TypeT] -> Expr
  sem intToStateTuple env target =
  | types ->
    let cards = map (cardinality env) types in
    let ids = create (length types) (lam. nameSym "n") in
    let i = map (lam x. (x.0, intToState env x.0 x.1)) (zip ids types) in
    let src = nvar_ target in
    match
      mapAccumL
        (lam acc. lam x.
          match x with (card, (id, i2s)) in
          let divAcc = divLitExpr src acc in
          let e = bind_ (nulet_ id (modi_ divAcc (int_ card))) i2s in
          (muli acc card, e))
        1 (zip cards i)
    with (_, elems) in
    utuple_ elems

  sem prod : [Int] -> Int
  sem prod = | s -> foldl muli 1 s

  -- NOTE(larshum, 2023-12-18): We use the utility functions below to avoid
  -- introducing unnecessary arithmetic operations without cluttering the code.
  sem addLitExpr : Expr -> Int -> Expr
  sem addLitExpr e =
  | 0 -> e
  | n -> addi_ e (int_ n)

  sem subLitExpr : Expr -> Int -> Expr
  sem subLitExpr e =
  | 0 -> e
  | n -> subi_ e (int_ n)

  sem mulLitExpr : Expr -> Int -> Expr
  sem mulLitExpr e =
  | 0 -> int_ 0
  | 1 -> e
  | n -> muli_ e (int_ n)

  sem divLitExpr : Expr -> Int -> Expr
  sem divLitExpr e =
  | 0 -> error "Attempted division by zero"
  | 1 -> e
  | n -> divi_ e (int_ n)
end

lang TypeVarTypeEnumerate = Enumerate + TypeVarTypeTAst
  sem resolveTypeVar : EnumerateEnv -> TypeT -> TypeT
  sem resolveTypeVar env =
  | TypeVarTypeT {n = {v = n}, info = info} ->
    optionGetOrElse (lam. errorNameUnbound info n) (mapLookup n env.typeVars)

  sem cardinality env =
  | (TypeVarTypeT _) & t -> cardinality env (resolveTypeVar env t)

  sem stateToInt env state =
  | (TypeVarTypeT _) & t -> stateToInt env state (resolveTypeVar env t)

  sem intToState env intVal =
  | (TypeVarTypeT _) & t -> intToState env intVal (resolveTypeVar env t)
end

lang ArrayTypeEnumerate = Enumerate + ArrayTypeTAst + IntegerExprTAst
  sem getArraySize : Info -> ExprT -> Int
  sem getArraySize info =
  | IntegerExprT {i = {v = count}} -> count
  | _ -> errorSingle [info] "Array unknown size at compile-time"

  sem cardinality env =
  | ArrayTypeT t ->
    let count = getArraySize t.info t.count in
    powi (cardinality env t.left) count

  sem stateToInt env state =
  | ArrayTypeT t ->
    let count = getArraySize t.info t.count in
    stateToIntTuple env state (make count t.left)

  sem intToState env intVal =
  | ArrayTypeT t ->
    let count = getArraySize t.info t.count in
    intToStateTuple env intVal (make count t.left)
end

lang ConcreteTypeEnumerate = Enumerate + ConcreteTypeTAst
  sem constructorCardinality : Info -> EnumerateEnv -> [TypeT] -> Int
  sem constructorCardinality info env =
  | params -> foldl (lam acc. lam ty. muli acc (cardinality env ty)) 1 params

  sem bindConstrTypeArgs : EnumerateEnv -> [Name] -> [TypeT] -> EnumerateEnv
  sem bindConstrTypeArgs env paramNames =
  | types ->
    { env with typeVars =
        foldl2
          (lam acc. lam p. lam ty. mapInsert p ty acc)
          env.typeVars paramNames types }

  sem cardinality env =
  | ConcreteTypeT {n = {v = n}, a = typeArgs, info = info} ->
    match mapLookup n env.concreteTypes with Some (params, constr) then
      let env = bindConstrTypeArgs env params typeArgs in
      -- NOTE(larshum, 2023-12-18): The cardinality of a constructor type is
      -- the sum of the cardinalities of its constructors.
      mapFoldWithKey
        (lam acc. lam. lam params.
          addi acc (constructorCardinality info env params))
        0 constr
    else errorNameUnbound info n

  sem stateToIntConstr : EnumerateEnv -> Name -> (Int, Expr) -> Name -> [TypeT]
                      -> (Int, Expr)
  sem stateToIntConstr env state acc constrId =
  | paramTypes ->
    match acc with (offset, accExpr) in
    let n = nameSym "n" in
    match
      match paramTypes with [] then
        (addi offset 1, int_ offset)
      else match paramTypes with [paramTy] then
        -- NOTE(larshum, 2023-12-18): We special-case on when the constructor has
        -- exactly one argument, because in that case, the argument is inlined
        -- in MExpr. In other cases, we convert it to an MExpr constructor
        -- taking a tuple argument (with one entry per parameter).
        (cardinality env paramTy, addLitExpr (stateToInt env n paramTy) offset)
      else
        let newOffset = addi offset (prod (map (cardinality env) paramTypes)) in
        (newOffset, addLitExpr (stateToIntTuple env n paramTypes) offset)
    with (newOffset, e) in
    let newExpr = match_ (nvar_ state) (npcon_ constrId (npvar_ n)) e accExpr in
    (newOffset, newExpr)

  sem stateToInt env state =
  | ConcreteTypeT {n = {v = n}, a = typeArgs, info = info} ->
    match mapLookup n env.concreteTypes with Some (params, constr) then
      let env = bindConstrTypeArgs env params typeArgs in
      match mapFoldWithKey (stateToIntConstr env state) (0, never_) constr with (_, e) in
      e
    else errorNameUnbound info n

  sem intToStateConstr : EnumerateEnv -> Name -> Info -> Int -> Name -> [TypeT]
                      -> (Int, Expr -> Expr)
  sem intToStateConstr env intVal info offset constrId =
  | paramTypes ->
    let n = nameSym "n" in
    match
      match paramTypes with [] then
        (addi offset 1, intToStateTuple env n [])
      else match paramTypes with [paramTy] then
        -- NOTE(larshum, 2023-12-18): As above, we assume the structure of the
        -- resulting expression is different in case the constructor takes one
        -- argument.
        let card = cardinality env paramTy in
        (addi offset card, intToState env n paramTy)
      else
        let newOffset = addi offset (prod (map (cardinality env) paramTypes)) in
        (newOffset, intToStateTuple env n paramTypes)
    with (newOffset, e) in
    let conApp = TmConApp {
      ident = constrId, body = e, ty = TyUnknown {info = info}, info = info
    } in
    let thnBody =
      if null paramTypes then conApp
      else
        bind_ (nulet_ n (subLitExpr (nvar_ intVal) offset)) conApp
    in
    let newExpr = lam els.
      if_ (lti_ (nvar_ intVal) (int_ newOffset)) thnBody els
    in
    (newOffset, newExpr)

  sem intToState env intVal =
  | ConcreteTypeT {n = {v = n}, a = typeArgs, info = info} ->
    match mapLookup n env.concreteTypes with Some (params, constr) then
      let env = bindConstrTypeArgs env params typeArgs in
      match mapMapAccum (intToStateConstr env intVal info) 0 constr
      with (_, constrConds) in
      foldr
        (lam condExpr. lam acc. condExpr acc)
        never_ (mapValues constrConds)
    else errorNameUnbound info n
end

lang TupleTypeEnumerate = Enumerate + TupleTypeTAst
  sem cardinality env =
  | TupleTypeT t -> prod (map (cardinality env) t.t)

  sem stateToInt env state =
  | TupleTypeT t -> stateToIntTuple env state t.t

  sem intToState env intVal =
  | TupleTypeT t -> intToStateTuple env intVal t.t
end

lang IntegerTypeEnumerate = Enumerate + IntegerTypeTAst
  sem cardinality env =
  | IntegerTypeT {lb = {v = lb}, ub = Some {v = ub}, namedUb = None _} ->
    addi (subi ub lb) 1
  | IntegerTypeT (t & {ub = None _, namedUb = Some _}) ->
    errorSingle [t.info] "Cannot determine cardinality of integer with named upper bound"
  | IntegerTypeT t -> errorSingle [t.info] "Invalid integer type"

  sem stateToInt env state =
  | IntegerTypeT {lb = {v = lb}} -> subLitExpr (nvar_ state) lb

  sem intToState env intVal =
  | IntegerTypeT {lb = {v = lb}} -> addLitExpr (nvar_ intVal) lb
end

lang BoolTypeEnumerate = Enumerate + BoolTypeTAst
  sem cardinality env =
  | BoolTypeT _ -> 2

  sem stateToInt env state =
  | BoolTypeT _ ->
    if_ (nvar_ state) (int_ 1) (int_ 0)

  sem intToState env intVal =
  | BoolTypeT _ ->
    eqi_ (nvar_ intVal) (int_ 1)
end

lang IntTypeEnumerate = Enumerate + IntTypeTAst
  sem cardinality env =
  | IntTypeT t -> errorSingle [t.info] "Infinite type found in cardinality"

  sem stateToInt env state =
  | IntTypeT t -> errorSingle [t.info] "Infinite type found in stateToInt"

  sem intToState env intVal =
  | IntTypeT t -> errorSingle [t.info] "Infinite type found in intToState"
end

lang AutomatonStateEnumerate = Enumerate + AutomatonStateTypeTAst
  sem automatonLookup : EnumerateEnv -> Info -> Name -> TypeT
  sem automatonLookup env info =
  | id ->
    match mapLookup id env.automatons with Some a then
      match mapLookup a env.automatonStates with Some ty then
        ty
      else
        errorSingle [info]
          (join [nameGetStr id, " refers to an unknown automaton ", nameGetStr a])
    else errorNameUnbound info id

  sem cardinality env =
  | AutomatonStateTypeT {automaton = {i = info, v = id}} ->
    cardinality env (automatonLookup env info id)

  sem stateToInt env state =
  | AutomatonStateTypeT {automaton = {i = info, v = id}} ->
    stateToInt env state (automatonLookup env info id)

  sem intToState env intVal =
  | AutomatonStateTypeT {automaton = {i = info, v = id}} ->
    intToState env intVal (automatonLookup env info id)
end

lang TrellisEnumerate =
  TypeVarTypeEnumerate + ArrayTypeEnumerate + ConcreteTypeEnumerate +
  TupleTypeEnumerate + IntegerTypeEnumerate + BoolTypeEnumerate +
  IntTypeEnumerate + AutomatonStateEnumerate
end

lang Test =
  TrellisEnumerate + TrellisAst + MExprEval + MExprEq + MExprPrettyPrint
end

mexpr

use Test in

-- Type AST builder functions
let tyBool = lam. BoolTypeT {bool = NoInfo (), info = NoInfo ()} in
let tyInteger = lam lb. lam ub.
  IntegerTypeT {
    lb = {i = NoInfo (), v = lb}, ub = Some {i = NoInfo (), v = ub},
    namedUb = None (), v = None (), info = NoInfo () }
in
let tyTuple = lam types.
  TupleTypeT {t = types, info = NoInfo ()}
in
let tyArray = lam ty. lam count.
  ArrayTypeT {
    left = ty, info = NoInfo (),
    count = IntegerExprT {i = {i = NoInfo (), v = count}, info = NoInfo ()} }
in
let tyConcrete = lam n. lam a.
  ConcreteTypeT {n = {i = NoInfo (), v = n}, a = a, info = NoInfo ()}
in
let tyVar = lam n.
  TypeVarTypeT {n = {i = NoInfo (), v = n}, info = NoInfo ()}
in
let tyAutomatonState = lam n.
  AutomatonStateTypeT {automaton = {i = NoInfo (), v = n}, info = NoInfo ()}
in

-- Helper functions and aliases
let env = enumerateEnvEmpty () in
let test = lam f. lam e. lam t.
  let n = nameSym "n" in
  let e = bind_ (nulet_ n e) (f n t) in
  eval {env = evalEnvEmpty ()} e
in
let stateToIntTest = lam env. test (stateToInt env) in
let intToStateTest = lam env. test (intToState env) in
let idTest = lam env. lam e. lam t.
  let n1 = nameSym "n" in
  let n2 = nameSym "n" in
  let res = eval {env = evalEnvEmpty ()} (bindall_ [
    nulet_ n1 e,
    nulet_ n2 (stateToInt env n1 t),
    intToState env n2 t
  ]) in
  eqExpr e res
in

let sum = lam s. foldl addi 0 s in
let ppExprs = lam l. lam r.
  join [ "LHS:\n", expr2str l, "\nRHS:\n", expr2str r ]
in

----------
-- BOOL --
----------

utest cardinality env (tyBool ()) with 2 in

utest stateToIntTest env false_ (tyBool ()) with int_ 0 using eqExpr else ppExprs in
utest stateToIntTest env true_ (tyBool ()) with int_ 1 using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) (tyBool ()) with false_ using eqExpr else ppExprs in
utest intToStateTest env (int_ 1) (tyBool ()) with true_ using eqExpr else ppExprs in
utest idTest env true_ (tyBool ()) with true in

----------------------
-- BOUNDED INTEGERS --
----------------------

utest cardinality env (tyInteger 1 2) with 2 in
utest cardinality env (tyInteger 0 10) with 11 in

utest stateToIntTest env (int_ 7) (tyInteger 0 10) with int_ 7 using eqExpr else ppExprs in
utest stateToIntTest env (int_ 17) (tyInteger 10 20) with int_ 7 using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) (tyInteger 1 1) with int_ 1 using eqExpr else ppExprs in
utest intToStateTest env (int_ 7) (tyInteger 10 20) with int_ 17 using eqExpr else ppExprs in
utest idTest env (int_ 2) (tyInteger 0 10) with true in

------------
-- TUPLES --
------------

utest cardinality env (tyTuple []) with 1 in
utest cardinality env (tyTuple [tyBool ()]) with 2 in
utest cardinality env (tyTuple [tyBool (), tyBool ()]) with 4 in
utest cardinality env (tyTuple [tyTuple [tyBool ()], tyTuple [tyInteger 1 10]]) with 20 in

utest stateToIntTest env (utuple_ []) (tyTuple []) with int_ 0 using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) (tyTuple []) with utuple_ [] using eqExpr else ppExprs in
utest stateToIntTest env (utuple_ [int_ 7]) (tyTuple [tyInteger 0 10])
with int_ 7 using eqExpr else ppExprs in
utest idTest env (utuple_ [int_ 1, int_ 2]) (tyTuple [tyInteger 1 10, tyInteger 1 10])
with true in
utest stateToIntTest env (utuple_ [int_ 2, true_]) (tyTuple [tyInteger 1 10, tyBool ()])
with int_ 11 using eqExpr else ppExprs in
utest intToStateTest env (int_ 3) (tyTuple [tyInteger 1 10, tyBool ()])
with utuple_ [int_ 4, false_] using eqExpr else ppExprs in

-- Tests that every valid instantiation of a tuple is mapped back to itself
-- when using stateToInt followed by intToState.
let ty = tyTuple [tyInteger 3 5, tyTuple [tyInteger 5 10, tyBool ()]] in
repeati
  (lam i.
    let i = addi i 3 in
    repeati
      (lam j.
        let j = addi j 5 in
        let t1 = utuple_ [int_ i, utuple_ [int_ j, false_]] in
        let t2 = utuple_ [int_ i, utuple_ [int_ j, true_]] in
        utest idTest env t1 ty with true in
        utest idTest env t2 ty with true in
        ())
      6)
  3;

------------
-- ARRAYS --
------------

utest cardinality env (tyArray (tyBool ()) 4) with 16 in
utest cardinality env (tyArray (tyInteger 1 10) 4) with 10000 in

utest stateToIntTest env (utuple_ []) (tyArray (tyBool ()) 0) with int_ 0
using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) (tyArray (tyBool ()) 0) with utuple_ []
using eqExpr else ppExprs in
utest stateToIntTest env (utuple_ [int_ 2, int_ 3]) (tyArray (tyInteger 1 10) 2)
with int_ 21 using eqExpr else ppExprs in
utest idTest env (utuple_ [int_ 2, int_ 3, int_ 4, int_ 5, int_ 6]) (tyArray (tyInteger 1 10) 5)
with true in

--------------------
-- CONCRETE TYPES --
--------------------

let _mkEnv = lam types : [(Name, [Name])]. lam constr : [[(Name, [TypeT])]].
  let binds =
    zipWith (lam ty. lam c. (ty.0, (ty.1, mapFromSeq nameCmp c))) types constr
  in
  { env with concreteTypes = mapFromSeq nameCmp binds }
in

utest
  let t = nameSym "T" in
  let env = _mkEnv [(t, [])] [[]] in
  cardinality env (tyConcrete t [])
with 0 in

utest
  let t = nameSym "Nucleotide" in
  let constr = map (lam x. (nameSym x, [])) ["A", "C", "G", "T"] in
  let env = _mkEnv [(t, [])] [constr] in
  cardinality env (tyConcrete t [])
with 4 in

utest
  let t = nameSym "T" in
  let params = map nameSym ["a", "b", "c"] in
  let tyvarParams = map tyVar params in
  let constr = [
    (nameSym "A", tyvarParams),
    (nameSym "B", [tyInteger 1 4]),
    (nameSym "C", tail tyvarParams)
  ] in
  let env = _mkEnv [(t, params)] [constr] in
  cardinality env (tyConcrete t [tyBool (), tyInteger 1 10, tyBool ()])
with sum [40, 4, 20] in

utest
  let foo = nameSym "Foo" in
  let foop = [nameSym "a"] in
  let fooc = [(nameSym "C1", map tyVar foop)] in

  let bar = nameSym "Bar" in
  let barp = [nameSym "b"] in
  let barc = [(nameSym "C2", map tyVar barp), (nameSym "C3", [])] in

  let env = _mkEnv [(foo, foop), (bar, barp)] [fooc, barc] in
  cardinality env (tyConcrete foo [tyConcrete bar [tyInteger 1 3]])
with addi 3 1 in

let nucleotide = nameSym "Nucleotide" in
let a = nameSym "A" in
let c = nameSym "C" in
let g = nameSym "G" in
let t = nameSym "T" in
let constr = [(a, []), (c, []), (g, []), (t, [])] in
let env = _mkEnv [(nucleotide, [])] [constr] in
let ty = tyConcrete nucleotide [] in

utest cardinality env ty with 4 in
utest stateToIntTest env (nconapp_ a uunit_) ty with int_ 0 using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ c uunit_) ty with int_ 1 using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ g uunit_) ty with int_ 2 using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ t uunit_) ty with int_ 3 using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) ty with nconapp_ a uunit_ using eqExpr else ppExprs in
utest intToStateTest env (int_ 1) ty with nconapp_ c uunit_ using eqExpr else ppExprs in
utest intToStateTest env (int_ 2) ty with nconapp_ g uunit_ using eqExpr else ppExprs in
utest intToStateTest env (int_ 3) ty with nconapp_ t uunit_ using eqExpr else ppExprs in

let opt = nameSym "Option" in
let params = [nameSym "a"] in
let some = nameSym "Some" in
let none = nameSym "None" in
let constr = [(some, [tyVar (head params)]), (none, [])] in
let env = _mkEnv [(opt, params)] [constr] in
let ty = tyConcrete opt [tyInteger 1 10] in

utest cardinality env ty with 11 in
utest stateToIntTest env (nconapp_ some (int_ 7)) ty with int_ 6 using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ none uunit_) ty with int_ 10 using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) ty with nconapp_ some (int_ 1) using eqExpr else ppExprs in
utest intToStateTest env (int_ 4) ty with nconapp_ some (int_ 5) using eqExpr else ppExprs in
utest intToStateTest env (int_ 10) ty with nconapp_ none uunit_ using eqExpr else ppExprs in

let t = nameSym "T" in
let params = map nameSym ["a", "b", "c"] in
let a = nameSym "A" in
let b = nameSym "B" in
let c = nameSym "C" in
let d = nameSym "D" in
let constr = [
  (a, map tyVar params),
  (b, [tyInteger 1 5, tyVar (get params 1)]),
  (c, []),
  (d, [tyVar (head params), tyVar (head params)])
] in
let env = _mkEnv [(t, params)] [constr] in

-- |A| = 120, |B| = 10, |C| = 1, |D| = 144
-- [0, 120) -> A, [120, 130) -> B, [130, 131) -> C, [131, 167) -> D
let ty = tyConcrete t [tyTuple [tyBool (), tyInteger 1 3], tyBool (), tyInteger 1 10] in

utest cardinality env ty with 167 in
utest stateToIntTest env (nconapp_ a (utuple_ [utuple_ [false_, int_ 1], false_, int_ 2])) ty
with int_ 12 using eqExpr else ppExprs in
utest intToStateTest env (int_ 0) ty
with nconapp_ a (utuple_ [utuple_ [false_, int_ 1], false_, int_ 1]) using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ b (utuple_ [int_ 2, false_])) ty
with int_ 121 using eqExpr else ppExprs in
utest intToStateTest env (int_ 127) ty
with nconapp_ b (utuple_ [int_ 3, true_]) using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ c uunit_) ty with int_ 130 using eqExpr else ppExprs in
utest intToStateTest env (int_ 130) ty with nconapp_ c uunit_ using eqExpr else ppExprs in
utest stateToIntTest env (nconapp_ d (utuple_ [utuple_ [false_, int_ 2], utuple_ [true_, int_ 3]])) ty
with int_ 163 using eqExpr in
utest intToStateTest env (int_ 131) ty
with nconapp_ d (utuple_ [utuple_ [false_, int_ 1], utuple_ [false_, int_ 1]]) using eqExpr else ppExprs in

---------------------
-- AUTOMATON TYPES --
---------------------

let a = nameSym "A" in
let aid = nameSym "a" in
let env = {env with automatons = mapFromSeq nameCmp [(aid, a)],
                    automatonStates = mapFromSeq nameCmp [(a, tyInteger 1 3)]}
in
let ty = tyAutomatonState aid in

utest cardinality env ty with 3 in
utest stateToIntTest env (int_ 2) ty with int_ 1 using eqExpr else ppExprs in
utest intToStateTest env (int_ 1) ty with int_ 2 using eqExpr else ppExprs in

()
