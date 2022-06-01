-- Bi-directionally maps an expression and a type to an integer.

-- TODO(Linnea, 2022-05-30): statically resolve sizes of arrays and ub in
-- integers

-- TODO: debug print if flag

include "trellis.mc"
include "trellis-common.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/eq.mc"
include "option.mc"

-- NOTE(Linnea, 2022-05-31): These types will likely be defined somewhere else,
-- once we have the analysis that creates it.
type TypeEnv = {
  -- Maps a concrete type to its parameters and constructors with parameters
  concreteTypes: Map Name ([Name], Map Name [Name]),
  -- Maps the currently bound type parameters to their types
  typeParams: Map Name TypeT
}

let typeEnvEmpty = {
  concreteTypes = mapEmpty nameCmp,
  typeParams = mapEmpty nameCmp
}


lang Enumerate = TrellisBaseAst
  -- Get the number of elements in the type, or error if not finite
  sem cardinality: TypeEnv -> TypeT -> Int

  -- Get the int representation of an expression of a given type
  sem intRepr: TypeEnv -> Name -> TypeT -> Expr

  -- Get the expression of an integer representation
  sem intToState: TypeEnv -> Name -> TypeT -> Expr
end

-- Fragment used by types compiling to tuples (array type and tuple type)
lang TupleEnumerate = Enumerate
  sem intReprTuple: Name -> [Name] -> [Expr] -> [Int] -> Expr
  sem intReprTuple state matchNames repr =
  | cards ->
    let matchExpr: Expr -> Expr = lam thn.
      match_ (nvar_ state) (ptuple_ (map npvar_ matchNames)) thn never_ in
    let prods: [Int] = snoc (prodAllRight cards) 1 in
    let f: Expr -> Int -> Expr = lam r. lam p. muli_ r (int_ p) in
    let sumExpr = foldl2 (lam acc: Expr. lam r: Expr. lam p: Int.
        addi_ acc (f r p)
      ) (f (head repr) (head prods)) (tail repr) (tail prods)
    in
    matchExpr sumExpr

  sem intToStateTuple: TypeEnv -> Name -> [Int] -> [TypeT] -> Expr
  sem intToStateTuple env intVal cards =
  | tys ->
     -- i -> (i/(|b||c|) mod |a|, i/|c| mod |b|, i mod |c|)
     let states: [Expr] =
       match tys with [] then []
       else
         let prods: [Int] = snoc (prodAllRight (tail cards)) 1 in
         zipWith3 (lam c. lam p. lam ty.
           let n = nameSym "t" in
           let e = modi_ (divi_ (nvar_ intVal) (int_ p)) (int_ c) in
           bind_ (nulet_ n e) (intToState env n ty)
         ) cards prods tys
     in
     -- TODO(Linnea,2022-05-25): tuple type
     utuple_ states

end

lang ArrayTypeEnumerate = Enumerate + ArrayTypeTAst + IntegerExprTAst + TupleEnumerate
  -- NOTE(Linnea,2022-05-24): Assumes Trellis arrays are compiled into MExpr
  -- tuples

  sem cardinality env =
  | ArrayTypeT t ->
    let cardLeft = cardinality env t.left in
    match t.count with IntegerExprT {i={v=count}} then
      powi cardLeft count
    else infoErrorExit t.info "Array size not statically known"

  sem intRepr env state =
  | ArrayTypeT t ->
    -- [a1,a2,a3] -> (intRepr a1)*|a|^2 + (intRepr a2)*|a| + (intRepr a3)
    match t.count with IntegerExprT {i={v=count}} then
      if eqi count 0 then int_ 0
      else
        let matchNames: [Name] = create count (lam. nameSym "t") in
        let repr: [Expr] = map (lam n. intRepr env n t.left) matchNames in
        let cards: [Int] = make (subi count 1) (cardinality env t.left) in
        intReprTuple state matchNames repr cards
    else infoErrorExit t.info "Array size not statically known"

  sem intToState env intVal =
  | ArrayTypeT t ->
    match t.count with IntegerExprT {i={v=count}} then
      let cards: [Int] = make count (cardinality env t.left) in
      intToStateTuple env intVal cards (make count t.left)
    else infoErrorExit t.info "Array size not statically known"

end

lang ConcreteTypeEnumerate = Enumerate + ConcreteTypeTAst + TupleEnumerate
  sem cardinality env =
  | ConcreteTypeT ({n = {v = name}} & t) ->
    match mapLookup name env.concreteTypes with Some (params, constr) then
      -- Populate the environment with the type arguments
      let tyParams = foldl2 (lam acc. lam p. lam a.
          mapInsert p a acc
        ) env.typeParams params t.a
      in
      let env = {env with typeParams = tyParams} in
      mapFoldWithKey (lam acc. lam. lam params.
          addi acc (cardinalityCon t.info env params)
        ) 0 constr
    else errorNameUnbound t.info name

  -- The cardinality of a constructor is the product of the cardinalities of
  -- its arguments
  sem cardinalityCon: Info -> TypeEnv -> [Name] -> Int
  sem cardinalityCon info env =
  | params ->
    foldl (lam acc. lam p.
        match mapLookup p env.typeParams with Some ty then
          muli acc (cardinality env ty)
        else errorNameUnbound info p
      ) 1 params

  sem intRepr env state =
  | ConcreteTypeT ({n = {v = name}} & t) ->
    match mapLookup name env.concreteTypes with Some (params, constr) then
      -- Populate the environment with the type arguments
      let tyParams = foldl2 (lam acc. lam p. lam a.
          mapInsert p a acc
        ) env.typeParams params t.a
      in
      let env = {env with typeParams = tyParams} in
      -- offset[i] is the accumulated cardinality of the preceding constructors
      -- for the ith constructor
      match mapFoldWithKey (lam acc. lam. lam cparams.
          match acc with (accCard, accOffset) in
          (addi accCard (cardinalityCon t.info env cparams), snoc accOffset accCard)
        ) (0, []) constr
      with (_, offset) in
      -- Match on each constructor, recursively call intRepr, add offset[i] in
      -- each arm
      -- OPT(Linnea, 2022-06-01): Avoid re-computation of cardinality of
      -- arguments that are in common for several constructors.
      recursive let matchCon = lam cs: [(Name, [Name])]. lam offset: [Int].
        match cs with [] then never_
        else match cs with [(cname, cparams)] ++ cs in
          -- Type of arguments, needed for recursive intRepr calls
          let tyArgs = map (lam p.
              match mapLookup p env.typeParams with Some ty then ty
              else errorNameUnbound t.info p
            ) cparams
          in
          -- NOTE(Linnea, 2022-06-01): special case when the constructor has
          -- exactly one argument. This assumes that we compile `C(a)` to `C a`,
          -- whereas a constructor with 0 or >1 arguments takes a tuple:
          -- `C(a,b)` compiles to `C (a,b)`, and `C` compiles to `C ()`.
          switch cparams
          case [p] then
            match tyArgs with [tyarg] in
            -- Matches on a constructor applied to a named arg
            let sub = nameSym "t" in
            match_ (nvar_ state) (npcon_ cname (npvar_ sub))
              (addi_ (int_ (head offset)) (intRepr env sub tyarg))
              (matchCon cs (tail offset))
          case _ then
            -- Matches on a constructor applied to a tuple
            let sub = nameSym "t" in
            let names = map (lam. nameSym "t") cparams in
            -- Get the int representation of the tuple
            let tupleNum: Expr =
              match cparams with [] then int_ 0
              else
                let repr: [Expr] = zipWith (intRepr env) names tyArgs in
                let cards: [Int] = map (cardinality env) (tail tyArgs) in
                intReprTuple sub names repr cards
            in
            -- Match the top-level named argument to a tuple
            let exprMatchTup: Expr -> Expr = lam thn.
              match_ (nvar_ sub) (ptuple_ (map npvar_ names)) thn never_
            in
            -- Match on the constructor, then match on the tuple if match,
            -- otherwise recurse
            match_ (nvar_ state) (npcon_ cname (npvar_ sub))
              (exprMatchTup
                (addi_ (int_ (head offset)) tupleNum))
              (matchCon cs (tail offset))
          end
      in
      matchCon (mapBindings constr) offset
    else errorNameUnbound t.info name
end

lang TupleTypeEnumerate = Enumerate + TupleTypeTAst + TupleEnumerate
  -- NOTE(Linnea,2022-05-24): Assumes Trellis tuples are compiled into MExpr
  -- tuples

  sem cardinality env =
  | TupleTypeT t ->
    foldl (lam acc. lam ty. muli acc (cardinality env ty)) 1 t.t

  sem intRepr env (state: Name) =
  | TupleTypeT t ->
    -- (a,b,c) -> (intRepr a)|b||c| + (intRepr b)|c| + (intRepr c)
    match t.t with [] then int_ 0
    else
      let matchNames: [Name] = map (lam. nameSym "t") t.t in
      let repr: [Expr] = zipWith (intRepr env) matchNames t.t in
      let cards: [Int] = map (cardinality env) (tail t.t) in
      intReprTuple state matchNames repr cards

   sem intToState env (intVal: Name) =
   | TupleTypeT t ->
     -- i -> (i/(|b||c|) mod |a|, i/|c| mod |b|, i mod |c|)
     let cards: [Int] = map (cardinality env) t.t in
     intToStateTuple env intVal cards t.t

end

lang IntegerTypeEnumerate = Enumerate + IntegerTypeTAst
  sem cardinality env =
  | IntegerTypeT t ->
    match t with {lb = {v = lb}, ub = ub, namedUb = namedUb} in
    match ub with Some ub then
      let ub: {i: Info, v: Int} = ub in
      addi 1 (subi ub.v lb)
    else match namedUb with Some namedUb then
      let namedUb: {i: Info, v: Name} = namedUb in
      infoErrorExit namedUb.i "named upper bound not supported yet"
    else infoErrorExit t.info "unbound integer in cardinality"

  sem intRepr env (state: Name) =
  | IntegerTypeT t ->
    match t.lb with {v=lb} in
    subi_ (nvar_ state) (int_ lb)

  sem intToState env (intVal: Name) =
  | IntegerTypeT t ->
    match t.lb with {v=lb} in
    addi_ (nvar_ intVal) (int_ lb)

end

lang BoolTypeEnumerate = Enumerate + BoolTypeTAst
  sem cardinality env =
  | BoolTypeT _ -> 2

  sem intRepr env (state: Name) =
  | BoolTypeT _ ->
    if_ (nvar_ state) (int_ 1) (int_ 0)

  sem intToState env (intVal: Name) =
  | BoolTypeT _ ->
    if_ (eqi_ (int_ 0) (nvar_ intVal)) false_ true_

end

-- TODO(Linnea, 2022-05-30): unlimited int, remove type? give error
lang IntTypeEnumerate = Enumerate + IntTypeTAst
end


lang TrellisEnumerate =
  ArrayTypeEnumerate + ConcreteTypeEnumerate +
  TupleTypeEnumerate + IntegerTypeEnumerate +  BoolTypeEnumerate
end

lang Test = TrellisEnumerate + MExprEval + MExprEq + MExprPrettyPrint end


mexpr

use Test in

-- Trellis AST builders
let tyboolt_ = BoolTypeT {bool= NoInfo(), info= NoInfo()} in
let tyintUbt_ =
  lam lb:Int. lam ub:Int.
  IntegerTypeT { lb= {i= NoInfo(),v=lb},
                 ub= Some {i= NoInfo(), v=ub},
                 namedUb= None(),
                 v= None(),
                 info = NoInfo() }
in
let tytuplet_ =
  lam types:[TypeT].
  TupleTypeT {t=types, info= NoInfo()}
in
let tyarrayt_ = use ArrayTypeTAst in
  lam ty:TypeT. lam count:ExprT.
  ArrayTypeT {left=ty, count=count, info= NoInfo()}
in
let tyconcretet_ = use ConcreteTypeTAst in
  lam n:Name. lam a:[TypeT].
  ConcreteTypeT {n={i= NoInfo(), v=n}, a=a, info= NoInfo()}
in
let intt_ = use IntegerExprTAst in
  lam v:Int.
  IntegerExprT {i= {i= NoInfo(), v=v}, info= NoInfo()}
in

-- Test helper functions
let _test = lam f. lam e: Expr. lam t: TypeT.
  let n = nameSym "n" in
  let eFull = bind_ (nulet_ n e) (f n t) in
  print "\n\n"; print (expr2str eFull); print "\n\n";
  eval {env = evalEnvEmpty} eFull
in

let intReprTest = _test (intRepr typeEnvEmpty) in
let intToStateTest = _test (intToState typeEnvEmpty) in

let intReprTestEnv = lam env. _test (intRepr env) in
let intToStateTestEnv = lam env. _test (intToState env) in

-- Bool type
utest cardinality typeEnvEmpty tyboolt_ with 2 in

utest intReprTest false_ tyboolt_ with int_ 0 using eqExpr in
utest intReprTest true_ tyboolt_ with int_ 1 using eqExpr in

utest intToStateTest (int_ 0) tyboolt_ with false_ using eqExpr in
utest intToStateTest (int_ 1) tyboolt_ with true_ using eqExpr in

-- Integer type
utest cardinality typeEnvEmpty (tyintUbt_ 1 1) with 1 in
utest cardinality typeEnvEmpty (tyintUbt_ 4 10) with 7 in

utest intReprTest (int_ 4) (tyintUbt_ 1 5) with int_ 3 using eqExpr in
utest intToStateTest (int_ 0) (tyintUbt_ 1 5) with int_ 1 using eqExpr in

-- Tuple type
utest cardinality typeEnvEmpty (tytuplet_ [tyboolt_, tyintUbt_ 1 4]) with 8 in

utest intReprTest uunit_ (tytuplet_ []) with int_ 0 using eqExpr in
utest intToStateTest (int_ 0) (tytuplet_ []) with uunit_ using eqExpr in

utest
  let ty = tytuplet_ [tyintUbt_ 2 3, tyintUbt_ 1 5, tyintUbt_ 3 5] in
  [ intReprTest (utuple_ [int_ 2, int_ 1, int_ 3]) ty
  , intReprTest (utuple_ [int_ 2, int_ 1, int_ 4]) ty
  , intReprTest (utuple_ [int_ 3, int_ 4, int_ 5]) ty
  , intReprTest (utuple_ [int_ 3, int_ 5, int_ 5]) ty
  ]
with [int_ 0, int_ 1, int_ 26, int_ 29]
using eqSeq eqExpr in

utest
  let ty = tytuplet_ [tyintUbt_ 2 3, tyintUbt_ 1 5, tyintUbt_ 3 5] in
  map (lam i. intToStateTest i ty) [int_ 0, int_ 1, int_ 26, int_ 29]
with [ utuple_ [int_ 2, int_ 1, int_ 3]
     , utuple_ [int_ 2, int_ 1, int_ 4]
     , utuple_ [int_ 3, int_ 4, int_ 5]
     , utuple_ [int_ 3, int_ 5, int_ 5]
     ]
using eqSeq eqExpr in

-- Array type
utest cardinality typeEnvEmpty (tyarrayt_ (tyintUbt_ 1 5) (intt_ 3)) with 125 in

utest intReprTest uunit_ (tyarrayt_ (tyintUbt_ 1 5) (intt_ 0)) with int_ 0 using eqExpr in
utest intToStateTest (int_ 0) (tyarrayt_ (tyintUbt_ 1 5) (intt_ 0)) with uunit_ using eqExpr in

utest
  let ty = tyarrayt_ (tyintUbt_ 1 5) (intt_ 3) in
  [ intReprTest (utuple_ [int_ 1, int_ 1, int_ 1]) ty
  , intReprTest (utuple_ [int_ 2, int_ 3, int_ 5]) ty
  , intReprTest (utuple_ [int_ 5, int_ 5, int_ 5]) ty
  ]
with [int_ 0, int_ 39, int_ 124]
using eqSeq eqExpr in

utest
  let ty = tyarrayt_ (tyintUbt_ 1 5) (intt_ 3) in
  map (lam i. intToStateTest i ty) [int_ 0, int_ 39, int_ 124]
with [ utuple_ [int_ 1, int_ 1, int_ 1]
     , utuple_ [int_ 2, int_ 3, int_ 5]
     , utuple_ [int_ 5, int_ 5, int_ 5]
     ]
using eqSeq eqExpr in

-- Concrete type

let _mkEnv = lam tys: [(Name, [Name])]. lam constr: [[(Name, [Name])]].
  let binds: [(Name, ([Name], Map Name [Name]))] =
    zipWith (lam ty: (Name, [Name]). lam c: [(Name, [Name])].
      (ty.0, (ty.1, mapFromSeq nameCmp c))
    ) tys constr
  in { typeEnvEmpty with concreteTypes = mapFromSeq nameCmp binds }
in

utest
  let tyName = nameSym "T" in
  let params = [] in
  let constr = [(nameSym "A", []), (nameSym "B", []), (nameSym "C", [])] in
  let env = _mkEnv [(tyName, params)] [constr] in
  cardinality env (tyconcretet_ tyName [])
with 3 in

utest
  let tyName = nameSym "T" in
  let params = map nameSym ["a", "b", "c"] in
  let constr = [(nameSym "A", params), (nameSym "B", []), (nameSym "C", tail params)] in
  let env = _mkEnv [(tyName, params)] [constr] in
  cardinality env (tyconcretet_ tyName [tyboolt_, tyintUbt_ 1 3, tyintUbt_ 4 7])
with addi 24 (addi 1 12) in

utest
  let t1 = nameSym "T1" in
  let p1 = map nameSym ["a"] in
  let c1 = [(nameSym "C1", p1)] in

  let t2 = nameSym "T2" in
  let p2 = map nameSym ["b"] in
  let c2 = [(nameSym "C2", p2), (nameSym "C3", [])] in

  let env = _mkEnv [(t1, p1), (t2, p2)] [c1, c2] in
  cardinality env (tyconcretet_ t1 [tyconcretet_ t2 [tyintUbt_ 1 3]])
with addi 3 1 in

utest
  let t = nameSym "T" in
  let params = [nameSym "a", nameSym "b"] in
  let a = nameSym "A" in
  let b = nameSym "B" in
  let constr = [(a, [get params 0]), (b, [get params 1])] in
  let env = _mkEnv [(t, params)] [constr] in

  let ty = tyconcretet_ t [tyintUbt_ 1 3, tyboolt_] in

  [ intReprTestEnv env (nconapp_ a (int_ 1)) ty
  , intReprTestEnv env (nconapp_ a (int_ 2)) ty
  , intReprTestEnv env (nconapp_ a (int_ 3)) ty
  , intReprTestEnv env (nconapp_ b false_) ty
  , intReprTestEnv env (nconapp_ b true_) ty
  ]
with [int_ 0, int_ 1, int_ 2, int_ 3, int_ 4]
using eqSeq eqExpr in

utest
  let t = nameSym "T" in
  let params = [nameSym "a", nameSym "b"] in
  let a = nameSym "A" in
  let b = nameSym "B" in
  let constr = [(a, []), (b, params)] in
  let env = _mkEnv [(t, params)] [constr] in

  let ty = tyconcretet_ t [tyintUbt_ 1 3, tyboolt_] in

  [ intReprTestEnv env (nconapp_ a uunit_) ty
  , intReprTestEnv env (nconapp_ b (utuple_ [int_ 1, false_])) ty
  , intReprTestEnv env (nconapp_ b (utuple_ [int_ 1, true_])) ty
  , intReprTestEnv env (nconapp_ b (utuple_ [int_ 2, false_])) ty
  , intReprTestEnv env (nconapp_ b (utuple_ [int_ 2, true_])) ty
  , intReprTestEnv env (nconapp_ b (utuple_ [int_ 3, false_])) ty
  , intReprTestEnv env (nconapp_ b (utuple_ [int_ 3, true_])) ty
  ]
with [int_ 0, int_ 1, int_ 2, int_ 3, int_ 4, int_ 5, int_ 6]
using eqSeq eqExpr in


()
