-- Bi-directionally maps an expression and a type to an integer.

-- TODO: statically resolve sizes of arrays and ub in integers

include "trellis.mc"
include "trellis-common.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/eq.mc"
include "option.mc"

lang Enumerate = TrellisBaseAst
  -- Get the number of elements in the type, or error if not finite
  sem cardinality: Type -> Int

  -- Get the int representation of an expression of a given type
  sem intRepr: Name -> Type -> Expr

  -- Get the expression of an integer representation
  sem intToState: Name -> Type -> Expr
end

lang TypeApplicationTypeEnumerate = Enumerate + TypeApplicationTypeTAst
end

-- Fragment used by types compiling to tuples (array type and tuple type)
lang TupleEnumerate = Enumerate
  sem intReprTuple: Name -> [Names] -> [Expr] -> [Int] -> Expr
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

  sem intToStateTuple: Name -> [Int] -> [Types] -> Expr
  sem intToStateTuple intVal cards =
  | tys ->
     -- i -> (i/(|b||c|) mod |a|, i/|c| mod |b|, i mod |c|)
     let states: [Expr] =
       match tys with [] then []
       else
         let prods: [Int] = snoc (prodAllRight (tail cards)) 1 in
         zipWith3 (lam c. lam p. lam ty.
           let n = nameSym "t" in
           let e = modi_ (divi_ (nvar_ intVal) (int_ p)) (int_ c) in
           bind_ (nulet_ n e) (intToState n ty)
         ) cards prods tys
     in
     -- TODO(Linnea,2022-05-25): tuple type
     tuple_ tyunknown_ states

end

lang ArrayTypeEnumerate = Enumerate + ArrayTypeTAst + IntegerExprTAst + TupleEnumerate
  -- NOTE(Linnea,2022-05-24): Assumes Trellis arrays are compiled into MExpr
  -- tuples

  sem cardinality =
  | ArrayTypeT t ->
    let cardLeft = cardinality t.left in
    match t.count with IntegerExprT {i={v=count}} then
      powi cardLeft count
    else infoErrorExit t.info "Array size not statically known"

  sem intRepr state =
  | ArrayTypeT t ->
    -- [a1,a2,a3] -> (intRepr a1)*|a|^2 + (intRepr a2)*|a| + (intRepr a3)
    match t.count with IntegerExprT {i={v=count}} then
      if eqi count 0 then int_ 0
      else
        let matchNames: [Name] = create count (lam. nameSym "t") in
        let repr: [Expr] = map (lam n. intRepr n t.left) matchNames in
        let cards: [Int] = make (subi count 1) (cardinality t.left) in
        intReprTuple state matchNames repr cards
    else infoErrorExit t.info "Array size not statically known"

  sem intToState intVal =
  | ArrayTypeT t ->
    match t.count with IntegerExprT {i={v=count}} then
      let cards: [Int] = make count (cardinality t.left) in
      intToStateTuple intVal cards (make count t.left)
    else infoErrorExit t.info "Array size not statically known"

end

lang ConcreteTypeEnumerate = Enumerate + ConcreteTypeTAst
end

lang TupleTypeEnumerate = Enumerate + TupleTypeTAst + TupleEnumerate
  -- NOTE(Linnea,2022-05-24): Assumes Trellis tuples are compiled into MExpr
  -- tuples

  sem cardinality =
  | TupleTypeT t ->
    foldl (lam acc. lam ty. muli acc (cardinality ty)) 1 t.t

  sem intRepr (state: Name) =
  | TupleTypeT t ->
    -- (a,b,c) -> (intRepr a)|b||c| + (intRepr b)|c| + (intRepr c)
    match t.t with [] then int_ 0
    else
      let matchNames: [Name] = map (lam. nameSym "t") t.t in
      let repr: [Expr] = zipWith intRepr matchNames t.t in
      let cards: [Int] = map cardinality (tail t.t) in
      intReprTuple state matchNames repr cards

   sem intToState (intVal: Name) =
   | TupleTypeT t ->
     -- i -> (i/(|b||c|) mod |a|, i/|c| mod |b|, i mod |c|)
     let cards: [Int] = map cardinality t.t in
     intToStateTuple intVal cards t.t

end

lang IntegerTypeEnumerate = Enumerate + IntegerTypeTAst
  sem cardinality =
  | IntegerTypeT t ->
    match t with {lb = {v = lb}, ub = ub, namedUb = namedUb} in
    match ub with Some ub then
      let ub: {i: Info, v: Int} = ub in
      addi 1 (subi ub.v lb)
    else match namedUb with Some namedUb then
      let namedUb: {i: Info, v: String} = namedUb in
      infoErrorExit namedUb.i "named upper bound not supported yet"
    else infoErrorExit t.info "unbound integer in cardinality"

  sem intRepr (state: Name) =
  | IntegerTypeT t ->
    match t.lb with {v=lb} in
    subi_ (nvar_ state) (int_ lb)

  sem intToState (intVal: Name) =
  | IntegerTypeT t ->
    match t.lb with {v=lb} in
    addi_ (nvar_ intVal) (int_ lb)

end

lang BoolTypeEnumerate = Enumerate + BoolTypeTAst
  sem cardinality =
  | BoolTypeT _ -> 2

  sem intRepr (state: Name) =
  | BoolTypeT _ ->
    if_ (nvar_ state) (int_ 1) (int_ 0)

  sem intToState (intVal: Name) =
  | BoolTypeT _ ->
    if_ (eqi_ (int_ 0) (nvar_ intVal)) false_ true_

end

-- TODO: unlimited int, remove type?
lang IntTypeEnumerate = Enumerate + IntTypeTAst
end


lang TrellisEnumerate =
   TypeApplicationTypeEnumerate + ArrayTypeEnumerate + ConcreteTypeEnumerate +
   TupleTypeEnumerate + IntegerTypeEnumerate +  BoolTypeEnumerate
end

lang Test = TrellisEnumerate + MExprEval + MExprEq end


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
  lam types:[Type].
  TupleTypeT {t=types, info= NoInfo()}
in
let tyarrayt_ = use ArrayTypeTAst in
  lam ty:TypeT. lam count:ExprT.
  ArrayTypeT {left=ty, count=count, info= NoInfo()}
in
let intt_ = use IntegerExprTAst in
  lam v:Int.
  IntegerExprT {i= {i= NoInfo(), v=v}, info= NoInfo()}
in

-- Test helper functions
let _test = lam f. lam e: Expr. lam t: TypeT.
  let n = nameSym "n" in
  let eFull = bind_ (nulet_ n e) (f n t) in
  eval {env = evalEnvEmpty} eFull
in

let intReprTest = _test intRepr in
let intToStateTest = _test intToState in

-- Bool type
utest cardinality tyboolt_ with 2 in

utest intReprTest false_ tyboolt_ with int_ 0 using eqExpr in
utest intReprTest true_ tyboolt_ with int_ 1 using eqExpr in

utest intToStateTest (int_ 0) tyboolt_ with false_ using eqExpr in
utest intToStateTest (int_ 1) tyboolt_ with true_ using eqExpr in

-- Integer type
utest cardinality (tyintUbt_ 1 1) with 1 in
utest cardinality (tyintUbt_ 4 10) with 7 in

utest intReprTest (int_ 4) (tyintUbt_ 1 5) with int_ 3 using eqExpr in
utest intToStateTest (int_ 0) (tyintUbt_ 1 5) with int_ 1 using eqExpr in

-- Tuple type
utest cardinality (tytuplet_ [tyboolt_, tyintUbt_ 1 4]) with 8 in

utest intReprTest uunit_ (tytuplet_ []) with int_ 0 in
utest intToState (int_ 0) (tytuplet_ []) with uunit_ using eqExpr in

utest
  let ty = tytuplet_ [tyintUbt_ 2 3, tyintUbt_ 1 5, tyintUbt_ 3 5] in
  [ intReprTest (tuple_ tyunknown_ [int_ 2, int_ 1, int_ 3]) ty
  , intReprTest (tuple_ tyunknown_ [int_ 2, int_ 1, int_ 4]) ty
  , intReprTest (tuple_ tyunknown_ [int_ 3, int_ 4, int_ 5]) ty
  , intReprTest (tuple_ tyunknown_ [int_ 3, int_ 5, int_ 5]) ty
  ]
with [int_ 0, int_ 1, int_ 26, int_ 29]
using eqSeq eqExpr in

utest
  let ty = tytuplet_ [tyintUbt_ 2 3, tyintUbt_ 1 5, tyintUbt_ 3 5] in
  map (lam i. intToStateTest i ty) [int_ 0, int_ 1, int_ 26, int_ 29]
with [ tuple_ tyunknown_ [int_ 2, int_ 1, int_ 3]
     , tuple_ tyunknown_ [int_ 2, int_ 1, int_ 4]
     , tuple_ tyunknown_ [int_ 3, int_ 4, int_ 5]
     , tuple_ tyunknown_ [int_ 3, int_ 5, int_ 5]
     ]
using eqSeq eqExpr in

-- Array type
utest cardinality (tyarrayt_ (tyintUbt_ 1 5) (intt_ 3)) with 125 in

utest intReprTest uunit_ (tyarrayt_ (tyintUbt_ 1 5) (intt_ 0)) with int_ 0 in
utest intToState (int_ 0) (tyarrayt_ (tyintUbt_ 1 5) (intt_ 0)) with uunit_ using eqExpr in

utest
  let ty = tyarrayt_ (tyintUbt_ 1 5) (intt_ 3) in
  [ intReprTest (tuple_ tyunknown_ [int_ 1, int_ 1, int_ 1]) ty
  , intReprTest (tuple_ tyunknown_ [int_ 2, int_ 3, int_ 5]) ty
  , intReprTest (tuple_ tyunknown_ [int_ 5, int_ 5, int_ 5]) ty
  ]
with [int_ 0, int_ 39, int_ 124] in

utest
  let ty = tyarrayt_ (tyintUbt_ 1 5) (intt_ 3) in
  map (lam i. intToStateTest i ty) [int_ 0, int_ 39, int_ 124]
with [ tuple_ tyunknown_ [int_ 1, int_ 1, int_ 1]
     , tuple_ tyunknown_ [int_ 2, int_ 3, int_ 5]
     , tuple_ tyunknown_ [int_ 5, int_ 5, int_ 5]
     ]
using eqSeq eqExpr in

()
