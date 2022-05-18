-- Bi-directionally maps an expression and a type to an integer.

-- TODO: use state in names

include "trellis.mc"
include "trellis-common.mc"
include "ast-builder.mc"

include "option.mc"

lang Enumerate = TrellisBaseAst
  -- Get the number of elements in the type, or error if not finite
  sem cardinality: Type -> Int

  -- Get the int representation of an expression of a given type
  sem intRepr: Expr -> Type -> Int

  -- Get the expression of an integer representation
  sem intToState: Int -> Type -> Expr
end

lang TypeApplicationTypeEnumerate = Enumerate + TypeApplicationTypeAst
end

lang ArrayTypeEnumerate = Enumerate + ArrayTypeAst + ArrayExprAst + IntegerExprAst
  sem cardinality =
  | ArrayType t ->
    let cardLeft = cardinality t.left in
    match t.count with IntegerExpr {i={v=count}} then
      powi cardLeft count
    else infoErrorExit t.info "Array size not statically known"

  sem intRepr state =
  | ArrayType t ->
    let cardLeft = cardinality t.left in
    match t.count with IntegerExpr {i={v=count}} then
      -- [a1,a2,a3] -> (intRepr a1)*|a|^2 + (intRepr a2)*|a| + (intRepr a3)
      match state with ArrayExpr {e=exprs} in
      let repr = map (lam e. intRepr e t.left) exprs in
      let prods = snoc (prodAllRight (make (subi count 1) cardLeft)) 1 in
      foldl2 (lam acc. lam r. lam p. addi acc (muli r p)) 0 repr prods

    else infoErrorExit t.info "Array size not statically known"

  sem intToState intVal =
  | ArrayType t ->
    -- i -> [i/(|a|^(n-1)) mod |a|, i/|a|^(n-2) mod |a|, ..., i mode |a|]
    let cardLeft = cardinality t.left in
    match t.count with IntegerExpr {i={v=count}} then
      let prods = snoc (prodAllRight (make (subi count 1) cardLeft)) 1 in
      let repr = map (lam p. modi (divi intVal p) cardLeft) prods in
      ArrayExpr {e = map (lam r. intToState r t.left) repr, info = t.info}
    else infoErrorExit t.info "Array size not statically known"
end

lang ConcreteTypeEnumerate = Enumerate + ConcreteTypeAst
end

lang TupleTypeEnumerate = Enumerate + TupleTypeAst + TupleExprAst
  sem cardinality =
  | TupleType t ->
    foldl (lam acc. lam ty. muli acc (cardinality ty)) 1 t.t

  sem intRepr state =
  | TupleType t ->
    match t.t with [] then 0
    else
      -- (a,b,c) -> (intRepr a)|b||c| + (intRepr b)|c| + (intRepr c)
      match state with TupleExpr {e=exprs} in
      let repr = zipWith intRepr exprs t.t in
      let cards = map cardinality (tail t.t) in
      let prods = snoc (prodAllRight cards) 1 in
      foldl2 (lam acc. lam r. lam p. addi acc (muli r p)) 0 repr prods

  sem intToState intVal =
  | TupleType t ->
    match t.t with [] then 0
    else
      -- i -> (i/(|b||c|) mod |a|, i/|c| mod |b|, i mod |c|)
      let cards = map cardinality t.t  in
      let prods = snoc (prodAllRight (tail cards)) 1 in
      let repr = zipWith (lam c. lam p. modi (divi intVal p) c) cards prods in
      TupleExpr {e = zipWith intToState repr t.t, info = t.info}
end

lang IntegerTypeEnumerate = Enumerate + IntegerTypeAst + IntegerExprAst
  sem cardinality =
  | IntegerType t ->
    match t with {lb = {v = lb}, ub = ub, namedUb = namedUb} in
    match ub with Some {v=ub} then addi 1 (subi ub lb)
    else match namedUb with Some namedUb then
      infoErrorExit namedUb.i "named upper bound not supported yet"
    else infoErrorExit t.info "unbound integer in cardinality"

  sem intRepr state =
  | IntegerType t ->
    match t.lb with {v = lb} in
    match state with IntegerExpr {i = {v = i}} in
    subi i lb

  sem intToState intVal =
  | IntegerType t ->
    let info = get_Type_info (IntegerType t) in
    match t.lb with {v = lb} in
    IntegerExpr { i = {i = info, v = addi lb intVal}, info = info }
end

lang BoolTypeEnumerate = Enumerate + BoolTypeAst + TrueExprAst + FalseExprAst
  sem cardinality =
  | BoolType _ -> 2

  sem intRepr state =
  | BoolType _ ->
    switch state
    case FalseExpr _ then 0
    case TrueExpr _ then 1
    end

  sem intToState intVal =
  | BoolType t ->
    let info = get_Type_info (BoolType t) in
    switch intVal
    case 0 then FalseExpr {info = info}
    case 1 then TrueExpr {info = info}
    end
end

-- TODO: unlimited int
lang IntTypeEnumerate = Enumerate + IntTypeAst
end


lang TrellisEnumerate =
  TypeApplicationTypeEnumerate + ArrayTypeEnumerate + ConcreteTypeEnumerate +
  TupleTypeEnumerate + IntegerTypeEnumerate +  BoolTypeEnumerate +
  IntTypeEnumerate
end

lang Test = TrellisEnumerate end


mexpr

use Test in

-- Bool type
utest cardinality (tybool_) with 2 in

utest intRepr false_ tybool_ with 0 in
utest intRepr true_ tybool_ with 1 in

utest intToState 0 tybool_ with false_ in
utest intToState 1 tybool_ with true_ in

-- Integer type
utest cardinality (tyintUb_ 1 1) with 1 in
utest cardinality (tyintUb_ 4 10) with 7 in

utest intRepr (int_ 4) (tyintUb_ 1 5) with 3 in
utest intToState 0 (tyintUb_ 1 5) with int_ 1 in

-- Tuple type
utest cardinality (tytuple_ [tybool_, tyintUb_ 1 4]) with 8 in

utest
  let ty = tytuple_ [tyintUb_ 2 3, tyintUb_ 1 5, tyintUb_ 3 5] in
  [ intRepr (tuple_ [int_ 2, int_ 1, int_ 3]) ty
  , intRepr (tuple_ [int_ 2, int_ 1, int_ 4]) ty
  , intRepr (tuple_ [int_ 3, int_ 4, int_ 5]) ty
  , intRepr (tuple_ [int_ 3, int_ 5, int_ 5]) ty
  ]
with [0,1,26,29] in

utest
  let ty = tytuple_ [tyintUb_ 2 3, tyintUb_ 1 5, tyintUb_ 3 5] in
  map (lam i. intToState i ty) [0,1,26,29]
with [ tuple_ [int_ 2, int_ 1, int_ 3]
     , tuple_ [int_ 2, int_ 1, int_ 4]
     , tuple_ [int_ 3, int_ 4, int_ 5]
     , tuple_ [int_ 3, int_ 5, int_ 5]
     ] in

-- Array type
utest cardinality (tyarray_ (tyintUb_ 1 5) (int_ 3)) with 125 in

utest
  let ty = tyarray_ (tyintUb_ 1 5) (int_ 3) in
  [ intRepr (array_ [int_ 1, int_ 1, int_ 1]) ty
  , intRepr (array_ [int_ 2, int_ 3, int_ 5]) ty
  , intRepr (array_ [int_ 5, int_ 5, int_ 5]) ty
  ]
with [0,39,124] in

utest
  let ty = tyarray_ (tyintUb_ 1 5) (int_ 3) in
  map (lam i. intToState i ty) [0,39,124]
with [ array_ [int_ 1, int_ 1, int_ 1]
     , array_ [int_ 2, int_ 3, int_ 5]
     , array_ [int_ 5, int_ 5, int_ 5]
     ] in

()
