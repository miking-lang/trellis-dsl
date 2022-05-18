
include "trellis.mc"

-- Types

let tybool_ = use BoolTypeAst in
  BoolType {bool= NoInfo(), info= NoInfo()}

let tyintUb_ = use IntegerTypeAst in
  lam lb:Int. lam ub:Int.
  IntegerType { lb= {i= NoInfo(),v=lb},
                ub= Some {i= NoInfo(), v=ub},
                namedUb= None(),
                v= None(),
                info = NoInfo() }

let tytuple_ = use TupleTypeAst in
  lam types:[Type].
  TupleType {t=types, info= NoInfo()}

let tyarray_ = use ArrayTypeAst in
  lam ty:Type. lam count:Expr.
  ArrayType {left=ty, count=count, info= NoInfo()}

-- Expressions

let true_ = use TrueExprAst in
  TrueExpr {info= NoInfo()}

let false_ = use FalseExprAst in
  FalseExpr {info= NoInfo()}

let int_ = use IntegerExprAst in
  lam v:Int.
  IntegerExpr {i= {i= NoInfo(), v=v}, info= NoInfo()}

let tuple_ = use TupleExprAst in
  lam elems:[Expr].
  TupleExpr {e=elems, info= NoInfo()}

let array_ = use ArrayExprAst in
  lam elems:[Expr].
  ArrayExpr {e=elems, info= NoInfo()}
