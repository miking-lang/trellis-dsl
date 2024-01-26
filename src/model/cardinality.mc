include "error.mc"
include "option.mc"
include "mexpr/info.mc"

include "ast.mc"

lang TrellisTypeCardinality = TrellisModelAst
  sem typeCardinality : TType -> Int
  sem typeCardinality =
  | TBool _ -> 2
  | TInt {bounds = Some (lo, hi)} -> addi (subi hi lo) 1
  | TInt {bounds = None _, info = info} | TProb {info = info} ->
    errorSingle [info] "Cannot compute cardinality of infinite type"
  | TTuple {tys = tys} -> foldl muli 1 (map typeCardinality tys)
  | TTable {args = args, ret = ret, info = info} ->
    errorSingle [info] "Cannot compute cardinality of a table type"
end

mexpr

use TrellisTypeCardinality in

let i = NoInfo () in
let ty1 = TBool {info = i} in
let ty2 = TInt {bounds = Some (2, 7), info = i} in
let ty3 = TInt {bounds = Some (0, 100), info = i} in
let ty4 = TTuple {tys = [ty1, ty2, ty3], info = i} in
utest typeCardinality ty1 with 2 in
utest typeCardinality ty2 with 6 in
utest typeCardinality ty3 with 101 in
utest typeCardinality ty4 with 1212 in

()
