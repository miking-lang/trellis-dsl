include "result.mc"
include "sys.mc"

lang TrellisZ3Ast
  type Z3Program = [Z3Decl]

  syn Z3Decl =
  | ZDCheckSat ()
  | ZDConst {id : String, ty : Z3Type}
  | ZDAssert {e : Z3Expr}

  syn Z3Type =
  | ZTInt ()

  syn Z3Expr =
  | ZETrue ()
  | ZEFalse ()
  | ZEInt {i : Int}
  | ZEVar {id : String}
  | ZEUnOp {op : Z3UOp, target : Z3Expr}
  | ZEBinOp {op : Z3BOp, lhs : Z3Expr, rhs : Z3Expr}

  syn Z3UOp =
  | ZUNot ()

  syn Z3BOp =
  | ZBGe ()
  | ZBLt ()
  | ZBAdd ()
  | ZBSub ()
  | ZBEq ()
  | ZBAnd ()
end

lang TrellisZ3PrettyPrint = TrellisZ3Ast
  sem printZ3Program : Z3Program -> String
  sem printZ3Program =
  | decls -> strJoin "\n" (map printZ3Decl decls)

  sem printZ3Parentheses : [String] -> String
  sem printZ3Parentheses =
  | strs -> join ["(", strJoin " " strs, ")"]

  sem printZ3Decl : Z3Decl -> String
  sem printZ3Decl =
  | ZDCheckSat _ ->
    printZ3Parentheses ["check-sat"]
  | ZDConst {id = id, ty = ty} ->
    printZ3Parentheses ["declare-const", id, printZ3Type ty]
  | ZDAssert {e = e} ->
    printZ3Parentheses ["assert", printZ3Expr e]

  sem printZ3Type : Z3Type -> String
  sem printZ3Type =
  | ZTInt _ -> "Int"

  sem printZ3Expr : Z3Expr -> String
  sem printZ3Expr =
  | ZETrue _ -> "true"
  | ZEFalse _ -> "false"
  | ZEInt {i = i} -> int2string i
  | ZEVar {id = id} -> id
  | ZEUnOp {op = uop, target = target} ->
    printZ3Parentheses [printUnOp uop, printZ3Expr target]
  | ZEBinOp {op = bop, lhs = lhs, rhs = rhs} ->
    printZ3Parentheses [printBinOp bop, printZ3Expr lhs, printZ3Expr rhs]

  sem printUnOp : Z3UOp -> String
  sem printUnOp =
  | ZUNot _ -> "not"

  sem printBinOp : Z3BOp -> String
  sem printBinOp =
  | ZBGe _ -> ">="
  | ZBLt _ -> "<"
  | ZBAdd _ -> "+"
  | ZBSub _ -> "-"
  | ZBEq _ -> "="
  | ZBAnd _ -> "and"
end

lang TrellisZ3Error
  syn Z3Error =
  | NotInstalled ()
  | UnknownOutput {program : String, stdout : String, stderr : String}
  | NonZeroReturnCode {program : String, stdout : String, stderr : String, code : Int}

  sem printZ3Error : Z3Error -> String
  sem printZ3Error =
  | NotInstalled _ -> "Could not find command 'z3'"
  | UnknownOutput t ->
    join [
      "Received unknown output when running z3 on the following program:\n",
      t.program, "\n\nstdout:", t.stdout, "\nstderr:\n", t.stderr ]
  | NonZeroReturnCode t ->
    join [
      "Got return code ", int2string t.code, " from z3 on following program:\n",
      t.program, "\n\nstdout:", t.stdout, "\nstderr:\n", t.stderr ]

  sem eqZ3Error : Z3Error -> Z3Error -> Bool
  sem eqZ3Error l =
  | r ->
    if eqi (constructorTag l) (constructorTag r) then
      eqZ3ErrorH (l, r)
    else false

  sem eqZ3ErrorH : (Z3Error, Z3Error) -> Bool
  sem eqZ3ErrorH =
  | (UnknownOutput l, UnknownOutput r) ->
    if eqString l.program r.program then
      if eqString l.stdout r.stdout then
        eqString l.stderr r.stderr
      else false
    else false
  | (NonZeroReturnCode l, NonZeroReturnCode r) ->
    if eqi l.code r.code then
      if eqString l.program r.program then
        if eqString l.stdout r.stdout then
          eqString l.stderr r.stderr
        else false
      else false
    else false
end

-- Runs a Z3 program for checking satisfiability using Z3 via the command-line
-- and returns true the given constraints are satisfiable. If the Z3 command
-- is not installed, or the output from Z3 is unknown, an error result is
-- returned.
lang TrellisZ3Run = TrellisZ3PrettyPrint + TrellisZ3Error
  sem checkZ3Installed : () -> Bool
  sem checkZ3Installed =
  | _ -> sysCommandExists "z3"

  sem runZ3SatProgram : Z3Program -> Result () Z3Error Bool
  sem runZ3SatProgram =
  | program ->
    if checkZ3Installed () then
      let z3Program = printZ3Program program in
      let path = sysTempFileMake () in
      writeFile path z3Program;
      let r = sysRunCommand ["z3", path] "" "." in
      deleteFile path;
      if eqi r.returncode 0 then
        switch strTrim r.stdout
        case "sat" then result.ok true
        case "unsat" then result.ok false
        case _ then
          result.err
            (UnknownOutput {program = z3Program, stdout = r.stdout, stderr = r.stderr})
        end
      else
        result.err (NonZeroReturnCode {
          program = z3Program, stdout = r.stdout, stderr = r.stderr,
          code = r.returncode
        })
    else result.err (NotInstalled ())
end

mexpr

use TrellisZ3Run in

let eqCheck = lam p. lam r.
  let l = runZ3SatProgram p in
  switch (result.consume l, result.consume r)
  case ((_, Right lv), (_, Right rv)) then eqBool lv rv
  case ((_, Left le), (_, Left re)) then eqSeq eqZ3Error le re
  case _ then false
  end
in
let ppProgram = lam p. lam.
  join ["Invalid result of program:\n", printZ3Program p]
in

let var = lam id. ZEVar {id = id} in
let int = lam i. ZEInt {i = i} in
let bop = lam op. lam l. lam r.
  ZEBinOp {op = op, lhs = l, rhs = r}
in
let uop = lam op. lam t.
  ZEUnOp {op = op, target = t}
in

-- Skip running the tests if Z3 is not found in the path.
if not (checkZ3Installed ()) then () else

let p = [
  ZDConst {id = "x", ty = ZTInt ()},
  ZDAssert {e = bop (ZBEq ()) (var "x") (int 0)},
  ZDCheckSat ()
] in
utest p with result.ok true using eqCheck else ppProgram in

let p2 = [
  ZDConst {id = "x", ty = ZTInt ()},
  ZDAssert {e = bop (ZBEq ()) (var "x") (int 0)},
  ZDAssert {e = bop (ZBEq ()) (var "x") (int 1)},
  ZDCheckSat ()
] in
utest p2 with result.ok false using eqCheck else ppProgram in

-- Examples based on tests for the 
let baseTypeConstraints = [
  ZDConst {id = "x0", ty = ZTInt ()},
  ZDConst {id = "x1", ty = ZTInt ()},
  ZDConst {id = "x2", ty = ZTInt ()},
  ZDConst {id = "x3", ty = ZTInt ()},
  ZDConst {id = "y0", ty = ZTInt ()},
  ZDConst {id = "y1", ty = ZTInt ()},
  ZDConst {id = "y2", ty = ZTInt ()},
  ZDConst {id = "y3", ty = ZTInt ()},
  ZDAssert {e = bop (ZBGe ()) (var "x0") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "x0") (int 16)},
  ZDAssert {e = bop (ZBGe ()) (var "x1") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "x1") (int 4)},
  ZDAssert {e = bop (ZBGe ()) (var "x2") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "x2") (int 4)},
  ZDAssert {e = bop (ZBGe ()) (var "x3") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "x3") (int 4)},
  ZDAssert {e = bop (ZBGe ()) (var "y0") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "y0") (int 16)},
  ZDAssert {e = bop (ZBGe ()) (var "y1") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "y1") (int 4)},
  ZDAssert {e = bop (ZBGe ()) (var "y2") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "y2") (int 4)},
  ZDAssert {e = bop (ZBGe ()) (var "y3") (int 0)},
  ZDAssert {e = bop (ZBLt ()) (var "y3") (int 4)}
] in
let checkSat = [ZDCheckSat ()] in

-- Checking whether the set constraints are non-empty.

-- { (1, [a, as...]) -> (k, [bs..., b]) | as == bs }
let fst = [
  ZDAssert {e = bop (ZBEq ()) (var "x0") (int 0)},
  ZDAssert {e = bop (ZBEq ()) (var "x2") (var "y1")},
  ZDAssert {e = bop (ZBEq ()) (var "x3") (var "y2")}
] in
let p3 = join [baseTypeConstraints, fst, checkSat] in
utest p3 with result.ok true using eqCheck else ppProgram in

let kmerEq = [
  ZDAssert {e = bop (ZBEq ()) (var "x1") (var "y1")},
  ZDAssert {e = bop (ZBEq ()) (var "x2") (var "y2")},
  ZDAssert {e = bop (ZBEq ()) (var "x3") (var "y3")}
] in

-- { (n1, x1) -> (n2, x2) | x1 == x2, n1 == 15, n2 == 15 }
let snd = [
  ZDAssert {e = bop (ZBEq ()) (var "x0") (int 15)},
  ZDAssert {e = bop (ZBEq ()) (var "y0") (int 15)}
] in
let p4 = join [baseTypeConstraints, kmerEq, snd, checkSat] in
utest p4 with result.ok true using eqCheck else ppProgram in

-- { (n1, x1) -> (n2, x2) | x1 == x2, n1 == 15, n2 == 14 }
let trd = [
  ZDAssert {e = bop (ZBEq ()) (var "x0") (int 15)},
  ZDAssert {e = bop (ZBEq ()) (var "y0") (int 14)}
] in
let p5 = join [baseTypeConstraints, kmerEq, trd, checkSat] in
utest p5 with result.ok true using eqCheck else ppProgram in

-- { (n1, x1) -> (n2, x2) | x1 == x2, n2 == n1 - 1, n2 != 14 }
let fth = [
  ZDAssert {e = bop (ZBEq ()) (var "y0") (bop (ZBSub ()) (var "x0") (int 1))},
  ZDAssert {e = uop (ZUNot ()) (bop (ZBEq ()) (var "y0") (int 14))}
] in
let p6 = join [baseTypeConstraints, kmerEq, fth, checkSat] in
utest p6 with result.ok true using eqCheck else ppProgram in

-- Verifying that all constraints are pairwise disjoint.

let p7 = join [baseTypeConstraints, fst, snd, checkSat] in
utest p7 with result.ok false using eqCheck else ppProgram in

let p8 = join [baseTypeConstraints, fst, trd, checkSat] in
utest p8 with result.ok false using eqCheck else ppProgram in

let p9 = join [baseTypeConstraints, fst, fth, checkSat] in
utest p9 with result.ok false using eqCheck else ppProgram in

let p10 = join [baseTypeConstraints, snd, trd, checkSat] in
utest p10 with result.ok false using eqCheck else ppProgram in

let p11 = join [baseTypeConstraints, snd, fth, checkSat] in
utest p11 with result.ok false using eqCheck else ppProgram in

let p12 = join [baseTypeConstraints, trd, fth, checkSat] in
utest p12 with result.ok false using eqCheck else ppProgram in

-- If we skip the 'n2 != 14' of the fourth set constraint, we find that the
-- third and fourth cases are overlapping.
let p13 = join [
  baseTypeConstraints, trd, [
    ZDAssert {e = bop (ZBEq ()) (var "y0") (bop (ZBSub ()) (var "x0") (int 1))}
  ],
  checkSat
] in
utest p13 with result.ok true using eqCheck else ppProgram in

()
