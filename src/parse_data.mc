include "parser/ll1.mc"

let parseLL1
  : String
  -> String
  -> [Int]
  = use ParserConcrete in
    let table =
      let top = ll1NonTerminal "Top" in
      let cont = ll1NonTerminal "Cont" in
      let int = ll1NonTerminal "Int" in
      let mkTop = lam toks.
        match toks with [UserSym x, UserSym xs]
        then cons x xs
        else never in
      let mkCont = lam toks.
        match toks with [_, UserSym x, UserSym xs]
        then cons x xs
        else never in
      let mkPos = lam toks.
        match toks with [Tok (IntTok {val = val})]
        then val
        else never in
      let mkNeg = lam toks.
        match toks with [_, Tok (IntTok {val = val})]
        then negi val
        else never in
      let grammar =
        { start = top
        , productions =
          [ { nt = top, label = "empty-file", rhs = [], action = lam _. [] }
          , { nt = top, label = "file", rhs = [ll1Nt int, ll1Nt cont], action = mkTop }
          , { nt = cont, label = "empty-continuation", rhs = [], action = lam _. [] }
          , { nt = cont, label = "continuation", rhs = [ll1Comma, ll1Nt int, ll1Nt cont], action = mkCont }
          , { nt = int, label = "pos-int", rhs = [ll1Int], action = mkPos }
          , { nt = int, label = "neg-int", rhs = [ll1Lit "-", ll1Int], action = mkNeg }
          ]
        }
      in ll1GenParser grammar
    in match table with Right table then
      lam path. lam source. ll1ParseWithTable table path source
    else match table with Left err then
      let _ = dprintLn (mapBindings (mapMap mapBindings err)) in
      error "Unexpected error"
    else never

let splitOnChar = lam delim.
  recursive let work = lam topAcc. lam midAcc. lam s.
    match s with [c] ++ s then
      if eqc c delim
      then work (snoc topAcc midAcc) [] s
      else work topAcc (snoc midAcc c) s
    else match s with [] then snoc topAcc midAcc
    else never
  in work [] []

let parseSplitOn
  : String
  -> String
  -> [Int]
  = lam path. lam source.
    let x = source in
    let xs = splitOnChar ',' x in
    map (lam x. string2int (filter (lam c. not (eqc c '\n')) x)) xs

mexpr

let time = lam label. lam f.
  let before = wallTimeMs () in
  let _ = f () in
  let after = wallTimeMs () in
  let _ = printLn (join [label, ": ", float2string (subf after before), "ms"]) in
  ()
in

let path = "../DNASeqAssignment/data/p.txt" in
let src = readFile path in
let _ = time "splitOn\t" (lam _. parseSplitOn path src) in
let _ = time "ll1\t" (lam _. parseLL1 path src) in
let _ = _printExtraTimings () in
utest Right (parseSplitOn path src) with parseLL1 path src in

let _ = printLn "DONE" in


-- splitOn : 2.869287e+1ms
-- ll1     : 1.691122e+3ms
-- 2.869287e+1 / 1.691122e+3 = 0.016966765259987155
-- roughly 1/10 of the time is spent in `nextToken`
-- 1/20 of the time is spent in `mapLookup` when looking in the table


-- Before the `TmFix` eval change and after
-- ~/Projects/trellis-dsl/src main*
-- ❯ mi run parse_data.mc
-- splitOn	: 2.794995e+1ms
-- ll1	: 6.133630e+2ms
-- tokenTimeCounter, 6.088378e+1
-- litEqCmp, 3.434570e+0
-- litMem, 5.225341e+0
-- openLookup, 5.202368e+1
-- cmpSym, 4.168066e+1
-- DONE


-- ~/Projects/trellis-dsl/src main*
-- ❯ mi run parse_data.mc
-- splitOn	: 1.223022e+1ms
-- ll1	: 9.693090e+1ms
-- tokenTimeCounter, 2.270947e+1
-- litEqCmp, 3.215820e+0
-- litMem, 4.704345e+0
-- openLookup, 2.915429e+1
-- cmpSym, 1.181787e+1
-- DONE
-- 1.223022e+1 / 9.693090e+1 = 0.12617462542904276

-- Roughly improvement by factor of 6

()
