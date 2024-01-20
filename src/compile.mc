include "seq.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

include "ast.mc"
include "repr.mc"
include "trellis-arg.mc"

lang TrellisGenerateInitialization =
  FutharkAst + FutharkTypePrettyPrint + TrellisRepresentation

  -- Finds the smallest integer type in Futhark that can fit the given number of bits.
  sem findSmallestIntegerType : Int -> FutType
  sem findSmallestIntegerType =
  | n ->
    -- NOTE(larshum, 2024-01-19): Currently, we represent the state using a
    -- signed integer, because using unsigned integers requires a lot of
    -- additional casts to work properly. Therefore, we lose one bit of information.
    if lti n 8 then FTyInt8 {info = NoInfo ()}
    else if lti n 16 then FTyInt16 {info = NoInfo ()}
    else if lti n 32 then FTyInt32 {info = NoInfo ()}
    else if lti n 64 then FTyInt64 {info = NoInfo ()}
    else error "Trellis does not support states that require more than 64 bits to encode"

  -- Generates the initialization part of the Futhark program, declaring the
  -- state, observation, and probability types and defining the total number of
  -- states.
  sem generateInitialization : Bool -> Int -> Int -> FutProg
  sem generateInitialization useDoublePrecision stateBits =
  | obsBits ->
    let stateType = findSmallestIntegerType stateBits in
    match pprintType 0 pprintEnvEmpty stateType with (_, stateTypeStr) in
    let obsType = findSmallestIntegerType obsBits in
    match pprintType 0 pprintEnvEmpty obsType with (_, obsTypeStr) in
    let probType =
      if useDoublePrecision then FTyFloat64 {info = NoInfo ()}
      else FTyFloat32 {info = NoInfo ()}
    in
    match pprintType 0 pprintEnvEmpty probType with (_, probTypeStr) in
    -- TODO(larshum, 2024-01-19): Add support for states with components that
    -- are not even powers of two.
    let nstates = slli 1 stateBits in
    FProg {decls = [
      FDeclModuleAlias {ident = nameNoSym "state", moduleId = stateTypeStr, info = NoInfo ()},
      FDeclModuleAlias {ident = nameNoSym "obs", moduleId = obsTypeStr, info = NoInfo ()},
      FDeclModuleAlias {ident = nameNoSym "prob", moduleId = probTypeStr, info = NoInfo ()},
      FDeclFun {ident = nameNoSym "nstates", entry = false, typeParams = [], params = [],
                ret = FTyInt64 {info = NoInfo ()}, body = futInt_ nstates, info = NoInfo ()}
    ]}

    sem generateInitializationHelper : TrellisOptions -> TrellisProgram -> FutProg
    sem generateInitializationHelper options =
    | p ->
      let stateBits =
        match findStateRepresentation p with Continuous nbits then nbits
        else error "Currently, states have to be encoded as even powers of two"
      in
      let outBits = bitReprCount (findOutputRepresentation p) in
      generateInitialization options.useDoublePrecisionFloats stateBits outBits
end

lang TrellisGenerateSetContainsChecks =
  FutharkAst + TrellisRepresentation

  -- For each set declaration, generate a Futhark function which checks whether
  -- a state (for values) or a pair of states (for transitions) is an element
  -- of the set. The result is a map from each set identifier to the
  -- corresponding function identifier and the generated function declarations.
  sem generateSetConstraints : TrellisProgram -> (Map Name Name, [FutDecl])
  sem generateSetConstraints =
  | p & (MainTrellisProgram {indecl = indecl}) ->
    let stateType = findStateType p in
    generateSetContainsCheckIndecl stateType (mapEmpty nameCmp) indecl

  sem generateSetContainsCheckIndecl
    : TrellisType -> Map Name Name -> [InModelDecl] -> (Map Name Name, [FutDecl])
  sem generateSetContainsCheckIndecl stateType names =
  | [SetInModelDecl {id = {v = id}, s = s, info = info}] ++ rest ->
    match generateSetContainsCheckIndecl stateType names rest with (names, decls) in
    let funId = nameSym (concat "in_" (nameGetStr id)) in
    let names = mapInsert id funId names in
    match generateSetConstraintsSet stateType s with (containsExprs, params) in
    let containsExpr =
      foldl
        (lam acc. lam e.
          futAppSeq_ (futConst_ (FCAnd ())) [acc, e])
        (head containsExprs)
        (tail containsExprs)
    in
    let decl = FDeclFun {
      ident = funId, entry = false, typeParams = [], params = params,
      ret = futBoolTy_, body = containsExpr, info = info
    } in
    (mapInsert id funId names, cons decl decls)
  | [_] ++ rest -> generateSetContainsCheckIndecl stateType names rest
  | [] -> (names, [])

  sem generateSetConstraintsSet : TrellisType -> TrellisSet -> ([FutExpr], [(Name, FutType)])
  sem generateSetConstraintsSet stateType =
  | BuilderTrellisSet {p = p, to = None _, e = e, info = info} ->
    let argType = FTyIdent {ident = nameNoSym "state_t", info = info} in
    let argId = nameSym "x" in
    match generateConstraintsPat stateType (nFutVar_ argId) p with (patConstraints, bound) in
    let exprConstraints = map (generateConstraintsExpr bound) e in
    (concat patConstraints exprConstraints, [(argId, argType)])
  | BuilderTrellisSet {p = p, to = Some to, e = e, info = info} ->
    let argType = FTyIdent {ident = nameNoSym "state_t", info = info} in
    let fstId = nameSym "x" in
    let sndId = nameSym "y" in
    let args = map (lam id. (id, argType)) [fstId, sndId] in
    match generateConstraintsPat stateType (nFutVar_ fstId) p with (lc, lbound) in
    match generateConstraintsPat stateType (nFutVar_ sndId) to with (rc, rbound) in
    let bound = mapUnion lbound rbound in
    let exprConstraints = map (generateConstraintsExpr bound) e in
    let patConstraints = concat lc rc in
    (concat patConstraints exprConstraints, args)
  | LiteralTrellisSet {info = info} ->
    errorSingle [info] "Generating constraints for literal sets not supported yet"

  sem generateConstraintsPat : TrellisType -> FutExpr -> TrellisPat -> ([FutExpr], Map Name FutExpr)
  sem generateConstraintsPat ty e =
  | p -> generateConstraintsPatH ty e [] (mapEmpty nameCmp) p

  sem generateElementConstraints : FutExpr -> (Int, TrellisPat, TrellisType)
                                -> ([FutExpr], Map Name FutExpr, Int)
                                -> ([FutExpr], Map Name FutExpr, Int)
  sem generateElementConstraints e elem =
  | (constraints, bound, shift) ->
    match elem with (elemBitsize, p, elemType) in
    let e =
      -- 1. Shift the bits of the provided expression to the right to align the
      -- bits belonging to this particular element with the least significant
      -- bits.
      let e1 =
        if eqi shift 0 then e
        else futAppSeq_ (futConst_ (FCShr ())) [e, futInt_ shift]
      in

      -- 2. Use bitwise AND to cancel out bits belonging to elements to the left
      -- of this element.
      let e2 =
        futAppSeq_ (futConst_ (FCBitAnd ())) [e1, futInt_ (subi (slli 1 elemBitsize) 1)]
      in

      -- 3. If the type of the element is an integer range with a non-zero
      -- lower bound, we need to translate the range back by adding its lower
      -- bound. This is because we always encode the lowest integer in the
      -- range as 0.
      match elemType with IntRangeTrellisType {lb = {v = lb & !0}} then
        futAdd_ e2 (futInt_ lb)
      else e2
    in
    match generateConstraintsPatH elemType e constraints bound p
    with (constraints, bound) in
    (constraints, bound, addi shift elemBitsize)

  sem generateConstraintsPatH : TrellisType -> FutExpr -> [FutExpr] -> Map Name FutExpr
                             -> TrellisPat -> ([FutExpr], Map Name FutExpr)
  sem generateConstraintsPatH ty e constraints bound =
  | ConTrellisPat {info = info} ->
    errorSingle [info] "Generating constraints for constructors not supported yet"
  | VarPTrellisPat {id = {v = id}} -> (constraints, mapInsert id e bound)
  | IntPTrellisPat {i = {v = i}, info = info} ->
    match ty with IntRangeTrellisType {lb = {v = lb}} then
      let c = futAppSeq_ (futConst_ (FCEq ())) [e, futInt_ (subi i lb)] in
      (cons c constraints, bound)
    else
      errorSingle [info] "Expected integer constraint to have int range type"
  | TruePTrellisPat _ -> (cons e constraints, bound)
  | FalsePTrellisPat _ ->
    let c = futIf_ e (futConst_ (FCBool {val = false})) (futConst_ (FCBool {val = true})) in
    (cons c constraints, bound)
  | ArrayPTrellisPat {p = p, info = info} ->
    -- TODO(larshum, 2024-01-20): Add a sanity check that ensures we have at
    -- most one dots pattern in the array and that it is bound to a variable.
    recursive let partitionArrayPatterns = lam lhs. lam p.
      switch p
      case [] then (lhs, None (), [])
      case [DotsTrellisPat {left = left}] ++ rest then (lhs, Some left, rest)
      case [h] ++ rest then partitionArrayPatterns (snoc lhs h) rest
      end
    in
    match
      match ty with ArrayTTrellisType {left = left, count = count, info = i} then
        match count with Some {v = c} then
          (left, c)
        else errorSingle [i] "Array type does not have an integer count"
      else errorSingle [info] "Array type mismatch"
    with (elemType, count) in
    let elemBitsize = bitReprCount (findTypeRepresentation (mapEmpty nameCmp) elemType) in
    match partitionArrayPatterns [] p with (lhs, dots, rhs) in

    -- We process the array from right to left, so that we can accumulate the
    -- number of bits needed to shift right to access the bits of the current
    -- element.
    let rhsElem = map (lam p. (elemBitsize, p, elemType)) rhs in
    let acc = foldr (generateElementConstraints e) (constraints, bound, 0) rhsElem in
    let acc =
      match dots with Some dotsPat then
        let dotsLength = subi count (addi (length lhs) (length rhs)) in
        let dotsType = ArrayTTrellisType {
          left = elemType, count = Some {i = info, v = dotsLength},
          namedCount = None (), info = info
        } in
        let dotsBitsize = muli dotsLength elemBitsize in
        let dotsElem = (dotsBitsize, dotsPat, dotsType) in
        generateElementConstraints e dotsElem acc
      else acc
    in
    let lhsElem = map (lam p. (elemBitsize, p, elemType)) lhs in
    match foldr (generateElementConstraints e) acc lhsElem with (constraints, bound, _) in
    (constraints, bound)
  | TupPTrellisPat {p = p, info = info} ->
    let elemTypes =
      match ty with TupleTTrellisType {t = t} then t
      else errorSingle [info] "Tuple type mismatch"
    in
    let elems =
      map
        (lam e.
          match e with (p, elemType) in
          let bits = bitReprCount (findTypeRepresentation (mapEmpty nameCmp) elemType) in
          (bits, p, elemType))
        (zip p elemTypes)
    in
    match foldr (generateElementConstraints e) (constraints, bound, 0) elems
    with (constraints, bound, _) in
    (constraints, bound)
  | DotsTrellisPat {info = info} ->
    errorSingle [info] "The '...' pattern cannot be used outside of array pattern"

  sem generateConstraintsExpr : Map Name FutExpr -> TrellisExpr -> FutExpr
  sem generateConstraintsExpr bound =
  | TrueTrellisExpr _ -> futConst_ (FCBool {val = true})
  | FalseTrellisExpr _ -> futConst_ (FCBool {val = false})
  | VarTrellisExpr {id = {v = id}, info = info} ->
    match mapLookup id bound with Some e then e
    else errorSingle [info] "Unbound variable in set builder constraint"
  | IntTrellisExpr {i = {v = i}} -> futInt_ i
  | AddTrellisExpr {left = left, right = right} ->
    futAppSeq_ (futConst_ (FCAdd ()))
      [ generateConstraintsExpr bound left
      , generateConstraintsExpr bound right ]
  | SubTrellisExpr {left = left, right = right} ->
    futAppSeq_ (futConst_ (FCSub ()))
      [ generateConstraintsExpr bound left
      , generateConstraintsExpr bound right ]
  | EqTrellisExpr {left = left, right = right} ->
    futAppSeq_ (futConst_ (FCEq ()))
      [ generateConstraintsExpr bound left
      , generateConstraintsExpr bound right ]
  | NeqTrellisExpr {left = left, right = right} ->
    futAppSeq_ (futConst_ (FCNeq ()))
      [ generateConstraintsExpr bound left
      , generateConstraintsExpr bound right ]
  | e ->
    errorSingle [get_TrellisExpr_info e] "Constraint generation not supported for this expression"
end

lang TrellisCompile =
  TrellisGenerateInitialization + TrellisGenerateSetContainsChecks

  type TrellisCompileResult = {
    -- Contains the initialization parts of the program
    initialization : FutProg,

    -- Contains the probability functions, their dependencies, and the entry
    -- point to the Futhark program.
    probabilityFunctions : FutProg
  }

  sem trellisCompile : TrellisOptions -> TrellisProgram -> TrellisCompileResult
  sem trellisCompile options =
  | p ->
    let init = generateInitializationHelper options p in
    match generateSetConstraints p with (setIds, decls) in
    -- TODO(larshum, 2024-01-19): generate the remaining parts of the code...
    { initialization = generateInitializationHelper options p
    , probabilityFunctions = FProg {decls = decls} }
end

lang TestLang = FutharkPrettyPrint + TrellisCompile
end

mexpr

use TestLang in

let values : FutProg -> (String, String, String, FutExpr) = lam prog.
  match prog with
    FProg {
      decls = [ FDeclModuleAlias {moduleId = fst},
                FDeclModuleAlias {moduleId = snd},
                FDeclModuleAlias {moduleId = trd},
                FDeclFun {body = body} ] }
  then
    (fst, snd, trd, body)
  else error "Unexpected initialization result"
in
let eqf = lam l. lam r.
  match l with (l1, l2, l3, l4) in
  match r with (r1, r2, r3, r4) in
  if forAll (lam p. p) [eqString l1 r1, eqString l2 r2, eqString l3 r3] then
    match (l4, r4) with (FEConst {val = FCInt {val = n1}}, FEConst {val = FCInt {val = n2}}) then
      eqi n1 n2
    else false
  else false
in
utest values (generateInitialization false 12 14) with ("i16", "i16", "f32", futInt_ 4096) using eqf in
utest values (generateInitialization true 12 14) with ("i16", "i16", "f64", futInt_ 4096) using eqf in
utest values (generateInitialization false 7 14) with ("i8", "i16", "f32", futInt_ 128) using eqf in
utest values (generateInitialization false 7 32) with ("i8", "i64", "f32", futInt_ 128) using eqf in
utest values (generateInitialization false 2 3) with ("i8", "i8", "f32", futInt_ 4) using eqf in

()
