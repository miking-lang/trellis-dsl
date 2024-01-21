include "seq.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

include "ast.mc"
include "repr.mc"
include "trellis-arg.mc"

let initialProbabilityId = nameSym "initial_probability"
let outputProbabilityId = nameSym "output_probability"
let transitionProbabilityId = nameSym "transition_probability"

let stateTyId = nameSym "state_t"
let probTyId = nameSym "prob_t"
let obsTyId = nameSym "obs_t"

lang TrellisCompileExpression = TrellisAst + FutharkAst
  sem compileTrellisExpr : Map Name FutType -> TrellisExpr -> FutExpr
  sem compileTrellisExpr params =
  | TrueTrellisExpr {info = info} ->
    FEConst {val = FCBool {val = true}, ty = FTyBool {info = info}, info = info}
  | FalseTrellisExpr {info = info} ->
    FEConst {val = FCBool {val = false}, ty = FTyBool {info = info}, info = info}
  | VarTrellisExpr {id = {v = id}, info = info} ->
    let defaultVar = lam.
      FEVar {ident = id, ty = FTyUnknown {info = info}, info = info}
    in
    match mapLookup id params with Some (FTyIdent {ident = tyId}) then
      if nameEq tyId stateTyId then
        -- TODO(larshum, 2024-01-21): We need to handle the state_t parameters
        -- in a different way, depending on how they are used, as they are
        -- a bitset in the generated code but may have a different type in the
        -- DSL code.
        defaultVar ()
      else defaultVar ()
    else defaultVar ()
  | ConstrTrellisExpr {info = info} ->
    let msg = join [
      "Compilation of constructors is not supported.\n",
      "All constructors should be eliminated in the simplification pass."
    ] in
    errorSingle [info] msg
  | IntTrellisExpr {i = {v = i}, info = info} ->
    FEConst {val = FCInt {val = i, sz = None ()}, ty = FTyUnknown {info = info}, info = info}
  | TupleProjTrellisExpr {left = left, idx = {v = idx}, info = info} ->
    FEProj {
      target = compileTrellisExpr params left,
      label = stringToSid (int2string idx), ty = FTyUnknown {info = info},
      info = info
    }
  | ArrayAccessTrellisExpr {left = left, e = e, info = info} ->
    FEArrayAccess {
      array = compileTrellisExpr params left, index = compileTrellisExpr params e,
      ty = FTyUnknown {info = info}, info = info
    }
  | IfTrellisExpr {c = c, thn = thn, right = right, info = info} ->
    FEIf {
      cond = compileTrellisExpr params c, thn = compileTrellisExpr params thn,
      els = compileTrellisExpr params right, ty = FTyUnknown {info = info},
      info = info
    }
  | AddTrellisExpr {left = left, right = right, info = info} ->
    compileTrellisBinOp info params (FCAdd ()) left right
  | SubTrellisExpr {left = left, right = right, info = info} ->
    compileTrellisBinOp info params (FCSub ()) left right
  | MulTrellisExpr {left = left, right = right, info = info} ->
    -- TODO(larshum, 2024-01-21): Is this integer or probability
    -- multiplication? If the latter, we need to compile it to use addition
    -- instead...
    compileTrellisBinOp info params (FCMul ()) left right
  | EqTrellisExpr {left = left, right = right, info = info} ->
    compileTrellisBinOp info params (FCEq ()) left right
  | NeqTrellisExpr {left = left, right = right, info = info} ->
    compileTrellisBinOp info params (FCNeq ()) left right
  | e ->
    errorSingle [get_TrellisExpr_info e] "Compilation of expression not supported yet"

  sem compileTrellisBinOp : Info -> Map Name FutType -> FutConst -> TrellisExpr
                         -> TrellisExpr -> FutExpr
  sem compileTrellisBinOp info param op lhs =
  | rhs ->
    FEApp {
      lhs = FEApp {
        lhs = FEConst {val = op, ty = FTyUnknown {info = info}, info = info},
        rhs = compileTrellisExpr param lhs,
        ty = FTyUnknown {info = info}, info = info
      },
      rhs = compileTrellisExpr param rhs,
      ty = FTyUnknown {info = info}, info = info
    }
end

lang TrellisCompileProbabilityDeclaration = TrellisCompileExpression
  sem compileProbDecl : Map Name Name -> Map Name FutType -> ProbDecl -> FutExpr
  sem compileProbDecl setIds paramMap =
  | OneProbDecl {e = e} -> compileTrellisExpr paramMap e
  | CasesProbDecl {cases = cases, info = info} ->
    let addParam = lam acc. lam p.
      match p with (id, ty) in
      FEApp {
        lhs = acc, rhs = FEVar {ident = id, ty = ty, info = info},
        ty = FTyBool {info = info}, info = info
      }
    in
    let probTy = FTyIdent {ident = probTyId, info = info} in
    let compileCase = lam c. lam acc.
      match c with {set = {v = setId}, e = e} in
      let params = mapBindings paramMap in
      let setContainsId =
        match mapLookup setId setIds with Some setContainsFunId then
          setContainsFunId
        else errorSingle [info] "Probability function case depends on undefined set"
      in
      let setContainsExpr = FEVar {
        ident = setContainsId, ty = FTyUnknown {info = info}, info = info
      } in
      let condExpr = foldl addParam setContainsExpr params in
      let body = compileTrellisExpr paramMap e in
      FEIf {cond = condExpr, thn = body, els = acc, ty = probTy, info = info}
    in
    let probModule = FEVar {
      ident = nameNoSym "prob", ty = FTyUnknown {info = info}, info = info
    } in
    let defaultCase = FEApp {
      lhs = FEProj {
        target = probModule, label = stringToSid "neg",
        ty = FTyArrow {from = probTy, to = probTy, info = info}, info = info
      },
      rhs = FEProj {
        target = probModule, label = stringToSid "inf", ty = probTy, info = info
      },
      ty = probTy, info = info
    } in
    foldr compileCase defaultCase cases
end

lang TrellisGenerateInitialization =
  FutharkAst + FutharkTypePrettyPrint + TrellisRepresentation

  -- Finds the smallest integer type in Futhark that can fit the given number of bits.
  sem findSmallestIntegerType : Int -> FutType
  sem findSmallestIntegerType =
  | n ->
    -- NOTE(larshum, 2024-01-19): Currently, we represent the state using a
    -- signed integer, because using unsigned integers requires a lot of
    -- additional casts to work properly. Therefore, we lose one bit of information.
    let sz =
      if lti n 8 then I8 ()
      else if lti n 16 then I16 ()
      else if lti n 32 then I32 ()
      else if lti n 64 then I64 ()
      else error "Trellis does not support states that require more than 63 bits to encode"
    in
    FTyInt {info = NoInfo (), sz = sz}

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
      FTyFloat {info = NoInfo (), sz = if useDoublePrecision then F64 () else F32 ()}
    in
    match pprintType 0 pprintEnvEmpty probType with (_, probTypeStr) in
    -- TODO(larshum, 2024-01-19): When the number of states are not continuous,
    -- we will not have the number of states be a power of two. In these cases,
    -- we may want to use the actual count and an array to map index to the
    -- corresponding (valid) state representation.
    let nstates = slli 1 stateBits in
    FProg {decls = [
      FDeclModuleAlias {ident = nameNoSym "state", moduleId = stateTypeStr, info = NoInfo ()},
      FDeclModuleAlias {ident = nameNoSym "obs", moduleId = obsTypeStr, info = NoInfo ()},
      FDeclModuleAlias {ident = nameNoSym "prob", moduleId = probTypeStr, info = NoInfo ()},
      FDeclFun {ident = nameNoSym "nstates", entry = false, typeParams = [], params = [],
                ret = FTyInt {info = NoInfo (), sz = I64 ()}, body = futInt_ nstates,
                info = NoInfo ()}
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
    let argType = FTyIdent {ident = stateTyId, info = info} in
    let argId = nameSym "x" in
    match generateConstraintsPat stateType (nFutVar_ argId) p with (patConstraints, bound) in
    let exprConstraints = map (generateConstraintsExpr bound) e in
    (concat patConstraints exprConstraints, [(argId, argType)])
  | BuilderTrellisSet {p = p, to = Some to, e = e, info = info} ->
    let argType = FTyIdent {ident = stateTyId, info = info} in
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
    match elem with (elemBitwidth, p, elemType) in
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
      futAppSeq_ (futConst_ (FCBitAnd ())) [e1, futInt_ (subi (slli 1 elemBitwidth) 1)]
    in
    match generateConstraintsPatH elemType e constraints bound p
    with (constraints, bound) in
    (constraints, bound, addi shift elemBitwidth)

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
    let elemBitwidth = bitReprCount (findTypeRepresentation (mapEmpty nameCmp) elemType) in
    match partitionArrayPatterns [] p with (lhs, dots, rhs) in

    -- We process the array from right to left, so that we can accumulate the
    -- number of bits needed to shift right to access the bits of the current
    -- element.
    let rhsElem = map (lam p. (elemBitwidth, p, elemType)) rhs in
    let acc = foldr (generateElementConstraints e) (constraints, bound, 0) rhsElem in
    let acc =
      match dots with Some dotsPat then
        let dotsLength = subi count (addi (length lhs) (length rhs)) in
        let dotsType = ArrayTTrellisType {
          left = elemType, count = Some {i = info, v = dotsLength},
          namedCount = None (), info = info
        } in
        let dotsBitwidth = muli dotsLength elemBitwidth in
        let dotsElem = (dotsBitwidth, dotsPat, dotsType) in
        generateElementConstraints e dotsElem acc
      else acc
    in
    let lhsElem = map (lam p. (elemBitwidth, p, elemType)) lhs in
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
          let bitWidth = bitReprCount (findTypeRepresentation (mapEmpty nameCmp) elemType) in
          (bitWidth, p, elemType))
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

lang TrellisGenerateProbabilityFunctions =
  TrellisRepresentation + TrellisCompileProbabilityDeclaration

  type ProbDef = {
    -- Mapping from the table arguments expected by the probability function to
    -- their type.
    tableArgs : Map Name FutType,

    -- The generated Futhark declaration of a probability function.
    decl : FutDecl
  }

  -- We encode each of the initial, output, and transition probabilities as an
  -- optional value, initially None. When we find the definition in the Trellis
  -- AST, we generate the required properties and set it to some. In a valid
  -- Trellis program, all three should be Some after extraction.
  type ProbDefs = {
    initial : Option ProbDef,
    output : Option ProbDef,
    transition : Option ProbDef
  }

  sem emptyProbDefs : () -> ProbDefs
  sem emptyProbDefs =
  | _ -> {initial = None (), output = None (), transition = None ()}

  sem generateProbabilityDefinitions : Map Name Name -> TrellisProgram -> (Map Name FutType, [FutDecl])
  sem generateProbabilityDefinitions setIds =
  | MainTrellisProgram {indecl = indecl} ->
    let tables = collectModelTables (mapEmpty nameCmp) indecl in
    let probDefs =
      foldl (extractProbabilityDefinition setIds tables) (emptyProbDefs ()) indecl
    in
    match probDefs with {initial = Some i, output = Some o, transition = Some t} then
      (mapUnion (mapUnion i.tableArgs o.tableArgs) t.tableArgs, [i.decl, o.decl, t.decl])
    else error "Model does not define initial, output, and transition probabilities"

  sem collectModelTables : Map Name FutType -> [InModelDecl] -> Map Name FutType
  sem collectModelTables acc =
  | [TableInModelDecl {id = {v = id}, dim = dim, ty = ty, info = info}] ++ rest ->
    let addTypeDimension = lam card. lam ty.
      FTyArray { elem = ty, dim = Some (AbsDim card), info = info }
    in
    let cards = map (findTypeCardinality (mapEmpty nameCmp)) dim in
    let outType =
      match ty with ProbTTrellisType {info = info} then
        FTyIdent {ident = probTyId, info = info}
      else
        errorSingle [info] "Currently, we only support tables of probabilities"
    in
    let tableType = foldr addTypeDimension outType cards in
    collectModelTables (mapInsert id tableType acc) rest
  | [_] ++ rest -> collectModelTables acc rest
  | [] -> acc

  sem extractProbabilityDefinition : Map Name Name -> Map Name FutType -> ProbDefs
                                  -> InModelDecl -> ProbDefs
  sem extractProbabilityDefinition setIds tables probDefs =
  | ProbInModelDecl (p & {init = Some _, out = None _, trans = None _}) ->
    match p with {fst = {v = xId}, pd = pd} in
    let tables = collectTableReferences tables (mapEmpty nameCmp) p.pd in
    let stateParam = (xId, FTyIdent {ident = stateTyId, info = p.info}) in
    let paramMap = mapFromSeq nameCmp [stateParam] in
    let initialDecl = FDeclFun {
      ident = initialProbabilityId, entry = false, typeParams = [],
      params = snoc (mapBindings tables) stateParam,
      ret = FTyIdent {ident = probTyId, info = p.info},
      body = compileProbDecl setIds paramMap p.pd, info = p.info
    } in
    let def = {tableArgs = tables, decl = initialDecl} in
    {probDefs with initial = Some def}
  | ProbInModelDecl (p & {init = None _, out = Some _, trans = None _}) ->
    match p with {fst = {v = xId}, snd = Some {v = outId}} in
    let tables = collectTableReferences tables (mapEmpty nameCmp) p.pd in
    let params =
      [ (xId, FTyIdent {ident = stateTyId, info = p.info})
      , (outId, FTyIdent {ident = obsTyId, info = p.info}) ]
    in
    let paramMap = mapFromSeq nameCmp params in
    let outputDecl = FDeclFun {
      ident = outputProbabilityId, entry = false, typeParams = [],
      params = concat (mapBindings tables) params,
      ret = FTyIdent {ident = probTyId, info = p.info},
      body = compileProbDecl setIds paramMap p.pd, info = p.info
    } in
    let def = {tableArgs = tables, decl = outputDecl} in
    {probDefs with output = Some def}
  | ProbInModelDecl (p & {init = None _, out = None _, trans = Some _}) ->
    match p with {fst = {v = xId}, snd = Some {v = yId}} in
    let tables = collectTableReferences tables (mapEmpty nameCmp) p.pd in
    let params =
      [ (xId, FTyIdent {ident = stateTyId, info = p.info})
      , (yId, FTyIdent {ident = stateTyId, info = p.info}) ]
    in
    let paramMap = mapFromSeq nameCmp params in
    let transitionDecl = FDeclFun {
      ident = transitionProbabilityId, entry = false, typeParams = [],
      params = concat (mapBindings tables) params,
      ret = FTyIdent {ident = probTyId, info = p.info},
      body = compileProbDecl setIds paramMap p.pd, info = p.info
    } in
    let def = {tableArgs = tables, decl = transitionDecl} in
    {probDefs with transition = Some def}
  | _ -> probDefs

  sem collectTableReferences : Map Name FutType -> Map Name FutType -> ProbDecl -> Map Name FutType
  sem collectTableReferences tables acc =
  | OneProbDecl {e = e} -> collectTableReferencesExpr tables acc e
  | CasesProbDecl {cases = cases} ->
    let collectTableReferencesCase = lam acc. lam c.
      match c with {e = e} in
      collectTableReferencesExpr tables acc e
    in
    foldl collectTableReferencesCase acc cases

  sem collectTableReferencesExpr : Map Name FutType -> Map Name FutType -> TrellisExpr -> Map Name FutType
  sem collectTableReferencesExpr tables acc =
  | VarTrellisExpr {id = {v = id}} ->
    match mapLookup id tables with Some ty then mapInsert id ty acc
    else acc
  | e -> sfold_TrellisExpr_TrellisExpr (collectTableReferencesExpr tables) acc e
end

lang TrellisGenerateEntryPoint = TrellisAst + FutharkAst
  sem generateViterbiEntryPoint : Map Name FutType -> FutDecl
  sem generateViterbiEntryPoint =
  | tables ->
    let stateTy = FTyIdent {ident = stateTyId, info = NoInfo ()} in
    let obsTy = FTyIdent {ident = obsTyId, info = NoInfo ()} in
    let nId = nameSym "n" in
    let mId = nameSym "m" in
    let retType = FTyArray {
      elem = FTyArray {
        elem = stateTy, dim = None (), info = NoInfo ()
      },
      dim = Some (NamedDim nId), info = NoInfo ()
    } in
    -- TODO(larshum, 2024-01-21): Include the predecessors and input signals as
    -- parameters to the entry point function.
    let predsId = nameSym "predecessors" in
    let predsTy = FTyArray {
      elem = FTyArray {elem = stateTy, dim = None (), info = NoInfo ()},
      dim = Some (NamedDim (nameNoSym "nstates")), info = NoInfo ()
    } in
    let inputSignalsId = nameSym "input_signals" in
    let inputSignalsTy = FTyArray {
      elem = FTyArray {elem = obsTy, dim = Some (NamedDim mId), info = NoInfo ()},
      dim = Some (NamedDim nId), info = NoInfo ()
    } in
    let params =
      concat
        (mapBindings tables)
        [ (predsId, predsTy), (inputSignalsId, inputSignalsTy) ]
    in
    let body = FEConst {
      val = FCInt {val = 0, sz = None ()}, ty = FTyUnknown {info = NoInfo ()},
      info = NoInfo ()
    } in
    FDeclFun {
      ident = nameNoSym "viterbi", entry = true,
      typeParams = [FPSize {val = nId}, FPSize {val = mId}],
      params = params, ret = retType, body = body,
      info = NoInfo ()
    }
end

lang TrellisCompile =
  TrellisGenerateInitialization + TrellisGenerateSetContainsChecks +
  TrellisGenerateProbabilityFunctions + TrellisGenerateEntryPoint

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
    match generateProbabilityDefinitions setIds p with (tables, probDecl) in
    let entry = generateViterbiEntryPoint tables in
    { initialization = generateInitializationHelper options p
    , probabilityFunctions = FProg {decls = join [decls, probDecl, [entry]]} }
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
