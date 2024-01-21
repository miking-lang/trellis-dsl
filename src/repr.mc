include "ast.mc"
include "trellis-common.mc"

lang TrellisRepresentationBase = TrellisAst
  -- NOTE(larshum, 2024-01-19): Used to indicate how many bits are needed to
  -- encode the state of a Trellis program, and whether this encoding is
  -- continuous. If any constituent of a state is not a power of two (except
  -- the leftmost one), the encoding is discontinuous as not very bit
  -- representation from zero to the cardinality of the type will be a valid
  -- state.
  syn BitRepr =
  | Continuous Int
  | Discontinuous Int

  sem bitReprCount : BitRepr -> Int
  sem bitReprCount =
  | Continuous n -> n
  | Discontinuous n -> n

  sem bitReprMap : (Int -> Int) -> BitRepr -> BitRepr
  sem bitReprMap f =
  | Continuous n -> Continuous (f n)
  | Discontinuous n -> Discontinuous (f n)

  sem bitReprAdd : BitRepr -> BitRepr -> BitRepr
  sem bitReprAdd lhs =
  | Continuous r ->
    match lhs with Continuous l then
      Continuous (addi l r)
    else
      Discontinuous (addi (bitReprCount lhs) r)
  | Discontinuous r -> Discontinuous (addi (bitReprCount lhs) r)

  sem findIntegerBitRepresentation : Int -> BitRepr
  sem findIntegerBitRepresentation =
  | 0 -> Continuous 0
  | 1 -> Discontinuous 1
  | n ->
    recursive let findRepr = lam c. lam i.
      if lti i n then findRepr (addi c 1) (slli i 1)
      else if eqi i n then Continuous c
      else Discontinuous c
    in
    findRepr 0 1

  -- Finds the cardinality of a given type, in terms of how many elements it
  -- consists of.
  sem findTypeCardinality : Map Name Int -> TrellisType -> Int
  sem findTypeCardinality typeCardinalities =
  | ArrayTTrellisType {left = left, count = count, info = info} ->
    let n =
      match count with Some {v = v} then v
      else errorSingle [info] "Array size is not an integer literal"
    in
    let powi = lam b. lam e.
      recursive let work = lam acc. lam e.
        if eqi e 0 then acc
        else work (muli acc b) (subi e 1)
      in work 1 e
    in
    powi (findTypeCardinality typeCardinalities left) n
  | ConcreteTrellisType {id = {v = id}, info = info} ->
    match mapLookup id typeCardinalities with Some n then n
    else errorSingle [info] "Declaration of concrete type not found"
  | TupleTTrellisType {t = t, info = info} ->
    foldl (lam acc. lam elem. muli acc (findTypeCardinality typeCardinalities elem)) 1 t
  | IntRangeTrellisType {lb = {v = lb}, ub = ub, info = info} ->
    match ub with Some {v = v} then
      addi (subi v lb) 1
    else
      errorSingle [info]
        "Cannot find cardinality of integer range with non-integer uppper bound"
  | BoolTrellisType _ -> 2
  | IntTTrellisType {info = info} | ProbTTrellisType {info = info} ->
    errorSingle [info] "Cannot find cardinality of infinite type"

  sem findTypeRepresentation : Map Name BitRepr -> TrellisType -> BitRepr
  sem findTypeRepresentation typeRepr =
  | ArrayTTrellisType {left = left, count = count, info = info} ->
    let n =
      match count with Some {v = v} then v
      else errorSingle [info] "Array size is not an integer literal"
    in
    bitReprMap (muli n) (findTypeRepresentation typeRepr left)
  | ConcreteTrellisType {id = {v = id}, info = info} ->
    match mapLookup id typeRepr with Some repr then repr
    else errorSingle [info] "Declaration of concrete type not found"
  | TupleTTrellisType {t = t, info = info} ->
    foldl bitReprAdd (Continuous 0) (map (findTypeRepresentation typeRepr) t)
  | IntRangeTrellisType {lb = {v = lb}, ub = ub, info = info} ->
    match ub with Some {v = v} then
      findIntegerBitRepresentation (addi (subi v lb) 1)
    else
      errorSingle [info]
        "Cannot find bit representation of integer range with non-integer uppper bound"
  | BoolTrellisType _ -> findIntegerBitRepresentation 2
  | IntTTrellisType {info = info} | ProbTTrellisType {info = info} ->
    errorSingle [info] "Cannot find bit representation of infinite type"

  -- Adds a mapping from a declared type identifier to its cardinality
  sem constructDeclTypeCardinalityMap : Map Name Int -> Decl -> Map Name Int
  sem constructDeclTypeCardinalityMap m =
  | TypeDecl {id = {v = id}, constr = constr} -> mapInsert id (length constr) m
  | _ -> m

  -- Adds a mapping from a declared type identifier to its bitwise representation
  sem constructDeclTypeReprMap : Map Name BitRepr -> Decl -> Map Name BitRepr
  sem constructDeclTypeReprMap m =
  | TypeDecl {id = {v = id}, constr = constr} ->
    let repr = findIntegerBitRepresentation (length constr) in
    mapInsert id repr m
  | _ -> m

  sem findModelTypeRepresentation : (TrellisProgram -> TrellisType) -> TrellisProgram -> BitRepr
  sem findModelTypeRepresentation f =
  | p & (MainTrellisProgram {d = d, indecl = indecl, info = info}) ->
    let types = foldl constructDeclTypeReprMap (mapEmpty nameCmp) d in
    findTypeRepresentation types (f p)
end

lang TrellisStateRepresentation = TrellisRepresentationBase + TrellisExtract
  sem findStateRepresentation : TrellisProgram -> BitRepr
  sem findStateRepresentation =
  | p -> findModelTypeRepresentation findStateType p
end

lang TrellisOutputRepresentation = TrellisRepresentationBase + TrellisExtract
  sem findOutputRepresentation : TrellisProgram -> BitRepr
  sem findOutputRepresentation =
  | p -> findModelTypeRepresentation findOutputType p
end

lang TrellisRepresentation =
  TrellisStateRepresentation + TrellisOutputRepresentation
end

mexpr

use TrellisRepresentation in

utest findIntegerBitRepresentation 0 with Continuous 0 in
utest findIntegerBitRepresentation 1 with Discontinuous 1 in
utest findIntegerBitRepresentation 2 with Continuous 1 in
utest findIntegerBitRepresentation 3 with Discontinuous 2 in
utest findIntegerBitRepresentation 4 with Continuous 2 in
utest findIntegerBitRepresentation 11 with Discontinuous 4 in
utest findIntegerBitRepresentation 12 with Discontinuous 4 in
utest findIntegerBitRepresentation 16 with Continuous 4 in
utest findIntegerBitRepresentation 17 with Discontinuous 5 in
utest findIntegerBitRepresentation 100 with Discontinuous 7 in

let n = nameNoSym "Nucleotide" in
let typeSizes = mapFromSeq nameCmp [(n, 4)] in
let typeReprs = mapFromSeq nameCmp [(n, Continuous 2)] in
let ty1 = BoolTrellisType {info = NoInfo ()} in
let ty2 = IntRangeTrellisType {
  lb = {i = NoInfo (), v = 1}, ub = Some {i = NoInfo (), v = 10},
  namedUb = None (), info = NoInfo ()
} in
let ty3 = TupleTTrellisType {t = [ty1, ty2], info = NoInfo ()} in
let ty4 = TupleTTrellisType {t = [ty1, ty1], info = NoInfo ()} in
let ty5 = ConcreteTrellisType {id = {i = NoInfo (), v = n}, info = NoInfo ()} in
utest findTypeCardinality typeSizes ty1 with 2 in
utest findTypeCardinality typeSizes ty2 with 10 in
utest findTypeCardinality typeSizes ty3 with 20 in
utest findTypeCardinality typeSizes ty4 with 4 in
utest findTypeCardinality typeSizes ty5 with 4 in
utest findTypeRepresentation typeReprs ty1 with Continuous 1 in
utest findTypeRepresentation typeReprs ty2 with Discontinuous 4 in
utest findTypeRepresentation typeReprs ty3 with Discontinuous 5 in
utest findTypeRepresentation typeReprs ty4 with Continuous 2 in
utest findTypeRepresentation typeReprs ty5 with Continuous 2 in

-- NOTE(larshum, 2024-01-21): Due to our bitwise encoding, repetition of
-- elements that do not use all bit encodings of the bits they require may lead
-- to a mismatch between the cardinality of the type and its bit width.
let ty6 = IntRangeTrellisType {
  lb = {i = NoInfo (), v = 1}, ub = Some {i = NoInfo (), v = 6},
  namedUb = None (), info = NoInfo ()
} in
let ty7 = ArrayTTrellisType {
  left = ty6, count = Some {i = NoInfo (), v = 3},
  namedCount = None (), info = NoInfo ()
} in
utest findTypeCardinality typeSizes ty6 with 6 in
utest findTypeCardinality typeSizes ty7 with 216 in
utest findTypeRepresentation typeReprs ty6 with Discontinuous 3 in
utest findTypeRepresentation typeReprs ty7 with Discontinuous 9 in

()
