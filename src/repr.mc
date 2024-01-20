include "ast.mc"
include "trellis-common.mc"

lang TrellisRepresentationBase = TrellisAst + TrellisExtract
  -- NOTE(larshum, 2024-01-19): Used to indicate how many bits are needed to
  -- encode the state of a Trellis program, and whether this encoding is
  -- continuous. If any constituent of a state is not a power of two (except
  -- the leftmost one), the encoding is discontinuous with respect to the
  -- index.
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

  sem findTypeRepresentation : Map Name BitRepr -> TrellisType -> BitRepr
  sem findTypeRepresentation types =
  | ArrayTTrellisType {left = left, count = count, info = info} ->
    let n =
      match count with Some {v = v} then
        v
      else
        errorSingle [info] "Array size is not an integer literal"
    in
    bitReprMap (muli n) (findTypeRepresentation types left)
  | ConcreteTrellisType {id = {v = id}, info = info} ->
    match mapLookup id types with Some repr then repr
    else errorSingle [info] "Type declaration not found"
  | TupleTTrellisType {t = t, info = info} ->
    let findRepr = lam acc. lam ty.
      let repr = findTypeRepresentation types ty in
      match (acc, repr) with (Continuous n, Continuous m) then
        Continuous (addi n m)
      else
        Discontinuous (addi (bitReprCount acc) (bitReprCount repr))
    in
    foldl findRepr (Continuous 0) t
  | IntRangeTrellisType {lb = {v = lb}, ub = ub, info = info} ->
    match ub with Some {v = v} then
      let count = addi (subi v lb) 1 in
      findIntegerBitRepresentation count
    else
      errorSingle [info] "Integer range upper bound is not an integer literal"
  | BoolTrellisType _ -> Continuous 1
  | IntTTrellisType {info = info} ->
    errorSingle [info] "Integer type is infinite"
  | ProbTTrellisType {info = info} ->
    errorSingle [info] "Probability type is infinite"

  -- Constructs a map from each declared type to its bit representation.
  sem constructDeclTypeBitReprMap : Map Name BitRepr -> Decl -> Map Name BitRepr
  sem constructDeclTypeBitReprMap m =
  | TypeDecl {id = {v = id}, constr = constr} ->
    let repr = findIntegerBitRepresentation (length constr) in
    mapInsert id repr m
  | LetDecl _ -> m
    
  sem findModelTypeRepresentation : (TrellisProgram -> TrellisType) -> TrellisProgram -> BitRepr
  sem findModelTypeRepresentation f =
  | p & (MainTrellisProgram {d = d, indecl = indecl, info = info}) ->
    let types = foldl constructDeclTypeBitReprMap (mapEmpty nameCmp) d in
    findTypeRepresentation types (f p)
end

lang TrellisStateRepresentation = TrellisRepresentationBase
  sem findStateRepresentation : TrellisProgram -> BitRepr
  sem findStateRepresentation =
  | p -> findModelTypeRepresentation findStateType p
end

lang TrellisOutputRepresentation = TrellisRepresentationBase
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
let types = mapFromSeq nameCmp [(n, Continuous 2)] in
let ty1 = BoolTrellisType {info = NoInfo ()} in
let ty2 = IntRangeTrellisType {
  lb = {i = NoInfo (), v = 1}, ub = Some {i = NoInfo (), v = 10},
  namedUb = None (), info = NoInfo ()
} in
let ty3 = TupleTTrellisType {t = [ty1, ty2], info = NoInfo ()} in
let ty4 = TupleTTrellisType {t = [ty1, ty1], info = NoInfo ()} in
let ty5 = ConcreteTrellisType {id = {i = NoInfo (), v = n}, info = NoInfo ()} in
utest findTypeRepresentation types ty1 with Continuous 1 in
utest findTypeRepresentation types ty2 with Discontinuous 4 in
utest findTypeRepresentation types ty3 with Discontinuous 5 in
utest findTypeRepresentation types ty4 with Continuous 2 in
utest findTypeRepresentation types ty5 with Continuous 2 in

()
