-- Extracting useful information from the Trellis AST that is not easily
-- accessible due to the shape of the (generated) AST.

include "ast.mc"

lang TrellisExtract = TrellisAst
  sem findStateType : TrellisProgram -> TrellisType
  sem findStateType =
  | MainTrellisProgram {indecl = indecl} ->
    _findStateTypeH indecl

  sem _findStateTypeH : [InModelDecl] -> TrellisType
  sem _findStateTypeH =
  | [StatePropertyInModelDecl {ty = ty}] ++ _ -> ty
  | [_] ++ rest -> _findStateTypeH rest
  | _ -> error "Could not find state property declaration in model"

  sem findOutputType : TrellisProgram -> TrellisType
  sem findOutputType =
  | MainTrellisProgram {indecl = indecl} ->
    _findOutputTypeH indecl

  sem _findOutputTypeH : [InModelDecl] -> TrellisType
  sem _findOutputTypeH =
  | [OutputPropertyInModelDecl {ty = ty}] ++ _ -> ty
  | [_] ++ rest -> _findOutputTypeH rest
  | _ -> error "Could not find output property declaration in model"
end
