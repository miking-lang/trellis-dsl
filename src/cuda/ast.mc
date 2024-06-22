-- Extends the C AST in the standard library with the features we need to
-- generate efficient CUDA code.

include "c/ast.mc"

lang TrellisCudaUnsignedTypes = CExprTypeAst
  -- Defines unsigned integer types, as we use them in the CUDA code
  -- generation.
  syn CType =
  | CTyUChar ()
  | CTyUShort ()
  | CTyUInt ()
  | CTyULongLong ()
end

lang TrellisCudaConstType = CExprTypeAst
  -- Adds the const-qualifier as a type annotation - this may enable the
  -- compiler to make further optimizations.
  syn CType =
  | CTyConst {ty : CType}

  sem smapAccumLCTypeCType f acc =
  | CTyConst t ->
    match f acc t.ty with (acc, ty) in
    (acc, CTyConst {t with ty = ty})
end

lang TrellisCudaMacro = CTopAst
  -- The top-level macro definition takes an arbitrary string contaning the
  -- code to replace it with.
  syn CTop =
  | CTMacroDefine { id : Name, value : String }

  sem smap_CTop_CExpr f =
  | CTMacroDefine _ & t -> t

  sem sreplace_CTop_CStmt f =
  | CTMacroDefine _ & t -> t

  sem sfold_CTop_CStmt f acc =
  | CTMacroDefine _ -> acc
end

lang TrellisCudaTernary = CExprTypeAst
  -- Adds the ternary operation expression to simplify compilation of
  -- if-expressions.
  syn CExpr =
  | CETernary {cond : CExpr, thn : CExpr, els : CExpr}

  sem smapAccumLCExprCExpr f acc =
  | CETernary t ->
    match f acc t.cond with (acc, cond) in
    match f acc t.thn with (acc, thn) in
    match f acc t.els with (acc, els) in
    (acc, CETernary {t with cond = cond, thn = thn, els = els})
end

lang TrellisCudaAst =
  TrellisCudaUnsignedTypes + TrellisCudaConstType + TrellisCudaMacro +
  TrellisCudaTernary

  syn CuAnnotation =
  | CuAHost ()
  | CuADevice ()
  | CuAGlobal ()
  | CuAConstant ()
  | CuAExternC ()

  type CuTop = {
    annotations : [CuAnnotation],
    top : CTop
  }

  type CuProgram = {
    includes : [String],
    tops : [CuTop]
  }
end
