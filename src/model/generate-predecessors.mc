include "futhark/ast.mc"
include "futhark/pprint.mc"

include "ast.mc"
include "compile.mc"
include "encode.mc"
include "pprint.mc"
include "../src-loc.mc"
include "../trellis-common.mc"

lang TrellisWritePredecessors
  -- Writes the predecessors to a file
  sem writePredecessors : String -> [[Int]] -> ()
  sem writePredecessors outputDir =
  | preds ->
    let file = join [outputDir, "/", predecessorsFileName] in
    writeFile file (strJoin "\n" (map (lam p. strJoin " " (map int2string p)) preds))
end

lang TrellisParsePredecessors
  syn Tok =
  | LBrace ()
  | RBrace ()
  | Comma ()
  | Num Int

  type ParseState = (String, Int)

  -- Attempts to parse the predecessors from a file containing the Futhark
  -- encoded integer outputs.
  sem parsePredecessors : String -> Option [[Int]]
  sem parsePredecessors =
  | str ->
    let initState = (str, 0) in
    match nextToken initState with Some (s, LBrace _) then
      match parsePredecessorsH s with Some (s, preds) then
        match nextToken s with Some (s, RBrace _) then
          match nextToken s with None () then
            Some preds
          else None ()
        else None ()
      else None ()
    else None ()

  sem parsePredecessorsH : ParseState -> Option (ParseState, [[Int]])
  sem parsePredecessorsH =
  | state ->
    recursive let work = lam acc. lam state.
      let t = nextToken state in
      match t with None () then Some (state, acc)
      else match t with Some (s, LBrace _) then
        match parseInnerSequence s with Some (s, seq) then
          match nextToken s with Some (s, RBrace _) then
            let acc = snoc acc seq in
            match nextToken s with Some (s, Comma _) then
              work acc s
            else Some (s, acc)
          else None ()
        else None ()
      else None ()
    in work [] state

  sem parseInnerSequence : ParseState -> Option (ParseState, [Int])
  sem parseInnerSequence =
  | state ->
    recursive let work = lam acc. lam state.
      match nextToken state with Some (state, Comma _) then
        match nextToken state with Some (state, Num n) then
          let acc = if eqi n (negi 1) then acc else snoc acc n in
          work acc state
        else None ()
      else Some (state, acc)
    in
    match nextToken state with Some (state, Num n) then
      work [n] state
    else None ()

  sem nextToken : ParseState -> Option (ParseState, Tok)
  sem nextToken =
  | (s, i) ->
    if lti i (length s) then
      let c = get s i in
      if isWhitespace c then nextToken (s, addi i 1)
      else if eqc c '-' then tokenizeNegativeNumber (s, i)
      else if isDigit c then tokenizeNumber (s, i)
      else
        let tok =
          switch c
          case '[' then Some (LBrace ())
          case ']' then Some (RBrace ())
          case ',' then Some (Comma ())
          case _ then None ()
          end
        in
        optionMap (lam t. ((s, addi i 1), t)) tok
    else None ()

  sem tokenizeNegativeNumber : ParseState -> Option (ParseState, Tok)
  sem tokenizeNegativeNumber =
  | (s, i) ->
    match tokenizeNumber (s, addi i 1) with Some (state, Num n) then
      Some (state, Num (negi n))
    else None ()

  sem tokenizeNumber : ParseState -> Option (ParseState, Tok)
  sem tokenizeNumber =
  | state ->
    recursive let tokNumber = lam n. lam state.
      let c = get state.0 state.1 in
      if isDigit c then
        let n = addi (muli n 10) (subi (char2int c) (char2int '0')) in
        tokNumber n (state.0, addi state.1 1)
      else if eqc c 'i' then
        -- NOTE(larshum, 2024-02-09): We assume the Futhark code uses 64-bit
        -- signed integers and prints the literal suffix.
        match subsequence state.0 state.1 3 with "i64" then
          Some ((state.0, addi state.1 3), Num n)
        else None ()
      else None ()
    in tokNumber 0 state
end

lang TrellisGeneratePredecessors =
  TrellisModelAst + TrellisWritePredecessors + TrellisParsePredecessors +
  TrellisCompileInitializer + TrellisEncode + FutharkAst + FutharkPrettyPrint

  -- Attempts to compute the predecessors of each state for a given model. The
  -- result is a nested sequence, where the row at index i corresponds to the
  -- predecessors of the state encoded as i. If successful, the function
  -- creates a file 'predecessors.txt' in the output directory and updates the
  -- environment to contain the number of predecessors.
  --
  -- This function can fail, for example if given a model for which all
  -- predecessors cannot fit in memory. In this case, we assume all states are
  -- predecessors.
  sem computePredecessors : TrellisCompileEnv -> TModel -> TrellisCompileEnv
  sem computePredecessors env =
  | model ->
    let futharkCode = generateFutharkCode env model in
    let tempDir = compileFutharkCode futharkCode in
    match runFutharkBinary tempDir with Some outputStr then
      match parsePredecessors outputStr with Some preds then
        writePredecessors env.options.outputDir preds;
        let maxpreds = foldl maxi 0 (map length preds) in
        {env with maxpreds = maxpreds}
      else env
    else env

  -- Generates Futhark code for finding the predecessors of all states.
  sem generateFutharkCode : TrellisCompileEnv -> TModel -> String
  sem generateFutharkCode env =
  | model ->
    let i = NoInfo () in
    let stateTy = nFutIdentTy_ stateTyId in
    let transArgs = [(model.transition.x, stateTy), (model.transition.y, stateTy)] in
    let cases =
      map
        (lam c.
          {c with body = EProb {p = 1.0, ty = TProb {info = i}, info = i}})
        model.transition.cases
    in
    match generateProbabilityFunction env i transitionProbabilityId transArgs cases
    with (_, {decl = decl}) in
    let stateTyStr =
      match pprintType 0 pprintEnvEmpty (stateFutharkType env) with (_, s) in
      s
    in
    let probTyStr = if env.options.useDoublePrecisionFloats then "f64" else "f32" in
    let p = FProg {decls = [
      FDeclModuleAlias {ident = stateModuleId, moduleId = stateTyStr, info = NoInfo ()},
      FDeclModuleAlias {ident = probModuleId, moduleId = probTyStr, info = NoInfo ()},
      FDeclType {
        ident = stateTyId, typeParams = [],
        ty = futProjTy_ (nFutIdentTy_ stateModuleId) "t", info = NoInfo ()},
      FDeclType {
        ident = probTyId, typeParams = [],
        ty = futProjTy_ (nFutIdentTy_ probModuleId) "t", info = NoInfo ()},
      constructTablesType env,
      FDeclConst {
        ident = nstatesId, ty = FTyInt {info = NoInfo (), sz = I64 ()},
        val = futInt_ (cardinalityType env.stateType), info = NoInfo ()},
      decl
    ]} in
    let predsCode = readFile (concat trellisSrcLoc "skeleton/preds.fut") in
    join [printFutProg p, predsCode]

  -- Compiles the generated Futhark code for computing the predecessors. If
  -- this stage fails, we report an error as it is due to a bug in the code
  -- generation.
  sem compileFutharkCode : String -> String
  sem compileFutharkCode =
  | code ->
    let predsFile = "preds.fut" in
    let tempDir = sysTempDirMake () in
    let srcPath = join [tempDir, "/", predsFile] in
    writeFile srcPath code;
    if not (sysCommandExists "futhark") then
      error "Futhark is used to compile the code generated by the Trellis compiler"
    else
      let compileResult = sysRunCommand ["futhark", "multicore", predsFile] "" tempDir in
      if eqi compileResult.returncode 0 then tempDir
      else error "Failed to compile intermediate Futhark program for finding predecessors"

  -- Attempts to run the compiled Futhark binary. If this is successful, we
  -- return the output sent to standard out (the predecessors in a Futhark
  -- format).
  --
  -- Note that the execution may fail if the model has too many predecessors to
  -- represent in memory. In this case, we assume the model has an infinite
  -- number of predecessors.
  sem runFutharkBinary : String -> Option String
  sem runFutharkBinary =
  | tempDir ->
    let runResult = sysRunCommand ["./preds", "--entry-point", "find_preds"] "0" tempDir in
    if eqi runResult.returncode 0 then Some runResult.stdout
    else None ()
end

lang TestLang = TrellisGeneratePredecessors + TrellisModelPrettyPrint
end

mexpr

use TestLang in

-- Parsing the predecessors from a string
utest parsePredecessors "[[0i64, 1i64], [0i64, 1i64]]" with Some [[0, 1], [0, 1]] in
utest parsePredecessors "[[0i64, 1i64], [0i64, -1i64]]" with Some [[0, 1], [0]] in

()
