include "seq.mc"

include "trellis-arg.mc"
include "model/compile.mc"

lang TrellisBuild = TrellisCompileBase
  -- Builds the resulting compiler output by producing a wrapper we can use via
  -- Python.
  sem buildPythonWrapper : TrellisCompileEnv -> String -> ()
  sem buildPythonWrapper env =
  | futharkProgramStr ->
    let options = env.options in
    let absPath = lam file. join [options.outputDir, "/", file] in

    -- 1. Write the generated Futhark code to a file
    let futFileName = "generated" in
    let futFile = concat futFileName ".fut" in
    writeFile (absPath futFile) futharkProgramStr;

    -- 2. Build the Futhark program using the appropriate backend
    assertCommandExists "futhark" "Used to compile the generated code";
    let cmd = ["futhark", options.futharkTarget, "--library", futFile] in
    let r = sysRunCommand cmd "" options.outputDir in
    if neqi r.returncode 0 then
      printLn (join ["Error when compiling Futhark code"]);
      printLn r.stdout;
      printLn r.stderr
    else

    -- 3. Prepare the Python FFI using the Futhark FFI build command
    assertCommandExists "build_futhark_ffi"
      (join [
        "Generates a Python FFI from the Futhark code.\n",
        "The command is provided by the futhark_ffi Python package."]);
    let r = sysRunCommand ["build_futhark_ffi", futFileName] "" options.outputDir in
    if neqi r.returncode 0 then
      printLn (join ["Error when generating the Python FFI helper code"]);
      printLn r.stdout;
      printLn r.stderr
    else

    -- 4. Write our generated Python wrapper code, which handles the Futhark
    -- call and automatically pads input signals.
    let pythonWrapperStr = generatePythonWrapper env futFileName in
    writeFile (absPath "viterbi.py") pythonWrapperStr;

    -- 5. Create an empty file '__init__.py' to allow calling the generated
    -- Python wrapper from another directory.
    writeFile (absPath "__init__.py") ""

  sem assertCommandExists : String -> String -> ()
  sem assertCommandExists cmd =
  | infoMsg ->
    if sysCommandExists cmd then ()
    else error infoMsg

  sem generatePythonWrapper : TrellisCompileEnv -> String -> String
  sem generatePythonWrapper env =
  | futFileName ->
    let batchSize = env.options.batchSize in
    let batchOverlap = env.options.batchOverlap in
    let batchOutputSize = subi batchSize batchOverlap in
    let signalsId = "signals" in
    let tableIds = mapKeys env.tables in
    let tableArgs =
      strJoin ", "
        (map (lam x. join ["args['", nameGetStr x, "']"]) tableIds)
    in
    -- TODO(larshum, 2024-01-28): How and where do we generate the predecessors?
    let pythonCode = strJoin "\n" [
      join ["def viterbi(", signalsId, ", args):"],
      join ["  nsignals = len(", signalsId, ")"],
      join ["  signal_lengths = [len(s) for s in ", signalsId, "]"],
      join [
        "  padded_signals = pad_signals(", signalsId, ", signal_lengths, ",
        int2string batchOutputSize, ", ", int2string batchOverlap, ")"],
      "  for i, s in enumerate(signals):",
      "    padded_signals[i][0:len(s)] = s",
      "  predecessors = read_predecessors()",
      join ["  viterbi = Futhark(_", futFileName, ")"],
      join ["  res = viterbi.viterbi(", tableArgs, ", predecessors, padded_signals)"],
      "  output = viterbi.from_futhark(res)",
      "  return unpad_outputs(output, signal_lengths)"
    ] in
    let pythonInitCode = readFile (concat trellisSrcLoc "skeleton/wrap.py") in
    concat pythonInitCode pythonCode
end
