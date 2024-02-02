include "seq.mc"
include "sys.mc"

include "src-loc.mc"
include "trellis-arg.mc"
include "trellis-common.mc"
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
    let futFileName = generatedFileName in
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
    writeFile (absPath "trellis.py") pythonWrapperStr;

    -- 5. Create an empty file '__init__.py' to allow calling the generated
    -- Python wrapper from another directory.
    writeFile (absPath "__init__.py") ""

  sem assertCommandExists : String -> String -> ()
  sem assertCommandExists cmd =
  | infoMsg ->
    if sysCommandExists cmd then ()
    else error infoMsg

  sem indent : Int -> String
  sem indent =
  | n -> create (muli n 4) (lam. ' ')

  sem generatePythonWrapper : TrellisCompileEnv -> String -> String
  sem generatePythonWrapper env =
  | futFileName ->
    let gpuTarget =
      match env.options.futharkTarget with "cuda" | "opencl" then true
      else false
    in
    let batchSize = env.options.batchSize in
    let batchOverlap = env.options.batchOverlap in
    let batchOutputSize = subi batchSize batchOverlap in
    let signalsId = "signals" in
    let tableIds = mapKeys env.tables in
    let tableArgs =
      join (map (lam x. join ["self.args['", nameGetStr x, "'], "]) tableIds)
    in
    let pythonGlueCode = strJoin "\n" [
      join [indent 1, "def viterbi(self, ", signalsId, "):"],
      join [
        indent 2, "padded_signals = pad_signals(", signalsId, ", ",
        int2string batchOutputSize, ", ", int2string batchOverlap, ")"],
      join [indent 2, "res = self.hmm.viterbi(", tableArgs, "self.vpreds, padded_signals)"],
      join [indent 2, "output = self.hmm.from_futhark(res)"],
      join [indent 2, "return unpad_outputs(output, ", signalsId, ")"],
      "",
      if gpuTarget then generateForwardGpuWrapper signalsId tableArgs
      else generateForwardCpuWrapper signalsId tableArgs
    ] in
    let pythonInitCode = readFile (concat trellisSrcLoc "skeleton/wrap.py") in
    concat pythonInitCode pythonGlueCode

  -- Generates Python wrapper code for the Forward algorithm when using a CPU
  -- target (C or multicore C).
  sem generateForwardCpuWrapper : String -> String -> String
  sem generateForwardCpuWrapper signalsId =
  | tableArgs ->
    strJoin "\n" [
      join [indent 1, "def forward(self, ", signalsId, "):"],
      join [indent 2, "lens = np.array([len(x) for x in ", signalsId, "])"],
      join [indent 2, "padded_signals = pad_signals(", signalsId, ", 0, 0)"],
      join [indent 2, "res = self.hmm.forward_cpu(", tableArgs, "self.fwpreds, padded_signals, lens)"],
      join [indent 2, "return self.hmm.from_futhark(res)"]
    ]

  -- Generates Python wrapper code for the Forward algorithm when using a GPU
  -- target (CUDA or OpenCL).
  sem generateForwardGpuWrapper : String -> String -> String
  sem generateForwardGpuWrapper signalsId =
  | tableArgs ->
    strJoin "\n" [
      join [indent 1, "def forward(self, ", signalsId, "):"],
      join [indent 2, "lens = np.array([len(x) for x in ", signalsId, "])"],
      join [indent 2, "padded_signals = pad_signals(", signalsId, ", 0, 0)"],
      join [indent 2, "res = self.hmm.forward_gpu(", tableArgs, "self.fwpreds, padded_signals)"],
      join [indent 2, "out = self.hmm.log_sum_exp_entry(res, lens)"],
      join [indent 2, "return self.hmm.from_futhark(out)"]
    ]
end
