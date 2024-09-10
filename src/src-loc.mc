include "sys.mc"

let trellisSrcCwd = sysGetCwd ()

let trellisSrcLocUnix =
  match sysGetEnv "HOME" with Some path then
    join [path, "/.local/src/trellis/"]
  else error "Environment variable HOME not set"

let trellisSrcLoc =
  if sysFileExists trellisSrcLocUnix then trellisSrcLocUnix else trellisSrcCwd
