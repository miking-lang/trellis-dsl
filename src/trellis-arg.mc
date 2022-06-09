include "arg.mc"

type Options = {}

let default = {}

let config = []

let menu = lam. join [
  "Usage: trellis file.mc [<options>]\n\n",
  "Options:\n",
  argHelpOptions config,
  "\n"
]
