include "trellis.mc"

mexpr

let f = get argv 1 in
let s = readFile f in
let res = parseTrellisExn f s in

()

