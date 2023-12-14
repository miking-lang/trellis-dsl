
include "trellis.mc"
include "trellis-arg.mc"
include "enumerate-states.mc"
include "pprint.mc"
include "resolve-lets.mc"

mexpr

-- Parse command-line arguments
let result = argParse default config in
match result with ParseOK r then
  let options: Options = r.options in
  -- Exactly one file as argument?
  if neqi (length r.strings) 1 then
    -- No, print the menu and exit
    print (menu ());
    exit 0
  else
    -- Yes, read and parse the file
    let filename = head r.strings in
    let ast = parseTrellisExn filename (readFile filename) in

    let ast = use TrellisResolveVariables in resolveLetVariables ast in

    printLn (use TrellisPrettyPrint in pprintTrellis ast);

    ()
else
  argPrintError result;
  exit 1
