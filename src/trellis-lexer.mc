include "parser/lexer.mc"

lang SetTokenParser = TokenParser
  syn Token =
  | SetUnionTok {info : Info}
  | SetIntersectionTok {info : Info}
  | SetMinusTok {info : Info}
  | SetInTok {info : Info}
  | SetNotinTok {info : Info}
  syn TokenRepr =
  | SetUnionRepr ()
  | SetIntersectionRepr ()
  | SetMinusRepr ()
  | SetInRepr ()
  | SetNotinRepr ()

  sem parseToken (pos : Pos) =
  | "\\u" ++ str ->
    let pos2 = advanceCol pos 3 in
    let info = makeInfo pos pos2 in
    {token = SetUnionTok {info = info}, lit = "\\u", info = info, stream = {pos = pos2, str = str}}
  | "\\n" ++ str ->
    let pos2 = advanceCol pos 3 in
    let info = makeInfo pos pos2 in
    {token = SetIntersectionTok {info = info}, lit = "\\n", info = info, stream = {pos = pos2, str = str}}
  | "\\in" ++ str ->
    let pos2 = advanceCol pos 4 in
    let info = makeInfo pos pos2 in
    {token = SetInTok {info = info}, lit = "\\in", info = info, stream = {pos = pos2, str = str}}
  | "\\notin" ++ str ->
    let pos2 = advanceCol pos 7 in
    let info = makeInfo pos pos2 in
    {token = SetNotinTok {info = info}, lit = "\\notin", info = info, stream = {pos = pos2, str = str}}
  | "\\setminus" ++ str ->
    let pos2 = advanceCol pos 10 in
    let info = makeInfo pos pos2 in
    {token = SetMinusTok {info = info}, lit = "\\setminus", info = info, stream = {pos = pos2, str = str}}

end

-- Eat line comments of the form #
lang TrellisLineCommentParser = WSACParser
  sem eatWSAC (p : Pos)  =
  | "#" ++ xs ->
    recursive
    let remove = lam p. lam str.
      match str with "\n" ++ xs then eatWSAC (advanceRow p 1) xs else
      match str with [x] ++ xs then remove (advanceCol p 1) xs else
      eatWSAC p str
    in remove p xs
end

lang TrellisDotsTokenParser = TokenParser
  syn Token =
  | DotsToken {info : Info}
  syn TokenRepr =
  | DotsRepr ()

  sem parseToken (pos : Pos) =
  | "..." ++ str ->
    let pos2 = advanceCol pos 3 in
    let info = makeInfo pos pos2 in
    {token = DotsToken {info = info}, lit = "...", info = info, stream = {pos = pos2, str = str}}

end
