include "parser/lexer.mc"

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
