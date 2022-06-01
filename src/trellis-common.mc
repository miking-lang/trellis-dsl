include "seq.mc"
include "name.mc"
include "error.mc"

-- Returns `base` to the power of `exp`
let powi = lam base: Int. lam exp: Int.
  recursive let powH = lam acc. lam base. lam exp.
    switch exp
    case 0 then acc
    case 1 then muli acc base
    case _ then
      if eqi (modi exp 2) 0 then powH acc (muli base base) (divi exp 2)
      else powH (muli base acc) (muli base base) (divi (subi exp 1) 2)
    end
  in
  powH 1 base exp

utest powi 2 3 with 8
utest powi 5 10 with 9765625

-- The ith element of the result is the product of all elements to the right of
-- the elements in `seq`
let prodAllRight: [Int] -> [Int] = lam seq.
  recursive let prodH = lam acc. lam prod. lam seq.
    match seq with [] then acc
    else
      let newProd = muli prod (head seq) in
      prodH (cons newProd acc) newProd (tail seq)
  in
  prodH [] 1 (reverse seq)

utest prodAllRight [3,2,4] with [24,8,4]

recursive
let foldl3 : all a. all b. all c. all d. (a -> b -> c -> d -> a) -> a -> [b] -> [c] -> [d] -> a =
  lam f. lam acc. lam seq1. lam seq2. lam seq3.
    let g = lam acc : (a, [b]). lam x2. lam x3.
      match acc with (acc, [x1] ++ xs1) in (f acc x1 x2 x3, xs1)
    in
    match foldl2 g (acc, seq1) seq2 seq3 with (acc, _) in acc
end

utest foldl3 (lam a. lam x1. lam x2. lam x3. snoc a (x1, x2, x3)) [] [1, 2, 3] [4, 5, 6] [7, 8, 9]
with [(1, 4, 7), (2, 5, 8), (3, 6, 9)]

let zipWith3: all a. all b. all c. all d. (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d] =
  lam f. foldl3 (lam acc. lam x1. lam x2. lam x3. snoc acc (f x1 x2 x3)) []

utest zipWith3 (lam x. lam y. lam z. addi x (addi y z)) [1,2,3] [4,5,6] [7,8,9]
with [12,15,18]

let errorNameUnbound = lam i: Info. lam n: Name.
  errorSingle [i] (join [nameGetStr n, " is unbound"])
