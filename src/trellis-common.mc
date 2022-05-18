-- Helper functions and misc

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
