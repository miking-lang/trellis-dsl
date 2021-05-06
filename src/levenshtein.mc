include "seq.mc"

let levenshtein = lam s1. lam s2.
  let n1 = addi (length s1) 1 in
  let n2 = addi (length s2) 1 in
  let mat = ref (create n1 (lam i. create n2 (lam i. 0))) in
  recursive let work = lam row. lam col.
    let val =
      if eqi row 0 then col
      else if eqi col 0 then row
      else
        let replace =
          let v = get (get (deref mat) (subi row 1)) (subi col 1) in
          if eqc (get s1 (subi row 1)) (get s2 (subi col 1)) then v else addi v 1
        in
        let insert = addi (get (get (deref mat) (subi row 1)) col) 1 in
        let delete = addi (get (get (deref mat) row) (subi col 1)) 1 in
        minOrElse (lam. error "Empty sequence") subi
                  [replace, insert, delete]
    in
    modref mat (set (deref mat) row (set (get (deref mat) row) col val));
    if and (eqi row (subi n1 1)) (eqi col (subi n2 1)) then
      ()
    else if eqi col (subi n2 1) then
      work (addi row 1) 0
    else
      work row (addi col 1)
  in
  work 0 0;
  get (get (deref mat) (length s1)) (length s2)

utest levenshtein "" "" with 0
utest levenshtein "massa" "maska" with 1
utest levenshtein "kitten" "sitting" with 3
utest levenshtein "ACGT" "GCT" with 2
