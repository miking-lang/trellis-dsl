
let is_predecessor (x : i64) (y : i64) : bool =
  transition_probability {} x y == 0.0

let count_preds (y : i64) : i64 =
  i64.sum (map (\x -> if is_predecessor x y then 1 else 0) (iota nstates))

let find_preds_state (maxpreds : i64) (y : i64) : [maxpreds]i64 =
  let preds = filter (\x -> is_predecessor x y) (iota nstates) in
  let preds =
    if length preds < maxpreds then
      preds ++ replicate (maxpreds - length preds) (-1)
    else preds
  in
  preds[0:maxpreds]

entry find_preds (_ : i64) : [nstates][]i64 =
  let maxpreds = i64.maximum (map count_preds (iota nstates)) in
  map (find_preds_state maxpreds) (iota nstates)
