open Core
open String
open Big_int

let rec bytes_of_big_int bi =
  let base = big_int_of_int 256 in
  let (q,r) = quomod_big_int bi base in
  let t = char_of_int (int_of_big_int r) in
  (if eq_big_int q zero_big_int then "" else bytes_of_big_int q)
  ^ of_char t

let rec big_int_of_bytes ?acc:(a=big_int_of_int 0) s =
  let base = big_int_of_int 256 in
  if is_empty s then a
  else
    let x = get s 0 in
    let xs = drop_prefix s 1 in
    let v = big_int_of_int (int_of_char x) in
    big_int_of_bytes ~acc:((add_big_int (mult_big_int a base) v)) xs

let unsigned_big_int_of_int64 (i:int64) =
  let open Core in
  let open Int64 in
  if i < Int64.zero
  then add_big_int (succ_big_int (big_int_of_int64 Int64.max_int)) (big_int_of_int64 i)
  else big_int_of_int64 i

let big_int_of_float (f:float) =
  big_int_of_int64 (Int64.bits_of_float f)

let float_of_big_int fbi =
  Int64.float_of_bits (int64_of_big_int fbi)

let float_of_bi_of_float (f:float) =
  float_of_big_int (big_int_of_float f)

(**************************************************************************)

let bi_of_int_of_bi bi =
  let _ = Printf.eprintf "Testing bi -> int -> bi:\n" in
  (bi == big_int_of_int (int_of_big_int bi))

let bi_of_bytes_of_bi bi =
  let _ = Printf.eprintf "Testing bi -> bytes -> bi:\n" in
  (bi == big_int_of_bytes (bytes_of_big_int bi))

let int_of_bibytes_of_int i =
  let bytes = (bytes_of_big_int (big_int_of_int i)) in
  let round = int_of_big_int (big_int_of_bytes bytes) in
  (*let _ = Printf.eprintf "Testing int -> big_int_bytes -> int. %i -> %b -> %r" i bytes round in *)
  round

let bibytes_of_int i =
  bytes_of_big_int (big_int_of_int i)

