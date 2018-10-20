open FullBin
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

let big_int_of_float (f:float) =
  let fi = Int64.of_float_unchecked f in
  big_int_of_int64 fi

let ocaml_float64_to_BER_exact (f:float): String.t option =
  let fb = big_int_of_float f in
  match float64_to_BER_exact fb with
  | None -> None
  | Some bbi -> Some (bytes_of_big_int bbi)

let ocaml_BER_to_float64_exact (ab:string): float option =
  let ai = big_int_of_bytes ab in
  match coq_BER_to_float64_exact ai with
  | None -> None
  | Some fbi -> Some (float_of_big_int fbi)

let ocaml_BER_to_float64_rounded (m:Binary.mode) (ab:string): float option =
  let ai = big_int_of_bytes ab in
  match coq_BER_to_float64_rounded m ai with
  | None -> None
  | Some fbi -> Some (float_of_big_int fbi)
