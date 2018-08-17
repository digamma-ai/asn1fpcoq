Require Import PArith ZArith.
Require Import Flocq.Core.Zaux Flocq.Core.Digits.

(* radices for ASN *)
Definition radix4  := Build_radix  4 (refl_equal _).
Definition radix8  := Build_radix  8 (refl_equal _).
Definition radix16 := Build_radix 16 (refl_equal _).

(* plain # of octets a number takes up *)
Definition octets (p : positive) : positive :=
  let radix256 := Build_radix 256 (refl_equal _) in
  Z.to_pos (Zdigits radix256 (Zpos p)).

Example octets_255 : octets 255 = 1%positive.
Proof. reflexivity. Qed.
Example octets_256 : octets 256 = 2%positive.
Proof. reflexivity. Qed.

(* smallest # of bits enough for 2s compl *)
(*
  this should be

    if z = -2^k
      return k+1
    else
      return (Zdigits2 z) + 1
 *)
Definition twos_bits (z : Z) : positive :=
  match z with
    | Z0 => 1
    | Zpos _ => Z.to_pos(Zdigits2 z + 1)
    | Zneg zn => 
      let zp := Zpos zn in
      let k := Z.log2 zp in
        if Zeq_bool (2 ^ k) zp
        then Z.to_pos(k+1)
        else Z.to_pos(Zdigits2 zp + 1)
  end.
                                
Example twos_bits_8 : twos_bits 8 = 5%positive.
Proof. reflexivity. Qed.
Example twos_bits_n8 : twos_bits (- 8) = 4%positive.
Proof. reflexivity. Qed.

(* smallest # of octets enough for 2s compl *)
Definition twos_octets (z : Z) : positive :=
  Z.to_pos ((Zpos (twos_bits z) + 7) / 8).

Example twos_octets_128 : twos_octets 128 = 2%positive.
Proof. reflexivity. Qed.
Example twos_octets_n128 : twos_octets (- 128) = 1%positive.
Proof. reflexivity. Qed.

(* is a real bounded for ASN *)
Definition ASN_bounded (m : positive) (e : Z) : bool :=
  let mo := octets m in
  let eo := twos_octets e in
    if Pos.gtb eo 3
    then Pos.leb (mo + eo) 125
    else Pos.leb (mo + eo) 126.

(* is radix accepted in ASN BER *)
(* definitely subject to change *)
Definition ASN_good_radix (b : radix) : bool :=
  match (radix_val b) with
  | 2%Z => true
  | 4%Z => true
  | 8%Z => true
  | 16%Z => true
  | _ => false
  end.

(* real type from ASN.1 BER *)
Inductive ASN_real :=
  | ASN_zero (s : bool)
  | ASN_infinity (s : bool)
  | ASN_nan
  | ASN_finite (s : bool) (m : positive) (b : radix) (e : Z) :
    andb (ASN_bounded m e) (ASN_good_radix b) = true -> ASN_real.
