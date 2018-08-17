Require Import PArith ZArith.
Require Import Flocq.Core.Zaux Flocq.Core.Digits.
(* ISO/IEC 8825-1:2015 *)

(*
  reals encoded in ASN.1 can have base 2,4,8,16
  [ 8.5.7.2 ]
*)
Definition radix4  := Build_radix  4 (refl_equal _).
Definition radix8  := Build_radix  8 (refl_equal _).
Definition radix16 := Build_radix 16 (refl_equal _).

(*
  smallest number of octets
  enough to encode a postive N

  here - number of digits in
  N's base-256 representation
*)
Definition octets (p : positive) : positive :=
  let radix256 := Build_radix 256 (refl_equal _) in
  Z.to_pos (Zdigits radix256 (Zpos p)).

Example octets_255 : octets 255 = 1%positive.
Proof. reflexivity. Qed.
Example octets_256 : octets 256 = 2%positive.
Proof. reflexivity. Qed.

(*
  smallest number of bits enough to
  encode an integers two's complement

  when given N bits, two's complement representation
  can encode integer values in the range
  [-2^(N-1), 2^(N-1)-1].
  _(twos_bits z)_ calculates the smallest N
  such that _z_ is in that range.
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

(*
  smallest number of octets enough to
  encode an integers two's complement.

  that equals
  the number of bits two's complement would take,
  divided by 8, rounded towads plus infinity
*)
Definition twos_octets (z : Z) : positive :=
  Z.to_pos ((Zpos (twos_bits z) + 7) / 8).

Example twos_octets_128 : twos_octets 128 = 2%positive.
Proof. reflexivity. Qed.
Example twos_octets_n128 : twos_octets (- 128) = 1%positive.
Proof. reflexivity. Qed.

(*
  for practical purposes ASN reals are encoded in short form
  thus having a limit of
  127 content octets [ 8.1.3.4 ]

  1 of these is used by a standard information octet
  [ 8.5.6 - 8.5.7.4 ]

  126 is left.

  the total number of octets,
  taken up by significand and exponent needs to be <= 126

  if exponent takes up more than 3 octets,
  an additional octet is required to encode exponent's lenth,
  [ 8.5.7.4 d) ]
  thus the total number of octets,
  taken up by significand and exponent needs to be <= 125
*)
Definition ASN_bounded (m : positive) (e : Z) : bool :=
  let mo := octets m in
  let eo := twos_octets e in
    if Pos.gtb eo 3
    then Pos.leb (mo + eo) 125
    else Pos.leb (mo + eo) 126.

(*
  binary radices defined in ASN.1 BER: 2, 4, 8, 16
  [ 8.5.7.2 ]
*)
Definition ASN_good_radix (b : radix) : bool :=
  match (radix_val b) with
  | 2%Z => true
  | 4%Z => true
  | 8%Z => true
  | 16%Z => true
  | _ => false
  end.

(*
  ASN.1 BER "RealSpecialValues":
  +inf, -inf, NaN, -0
  [ 8.5.9 ]
  
  or finite values
  [8.5.7]
  
  (the value "+0" is defined separately in [ 8.5.3 ]
  and, in our scope, shall be treated as a special value)
*)
Inductive ASN_real :=
  | ASN_zero (s : bool)
  | ASN_infinity (s : bool)
  | ASN_nan
  | ASN_finite (s : bool) (m : positive) (b : radix) (e : Z) :
    andb (ASN_bounded m e) (ASN_good_radix b) = true -> ASN_real.
