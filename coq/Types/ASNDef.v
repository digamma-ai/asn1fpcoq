Require Import PArith ZArith.
Require Import Flocq.Core.Zaux Flocq.Core.Digits.
Require Import ASN1FP.Aux.Bits.

Open Scope Z.

(* ISO/IEC 8825-1:2015 *)

(*
  floats encoded in ASN.1 can have base 2,4,8,16
  [ 8.5.7.2 ]
*)
Definition radix4  := Build_radix  4 (refl_equal _).
Definition radix8  := Build_radix  8 (refl_equal _).
Definition radix16 := Build_radix 16 (refl_equal _).

Section BER.

(*
  for practical purposes ASN.1 BER floats are encoded in short form
  thus having a limit of
  127 content octets [ 8.1.3.4 ]

  1 of these is used by a standard information octet
  [ 8.5.6 - 8.5.7.4 ]

  126 are left.

  the total number of octets,
  taken up by significand and exponent, needs to be < 127


  if exponent takes up more than 3 octets,
  an additional octet is required to encode exponent's lenth,
  [ 8.5.7.4 d) ]
  thus the total number of octets,
  taken up by significand and exponent, needs to be < 126
*)
Definition bounded (m : positive) (e : Z) : bool :=
  let mo := olen (Zpos m) in
  let eo := twos_olen e in
  if Z.ltb 3 eo
    then Z.ltb (mo + eo) 126
    else Z.ltb (mo + eo) 127.

(*
  binary radices defined in ASN.1 BER: 2, 4, 8, 16
  [ 8.5.7.2 ]
*)
Definition valid_radix (b : radix) : bool :=
  (b =? 2) || (b =? 4) || (b =? 8) || (b =? 16).

Definition valid_scaling (f : Z) : bool :=
  (-1 <? f) && (f <? 4).

(*
  is a given triple (b,f,m,e)
  ( encoding the number m*(2^f)*(b^e) )
  in a format accepted by ASN.1 BER
*)
Definition valid_BER (b : radix) (f : Z) (m : positive) (e : Z) : bool :=
  (bounded m e) && (valid_radix b) && (valid_scaling f).
(*
  ASN.1 BER "RealSpecialValues":
  +inf, -inf, NaN, -0
  [ 8.5.9 ]
  
  or finite values
  [8.5.7]
  
  the value "+0" is defined separately in [ 8.5.3 ]
  and, in our scope, shall be treated as a special value
*)
Inductive BER_float :=
  | BER_zero (s : bool)
  | BER_infinity (s : bool)
  | BER_nan
  | BER_finite (s : bool) (b : radix) (f : Z) (m : positive) (e : Z) :
    (valid_BER b f m e = true) -> BER_float.

(*
  is the encoding a finite real number
*)
Definition is_finite (r : BER_float) : bool :=
  match r with
  | BER_zero _ => true
  | BER_finite _ _ _ _ _ _ => true
  | _ => false
  end.

(*
  strict equality:
  check if all parts are exactly equal
*)
Definition BER_float_strict_eqb (f1 f2 : BER_float) : bool :=
  match f1,f2 with
  | BER_zero s1, BER_zero s2 => Bool.eqb s1 s2
  | BER_infinity s1, BER_infinity s2 => Bool.eqb s1 s2
  | BER_nan, BER_nan => true
  | BER_finite s1 b1 f1 m1 e1 _, BER_finite s2 b2 f2 m2 e2 _ =>
    (Bool.eqb s1 s2) && (Z.eqb b1 b2) && (Z.eqb f1 f2) && (Pos.eqb m1 m2) && (Z.eqb e1 e2)
  | _ , _ => false
  end.

Definition valid_BER_sumbool (b : radix) (f : Z) (m : positive) (e : Z) :=
  Sumbool.sumbool_of_bool (valid_BER b f m e).

End BER.

Section DER.

  (*
  Fixpoint derize (m e : Z) {measure (abs_nat m)}: Z * Z :=
    if orb (Z.odd m) (m =? 0)
    then (m, e)
    else derize (Z.div2 m) (e + 1).
  *)

End DER.