Require Import ZArith.
Require Import ASNDef.

(*
  calculate two's complement of an integer _z_
  on a given number of bits _b_
*)
Definition twos_complement (b : positive) (z : Z) : Z :=
  z mod (2 ^ Zpos b).

(*
  calculate two's complement of an integer _z_
  on the smallest number of octets possible
*)
Definition ASN_twos_complement (z : Z) : Z :=
  twos_complement (twos_octets z) z.