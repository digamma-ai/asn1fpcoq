Require Import ZArith.
Require Import ASNDef.

(*
  calculate two's complement of an integer _z_
  on a given number of bits _b_
*)
Let twos_complement (b : nat) (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => Pos.to_nat p
  | Zneg p => (2 ^ b) - Pos.to_nat p
  end.

(*
  calculate two's complement of an integer _z_
  on the smallest number of octets possible
*)
Definition octet_twos_complement (z : Z) : nat :=
  twos_complement (8 * (twos_octets z)) z.