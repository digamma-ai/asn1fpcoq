Require Import ZArith.
Require Import ASNDef.

Definition twos_complement (b : positive) (z : Z) : Z :=
  z mod (2 ^ Zpos b).

Definition ASN_twos_complement (z : Z) : Z :=
  twos_complement (twos_octets z) z.