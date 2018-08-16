Require Import PArith ZArith.
Require Import ASNDef ASNCalc.

Lemma twos_octets_correct :
  forall z : Z, (twos_bits z <= 8 * (twos_octets z) < twos_bits z + 8)%positive.
Admitted.

Lemma twos_comp_nonnegative :
  forall (b : positive) (z : Z), Z.le 0 (twos_complement b z).
Admitted.
