Require Import PArith ZArith.
Require Import ASNDef ASNCalc.

Lemma gt_bits_O (p : positive) :
  bits p > 0.
Proof. 
  unfold bits.
  apply gt_Sn_O.
Qed.

Lemma gt_twosbits_O (z : Z) :
  twos_bits z > 0.
Proof.
  unfold twos_bits.
  destruct z.
  - apply gt_Sn_O.
  - apply gt_Sn_O.
  - destruct Zeq_bool.
    + apply gt_bits_O.
    + apply gt_Sn_O.
Qed.

Lemma gt_octets_O (p : positive) :
  octets p > 0.
Admitted.

Lemma twos_octets_correct (z : Z) :
  twos_bits z <= 8 * (twos_octets z) < twos_bits z + 8.
Admitted.