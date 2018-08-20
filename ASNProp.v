Require Import PArith ZArith.
Require Import Lia.
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
Proof.
  unfold octets, bits_to_octets.
  assert(B: bits p  > 0) by apply gt_bits_O.
  Opaque bits. simpl.
  generalize (Nat.divmod_spec (bits p+7) 7 0 7).
  intros H.
  assert(S: 7<=7) by auto.
  specialize (H S). clear S.
  destruct (Nat.divmod (bits p + 7) 7 0 7).
  destruct H as [H1 H2].
  simpl.
  lia.
Qed.

Lemma twos_octets_correct (z : Z) :
  twos_bits z <= 8 * (twos_octets z) < twos_bits z + 8.
Admitted.