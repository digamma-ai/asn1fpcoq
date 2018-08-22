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

Check Nat.divmod_spec (8 + 7) 7 0 7.

Lemma gt_bitstooctets_O (b : nat) :
  b > 0 -> bits_to_octets b > 0.
Proof.
  intros H1.
  unfold bits_to_octets. simpl.
  generalize (Nat.divmod_spec (b + 7) 7 0 7).
  intros H2.
  assert (H3: 7<=7) by reflexivity.
  apply H2 in H3. clear H2.
  destruct (Nat.divmod (b + 7) 7 0 7) as (q',u').
  destruct H3 as [H4 H5].
  simpl.
  lia.
Qed.

Lemma gt_octets_O (p : positive) :
  octets p > 0.
Proof.
  unfold octets.
  apply gt_bitstooctets_O.
  apply gt_bits_O.
Qed.

Lemma gt_twosoctets_O (z : Z) :
  twos_octets z > 0.
Proof.
  unfold twos_octets.
  apply gt_bitstooctets_O.
  apply gt_twosbits_O.
Qed.

Lemma bits_to_octets_correct (b : nat) :
  b <= 8 * bits_to_octets b < b + 8.
Admitted.