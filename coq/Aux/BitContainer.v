Require Import ZArith PArith.
Require Import ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits.
Require Import Lia.

Open Scope Z.

Definition nblen (n : Z) : nat := Z.to_nat (Z.log2 n + 1).

Inductive container (l : nat) :=
  cont (v : Z) (N : 0 <= v) (L : (nblen v <= l)%nat) : container l.

Definition cast_cont {l1 l2 : nat} (c1: container l1) (E: l1 = l2): container l2 :=
  match E in _ = p return container p with
  | eq_refl => c1
  end.

Lemma join_nonneg (l2 : nat) {v1 v2 : Z} (N1: 0 <= v1) (N2: 0 <= v2):
  0 <= v1 * two_power_nat l2 + v2.
Proof.
  rewrite two_power_nat_correct.
  rewrite Zpower_nat_Z.
  remember (Z.of_nat l2) as p.
  remember (2 ^ p) as p2.
  assert(0 <= p2).
  {
    subst.
    apply Z.pow_nonneg.
    lia.
  }
  apply Z.add_nonneg_nonneg; auto.
  apply Z.mul_nonneg_nonneg; auto.
Qed.

Lemma join_nblen
      {l1 l2 : nat}
      {v1 v2: Z}
      (N1: 0 <= v1) (N2: 0 <= v2)
      (L1 : (nblen v1 <= l1)%nat)
      (L2 : (nblen v2 <= l2)%nat):
  (nblen (v1 * two_power_nat l2 + v2) <= l1 + l2)%nat.
Proof.
  unfold nblen in *.
  apply Nat2Z.inj_le.
  rewrite Z2Nat.id.
  -
    apply Nat2Z.inj_le in L1.
    apply Nat2Z.inj_le in L2.
    rewrite Z2Nat.id in L1.
    rewrite Z2Nat.id in L2.
    +
      rewrite Z.add_1_r in *.
      admit.
    +
      assert(0<=Z.log2 v2) by apply Z.log2_nonneg; lia.
    +
      assert(0<=Z.log2 v1) by apply Z.log2_nonneg; lia.
  -
    assert(0<=(Z.log2 (v1 * two_power_nat l2 + v2))) by apply Z.log2_nonneg.
    lia.
Admitted.

Definition join_cont {l1 l2 : nat} (c1 : container l1) (c2 : container l2)
  : container (l1 + l2) :=
  match c1, c2 with
  | cont _ v1 N1 L1, cont _ v2 N2 L2 =>
    cont (l1 + l2)
         (v1 * two_power_nat l2 + v2)
         (join_nonneg l2 N1 N2)
         (join_nblen N1 N2 L1 L2)
  end.

Definition split_cont {l1 l2: nat} (c : container (l1+l2))
  : container l1 * container l2.
Proof.
  destruct c as [v N B].
  remember (v mod (two_power_nat l2)) as v2.
  remember (v / (two_power_nat l2)) as v1.
  assert (N1 : 0 <= v1) by admit.
  assert (N2 : 0 <= v2) by admit.
  assert (L1 : (nblen v1 <= l1)%nat) by admit.
  assert (L2 : (nblen v2 <= l2)%nat) by admit.
  exact (cont l1 v1 N1 L1, cont l2 v2 N2 L2).
Admitted.

Lemma split_join_roundtrip {l1 l2 : nat} (c1 : container l1) (c2 : container l2) :
  split_cont (join_cont c1 c2) = (c1, c2).
Proof.
Admitted.







(* not sure about this stuff. Review later. Vadim *)

Definition cont_of_Z := cont.

Definition Z_of_cont {l : nat} (c : container l) :=
  match c with cont _ v _ _ => v end.

Lemma blen_Z_of_cont {l : nat} (c : container l) :
  (nblen (Z_of_cont c) <= l)%nat.
Proof. destruct c; auto. Qed.

Lemma nonneg_Z_of_cont {l : nat} (c : container l) :
  0 <= Z_of_cont c.
Proof. destruct c; auto. Qed.

Definition cont_Z_roundtrip {l : nat} (c : container l) :=
  match c with
  | cont _ v N L => cont_of_Z l (Z_of_cont c) (nonneg_Z_of_cont c) (blen_Z_of_cont c)
  end.