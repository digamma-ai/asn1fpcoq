Require Import ZArith PArith.
Require Import ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits.
Require Import Lia.

Open Scope Z.

Axiom nblen: Z -> nat.

Inductive container (l : nat) :=
  cont (v : Z) (N : 0 <= v) (L : (nblen v <= l)%nat) : container l.
  
Definition join_cont {l1 l2 : nat} (c1 : container l1) (c2 : container l2)
  : container (l1 + l2).
Proof.
Admitted.

Definition split_cont {l1 l2: nat} (c : container (l1+l2))
  : container l1 * container l2.
Proof.
  intros.
  destruct c eqn:C.
Admitted.

Definition cont_cast {l1 l2 : nat} (c1 : container l1) (eq : l1 = l2) : container l2 :=
 match eq in _ = p return container p with
   | eq_refl => c1
 end.

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