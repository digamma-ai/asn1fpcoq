Require Import ZArith PArith.
Require Import ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits.
Require Import Lia.

Open Scope Z.

Inductive container (l : Z) :=
  cont (v : Z) (N : 0 <= v) (L : blen v <= l) : container l.
  
Definition join_cont {l1 l2 : Z} (c1 : container l1) (c2 : container l2)
  : container (l1 + l2).
  destruct c1 eqn:C1; rename v into v1, N into N1, L into L1.
  destruct c2 eqn:C2; rename v into v2, N into N2, L into L2.
  remember (l1 + l2) as l.
  remember (v1 * 2^l2 + v2) as v.
  assert (N : 0 <= v) by admit. (** trivial *)
  assert (L : blen v <= l).
  {
    subst.
    unfold blen in *.
    admit.
    (** somewhat complicated, has been attempted before *)
  }
  exact (cont l v N L).
Admitted.

Definition split_cont_by_fst {l : Z} (l1 : Z) (c : container l)
  : (l1 <= l) -> container l1 * container (l - l1).
  intros.
  destruct c eqn:C.
  remember (l - l1) as l2.
  remember (v mod 2^l2) as v2.
  remember (v / 2^l2) as v1.
  assert (N1 : 0 <= v1) by admit.
  assert (N2 : 0 <= v2) by admit.
  assert (L1 : blen v1 <= l1) by admit.
  assert (L2 : blen v2 <= l2) by admit.
  exact (cont l1 v1 N1 L1, cont l2 v2 N2 L2).
Admitted.

Definition cont_cast {l1 l2 : Z} (c1 : container l1) (eq : l1 = l2) : container l2 :=
 match eq in _ = p return container p with
   | eq_refl => c1
 end.

Lemma blen_pos (a : Z) :
  0 < blen a.
Proof. unfold blen; generalize (Z.log2_nonneg a); lia. Qed.

Definition split_join {l1 l2 : Z} (c1 : container l1) (c2 : container l2)
  : container l1 * container l2.
  remember (join_cont c1 c2) as j.
  destruct c1; rename v into v1, N into N1, L into L1.
  destruct c2; rename v into v2, N into N2, L into L2.
  generalize (blen_pos v2); intros.
  assert (l1 <= l1 + l2) by lia.
  assert (l1 + l2 - l1 = l2) by lia.
  destruct (split_cont_by_fst l1 j H0) as [c1' c2'].
  exact (c1', cont_cast c2' H1).
Defined.

Lemma split_join_roundtrip {l1 l2 : Z} (c1 : container l1) (c2 : container l2) :
  split_join c1 c2 = (c1, c2).
Admitted.

Definition cont_of_Z := cont.

Definition Z_of_cont {l : Z} (c : container l) :=
  match c with cont _ v _ _ => v end.

Lemma blen_Z_of_cont {l : Z} (c : container l) :
  blen (Z_of_cont c) <= l.
Proof. destruct c; auto. Qed.

Lemma nonneg_Z_of_cont {l : Z} (c : container l) :
  0 <= Z_of_cont c.
Proof. destruct c; auto. Qed.

Definition cont_Z_roundtrip {l : Z} (c : container l) :=
  match c with
  | cont _ v N L => cont_of_Z l (Z_of_cont c) (nonneg_Z_of_cont c) (blen_Z_of_cont c)
  end.