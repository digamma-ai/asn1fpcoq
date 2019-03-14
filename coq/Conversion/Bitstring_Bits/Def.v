Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Bits ASN1FP.Aux.Option ASN1FP.Aux.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.
Require Import Lia.

Open Scope Z.

(** * common lengths *)

Definition cont1 := container 1.

Definition cont2 := container 2.
Definition cont8 := container 8.

Definition b1_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 1)%nat) : cont1
:= cont 1 v N L.
Definition b2_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 2)%nat) : cont2
:= cont 2 v N L.
Definition b8_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 8)%nat) : cont8
:= cont 8 v N L.

(* create and append containers of common lengths *)
Definition append_b1_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 1)%nat)
        {l : nat} (c : container l)
: container (1 + l) := join_cont (b1_cont v N L) c.

Definition append_b2_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 2)%nat)
        {l : nat} (c : container l)
: container (2 + l) := join_cont (b2_cont v N L) c.

Definition append_b8_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 8)%nat)
        {l : nat} (c : container l)
: container (8 + l) := join_cont (b8_cont v N L) c.

(* cut containers of common lengths (from left *)
Fact O_lt_1 : (0 < 1)%nat.
Proof. lia. Qed.

Definition cut_b1_cont {l : nat} (c : container (1 + l)) (L : (0 < l)%nat)
: cont1 * container l := split_cont c O_lt_1 L.

Fact O_lt_2 : (0 < 2)%nat.
Proof. lia. Qed.

Definition cut_b2_cont {l : nat} (c : container (2 + l)) (L : (0 < l)%nat)
: cont2 * container l := split_cont c O_lt_2 L.

Fact O_lt_8 : (0 < 8)%nat.
Proof. lia. Qed.

Definition cut_b8_cont {l : nat} (c : container (8 + l)) (L : (0 < l)%nat)
: cont8 * container l := split_cont c O_lt_8 L.

(*** these might or might not be useful *)
(*
Definition cut_append_b1 (v : Z) (N : 0 <= v) (L : (nblen v <= 1)%nat)
        {l : nat} (c : container l) :
cut_b1_cont (append_b1_cont v N L c) = (b1_cont v N L, c).
Proof. apply split_join_roundtrip. Qed.

Definition cut_append_b2 (v : Z) (N : 0 <= v) (L : (nblen v <= 2)%nat)
        {l : nat} (c : container l) :
cut_b2_cont (append_b2_cont v N L c) = (b2_cont v N L, c).
Proof. apply split_join_roundtrip. Qed.

Definition cut_append_b8 (v : Z) (N : 0 <= v) (L : (nblen v <= 8)%nat)
        {l : nat} (c : container l) :
cut_b8_cont (append_b8_cont v N L c) = (b8_cont v N L, c).
Proof. apply split_join_roundtrip. Qed.
*)

(* common operations *)
Definition z2n := Z.to_nat.
Definition c2z {l : nat} (c : container l) := Z_of_cont c.
Definition c2n {l : nat} (c : container l) := z2n (c2z c).


(** * container tuples *)

(* nbs - normal bitstring (i.e. not a special value) *)
Inductive BER_nbs :=
| short_nbs
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (e : container (8 * (c2n ee + 1))) (m : container (8*((c2n co) - (c2n ee) - 2)))
    (VS1 : c2z id = real_id_b) (VS2 : c2z t = 1) (VS3 : c2z ee <= 2) (VS4 : 1 <= c2z m)
    (VS5 : c2z co <= 127)
| long_nbs
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (eo : cont8)
    (e : container (8*(c2n eo))) (m : container (8 * ((c2n co) - (c2n eo) - 2)))
    (VL1 : c2z id = real_id_b) (VL2 : c2z t = 1) (VL3 : c2z ee = 3) (VL4 : 1 <= c2z m)
    (VL5 : c2z co <= 127).

Inductive BER_bs_aux :=
| special_aux (val : Z) : BER_bs_aux
| normal_aux (b : BER_nbs) : BER_bs_aux.



(** * bitstring -> nbs lemmas *)

Ltac split_valid :=
  unfold valid_short in *;
  unfold valid_long in *;
  unfold real_id_b in *; repeat split_andb; debool; subst.

(** * id *)
Lemma VS_id_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= id.
Proof. split_valid; lia. Qed.

Lemma VS_id_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen id <= 8)%nat.
Proof. split_valid; unfold nblen; simpl; lia. Qed.

Lemma VL_id_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= id.
Proof. split_valid; lia. Qed.

Lemma VL_id_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen id <= 8)%nat.
Proof. split_valid; unfold nblen; simpl; lia. Qed.

(** * co *)
Lemma VS_co_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= co.
Proof. split_valid; lia. Qed.

Lemma VS_co_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen co <= 8)%nat.
Proof.
  split_valid.
  replace 8%nat with (Z.to_nat (8%Z)) by trivial.
  assert (co < 128) by lia;
    replace 128 with (2^7) in H by trivial;
    apply Z.log2_lt_pow2 in H; [|lia].
  apply Z2Nat.inj_le; [ | try lia | try lia].
  assert (0 <= Z.log2 co) by apply Z.log2_nonneg.
  lia.
Qed.

Lemma VL_co_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= co.
Proof. split_valid; lia. Qed.

Lemma VL_co_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen co <= 8)%nat.
Proof.
  split_valid.
  replace 8%nat with (Z.to_nat (8%Z)) by trivial.
  assert (co < 128) by lia;
    replace 128 with (2^7) in H by trivial;
    apply Z.log2_lt_pow2 in H; [|lia].
  apply Z2Nat.inj_le; [ | try lia | try lia].
  assert (0 <= Z.log2 co) by apply Z.log2_nonneg.
  lia.
Qed.

(** * t *)
Lemma VS_t_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= t.
Proof. split_valid; lia. Qed.

Lemma VS_t_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen t <= 1)%nat.
Proof.
  split_valid.
  replace 1%nat with (Z.to_nat (1%Z)) by trivial.
  unfold nblen. simpl. reflexivity.
Qed.

Lemma VL_t_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= t.
Proof. split_valid; lia. Qed.

Lemma VL_t_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen t <= 1)%nat.
Proof.
  split_valid.
  replace 1%nat with (Z.to_nat (1%Z)) by trivial.
  unfold nblen. simpl. reflexivity.
Qed.


(** * s *)
Lemma VS_s_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= s.
Proof. split_valid; lia. Qed.

Lemma VS_s_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen s <= 1)%nat.
Proof.
  destruct (Z.eq_dec s 0).
  - subst; auto.
  - split_valid; assert (0 < s) by lia.
    replace 1%nat with (Z.to_nat (1%Z)) by trivial.
    assert (P : s < 2) by lia;
      replace 2 with (2^1) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 s) by apply Z.log2_nonneg.
    lia.
Qed.

Lemma VL_s_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= s.
Proof. split_valid; lia. Qed.

Lemma VL_s_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen s <= 1)%nat.
Proof.
  destruct (Z.eq_dec s 0).
  - subst; auto.
  - split_valid; assert (0 < s) by lia.
    replace 1%nat with (Z.to_nat (1%Z)) by trivial.
    assert (P : s < 2) by lia;
      replace 2 with (2^1) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 s) by apply Z.log2_nonneg.
    lia.
Qed.


(** * bb *)
Lemma VS_bb_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= bb.
Proof. split_valid; lia. Qed.

Lemma VS_bb_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen bb <= 2)%nat.
Proof.
  destruct (Z.eq_dec bb 0).
  - subst; auto.
  - split_valid; assert (0 < bb) by lia.
    replace 2%nat with (Z.to_nat (2%Z)) by trivial.
    assert (P : bb < 4) by lia;
      replace 4 with (2^2) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 bb) by apply Z.log2_nonneg.
    lia.
Qed.

Lemma VL_bb_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= bb.
Proof. split_valid; lia. Qed.

Lemma VL_bb_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen bb <= 2)%nat.
Proof.
  destruct (Z.eq_dec bb 0).
  - subst; auto.
  - split_valid; assert (0 < bb) by lia.
    replace 2%nat with (Z.to_nat (2%Z)) by trivial.
    assert (P : bb < 4) by lia;
      replace 4 with (2^2) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 bb) by apply Z.log2_nonneg.
    lia.
Qed.

(** * ff *)
Lemma VS_ff_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= ff.
Proof. split_valid; lia. Qed.

Lemma VS_ff_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen ff <= 2)%nat.
Proof.
  destruct (Z.eq_dec ff 0).
  - subst; auto.
  - split_valid; assert (0 < ff) by lia.
    replace 2%nat with (Z.to_nat (2%Z)) by trivial.
    assert (P : ff < 4) by lia;
      replace 4 with (2^2) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 ff) by apply Z.log2_nonneg.
    lia.
Qed.

Lemma VL_ff_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= ff.
Proof. split_valid; lia. Qed.

Lemma VL_ff_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen ff <= 2)%nat.
Proof.
  destruct (Z.eq_dec ff 0).
  - subst; auto.
  - split_valid; assert (0 < ff) by lia.
    replace 2%nat with (Z.to_nat (2%Z)) by trivial.
    assert (P : ff < 4) by lia;
      replace 4 with (2^2) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 ff) by apply Z.log2_nonneg.
    lia.
Qed.

(** * ee *)
Lemma VS_ee_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= ee.
Proof. split_valid; lia. Qed.

Lemma VS_ee_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen ee <= 2)%nat.
Proof.
  destruct (Z.eq_dec ee 0).
  - subst; auto.
  - split_valid; assert (0 < ee) by lia.
    replace 2%nat with (Z.to_nat (2%Z)) by trivial.
    assert (P : ee < 4) by lia;
      replace 4 with (2^2) in P by trivial;
      apply Z.log2_lt_pow2 in P; [|lia].
    apply Z2Nat.inj_le; [ | try lia | try lia].
    assert (0 <= Z.log2 ee) by apply Z.log2_nonneg.
    lia.
Qed.

Lemma VL_ee_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= ee.
Proof. split_valid; lia. Qed.

Lemma VL_ee_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen ee <= 2)%nat.
Proof. split_valid. trivial. Qed.

(** * eo *)
Lemma VL_eo_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= eo.
Proof. split_valid; lia. Qed.

Lemma VL_eo_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen eo <= 8)%nat.
Proof.
  split_valid.
  replace 8%nat with (Z.to_nat (8%Z)) by trivial.
  assert (0 <= olen m).
  { 
    unfold olen, olen_of_blen, blen.
    apply Z.div_pos; [| lia].
    generalize (Z.log2_nonneg m); lia.
  }
  assert (eo <= co) by lia.
  assert (co < 128) by lia.
  assert (P : eo < 128) by lia;
    replace 128 with (2^7) in P by trivial;
    apply Z.log2_lt_pow2 in P; [|lia].
  apply Z2Nat.inj_le; [ | try lia | try lia].
  assert (0 <= Z.log2 eo) by apply Z.log2_nonneg.
  lia.
Qed.

(** * e *)
Lemma VS_e_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= e.
Proof. split_valid; lia. Qed.

Lemma VS_e_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
  (nblen e <= 8* (c2n eec + 1))%nat.
Proof.
  assert (H := VS).
  intros eec.
  replace (c2n eec) with (Z.to_nat ee).
  split_valid.
  - unfold nblen.
    replace (8 * (Z.to_nat ee + 1))%nat with (Z.to_nat (8 * (ee + 1))).
    + apply Z2Nat.inj_le; [ | lia |].
      assert (0 <= Z.log2 e) by apply Z.log2_nonneg.
      lia.
      unfold olen, olen_of_blen, blen in H3.
      remember (Z.log2 e + 1) as el.
      apply (Zmult_le_compat_l _ _ 8) in H3; [| lia].
      assert (0 < 8) by lia.
      assert (T : 0 <= el). { subst el. generalize (Z.log2_nonneg e). lia. }
      generalize (Zdiv_pinf_ge el 8 T H); intros.
      replace (8 - 1) with 7 in H0 by trivial.
      lia.
    + replace 8%nat with (Z.to_nat 8%Z) by reflexivity;
        replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
      rewrite <- Z2Nat.inj_add, <- Z2Nat.inj_mul; lia.
  - subst eec.
    unfold c2n, c2z, z2n, Z_of_cont, b2_cont.
    reflexivity.
Qed.

Lemma VL_e_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= e.
Proof. split_valid; lia. Qed.

Lemma VL_e_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
  (nblen e <= 8 * c2n eoc)%nat.
Proof.
  assert (H := VL).
  intros eoc.
  replace (c2n eoc) with (Z.to_nat eo).
  split_valid.
  - unfold nblen.
    replace (8 * (Z.to_nat eo))%nat with (Z.to_nat (8 * eo)).
    + apply Z2Nat.inj_le; [ | lia |].
      assert (0 <= Z.log2 e) by apply Z.log2_nonneg.
      lia.
      unfold olen, olen_of_blen, blen in H3.
      remember (Z.log2 e + 1) as el.
      apply (Zmult_le_compat_l _ _ 8) in H3; [| lia].
      assert (0 < 8) by lia.
      assert (T : 0 <= el). { subst el. generalize (Z.log2_nonneg e). lia. }
      generalize (Zdiv_pinf_ge el 8 T H); intros.
      replace (8 - 1) with 7 in H0 by trivial.
      lia.
    + replace 8%nat with (Z.to_nat 8%Z) by reflexivity.
      rewrite <- Z2Nat.inj_mul; lia.
  - subst eoc.
    unfold c2n, c2z, z2n, Z_of_cont, b2_cont.
    reflexivity.
Qed.

(** * m *)
Lemma VS_m_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= m.
Proof. split_valid; lia. Qed.

Ltac uncont :=
  unfold c2n, c2z, z2n, Z_of_cont in *; try reflexivity.

Lemma VS_m_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  let coc := (b8_cont co (VS_co_N VS) (VS_co_L VS)) in
  let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
  (nblen m <= 8 * (c2n coc - c2n eec - 2))%nat.
Proof.
  intros coc eec.
  replace (c2n coc) with (Z.to_nat co) by uncont.
  replace (c2n eec) with (Z.to_nat ee) by uncont.
  clear coc eec.
  split_valid.
  unfold nblen.
  unfold olen, olen_of_blen, blen in H13.
  remember (Z.log2 m + 1) as lm.
  assert (P : 8 * ((lm + 7) / 8) <= 8 * (co - ee - 2)) by lia; clear H13.
  assert (T1 : 0 < 8) by lia.
  assert (T : 0 <= lm). { subst lm. generalize (Z.log2_nonneg m). lia. }
  generalize (Zdiv_pinf_ge lm 8 T T1); intros P1; replace (8 - 1) with 7 in P1 by trivial.
  assert (P2 : lm <= 8 * (co - ee - 2)) by lia.
  generalize (Z.log2_nonneg m); intros P3.
  replace (8 * (Z.to_nat co - Z.to_nat ee - 2))%nat with (Z.to_nat (8 * (co - ee - 2))).
  - apply Z2Nat.inj_le; lia.
  - replace 8%nat with (Z.to_nat 8) by trivial.
    replace 2%nat with (Z.to_nat 2) by trivial.
    rewrite <- Z2Nat.inj_sub by lia.
    rewrite <- Z2Nat.inj_sub by lia.
    rewrite <- Z2Nat.inj_mul; [ reflexivity | lia | ].
    lia.
Qed.

Lemma VL_m_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= m.
Proof. split_valid; lia. Qed.

Lemma VL_m_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  let coc := (b8_cont co (VL_co_N VL) (VL_co_L VL)) in
  let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
  (nblen m <= 8* (c2n coc - c2n eoc - 2))%nat.
Proof.
  intros coc eoc.
  replace (c2n coc) with (Z.to_nat co) by uncont.
  replace (c2n eoc) with (Z.to_nat eo) by uncont.
  clear coc eoc.
  split_valid.
  unfold nblen.
  unfold olen, olen_of_blen, blen in H14.
  generalize (Z.log2_nonneg m); intros P3.
  remember (Z.log2 m + 1) as lm.
  assert (P : 8 * ((lm + 7) / 8) <= 8 * (co - eo - 2)) by lia; clear H14.
  assert (T1 : 0 < 8) by lia.
  assert (T : 0 <= lm). { subst lm. generalize (Z.log2_nonneg m). lia. }
  generalize (Zdiv_pinf_ge lm 8 T T1); intros P1; replace (8 - 1) with 7 in P1 by trivial.
  assert (P2 : lm <= 8 * (co - eo - 2)) by lia.
  replace (8 * (Z.to_nat co - Z.to_nat eo - 2))%nat with (Z.to_nat (8 * (co - eo - 2))).
  - apply Z2Nat.inj_le; lia.
  - replace 8%nat with (Z.to_nat 8) by trivial.
    replace 2%nat with (Z.to_nat 2) by trivial.
    rewrite <- Z2Nat.inj_sub by lia.
    rewrite <- Z2Nat.inj_sub by lia.
    rewrite <- Z2Nat.inj_mul; [ reflexivity | lia | ].
    lia.
Qed.

Lemma valid_short_VS1 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b8_cont id (VS_id_N VS) (VS_id_L VS)) = real_id_b.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_short_VS2 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b1_cont t (VS_t_N VS) (VS_t_L VS)) = 1.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_short_VS3 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) <= 2.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_short_VS4 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  let coc := (b8_cont co (VS_co_N VS) (VS_co_L VS)) in
  let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
  1 <= c2z (cont (8 * (c2n coc - c2n eec - 2)) m (VS_m_N VS) (VS_m_L VS)).
Proof. simpl. split_valid. auto. Qed.

Lemma valid_short_VS5 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b8_cont co (VS_co_N VS) (VS_co_L VS)) <= 127.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_long_VL1 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b8_cont id (VL_id_N VL) (VL_id_L VL)) = real_id_b.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_long_VL2 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b1_cont t (VL_t_N VL) (VL_t_L VL)) = 1.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_long_VL3 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b2_cont ee (VL_ee_N VL) (VL_ee_L VL)) = 3.
Proof. simpl. split_valid. auto. Qed.

Lemma valid_long_VL4 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  let coc := (b8_cont co (VL_co_N VL) (VL_co_L VL)) in
  let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
  1 <= c2z (cont (8 * (c2n coc - c2n eoc - 2)) m (VL_m_N VL) (VL_m_L VL)).
Proof. simpl. split_valid. auto. Qed.

Lemma valid_long_VL5 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b8_cont co (VL_co_N VL) (VL_co_L VL)) <= 127.
Proof. simpl. split_valid. auto. Qed.


(** * nbs -> bitstring lemmas *)

Lemma c2z_nneg {l : nat} (c : container l) :
  0 <= c2z c.
Proof. destruct c. simpl. apply N. Qed.

Lemma c12z_le_1 (c : cont1) :
  c2z c <= 1.
Proof.
  destruct c; simpl.
  unfold nblen in L.
  replace 1%nat with (Z.to_nat 1) in L by trivial.
  generalize (Z.log2_nonneg v); intros.
  apply Z2Nat.inj_le in L; try lia.
  assert (L1 : Z.log2 v < 1) by lia; clear L.
  replace 1 with (Z.log2 2) in L1 by trivial.
  apply Z.log2_lt_cancel in L1.
  lia.
Qed.

Lemma c22z_le_3 (c : cont2) :
  c2z c <= 3.
Proof.
  destruct c; simpl.
  unfold nblen in L.
  replace 2%nat with (Z.to_nat 2) in L by trivial.
  generalize (Z.log2_nonneg v); intros.
  apply Z2Nat.inj_le in L; try lia.
  assert (L1 : Z.log2 v < 2) by lia; clear L.
  replace  2 with (Z.log2 4) in L1 by trivial.
  apply Z.log2_lt_cancel in L1.
  lia.
Qed.
  
Lemma Z2Nat_pos_inj_le (a b : Z) :
  0 < a ->
  (Z.to_nat a <= Z.to_nat b)%nat ->
  a <= b.
Proof.
  intros.
  destruct a; try inversion H.
  destruct b; simpl in H0; lia.
Qed.

Lemma Z2Nat_pos_iff (x : Z) :
  (0 < Z.to_nat x)%nat <->
  0 < x.
Proof. destruct x; simpl; lia. Qed.

Lemma Z2Nat_mul_pos (x y : Z) :
  (0 < Z.to_nat x * Z.to_nat y)%nat ->
  0 < x /\ 0 < y.
Proof.
  intros.
  apply Nat.lt_0_mul in H.
  destruct H.
  - destruct H as [H1 H2];
      apply Z2Nat_pos_iff in H1;
        apply Z2Nat_pos_iff in H2.
    auto.
  - unfold Z.to_nat in H; destruct H; inversion H.
Qed.

Definition nbs_co (b : BER_nbs) : nat :=
  match b with
  | short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5 =>
    c2n co
  | long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 VL5 =>
    c2n co
  end.

Lemma nbs_co_positive (b : BER_nbs) :
  (1 <= nbs_co b)%nat.
Proof.
  destruct b; simpl.
  all: destruct m, ee, co; rename v into m, v0 into ee, v1 into co; uncont.
  all: generalize (nblen_positive m); intros NBL.
  all: assert (COP : (0 < Z.to_nat co)%nat) by lia; lia.
Qed.

Lemma Z_div_pinf_le_upper_bound (x y : Z) :
  x <= 8 * y ->
  (x + 7) / 8 <= y.
Proof.
  intros.
  assert (x - 1 < 8 * y) by lia; clear H.
  replace x with ((x - 1) + 1) by lia.
  remember (x - 1) as x'; clear Heqx'.
  replace (x' + 1 + 7) with (x' + 1 * 8) by lia.
  rewrite Z.div_add by lia.
  apply Z.div_lt_upper_bound in H0; lia.
Qed.
  
Lemma short_nbs_valid
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (e : container (8 * (c2n ee + 1))) (m : container (8*((c2n co) - (c2n ee) - 2)))
    (VS1 : c2z id = real_id_b) (VS2 : c2z t = 1) (VS3 : c2z ee <= 2) (VS4 : 1 <= c2z m)
    (VS5 : c2z co <= 127) :
    valid_short (c2z id) (c2z co)
                (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee)
                (c2z e) (c2z m) = true.
Proof.
  generalize (nbs_co_positive
                (short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5)).
  intros COP; simpl in COP.
  unfold valid_short.
  destruct co, ee, e, m; rename v into co, v0 into ee, v1 into e, v2 into m.
  uncont.
  assert (C: 0 < co) by (apply Z2Nat_pos_iff; lia); clear COP.
  split_andb_goal; debool.
  all: try auto; try apply c2z_nneg; try apply c12z_le_1; try apply c22z_le_3.
  all: clear id N1 N2 VS1 VS2 t s bb ff N L0 L.
  all: unfold nblen, olen, olen_of_blen, blen in *.
  - clear L1 e. lia.
  - clear L1 e VS3 VS4 VS5.
    generalize (Z.log2_nonneg m); intros;
      remember (Z.log2 m + 1) as mb; assert (M : 0 < mb) by lia;
        clear H Heqmb m.
    replace 8%nat with (Z.to_nat 8) in L2 by trivial.
    replace 2%nat with (Z.to_nat 2) in L2 by trivial.
    repeat rewrite <- Z2Nat.inj_sub in L2 by lia.
    copy_apply Z2Nat_pos_iff M.
    assert (P : (0 < Z.to_nat 8 * Z.to_nat (co - ee - 2))%nat) by lia.
    apply Z2Nat_mul_pos in P; destruct P as [P1 P2].
    rewrite <- Z2Nat.inj_mul in L2 by lia.
    apply Z2Nat.inj_le in L2; try lia.
    clear P1 P2 C H.
    apply Z.le_add_le_sub_r, Z.le_add_le_sub_r.
    replace (co - 2 - ee) with (co - ee - 2) by lia.
    remember (co - ee - 2) as mo; clear Heqmo N0 co ee M.
    apply Z_div_pinf_le_upper_bound; auto.
  - clear L2 VS3 VS4 m VS5 C co.
    generalize (Z.log2_nonneg e); intros;
      remember (Z.log2 e + 1) as eb; assert (M : 0 < eb) by lia;
        clear H Heqeb e.
    replace 8%nat with (Z.to_nat 8) in L1 by trivial.
    replace 1%nat with (Z.to_nat 1) in L1 by trivial.
    rewrite <- Z2Nat.inj_add in L1 by lia.
    copy_apply Z2Nat_pos_iff M.
    assert (P : (0 < Z.to_nat 8 * Z.to_nat (ee + 1))%nat) by lia.
    apply Z2Nat_mul_pos in P; destruct P as [P1 P2].
    rewrite <- Z2Nat.inj_mul in L1 by lia.
    apply Z2Nat.inj_le in L1; try lia.
    clear P1 P2 H.
    apply Z_div_pinf_le_upper_bound; auto.
Qed.


Lemma long_nbs_valid
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (eo : cont8)
    (e : container (8*(c2n eo))) (m : container (8 * ((c2n co) - (c2n eo) - 2)))
    (VL1 : c2z id = real_id_b) (VL2 : c2z t = 1) (VL3 : c2z ee = 3) (VL4 : 1 <= c2z m)
    (VL5 : c2z co <= 127) :
    valid_long  (c2z id) (c2z co)
                (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee) (c2z eo)
                (c2z e) (c2z m) = true.
Proof.
  generalize (nbs_co_positive
                (long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 VL5)).
  intros COP; simpl in COP.
  unfold valid_long.
  destruct co, ee, eo, e, m; rename v into co, v0 into ee, v1 into eo, v2 into e, v3 into m.
  uncont.
  assert (C: 0 < co) by (apply Z2Nat_pos_iff; lia); clear COP.
  split_andb_goal; debool.
  all: try auto; try apply c2z_nneg; try apply c12z_le_1; try apply c22z_le_3.
  all: clear id N2 VL1 VL2 t s bb ff N L0 L.
  all: unfold nblen, olen, olen_of_blen, blen in *.
  - clear L1 L2 e. lia.
  - clear L1 L2 e VL3 VL4 VL5.
    generalize (Z.log2_nonneg m); intros;
      remember (Z.log2 m + 1) as mb; assert (M : 0 < mb) by lia;
        clear H Heqmb m N3.
    replace 8%nat with (Z.to_nat 8) in L3 by trivial.
    replace 2%nat with (Z.to_nat 2) in L3 by trivial.
    repeat rewrite <- Z2Nat.inj_sub in L3 by lia.
    copy_apply Z2Nat_pos_iff M.
    assert (P : (0 < Z.to_nat 8 * Z.to_nat (co - eo - 2))%nat) by lia.
    apply Z2Nat_mul_pos in P; destruct P as [P1 P2].
    rewrite <- Z2Nat.inj_mul in L3 by lia.
    apply Z2Nat.inj_le in L3; try lia.
    clear P1 P2 C H.
    apply Z.le_add_le_sub_r, Z.le_add_le_sub_r.
    replace (co - 2 - eo) with (co - eo - 2) by lia.
    remember (co - ee - 2) as mo.
    apply Z_div_pinf_le_upper_bound; auto.
    - clear L1 VL3 VL4 N3 L3 m VL5 C co N0 ee.
      generalize (Z.log2_nonneg e); intros;
        remember (Z.log2 e + 1) as eb; assert (M : 0 < eb) by lia;
          clear H Heqeb e.
      replace 8%nat with (Z.to_nat 8) in L2 by trivial.
      copy_apply Z2Nat_pos_iff M.
      assert (P : (0 < Z.to_nat 8 * Z.to_nat eo)%nat) by lia.
      apply Z2Nat_mul_pos in P; destruct P as [P1 P2].
      rewrite <- Z2Nat.inj_mul in L2 by lia.
      apply Z2Nat.inj_le in L2; lia.
    - clear L2 VL3 VL4 N3 L3 m VL5 C co N0 ee e.
      replace 8%nat with (Z.to_nat 8) in L1 by trivial.
      generalize (Z.log2_nonneg eo); intros;
        apply Z2Nat.inj_le in L1; try lia; clear H.
      assert (Z.log2 eo < 8) by lia; clear L1.
      replace 8 with (Z.log2 256) in H by trivial.
      apply Z.log2_lt_cancel in H.
      lia.
    - clear L1 VL3 VL4 N3 L3 m VL5 C co N0 ee.
      generalize (Z.log2_nonneg e); intros;
        remember (Z.log2 e + 1) as eb; assert (M : 0 < eb) by lia;
          clear H Heqeb e.
      replace 8%nat with (Z.to_nat 8) in L2 by trivial.
      copy_apply Z2Nat_pos_iff M.
      assert (P : (0 < Z.to_nat 8 * Z.to_nat eo)%nat) by lia.
      apply Z2Nat_mul_pos in P; destruct P as [P1 P2].
      rewrite <- Z2Nat.inj_mul in L2 by lia.
      apply Z2Nat.inj_le in L2; try lia.
      apply Z_div_pinf_le_upper_bound; auto.
Qed.


(** * BER_bitstring <-> BER_bs_aux *)

Definition bsaux_of_bitstring (b : BER_bitstring) : BER_bs_aux :=
  match b with
  | special val => special_aux val
  | short id co t s bb ff ee e m VS =>
    let coc := (b8_cont co (VS_co_N VS) (VS_co_L VS)) in
    let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
    normal_aux (short_nbs
      (b8_cont id (VS_id_N VS) (VS_id_L VS))
      coc
      (b1_cont t  (VS_t_N  VS) (VS_t_L  VS))
      (b1_cont s  (VS_s_N  VS) (VS_s_L  VS))
      (b2_cont bb (VS_bb_N VS) (VS_bb_L VS))
      (b2_cont ff (VS_ff_N VS) (VS_ff_L VS))
      eec
      (cont (8 * (c2n eec + 1)) e (VS_e_N VS) (VS_e_L VS))
      (cont (8 * ((c2n coc) - (c2n eec) - 2)) m (VS_m_N VS) (VS_m_L VS))
      (valid_short_VS1 VS)
      (valid_short_VS2 VS)
      (valid_short_VS3 VS)
      (valid_short_VS4 VS)
      (valid_short_VS5 VS))
  | long id co t s bb ff ee eo e m VL =>
    let coc := (b8_cont co (VL_co_N VL) (VL_co_L VL)) in
    let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
    normal_aux (long_nbs
      (b8_cont id (VL_id_N VL) (VL_id_L VL))
      coc
      (b1_cont t  (VL_t_N  VL) (VL_t_L  VL))
      (b1_cont s  (VL_s_N  VL) (VL_s_L  VL))
      (b2_cont bb (VL_bb_N VL) (VL_bb_L VL))
      (b2_cont ff (VL_ff_N VL) (VL_ff_L VL))
      (b2_cont ee (VL_ee_N VL) (VL_ee_L VL))
      eoc
      (cont (8 * (c2n eoc)) e (VL_e_N VL) (VL_e_L VL))
      (cont (8 * ((c2n coc) - (c2n eoc) - 2)) m (VL_m_N VL) (VL_m_L VL))
      (valid_long_VL1 VL)
      (valid_long_VL2 VL)
      (valid_long_VL3 VL)
      (valid_long_VL4 VL)
      (valid_long_VL5 VL))
  end.

Definition bitstring_of_bsaux (b : BER_bs_aux) : BER_bitstring :=
  match b with
  | special_aux val => special val
  | normal_aux b =>
    match b with
    | short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5 =>
      short (c2z id) (c2z co)
            (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee)
            (c2z e) (c2z m)
            (short_nbs_valid id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5)
    | long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 VL5 =>
      long  (c2z id) (c2z co)
            (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee) (c2z eo)
            (c2z e) (c2z m)
            (long_nbs_valid id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 VL5)
    end
  end.


(** * lengths *)

Definition info_nblen := 24%nat.

Definition nbs_nblen (b : BER_nbs) : nat :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ => 8 * (c2n co + 2)
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ => 8 * (c2n co + 2)
  end.

Definition content_nblen (b : BER_nbs) : nat :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ => 8 * (c2n co - 1)
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ => 8 * (c2n co - 1)
  end.

Lemma short_nblen_correct {l1 l2 : nat} (co : container l1) (ee : container l2)
  (m : container (8 * (c2n co - c2n ee - 2))) :
    (8 * (c2n ee + 1) + 8 * (c2n co - c2n ee - 2))%nat = (8 * (c2n co - 1))%nat.
Proof.
  destruct co, ee, m; rename v into co, v0 into ee, v1 into m.
  uncont; clear L L0 N N0 l1 l2.
  generalize (nblen_positive m); intros.
  lia.
Qed.

Lemma long_nblen_correct {l1 l2 : nat} (co : container l1) (eo : container l2)
  (m : container (8 * (c2n co - c2n eo - 2))) :
    (8 + (8 * c2n eo + 8 * (c2n co - c2n eo - 2)))%nat = (8 * (c2n co - 1))%nat.
Proof.
  destruct co, eo, m; rename v into co, v0 into eo, v1 into m.
  uncont; clear L L0 N N0 l1 l2.
  generalize (nblen_positive m); intros.
  lia.
Qed.

Lemma nbs_nblen_correct (b : BER_nbs) :
  (info_nblen + content_nblen b)%nat = nbs_nblen b.
Proof.
  generalize (nbs_co_positive b).
  destruct b;
    unfold nbs_co, content_nblen, nbs_nblen, info_nblen;
    lia.
Qed.

Definition BER_nblen (b : Z) : nat :=
  let l := nblen b in
  l + (l mod 8)%nat.

Lemma BER_nblen_correct (b : Z) :
  (nblen b <= BER_nblen b)%nat.
Proof. unfold BER_nblen; lia. Qed.

Definition bsaux_nblen (b : BER_bs_aux) :=
  match b with
  | special_aux val => nblen (Z.abs val)
  | normal_aux b => nbs_nblen b
  end.
 


(** * joining nbs *)

Definition mk_info (b : BER_nbs) : container info_nblen :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ =>
       join_cont id
      (join_cont co
      (join_cont t
      (join_cont s
      (join_cont bb
      (join_cont ff ee
       )))))
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ =>
       join_cont id
      (join_cont co
      (join_cont t
      (join_cont s
      (join_cont bb
      (join_cont ff ee
       )))))
  end.

Definition append_info {l : nat} (b : BER_nbs) (c : container l) :=
  join_cont (mk_info b) c.

Definition mk_content (b : BER_nbs) : container (content_nblen b) :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ =>
    cast_cont (join_cont e m) (short_nblen_correct co ee m)
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ =>
    cast_cont (join_cont eo (join_cont e m)) (long_nblen_correct co eo m)
  end.

Definition cont_of_nbs (b : BER_nbs) : container (nbs_nblen b) :=
  cast_cont (append_info b (mk_content b)) (nbs_nblen_correct b).



(** * splitting (into) nbs *)

Fact info_nblen_positive : (0 < info_nblen)%nat.
Proof. unfold info_nblen. lia. Qed.

Definition cut_info {l : nat} (c : container (info_nblen + l)) (L : (0 < l)%nat) :
  (container info_nblen * container l) :=
  split_cont c info_nblen_positive L.

Fact ilc1 : (0 < info_nblen - 8)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc2 : (0 < info_nblen - 8 - 8)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc3 : (0 < info_nblen - 8 - 8 - 1)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc4 : (0 < info_nblen - 8 - 8 - 1 - 1)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc5 : (0 < info_nblen - 8 - 8 - 1 - 1 - 2)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc6 : (0 < info_nblen - 8 - 8 - 1 - 1 - 2 - 2)%nat.
Proof. unfold info_nblen. lia. Qed.

Definition split_info (c : container info_nblen) :
  (cont8 * cont8 * cont1 * cont1 * cont2 * cont2 * cont2) :=
  let '(id, c)  := cut_b8_cont c ilc1 in
  let '(co, c)  := cut_b8_cont c ilc2 in
  let '(t,  c)  := cut_b1_cont c ilc3 in
  let '(s,  c)  := cut_b1_cont c ilc4 in
  let '(bb, c)  := cut_b2_cont c ilc5 in
  let '(ff, ee) := cut_b2_cont c ilc6 in
  (id, co, t, s, bb, ff, ee).

Definition split_cut_info {l : nat} (c : container (info_nblen + l)) (L : (0 < l)%nat) :=
  let '(info, content) := cut_info c L in
  let '(id, co, t, s, bb, ff, ee) := split_info info in
  (id, co, t, s, bb, ff, ee, content).

Definition e_nblen_of_long_cont {l : nat} (c : container (8 + l)) (L : (0 < l)%nat) : nat :=
  c2n (fst (cut_b8_cont c L)).

Definition try_cut_num (a b : nat) : option (a = b + (a - b))%nat :=
  match (Nat.eq_dec a (b + (a - b))) with
  | right _ => None
  | left H => Some H
  end.

Lemma try_cut_num_works (a b : nat) (L : (0 < a - b)%nat) :
  is_Some_b (try_cut_num a b) = true.
Proof.
  unfold try_cut_num.
  destruct (Nat.eq_dec a (b + (a - b))); simpl.
  reflexivity.
  lia.
Qed.

Definition cut_num (a b : nat) (L : (0 < a - b)%nat) :
  (a = b + (a - b))%nat.
{
  generalize (try_cut_num_works a b L); intros.
  destruct (try_cut_num a b).
  exact e.
  inversion H.
} Defined.

Definition cut_cont {l : nat} (c : container l) (l1 : nat) (L : (0 < l - l1)%nat)
  : container (l1 + (l - l1)) :=
  cast_cont c (cut_num l l1 L).
  
Definition try_cut_cont {l : nat} (c : container l) (l1 : nat)
  : option (container (l1 + (l - l1))) :=
    match le_lt_dec l1 0 with
    | left _ => None
    | right L1 =>
      match le_lt_dec (l - l1) 0 with
      | left _ => None
      | right L2 =>
      Some ((cut_cont c l1 L2))
      end
    end.

Definition try_split_cont {l : nat} (c : container l) (l1 : nat) :=
    match le_lt_dec l1 0 with
    | left _ => None
    | right L1 =>
      match le_lt_dec (l - l1) 0 with
      | left _ => None
      | right L2 =>
      Some (split_cont (cut_cont c l1 L2) L1 L2)
      end
    end.

Definition try_split_long_cont  {l : nat} (c : container (8 + l)) (L : (0 < l)%nat)
  : option (container 8 *
            container (e_nblen_of_long_cont c L) *
            container (l - e_nblen_of_long_cont c L)) :=
    let eo := fst (cut_b8_cont c L) in
    let em := snd (cut_b8_cont c L) in
    let eon := c2n eo in
    match try_split_cont em eon with
    | None => None
    | Some (e,m) =>
      Some (eo, e, m)
    end.

Definition check_short_elen {l : nat} (ee : cont2) (e : container l) :=
  match Nat.eq_dec l (8 * (c2n ee + 1)) with
  | right _ => None
  | left E => Some (cast_cont e E)
  end.

Definition check_long_elen {l : nat} (eo : cont8) (e : container l) :=
  match Nat.eq_dec l (8 * (c2n eo)) with
  | right _ => None
  | left E => Some (cast_cont e E)
  end.

Definition check_short_mlen {l : nat} (co : cont8) (ee : cont2) (m : container l) :=
  match Nat.eq_dec l (8 * (c2n co - c2n ee - 2)) with
  | right _ => None
  | left M => Some (cast_cont m M)
  end.

Definition check_long_mlen {l : nat} (co : cont8) (eo : cont8) (m : container l) :=
  match Nat.eq_dec l (8 * (c2n co - c2n eo - 2)) with
  | right _ => None
  | left M => Some (cast_cont m M)
  end.

Definition construct_short_nbs
           {l1 l2 : nat}
           (id co : cont8)
           (t s : cont1) (bb ff ee : cont2)
           (e : container l1) (m : container l2)
  : option BER_nbs :=
  match (check_short_elen ee e) with
  | None => None
  | Some e =>
    match (check_short_mlen co ee m) with
    | None => None
    | Some m =>
      match Z.eq_dec (c2z id) real_id_b with
      | right _ => None
      | left VS1 =>
        match Z.eq_dec (c2z t) 1 with
        | right _ => None
        | left VS2 =>
          match Z_le_dec (c2z ee) 2 with
          | right _ => None
          | left VS3 =>
            match Z_le_dec 1 (c2z m) with
            | right _ => None
            | left VS4 =>
              match Z_le_dec (c2z co) 127 with
              | right _ => None
              | left VS5 =>
              Some (short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5)
              end
            end
          end
        end
      end
    end
  end.

Definition construct_long_nbs
           { l1 l2 : nat }
           (id co : cont8)
           (t s : cont1) (bb ff ee : cont2)
           (eo : cont8)
           (e : container l1) (m : container l2)
  : option BER_nbs :=
  match (check_long_elen eo e) with
  | None => None
  | Some e =>
    match (check_long_mlen co eo m) with
    | None => None
    | Some m =>
      match Z.eq_dec (c2z id) real_id_b with
      | right _ => None
      | left VL1 =>
        match Z.eq_dec (c2z t) 1 with
        | right _ => None
        | left VL2 =>
          match Z.eq_dec (c2z ee) 3 with
          | right _ => None
          | left VL3 =>
            match Z_le_dec 1 (c2z m) with
            | right _ => None
            | left VL4 =>
              match Z_le_dec (c2z co) 127 with
              | right _ => None
              | left VL5 =>
               Some (long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 VL5)
              end
            end
          end
        end
      end
    end
  end.

Definition nbs_of_cont {l : nat} (c : container l) :=
  match (try_cut_cont c info_nblen) with
  | None => None
  | Some c =>
    match le_lt_dec (l - info_nblen) 0 with
    | left _ => None
    | right L =>
      let '(id, co, t, s, bb, ff, ee, content) := split_cut_info c L in
      if (c2n ee =? 3)%nat
      then match (try_cut_cont content 8) with
           | None => None
           | Some content =>
             match le_lt_dec (l - info_nblen - 8) 0 with
             | left _ => None
             | right L =>
               match (try_split_long_cont content L) with
               | None => None
               | Some (eo, e, m) =>
                   construct_long_nbs id co t s bb ff ee eo e m
               end
             end
           end
      else match (try_split_cont content (8 * (c2n ee + 1))) with
           | None => None
           | Some (e, m) =>
               construct_short_nbs id co t s bb ff ee e m
           end
    end
  end.


(** * cont <-> Z *)

Definition cont_of_BER_bits (b : Z) : option (container (BER_nblen b)) :=
  match (Z_gt_le_dec 0 b) with
  | left _ => None
  | right N => Some (cont (BER_nblen b) b N (BER_nblen_correct b))
  end.

Definition cont_of_Z_abs (n : Z) : container (nblen (Z.abs n)) :=
  let na := Z.abs n in
  cont (nblen na) na (Z.abs_nonneg n) (Nat.le_refl (nblen na)).
  
Definition cont_of_bsaux (b : BER_bs_aux) : container (bsaux_nblen b) :=
  match b with
  | special_aux val => cont_of_Z_abs val
  | normal_aux b => cont_of_nbs b
  end.

Definition Z_of_bsaux (b : BER_bs_aux) :=
  c2z (cont_of_bsaux b).

Definition bits_of_bitstring (b : BER_bitstring) : Z :=
  Z_of_bsaux (bsaux_of_bitstring b).

Definition mk_special_bsaux (b : Z) :=
  if b =? pzero_b
  then Some (special_aux b)
  else if b =? nzero_b
       then Some (special_aux b)
       else if b =? pinf_b
            then Some (special_aux b)
            else if b =? ninf_b
                 then Some (special_aux b)
                 else if b =? nan_b
                      then Some (special_aux b)
                           else None.

Definition bsaux_of_bits (b : Z) : option BER_bs_aux :=
  if b <? 0
  then None
  else match (mk_special_bsaux b) with
       | Some b => Some b
       | None =>
         match cont_of_BER_bits b with
         | None => None
         | Some c =>
           match (nbs_of_cont c) with
           | None => None
           | Some b => Some (normal_aux b)
           end
         end
       end.

Definition bitstring_of_bits (b : Z) : option BER_bitstring :=
  match bsaux_of_bits b with
  | None => None
  | Some b => Some (bitstring_of_bsaux b)
  end.