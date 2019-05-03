Require Import ZArith Lia.
Require Import ProofIrrelevance.
Require Import ASN1FP.Types.Bitstring ASN1FP.Types.BSaux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Aux.StructTactics ASN1FP.Types.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option.

(** * bitstring -> nbs lemmas *)

Ltac split_valid :=
  unfold valid_short in *;
  unfold valid_long in *;
  unfold real_id_b in *; repeat split_andb; debool; subst.

Ltac uncont :=
  unfold c2n, c2z, Z_of_cont in *; try reflexivity.


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
    unfold c2n, c2z, Z_of_cont, b2_cont.
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
    unfold c2n, c2z, Z_of_cont, b2_cont.
    reflexivity.
Qed.


(** * m *)
Lemma VS_m_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= m.
Proof. split_valid; lia. Qed.

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


(** * short correctness guarantees *)
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


(** * long correctness guarantees *)
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

Lemma long_nbs_valid (id co : cont8)
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

