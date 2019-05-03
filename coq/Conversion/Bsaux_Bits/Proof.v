Require Import ZArith Lia.
Require Import ProofIrrelevance.
Require Import ASN1FP.Types.Bitstring ASN1FP.Types.BSaux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Aux.StructTactics ASN1FP.Types.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option ASN1FP.Conversion.Bsaux_Bits.Def.
Require Import ASN1FP.Conversion.Bitstring_Bsaux.Def ASN1FP.Conversion.Bitstring_Bsaux.Proof.

Open Scope bool_scope.

Definition cont_eqb {l1 l2 : nat} (c1 : container l1) (c2 : container l2) :=
  match c1, c2 with
  | cont _ v1 _ _, cont _ v2 _ _ => andb (Nat.eqb l1 l2) (Z.eqb v1 v2)
  end.

Infix "=c=" := cont_eqb (at level 50).

Definition BER_nbs_eqb (b1 b2 : BER_nbs) :=
  match b1, b2 with
  | short_nbs id1 co1 t1 s1 bb1 ff1 ee1 e1 m1 _ _ _ _ _,
    short_nbs id2 co2 t2 s2 bb2 ff2 ee2 e2 m2 _ _ _ _ _ =>
    (id1 =c= id2) && (co1 =c= co2) && (t1 =c= t2)   &&
    (s1 =c= s2)   && (bb1 =c= bb2) && (ff1 =c= ff2) &&
    (ee1 =c= ee2) && (e1 =c= e2)   && (m1 =c= m2)
  | long_nbs id1 co1 t1 s1 bb1 ff1 ee1 eo1 e1 m1 _ _ _ _ _,
    long_nbs id2 co2 t2 s2 bb2 ff2 ee2 eo2 e2 m2 _ _ _ _ _ =>
    (id1 =c= id2) && (co1 =c= co2) && (t1 =c= t2)   &&
    (s1 =c= s2)   && (bb1 =c= bb2) && (ff1 =c= ff2) &&
    (ee1 =c= ee2) && (eo1 =c= eo2) && (e1 =c= e2)   &&
    (m1 =c= m2)
  | _, _ => false
  end.

Definition BER_bsaux_eqb (b1 b2 : BER_bs_aux) :=
  match b1, b2 with
  | special_aux z1, special_aux z2 => special_eqb z1 z2
  | normal_aux nbs1, normal_aux nbs2 =>
    BER_nbs_eqb nbs1 nbs2
  | _, _ => false
  end.

Definition cont_eqb_pair {l11 l12 l21 l22 : nat}
           (p1 : container l11 * container l12)
           (p2 : container l21 * container l22) :=
  match p1 with
  | (c11, c12) =>
    match p2 with
    | (c21, c22) =>
      andb (c11 =c= c21) (c12 =c= c22)
    end
  end.

Lemma add_small_div (a b x : Z) :
  0 < x ->
  0 <= b ->
  b < x ->
  (a * x + b) / x = a.
Proof.
  intros OX OB BX.
  rewrite Z.div_add_l; try lia.
  rewrite Z.div_small; lia.
Qed.

Lemma split_join_cont_eqb {l1 l2 : nat} (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (c1 : container l1) (c2 : container l2) :
  cont_eqb_pair
    (split_cont (join_cont c1 c2) L1 L2)
    (c1, c2)
  = true.
Proof.
  unfold split_cont, join_cont, cont_eqb_pair.
  destruct c1 as (v1, N1, L1').
  destruct c2 as (v2, N2, L2').
  simpl.
  repeat rewrite Nat.eqb_refl, Bool.andb_true_l.
  clear L1 L1' l1 L2.
  unfold nblen in L2'.
  rewrite two_power_nat_equiv.
  replace l2 with (Z.to_nat (Z.of_nat l2)) in L2' by apply Nat2Z.id.
  remember (Z.of_nat l2) as l; clear Heql l2.
  apply Z2Nat_pos_inj_le in L2'; try (generalize (Z.log2_nonneg v2); lia).
  assert (0 < l) by (generalize (Z.log2_nonneg v2); lia).
  destruct (Z.eq_dec v2 0); subst.
  - repeat rewrite Z.add_0_r.
    rewrite Z.div_mul, Z.mod_mul.
    repeat rewrite Z.eqb_refl; trivial.
    all: generalize (Z.pow_pos_nonneg 2 l); lia.
  - assert (L : Z.log2 v2 < l) by lia; clear L2'; apply Z.log2_lt_pow2 in L; try lia.
    assert (0 < 2^l) by (apply Z.pow_pos_nonneg; lia).
    remember (2^l) as x; clear Heqx n H l.
    split_andb_goal; debool.
    + apply add_small_div; assumption.
    + rewrite Z.add_comm.
      rewrite Z.mod_add; [|lia].
      apply Z.mod_small; lia.
Qed.

Lemma split_join_cont_eq {l1 l2 : nat} (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (c1 : container l1) (c2 : container l2) :
    (split_cont (join_cont c1 c2) L1 L2) = (c1, c2).
Proof.
  generalize (split_join_cont_eqb L1 L2 c1 c2); intros H.
  unfold cont_eqb_pair in H.
  unfold cont_eqb in *.
  repeat break_match.
  repeat split_andb; debool; subst.
  rewrite proof_irrelevance with (p1 := N0) (p2 := N).
  rewrite proof_irrelevance with (p1 := L0) (p2 := L).
  rewrite proof_irrelevance with (p1 := N2) (p2 := N1).
  rewrite proof_irrelevance with (p1 := L4) (p2 := L3).
  reflexivity.
Qed.

Lemma split_join_cont_fst {l1 l2 : nat} (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (c1 : container l1) (c2 : container l2) :
  fst (split_cont (join_cont c1 c2) L1 L2) =c= c1 = true.
Proof.
  generalize (split_join_cont_eqb L1 L2 c1 c2); intros.
  unfold cont_eqb_pair in H.
  break_match.
  split_andb.
  simpl.
  assumption.
Qed.

Lemma split_join_cont_snd {l1 l2 : nat} (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (c1 : container l1) (c2 : container l2) :
  snd (split_cont (join_cont c1 c2) L1 L2) =c= c2 = true.
Proof.
  generalize (split_join_cont_eqb L1 L2 c1 c2); intros.
  unfold cont_eqb_pair in H.
  break_match.
  split_andb.
  simpl.
  assumption.
Qed.

Lemma cut_append_info {l : nat} (b : BER_nbs) (c : container l) (L : (0 < l)%nat)  :
  (fst (cut_info (append_info b c) L) =c= mk_info b) = true.
Proof.
  unfold cut_info, append_info.
  apply split_join_cont_fst.
Qed.

Definition option_het_eq {A B : Type} (f : A -> B -> bool) : (option A -> option B -> bool) :=
  fun (a : option A) (b : option B) =>
    match a, b with
    | Some a, Some b => f a b
    | Some a, None   => false
    | None,   Some b => false
    | None,   None   => true
    end.
  

Lemma nbs_is_not_special (b : BER_nbs) :
  classify_BER (c2z (cont_of_nbs b)) = None.
Proof.
Admitted.

Lemma cont_eqb_refl {l : nat}
      (c : container l) :
  c =c= c = true.
Proof.
  unfold cont_eqb.
  break_match.
  rewrite Nat.eqb_refl.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma cont_eqb_sym {l1 l2 : nat}
      (c1 : container l1)
      (c2 : container l2) :
  c1 =c= c2 = c2 =c= c1.
Proof.
  unfold cont_eqb.
  repeat break_match.
  rewrite Nat.eqb_sym.
  rewrite Z.eqb_sym.
  reflexivity.
Qed.

Lemma cont_eqb_trans {l1 l2 l3 : nat}
      (c1 : container l1)
      (c2 : container l2)
      (c3 : container l3) :
  c1 =c= c2 = true ->
  c2 =c= c3 = true ->
  c1 =c= c3 = true.
Proof.
  intros H1 H2.
  unfold cont_eqb in *.
  repeat break_match.
  repeat split_andb; debool.
  subst. rewrite Nat.eqb_refl, Z.eqb_refl.
  reflexivity.
Qed.

Lemma BER_nbs_eqb_refl (b : BER_nbs) :
  BER_nbs_eqb b b = true.
Proof.
  unfold BER_nbs_eqb.
  break_match.
  all: repeat rewrite cont_eqb_refl; reflexivity.
Qed.

Lemma BER_nbs_eqb_sym (b1 b2 : BER_nbs) :
  BER_nbs_eqb b1 b2 = BER_nbs_eqb b2 b1.
Proof.
  unfold BER_nbs_eqb.
  repeat break_match; try reflexivity.
  all: rewrite cont_eqb_sym with (c1 := id).
  all: rewrite cont_eqb_sym with (c1 := co).
  all: rewrite cont_eqb_sym with (c1 :=  t).
  all: rewrite cont_eqb_sym with (c1 :=  s).
  all: rewrite cont_eqb_sym with (c1 := bb).
  all: rewrite cont_eqb_sym with (c1 := ff).
  all: rewrite cont_eqb_sym with (c1 := ee).
  all: try (rewrite cont_eqb_sym with (c1 := eo)).
  all: rewrite cont_eqb_sym with (c1 := e).
  all: rewrite cont_eqb_sym with (c1 := m).
  all: reflexivity.
Qed.

Lemma BER_nbs_eqb_trans (b1 b2 b3 : BER_nbs) :
  BER_nbs_eqb b1 b2 = true ->
  BER_nbs_eqb b2 b3 = true ->
  BER_nbs_eqb b1 b3 = true.
Proof.
  intros H1 H2.
  unfold BER_nbs_eqb in *.
  repeat break_match;
    try (inversion H2; rewrite ->H2); try (inversion H1; rewrite ->H1).
  all: repeat split_andb.
  all: rewrite cont_eqb_trans with (c2 := id1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 := co1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 :=  t1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 :=  s1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 := bb1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 := ff1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 := ee1); [| assumption | assumption].
  all: try (rewrite cont_eqb_trans with (c2 := eo1); [| assumption | assumption]).
  all: rewrite cont_eqb_trans with (c2 := e1); [| assumption | assumption].
  all: rewrite cont_eqb_trans with (c2 := m1); [| assumption | assumption].
  all: reflexivity.
Qed.

Lemma split_cast_join {l1 l2 : nat}
      (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (c1 : container l1) (c2 : container l2) :
      split_cont (cast_cont (join_cont c1 c2) (eq_refl (l1 + l2)%nat)) L1 L2 = (c1, c2).
Proof. simpl; apply split_join_cont_eq. Qed.

(** * care *)
Lemma split_cut_join {l1 l2 : nat}
      (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (L2' : (0 < l1 + l2 - l1)%nat)
      (c1 : container l1) (c2 : container l2) :
  cont_eqb_pair
    (split_cont (cut_cont (join_cont c1 c2) l1 L2') L1 L2')
    (c1, c2)
  = true.
Proof.
  unfold cont_eqb_pair.
  break_match; rename c0 into r_c1, c into r_c2.
  unfold cut_cont in Heqp.
  generalize (split_cast_join L1 L2 c1 c2); intro.
  unfold cut_num in Heqp.
  unfold try_cut_num in Heqp.
Admitted.

Lemma cont_eq_nbs_eq {l1 l2 : nat} (c1 : container l1) (c2 : container l2) :
  c1 =c= c2 = true ->
  (option_het_eq BER_nbs_eqb) (nbs_of_cont c1) (nbs_of_cont c2) = true.
Proof.
  intros H.
  destruct c1 as (v1, N1, L1).
  destruct c2 as (v2, N2, L2).
  simpl in H; split_andb; debool;
    subst; rename l2 into l; rename v2 into v.
  rewrite proof_irrelevance with (p1 := N2) (p2 := N1).
  rewrite proof_irrelevance with (p1 := L2) (p2 := L1).
  unfold option_het_eq.
  break_match.
  rewrite BER_nbs_eqb_refl; reflexivity.
  reflexivity.
Qed.

Theorem nbs_cont_roundtrip (b : BER_nbs) :
  (option_het_eq BER_nbs_eqb) (nbs_of_cont (cont_of_nbs b)) (Some b) = true.
Proof.
  unfold option_het_eq.
  break_match; [rename b0 into r_b |].
  - (* backward pass successful *)
    unfold nbs_of_cont, cont_of_nbs in Heqo.
    repeat break_match.
    inversion Heqo.
    inversion Heqo.
    subst.
    unfold try_cut_cont in Heqo0.
    repeat break_match; inversion Heqo0; clear Heqo0; subst c.
    unfold split_cut_info in Heqp.
    break_match.
Admitted.

Definition cont_len {l : nat} (c : container l) := l.

Lemma cont_eq_cont_len_eq {l : nat}
      (c1 c2 : container l) :
  c1 = c2 ->
  cont_len c1 = cont_len c2.
Proof. destruct c1, c2. reflexivity. Qed.

Lemma cast_cont_len_eq {l1 l2 : nat}
      {c1 : container l1}
      {E : (l1 = l2)%nat} :
  cont_len (cast_cont c1 E) =
  cont_len c1.
Proof. subst. reflexivity. Qed.

Lemma join_cont_len_sum {l1 l2 : nat}
      (c1 : container l1) (c2 : container l2) :
  cont_len (join_cont c1 c2) = (cont_len c1 + cont_len c2)%nat.
Proof. destruct c1, c2. unfold cont_len. reflexivity. Qed.

Lemma BER_nblen_nbs_nblen (b : BER_nbs)
      (v : Z) (N : 0 <= v) (L : (nblen v <= nbs_nblen b)%nat) :
    cont_of_nbs b = cont (nbs_nblen b) v N L ->
    BER_nblen v = nbs_nblen b.
Proof.
  intros H.
  unfold BER_nblen, nbs_nblen in *.
  unfold cont_of_nbs, append_info, mk_info, mk_content in H.

  destruct b.
  destruct id as (vid, Nid, Lid).
  destruct co as (vco, Nco, Lco).
  unfold join_cont at 2 in H.
  unfold join_cont at 2 in H.
  unfold content_nblen in H.
Admitted.

Lemma cont_of_bits_of_cont_of_nbs (b : BER_nbs) (l : 0 <= c2z (cont_of_nbs b)) :
    cont (BER_nblen (c2z (cont_of_nbs b)))
         (c2z (cont_of_nbs b))
         l
         (BER_nblen_correct (c2z (cont_of_nbs b)))
    =c=
    cont_of_nbs b = true.
Proof.
  simpl.
  break_match.
  split_andb_goal; debool; simpl.
  apply (BER_nblen_nbs_nblen b v N L); assumption.
  reflexivity.
Qed.

Theorem bsaux_bits_roundtrip (b : BER_bs_aux) :
  roundtrip_option
      BER_bs_aux Z BER_bs_aux
      (Some_ize Z_of_bsaux)
      bsaux_of_bits
      BER_bsaux_eqb
      b.
Proof.
  unfold roundtrip_option, bool_het_inverse'; simpl; intros T; clear T.
  unfold bsaux_of_bits, Z_of_bsaux.
  repeat break_match; inversion Heqo; clear Heqo; subst; debool.
  - unfold cont_of_bsaux in *.
    break_match.
    + (* special *)
      unfold mk_special_bsaux in *.
      destruct val.
      all: simpl in *.
      all: inversion Heqo0.
      all: reflexivity.
    + (* normal *)
      contradict Heqo0.
      unfold mk_special_bsaux.
      unfold bsaux_nblen.
      rewrite nbs_is_not_special.
      intros H; inversion H.
  - unfold BER_bsaux_eqb.
    break_match; subst b.

    + (* was special, decoded as nbs *)
      subst.
      contradict Heqo0.
      unfold mk_special_bsaux, c2z, cont_of_bsaux, bits_of_special, classify_BER.
      simpl.
      repeat break_match; discriminate.

    + (* was nbs, decoded as nbs *)
      rename b0 into b.
      rename b1 into r_b.

      (** * care: might be losing information *)
      clear Heqo0 Heqb1.

      unfold cont_of_bsaux in *.
      unfold cont_of_BER_bits in Heqo1.
      break_match; inversion Heqo1; subst c; clear Heqo1.
      generalize (cont_of_bits_of_cont_of_nbs b l); intros H; rewrite cont_eqb_sym in H.
      generalize (cont_eq_nbs_eq
                 (cont_of_nbs b)
                 (cont (BER_nblen (c2z (cont_of_nbs b)))
                       (c2z (cont_of_nbs b))
                       l
                       (BER_nblen_correct (c2z (cont_of_nbs b)))) H);
        intros H1.
      unfold bsaux_nblen in *.
      rewrite Heqo2 in H1.
      unfold option_het_eq in H1; break_match; inversion H1; clear H2.
      generalize (nbs_cont_roundtrip b); intros H2.
      unfold option_het_eq in H2; break_match; inversion H2; clear H3.
      rewrite H1.
      rewrite BER_nbs_eqb_trans with (b2 := b0).
      reflexivity.
      inversion Heqo; rewrite <-H3; rewrite BER_nbs_eqb_sym; assumption.
      assumption.
  - admit. (* trivial *)
  - admit.
  - admit. (* trivial *)
Admitted.
