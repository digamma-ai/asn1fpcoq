Require Import ZArith Lia.
Require Import ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Aux.StructTactics ASN1FP.Aux.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option
        ASN1FP.Conversion.Bitstring_Bits.Def.

Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
  := Basics.compose Some.

Lemma special_eqb_refl (val : BER_special) :
  special_eqb val val = true.
Proof. destruct val; reflexivity. Qed.
  
Theorem bitstring_bsaux_roundtrip (b : BER_bitstring) :
  roundtrip_option
      BER_bitstring BER_bs_aux BER_bitstring
      (Some_ize bsaux_of_bitstring)
      (Some_ize bitstring_of_bsaux)
      BER_bitstring_eqb
      b.
Proof.
  (* basic simplification *)
  unfold roundtrip_option.
  intros H; clear H.
  unfold bool_het_inverse'; simpl.

  unfold bitstring_of_bsaux, bsaux_of_bitstring.
  repeat break_match; inversion Heqb0; subst.
  - simpl. rewrite special_eqb_refl. reflexivity.
  - clear H7 H8.
    unfold c2z, c2n; simpl.
    inversion Heqb0; subst.
    repeat apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H0.
    repeat apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H1.
    rewrite <- H0, <- H1.
    simpl.
    repeat rewrite Z.eqb_refl.
    reflexivity.
  - 
    unfold c2z, c2n; simpl.
    inversion Heqb0; subst.
    repeat apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H0.
    repeat apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H1.
    rewrite <- H0, <- H1.
    simpl.
    repeat rewrite Z.eqb_refl.
    reflexivity.
Qed.

Definition cont_eqb {l1 l2 : nat} (c1 : container l1) (c2 : container l2) :=
  match c1, c2 with
  | cont _ v1 _ _, cont _ v2 _ _ => andb (l1 =? l2)%nat (v1 =? v2)
  end.

Infix "=c=" := cont_eqb (at level 50).

Open Scope bool_scope.

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

Lemma split_join_cont {l1 l2 : nat} (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
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

Lemma split_join_cont_fst {l1 l2 : nat} (L1 : (0 < l1)%nat) (L2 : (0 < l2)%nat)
      (c1 : container l1) (c2 : container l2) :
  fst (split_cont (join_cont c1 c2) L1 L2) =c= c1 = true.
Proof.
  generalize (split_join_cont L1 L2 c1 c2); intros.
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
  generalize (split_join_cont L1 L2 c1 c2); intros.
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
  subst.
  rewrite Nat.eqb_refl, Z.eqb_refl.
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
  - remember (cont_of_bsaux b) as cont_of_b.
    remember (c2z cont_of_b) as bits_of_b.
    unfold BER_bsaux_eqb.
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
      
      (* clean simplification *)
      unfold bsaux_nblen in cont_of_b;
        unfold cont_of_bsaux in Heqcont_of_b.

      destruct b, r_b; simpl; apply (f_equal Some).
      remember (short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5) as b.

      rename id0 into r_id;  move r_id  after b.
      rename co0 into r_co;  move r_co  after b.
      rename  t0 into r_t;   move r_t   after b.
      rename  s0 into r_s;   move r_s   after b.
      rename bb0 into r_bb;  move r_bb  after b.
      rename ff0 into r_ff;  move r_ff  after b.
      rename ee0 into r_ee;  move r_ee  after b.
      rename  e0 into r_e;   move r_e   after b.
      rename  m0 into r_m;   move r_m   after b.
      rename VS0 into r_VS1; move r_VS1 after b.
      rename VS6 into r_VS2; move r_VS2 after b.
      rename VS7 into r_VS3; move r_VS3 after b.
      rename VS8 into r_VS4; move r_VS4 after b.
      rename VS9 into r_VS5; move r_VS5 after b.


      rename Heqb into B, Heqcont_of_b into COB, Heqbits_of_b into BOB.
      move BOB at top.
      move COB at top.
      move B at top.
      rename c into r_cont_of_b, Heqo1 into r_COB, Heqo2 into r_B.





      * (* was short, decoded as short *)
        unfold cont_of_BER_bits in r_COB; break_match; inversion r_COB.
        subst r_cont_of_b; clear r_COB.
        unfold nbs_of_cont, construct_long_nbs, construct_short_nbs in r_B.
        repeat break_match; inversion r_B.
        subst.
        apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H7.
        repeat apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H8.
        subst.
        clear r_B.
        admit.


      * (* was short, decoded as long *)
        exfalso.
        unfold cont_of_BER_bits in Heqo1;
          break_match; inversion Heqo1; clear Heqo1.
        subst c.
        admit.
      * (* was long, decoded as short *)
        (** same as short -> long *)
        admit.
      * (* was long, decoded as long *)
        (** same as short -> short *)
        admit.
        
        




      
        (*
      * (* was short, decoded as short *)
        

        unfold cont_of_BER_bits in Heqo1.
        break_match; inversion Heqo1; clear Heqo1.
        subst c.
        unfold nbs_of_cont in Heqo2.
        break_match; [| inversion Heqo2].
        repeat break_match; inversion Heqo2; clear Heqo2.
        
        -- (* trying to decode as long nbs *)
           unfold construct_long_nbs in H0.
           repeat break_match; inversion H0.

        -- (* decoding as short nbs *)
           unfold construct_short_nbs in H0.
           repeat break_match; inversion H0; clear H0.
           
           subst.
           apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H8.
           repeat apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H9.

           unfold try_cut_cont in Heqo; break_match; inversion Heqo; clear Heqo.
           break_match; inversion H0; clear H0.
           unfold split_cut_info, cut_info,
             split_cont, cut_cont, cast_cont, cut_num, try_cut_num in Heqp.
           repeat break_match.
           inversion Heqp0; clear Heqp0.

           unfold cut_cont in H1.
           unfold cast_cont in H1.



           

           destruct id as (id, IDN, IDL).
           destruct co as (co, CON, COL).
           destruct  t as ( t,  TN,  TL).
           destruct  s as ( s,  SN,  SL).
           destruct bb as (bb, BBN, BBL).
           destruct ff as (ff, FFN, FFL).
           destruct ee as (ee, EEN, EEL).
           destruct e  as ( e,  EN,  EL).
           destruct m  as ( m,  MN,  ML).

           destruct id0 as (id0, IDN0, IDL0).
           destruct co0 as (co0, CON0, COL0).
           destruct  t0 as ( t0,  TN0,  TL0).
           destruct  s0 as ( s0,  SN0,  SL0).
           destruct bb0 as (bb0, BBN0, BBL0).
           destruct ff0 as (ff0, FFN0, FFL0).
           destruct ee0 as (ee0, EEN0, EEL0).
           destruct e0  as ( e0,  EN0,  EL0).
           destruct m0  as ( m0,  MN0,  ML0).

           unfold c2z, Z_of_cont in *.
           subst.
           split_andb_goal.
           simpl.


           unfold cont_eqb.


           subst.
*)

  - admit. (* trivial *)
  - admit.
  - admit. (* trivial *)
Admitted.

Theorem bitsrting_bits_roundtrip (b : BER_bitstring) :
  roundtrip_option
      BER_bitstring Z BER_bitstring
      (Some_ize bits_of_bitstring)
      bitstring_of_bits
      BER_bitstring_eqb
      b.
Admitted.