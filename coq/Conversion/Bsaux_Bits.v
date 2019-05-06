Require Import ZArith Lia.
Require Import ProofIrrelevance.
Require Import ASN1FP.Types.Bitstring ASN1FP.Types.BSaux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Aux.StructTactics ASN1FP.Types.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option.
Require Import ASN1FP.Conversion.Bitstring_Bsaux.

Section Definitions.

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
    | special_aux val => nblen (bits_of_special val)
    | normal_aux b => nbs_nblen b
    end.
   
  
  
  (** * nbs -> cont *)
  
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
  
  
  
  (** * cont -> nbs *)
  
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
  
  Program Definition split_info (c : container info_nblen) :
    (cont8 * cont8 * cont1 * cont1 * cont2 * cont2 * cont2) :=
    let '(id, c)  := cut_b8_cont c ilc1 in
    let '(co, c)  := cut_b8_cont c ilc2 in
    let '(t,  c)  := cut_b1_cont c ilc3 in
    let '(s,  c)  := cut_b1_cont c ilc4 in
    let '(bb, c)  := cut_b2_cont c ilc5 in
    let '(ff, ee) := cut_b2_cont c ilc6 in
    (id, co, t, s, bb, ff, ee).
  
  (* TODO: would be nice to clean this *)
  
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
  
  (** * bsaux <-> cont *)
  
  Lemma bits_of_special_nonneg (val : BER_special) :
    0 <= bits_of_special val.
  Proof.
    destruct val; simpl.
    unfold pzero_b; lia.
    unfold nzero_b; lia.
    unfold pinf_b; lia.
    unfold ninf_b; lia.
    unfold nan_b; lia.
  Qed.
  
  Definition cont_of_bsaux (b : BER_bs_aux) : container (bsaux_nblen b) :=
    match b with
    | special_aux val =>
      let zval := bits_of_special val in
      cont (nblen zval) zval (bits_of_special_nonneg val) (Nat.le_refl (nblen zval))
    | normal_aux b => cont_of_nbs b
    end.
  
  
  (** * cont <-> Z *)
  
  Definition cont_of_BER_bits (b : Z) : option (container (BER_nblen b)) :=
    match (Z_gt_le_dec 0 b) with
    | left _ => None
    | right N => Some (cont (BER_nblen b) b N (BER_nblen_correct b))
    end.
    
  Definition Z_of_bsaux (b : BER_bs_aux) :=
    c2z (cont_of_bsaux b).
  
  Definition bits_of_bitstring (b : BER_bitstring) : Z :=
    Z_of_bsaux (bsaux_of_bitstring b).
  
  Definition mk_special_bsaux (b : Z) : option BER_bs_aux :=
    match classify_BER b with
    | Some pzero => Some (special_aux pzero)
    | Some nzero => Some (special_aux nzero)
    | Some pinf  => Some (special_aux pinf)
    | Some ninf  => Some (special_aux ninf)
    | Some nan   => Some (special_aux nan)
    | None       => None
    end.
  
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

End Definitions.



Section Correctness.
 
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

End Correctness.
