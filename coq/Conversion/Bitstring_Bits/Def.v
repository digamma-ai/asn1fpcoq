Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits ASN1FP.Aux.BitContainer ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.
Require Import Lia.

Open Scope Z.

Section CommonLengths.

  Definition cont1 := container 1.
  Definition cont2 := container 2.
  Definition cont8 := container 8.

  (* create containers for commong lengths *)
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
  Definition cut_b1_cont {l : nat} (c : container (1 + l))
  : cont1 * container l := split_cont c.

  Definition cut_b2_cont {l : nat} (c : container (2 + l))
  : cont2 * container l := split_cont c.

  Definition cut_b8_cont {l : nat} (c : container (8 + l))
  : cont8 * container l := split_cont c.

  (* these might or might not be useful *)
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

End CommonLengths.


Section NormalBitStrings.

  Definition z2n := Z.to_nat.
  Definition c2z {l : nat} (c : container l) := Z_of_cont c.
  Definition c2n {l : nat} (c : container l) := z2n (c2z c).

  Ltac deVS :=
    unfold valid_short, real_id_b in *; repeat split_andb; debool; subst.
  
  Ltac deVL :=
    unfold valid_long, real_id_b in *; repeat split_andb; debool; subst.
  
  
  (** * id *)
  Lemma VS_id_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= id.
  Proof. deVS; lia. Qed.
  
  Lemma VS_id_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen id <= 8)%nat.
  Proof. deVS; unfold nblen; simpl; lia. Qed.
  
  Lemma VL_id_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= id.
  Proof. deVL; lia. Qed.
  
  Lemma VL_id_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen id <= 8)%nat.
  Proof. deVL; unfold nblen; simpl; lia. Qed.
  
  (** * co *)
  Lemma VS_co_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= co.
  Proof. deVS; lia. Qed.
  
  Lemma VS_co_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen co <= 8)%nat.
  Admitted.
  
  Lemma VL_co_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= co.
  Proof. deVL; lia. Qed.
  
  Lemma VL_co_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen co <= 8)%nat.
  Admitted.
  
  (** * t *)
  Lemma VS_t_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= t.
  Proof. deVS; lia. Qed.
  
  Lemma VS_t_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen t <= 1)%nat.
  Admitted.
  
  Lemma VL_t_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= t.
  Proof. deVL; lia. Qed.
  
  Lemma VL_t_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen t <= 1)%nat.
  Admitted.
  
  (** * s *)
  Lemma VS_s_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= s.
  Proof. deVS; lia. Qed.
  
  Lemma VS_s_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen s <= 1)%nat.
  Admitted.
  
  Lemma VL_s_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= s.
  Proof. deVL; lia. Qed.
  
  Lemma VL_s_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen s <= 1)%nat.
  Admitted.
  
  (** * bb *)
  Lemma VS_bb_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= bb.
  Proof. deVS; lia. Qed.
  
  Lemma VS_bb_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen bb <= 2)%nat.
  Admitted.
  
  Lemma VL_bb_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= bb.
  Proof. deVL; lia. Qed.
  
  Lemma VL_bb_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen bb <= 2)%nat.
  Admitted.
  
  (** * ff *)
  Lemma VS_ff_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= ff.
  Proof. deVS; lia. Qed.
  
  Lemma VS_ff_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen ff <= 2)%nat.
  Admitted.
  
  Lemma VL_ff_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= ff.
  Proof. deVL; lia. Qed.
  
  Lemma VL_ff_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen ff <= 2)%nat.
  Admitted.
  
  (** * ee *)
  Lemma VS_ee_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= ee.
  Proof. deVS; lia. Qed.
  
  Lemma VS_ee_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen ee <= 2)%nat.
  Admitted.
  
  Lemma VL_ee_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= ee.
  Proof. deVL; lia. Qed.
  
  Lemma VL_ee_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen ee <= 2)%nat.
  Admitted.
  
  (** * eo *)
  Lemma VL_eo_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= eo.
  Proof. deVL; lia. Qed.
  
  Lemma VL_eo_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen eo <= 8)%nat.
  Admitted.
  
  (** * e *)
  Lemma VS_e_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= e.
  Proof. deVS; lia. Qed.
  
  Lemma VS_e_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen e <= z2n (8*(ee + 1)))%nat.
  Admitted.
  
  Lemma VL_e_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= e.
  Proof. deVL; lia. Qed.
  
  Lemma VL_e_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen e <= z2n (8*eo))%nat.
  Admitted.
  
  (** * m *)
  Lemma VS_m_N {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    0 <= m.
  Proof. deVS; lia. Qed.
  
  Lemma VS_m_L {id co t s bb ff ee e m : Z}
        (VS : valid_short id co t s bb ff ee e m = true) :
    (nblen m <= z2n (8*(co - ee - 2)))%nat.
  Admitted.
  
  Lemma VL_m_N {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    0 <= m.
  Proof. deVL; lia. Qed.
  
  Lemma VL_m_L {id co t s bb ff ee eo e m : Z}
        (VL : valid_long id co t s bb ff ee eo e m = true) :
    (nblen m <= z2n (8*(co - eo - 2)))%nat.
  Admitted.

  Inductive BER_nbs :=
  | short_nbs
      (id co : cont8)
      (t s : cont1) (bb ff ee : cont2)
      (e : container (8*((c2n ee) + 1))) (m : container (8*((c2n co) - (c2n ee) - 2)))
      (VS1 : c2z id = real_id_b) (VS2 : c2z t = 1) (VS3 : c2z ee <= 2) (VS4 : 1 <= c2z m)
  | long_nbs
      (id co : cont8)
      (t s : cont1) (bb ff ee : cont2)
      (eo : cont8)
      (e : container (8*(c2n eo))) (m : container (8*((c2n co) - (c2n eo) - 2)))
      (VL1 : c2z id = real_id_b) (VL2 : c2z t = 1) (VL3 : c2z ee = 3) (VL4 : 1 <= c2z m).
  
  Inductive BER_bs_aux :=
  | special_aux (val : Z) : BER_bs_aux
  | normal_aux (b : BER_nbs) : BER_bs_aux.

  Definition bitstring_of_bsaux (b : BER_bs_aux) : BER_bitstring.
  Admitted.
  
  Definition bsaux_of_bitstring (b : BER_bitstring) : BER_bs_aux.
  Admitted.

End NormalBitStrings.


Section Lengths.

  Definition info_nblen := 24%nat.
  
  Definition nbs_nblen (b : BER_nbs) : nat :=
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ => 8 * (c2n co + 2)
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ => 8 * (c2n co + 2)
    end.

  Definition content_nblen (b : BER_nbs) : nat :=
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ => 8 * (c2n co - 1)
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ => 8 * (c2n co - 1)
    end.

  Lemma short_nblen_correct {l1 l2 : nat} (co : container l1) (ee : container l2) :
      (8 * (c2n ee + 1) + 8 * (c2n co - c2n ee - 2))%nat = (8 * (c2n co - 1))%nat.
  Proof.
    remember (c2n co) as x; remember (c2n ee) as y.
    rewrite <- Nat.mul_add_distr_l.
    replace (y + 1 + (x - y - 2))%nat with (x - 1)%nat.
    reflexivity.
  Admitted.

  Lemma long_nblen_correct {l1 l2 : nat} (co : container l1) (eo : container l2) :
      (8 + (8 * c2n eo + 8 * (c2n co - c2n eo - 2)))%nat = (8 * (c2n co - 1))%nat.
  Proof.
    remember (c2n co) as x; remember (c2n eo) as y.
    rewrite <- Nat.mul_add_distr_l.
  Admitted.

  Lemma nbs_nblen_correct (b : BER_nbs) :
    (info_nblen + content_nblen b)%nat = nbs_nblen b.
  Proof.
    unfold info_nblen.
    destruct b.
    - (* short *)
      unfold content_nblen, nbs_nblen.
      remember (c2n co) as x.
      replace 24%nat with (8 * 3)%nat by trivial.
      rewrite <- Nat.mul_add_distr_l.
      admit.
    - (* long *)
      unfold content_nblen, nbs_nblen.
      remember (c2n co) as x.
      replace 24%nat with (8 * 3)%nat by trivial.
      rewrite <- Nat.mul_add_distr_l.
      admit.
  Admitted.

End Lengths.
  

Section Join.

    
  Definition mk_info (b : BER_nbs) : container info_nblen :=
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ =>
         join_cont id
        (join_cont co
        (join_cont t
        (join_cont s
        (join_cont bb
        (join_cont ff ee
         )))))
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ =>
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
    | short_nbs id co t s bb ff ee e m _ _ _ _ =>
      cast_cont (join_cont e m) (short_nblen_correct co ee)
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ =>
      cast_cont (join_cont eo (join_cont e m)) (long_nblen_correct co eo)
    end.

  Definition cont_of_nbs (b : BER_nbs) : container (nbs_nblen b) :=
    cast_cont (append_info b (mk_content b)) (nbs_nblen_correct b).

End Join.


Section Split.

  Definition cut_info {l : nat} (c : container (info_nblen + l)) :
    (container info_nblen * container l) :=
    split_cont c.

  Definition split_info (c : container info_nblen) :
    (cont8 * cont8 * cont1 * cont1 * cont2 * cont2 * cont2) :=
    let '(id, c) := cut_b8_cont c in
    let '(co, c) := cut_b8_cont c in
    let '(t,  c) := cut_b1_cont c in
    let '(s,  c) := cut_b1_cont c in
    let '(bb, c) := cut_b2_cont c in
    let '(ff, ee) := cut_b2_cont c in
    (id, co, t, s, bb, ff, ee).

  Definition split_cut_info {l : nat} (c : container (info_nblen + l)) :=
    let '(info, content) := cut_info c in
    let '(id, co, t, s, bb, ff, ee) := split_info info in
    (id, co, t, s, bb, ff, ee, content).

  Definition e_blen_of_long_cont {l : nat} (c : container (8 + l)) : nat :=
    c2n (fst (cut_b8_cont c)).

  Definition cut_num (a b : nat) : option (a = b + (a - b))%nat :=
    match (Nat.eq_dec a (b + (a - b))) with
    | right _ => None
    | left H => Some H
    end.

  Definition cut_cont {l : nat} (c : container l) (l1 : nat) : option (container (l1 + (l - l1))) :=
    match (cut_num l l1) with
    | None => None
    | Some H => Some (cast_cont c H)
    end.

  Definition split_long_cont  {l : nat} (c : container (8 + l))
    : option (container 8 *
              container (e_blen_of_long_cont c) *
              container (l - e_blen_of_long_cont c))
    :=
      let eo := fst (cut_b8_cont c) in
      let em := snd (cut_b8_cont c) in
      let eon := z2n (Z_of_cont eo) in
      match (cut_cont em eon) with
      | None => None
      | Some em =>
      let '(e, m) := split_cont em in
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

  Definition check_valid_short
             {l : nat} (id : cont8) (t : cont1) (ee : cont2) (m : container l) :=
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
            Some (VS1, VS2, VS3, VS4)
          end
        end
      end
    end.

  Definition check_valid_long
             {l : nat} (id : cont8) (t : cont1) (eo : cont2) (m : container l) :=
    match Z.eq_dec (c2z id) real_id_b with
    | right _ => None
    | left VS1 =>
      match Z.eq_dec (c2z t) 1 with
      | right _ => None
      | left VS2 =>
        match Z.eq_dec (c2z eo) 3 with
        | right _ => None
        | left VS3 =>
          match Z_le_dec 1 (c2z m) with
          | right _ => None
          | left VS4 =>
            Some (VS1, VS2, VS3, VS4)
          end
        end
      end
    end.

  Definition construct_short_nbs
             { l1 l2 : nat }
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
        match (check_valid_short id t ee m) with
        | None => None
        | Some (VS1, VS2, VS3, VS4) =>
        Some (short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4)
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
        match (check_valid_long id t ee m) with
        | None => None
        | Some (VS1, VS2, VS3, VS4) =>
        Some (long_nbs id co t s bb ff ee eo e m VS1 VS2 VS3 VS4)
        end
      end
    end.

  Definition cont_len_split {l : nat} (c : container l) (l1 : nat) :=
    match (cut_cont c info_nblen) with
    | None => None
    | Some c =>
      let '(id, co, t, s, bb, ff, ee, content) := split_cut_info c in
      if (c2n ee =? 3)%nat
      then match (cut_cont content 8) with
           | None => None
           | Some content =>
             match (split_long_cont content) with
             | None => None
             | Some (eo, e, m) =>
                 construct_long_nbs id co t s bb ff ee eo e m
               end
             end
      else match (cut_cont content (c2n ee + 1)) with
           | None => None
           | Some c =>
             let '(e, m) := split_cont c in
               construct_short_nbs id co t s bb ff ee e m
           end
    end.

  Lemma split_mk_info (b : BER_nbs) :
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ =>
      split_info (mk_info b) = (id, co, t, s, bb, ff, ee)
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ =>
      split_info (mk_info b) = (id, co, t, s, bb, ff, ee)
    end.
  Proof.
    unfold split_info, mk_info, cut_b1_cont, cut_b2_cont, cut_b8_cont.
    repeat break_match.
    rewrite split_join_roundtrip in Heqp; tuple_inversion.
    rewrite split_join_roundtrip in Heqp0; tuple_inversion.
    rewrite split_join_roundtrip in Heqp1; tuple_inversion.
    rewrite split_join_roundtrip in Heqp2; tuple_inversion.
    rewrite split_join_roundtrip in Heqp3; tuple_inversion.
    rewrite split_join_roundtrip in Heqp4; tuple_inversion.
    reflexivity.
    rewrite split_join_roundtrip in Heqp; tuple_inversion.
    rewrite split_join_roundtrip in Heqp0; tuple_inversion.
    rewrite split_join_roundtrip in Heqp1; tuple_inversion.
    rewrite split_join_roundtrip in Heqp2; tuple_inversion.
    rewrite split_join_roundtrip in Heqp3; tuple_inversion.
    rewrite split_join_roundtrip in Heqp4; tuple_inversion.
    reflexivity.
  Qed.

End Split.


Section special.

End special.


Definition BER_blen (b : Z) : nat :=
  let l := nblen b in
  l + (l mod 8)%nat.

Fact BER_blen_correct (b : Z) :
  (nblen b <= BER_blen b)%nat.
Proof. unfold BER_blen; lia. Qed.

Definition cont_of_BER_bits (b : Z) : option (container (BER_blen b)) :=
  match (Z_gt_le_dec 0 b) with
  | left _ => None
  | right N => Some (cont (BER_blen b) b N (BER_blen_correct b))
  end.

Definition bitstring_of_bits (b : Z) : option BER_bitstring :=
  match classify_BER b with
    | Some pzero => Some (special pzero_b)
    | Some nzero => Some (special nzero_b)
    | Some pinf => Some (special pinf_b)
    | Some ninf => Some (special ninf_b)
    | Some nan => Some (special nan_b)
    | None =>
      let '(id, co_content) := split_octets_by_fst 1 b in
      let '(co, content) := split_octets_by_fst 1 co_content in
      let '(tsbbffee, l_exp_signif) := split_octets_by_fst 1 content in
      let '(t, sbbffee) := split_bits_by_snd 7 tsbbffee in
      let '(s, bbffee) := split_bits_by_snd 6 sbbffee in
      let '(bb, ffee) := split_bits_by_snd 4 bbffee in
      let '(ff, ee) := split_bits_by_snd 2 ffee in
      if (2 <? ee)
      then
        let '(e_olen, exp_signif) := split_octets_by_fst 1 l_exp_signif in
        let '(exp, signif) := split_octets_by_snd (co - e_olen - 2) exp_signif in
        match valid_long_sumbool id co t s bb ff ee e_olen exp signif with
          | right _ => None
          | left V => Some (long id co t s bb ff ee e_olen exp signif V)
        end
      else
        let '(exp, signif) := split_octets_by_snd (co - ee - 2) l_exp_signif in
        match valid_short_sumbool id co t s bb ff ee exp signif with
          | right _ => None
          | left V => Some (short id co t s bb ff ee exp signif V)
        end
    end.

Definition bits_of_bitstring (b : BER_bitstring) : Z.
Admitted.