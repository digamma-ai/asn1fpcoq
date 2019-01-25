Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits ASN1FP.Aux.BitContainer ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.
Require Import Lia.

Open Scope Z.

(* TODO: restructure *)

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

Section outer_sec.

  Let z2n := Z.to_nat.
  Let c2z {l : nat} (c : container l) := Z_of_cont c.
  Let c2n {l : nat} (c : container l) := z2n (c2z c).

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

Section normal.

  Let info_nblen := 24%nat.
    
  (* joining *)

  (*
  Definition content_nblen (b : BER_nbs) : nat :=
    match b with
    | short_nbs _ co _ _ _ _ ee _ _ _ 
      => (z2n (8 * (ee + 1)) + z2n (8 * (co - ee - 2)))
    | long_nbs _ co _ _ _ _ _ eo _ _ _
      => 8 + (z2n (8 * eo) + z2n (8 * (co - eo - 2)))
    end.
  
  Definition nbs_nblen (b : BER_nbs) : nat :=
    match b with
    | short_nbs _ co _ _ _ _ ee _ _ _ 
      => info_nblen + content_nblen b
    | long_nbs _ co _ _ _ _ _ eo _ _ _
      => info_nblen + content_nblen b
    end.
*)
  
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

  Definition split_info (c : container info_nblen) :
    (cont8 * cont8 * cont1 * cont1 * cont2 * cont2 * cont2) :=
    let '(id, c) := cut_b8_cont c in
    let '(co, c) := cut_b8_cont c in
    let '(t,  c) := cut_b1_cont c in
    let '(s,  c) := cut_b1_cont c in
    let '(bb, c) := cut_b2_cont c in
    let '(ff, ee) := cut_b2_cont c in
    (id, co, t, s, bb, ff, ee).

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
  
  Definition cut_info {l : nat} (c : container (info_nblen + l)) :
    (container info_nblen * container l) :=
  split_cont c.
    
  Definition append_info {l : nat} (b : BER_nbs) (c : container l) :=
    join_cont (mk_info b) c.

  Definition content_nblen (b : BER_nbs) : nat :=
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ => 8*(c2n co - 1)
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ => 8*(c2n co - 1)
    end.

  Definition nbs_nblen (b : BER_nbs) : nat :=
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ => 8*(c2n co + 2)
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ => 8*(c2n co + 2)
    end.

  Program Definition mk_content (b : BER_nbs) : container (content_nblen b) :=
    match b with
    | short_nbs id co t s bb ff ee e m _ _ _ _ =>
      join_cont e m
    | long_nbs id co t s bb ff ee eo e m _ _ _ _ =>
      join_cont eo (join_cont e m)
    end.

  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.


  (* splitting *)

  Definition e_blen_of_long_cont {l : nat} (c : container (8 + l)) : nat :=
    z2n (Z_of_cont (fst (cut_b8_cont c))).

  Definition split_long_cont  {l : nat} (c : container (8 + l))
    : option (container 8 *
              container (e_blen_of_long_cont c) *
              container (l - e_blen_of_long_cont c))
    :=
      let eo := fst (cut_b8_cont c) in
      let em := snd (cut_b8_cont c) in
      let eon := z2n (Z_of_cont eo) in
      match (Nat.eq_dec l (eon + (l - eon))) with
      | right _ => None
      | left H =>
      let '(e, m) := split_cont (cast_cont em H) in
        Some (eo, e, m)
      end.

End normal.

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

(*
Lemma cut_append_info {l : nat} (b : BER_bitstring) (c : container l) :
    cut_info (append_info b c) = (mk_info b, c).

Definition cut_id {l : nat} (c : container (8 + l)) :=
*)

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

End outer_sec.