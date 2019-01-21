Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits ASN1FP.Aux.BitContainer ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.
Require Import Lia.

Open Scope Z.

Let z2n := Z.to_nat.

(* subject to change *)
Inductive BER_nbs :=
| short_nbs (id co t s bb ff ee e m : Z) :
    valid_short id co t s bb ff ee e m = true -> BER_nbs
| long_nbs (id co t s bb ff ee eo e m : Z) :
    valid_long id co t s bb ff ee eo e m = true -> BER_nbs.

Inductive BER_bs_aux :=
| special_aux (val : Z) : BER_bs_aux
| normal_aux (b : BER_nbs) : BER_bs_aux.

Definition bitstring_of_bsaux (b : BER_bs_aux) : BER_bitstring :=
  match b with
  | special_aux val => special val
  | normal_aux b => match b with
                   | short_nbs id co t s bb ff ee e m VS => short id co t s bb ff ee e m VS
                   | long_nbs id co t s bb ff ee eo e m VL => long id co t s bb ff ee eo e m VL
                   end
  end.

Definition bsaux_of_bitstring (b : BER_bitstring) : BER_bs_aux :=
  match b with
  | special val => special_aux val
  | short id co t s bb ff ee e m VS => normal_aux (short_nbs id co t s bb ff ee e m VS)
  | long id co t s bb ff ee eo e m VL => normal_aux (long_nbs id co t s bb ff ee eo e m VL)
  end.

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
  
  Definition mk_info (b : BER_nbs) : container info_nblen :=
    match b with
    | short_nbs id co t s bb ff ee e m VS =>
         append_b8_cont id (VS_id_N VS) (VS_id_L VS)
        (append_b8_cont co (VS_co_N VS) (VS_co_L VS)
        (append_b1_cont t  (VS_t_N VS)  (VS_t_L VS)
        (append_b1_cont s  (VS_s_N VS)  (VS_s_L VS)
        (append_b2_cont bb (VS_bb_N VS) (VS_bb_L VS)
        (append_b2_cont ff (VS_ff_N VS) (VS_ff_L VS)
        (       b2_cont ee (VS_ee_N VS) (VS_ee_L VS)
         ))))))
    | long_nbs id co t s bb ff ee eo e m VL => 
         append_b8_cont id (VL_id_N VL) (VL_id_L VL)
        (append_b8_cont co (VL_co_N VL) (VL_co_L VL)
        (append_b1_cont t  (VL_t_N VL)  (VL_t_L VL)
        (append_b1_cont s  (VL_s_N VL)  (VL_s_L VL)
        (append_b2_cont bb (VL_bb_N VL) (VL_bb_L VL)
        (append_b2_cont ff (VL_ff_N VL) (VL_ff_L VL)
        (       b2_cont ee (VL_ee_N VL) (VL_ee_L VL)
        ))))))
    end.
    
  Definition append_info {l : nat} (b : BER_nbs) (c : container l) :=
    join_cont (mk_info b) c.
  
  Definition mk_content (b : BER_nbs) : container (content_nblen b) :=
    match b with
    | short_nbs id co t s bb ff ee e m VS =>
        (join_cont (cont (z2n (8*(ee+1))) e (VS_e_N VS) (VS_e_L VS))
        (cont (z2n (8*(co - ee - 2))) m (VS_m_N VS) (VS_m_L VS)))
    | long_nbs id co t s bb ff ee eo e m VL => 
        append_b8_cont eo (VL_eo_N VL) (VL_eo_L VL)
        (join_cont (cont (z2n (8*eo)) e (VL_e_N VL) (VL_e_L VL))
        (cont (z2n (8*(co - eo - 2))) m (VL_m_N VL) (VL_m_L VL)))
    end.
  
  Program Definition cont_of_nbs (b : BER_nbs) : container (nbs_nblen b) :=
   match b with
    | short_nbs _ _ _ _ _ _ _ _ _ _ =>
        append_info b (mk_content b)
    | long_nbs _ _ _ _ _ _ _ _ _ _ _=> 
        append_info b (mk_content b)
    end.
  
  Definition bits_of_nbs (b : BER_nbs) : Z :=
  Z_of_cont (cont_of_nbs b).

  (* splitting *)

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

  Definition e_blen_of_long_content {l : nat} (c : container (8 + l)) : nat :=
    z2n (Z_of_cont (fst (cut_b8_cont c))).

  Definition split_me (el ml : nat) (me : container (el + ml)) :=
    split_cont me.

  (*
  Definition split_long_content  {l : nat} (c : container (8 + l)) :=
                         let '(eo, em) := cut_b8_cont c in
                         let eon := z2n (Z_of_cont eo) in
                         match (Nat.eq_dec l (eon + (l - eon))) with
                         | right _ => None
                         | left H => split_cont (cast_cont em H)
                         end.
  *)
                       
  Lemma split_mk_info (b : BER_nbs) :
    match b with
    | short_nbs id co t s bb ff ee e m VS =>
      split_info (mk_info b) =
        (b8_cont id (VS_id_N VS) (VS_id_L VS),
         b8_cont co (VS_co_N VS) (VS_co_L VS),
         b1_cont t  (VS_t_N  VS) (VS_t_L  VS),
         b1_cont s  (VS_s_N  VS) (VS_s_L  VS),
         b2_cont bb (VS_bb_N VS) (VS_bb_L VS),
         b2_cont ff (VS_ff_N VS) (VS_ff_L VS),
         b2_cont ee (VS_ee_N VS) (VS_ee_L VS))
    | long_nbs id co t s bb ff ee eo e m VL =>
      split_info (mk_info b) =
        (b8_cont id (VL_id_N VL) (VL_id_L VL),
         b8_cont co (VL_co_N VL) (VL_co_L VL),
         b1_cont t  (VL_t_N  VL) (VL_t_L  VL),
         b1_cont s  (VL_s_N  VL) (VL_s_L  VL),
         b2_cont bb (VL_bb_N VL) (VL_bb_L VL),
         b2_cont ff (VL_ff_N VL) (VL_ff_L VL),
         b2_cont ee (VL_ee_N VL) (VL_ee_L VL))
    end.
  Proof.
    unfold split_info, mk_info.
    repeat break_match;
    rewrite cut_append_b8 in Heqp; tuple_inversion.
    rewrite cut_append_b8 in Heqp0; tuple_inversion.
    rewrite cut_append_b1 in Heqp1; tuple_inversion.
    rewrite cut_append_b1 in Heqp2; tuple_inversion.
    rewrite cut_append_b2 in Heqp3; tuple_inversion.
    rewrite cut_append_b2 in Heqp4; tuple_inversion.
    reflexivity.
    rewrite cut_append_b8 in Heqp0; tuple_inversion.
    rewrite cut_append_b1 in Heqp1; tuple_inversion.
    rewrite cut_append_b1 in Heqp2; tuple_inversion.
    rewrite cut_append_b2 in Heqp3; tuple_inversion.
    rewrite cut_append_b2 in Heqp4; tuple_inversion.
    reflexivity.
  Qed.

  (*
  Lemma split_mk_content (b : BER_nbs) :
  *)

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