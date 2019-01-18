Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits ASN1FP.Aux.BitContainer ASN1FP.Aux.Tactics.
Require Import Lia.

Open Scope Z.

Let z2n := Z.to_nat.

(* subject to change *)

Definition bitstring_info_nblen (b : BER_bitstring) : nat :=
  match b with
  | special val => nblen (Z.abs val)
  | short _ co _ _ _ _ ee _ _ _ 
    => 24 (*(8 + (8 + (1 + (1 + (2 + (2 + 2))))))*)
  | long _ co _ _ _ _ _ eo _ _ _
    => 32 (*(8 + (8 + (1 + (1 + (2 + (2 + (2 + 8)))))))*)
  end.
  
Definition bitstring_content_nblen (b : BER_bitstring) : nat :=
  match b with
  | special val => nblen (Z.abs val)
  | short _ co _ _ _ _ ee _ _ _ 
    => (z2n (8 * (ee + 1)) + z2n (8 * (co - ee - 2)))
  | long _ co _ _ _ _ _ eo _ _ _
    => (z2n (8 * eo) + z2n (8 * (co - eo - 2)))
  end.

Definition bitstring_nblen (b : BER_bitstring) : nat :=
  match b with
  | special val => nblen (Z.abs val)
  | short _ co _ _ _ _ ee _ _ _ 
    => bitstring_info_nblen b + bitstring_content_nblen b
  | long _ co _ _ _ _ _ eo _ _ _
    => bitstring_info_nblen b + bitstring_content_nblen b
  end.

(* create containers for commong lengths *)
Definition b1_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 1)%nat)
  : container 1 := cont 1 v N L.

Definition b2_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 2)%nat)
  : container 2 := cont 2 v N L.

Definition b8_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 8)%nat)
  : container 8 := cont 8 v N L.

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
  : container 1 * container l := split_cont c.

Definition cut_b2_cont {l : nat} (c : container (2 + l))
  : container 2 * container l := split_cont c.

Definition cut_b8_cont {l : nat} (c : container (8 + l))
  : container 8 * container l := split_cont c.


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

Fact tmpaux1 : 0 <= 0. Proof. reflexivity. Qed.
Fact tmpaux2 : (nblen 0 <= 17)%nat. Proof. unfold nblen. simpl. lia. Qed.

Fact nblen_cont_len (v : Z) :
  (nblen v <= nblen v)%nat.
Proof. reflexivity. Qed.

Definition info_cont (b : BER_bitstring) : container (bitstring_info_nblen b) :=
  match b with
  | special val => 
    let v := Z.abs val in
    cont (nblen v) v (Z.abs_nonneg val) (nblen_cont_len v)


  | short id co t s bb ff ee e m VS =>
       append_b8_cont id (VS_id_N VS) (VS_id_L VS)
      (append_b8_cont co (VS_co_N VS) (VS_co_L VS)
      (append_b1_cont t  (VS_t_N VS)  (VS_t_L VS)
      (append_b1_cont s  (VS_s_N VS)  (VS_s_L VS)
      (append_b2_cont bb (VS_bb_N VS) (VS_bb_L VS)
      (append_b2_cont ff (VS_ff_N VS) (VS_ff_L VS)
      (       b2_cont ee (VS_ee_N VS) (VS_ee_L VS)
       ))))))
  | long id co t s bb ff ee eo e m VL => 
       append_b8_cont id (VL_id_N VL) (VL_id_L VL)
      (append_b8_cont co (VL_co_N VL) (VL_co_L VL)
      (append_b1_cont t  (VL_t_N VL)  (VL_t_L VL)
      (append_b1_cont s  (VL_s_N VL)  (VL_s_L VL)
      (append_b2_cont bb (VL_bb_N VL) (VL_bb_L VL)
      (append_b2_cont ff (VL_ff_N VL) (VL_ff_L VL)
      (append_b2_cont ee (VL_ee_N VL) (VL_ee_L VL)
      (       b8_cont eo (VL_eo_N VL) (VL_eo_L VL)
      )))))))
  end.
  
Definition append_info {l : nat} (b : BER_bitstring) (c : container l) :=
  join_cont (info_cont b) c.

Definition mk_content (b : BER_bitstring) : container (bitstring_content_nblen b) :=
  match b with
  | special val =>
    let v := Z.abs val in
    cont (nblen v) v (Z.abs_nonneg val) (nblen_cont_len v)
  | short id co t s bb ff ee e m VS =>
      (join_cont (cont (z2n (8*(ee+1))) e (VS_e_N VS) (VS_e_L VS))
      (cont (z2n (8*(co - ee - 2))) m (VS_m_N VS) (VS_m_L VS)))
  | long id co t s bb ff ee eo e m VL => 
      (join_cont (cont (z2n (8*eo)) e (VL_e_N VL) (VL_e_L VL))
      (cont (z2n (8*(co - eo - 2))) m (VL_m_N VL) (VL_m_L VL)))
  end.

Program Definition cont_of_bitstring (b : BER_bitstring) : container (bitstring_nblen b) :=
 match b with
  | special val =>
    let v := Z.abs val in
    cont (nblen v) v (Z.abs_nonneg val) (nblen_cont_len v)
  | short _ _ _ _ _ _ _ _ _ _ =>
      append_info b (mk_content b)
  | long _ _ _ _ _ _ _ _ _ _ _=> 
      append_info b (mk_content b)
  end.

Definition bits_of_bitstring (b : BER_bitstring) : Z :=
  Z_of_cont (cont_of_bitstring b).

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