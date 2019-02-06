Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits ASN1FP.Aux.BitContainer ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.
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

(* TODO : move this to containers *)
Definition Z_of_cont {l : nat} (c : container l) :=
  match c with cont _ v _ _ => v end.

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
| long_nbs
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (eo : cont8)
    (e : container (8*(c2n eo))) (m : container (8 * ((c2n co) - (c2n eo) - 2)))
    (VL1 : c2z id = real_id_b) (VL2 : c2z t = 1) (VL3 : c2z ee = 3) (VL4 : 1 <= c2z m).

Inductive BER_bs_aux :=
| special_aux (val : Z) : BER_bs_aux
| normal_aux (b : BER_nbs) : BER_bs_aux.



(** * bitstring -> nbs lemmas *)

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
  let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
  (nblen e <= 8* (c2n eec + 1))%nat.
Admitted.

Lemma VL_e_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= e.
Proof. deVL; lia. Qed.

Lemma VL_e_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
  (nblen e <= 8 * c2n eoc)%nat.
Admitted.

(** * m *)
Lemma VS_m_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= m.
Proof. deVS; lia. Qed.

Lemma VS_m_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  let coc := (b8_cont co (VS_co_N VS) (VS_co_L VS)) in
  let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
  (nblen m <= 8 * (c2n coc - c2n eec - 2))%nat.
Admitted.

Lemma VL_m_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= m.
Proof. deVL; lia. Qed.

Lemma VL_m_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  let coc := (b8_cont co (VL_co_N VL) (VL_co_L VL)) in
  let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
  (nblen m <= 8* (c2n coc - c2n eoc - 2))%nat.
Admitted.

Lemma valid_short_VS1 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b8_cont id (VS_id_N VS) (VS_id_L VS)) = real_id_b.
Admitted.

Lemma valid_short_VS2 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b1_cont t (VS_t_N VS) (VS_t_L VS)) = 1.
Admitted.

Lemma valid_short_VS3 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  c2z (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) <= 2.
Admitted.

Lemma valid_short_VS4 {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  let coc := (b8_cont co (VS_co_N VS) (VS_co_L VS)) in
  let eec := (b2_cont ee (VS_ee_N VS) (VS_ee_L VS)) in
  1 <= c2z (cont (8 * (c2n coc - c2n eec - 2)) m (VS_m_N VS) (VS_m_L VS)).
Admitted.

Lemma valid_long_VL1 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b8_cont id (VL_id_N VL) (VL_id_L VL)) = real_id_b.
Admitted.

Lemma valid_long_VL2 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b1_cont t (VL_t_N VL) (VL_t_L VL)) = 1.
Admitted.

Lemma valid_long_VL3 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  c2z (b2_cont ee (VL_ee_N VL) (VL_ee_L VL)) = 3.
Admitted.

Lemma valid_long_VL4 {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  let coc := (b8_cont co (VL_co_N VL) (VL_co_L VL)) in
  let eoc := (b8_cont eo (VL_eo_N VL) (VL_eo_L VL)) in
  1 <= c2z (cont (8 * (c2n coc - c2n eoc - 2)) m (VL_m_N VL) (VL_m_L VL)).
Admitted.



(** * nbs -> bitstring lemmas *)

Lemma short_nbs_valid
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (e : container (8 * (c2n ee + 1))) (m : container (8*((c2n co) - (c2n ee) - 2)))
    (VS1 : c2z id = real_id_b) (VS2 : c2z t = 1) (VS3 : c2z ee <= 2) (VS4 : 1 <= c2z m) :
    valid_short (c2z id) (c2z co)
                (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee)
                (c2z e) (c2z m) = true.
Admitted.

Lemma long_nbs_valid
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (eo : cont8)
    (e : container (8*(c2n eo))) (m : container (8 * ((c2n co) - (c2n eo) - 2)))
    (VL1 : c2z id = real_id_b) (VL2 : c2z t = 1) (VL3 : c2z ee = 3) (VL4 : 1 <= c2z m) :
    valid_long  (c2z id) (c2z co)
                (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee) (c2z eo)
                (c2z e) (c2z m) = true.
Admitted.




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
      (valid_short_VS4 VS))
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
      (valid_long_VL4 VL))
  end.

Definition bitstring_of_bsaux (b : BER_bs_aux) : BER_bitstring :=
  match b with
  | special_aux val => special val
  | normal_aux b =>
    match b with
    | short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 =>
      short (c2z id) (c2z co)
            (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee)
            (c2z e) (c2z m)
            (short_nbs_valid id co t s bb ff ee e m VS1 VS2 VS3 VS4)
    | long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 =>
      long  (c2z id) (c2z co)
            (c2z t) (c2z s) (c2z bb) (c2z ff) (c2z ee) (c2z eo)
            (c2z e) (c2z m)
            (long_nbs_valid id co t s bb ff ee eo e m VL1 VL2 VL3 VL4)
    end
  end.


(** * lengths *)

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
  destruct b.
  - (* short *)
    unfold content_nblen, nbs_nblen, info_nblen.
    remember (c2n co) as x.
    replace 24%nat with (8 * 3)%nat by trivial.
    rewrite <- Nat.mul_add_distr_l.
    admit.
  - (* long *)
    unfold content_nblen, nbs_nblen, info_nblen.
    remember (c2n co) as x.
    replace 24%nat with (8 * 3)%nat by trivial.
    rewrite <- Nat.mul_add_distr_l.
    admit.
Admitted.

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



(** * splitting (into) nbs *)

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

Definition e_nblen_of_long_cont {l : nat} (c : container (8 + l)) : nat :=
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
            container (e_nblen_of_long_cont c) *
            container (l - e_nblen_of_long_cont c)) :=
    let eo := fst (cut_b8_cont c) in
    let em := snd (cut_b8_cont c) in
    let eon := c2n eo in
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
              Some (short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4)
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
               Some (long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4)
            end
          end
        end
      end
    end
  end.

Definition nbs_of_cont {l : nat} (c : container l) :=
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
  if b <=? 0
  then None
  else match (mk_special_bsaux b) with
       | Some b => Some b
       | None =>
         match (nbs_of_cont (cont_of_Z_abs b)) with
         | None => None
         | Some b => Some (normal_aux b)
         end
       end.

Definition bitstring_of_bits (b : Z) : option BER_bitstring :=
  match bsaux_of_bits b with
  | None => None
  | Some b => Some (bitstring_of_bsaux b)
  end.



(** * correctness lemmas *)

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