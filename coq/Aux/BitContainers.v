Require Import ZArith PArith.
Require Import ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits.


Open Scope nat.

Section Pos_container_len.
  
  Definition pos_blen (v : positive) : nat :=
    Z.to_nat ((log_inf v) + 1).
  
  Inductive container := cont (l : nat) (v : positive) (C : pos_blen v <= l).
  
  Definition join_cont (h t : container) : container.
    destruct h eqn:H; rename l into hl, v into hv, C into hC.
    destruct t eqn:T; rename l into tl, v into tv, C into tC.
    remember ((Pos.shiftl_nat hv tl) + tv)%positive as rv.
    remember (hl + tl) as rl.
    assert (rC : pos_blen rv <= rl).
    {
      subst.
      unfold pos_blen in *.
      admit.
    }
    exact (cont rl rv rC).
  Admitted.
  
  Definition split_cont_fst (hl : nat) (c : container) : container * container.
    destruct c.
    remember (l - hl) as tl.
    remember (Pos.shiftr_nat v tl) as t.
    remember (Z.to_pos ((Z.pos v) mod (2^(Z.of_nat tl)))) as h.
    assert (hC : pos_blen h <= hl).
    {
      admit.
    }
    assert (tC : pos_blen t <= tl).
    {
      admit.
    }
    exact (cont hl h hC, cont tl t tC).
  Admitted.

End Pos_container_len.

Section Pos_container_leading.
  
  Inductive word :=
    | mk_word (l : nat) (v : positive).
  
  Definition join_words (h t : word) : word :=
    match h, t with
    | mk_word lh vh, mk_word lt vt => mk_word lh ((Pos.shiftl_nat vh lt) + vt)
    end.
  
  Definition word_pos_blen (w : word) : nat :=
    match w with
    | mk_word l v => l + Z.to_nat ((log_inf v) + 1)
    end.
  
  Definition split_head (hl : nat) (w : word) : word * word :=
    match w with
    | mk_word l v =>
    let wbl := word_pos_blen w in
    let h := Pos.shiftr_nat v (wbl - l - hl) in
      (mk_word l h,
       mk_word (wbl - l - Z.to_nat ((log_inf h) + 1))
               (Z.to_pos ((Z.pos v) mod (2^(Z.of_nat hl)))))
    end.
  
  Lemma split_join (h t : word) :
    split_head (word_pos_blen h) (join_words h t) = (h, t).
  Proof.
    destruct h eqn:H; rename l into hl, v into hv.
    destruct t eqn:T; rename l into tl, v into tv.
    unfold split_head, join_words, word_pos_blen.
    subst.
    remember (Pos.shiftl_nat hv tl + tv)%positive as r.
  Abort.

End Pos_container_leading.

Open Scope Z.

Section Z_container_len.

  Inductive zcontainer :=
    zcont (l : Z) (v : Z) : (0 <= v) -> (blen v <= l) -> zcontainer.
    
  Definition join_zcont (h t : zcontainer) : zcontainer.
    destruct h eqn:H; rename l into hl, v into hv, l0 into hOV, l1 into hBV.
    destruct t eqn:T; rename l into tl, v into tv, l0 into tOV, l1 into tBV.
    remember (hl + tl) as rl.
    remember (hv * 2^tl + tv) as rv.
    assert (rOV : 0 <= rv) by admit. (** trivial *)
    assert (rBV : blen rv <= rl).
    {
      subst.
      unfold blen in *.
      admit.
      (** somewhat complicated, has been attempted before *)
    }
    exact (zcont rl rv rOV rBV).
  Admitted.
  
  Definition split_zcont_by_fst (hl : Z) (c : zcontainer) : zcontainer * zcontainer.
    destruct c eqn:C; rename l0 into OV, l1 into BV.
    remember (l - hl) as tl.
    remember (v mod 2^tl) as tv.
    remember (v / 2^tl) as hv.
    assert (hOV : 0 <= hv) by admit. (* simple *)
    assert (tOV : 0 <= tv) by admit. (* simple *)
    assert (hBV : blen hv <= hl) by admit. (* complex *)
    assert (tBV : blen tv <= tl) by admit. (* complex *)
    exact (zcont hl hv hOV hBV, zcont tl tv tOV tBV).
  Admitted.

End Z_container_len.