Require Import ZArith Datatypes Sumbool Bool.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.
Require Import ASNDef Aux.

Notation float := Binary.binary_float.

Definition good_real_sumbool (m : positive) (e : Z) (b : radix) :=
  sumbool_of_bool (good_real m e b).

Definition binary_bounded_sumbool (prec emax: Z) (m: positive) (e:Z) :=
  sumbool_of_bool (Binary.bounded prec emax m e).

Definition IEEE_to_ASN {prec emax: Z} (f : float prec emax)
  : option ASN_real :=
  match f with
  | B754_zero _ _ s => Some (ASN_zero s)
  | B754_infinity _ _ s => Some (ASN_infinity s)
  | B754_nan _ _ _ _ _ => Some (ASN_nan)
  | B754_finite _ _ s m e _ =>
    match good_real_sumbool m e radix2 with
    | left G => Some (ASN_finite s radix2 m e G)
    | right _ => None
    end
  end.

Definition prec_gt_1 (prec : Z) : Prop := (prec > 1)%Z.

Definition reasonable_float (prec emax : Z) : bool :=
  andb
    (Z.gtb prec  1)
    (Z.gtb emax prec).

Lemma reasonable_prec_gt_1 {prec emax : Z} : reasonable_float prec emax = true -> prec_gt_1 prec.
Proof.
  intros H.
  unfold reasonable_float in H.
  apply andb_prop in H.
  destruct H as [H H1]. clear H1.
  apply Zgt_is_gt_bool.
  apply H.
Qed.

Definition reasonable_float_sumbool (prec emax : Z) :=
  sumbool_of_bool (reasonable_float prec emax).

Fact def_NAN (prec : Z) (pc : prec_gt_1 prec) :
  nan_pl prec 1 = true.
Proof.
  unfold nan_pl. simpl.
  apply Zlt_is_lt_bool.
  apply Z.gt_lt.
  apply pc.
Qed.

Definition ASN_to_IEEE (prec emax: Z) (r : ASN_real)
  : option (float prec emax) :=
  match reasonable_float_sumbool prec emax with
  | left R =>
    match r with
    | ASN_zero s => Some (B754_zero prec emax s)
    | ASN_infinity s => Some (B754_infinity prec emax s)
    | ASN_nan => Some (B754_nan prec emax true 1 (def_NAN prec (reasonable_prec_gt_1 R)))
    | ASN_finite s b m e x =>
      match binary_bounded_sumbool prec emax m e with
      | left B => Some (B754_finite prec emax s m e B)
      | right _ => None
      end
    end
  | right _ => None
  end.

Definition float_eqb_nan_t {prec emax : Z} (x y : float prec emax) : bool :=
  match Bcompare prec emax x y with
  | Some Eq => true
  | None => true
  | _ => false
  end.

Definition pass_guarantee {A B : Type} (r : A -> bool) (f : A -> option B) : Prop :=
  forall (a : A), (r a = true -> is_Some_b (f a) = true).

Definition roundtrip {A B: Type}
           (f: A -> option B) (* forward pass *)
           (b: B -> option A) (* backward pass *)
           (r: A -> bool) (* subset of A on which roundtrip works *)
           (R: pass_guarantee r f) (* r guarantees f happens *)
           (e: A -> A -> bool) (* equivalence on A *)
           (x: A) (* value *)
  : Prop :=
    r x = true ->
    option_liftM2 e (option_bind b (f x)) (Some x) = Some true.

Definition is_convertible_IEEE (prec emax : Z) (f : float prec emax) : bool :=
  if (reasonable_float prec emax)
  then match f with
       | B754_finite _ _ _ m e _ => good_real m e radix2
       | _ => true
       end
  else false.

Lemma conv_pass_guarantee (prec emax : Z) :
  pass_guarantee (is_convertible_IEEE prec emax) IEEE_to_ASN.
Proof.
  unfold pass_guarantee.
  intros a.
  unfold is_convertible_IEEE.
  destruct (reasonable_float prec emax).
  - (* reasonable_float = true *)
    case a.
      (* B754_zero *)
        reflexivity.
      (* B754_infinity *)
        reflexivity.
      (* B754_nan *)
        reflexivity.
      (* B754_finite *)
        intros s m e B.
        unfold IEEE_to_ASN.
        case good_real_sumbool.
          (* good_real = true *)
            reflexivity.
          (* good_real = false *)
            intros H1 H2.
            rewrite -> H1 in H2.
            inversion H2.
  - (* reasonable_float = false *)
    intros H.
    inversion H.
Qed.

Lemma IEEE_ASN_roundtrip {prec emax : Z} (f : float prec emax):
  roundtrip
    IEEE_to_ASN
    (ASN_to_IEEE prec emax)
    (is_convertible_IEEE prec emax)
    (conv_pass_guarantee prec emax)
    (float_eqb_nan_t)
    f.
Proof.
  unfold roundtrip.
  unfold option_liftM2.
  unfold option_bind.
  destruct (IEEE_to_ASN f) eqn:ASN_f.
  - (* ASN_f = Some a *)
    intros H.

    destruct ASN_to_IEEE eqn:round_f.
    + (* Some b *)
      destruct f.
      * (* zero *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        admit.
      * (* infinity *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        admit.
      * (* nan *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        admit.
      * (* finite *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        admit.

    + (* None *)
      exfalso.
      admit.

  - (* ASN_f = None *)
    intros H.
    exfalso.
    generalize (conv_pass_guarantee prec emax).
    unfold pass_guarantee.
    intros H1.
    apply H1 in H. clear H1.
    rewrite -> ASN_f in H.
    inversion H.
Abort.