Require Import ZArith Datatypes Sumbool Bool.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.
Require Import ASNDef Aux.
Require Import StructTactics.

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
    (Z.gtb prec 1)
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

Definition roundtrip {A B: Type}
           (f: A -> option B) (* forward pass *)
           (b: B -> option A) (* backward pass *)
           (e: A -> A -> bool) (* equivalence on A *)
           (x: A) (* value *)
  : Prop :=
    is_Some_b (f x) = true ->
    option_liftM2 e (option_bind b (f x)) (Some x) = Some true.

(* This defines a subset of float values we support *)
Definition is_convertible_IEEE {prec emax : Z} (f : float prec emax) : bool :=
  if (reasonable_float prec emax)
  then match f with
       | B754_finite _ _ _ m e _ => good_real m e radix2
       | _ => true
       end
  else false.

(* Guarantees that for all supported float value forwaed pass does not generate an error *)
Theorem IEEE_ASN_pass_guarantee (prec emax : Z) :
  forall (a : float prec emax), (is_convertible_IEEE a = true -> is_Some_b (IEEE_to_ASN a) = true).
Proof.
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

Ltac some_none :=
  match goal with
  | [ H: Some _ = None |- _ ] => inversion H
  | [ H: None = Some _ |- _ ] => inversion H
  end.

Ltac true_is_false :=
  match goal with
  | [ H: true = false |- _ ] => inversion H
  | [ H: false = true |- _ ] => inversion H
  end.

Ltac some_inv :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H
  end.

(*
Ltac compare_inv :=
  match goal with
  | [ H: (?e ?= ?e)%Z = Lt ] => ....
  | [ H: (?e ?= ?e)%Z = Gt ] => ....
  end.
 *)

Theorem IEEE_ASN_roundtrip {prec emax : Z} (f : float prec emax):
  roundtrip
    IEEE_to_ASN
    (ASN_to_IEEE prec emax)
    (float_eqb_nan_t)
    f.
Proof.
  intros a.
  unfold float_eqb_nan_t, option_liftM2, option_bind, IEEE_to_ASN, ASN_to_IEEE, is_convertible_IEEE, Bcompare in *.
  repeat break_match; try some_none; try true_is_false; (repeat try some_inv); subst; try reflexivity.


  TODO




  unfold roundtrip.
  unfold option_liftM2.
  unfold option_bind.
  destruct (IEEE_to_ASN f) eqn:ASN_f.
  - (* f -> Some a *)
    intros H.
    destruct ASN_to_IEEE eqn:round_f.

    + (* f -> Some a -> Some b *)
      destruct f.

      * (* f = zero *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        destruct b.
          (* round_f = zero *)
            reflexivity.
          (* round_f = infinity *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.
          (* round_f = nan *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.
          (* round_f = finite *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.

      * (* f = infinity *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        destruct b.
          (* round_f = zero *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.
          (* round_f = infinity *)
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
                admit. (* trivial *)
              (* reasonable = false *)
                inversion round_f.
          (* round_f = nan *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.
          (* round_f = finite *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.

      * (* f = nan *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        destruct b.
          (* round_f = zero *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.
          (* round_f = infinity *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.
          (* round_f = nan *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
                admit.
              (* reasonable = false *)
                inversion round_f.

          (* round_f = finite *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            rewrite -> Some_elim in ASN_f.
            rewrite <- ASN_f in round_f.
            unfold ASN_to_IEEE in round_f.
            destruct reasonable_float_sumbool in round_f.
              (* reasonable = true *)
                inversion round_f.
              (* reasonable = false *)
                inversion round_f.

      * (* f = finite *)
        apply Some_elim.
        unfold float_eqb_nan_t.
        destruct b.
          (* round_f = zero *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            unfold is_convertible_IEEE in H.
            destruct good_real_sumbool.
              (* good_real = true *)
                inversion ASN_f.
                rewrite <- H1 in round_f.
                unfold ASN_to_IEEE in round_f.
                destruct binary_bounded_sumbool.
                  (* bounded = true *)
                    destruct reasonable_float_sumbool.
                      (* reasonable = true *)
                        inversion round_f.
                      (* reasonable = false *)
                        inversion round_f.
                   (* bounded = false *)
                        rewrite -> e0 in e2.
                        inversion e2.
              (* good_real = false *)
                inversion ASN_f.

          (* round_f = infinity *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            unfold is_convertible_IEEE in H.
            destruct good_real_sumbool.
              (* good_real = true *)
                inversion ASN_f.
                rewrite <- H1 in round_f.
                unfold ASN_to_IEEE in round_f.
                destruct binary_bounded_sumbool.
                  (* bounded = true *)
                    destruct reasonable_float_sumbool.
                      (* reasonable = true *)
                        inversion round_f.
                      (* reasonable = false *)
                        inversion round_f.
                   (* bounded = false *)
                        rewrite -> e0 in e2.
                        inversion e2.
              (* good_real = false *)
                inversion ASN_f.
          (* round_f = nan *)
            exfalso.
            unfold IEEE_to_ASN in ASN_f.
            unfold is_convertible_IEEE in H.
            destruct good_real_sumbool.
              (* good_real = true *)
                inversion ASN_f.
                rewrite <- H1 in round_f.
                unfold ASN_to_IEEE in round_f.
                destruct binary_bounded_sumbool.
                  (* bounded = true *)
                    destruct reasonable_float_sumbool.
                      (* reasonable = true *)
                        inversion round_f.
                      (* reasonable = false *)
                        inversion round_f.
                   (* bounded = false *)
                        rewrite -> e0 in e3.
                        inversion e3.
              (* good_real = false *)
                inversion ASN_f.
          (* round_f = finite *)
            unfold IEEE_to_ASN in ASN_f.
            unfold is_convertible_IEEE in H.
            destruct (reasonable_float_sumbool prec emax).
              (* reasonable_float = true *)
                rewrite -> e3 in H.
                destruct good_real_sumbool.
                  (* good_real = true *)
                    inversion ASN_f.
                    rewrite <- H1 in round_f.
                    unfold ASN_to_IEEE in round_f.
                    destruct reasonable_float_sumbool.
                      (* reasonable_float = true *)
                        destruct binary_bounded_sumbool.
                          (* binary_bounded = true *)
                            admit.
                          (* binary_bounded = false *)
                            rewrite -> e0 in e6.
                            inversion e6.
                      (* reasonable_float = false *)
                        rewrite -> e3 in e5.
                        inversion e5.
                  (* good_real = false *)
                    rewrite -> e4 in H.
                    inversion H.
              (* reasonable_float = false *)
                rewrite -> e3 in H.
                inversion H.


    + (* round_f = None *)
      exfalso.
      destruct f.
        (* f = zero *)
          simpl in ASN_f.
          inversion ASN_f.
          rewrite <- H1 in round_f.
          unfold ASN_to_IEEE in round_f.
          destruct reasonable_float_sumbool.
            (* reasonable = true *)
              inversion round_f.
            (* reasonable = false *) 
              unfold is_convertible_IEEE in H.
              rewrite -> e in H.
              inversion H.
       (* f = infinity *)
          simpl in ASN_f.
          inversion ASN_f.
          rewrite <- H1 in round_f.
          unfold ASN_to_IEEE in round_f.
          destruct reasonable_float_sumbool.
            (* reasonable = true *)
              inversion round_f.
            (* reasonable = false *) 
              unfold is_convertible_IEEE in H.
              rewrite -> e in H.
              inversion H.
       (* f = nan *)
          simpl in ASN_f.
          inversion ASN_f.
          rewrite <- H1 in round_f.
          unfold ASN_to_IEEE in round_f.
          destruct reasonable_float_sumbool.
            (* reasonable = true *)
              inversion round_f.
            (* reasonable = false *) 
              unfold is_convertible_IEEE in H.
              rewrite -> e0 in H.
              inversion H.
       (* f = finite *)
          simpl in ASN_f.
          destruct good_real_sumbool.
            (* good_real = true *)
              inversion ASN_f.
              rewrite <- H1 in round_f.
              unfold ASN_to_IEEE in round_f.
              destruct reasonable_float_sumbool.
                (* reasonable = true *)
                  destruct binary_bounded_sumbool.
                    (* bounded = false *)
                      inversion round_f.
                    (* bounded = true *)
                      rewrite -> e0 in e3.
                      inversion e3.
                (* reasonable = false *)
                unfold is_convertible_IEEE in H.
                rewrite -> e2 in H.
                inversion H.
            (* good_real = false *)
              inversion ASN_f.

  - (* ASN_f = None *)
    intros H.
    exfalso.
    generalize (IEEE_ASN_pass_guarantee prec emax).
    unfold pass_guarantee.
    intros H1.
    apply H1 in H. clear H1.
    rewrite -> ASN_f in H.
    inversion H.
Admitted.