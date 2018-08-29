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

(*
Lemma roundtrip_if_some {prec emax : Z} (f : float prec emax) :
  let ASN_f := IEEE_to_ASN f in
  is_Some_b ASN_f = true ->
  (bin_bool_option_bind float_eqb_nan_t
                        (option_bind (ASN_to_IEEE prec emax) ASN_f) (Some f)) = true.
 *)


Definition roundtrip {A B: Type}
           (f: A -> option B)
           (b: B -> option A)
           (r: A -> bool) (* restriction on A for which roundtrip must work *)
           (R: forall (a:A), r a = true -> is_Some_b (f a) = true) (* forward pass guaranteed to work on restriced value *)
           (e: A -> A -> bool)
           (x: A): Prop
  :=
    option_liftM2 e (option_bind b (f x)) (Some x) = Some true.

Lemma roundtrip_if_some' {prec emax : Z} (f : float prec emax):
  roundtrip
    IEEE_to_ASN
    (ASN_to_IEEE prec emax)
    is_supported_float
    all_supported_convert_to_ASN_without_error
    (float_eqb_nan_t)
    f.
