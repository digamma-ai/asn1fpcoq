Require Import ZArith Datatypes Sumbool Bool.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.
Require Import ASN.ASNDef Aux.Option Aux.StructTactics Aux.Tactics.

Notation float := Binary.binary_float.

(*
  a meaningful binary_float format is that, for which

  - number of explicit significand bits is greater than 0
    (prec > 1) 
 *)
Definition meaningful_float (prec emax : Z) : bool :=
(*andb*)
    (Z.gtb prec 1)
    (*(Z.gtb emax prec)*).

Definition prec_gt_1 (prec : Z) : Prop := (prec > 1)%Z.

(*
  any "meaningful" float has precision > 1
*)
Lemma meaningful_prec_gt_1 {prec emax : Z} :
  meaningful_float prec emax = true -> prec_gt_1 prec.
Proof.
  intros H.
  unfold meaningful_float in H.
  (*apply andb_prop in H. 
  destruct H as [H H1]. clear H1.*)
  apply Zgt_is_gt_bool.
  apply H.
Qed.

(*
  for any meaningful precision, a NaN payload of 1 is encodable
*)
Fact def_NAN (prec : Z) (pc : prec_gt_1 prec) :
  nan_pl prec 1 = true.
Proof.
  unfold nan_pl. simpl.
  apply Zlt_is_lt_bool.
  apply Z.gt_lt.
  apply pc.
Qed.

Definition good_real_sumbool (m : positive) (e : Z) (b : radix) :=
  sumbool_of_bool (good_real m e b).

Definition binary_bounded_sumbool (prec emax: Z) (m: positive) (e:Z) :=
  sumbool_of_bool (Binary.bounded prec emax m e).

Definition meaningful_float_sumbool (prec emax : Z) :=
  sumbool_of_bool (meaningful_float prec emax).

(*
  for any "meaningful" float s*m*(2^e)
  return its ASN.1 representation if possible

  NOTE:
  1) ASN.1 representation is set to have radix = 2
     (directly representing the IEEE-754 radix)
  2) Only direct conversion is attempted
     (i.e. (s,m,e) -> (s,m,e)
      not  (s,m,e) -> (s,m*2,e-1))
  3) If the float is not "meaningful"
     or direct conversion is impossible,
     `None` is returned
  4) After the conversion, IEEE-754 NaN payload is lost,
     as it is not supported by the ASN.1 standard
*)
Definition IEEE_to_ASN {prec emax: Z} (f : float prec emax)
  : option ASN_real :=
  if (meaningful_float prec emax)
  then match f with
       | B754_zero _ _ s => Some (ASN_zero s)
       | B754_infinity _ _ s => Some (ASN_infinity s)
       | B754_nan _ _ _ _ _ => Some (ASN_nan)
       | B754_finite _ _ s m e _ =>
         match good_real_sumbool m e radix2 with
         | left G => Some (ASN_finite s radix2 m e G)
         | right _ => None
         end
       end
  else None.

                                                                                (* !!!TODO!!! *)
                                                      (* ASN radix>2 is converted into radix2 *)

(*
  for any "meaningful" `float prec emax` format
  and any ASN.1 real number s*m*(b^e)
  return the number's representation in the given format if possible

  NOTE:
  1) Only direct conversion is attempted
     (i.e. (s,m,e) -> (s,m,e)
      not  (s,m,e) -> (s,m*2,e-1))
  2) If the float is not "meaningful"
     or direct conversion is impossible,
     `None` is returned
  3) If the ASN encoding is a NaN,
     float's NaN payload is set to 0
     (meaning 1, if implicit significand bit is included)
*)
Definition ASN_to_IEEE (prec emax: Z) (r : ASN_real)
  : option (float prec emax) :=
  match meaningful_float_sumbool prec emax with
  | left R =>
    match r with
    | ASN_zero s => Some (B754_zero prec emax s)
    | ASN_infinity s => Some (B754_infinity prec emax s)
    | ASN_nan => Some (B754_nan prec emax true 1 (def_NAN prec (meaningful_prec_gt_1 R)))
    | ASN_finite s b m e x =>
      match binary_bounded_sumbool prec emax m e with
      | left B => Some (B754_finite prec emax s m e B)
      | right _ => None
      end
    end
  | right _ => None
  end.

(*
  eqivalence on floats, returning `true`
  for normal equality
  or for any two NaN values (NaN payloads not taken into account)
*)
Definition float_eqb_nan_t {prec emax : Z} (x y : float prec emax) : bool :=
  match Bcompare prec emax x y with
  | Some Eq => true
  | None => true
  | _ => false
  end.

(*
    f    b
  A -> B -> A

  if
    forward pass happens
  then
      backward pass happens
    and
      backward pass returns an element,
      equivalent to the starting one
*)
Definition roundtrip {A B: Type}
           (f: A -> option B) (* forward pass *)
           (b: B -> option A) (* backward pass *)
           (e: A -> A -> bool) (* equivalence on A *)
           (x: A) (* value *)
  : Prop :=
    is_Some_b (f x) = true ->
    option_liftM2 e (option_bind b (f x)) (Some x) = Some true.

(* Indicator function on the subset of the supported float subset *)
Definition is_convertible_IEEE {prec emax : Z} (f : float prec emax) : bool :=
  if (meaningful_float prec emax)
  then match f with
       | B754_finite _ _ _ m e _ => good_real m e radix2
       | _ => true
       end
  else false.

(* Guarantees that for all supported float value forward pass does not generate an error *)
Theorem IEEE_ASN_pass_guarantee (prec emax : Z) :
  forall (a : float prec emax), (is_convertible_IEEE a = true -> is_Some_b (IEEE_to_ASN a) = true).
Proof.
  intros a.
  unfold is_convertible_IEEE.
  unfold IEEE_to_ASN.
  destruct (meaningful_float prec emax) eqn:MF.
  - (* meaningful_float = true *)
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
            intros GR1 GR2.
            reflexivity.
          (* good_real = false *)
            intros H1 H2.
            rewrite -> H1 in H2.
            inversion H2.
  - (* meaningful_float = false *)
    intros H.
    inversion H.
Qed.


(*
  roundtrip statement for IEEE->ASN->IEEE conversion
  (see `roundtrip`)

  if
    IEEE->ASN happens
  then
      ASN->IEEE happens
    and
      yields en element, equivalent to
      the starting one
*)
Theorem IEEE_ASN_roundtrip {prec emax : Z} (f : float prec emax):
  roundtrip
    IEEE_to_ASN
    (ASN_to_IEEE prec emax)
    (float_eqb_nan_t)
    f.
Proof.
  intros FPT.

  unfold float_eqb_nan_t, option_liftM2, option_bind,
  IEEE_to_ASN, ASN_to_IEEE, Bcompare in *.

  repeat break_match; try some_eq_none_inv; (repeat try some_inv); subst;
    try reflexivity; try true_eq_false_inv;
    try compare_nrefl; try check_contradiction.

  (* if initial conversion does not work *)
  inversion FPT.
  inversion FPT.
Qed.