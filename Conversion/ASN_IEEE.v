Require Import ZArith Datatypes Sumbool Bool.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux Flocq.Core.FLX.
Require Import ASN.ASNDef IEEE.Aux Aux.Option Aux.StructTactics Aux.Tactics.

Definition Prec_gt_1 (prec : Z) := Z.gt prec 1.

(*
  if
    forward pass happens
  then
      backward pass happens
    and
      backward pass returns an element,
      equivalent to the starting one
*)
Definition roundtrip {A1 A2 B: Type}
           (f: A1 -> option B) (* forward pass *)
           (b: B -> option A2) (* backward pass *)
           (e: A1 -> A2 -> bool) (* equivalence on A *)
           (x: A1) (* value *)
  : Prop :=
    is_Some_b (f x) = true ->
    option_liftM2 e (Some x) (option_bind b (f x)) = Some true.

Definition valid_BER_sumbool (m : positive) (e : Z) (b : radix) :=
  sumbool_of_bool (valid_BER m e b).

Definition binary_bounded_sumbool (prec emax: Z) (m: positive) (e:Z) :=
  sumbool_of_bool (Binary.bounded prec emax m e).

Section Conversions_exact.

Variable prec emax : Z.
Context (prec_gt_1 : Prec_gt_1 prec).
Hypothesis Hmax : (prec < emax)%Z.
Let float := binary_float prec emax.

Let prec_gt_0 : Prec_gt_0 prec.
Proof.
  unfold Prec_gt_0.
  (*n = 0
        m = 1
              p = prec*)
  apply (Z.lt_trans 0 1 prec).
    (* 1 < 0 *)
      reflexivity.
    (* 1 < prec *)
      apply Z.gt_lt.
      apply prec_gt_1.
Qed.

Let def_NaN :
  nan_pl prec 1 = true.
Proof.
  unfold nan_pl. simpl.
  apply Z.ltb_lt, Z.gt_lt, prec_gt_1.
Qed.

(*
  for any "meaningful" float s*m*(2^e)
  return its ASN.1 BER representation if possible

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
Definition IEEE_to_BER_exact (f : float) : option BER_float :=
  match f with
       | B754_zero _ _ s => Some (BER_zero s)
       | B754_infinity _ _ s => Some (BER_infinity s)
       | B754_nan _ _ _ _ _ => Some (BER_nan)
       | B754_finite _ _ s m e _ =>
         match valid_BER_sumbool m e radix2 with
         | left G => Some (BER_finite s radix2 m e G)
         | right _ => None
         end
       end.

(* Indicator function on the supported subset of floats *)
Definition is_exact_convertible_IEEE (f : float) : bool :=
  match f with
    | B754_finite _ _ _ m e _ => valid_BER m e radix2
    | _ => true
  end.

(* Guarantees that for all supported float values forward pass does not generate an error *)
Theorem IEEE_BER_pass_guarantee :
  forall (f : float),
    is_exact_convertible_IEEE f = true ->
    is_Some_b (IEEE_to_BER_exact f) = true.
Proof.
  intros f.
  unfold is_exact_convertible_IEEE.
  unfold IEEE_to_BER_exact.
    case f.
      (* B754_zero *)
        reflexivity.
      (* B754_infinity *)
        reflexivity.
      (* B754_nan *)
        reflexivity.
      (* B754_finite *)
        intros s m e B.
        unfold IEEE_to_BER_exact.
        case valid_BER_sumbool.
          (* good_real = true *)
            intros GR1 GR2.
            reflexivity.
          (* good_real = false *)
            intros H1 H2.
            rewrite -> H1 in H2.
            inversion H2.
Qed.

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
Definition BER_to_IEEE_exact (r : BER_float) : option float :=
    match r with
    | BER_zero s => Some (B754_zero _ _ s)
    | BER_infinity s => Some (B754_infinity _ _ s)
    | BER_nan => Some (B754_nan _ _ true 1 def_NaN)
    | BER_finite s b m e x =>
      if Z.eqb (radix_val b) 2
      then match binary_bounded_sumbool prec emax m e with
           | left B => Some (B754_finite _ _ s m e B)
           | right _ => None
           end
      else None
    end.

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
Theorem IEEE_BER_roundtrip_exact (f : float):
  roundtrip
    IEEE_to_BER_exact
    (BER_to_IEEE_exact)
    (float_eqb_nan_t)
    f.
Proof.
  intros FPT.

  unfold float_eqb_nan_t, option_liftM2, option_bind,
  IEEE_to_BER_exact, BER_to_IEEE_exact, Bcompare in *.

  repeat break_match; try some_eq_none_inv; (repeat try some_inv); subst;
    try reflexivity; try true_eq_false_inv;
    try compare_nrefl; try check_contradiction.

  (* if initial conversion returns radix /= 2 *)
  inversion Heqb1.

  (* if initial conversion returns None *)
  inversion FPT.
Qed.

End Conversions_exact.



Section Conversions_rounded.

Variable prec emax : Z.
Context (prec_gt_1 : Prec_gt_1 prec).
Hypothesis Hmax : (prec < emax)%Z.
Let float := binary_float prec emax.

Variable target_prec target_emax : Z.
Context (target_prec_gt_1 : Prec_gt_1 target_prec).
Hypothesis target_Hmax : (target_prec < target_emax)%Z.
Let target_float := binary_float target_prec target_emax.

Let target_prec_gt_0 : Prec_gt_0 target_prec.
Proof.
  unfold Prec_gt_0.
  (*n = 0
        m = 1
              p = prec*)
  apply (Z.lt_trans 0 1 target_prec).
    (* 1 < 0 *)
      reflexivity.
    (* 1 < prec *)
      apply Z.gt_lt.
      apply target_prec_gt_1.
Qed.

(* 1 (the number) can always be the payload of a NaN *)
Let def_target_NaN :
  nan_pl target_prec 1 = true.
Proof.
  unfold nan_pl. simpl.
  apply Z.ltb_lt, Z.gt_lt, target_prec_gt_1.
Qed.

(*
  given a triple (s,m,e) standing for s*m*2^e,
  return a corresponding binary_float object in target form,
  correctly rounded in accordance with the specified rounding mode
*)
Let round_finite (rounding : mode) (s : bool) (m : positive) (e : Z) : target_float :=
  binary_normalize
    target_prec target_emax target_prec_gt_0 target_Hmax
    rounding
    (cond_Zopp s (Zpos m)) e s.

(*
  given a binary_float and a rounding mode
  convert it to target format, rounding if necessary

  NaN payload is set to 1 uncoditionally
*)
Definition IEEE_to_IEEE_round_reset_nan (rounding : mode) (f : float) : target_float :=
  match f with
    | B754_nan _ _ _ _ _ => B754_nan _ _ true 1 def_target_NaN
    | B754_infinity _ _ s => B754_infinity _ _ s
    | B754_zero _ _ s => B754_zero _ _ s
    | B754_finite _ _ s m e _ => round_finite rounding s m e
  end.

(*
  given a BER_float and a rounding mode,
  return a binary_float in target format,
  rounded if necessary
*)
Definition BER_to_IEEE_round (rounding : mode) (r : BER_float) : option (target_float) :=
    match r with
    | BER_zero s => Some (B754_zero _ _ s)
    | BER_infinity s => Some (B754_infinity _ _ s)
    | BER_nan => Some (B754_nan _ _ true 1 def_target_NaN)
    | BER_finite s b m e x =>
      if Z.eqb (radix_val b) 2
      then Some (round_finite rounding s m e)
      else None
    end.

(*
  for two binary_float`s in starting and target formats,
  check if the second is the result of
  converting (rounded accordingly) the first to target format
*)
Definition correctly_rounded_nan_t (rounding : mode) (f : float) (cf : target_float) :=
  float_eqb_nan_t
    (IEEE_to_IEEE_round_reset_nan rounding f)
    cf.

Theorem IEEE_BER_roundtrip_rounded (rounding : mode) (f : float) :
  roundtrip
    (IEEE_to_BER_exact prec emax)
    (BER_to_IEEE_round rounding)
    (correctly_rounded_nan_t rounding)
    f.
Admitted.


End Conversions_rounded.