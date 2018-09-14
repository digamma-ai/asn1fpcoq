Require Import ZArith Datatypes Sumbool Bool.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux Flocq.Core.FLX.
Require Import ASN.ASNDef Aux.Option Aux.StructTactics Aux.Tactics.


(* Variable prec emax : Z.                     *)
(* Context (prec1_gt_0_ : Prec_gt_0 prec).     *)
(* Let emin := (3 - emax - prec)%Z.            *)
(* Hypothesis Hmax : (prec < emax)%Z.          *)
(* Let binary_float := binary_float prec emax. *)

(*
  a meaningful binary_float format is that, for which

  - number of explicit significand bits is greater than 0
    (prec > 1) 
 *)
Definition meaningful_float (prec emax : Z) : bool :=
andb
    (Z.gtb prec 1)
    (Z.ltb prec emax).

Definition prec_gt_1 (prec : Z) : Prop := (prec > 1)%Z.
Definition prec_gt_0 (prec : Z) : Prop := (prec > 0)%Z.

(*
  any "meaningful" float has precision > 1
*)
Lemma meaningful_prec_gt_1 {prec emax : Z} :
  meaningful_float prec emax = true -> prec_gt_1 prec.
Proof.
  intros H.
  unfold meaningful_float in H.
  apply andb_prop in H. 
  destruct H as [H H1]. clear H1.
  apply Zgt_is_gt_bool.
  apply H.
Qed.

Lemma meaningful_prec_gt_0 {prec emax : Z} :
  meaningful_float prec emax = true -> Prec_gt_0 prec.
Admitted.
Lemma meaningful_hmax {prec emax : Z} :
  meaningful_float prec emax = true -> Z.lt prec emax.
Admitted.

(*
  for any meaningful precision, a NaN payload of 1 is encodable
*)
Fact def_NAN (prec : Z) (pc : prec_gt_1 prec) :
  nan_pl prec 1 = true.

  unfold nan_pl. simpl.
  apply Zlt_is_lt_bool.
  apply Z.gt_lt.
  apply pc.
Qed.

Definition valid_BER_sumbool (m : positive) (e : Z) (b : radix) :=
  sumbool_of_bool (valid_BER m e b).

Definition binary_bounded_sumbool (prec emax: Z) (m: positive) (e:Z) :=
  sumbool_of_bool (Binary.bounded prec emax m e).

Definition meaningful_float_sumbool (prec emax : Z) :=
  sumbool_of_bool (meaningful_float prec emax).

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
Definition IEEE_to_BER {prec emax: Z} (f : binary_float prec emax)
  : option BER_float :=
  if (meaningful_float prec emax)
  then match f with
       | B754_zero _ _ s => Some (BER_zero s)
       | B754_infinity _ _ s => Some (BER_infinity s)
       | B754_nan _ _ _ _ _ => Some (BER_nan)
       | B754_finite _ _ s m e _ =>
         match valid_BER_sumbool m e radix2 with
         | left G => Some (BER_finite s radix2 m e G)
         | right _ => None
         end
       end
  else None.

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
Definition BER_to_IEEE_exact (prec emax: Z) (r : BER_float)
  : option (binary_float prec emax) :=
  match meaningful_float_sumbool prec emax with
  | left R =>
    match r with
    | BER_zero s => Some (B754_zero prec emax s)
    | BER_infinity s => Some (B754_infinity prec emax s)
    | BER_nan => Some (B754_nan prec emax true 1 (def_NAN prec (meaningful_prec_gt_1 R)))
    | BER_finite s b m e x =>
      if Z.eqb (radix_val b) 2
      then match binary_bounded_sumbool prec emax m e with
           | left B => Some (B754_finite prec emax s m e B)
           | right _ => None
           end
      else None
    end
  | right _ => None
  end.

Definition BER_to_IEEE_round (prec emax: Z) (r : BER_float) (rounding : mode)
  : option (binary_float prec emax) :=
  match meaningful_float_sumbool prec emax with
  | left R =>
    match r with
    | BER_zero s => Some (B754_zero prec emax s)
    | BER_infinity s => Some (B754_infinity prec emax s)
    | BER_nan => Some (B754_nan prec emax true 1 (def_NAN prec (meaningful_prec_gt_1 R)))
    | BER_finite s b m e x =>
      if Z.eqb (radix_val b) 2
      then Some (binary_normalize prec emax (meaningful_prec_gt_0 R) (meaningful_hmax R) rounding (cond_Zopp s (Zpos m)) e s)
      else None
    end
  | right _ => None
  end.

(*
  eqivalence on floats, returning `true`
  for normal equality
  or for any two NaN values (NaN payloads not taken into account)
*)
Definition float_eqb_nan_t {prec emax : Z} (x y : binary_float prec emax) : bool :=
  match Bcompare prec emax x y with
  | Some Eq => true
  | None => true
  | _ => false
  end.


(*
Definition float_eqb_nan_t' {prec1 emax1 prec2 emax2 : Z} (x: float prec1 emax1) (y: float prec2 emax2): bool.
Proof.
  destruct (Z_eq_dec prec1 prec2), (Z_eq_dec emax1 emax2).
  -
    subst.
    exact (float_eqb_nan_t y x).
  - exact false.
  - exact false.
  - exact false.
Defined.
*)
Definition float_eqb_nan_t' {prec1 emax1 prec2 emax2 : Z} (x: binary_float prec1 emax1) (y: binary_float prec2 emax2): bool:=
  match Z.eq_dec prec1 prec2, Z.eq_dec emax1 emax2 with
  | left Ep, left Ee =>
    eq_rec_r (fun prec' : Z => binary_float prec' emax1 -> bool)
             (eq_rec_r (fun emax' : Z => binary_float prec2 emax' -> bool)
                       (float_eqb_nan_t y) Ee)
             Ep x
  | _, _ => false
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
Theorem IEEE_ASN_roundtrip {prec emax : Z} (f : binary_float prec emax):
  roundtrip
    IEEE_to_BER
    (BER_to_IEEE prec emax)
    (float_eqb_nan_t)
    f.
Proof.
  intros FPT.

  unfold float_eqb_nan_t, option_liftM2, option_bind,
  IEEE_to_BER, BER_to_IEEE, Bcompare in *.

  repeat break_match; try some_eq_none_inv; (repeat try some_inv); subst;
    try reflexivity; try true_eq_false_inv;
    try compare_nrefl; try check_contradiction.

  (* if initial conversion returns radix != 2 *)
  inversion Heqb1.

  (* if initial conversion does not work *)
  inversion FPT.
  inversion FPT.
Qed.

(* Indicator function on the subset of the supported float subset *)
Definition is_convertible_IEEE {prec emax : Z} (f : binary_float prec emax) : bool :=
  if (meaningful_float prec emax)
  then match f with
       | B754_finite _ _ _ m e _ => valid_BER m e radix2
       | _ => true
       end
  else false.

(* Guarantees that for all supported float value forward pass does not generate an error *)
Theorem IEEE_ASN_pass_guarantee (prec emax : Z) :
  forall (a : binary_float prec emax), (is_convertible_IEEE a = true -> is_Some_b (IEEE_to_BER a) = true).
Proof.
  intros a.
  unfold is_convertible_IEEE.
  unfold IEEE_to_BER.
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
        unfold IEEE_to_BER.
        case valid_BER_sumbool.
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
