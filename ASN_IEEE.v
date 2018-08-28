Require Import ZArith Datatypes Sumbool Bool.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.
Require Import ASNDef.

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

Fact def_NAN (prec : Z) : nan_pl prec 1 = true.
Admitted.

Definition ASN_to_IEEE (prec emax: Z) (r : ASN_real)
  : option (float prec emax) :=
    match r with
    | ASN_zero s => Some (B754_zero prec emax s)
    | ASN_infinity s => Some (B754_infinity prec emax s)
    | ASN_nan => Some (B754_nan prec emax true 1 (def_NAN prec))
    | ASN_finite s b m e x =>
      match binary_bounded_sumbool prec emax m e with
      | left B => Some (B754_finite prec emax s m e B)
      | right _ => None
      end
    end.

Definition option_bind
           {A B: Type} (f: A -> option B) : (option A -> option B) :=
  fun oa => match oa with
         | Some a => f a
         | None => None
         end.

Definition meaningful_float_eqb {prec emax : Z} (x y : float prec emax) :=
  match Bcompare prec emax x y with
  | Some Eq => true
  | None => true
  | _ => false
  end.
    
Definition option_float_eq {prec emax: Z}
           (a b : option (float prec emax)): bool :=
  match a,b with
  | None, None => true
  | Some a, Some b => meaningful_float_eqb a b
  | _ , _ => false
  end.

Lemma roundtrip {prec emax: Z} (f : float prec emax):
  option_float_eq
    (option_bind
       (ASN_to_IEEE prec emax)
       (IEEE_to_ASN f))
    (Some f) = true.
Admitted.