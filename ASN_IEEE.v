Require Import ZArith Datatypes.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.
Require Import ASNDef.

Inductive convertible_IEEE :=
  | Bin32 (f : binary32)
  | Bin64 (f : binary64).

Lemma bin32_finite_convertible (m : positive) (e : Z) :
  Binary.bounded 24 128 m e = true -> good_real m e radix2 = true.
Admitted.

Lemma bin64_finite_convertible (m : positive) (e : Z) :
  Binary.bounded 53 1024 m e = true -> good_real m e radix2 = true.
Admitted.

Definition IEEE_to_ASN (f : convertible_IEEE) : ASN_real :=
  match f with
  | Bin32 f32 => match f32 with
              | B754_zero _ _ s => ASN_zero s
              | B754_infinity _ _ s => ASN_infinity s
              | B754_nan _ _ _ _ _ => ASN_nan
              | B754_finite _ _ s m e H =>
                ASN_finite s radix2 m e (bin32_finite_convertible m e H)
              end
  | Bin64 f64 => match f64 with
              | B754_zero _ _ s => ASN_zero s
              | B754_infinity _ _ s => ASN_infinity s
              | B754_nan _ _ _ _ _ => ASN_nan
              | B754_finite _ _ s m e H =>
                ASN_finite s radix2 m e (bin64_finite_convertible m e H)
              end
  end.

Definition convertible_ASN : ASN_real -> bool.
Admitted.

Definition ASN_to_IEEE (r : ASN_real) :
  convertible_ASN r = true -> convertible_IEEE.
Admitted.

Lemma IEEE_to_ASN_reversible (f : convertible_IEEE) :
  convertible_ASN (IEEE_to_ASN f) = true.
Admitted.

Lemma round_trip (f : convertible_IEEE) :
  ASN_to_IEEE (IEEE_to_ASN f) (IEEE_to_ASN_reversible f) = f.
Admitted.