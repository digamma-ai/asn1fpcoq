Require Import ZArith.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux.
Require Import ASNDef.

Variable prec emax : Z.

Lemma subset_IEEE_ASN (m : positive) (e : Z) :
  (Binary.bounded prec emax m e = true) -> (good_real m e radix2 = true).
Proof.
  intros H1.
  unfold Binary.bounded in H1.
  apply andb_prop in H1.
  inversion H1 as [H2 H3]. clear H1.
  unfold canonical_mantissa in H2.
  apply Zeq_bool_eq in H2.
  unfold FLT.FLT_exp in H2.
Abort.

(*
Definition IEEE_to_ASN (b : binary_float prec emax) :=
  match b with
  | B754_zero _ _ s => ASN_zero s
  | B754_infinity _ _ s => ASN_infinity s
  | B754_nan _ _ _ _ _ => ASN_nan
  | B754_finite _ _ s m e H => ASN_finite s m radix2 e (subset_IEEE_ASN m e H)
  end.

Theorem IEEE_to_ASN_inj  (x y : ASN.real) :
  IEEE_to_ASN x = IEEE_to_ASN y -> x = y.
*)