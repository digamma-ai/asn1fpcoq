Require Import ZArith.
Require Import Flocq.IEEE754.Binary.

(*
 *  eqivalence on floats of the same type, returning `true`
 *  for normal equality
 *  or for any two NaN values (NaN payloads not taken into account)
 *)
Definition float_eqb_nan_t {prec emax : Z} (x y : binary_float prec emax) : bool :=
  match Bcompare prec emax x y with
  | Some Eq => true
  | None => true
  | _ => false
  end.

Definition binary_bounded_sumbool (prec emax : Z) (m : positive) (e : Z) :=
  Sumbool.sumbool_of_bool (Binary.bounded prec emax m e).