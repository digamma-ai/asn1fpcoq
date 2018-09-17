Require Import ZArith.
Require Import Flocq.IEEE754.Binary.

(*
  eqivalence on floats of the same type, returning `true`
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
Definition float_eqb_nan_t' {p e tp te : Z}
           (x : binary_float p e)
           (y : binary_float tp te) : bool :=
(*
Proof.
  destruct (Z_eq_dec p tp), (Z_eq_dec e te).
  - subst.
    exact (float_eqb_nan_t y x).
  - exact false.
  - exact false.
  - exact false.
Defined.
*)
  match (Z_eq_dec p tp), (Z_eq_dec e te) with
  | left Ep, left Ee =>
    eq_rec_r (fun prec' : Z => binary_float prec' e -> bool)
             (eq_rec_r (fun emax' : Z => binary_float tp emax' -> bool)
                       (float_eqb_nan_t y) Ee)
             Ep x
  | _, _ => false
  end.
*)