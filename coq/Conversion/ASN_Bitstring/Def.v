Require Import ZArith.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Bits ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.

Require Import Flocq.Core.Zaux.

Open Scope Z.

Section Atomic.

  (*
   * functions converting individual meaningful parts of a BER-encoded real
   * to their corresponding binary strings
   *)

  (* [ 8.5.7.2 ] *)
  Definition bits_of_radix (b : radix) : Z :=
    if Z.eqb b 2 then 0
    else if Z.eqb b 4 then 1
        else if Z.eqb b 8 then 2
              else if Z.eqb b 16 then 3
                  else 0.

  Definition radix_of_bits (b : Z) : radix :=
    if Z.eqb b 0 then radix2
    else if Z.eqb b 1 then radix4
        else if Z.eqb b 2 then radix8
              else if Z.eqb b 3 then radix16
                  else radix2.

  (* [ 8.5.7.1 ] *)
  Definition bits_of_sign (s : bool) : Z :=
    if s then 1 else 0.

  Definition sign_of_bits (s : Z) : bool :=
    if (Z.eqb s 1) then true else false.

  (* [ 8.5.7.5 ] *)
  Definition bits_of_signif (m : positive) : Z :=
    Zpos m.

  Definition signif_of_bits (m : Z) : positive :=
    Z.to_pos m.

  (* [ 8.5.7.4 ] *)
  Definition bits_of_exp (e_olen e : Z) : Z :=
    twos_comp_extended (8 * e_olen) e.

  Definition exp_of_bits (e_olen e : Z) : Z :=
    twos_comp_extended (8 * e_olen) e.

End Atomic.

Definition bitstring_of_finite_BER
            (b : radix) (f : Z) (s : bool) (m : positive) (e : Z) : option BER_bitstring :=
  let m := bits_of_signif m in
  let s := bits_of_sign s in
  let bb := bits_of_radix b in
  let e_olen := twos_olen e in let e := bits_of_exp e_olen e in
    if Z.ltb (e_olen) 4
    then
      match (valid_short_sumbool real_id_b (e_olen + olen m + 1) binary_bit s bb f (e_olen - 1) e m) with
      | right _ => None
      | left V => Some (short real_id_b (e_olen + olen m + 1) binary_bit s bb f (e_olen - 1) e m V)
      end
    else
      match (valid_long_sumbool real_id_b (e_olen + olen m + 2) binary_bit s bb f 3 e_olen e m) with
          | right _ => None
          | left V => Some (long real_id_b (e_olen + olen m + 2) binary_bit s bb f 3 e_olen e m V)
      end.

Definition bitstring_of_BER (f : BER_float) : option BER_bitstring :=
  match f with
  | BER_zero s => Some (if s then special nzero else special pzero)
  | BER_infinity s => Some (if s then special ninf else special pinf)
  | BER_nan => Some (special nan)
  | BER_finite s b ff m e _ => bitstring_of_finite_BER s b ff m e
  end.

Definition BER_of_bitstring (b : BER_bitstring) : option BER_float :=
  match b with
  | special val =>
    match val with
    | pzero => Some (BER_zero false)
    | nzero => Some (BER_zero true)
    | pinf => Some (BER_infinity false)
    | ninf => Some (BER_infinity true)
    | nan => Some (BER_nan)
    end
  | short id co t s bb ff ee e m _ =>
    let s := (sign_of_bits s) in
    let b := (radix_of_bits bb) in
    let m := (signif_of_bits m) in
    let e := (exp_of_bits (ee + 1) e) in
    match valid_BER_sumbool b ff m e with
    | right _ => None
    | left V => Some (BER_finite b ff s m e V)
    end
  | long id co t s bb ff ee eo e m _ =>
    let s := (sign_of_bits s) in
    let b := (radix_of_bits bb) in
    let m := (signif_of_bits m) in
    let e := (exp_of_bits (eo) e) in
    match valid_BER_sumbool b ff m e with
    | right _ => None
    | left V => Some (BER_finite b ff s m e V)
    end
  end.