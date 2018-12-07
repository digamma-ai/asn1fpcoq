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
  Definition radix2bits (b : radix) : Z :=
    if Z.eqb b 2 then 0
    else if Z.eqb b 4 then 1
        else if Z.eqb b 8 then 2
              else if Z.eqb b 16 then 3
                  else 0.

  Definition bits2radix (b : Z) : radix :=
    if Z.eqb b 0 then radix2
    else if Z.eqb b 1 then radix4
        else if Z.eqb b 2 then radix8
              else if Z.eqb b 3 then radix16
                  else radix2.

  (* [ 8.5.7.1 ] *)
  Definition sign2bits (s : bool) : Z :=
    if s then 1 else 0.

  Definition bits2sign (s : Z) : bool :=
    if (Z.eqb s 1) then true else false.

  (* [ 8.5.7.5 ] *)
  Definition signif2bits (m : positive) : Z :=
    Zpos m.

  Definition bits2signif (m : Z) : positive :=
    Z.to_pos m.

  (* [ 8.5.7.4 ] *)
  Definition exp2bits (e_olen e : Z) : Z :=
    twos_comp_extended (8 * e_olen) e.

  Definition bits2exp (e_olen e : Z) : Z :=
    twos_comp_extended (8 * e_olen) e.

End Atomic.

Definition finite_BER_to_bitstring
            (s : bool) (b : radix) (f : Z) (m : positive) (e : Z) : option BER_bitstring :=
  let m := signif2bits m in
  let s := sign2bits s in
  let bb := radix2bits b in
  let e_olen := twos_olen e in let e := exp2bits e_olen e in
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

Definition BER_to_bitstring (f : BER_float) : option BER_bitstring :=
  match f with
  | BER_zero s => Some (if s then special nzero_b else special pzero_b)
  | BER_infinity s => Some (if s then special ninf_b else special pinf_b)
  | BER_nan => Some (special nan_b)
  | BER_finite s b ff m e _ => finite_BER_to_bitstring s b ff m e
  end.

Definition bitstring_to_BER (b : BER_bitstring) : option BER_float :=
  match b with
  | special val =>
    match classify_BER val with
    | Some pzero => Some (BER_zero false)
    | Some nzero => Some (BER_zero true)
    | Some pinf => Some (BER_infinity false)
    | Some ninf => Some (BER_infinity true)
    | Some nan => Some (BER_nan)
    | None => None
    end
  | short id co t s bb ff ee e m _ =>
    let s := (bits2sign s) in
    let b := (bits2radix bb) in
    let m := (bits2signif m) in
    let e := (bits2exp (ee + 1) e) in
    match valid_BER_sumbool b ff m e with
    | right _ => None
    | left V => Some (BER_finite s b ff m e V)
    end
  | long id co t s bb ff ee eo e m _ =>
    let s := (bits2sign s) in
    let b := (bits2radix bb) in
    let m := (bits2signif m) in
    let e := (bits2exp (eo) e) in
    match valid_BER_sumbool b ff m e with
    | right _ => None
    | left V => Some (BER_finite s b ff m e V)
    end
  end.