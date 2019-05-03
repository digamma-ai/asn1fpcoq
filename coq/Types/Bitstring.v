Require Import ZArith.
Require Import ASN1FP.Types.ASN
               ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits ASN1FP.Aux.StructTactics ASN1FP.Aux.Tactics.

Open Scope Z.

(* TODO: consult the doc *)
Definition real_id_b := 9.

(*
 * only binary encoding is supported
 * [ 8.5.6 (a) ]
 *   NOTE: "SpecialRealValues" ([ 8.5.9 ]) are defined separately
 *)
Definition binary_bit := 1.

(*
 * "SpecialRealValues" as bit strings including all parts of the encoding
 * [ 8.5.9 ]
 *)
Definition pzero_b   := 2304.
Definition nzero_b   := 590147.
Definition pinf_b    := 590144.
Definition ninf_b    := 590145.
Definition nan_b     := 590146.

Inductive BER_special :=
| pzero
| nzero
| pinf
| ninf
| nan.

Definition special_eqb (s1 s2 : BER_special) : bool :=
  match s1, s2 with
  | pzero, pzero => true
  | nzero, nzero => true
  | pinf,  pinf => true
  | ninf,  ninf => true
  | nan,   nan => true
  | _, _ => false
  end.

Definition classify_BER (val : Z) : option BER_special :=
  if val =? pzero_b then Some pzero
  else if val =? nzero_b then Some nzero
    else if val =? pinf_b then Some pinf
      else if val =? ninf_b then Some ninf
        else if val =? nan_b then Some nan
           else None.

Definition bits_of_special (val : BER_special) : Z :=
  match val with
  | pzero => pzero_b
  | nzero => nzero_b
  | pinf => pinf_b
  | ninf => ninf_b
  | nan => nan_b
  end.

Definition valid_special (val : Z) : bool :=
  match (classify_BER val) with
  | Some _ => true
  | None   => false
  end.

(*
 * do the atomic parts constitute a valid BER-encoded real
 * in short form:
 *   id - identifier octet(s)  [ 8.1.2 ]
 *   co - length octet(s)      [ 8.1.3 ]
 *   t  - encoding type bit    [ 8.5.6 ]
 *   s  - sign bit             [ 8.5.7.1 ]
 *   bb - base bits            [ 8.5.7.2 ]
 *   ff - scaling factor bits  [ 8.5.7.3 ]
 *   ee - exponent format bits [ 8.5.7.4 ]
 *   e  - exponent bits        [ 8.5.7.4 ]
 *   m  - mantissa bits        [ 8.5.7.5 ]
 *)
Definition valid_short (id co t s bb ff ee e m : Z) : bool :=
     (id =? real_id_b)          (* identifier is "REAL" *)
  && (1 <=? co) && (co <=? 127) (* encoding is in short form *)
  && ((olen m) + ee + 2 <=? co) (* content fits in given space *)
  && (t =? 1)                   (* encoding is binary *)
  && (0 <=? s) && (s <=? 1 )    (* sign bit is well-formed *)
  && (0 <=? bb) && (bb <=? 3)   (* radix bit is well-formed *)
  && (0 <=? ff) && (ff <=? 3)   (* scaling factor is well-formed *)
  && (0 <=? ee) && (ee <=? 2)   (* exponent length is well-formed *)
  && ((olen e) <=? ee + 1)          (* exponent length is correct *)
  && (0 <=? e)                  (* exponent is non-negative
                                   (it is two's complement) *)
  && (1 <=? m).                 (* mantissa is positive *)

(*
 * do the atomic parts constitute a valid BER-encoded real
 * in long form:
 *   id - identifier octet(s)   [ 8.1.2 ]
 *   co - length octet(s)       [ 8.1.3 ]
 *   t  - encoding type bit     [ 8.5.6 ]
 *   s  - sign bit              [ 8.5.7.1 ]
 *   bb - base bits             [ 8.5.7.2 ]
 *   ff - scaling factor bits   [ 8.5.7.3 ]
 *   ee - exponent format bits  [ 8.5.7.4 ]
 *   eo - exponent length octet [ 8.5.7.4 (d) ]
 *   e  - exponent bits         [ 8.5.7.4 ]
 *   m  - mantissa bits         [ 8.5.7.5 ]
 *)
Definition valid_long (id co t s bb ff ee eo e m : Z) : bool :=
     (id =? real_id_b)          (* identifier is "REAL" *)
  && (1 <=? co) && (co <=? 127) (* encoding is in short form *)
  && ((olen m) + eo + 2 <=? co) (* content fits in given space *)
  && (t =? 1)                   (* encoding is binary *)
  && (0 <=? s) && (s <=? 1 )    (* sign bit is well-formed *)
  && (0 <=? bb) && (bb <=? 3)   (* radix bit is well-formed *)
  && (0 <=? ff) && (ff <=? 3)   (* scaling factor is well-formed *)
  && (ee =? 3)                  (* exponent length identifier is well-formed *)
  && (1 <=? eo) && (eo <=? 255) (* exponent length is well-formed *)
  && ((olen e) <=? eo)          (* exponent length is correct *)
  && (0 <=? e)                  (* exponent is non-negative
                                   (it is two's complement) *)
  && (1 <=? m).                 (* mantissa is positive *)

(*
 * a tuple containing all elementary parts of a BER-encoded real
 * the parts are final binary strings, which only need to be concatenated
 *)
Inductive BER_bitstring :=
  | special (val : BER_special)
  | short (id co t s bb ff ee e m : Z) :
      (valid_short id co t s bb ff ee e m) = true -> BER_bitstring
  | long  (id co t s bb ff ee eo e m : Z) :
      (valid_long id co t s bb ff ee eo e m) = true -> BER_bitstring.

(* TODO: simplify? *)
Definition BER_bitstring_eqb (b1 b2 : BER_bitstring) : bool :=
  match b1, b2 with
  | special val1, special val2 => special_eqb val1 val2
  | short id1 co1 t1 s1 bb1 ff1 ee1 e1 m1 _, short id2 co2 t2 s2 bb2 ff2 ee2 e2 m2 _ =>
         (id1 =? id2) && (co1 =? co2) && (t1 =? t2) && (s1 =? s2) && (bb1 =? bb2)
      && (ff1 =? ff2) && (ee1 =? ee2) && (e1 =? e2) && (m1 =? m2)
  | long id1 co1 t1 s1 bb1 ff1 ee1 eo1 e1 m1 _, long id2 co2 t2 s2 bb2 ff2 ee2 eo2 e2 m2 _ =>
         (id1 =? id2) && (co1 =? co2) && (t1  =?  t2) && (s1 =? s2) && (bb1 =? bb2)
      && (ff1 =? ff2) && (ee1 =? ee2) && (eo1 =? eo2) && (e1 =? e2) && (m1  =?  m2)
  | _, _ => false
  end.

Definition valid_short_sumbool (id co t s bb ff ee e m : Z) :=
  Sumbool.sumbool_of_bool (valid_short id co t s bb ff ee e m).

Definition valid_long_sumbool (id co t s bb ff ee eo e m : Z) :=
  Sumbool.sumbool_of_bool (valid_long id co t s bb ff ee eo e m).
