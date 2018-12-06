Require Import ZArith.
Require Import ASN1FP.Types.ASNDef
               ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits ASN1FP.Aux.StructTactics ASN1FP.Aux.Tactics.

Require Import Template.All Switch.Switch Strings.String Lists.List.

Import ListNotations.

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

Run TemplateProgram
  (mkSwitch Z Z.eqb
    [ (pzero_b, "pzero") ;
      (nzero_b, "nzero") ;
      (pinf_b,   "pinf") ;
      (ninf_b,   "ninf") ;
      (nan_b,     "nan") ]
    "BER_specials" "classify_BER"
  ).

Definition valid_special (val : Z) : bool :=
  match (classify_BER val) with
  | Some _ => true
  | None   => false
  end.

(*
 * can [co] be classified as a
 * content length octet in short form
 *)
Definition correct_short_co (co e_olen m_olen : Z) : bool :=
  ((e_olen + m_olen) <? co) && (co <? 128).

(*
 * do the atomic parts constitute a valid BER-encoded real
 * in short form:
 *   id - identifier octet(s) [ 8.1.2 ]
 *   co - length octet(s) [ 8.1.3 ]
 *   t  - encoding type bit [ 8.5.6 ]
 *   s  - sign bit [ 8.5.7.1 ]
 *   bb - base bits [ 8.5.7.2 ]
 *   ff - scaling factor bits [ 8.5.7.3 ]
 *   ee - exponent format bits [ 8.5.7.4 ]
 *   e  - exponent bits [ 8.5.7.4 ]
 *   m  - mantissa bits [ 8.5.7.5 ]
 *)
Definition valid_short (id co t s bb ff ee e m : Z) : bool :=
     (Z.eqb id real_id_b)                  (* identifier is "REAL" *) (* TODO *)
  && (correct_short_co co (ee+1) (olen m)) (* encoding length is correct *)
  && (Z.eqb t 1)                           (* encoding is binary *)
  && (Z.ltb (-1)  s) && (Z.ltb  s 2)       (* sign bit is well-formed *)
  && (Z.ltb (-1) bb) && (Z.ltb bb 4)       (* radix bit is well-formed *)
  && (Z.ltb (-1) ff) && (Z.ltb ff 4)       (* scaling factor is well-formed *)
  && (Z.ltb (-1) ee) && (Z.ltb ee 3)       (* exponent length is well-formed *)
  && (Z.ltb (olen e) (ee + 2))             (* exponent length is correct *)
  && (Z.ltb (-1) e)                        (* exponent is non-negative *)
                                           (* (it is two's complement) *)
  && (Z.ltb 0 m).                          (* mantissa is positive *)

Definition correct_long_co (co e_olen m_olen : Z) : bool :=
  ((e_olen + m_olen + 1) <? co) && (co <? 128).

(*
 * do the atomic parts constitute a valid BER-encoded real
 * in long form:
 *   id - identifier octet(s) [ 8.1.2 ]
 *   co - length octet(s) [ 8.1.3 ]
 *   t  - encoding type bit [ 8.5.6 ]
 *   s  - sign bit [ 8.5.7.1 ]
 *   bb - base bits [ 8.5.7.2 ]
 *   ff - scaling factor bits [ 8.5.7.3 ]
 *   ee - exponent format bits [ 8.5.7.4 ]
 *   eo - exponent length octet [ 8.5.7.4 (d) ]
 *   e  - exponent bits [ 8.5.7.4 ]
 *   m  - mantissa bits [ 8.5.7.5 ]
 *)
Definition valid_long (id co t s bb ff ee eo e m : Z) : bool :=
     (Z.eqb id real_id_b)              (* identifier is "REAL" *)
  && (correct_long_co co eo (olen m))  (* encoding length is correct *)
  && (Z.eqb t 1)                       (* encoding is binary *)
  && (Z.ltb (-1)  s) && (Z.ltb  s 2)   (* sign bit is well-formed *)
  && (Z.ltb (-1) bb) && (Z.ltb bb 4)   (* radix bit is well-formed *)
  && (Z.ltb (-1) ff) && (Z.ltb ff 4)   (* scaling factor is well-formed *)
  && (Z.eqb ee 3)                      (* exponent is in long form *)
  && (Z.ltb (-1) eo) && (Z.ltb eo 256) (* exponent length is well-formed *)
  && (Z.ltb (olen e) (eo + 1))         (* exponent length is correct *)
  && (Z.ltb (-1) e)                    (* exponent is non-negative *)
                                       (* (it is two's complement) *)
  && (Z.ltb 0 m).                      (* mantissa is positive *)

Inductive BER_bitstring :=
  | special   (val : Z)
  | short (id co t s bb ff ee e m : Z) :
      (valid_short id co t s bb ff ee e m) = true -> BER_bitstring
  | long  (id co t s bb ff ee eo e m : Z) :
      (valid_long id co t s bb ff ee eo e m) = true -> BER_bitstring.

(* TODO: simplify? *)
Definition BER_bitstring_eqb (b1 b2 : BER_bitstring) : bool :=
  match b1, b2 with
  | special val1, special val2 => Z.eqb val1 val2
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

(* Definition correct_bitstring (b : BER_bitstring) : bool := *)
(*   match b with *)
(*   | special val => (valid_special val) *)
(*   | short id co t s bb ff ee    e m => (valid_short id co t s bb ff ee    e m) *)
(*   | long  id co t s bb ff ee eo e m => (valid_long  id co t s bb ff ee eo e m) *)
(*   end. *)
