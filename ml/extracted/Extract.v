Require ASN1FP.Conversion.ASNBin.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
(* Require ExtrOcamlBigIntConv. *)

Extraction Language Ocaml.
Extraction Blacklist String List Nat.

Set Extraction AccessOpaque.

(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

(* Extraction Library ExtrOcamlBigIntConv. *)

Recursive Extraction Library ASNBin.
