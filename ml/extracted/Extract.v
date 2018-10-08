Require ASN1FP.Conversion.ASN_IEEE.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language Ocaml.
Extraction Blacklist String List Nat.

Set Extraction AccessOpaque.

(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlIntConv.
Extraction Library BinInt.

Recursive Extraction Library ASN_IEEE.
