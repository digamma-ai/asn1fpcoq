Require ASN1FP.Conversion.FullBin.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlZBigInt.
Require ExtrOcamlBigIntConv.

Extraction Language Ocaml.
Extraction Blacklist String List Nat.

Set Extraction AccessOpaque.

(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlBasic.
Extraction Library ExtrOcamlNatBigInt.
Extraction Library ExtrOcamlZBigInt.

Recursive Extraction Library FullBin.
