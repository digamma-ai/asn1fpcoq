Require ASN1FP.Conversion.Full.Extracted.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlZBigInt.
Require ExtrOcamlBigIntConv.

Extraction Language Ocaml.
Extraction Blacklist String List Nat.

Set Extraction AccessOpaque.

Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".

(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlBasic.
Extraction Library ExtrOcamlNatBigInt.
Extraction Library ExtrOcamlZBigInt.


Recursive Extraction Library Extracted.
