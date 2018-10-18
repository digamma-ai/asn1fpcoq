Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Conversion.Bitstring_Bits.Def.

Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
  := Basics.compose Some.

Theorem bitsrting_bits_roundtrip (b : BER_bitstring) :
  roundtrip_option
      BER_bitstring Z BER_bitstring
      (Some_ize bitstring_to_bits)
      bits_to_bitstring
      BER_bitstring_eqb
      b.
Admitted.
