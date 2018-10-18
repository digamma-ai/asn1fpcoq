Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Conversion.Bitstring_Bits.Def.

Theorem bitsrting_bits_roundtrip (b : BER_bitstring) :
    bool_het_inverse
      BER_bitstring Z BER_bitstring
      bitstring_to_bits
      bits_to_bitstring
      BER_bitstring_eqb
      b.
Admitted.
