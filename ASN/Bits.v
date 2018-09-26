Require Import ZArith Zdigits Datatypes.
Require Import ASN.ASNDef ASN.ASNCalc Aux.Option Aux.Bits Conversion.ASN_IEEE.
Require Import Program.Basics.
Require Import Flocq.Core.Zaux.

Let BER_REAL_IDENTIFIER := 9%Z.

Section BER_atomic.

  Definition BER_radix2Z (b : radix) : Z :=
    (Z.log2 b) - 1.

  Definition BER_Z2radix (b : Z) : radix :=
    if (b =? 0)%Z
    then radix2
    else if (b =? 1)%Z
         then radix4
         else if (b =? 2)%Z
              then radix8
              else if (b =? 4)%Z
                   then radix16
                   else radix2.

  Definition BER_sign2Z (s : bool) : Z :=
    if s then 1 else 0.

  Definition BER_Z2sign (s : Z) : bool :=
    if (s =? 1)%Z then true else false.

  (* TODO: two's complement*)
  Definition BER_exp2Z (e : Z) : Z :=
    e.

  Definition BER_Z2exp (e : Z) : Z :=
    e.

End BER_atomic.


Section BER_encoding.

  Infix "+o+" := join_octets (at level 100, right associativity).

  (*
    given the three main blocks of any BER encoding,
    create the BER bit string
  *)
  Definition join_BER_bits (id len content : Z) : Z :=
    id +o+ len +o+ content.

  (*
    given the content block of a BER real encoding,
    create the full bit string
    (add indentifier and inferred content length)
  *)
  Let make_BER_real_bits (content : Z) : Z :=
    join_BER_bits BER_REAL_IDENTIFIER (Zoctets content) content.


  Let BER_PLUS_ZERO_BITS := (* 8.1.3.4 : length octet; 8.5.2 : content octet*)
    join_octets BER_REAL_IDENTIFIER 0.
  Let BER_MINUS_ZERO_BITS :=
    make_BER_real_bits 131.
  Let BER_PLUS_INFINITY_BITS :=
    make_BER_real_bits 128.
  Let BER_MINUS_INFINITY_BITS :=
    make_BER_real_bits 129.
  Let BER_NOT_A_NUMBER_BITS :=
    make_BER_real_bits 130.

  Inductive REAL_SPECIAL_VALUES :=
  | BER_PLUS_ZERO
  | BER_MINUS_ZERO
  | BER_PLUS_INFINITY
  | BER_MINUS_INFINITY
  | BER_NOT_A_NUMBER
  | BER_FINITE.

  Definition classify_BER_float_bits (b : Z) : REAL_SPECIAL_VALUES :=
    if Z.eq_dec b BER_PLUS_ZERO_BITS
    then BER_PLUS_ZERO
    else if Z.eq_dec b BER_MINUS_ZERO_BITS
        then BER_MINUS_ZERO
        else if Z.eq_dec b BER_PLUS_INFINITY_BITS
              then BER_PLUS_INFINITY
                    else if Z.eq_dec b BER_MINUS_INFINITY_BITS
                          then BER_MINUS_INFINITY
                          else if Z.eq_dec b BER_NOT_A_NUMBER_BITS
                              then BER_NOT_A_NUMBER
                              else BER_FINITE.

  Definition BER_binary_real_descriptor
             (sign radix scaling_factor exp_octets : Z) : Z :=
    let bin_sign               := join_bits 1 sign 1 in
    let bin_sign_radix         := join_bits bin_sign radix 2 in
    let bin_sign_radix_scaling := join_bits bin_sign_radix scaling_factor 2 in
    join_bits bin_sign_radix_scaling exp_octets 2.

  (* TODO: two's complement *)
  (* TODO: [8.5.7.4] *)
  (*
    given the sign, radix, mantissa and exponent of a BER float
    generate the content block of that float
  *)
  Definition make_BER_finite_real_content_no_scl (s : bool) (b : radix) (m : positive) (e : Z) :=
    let Zm := Zpos m in
    let e_octets := Zoctets e in
    let twos_e := Z.of_nat (octet_twos_complement e) in
    let long_exp := (Z.gtb e_octets 3) in
    let descriptor := if long_exp
                      then BER_binary_real_descriptor (bit_value s) (BER_radix2Z b) 0 3
                      else BER_binary_real_descriptor (bit_value s) (BER_radix2Z b) 0 (e_octets-1)
    in
    if long_exp
    then descriptor +o+ e_octets +o+ twos_e +o+ Zm
    else descriptor +o+ twos_e +o+ Zm.

  (* TODO: [8.5.7.4] *)
  (* encoding a BER float as a bit-string *)
  Definition bits_of_BER (f : BER_float) : Z :=
    match f with
    | BER_zero s => if s then BER_MINUS_ZERO_BITS else BER_PLUS_ZERO_BITS
    | BER_infinity s => if s then BER_MINUS_INFINITY_BITS else BER_PLUS_INFINITY_BITS
    | BER_nan => BER_NOT_A_NUMBER_BITS
    | BER_finite s b m e _ => make_BER_real_bits
                                (make_BER_finite_real_content_no_scl s b m e)
    end.

  Example short_BER_ex1 :
    make_BER_real_bits
      (make_BER_finite_real_content_no_scl false radix2 532 (- 773)) = 2539330643624468%Z.
  Proof. reflexivity. Qed.

End BER_encoding.






Section BER_decoding.

  Definition split_short_BER (b : Z) : Z * Z * Z :=
    let '(id, len_content) := split_octets_by_fst b 1 in
    let '(len, content) := split_octets_by_fst len_content 1 in
    (id, len, content).

  Definition split_BER_real_descriptor (b : Z) : Z * Z * Z * Z * Z :=
    let '(tsbbff, ee) := split_bits_by_snd b 2 in
    let '(tsbb, ff)   := split_bits_by_snd tsbbff 2 in
    let '(ts, bb)     := split_bits_by_snd tsbb 2 in
    let '(t, s)       := split_bits_by_snd ts 1 in
    (t, s, bb, ff, ee).

  Definition split_BER_finite_real_content (b : Z) :=
    let '(descriptor, content) := split_octets_by_fst b 1 in
    let '(t, s, bb, ff, ee) := split_BER_real_descriptor descriptor in
    if (Z.eqb ee 3)
    then let '(elength, exp_significand) := split_octets_by_fst 1 content in
         let '(exp, significand) := split_octets_by_fst exp_significand elength in
         (t, s, bb, ff, ee, elength, exp, significand)
    else let '(exp, significand) := split_octets_by_fst content (ee + 1) in
         (t, s, bb, ff, ee, (ee + 1)%Z, exp, significand).

  (* TODO: [8.5.7.4] *)
  (* decoding a bit string to a BER float *)
  Definition BER_of_bits (b : Z) : option BER_float :=
    let '(id, len, content) := split_short_BER b in
    let '(t, s, bb, ff, ee, elength, exp, significand) := split_BER_finite_real_content content in
    let significand := Z.to_pos significand in
    let b := BER_Z2radix bb in
    let exp := BER_Z2exp exp in

    match classify_BER_float_bits b with
    | BER_PLUS_ZERO => Some (BER_zero false)
    | BER_MINUS_ZERO => Some (BER_zero true)
    | BER_PLUS_INFINITY => Some (BER_infinity false)
    | BER_MINUS_INFINITY => Some (BER_infinity true)
    | BER_NOT_A_NUMBER => Some BER_nan
    | BER_FINITE =>
      if ((Z.eqb id 9)
          &&
          (Z.ltb len 128)
          &&
          (Z.eqb (Zoctets content) len)
          &&
          (Z.eqb t 1)
          &&
          (((Z.eqb ee 3) && (Z.gtb elength 0) && (Z.ltb elength 256))
            ||
            ((Z.ltb ee 3) && (Z.eqb elength (ee+1))))
          &&
          (Z.eqb (Zoctets exp) elength))%bool
      then match valid_BER_sumbool significand exp b with
           | left B => Some (BER_finite (BER_Z2sign s) b significand exp B)
           | right _ => None
           end
      else None
    end.

End BER_decoding.

  (* the meaningless function *)
  Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
    := compose Some.

  (* equality on BER_float *)
  Definition BER_eq_b : BER_float -> BER_float -> bool.
  Admitted.

  (*
    for any BER_float,
    if it can be encoded as a bit string (which it can, see `Some_ize_always_some`)
    then
        it can be decoded
      and
        the result is equal to the starting float
  *)
  Theorem BER_bits_BER_roundtrip (f : BER_float) :
    roundtrip
      BER_float Z BER_float
      (Some_ize bits_of_BER)
      (BER_of_bits)
      BER_eq_b
      f.
  Admitted.


Section Aux.

  Theorem bits_of_BER_decodable :
    forall f : BER_float, is_Some_b (BER_of_bits (bits_of_BER f)) = true.
  Admitted.

  Theorem Some_ize_always_some :
    forall (A B : Type) (f : A -> B) (a : A),
      is_Some_b ((Some_ize f) a) = true.
  Proof.
    intros A B f a.
    reflexivity.
  Qed.

End Aux.