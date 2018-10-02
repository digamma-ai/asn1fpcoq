Require Import ZArith Bool.
Require Import ASN.ASNDef ASN.Aux Aux.Option Aux.Bits Aux.Roundtrip Aux.StructTactics.
Require Import Program.Basics.
Require Import Flocq.Core.Zaux.

Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Template.All.
Require Import Switch.Switch.

Import ListNotations.

Definition BER_REAL_IDENTIFIER := 9%Z.

Section BER_atomic.

  (*
    functions for converting between
    binary strings of atomic parts of BER real encodings
    and abstract representations of those parts
  *)

  Definition BER_radix2bits (b : radix) : Z :=
    (Z.log2 b) - 1.

  Definition BER_bits2radix (b : Z) : radix :=
    if (b =? 0)%Z
    then radix2
    else if (b =? 1)%Z
         then radix4
         else if (b =? 2)%Z
              then radix8
              else if (b =? 4)%Z
                   then radix16
                   else radix2.

  Definition BER_sign2bits (s : bool) : Z :=
    if s then 1 else 0.

  Definition BER_bits2sign (s : Z) : bool :=
    if (s =? 1)%Z then true else false.

  (* TODO: perhaps unify? *)
  Definition BER_exp2bits (e : Z) : Z :=
    octet_twos_complement (twos_olen e) e.

  Definition BER_bits2exp (e_olength : Z) (e : Z) : Z :=
    octet_twos_complement e_olength e.

End BER_atomic.


Section BER_encoding.

  (* see [join_octets] *)
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
    join_BER_bits BER_REAL_IDENTIFIER (olen content) content.

 (* [8.1.3.4] : length octet; [8.5.2] : content octet*)
  Definition BER_PLUS_ZERO_BITS :=
    join_octets BER_REAL_IDENTIFIER 0.
  (* [8.5.9] : "RealSpecialValues" *)
  Definition BER_MINUS_ZERO_BITS :=
    make_BER_real_bits 131.
  Definition BER_PLUS_INFINITY_BITS :=
    make_BER_real_bits 128.
  Definition BER_MINUS_INFINITY_BITS :=
    make_BER_real_bits 129.
  Definition BER_NOT_A_NUMBER_BITS :=
    make_BER_real_bits 130.

  (*
    join together all parts of the descriptor of a BER binary real
    NOTE: no atomic conversions are performed here
  *)
  Definition make_BER_binary_real_descriptor
             (sign radix scaling_factor exp_octets : Z) : Z :=
    let bin_sign               := join_bits 1 sign 1 in
    let bin_sign_radix         := join_bits bin_sign radix 2 in
    let bin_sign_radix_scaling := join_bits bin_sign_radix scaling_factor 2 in
    join_bits bin_sign_radix_scaling exp_octets 2.

  (* TODO: [8.5.7.4] *)
  (*
    given the sign, radix, mantissa and exponent of a BER float
    generate the content block of that float
    NOTE: all atomic conversions are performed here
  *)
  Definition make_BER_finite_real_content (scaled : bool) (s : bool) (b : radix) (m : positive) (e : Z) :=
    let m := Zpos m in
    let scaling_factor := if scaled then Z.log2 (m mod b) else 0%Z in
    let m_bits := (m * 2^scaling_factor)%Z in
    let e_olength := twos_olen e in
    let e_bits := BER_exp2bits e in
    let long_exp := (Z.gtb e_olength 3) in
    let descriptor := if long_exp
                      then make_BER_binary_real_descriptor (BER_sign2bits s) (BER_radix2bits b) scaling_factor 3
                      else make_BER_binary_real_descriptor (BER_sign2bits s) (BER_radix2bits b) scaling_factor (e_olength-1)
    in
    if long_exp
    then descriptor +o+ e_olength +o+ e_bits +o+ m_bits
    else descriptor +o+ e_bits +o+ m_bits.

  (* encoding a BER float as a bit-string *)
  Definition bits_of_BER (scaled : bool) (f : BER_float) : Z :=
    match f with
    | BER_zero s => if s then BER_MINUS_ZERO_BITS else BER_PLUS_ZERO_BITS
    | BER_infinity s => if s then BER_MINUS_INFINITY_BITS else BER_PLUS_INFINITY_BITS
    | BER_nan => BER_NOT_A_NUMBER_BITS
    | BER_finite s b m e _ => make_BER_real_bits
                                (make_BER_finite_real_content scaled s b m e)
    end.

  Example short_BER_ex1 :
    make_BER_real_bits
      (make_BER_finite_real_content false false radix2 532 (- 773)) = 2539330643624468%Z.
  Proof. reflexivity. Qed.

End BER_encoding.


Section BER_decoding.

  (*
    given the bit string representing a BER in short form,
    split it into the three main parts
  *)
  Definition split_short_BER (b : Z) : Z * Z * Z :=
    let '(id, len_content) := split_octets_by_fst b 1 in
    let '(len, content) := split_octets_by_fst len_content 1 in
    (id, len, content).

  (*
    given the bit string of a BER real descriptor octet,
    split it into meaningful parts
  *)
  Definition split_BER_real_descriptor (b : Z) : Z * Z * Z * Z * Z :=
    let '(tsbbff, ee) := split_bits_by_snd b 2 in
    let '(tsbb, ff)   := split_bits_by_snd tsbbff 2 in
    let '(ts, bb)     := split_bits_by_snd tsbb 2 in
    let '(t, s)       := split_bits_by_snd ts 1 in
    (t, s, bb, ff, ee).

  (*
    given the bit string of a finite BER real (i.e. not a special value),
    split it into atomic parts:
      encoding type [t]
      sign [s]
      radix [bb]
      scaling factor [ff]
      exponent length descriptor [ee]
      actual exponent length in octets [e_olength]
        (inferred if exponent is in short form)
      exponent [exp]
      significand [significand]
  *)
  Definition split_BER_finite_real_content (b : Z) :=
    let '(descriptor, content) := split_octets_by_fst b 1 in
    let '(t, s, bb, ff, ee) := split_BER_real_descriptor descriptor in
    if (Z.eqb ee 3)
    then let '(e_olength, exp_significand) := split_octets_by_fst 1 content in
         let '(exp, significand) := split_octets_by_fst exp_significand e_olength in
         (t, s, bb, ff, ee, e_olength, exp, significand)
    else let '(exp, significand) := split_octets_by_fst content (ee + 1) in
         (t, s, bb, ff, ee, (ee + 1)%Z, exp, significand).

Run TemplateProgram
    (mkSwitch Z Z.eqb
              [(BER_PLUS_ZERO_BITS,     "pzero") ;
               (BER_MINUS_ZERO_BITS,    "nzero") ;
               (BER_PLUS_INFINITY_BITS,  "pinf") ;
               (BER_MINUS_INFINITY_BITS, "ninf") ;
               (BER_NOT_A_NUMBER_BITS,    "nan")]
              "BER_special_values" "classify_BER_special"
    ).

  (* TODO: [8.5.7.4] and triple-check the IF *)
  (* decoding a bit string to a BER float *)
  Definition BER_of_bits (b : Z) : option BER_float :=
    let '(id, len, content) := split_short_BER b in
    let '(t, s, bb, ff, ee, e_olength, exp, significand) := split_BER_finite_real_content content in
    let significand := Z.to_pos (significand * (2^ff)) in
    let bb := BER_bits2radix bb in
    let exp := BER_bits2exp e_olength exp in

    match (classify_BER_special b) with
    | Some pzero => Some (BER_zero false)
    | Some nzero => Some (BER_zero true)
    | Some pinf => Some (BER_infinity false)
    | Some ninf => Some (BER_infinity true)
    | Some nan => Some (BER_nan)
    | None =>
      if ((Z.eqb id 9)
          &&
          (Z.ltb len 128)
          &&
          (Z.eqb (olen content) len)
          &&
          (Z.eqb t 1)
          &&
          (((Z.eqb ee 3) && (Z.gtb e_olength 0) && (Z.ltb e_olength 256))
            ||
            ((Z.ltb ee 3) && (Z.eqb e_olength (ee+1))))
          &&
          (Z.eqb (olen exp) e_olength))%bool
      then match valid_BER_sumbool significand exp bb with
           | left B => Some (BER_finite (BER_bits2sign s) bb significand exp B)
           | right _ => None
           end
      else None
    end.

End BER_decoding.

  (* the meaningless function *)
  Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
    := compose Some.

  (* equality on BER_float *)
  Definition BER_eq_b (f1 f2 : BER_float) : bool :=
    match f1, f2 with
    | BER_zero s1, BER_zero s2 => eqb s1 s2
    | BER_infinity s1, BER_infinity s2 => eqb s1 s2
    | BER_nan, BER_nan => true
    | BER_finite s1 b1 m1 e1 _, BER_finite s2 b2 m2 e2 _ =>
      (eqb s1 s2) && (b1 =? b2)%Z && (m1 =? m2)%positive && (e1 =? e2)%Z
    | _, _ => false
    end.

  Lemma split_join_BER (id len content : Z) :
    split_short_BER (join_BER_bits id len content) = (id, len, content).
  Proof.
    unfold split_short_BER, join_BER_bits.
    destruct split_octets_by_fst as [id_d len_content_d] eqn:H1.
    destruct split_octets_by_fst as [len_d content_d] eqn:H2.
    (* this statement is wrong, split_short_BER is not the inverse of join_BER_bits,
       since it only works on SHORT BER, while join joins anything
       need to add another check or a join_short_BER function *)
  Admitted.


  Theorem bits_of_BER_decodable :
    forall (scaling : bool) (f : BER_float), is_Some_b (BER_of_bits (bits_of_BER scaling f)) = true.
  Proof.
    intros scaling f.
    case f.
    - (* BER_zero *)
      simpl. destruct s.
      + (* minus_zero *)
        reflexivity.
      + (* plus_zero *)
        reflexivity.
    - (* BER_infinity *)
      simpl. destruct s.
      + (* minus_infinity *)
        reflexivity.
      + (* plus_infinity *)
        reflexivity.
    - (* NaN *)
      reflexivity.

    - (* finite *)
      intros s b m e VB.
      unfold BER_of_bits.

      (* parse all tuples *)
      destruct (split_short_BER (bits_of_BER scaling (BER_finite s b m e VB))) as [id_len content] eqn:B1.
      destruct id_len as [id len] eqn:B2.

      destruct (split_BER_finite_real_content content) as [tsbbffee_eolen_exp signif_bits] eqn:H1.
      destruct tsbbffee_eolen_exp as [tsbbffee_eolen exp_bits] eqn:H2.
      destruct tsbbffee_eolen as [tsbbffee exp_oct_len] eqn:H3.
      destruct tsbbffee as [tsbbff ee] eqn:H4.
      destruct tsbbff as [tsbb ff] eqn:H5.
      destruct tsbb as [ts bb] eqn:H6.
      destruct ts as [t sign_bit] eqn:H7.

      subst.
      repeat break_match; try reflexivity.
      + (* decoded number is not encodable *)
        exfalso.
        clear Heqo.
        unfold bits_of_BER in B1.
        rewrite -> (split_join_BER BER_REAL_IDENTIFIER (olen (make_BER_finite_real_content scaling s b m e)) (make_BER_finite_real_content scaling s b m e)) in B1.
        inversion B1. subst. clear B1.
        admit.
      + (* incorrect encoding  form *)
        exfalso.

Admitted.

  (*
    for any BER_float,
    if it can be encoded as a bit string (which it can, see `Some_ize_always_some`)
    then
        it can be decoded
      and
        the result is equal to the starting float
  *)
  Theorem BER_bits_BER_roundtrip (scaling : bool) (f : BER_float) :
    roundtrip_option
      BER_float Z BER_float
      (Some_ize (bits_of_BER scaling))
      (BER_of_bits)
      BER_eq_b
      f.
  Proof.
    unfold roundtrip_option, Some_ize, compose, bool_het_inverse'.
    simpl. intros H; clear H.
    break_match.
    - admit.
    - admit.
  Admitted.

Section Aux.

  Theorem Some_ize_always_some :
    forall (A B : Type) (f : A -> B) (a : A),
      is_Some_b ((Some_ize f) a) = true.
  Proof.
    intros A B f a.
    reflexivity.
  Qed.

End Aux.