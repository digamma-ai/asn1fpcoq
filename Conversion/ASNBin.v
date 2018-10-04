Require Import ZArith Sumbool Option.
Require Import ASN.ASNDef Aux.Roundtrip Aux.Bits Aux.StructTactics Aux.Tactics.
Require Import Lia.
Require Import Flocq.Core.Zaux.

Require Import Arith.EqNat Strings.String Lists.List.
Require Import Template.All Switch.Switch.

Import ListNotations.
  



Section Bitstring_def.

  Let real_id_b := 9%Z.

  Let pzero_b   := 2304%Z.
  Let nzero_b   := 590211%Z.
  Let pinf_b    := 590208%Z.
  Let ninf_b    := 590209%Z.
  Let nan_b     := 590210%Z.

  Run TemplateProgram
      (mkSwitch Z Z.eqb
                [(pzero_b,    "pzero") ;
                (nzero_b,     "nzero") ;
                (pinf_b,       "pinf") ;
                (ninf_b,       "ninf") ;
                (nan_b,         "nan")]
                "BER_specials" "classify_BER"
      ).

  Inductive BER_bitstring :=
  | special   (val : Z)
  | short (id content_olen type sign base scaling exp_olen_b            exponent significand : Z)
  | long  (id content_olen type sign base scaling       lexp exp_olen_o exponent significand : Z).


  Definition BER_bitstring_eqb (b1 b2 : BER_bitstring) : bool.
  Admitted.
    (* match b1, b2 with *)
    (* | special val1, special val2 => Z.eqb val1 val2 *)
    (* | short id1 co1 t1 s1 bb1 ff1 ee1 e1 m1, short id2 co2 t2 s2 bb2 ff2 ee2 e2 m2 => *)
    (* | long id1 co1 t1 s1 bb1 ff1 ee1 eo1 e1 m1, long id2 co2 t2 s2 bb2 ff2 ee2 eo2 e2 m => *)
    (* | _, _ => false *)
    (* end. *)


  Definition valid_special (val : Z) : bool :=
    match (classify_BER val) with
    | Some _ => true
    | None   => false
    end.

  Definition correct_short_co (co e m : Z) : bool :=
    Z.eqb co (olen e + olen m + 1).

  Definition valid_short (id co t s bb ff ee e m : Z) : bool :=
       (Z.eqb id 9)                      (* identifier is "REAL" *)
    && (correct_short_co co e m)         (**encoding length is correct *)
    && (Z.eqb t 1)                       (* encoding is binary *)
    && (Z.ltb (-1)  s) && (Z.ltb  s 2)   (* sign bit is well-formed *)
    && (Z.ltb (-1) bb) && (Z.ltb bb 4)   (* radix bit is well-formed *)
    && (Z.ltb (-1) ff) && (Z.ltb ff 4)   (* scaling factor is well-formed *)
    && (Z.ltb (-1) ee) && (Z.ltb ee 3)   (**exponent length is well-formed *)
    && (Z.ltb (olen e) (ee + 2))         (**exponent length is correct *)
    && (Z.ltb (-1) e)                    (* exponent is non-negative (it is two's complement) *)
    && (Z.ltb 0 m).                      (* mantissa is positive *)

  Definition correct_long_co (co e m : Z) : bool :=
    Z.eqb co (olen e + olen m + 2).

    Definition valid_long (id co t s bb ff ee eo e m : Z) : bool :=
       (Z.eqb id real_id_b)              (* identifier is "REAL" *)
    && (correct_long_co co e m)          (**encoding length is correct *)
    && (Z.eqb t 1)                       (* encoding is binary *)
    && (Z.ltb (-1)  s) && (Z.ltb  s 2)   (* sign bit is well-formed *)
    && (Z.ltb (-1) bb) && (Z.ltb bb 4)   (* radix bit is well-formed *)
    && (Z.ltb (-1) ff) && (Z.ltb ff 4)   (* scaling factor is well-formed *)
    && (Z.eqb ee 3)                      (**exponent is in long form *)
    && (Z.ltb (-1) eo) && (Z.ltb eo 256) (**exponent length is well-formed *)
    && (Z.ltb (olen e) (eo + 1))         (**exponent length is correct *)
    && (Z.ltb (-1) e)                    (* exponent is non-negative (it is two's complement) *)
    && (Z.ltb 0 m).                      (* mantissa is positive *)

  Definition correct_bitstring (b : BER_bitstring) : bool :=
    match b with
    | special val => (valid_special val)
    | short id co t s bb ff ee    e m => (valid_short id co t s bb ff ee    e m)
    | long  id co t s bb ff ee eo e m => (valid_long  id co t s bb ff ee eo e m)
    end.
      
  Section Atomic.

    Definition radix2bits (b : radix) : Z :=
      if Z.eqb b 2 then 0
      else if Z.eqb b 4 then 1
          else if Z.eqb b 8 then 2
                else if Z.eqb b 16 then 3
                    else 0.

    Definition bits2radix (b : Z) : radix :=
      if Z.eqb b 0 then radix2
      else if Z.eqb b 1 then radix4
          else if Z.eqb b 2 then radix8
                else if Z.eqb b 3 then radix16
                    else radix2.

    Lemma radix2bits_inv (b : radix) :
      valid_radix b = true ->
      bool_het_inverse
        radix Z radix
        radix2bits
        bits2radix 
        Z.eqb
        b.
    Proof.
      intros H.
      unfold bool_het_inverse, Basics.compose, bits2radix, radix2bits.
      destruct (Z.eqb b 2) eqn:R2.
      - simpl. apply R2.
      - destruct (Z.eqb b 4) eqn:R4.
        + simpl. apply R4.
        + destruct (Z.eqb b 8) eqn:R8.
          * simpl. apply R8.
          * destruct (Z.eqb b 16) eqn:R16.
            { simpl. apply R16. }
            {
              contradict H.
              unfold valid_radix.
              rewrite R2. rewrite R4. rewrite R8. rewrite R16.
              simpl. auto.
            }
    Qed.

    Definition sign2bits (s : bool) : Z :=
      if s then 1 else 0.

    Definition bits2sign (s : Z) : bool :=
      if (Z.eqb s 1) then true else false.

    Lemma sign2bits_inv (s : bool) :
      bool_het_inverse
        bool Z bool
        sign2bits
        bits2sign
        Bool.eqb
        s.
    Proof.
      unfold bool_het_inverse, bits2sign, sign2bits.
      destruct s.
      - reflexivity.
      - reflexivity.
    Qed.

    Definition signif2bits (m : positive) : Z :=
      Zpos m.

    Definition bits2signif (m : Z) : positive :=
      Z.to_pos m.

    Lemma signif2bits_inv (m : positive) :
      bool_het_inverse
        positive Z positive
        signif2bits
        bits2signif
        Pos.eqb
        m.
    Proof.
      unfold bool_het_inverse, bits2signif, signif2bits.
      simpl. apply Pos.eqb_refl.
    Qed.

    Definition exp2bits (e_olen e : Z) : Z.
    Admitted.

    Definition bits2exp (e_olen e : Z) : Z.
    Admitted.

    Lemma exp2bits_inv (e_olen e  : Z) :
      bool_het_inverse
        Z Z Z
        (exp2bits e_olen)
        (bits2exp e_olen)
        Z.eqb
        e.
    Admitted.

  End Atomic.

  (* TODO: scaling *)
  Definition finite_BER_to_bitstring (scaled : bool) (s : bool) (b : radix) (m : positive) (e : Z) : BER_bitstring :=
    let m := signif2bits m in
    let s := sign2bits s in
    let bb := radix2bits b in
    let ff := 0%Z in
    let e_olen := twos_olen e in
    let e := exp2bits e_olen e in
      if Z.ltb (e_olen) 4
      then short real_id_b (e_olen + olen m + 1)%Z 1 s bb ff (e_olen - 1)        e m
      else long  real_id_b (e_olen + olen m + 2)%Z 1 s bb ff            3 e_olen e m.

  Definition BER_to_bitstring (scaled : bool) (f : BER_float) : BER_bitstring :=
    match f with
    | BER_zero s => if s then special nzero_b else special pzero_b
    | BER_infinity s => if s then special ninf_b else special pinf_b
    | BER_nan => special nan_b
    | BER_finite s b m e _ => finite_BER_to_bitstring scaled s b m e
    end.

  Lemma valid_short_valid_BER {id co t s bb ff ee e m : Z} :
    valid_short id co t s bb ff ee e m = true ->
    valid_BER (bits2signif m) (bits2exp (ee + 1) e) (bits2radix bb) = true.
  Proof.
    unfold valid_short. intros H.
    repeat split_andb.
     clear H0. clear H6. clear H7. clear H10. clear H11. clear H12. clear H13.
     unfold valid_BER. apply andb_true_intro. split.
    - (* bounded *)
      clear H8. clear H9.
      unfold bounded.
      break_match.
      + (* long exponent *)
        exfalso.
        rewrite Z.ltb_lt in *.
        apply (Z.lt_trans (olen e) (ee + 2) 5) in H3.
        (* *)

        (* *)
          apply (Zplus_lt_compat_r ee 3 2).
          apply H4.






    - (* valid_radix *)
      admit.
  Admitted.

  Lemma valid_long_valid_BER {id co t s bb ff ee eo e m : Z} :
    valid_long id co t s bb ff ee eo e m = true ->
    valid_BER (bits2signif m) (bits2exp (eo) e) (bits2radix bb) = true.
  Admitted.

  Definition valid_short_sumbool (id co t s bb ff ee e m : Z) :=
    sumbool_of_bool (valid_short id co t s bb ff ee e m).

  Definition valid_long_sumbool (id co t s bb ff ee eo e m : Z) :=
    sumbool_of_bool (valid_long id co t s bb ff ee eo e m).

  (* default garbage return in BER_nan *)
  Definition bitstring_to_BER (b : BER_bitstring) : option BER_float :=
    match b with
    | special val =>
      match classify_BER val with
      | Some pzero => Some (BER_zero false)
      | Some nzero => Some (BER_zero true)
      | Some pinf => Some (BER_infinity false)
      | Some ninf => Some (BER_infinity true)
      | Some nan => Some (BER_nan)
      | None => None
      end

    | short id co t s bb ff ee    e m =>
      match valid_short_sumbool id co t s bb ff ee e m with
      | right _ => None
      | left V =>
        Some (BER_finite
                (bits2sign s)
                (bits2radix bb)
                (bits2signif m)
                (bits2exp (ee + 1) e)
                (valid_short_valid_BER V)
             )
      end

    | long  id co t s bb ff ee eo e m =>
      match valid_long_sumbool id co t s bb ff ee eo e m with
      | right _ => None
      | left V =>
        Some (BER_finite
                (bits2sign s)
                (bits2radix bb)
                (bits2signif m)
                (bits2exp (eo) e)
                (valid_long_valid_BER V)
             )
      end
    end.

  Lemma BER_to_bitstring_correct (scaled : bool) (f : BER_float) :
    correct_bitstring (BER_to_bitstring scaled f) = true.
  Admitted.

  Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
    := Basics.compose Some.

  Theorem BER_bitstring_BER_roundtrip (scaled : bool) (f : BER_float) :
    roundtrip_option
      BER_float BER_bitstring BER_float
      (Some_ize (BER_to_bitstring scaled))
      bitstring_to_BER
      BER_float_strict_eqb
      f.
  Proof.
    unfold roundtrip_option, Some_ize.
    simpl. intros H. clear H.
    unfold bool_het_inverse'. simpl.
    break_match.
    - (* pass *)
      destruct f.
      + (* zero *)
        destruct s; simpl in *; inversion Heqo; reflexivity.
      + (* infinity *)
        destruct s; simpl in *; inversion Heqo; reflexivity.
      + (* nan *)
        inversion Heqo. reflexivity.
      + (* finite *)
        simpl in *.
        unfold finite_BER_to_bitstring in Heqo.
        destruct (twos_olen e <? 4)%Z.
        * (* long exponent *)
          simpl in *.
          destruct valid_short_sumbool eqn:VS; try some_eq_none_inv.
          inversion Heqo as [H]. clear Heqo.
          rewrite sign2bits_inv.

          (* radix needs to be correct to be invertable *)
          inversion e0 as [BV].
          unfold valid_BER in BV.
          apply andb_prop in BV. inversion BV as [B V]. clear B.
          rewrite (radix2bits_inv b0 V).

          rewrite signif2bits_inv.

          assert (T : Z.eq (twos_olen e - 1 + 1) (twos_olen e)).
          { admit. }
          rewrite T.
          rewrite exp2bits_inv.

          rewrite e0.

          reflexivity.
        * (* short exponent *)
          simpl in *.
          destruct valid_long_sumbool eqn:VS; try some_eq_none_inv.
          inversion Heqo as [H]. clear Heqo.
          rewrite sign2bits_inv.

          (* radix needs to be correct to be invertable *)
          inversion e0 as [BV].
          unfold valid_BER in BV.
          apply andb_prop in BV. inversion BV as [B V]. clear B.
          rewrite (radix2bits_inv b0 V).

          rewrite signif2bits_inv.
          rewrite exp2bits_inv.
          rewrite e0.
          reflexivity.
    - (* no pass *)
      exfalso.
      generalize dependent (BER_to_bitstring_correct scaled f). intros C.
      unfold bitstring_to_BER in Heqo.

      destruct BER_to_bitstring eqn:BB.

      + (* special *)
        destruct classify_BER eqn:H.
        * break_match; try some_eq_none_inv.
        * simpl in C.
          unfold valid_special in C.
          rewrite H in C.
          inversion C.

      + (* short *)
        destruct valid_short_sumbool.
        * some_eq_none_inv.
        * clear Heqo.
          unfold correct_bitstring in C.
          rewrite e in C. inversion C.

      + (* long *)
        destruct valid_long_sumbool.
        * some_eq_none_inv.
        * clear Heqo.
          unfold correct_bitstring in C.
          rewrite e in C. inversion C.
  Admitted.

End Bitstring_def.

Section Bitstring_bits.

  Definition bitstring_to_bits : BER_bitstring -> Z.
  Admitted.

  Definition bits_to_bitstring : Z -> BER_bitstring.
  Admitted.

  Theorem bitsrting_bits_bitstring_roundtrip (b : BER_bitstring) :
    bool_het_inverse
      BER_bitstring Z BER_bitstring
      bitstring_to_bits
      bits_to_bitstring
      BER_bitstring_eqb
      b.
  Admitted.

End Bitstring_bits.

Definition BER_to_bits (scaled : bool) : BER_float -> Z :=
  Basics.compose bitstring_to_bits (BER_to_bitstring scaled).

Definition bits_to_BER : Z -> option BER_float :=
  Basics.compose bitstring_to_BER bits_to_bitstring.

Theorem BER_bits_BER_roundtrip (scaled : bool) (f : BER_float) :
  roundtrip_option
    BER_float Z BER_float
    (Some_ize (BER_to_bits scaled))
    bits_to_BER
    BER_float_strict_eqb
    f.
Proof.
  unfold roundtrip_option. simpl. intros T. clear T.
  unfold Some_ize, BER_to_bits, bits_to_BER, Basics.compose, bool_het_inverse'. simpl.
  set (bf := BER_to_bitstring scaled f).

  (* ... *)

  assert (H : BER_bitstring_eqb bf (bits_to_bitstring (bitstring_to_bits bf)) = true).
  {
    generalize dependent (bitsrting_bits_bitstring_roundtrip (BER_to_bitstring scaled f)).
    unfold bool_het_inverse, Basics.compose.
    intros H. apply H.
  }

  (* ... *)

Admitted.
