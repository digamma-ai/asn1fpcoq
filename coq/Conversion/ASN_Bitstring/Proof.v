Require Import ZArith.
Require Import Lia.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits ASN1FP.Aux.Tactics
        ASN1FP.Conversion.ASN_Bitstring.Def ASN1FP.Conversion.ASN_Bitstring.Atomic.
Require Import Flocq.Core.Zaux.

Open Scope Z.

  Theorem BER_bitstring_roundtrip (scaled : bool) (f : BER_float) :
    roundtrip_option
      BER_float BER_bitstring BER_float
      (BER_to_bitstring scaled)
      bitstring_to_BER
      BER_float_strict_eqb
      f.
  Admitted.
  (* Proof. *)
  (*   unfold roundtrip_option, Some_ize. *)
  (*   simpl. intros H. clear H. *)
  (*   unfold bool_het_inverse'. simpl. *)
  (*   break_match. *)
  (*   - (* pass *) *)
  (*     destruct f. *)
  (*     + (* zero *) *)
  (*       destruct s; simpl in *; inversion Heqo; reflexivity. *)
  (*     + (* infinity *) *)
  (*       destruct s; simpl in *; inversion Heqo; reflexivity. *)
  (*     + (* nan *) *)
  (*       inversion Heqo. reflexivity. *)
  (*     + (* finite *) *)
  (*       simpl in *. *)
  (*       unfold finite_BER_to_bitstring in Heqo. *)
  (*       destruct (twos_olen e <? 4)%Z. *)
  (*       * (* long exponent *) *)
  (*         simpl in *. *)
  (*         destruct valid_short_sumbool eqn:VS; try some_eq_none_inv. *)
  (*         inversion Heqo as [H]. clear Heqo. *)
  (*         rewrite sign2bits_inv. *)

  (*         (* radix needs to be correct to be invertable *) *)
  (*         inversion e0 as [BV]. *)
  (*         unfold valid_BER in BV. *)
  (*         apply andb_prop in BV. inversion BV as [B V]. clear B. *)
  (*         rewrite (radix2bits_inv b0 V). *)

  (*         rewrite signif2bits_inv. *)

  (*         remember (twos_olen e) as toe. *)
  (*         assert (T : (toe - 1 + 1 = toe)%Z) by ring. *)
  (*         rewrite T. *)
  (*         rewrite exp2bits_inv. *)

  (*         rewrite e0. *)

  (*         reflexivity. *)
  (*       * (* short exponent *) *)
  (*         simpl in *. *)
  (*         destruct valid_long_sumbool eqn:VS; try some_eq_none_inv. *)
  (*         inversion Heqo as [H]. clear Heqo. *)
  (*         rewrite sign2bits_inv. *)

  (*         (* radix needs to be correct to be invertable *) *)
  (*         inversion e0 as [BV]. *)
  (*         unfold valid_BER in BV. *)
  (*         apply andb_prop in BV. inversion BV as [B V]. clear B. *)
  (*         rewrite (radix2bits_inv b0 V). *)

  (*         rewrite signif2bits_inv. *)
  (*         rewrite exp2bits_inv. *)
  (*         rewrite e0. *)
  (*         reflexivity. *)
  (*   - (* no pass *) *)
  (*     exfalso. *)
  (*     generalize dependent (BER_to_bitstring_correct scaled f). intros C. *)
  (*     unfold bitstring_to_BER in Heqo. *)

  (*     destruct BER_to_bitstring eqn:BB. *)

  (*     + (* special *) *)
  (*       destruct classify_BER eqn:H. *)
  (*       * break_match; try some_eq_none_inv. *)
  (*       * simpl in C. *)
  (*         unfold valid_special in C. *)
  (*         rewrite H in C. *)
  (*         inversion C. *)

  (*     + (* short *) *)
  (*       destruct valid_short_sumbool. *)
  (*       * some_eq_none_inv. *)
  (*       * clear Heqo. *)
  (*         unfold correct_bitstring in C. *)
  (*         rewrite e in C. inversion C. *)

  (*     + (* long *) *)
  (*       destruct valid_long_sumbool. *)
  (*       * some_eq_none_inv. *)
  (*       * clear Heqo. *)
  (*         unfold correct_bitstring in C. *)
  (*         rewrite e in C. inversion C. *)
  (* Qed. *)
