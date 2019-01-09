Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits.

Definition append_e (e m : Z) :=
  join_octets e m.

Section Short.

  Variable id co t s bb ff ee e m : Z.
  Hypothesis V : valid_short id co t s bb ff ee e m = true.
  Let b := short id co t s bb ff ee e m V.

  (* construct information octet *)
  Let ffee := join_bits_ext 2 ff ee.
  Let bbffee := join_bits_ext 4 bb ffee.
  Let sbbffee := join_bits_ext 6 s bbffee.
  Let i := join_bits_ext 7 t sbbffee.

  (* join main parts by octets *)
  Let m_olen := co - ee - 2.
  Let e_m := join_octets_ext m_olen e m.

  Lemma m_olen_correct_s :
    olen m <= m_olen.
  Admitted.

  Let e_m_olen := co - 1.
  Let i_e_m := join_octets_ext e_m_olen i e_m.

  Lemma e_m_olen_correct_s :
    olen e_m <= e_m_olen.
  Admitted.

  Let co_i_e_m := join_octets_ext co co i_e_m.

  Lemma i_e_m_olen_correct_s :
    olen i_e_m <= co.
  Admitted.

  Let id_co_i_e_m := join_octets_ext (co + 1) id co_i_e_m.

  Lemma co_i_e_m_olen_correct_s :
    olen co_i_e_m <= co + 1.
  Admitted.

  Definition bits_of_short_bitstring_aux :=
    id_co_i_e_m.

End Short.

Section Long.

  Variable id co t s bb ff ee eo e m : Z.
  Hypothesis V : valid_long id co t s bb ff ee eo e m = true.
  Let b := long id co t s bb ff ee eo e m V.

  (* construct information octet *)
  Let ffee := join_bits_ext 2 ff ee.
  Let bbffee := join_bits_ext 4 bb ffee.
  Let sbbffee := join_bits_ext 6 s bbffee.
  Let i := join_bits_ext 7 t sbbffee.

  (* join main parts by octets *)
  Let m_olen := co - eo - 2.
  Let e_m := join_octets_ext m_olen e m.

  Lemma m_olen_correct_l :
    olen m <= m_olen.
  Admitted.

  Let e_m_olen := co - 2.
  Let eo_e_m := join_octets_ext e_m_olen i e_m.

  Lemma e_m_olen_correct_l :
    olen e_m <= e_m_olen.
  Admitted.

  Let eo_e_m_olen := co - 1.
  Let i_eo_e_m := join_octets_ext eo_e_m_olen i eo_e_m.

  Lemma eo_e_m_olen_correct :
    olen eo_e_m <= eo_e_m_olen.
  Admitted.

  Let co_i_eo_e_m := join_octets_ext co co i_eo_e_m.

  Lemma i_e_m_olen_correct_l :
    olen i_eo_e_m <= co.
  Admitted.

  Let id_co_i_eo_e_m := join_octets_ext (co + 1) id co_i_eo_e_m.

  Lemma co_i_e_m_olen_correct_l :
    olen co_i_eo_e_m <= co + 1.
  Admitted.

  Definition bits_of_long_bitstring_aux :=
    id_co_i_eo_e_m.

End Long.

Definition bits_of_bitstring (b : BER_bitstring) :=
  match b with
  | special val => val
  | short id co t s bb ff ee e m x =>
      bits_of_short_bitstring_aux id co t s bb ff ee e m
  | long id co t s bb ff ee eo e m x =>
      bits_of_long_bitstring_aux id co t s bb ff ee eo e m
  end.

(*
Definition bits_of_bitstring (b : BER_bitstring) : Z :=
  match b with
  | special val =>
    match classify_BER val with
    | Some pzero => pzero_b
    | Some nzero => nzero_b
    | Some pinf => pinf_b
    | Some ninf => ninf_b
    | Some nan => nan_b
    | None => -1
    end

  | short id content_olen type sign base scaling exp_olen_b exponent significand _ =>
    let em_olen := content_olen - 1 in
    let em_blen := 8*em_olen in
    join_octets_ext (content_olen + 1) id
      (join_octets_ext content_olen content_olen

        (join_bits_ext (em_blen + 7) type
          (join_bits_ext (em_blen + 6) sign
            (join_bits_ext (em_blen + 4) base
              (join_bits_ext (em_blen + 2) scaling

                (join_octets_ext em_olen exp_olen_b
                  (join_octets_ext (em_olen - exp_olen_b - 1) exponent
                    significand)))))))


  | long id content_olen type sign base scaling lexp exp_olen_o exponent significand _ =>
    let em_olen := content_olen - 2 in
    let lem_blen := 8*(em_olen+1) in
    join_octets_ext (content_olen + 1) id
      (join_octets_ext content_olen content_olen

        (join_bits_ext (lem_blen + 7) type
          (join_bits_ext (lem_blen + 6) sign
            (join_bits_ext (lem_blen + 4) base
              (join_bits_ext (lem_blen + 2) scaling
                (join_octets_ext (em_olen + 1) lexp

                  (join_octets_ext em_olen exp_olen_o
                    (join_octets_ext (em_olen - exp_olen_o) exponent
                      significand))))))))
  end.
*)

Definition bitstring_of_bits (b : Z) : option BER_bitstring :=
  match classify_BER b with
    | Some pzero => Some (special pzero_b)
    | Some nzero => Some (special nzero_b)
    | Some pinf => Some (special pinf_b)
    | Some ninf => Some (special ninf_b)
    | Some nan => Some (special nan_b)
    | None =>
      let '(id, co_content) := split_octets_by_fst 1 b in
      let '(co, content) := split_octets_by_fst 1 co_content in
      let '(tsbbffee, l_exp_signif) := split_octets_by_fst 1 content in
      let '(t, sbbffee) := split_bits_by_snd 7 tsbbffee in
      let '(s, bbffee) := split_bits_by_snd 6 sbbffee in
      let '(bb, ffee) := split_bits_by_snd 4 bbffee in
      let '(ff, ee) := split_bits_by_snd 2 ffee in
      if (2 <? ee)
      then
        let '(e_olen, exp_signif) := split_octets_by_fst 1 l_exp_signif in
        let '(exp, signif) := split_octets_by_snd (co - e_olen - 2) exp_signif in
        match valid_long_sumbool id co t s bb ff ee e_olen exp signif with
          | right _ => None
          | left V => Some (long id co t s bb ff ee e_olen exp signif V)
        end
      else
        let '(exp, signif) := split_octets_by_snd (co - ee - 2) l_exp_signif in
        match valid_short_sumbool id co t s bb ff ee exp signif with
          | right _ => None
          | left V => Some (short id co t s bb ff ee exp signif V)
        end
    end.