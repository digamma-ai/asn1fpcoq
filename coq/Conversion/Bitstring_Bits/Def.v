Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits.

Definition bitstring_to_bits (b : BER_bitstring) : Z :=
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

Definition bits_to_bitstring (b : Z) : option BER_bitstring :=
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
