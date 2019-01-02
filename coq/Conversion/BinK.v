Require Import ZArith.
Require Import ASN1FP.Conversion.IEEE_ASN.DefProof.

Open Scope Z.

(*
 * auxiliary functions for the most common formats
 * combining partial conversions into one full pass
 *)

Section B32.

  Let prec := 24.
  Let emax := 128.
  Let prec_gt_1 : prec > 1.
  Proof. reflexivity. Qed.
  Let prec_lt_emax : prec < emax.
  Proof. subst prec. subst emax. reflexivity. Qed.

  Definition normalize_b32_abstract (m e : Z) :=
    let '(mx, ex) := normalize_IEEE_finite prec emax (Z.to_pos m) e in
    (Zpos mx, ex).
  
  Definition BER_of_b32_abstract := BER_of_IEEE_exact prec emax.

  Definition b32_of_BER_abstract_exact := IEEE_of_BER_exact prec emax prec_gt_1.

  Definition b32_of_BER_abstract_rounded := IEEE_of_BER_rounded prec emax prec_gt_1 prec_lt_emax.

End B32.

Section B64.

  Let prec := 53%Z.
  Let emax := 1024%Z.
  Let prec_gt_1 : prec > 1.
  Proof. reflexivity. Qed.
  Let prec_lt_emax : prec < emax.
  Proof. subst prec. subst emax. reflexivity. Qed.
  
  Definition normalize_b64_abstract (m e : Z) :=
    let '(mx, ex) := normalize_IEEE_finite prec emax (Z.to_pos m) e in
    (Zpos mx, ex).

  Definition BER_of_b64_abstract := BER_of_IEEE_exact prec emax.

  Definition b64_of_BER_abstract_exact := IEEE_of_BER_exact prec emax prec_gt_1.

  Definition b64_of_BER_abstract_rounded := IEEE_of_BER_rounded prec emax prec_gt_1 prec_lt_emax.

End B64.
