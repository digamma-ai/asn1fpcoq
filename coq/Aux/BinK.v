Require Import ZArith.
Require Import Conversion.ASN_IEEE.

Open Scope Z.

Section B32.

  Let prec := 24.
  Let emax := 128.
  Let prec_gt_1 : Prec_gt_1 prec.
  Proof. reflexivity. Qed.
  Let prec_lt_emax : prec < emax.
  Proof. subst prec. subst emax. reflexivity. Qed.
  
  Definition b32_to_BER_abstract := IEEE_to_BER_exact prec emax.

  Definition BER_to_b32_abstract_exact := BER_to_IEEE_exact prec emax prec_gt_1.

  Definition BER_to_b32_abstract_rounded := BER_to_IEEE_rounded prec emax prec_gt_1 prec_lt_emax.

End B32.


Section B64.

  Let prec := 53%Z.
  Let emax := 1024%Z.
  Let prec_gt_1 : Prec_gt_1 prec.
  Proof. reflexivity. Qed.
  Let prec_lt_emax : prec < emax.
  Proof. subst prec. subst emax. reflexivity. Qed.
  
  Definition b64_to_BER_abstract := IEEE_to_BER_exact prec emax.

  Definition BER_to_b64_abstract_exact := BER_to_IEEE_exact prec emax prec_gt_1.

  Definition BER_to_b64_abstract_rounded := BER_to_IEEE_rounded prec emax prec_gt_1 prec_lt_emax.

End B64.