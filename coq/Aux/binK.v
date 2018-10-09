Require Import ZArith.
Require Import Conversion.ASN_IEEE.

Section B32.

  Let prec := 24%Z.
  Let emax := 128%Z.
  Let prec_gt_1 : Prec_gt_1 prec.
  Proof. reflexivity. Qed.
  
  Definition b32_to_BER_abstract := IEEE_to_BER_exact prec emax.

  Definition BER_to_b32_abstract := BER_to_IEEE_exact prec emax prec_gt_1.

End B32.


Section B64.

  Let prec := 53%Z.
  Let emax := 1024%Z.
  Let prec_gt_1 : Prec_gt_1 prec.
  Proof. reflexivity. Qed.
  
  Definition b64_to_BER_abstract := IEEE_to_BER_exact prec emax.

  Definition BER_to_b64_abstract := BER_to_IEEE_exact prec emax prec_gt_1.

End B64.