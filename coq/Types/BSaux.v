Require Import ZArith.
Require Import ASN1FP.Types.BitContainer ASN1FP.Types.Bitstring.

(** * container tuples *)

(* nbs - normal bitstring (i.e. not a special value) *)
Inductive BER_nbs :=
| short_nbs
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (e : container (8 * (c2n ee + 1))) (m : container (8*((c2n co) - (c2n ee) - 2)))
    (VS1 : c2z id = real_id_b) (VS2 : c2z t = 1) (VS3 : c2z ee <= 2) (VS4 : 1 <= c2z m)
    (VS5 : c2z co <= 127)
| long_nbs
    (id co : cont8)
    (t s : cont1) (bb ff ee : cont2)
    (eo : cont8)
    (e : container (8*(c2n eo))) (m : container (8 * ((c2n co) - (c2n eo) - 2)))
    (VL1 : c2z id = real_id_b) (VL2 : c2z t = 1) (VL3 : c2z ee = 3) (VL4 : 1 <= c2z m)
    (VL5 : c2z co <= 127).

Inductive BER_bs_aux :=
| special_aux (val : BER_special) : BER_bs_aux
| normal_aux (b : BER_nbs) : BER_bs_aux.
