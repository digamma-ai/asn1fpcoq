Require Import ZArith.
Require Import ASN1FP.Types.ASNDef
               ASN1FP.Aux.Bits ASN1FP.Aux.Roundtrip.
Require Import Flocq.Core.Zaux.

Section Def.

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

  Definition sign2bits (s : bool) : Z :=
    if s then 1 else 0.

  Definition bits2sign (s : Z) : bool :=
    if (Z.eqb s 1) then true else false.

  Definition signif2bits (m : positive) : Z :=
    Zpos m.

  Definition bits2signif (m : Z) : positive :=
    Z.to_pos m.

  Definition exp2bits (e_olen e : Z) : Z :=
    twos_comp_extended (8 * e_olen) e.

  Definition bits2exp (e_olen e : Z) : Z :=
    twos_comp_extended (8 * e_olen) e.

End Def.

Section Proofs.

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
		
		Lemma exp2bits_inv (e_olen e  : Z) :
		  bool_het_inverse
			Z Z Z
			(exp2bits e_olen)
			(bits2exp e_olen)
			Z.eqb
			e.
		Proof.
		  apply twos_comp_extended_roundtrip.
		Qed.

End Proofs.