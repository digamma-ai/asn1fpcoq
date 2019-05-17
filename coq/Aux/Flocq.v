Require Import ZArith Lia Basics RelationClasses.
Require Import Flocq.IEEE754.Binary Flocq.Core.Defs Flocq.Core.Zaux.
Require Import ASN1FP.Aux.StructTactics ASN1FP.Aux.Option.

Open Scope Z.

Section Flocq_bounded_IEEE.
 
  Let log2 := log_inf.
  Let digits := compose Z.succ log2.
  
  Lemma digits2_pos_log2 (m : positive) :
    Z.pos (Digits.digits2_pos m) = Z.succ (log2 m).
  Proof.
    induction m; simpl; try (rewrite Pos2Z.inj_succ, IHm); reflexivity.
  Qed.
  
  Lemma digits2_pos_digits (m : positive) :
    Z.pos (Digits.digits2_pos m) = digits m.
  Proof.
    unfold digits, compose.
    apply digits2_pos_log2.
  Qed.
  
  (** ** Flocq's Binary.bounded rewritten in a form close to IEEE-754 *)
  Lemma bounded_unfolded (prec emax : Z)
        (prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec) (Hmax : (prec < emax)%Z)
        (m : positive) (e : Z) :
    let emin := 3 - emax - prec in
    bounded prec emax m e = true
    <->
    or
      (digits m < prec /\ e = emin)
      (digits m = prec /\ emin <= e <= emax - prec).
  Proof.
    intro.
    unfold FLX.Prec_gt_0, bounded, canonical_mantissa, FLT.FLT_exp in *.
    rewrite Bool.andb_true_iff, Z.leb_le, <-Zeq_is_eq_bool, digits2_pos_digits.
    split; intro.
    all: destruct (Z_lt_le_dec (digits m + e - prec) emin).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: lia.
  Qed.

  Lemma shl_align_fexp_works_iff (prec emax : Z) (m : positive) (e : Z) :
    let emin := 3 - emax - prec in
    shl_align_fexp prec emax m e <> (m, e)
    <->
    (emin < e /\ digits m + e - prec < emin) \/ (digits m < prec /\ emin <= digits m + e - prec).
  Proof.
    intro.
    unfold shl_align_fexp, shl_align, FLT.FLT_exp.
    rewrite digits2_pos_digits.
    replace (3 - emax - prec) with emin by reflexivity.
    destruct (Z_lt_le_dec (digits m + e - prec) emin).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: split.
    all: break_match.
    all: try (intros T; contradict T; reflexivity).
    all: try lia.
    all: intro H; destruct H as [H1 | H1]; destruct H1 as [H1 H2].
    all: intro H; tuple_inversion.
    all: try lia.
    rewrite H3 in H4.
    lia.
  Qed.

  Lemma shl_align_fexp_bad (prec emax : Z) (m : positive) (e : Z) :
    (prec <= digits m)
     ->
    shl_align_fexp prec emax m e = (m, e).
  Proof.
    unfold shl_align_fexp, shl_align, FLT.FLT_exp.
    rewrite digits2_pos_digits.
    destruct (Z_lt_le_dec (digits m + e - prec) (3 - emax - prec)).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: break_match; try reflexivity; try lia.
  Qed.
     


End Flocq_bounded_IEEE.

Section normalization.

  (* a basic float - a pair of two integers - mantissa and exponent *)
  Let float := float radix2.
  Let Float := Float radix2.

  Definition not_zero (f : float) := (Fnum f) <> 0.

  Definition valid_float (prec emax : Z) (f : float) :=
    match (Fnum f) with
    | Z0 => true
    | Z.pos m => bounded prec emax m (Fexp f)
    | Z.neg m => bounded prec emax m (Fexp f)
    end.
  
  Definition float_eq (f1 : float) (f2 : float) : Prop :=
    let '(m1, e1) := (Fnum f1, Fexp f1) in
    let '(m2, e2) := (Fnum f2, Fexp f2) in
    or
      (e2 <= e1 /\ m2 = m1 * 2 ^ (e1 - e2))
      (e1 <= e2 /\ m1 = m2 * 2 ^ (e2 - e1)).

  Lemma float_eq_refl : Reflexive float_eq.
  Proof.
    unfold Reflexive; intro f.
    unfold float_eq; left.
    replace (Fexp f - Fexp f) with 0.
    all: lia.
  Qed.

  Lemma float_eq_sym : Symmetric float_eq.
  Proof.
    unfold Symmetric, float_eq.
    intros; destruct H; auto.
  Qed.

  Lemma Zpow_divide (b p1 p2 : Z) :
    0 < b ->
    0 <= p1 <= p2 ->
    (b ^ p1 | b ^ p2).
  Proof.
    intros B P.
    rewrite <-Z.mod_divide by (apply Z.pow_nonzero; lia).
    replace p2 with ((p2 - p1) + p1) by lia.
    rewrite Z.pow_add_r by lia.
    apply Z_mod_mult.
  Qed.

  Lemma float_eq_trans : Transitive float_eq.
  Proof.
    unfold Transitive.
    destruct x as [mx ex], y as [my ey], z as [mz ez].
    unfold float_eq.
    clear float Float.
    simpl.
    intros XY YZ.
    destruct XY as [XY | XY]; destruct YZ as [YZ | YZ].
    all: destruct XY as [EXY MXY]; destruct YZ as [EYZ MYZ]; subst.
    - left; split; [lia |].
      rewrite <-Z.mul_assoc.
      rewrite <-Z.pow_add_r; try lia.
      replace (ex - ey + (ey - ez)) with (ex - ez) by lia.
      reflexivity.
    - destruct (Z.eq_dec ex ez); subst.
      + (* ex = ez *)
        apply Z.mul_reg_r in MYZ.
        subst; left; split; [lia |].
        rewrite Z.sub_diag; lia.
        generalize (Z.pow_pos_nonneg 2 (ez - ey)); lia.
      + destruct (Z_lt_le_dec ex ez).
        * (* ex < ez *)
          rename MYZ into H.
          assert (H1 : ey <= ex < ez) by lia; clear EXY EYZ n l.
          right; split; [lia |].
          apply f_equal with (f := fun x => Z.div x (2 ^ (ex - ey))) in H.
          rewrite Z_div_mult in H;
            [| generalize (Z.pow_pos_nonneg 2 (ex - ey)); lia].
          subst.
          rewrite Z.divide_div_mul_exact;
            [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
          replace (ez - ey) with ((ez - ex) + (ex - ey)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
          reflexivity.
        * (* ez < ex *)
          rename MYZ into H.
          assert (H1: ey <= ez < ex) by lia; clear EXY EYZ n l.
          left; split; [lia |].
          apply f_equal with (f := fun x => Z.div x (2 ^ (ez - ey))) in H.
          rewrite Z_div_mult in H;
            [| generalize (Z.pow_pos_nonneg 2 (ez - ey)); lia].
          subst.
          rewrite Z.divide_div_mul_exact;
            [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
          replace (ex - ey) with ((ex - ez) + (ez - ey)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
          reflexivity.
    - destruct (Z.eq_dec ex ez); subst.
      + (* ex = ez *)
        left; split; [lia |].
        rewrite Z.sub_diag; lia.
      + destruct (Z_lt_le_dec ex ez).
        * (* ex < ez *)
          assert (H : ex < ez <= ey) by lia; clear EXY EYZ n l.
          right; split; [lia |].
          rewrite <-Z.mul_assoc.
          rewrite <-Z.pow_add_r by lia.
          replace (ey - ez + (ez - ex)) with (ey - ex) by lia.
          reflexivity.
        * (* ez < ex *)
          assert (H: ez < ex <= ey) by lia; clear EXY EYZ n l.
          left; split; [lia |].
          rewrite <-Z.mul_assoc.
          rewrite <-Z.pow_add_r by lia.
          replace (ey - ex + (ex - ez)) with (ey - ez) by lia.
          reflexivity.
    - right; split; [lia |].
      rewrite <-Z.mul_assoc.
      rewrite <-Z.pow_add_r; try lia.
      replace (ez - ey + (ey - ex)) with (ez - ex) by lia.
      reflexivity.
  Qed.

  Definition float_eq_equivalence :=
    Build_Equivalence float_eq float_eq_refl float_eq_sym float_eq_trans.

  Lemma not_zero_eq (f1 f2 : float) :
    not_zero f1 ->
    float_eq f1 f2 ->
    not_zero f2.
  Proof.
    unfold not_zero, float_eq.
    destruct f1 as [m1 e1], f2 as [m2 e2]; simpl.
    intros NZ1 H.
    destruct H; destruct H as [H1 H2]; subst.
    - assert (0 < 2 ^ (e1 - e2)) by (apply Z.pow_pos_nonneg; lia).
      apply Z.neq_mul_0.
      lia.
    - intros H; contradict NZ1.
      subst; reflexivity.
  Qed.

  (** * converting between floats in the same cohort *)

  (* increase a given float's exponent by `de` *)
  Definition inc_e (f : float) (de : positive) : option float :=
    let '(m, e) := (Fnum f, Fexp f) in
    let rm := two_power_pos de in
    if (Zmod m rm =? 0)
    then Some (Float (m / two_power_pos de) (e + Z.pos de))
    else None.

  (* decrese a given float's exponent by `de` *)
  Definition dec_e (f : float) (de : positive) : float :=
    let '(m, e) := (Fnum f, Fexp f) in
    let rm := two_power_pos de in
    Float (m * two_power_pos de) (e - Z.pos de).

  (* shift (up or down) the exponent by de *)
  Definition shift_e (f : float) (de : Z) : option float :=
    match de with
    | Z0 => Some f
    | Z.pos pde => inc_e f pde
    | Z.neg nde => Some (dec_e f nde)
    end.

  (* set exponent to a given one *)
  Definition set_e (f : float) (e : Z) : option float :=
    shift_e f (e - Fexp f).

  Lemma inc_e_correct (f1 : float) (de : positive) {f2 : float} :
    inc_e f1 de = Some f2 ->
    Fexp f2 = Fexp f1 + Z.pos de.
  Proof.
    unfold inc_e.
    intro; break_match; inversion H; clear H.
    reflexivity.
  Qed.

  Lemma dec_e_correct (f : float) (de : positive) :
    Fexp (dec_e f de) = Fexp f - Z.pos de.
  Proof. reflexivity. Qed.

  Lemma shift_e_correct (f1 : float) (de : Z) {f2 : float} :
    shift_e f1 de = Some f2 ->
    Fexp f2 = Fexp f1 + de.
  Proof.
    unfold shift_e; intro; break_match; inversion H; clear H.
    lia.
    apply inc_e_correct; assumption.
    apply dec_e_correct.
  Qed.

  Lemma set_e_correct (f1 : float) (e : Z) {f2 : float} :
    set_e f1 e = Some f2 ->
    Fexp f2 = e.
  Proof.
    unfold set_e.
    intro H.
    apply shift_e_correct in H.
    lia.
  Qed.

  (* increasing/decreasing/setting an exponent preserves the float's value *)
  Lemma inc_e_eq (f1 : float) (de : positive) {f2 : float} :
    inc_e f1 de = Some f2 ->
    float_eq f1 f2.
  Proof.
    intros.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    unfold inc_e in H; break_match; inversion H; clear H.
    unfold float_eq.
    simpl in *.
    right.
    replace (e1 + Z.pos de - e1) with (Z.pos de) by lia.
    rewrite <-two_power_pos_equiv.
    remember (two_power_pos de) as rm.
    rewrite Z.eqb_eq in Heqb.
    rewrite Z.mul_comm.
    rewrite <-Z_div_exact_2 with (b := rm); try auto.
    rewrite two_power_pos_equiv in Heqrm.
    assert (0 < 2 ^ Z.pos de).
    apply Z.pow_pos_nonneg.
    all: try lia.
    subst rm.
    rewrite two_power_pos_equiv.
    generalize (Z.pow_pos_nonneg 2 (Z.pos de)).
    lia.
  Qed.

  Lemma dec_e_eq (f : float) (de : positive) :
    float_eq f (dec_e f de).
  Proof.
    destruct f as [m e].
    unfold dec_e, float_eq.
    simpl.
    left.
    replace (e - (e - Z.pos de)) with (Z.pos de) by lia.
    rewrite two_power_pos_equiv.
    split.
    lia.
    reflexivity.
  Qed.

  Lemma shift_e_eq (f1 : float) (de : Z) {f2 : float} :
    shift_e f1 de = Some f2 ->
    float_eq f1 f2.
  Proof.
    destruct de; simpl.
    - intro H; inversion H; apply float_eq_refl.
    - apply inc_e_eq.
    - intro H; inversion H; apply dec_e_eq.
  Qed.

  Lemma set_e_eq (f1 : float) (e : Z) {f2 : float} :
    set_e f1 e = Some f2 ->
    float_eq f1 f2.
  Proof.
    unfold set_e.
    apply shift_e_eq.
  Qed.

  (** exponent can always be decreased *)
  Lemma can_decrease_exponent (f : float) (e : Z) :
    e < Fexp f ->
    is_Some_b (set_e f e) = true.
  Proof.
    unfold set_e, shift_e.
    destruct f as [fm fe]; simpl; intro.
    break_match; try lia.
    reflexivity.
  Qed.

  (* binary digits of m, disregarding the sign *)
  Definition digits (m : Z) := Z.log2 (Z.abs m) + 1.

  Lemma digits_mul_pow2 (m : Z) (d : positive) :
    m <> 0 -> digits (m * two_power_pos d) = digits m + Z.pos d.
  Proof.
    intro.
    rewrite two_power_pos_equiv.
    unfold digits.
    rewrite Z.abs_mul, Z.abs_pow.
    replace (Z.abs 2) with 2 by reflexivity.
    remember (Z.abs m) as pm; remember (Z.pos d) as pd.
    rewrite Z.log2_mul_pow2.
    all: lia.
  Qed.

  Lemma Zabs_div_exact (a b : Z) :
    b <> 0 ->
    a mod b = 0 ->
    Z.abs (a / b) = Z.abs a / Z.abs b.
  Proof.
    intros B AMB.
    apply Zmod_divides in AMB; [| assumption ].
    destruct AMB as [c AMB].
    rewrite AMB at 1.
    apply f_equal with (f := Z.abs) in AMB.
    rewrite Z.abs_mul in AMB.
    rewrite AMB.
    rewrite Z.mul_comm. rewrite Z.div_mul.
    rewrite Z.mul_comm. rewrite Z.div_mul.
    all: lia.
  Qed.

  Lemma digits_div_pow2 (m : Z) (d : positive) :
    m <> 0 ->
    m mod two_power_pos d = 0 ->
    digits (m / two_power_pos d) = digits m - Z.pos d.
  Proof.
    intros M H.
    unfold digits.
    rewrite Zabs_div_exact.
    rewrite two_power_pos_equiv in *.
    rewrite Z.abs_pow.
    remember (Z.abs m) as pm; remember (Z.pos d) as pd.
    apply Zmod_divides in H; destruct H.
    subst m.
    rewrite Z.abs_mul, Z.abs_pow in Heqpm.
    replace (Z.abs 2) with 2 in * by reflexivity.
    subst pm.
    remember (Z.abs x) as px.
    rewrite Z.mul_comm.
    rewrite Z.div_mul.
    rewrite Z.log2_mul_pow2.
    all: subst.
    all: try lia.
    destruct (Z.eq_dec x 0); subst; lia.
    destruct (Z.eq_dec (2 ^ Z.pos d) 0); [ rewrite e in M; lia | assumption ].
    assert (m mod 2 ^ Z.pos d < 2 ^ Z.pos d); try lia.
    apply Zmod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
    rewrite two_power_pos_equiv; generalize (Z.pow_pos_nonneg 2 (Z.pos d)); lia.
  Qed.

  (** ** correspondence between shifting the exponent and the number of digits of the mantissa *)

  Definition inc_digits_m := dec_e.
  Definition dec_digits_m := inc_e.
  Definition shift_digits_m (f : float) (ddm : Z) := shift_e f (- ddm).
  Definition set_digits_m (f : float) (dm : Z) := shift_digits_m f (dm - digits (Fnum f)).

  Lemma inc_digits_m_correct (f : float) (ddm : positive) :
    not_zero f ->
    digits (Fnum (inc_digits_m f ddm)) = digits (Fnum f) + Z.pos ddm.
  Proof.
    unfold inc_digits_m, dec_e; simpl.
    apply digits_mul_pow2.
  Qed.

  Lemma dec_digits_m_correct (f1 : float) (ddm : positive) {f2 : float} :
    not_zero f1 ->
    dec_digits_m f1 ddm = Some f2 ->
    digits (Fnum f2) = digits (Fnum f1) - Z.pos ddm.
  Proof.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    unfold dec_digits_m, inc_e.
    simpl; intros M H.
    break_match; inversion H; clear H.
    rewrite Z.eqb_eq in Heqb.
    apply digits_div_pow2; assumption.
  Qed.

  Lemma shift_digits_m_correct (f1 : float) (ddm : Z) {f2 : float} :
    Fnum f1 <> 0 ->
    shift_digits_m f1 ddm = Some f2 ->
    digits (Fnum f2) = digits (Fnum f1) + ddm.
  Proof.
    unfold shift_digits_m, shift_e.
    simpl; intros M H.
    break_match; inversion H; clear H; subst.
    - lia.
    - replace inc_e with dec_digits_m in H1 by reflexivity.
      replace ddm with (Z.neg p) by lia.
      apply dec_digits_m_correct; assumption.
    - replace dec_e with inc_digits_m in Heqz by reflexivity.
      replace ddm with (Z.pos p) by lia.
      apply inc_digits_m_correct; assumption.
  Qed.

  Lemma set_digits_m_correct (f1 : float) (dm : Z) {f2 : float} :
    not_zero f1 ->
    set_digits_m f1 dm = Some f2 ->
    digits (Fnum f2) = dm.
  Proof.
    intros M H.
    unfold set_digits_m in H.
    apply shift_digits_m_correct in H; [| assumption].
    rewrite H.
    lia.
  Qed.

  Lemma inc_digits_m_eq (f : float) (ddm : positive) :
    float_eq f (inc_digits_m f ddm).
  Proof.
    unfold inc_digits_m.
    apply dec_e_eq.
  Qed.

  Lemma dec_digits_m_eq (f1 : float) (ddm : positive) {f2 : float} :
    dec_digits_m f1 ddm = Some f2 ->
    float_eq f1 f2.
  Proof.
    unfold dec_digits_m.
    apply inc_e_eq.
  Qed.

  Lemma shift_digits_m_eq (f1 : float) (ddm : Z) {f2 : float} :
    shift_digits_m f1 ddm = Some f2 ->
    float_eq f1 f2.
  Proof.
    unfold shift_digits_m.
    apply shift_e_eq.
  Qed.

  Lemma set_digits_m_eq (f1 : float) (dm : Z) {f2 : float} :
    set_digits_m f1 dm = Some f2 ->
    float_eq f1 f2.
  Proof.
    unfold set_digits_m.
    apply shift_digits_m_eq.
  Qed.

  Definition normalize_float (prec emax : Z) (f : float) (NZ : not_zero f) : option float :=
    let emin := 3 - emax - prec in
    match set_e f emin with
      | None => None
      | Some f1 => if digits (Fnum f1) <=? prec
                   then Some f1
                   else match set_digits_m f prec with
                       | None => None
                       | Some f2 => if andb
                                         (emin <=? Fexp f2)
                                         (Fexp f2 <=? emax - prec)
                                    then Some f2
                                    else None
                       end
    end.

  Lemma exponent_unique_fnum (f1 f2 : float) :
    float_eq f1 f2 ->
    Fexp f1 = Fexp f2 ->
    Fnum f1 = Fnum f2.
  Proof.
    unfold float_eq.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    simpl; intros H E; destruct H; destruct H as [T H]; clear T; subst.
    all: rewrite Z.sub_diag; simpl; lia.
  Qed.

  Lemma exponent_unique (f1 f2 : float) :
    float_eq f1 f2 ->
    Fexp f1 = Fexp f2 ->
    f1 = f2.
  Proof.
    intros.
    copy_apply (exponent_unique_fnum f1 f2 H) H0.
    destruct f1, f2; simpl in *.
    subst; reflexivity.
  Qed.

  Lemma digits_m_unique_fexp (f1 f2 : float) :
    not_zero f1 ->
    float_eq f1 f2 ->
    digits (Fnum f1) = digits (Fnum f2) ->
    Fexp f1 = Fexp f2.
  Proof.
    intros NZ1 H.
    assert (NZ2 : not_zero f2) by apply (not_zero_eq f1 f2 NZ1 H).
    unfold float_eq in *.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    simpl in *; intro DM; destruct H; destruct H as [H1 H2]; subst.
    all: destruct (Z.eq_dec e1 e2); try assumption.
    - assert (e2 < e1) by lia; clear H1 n.
      apply Zcompare_Gt in H.
      apply Zcompare_Gt_spec in H; destruct H as [de H].
      replace (e1 - e2) with (Z.pos de) in DM by lia.
      rewrite <-two_power_pos_equiv in DM.
      rewrite digits_mul_pow2 in DM by assumption.
      contradict DM; lia.
    - assert (e1 < e2) by lia; clear H1 n.
      apply Zcompare_Gt in H.
      apply Zcompare_Gt_spec in H; destruct H as [de H].
      replace (e2 - e1) with (Z.pos de) in DM by lia.
      rewrite <-two_power_pos_equiv in DM.
      rewrite digits_mul_pow2 in DM by assumption.
      contradict DM; lia.
  Qed.

  Lemma digits_m_unique (f1 f2 : float) :
    not_zero f1 ->
    float_eq f1 f2 ->
    digits (Fnum f1) = digits (Fnum f2) ->
    f1 = f2.
  Proof.
    intros.
    copy_apply (digits_m_unique_fexp f1 f2 H H0) H1.
    apply exponent_unique; assumption.
  Qed.

  Fact digits_Zpos_log_inf (p : positive) :
  digits (Z.pos p) = Z.succ (log_inf p).
  Proof.
    unfold digits, Z.abs.
    rewrite <-Zlog2_log_inf.
    reflexivity.
  Qed.

  Fact digits_Zneg_log_inf (p : positive) :
  digits (Z.neg p) = Z.succ (log_inf p).
  Proof.
    unfold digits, Z.abs.
    rewrite <-Zlog2_log_inf.
    reflexivity.
  Qed.
    
  Lemma valid_float_closed_form (prec emax : Z) (f : float) (NZ : not_zero f)
        (prec_gt_0 : FLX.Prec_gt_0 prec) (Hmax : prec < emax) :
    let emin := 3 - emax - prec in
    let '(m, e) := (Fnum f, Fexp f) in
      valid_float prec emax f = true
      <->
      or
        (digits m < prec /\ e = emin)
        (digits m = prec /\ emin <= e <= emax - prec).
  Proof.
    destruct f as [m e].
    intro.
    unfold FLX.Prec_gt_0 in prec_gt_0.
    unfold valid_float.
    simpl.
    destruct m.
    - (* Z0 *)
      unfold not_zero in NZ; simpl in NZ.
      contradict NZ.
      reflexivity.
    - (* Zpos *)
      rewrite bounded_unfolded by assumption;
        rewrite digits_Zpos_log_inf;
        unfold compose.
      split; intros H; destruct H; auto.
    - (* Zneg *)
      rewrite bounded_unfolded by assumption.
        rewrite digits_Zneg_log_inf;
        unfold compose.
      split; intros H; destruct H; auto.
  Qed.

  Lemma not_None_iff_exists_Some {A : Type} {x : option A} :
    x <> None <-> exists y, x = Some y.
  Proof.
    split; intro.
    - destruct x.
      + exists a; reflexivity.
      + contradict H; reflexivity.
    - destruct H; subst; discriminate.
  Qed.

  Lemma valid_float_superset (prec emax : Z) (f : float) :
    valid_float prec emax f = true ->
    Fexp f = 3 - emax - prec \/ digits (Fnum f) = prec.
  Proof.
    intros.
  Admitted.

  Lemma float_eq_trans_l (f1 f2 f3 : float) :
    float_eq f1 f2 ->
    float_eq f1 f3 ->
    float_eq f2 f3.
  Proof.
    intros EQ12 EQ13.
    apply float_eq_sym in EQ12.
    apply float_eq_trans with (y := f1);
      assumption.
  Qed.

  Lemma float_eq_trans_r (f1 f2 f3 : float) :
    float_eq f2 f1 ->
    float_eq f3 f1 ->
    float_eq f2 f3.
  Proof.
    intros EQ12 EQ13.
    apply float_eq_sym in EQ13.
    apply float_eq_trans with (y := f1);
      assumption.
  Qed.

  Lemma float_eq_set_e (f1 f2 : float) :
    float_eq f1 f2 ->
    set_e f1 (Fexp f2) = Some f2.
  Proof.
    intro.
    destruct set_e eqn:SE.
    - (* if successful, then equal *)
      copy_apply set_e_eq SE; rename H0 into H1.
      apply set_e_correct in SE.
      apply (float_eq_trans_l f1 f f2 H1) in H.
      apply (exponent_unique f f2 H) in SE.
      subst; reflexivity.
    - (* always successful *)
      exfalso.
      unfold float_eq, set_e, shift_e, inc_e, dec_e in *.
      destruct f1 as [m1 e1], f2 as [m2 e2]; simpl in *.
      repeat break_match; try discriminate.
      clear SE; rename Heqb into H1.
      apply Z.eqb_neq in H1.
      destruct H; destruct H as [E M]; [lia |]; subst.
      rewrite two_power_pos_equiv in H1.
      rewrite Z.mod_mul in H1; auto.
      generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
  Qed.

  Lemma float_eq_set_digits_m (f1 f2 : float) :
    not_zero f1 ->
    float_eq f1 f2 ->
    set_digits_m f1 (digits (Fnum f2)) = Some f2.
  Proof.
    intros NZ1 H.
    assert (NZ2 : not_zero f2) by apply (not_zero_eq f1 f2 NZ1 H).
    destruct set_digits_m eqn:SDM.
    - (* if successful, then equal *)
      copy_apply set_digits_m_eq SDM; rename H0 into H1.
      apply set_digits_m_correct in SDM; auto.
      apply (float_eq_trans_l f1 f f2 H1) in H.
      assert (NZ: not_zero f) by (apply not_zero_eq with (f1 := f1); assumption).
      apply (digits_m_unique f f2 NZ H) in SDM.
      subst; reflexivity.
    - (* always successful *)
      exfalso.
      unfold float_eq, set_digits_m, shift_digits_m, shift_e, inc_e, dec_e in *.
      destruct f1 as [m1 e1], f2 as [m2 e2]; simpl in *.
      repeat break_match; try discriminate.
      clear SDM; rename Heqb into H1.
      apply Z.eqb_neq in H1.
      destruct H; destruct H as [E M]; subst.
      + destruct (Z.eq_dec e1 e2).
        replace (e1 - e2) with 0 in Heqz by lia;
          rewrite Z.mul_1_r in Heqz; lia.
        assert (e2 < e1) by lia; clear E n.
        apply Zcompare_Gt in H.
        apply Zcompare_Gt_spec in H; destruct H.
        replace (e1 - e2) with (Z.pos x) in *.
        rewrite <-two_power_pos_equiv in *.
        rewrite digits_mul_pow2 in Heqz.
        lia.
        auto.
      + destruct (Z.eq_dec e1 e2).
        replace (e2 - e1) with 0 in Heqz by lia;
          rewrite Z.mul_1_r in Heqz; lia.
        assert (e1 < e2) by lia; clear E n.
        apply Zcompare_Gt in H.
        apply Zcompare_Gt_spec in H; destruct H.
        replace (e2 - e1) with (Z.pos x) in *.
        rewrite <-two_power_pos_equiv in *.
        rewrite digits_mul_pow2 in Heqz.
        assert (x = p) by lia; subst.
        rewrite two_power_pos_equiv in H1.
        rewrite Z.mod_mul in H1; auto.
        generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
        auto.
  Qed.

  Lemma set_e_definition (f1 : float) (e : Z) {f2 : float} :
    set_e f1 e = Some f2 <->
    float_eq f1 f2 /\ Fexp f2 = e.
  Proof.
    split; intro.
    - split.
      apply (set_e_eq f1 e H). apply (set_e_correct f1 e H).
    - destruct H as [EQ FEXP].
      subst.
      apply (float_eq_set_e f1 f2 EQ).
  Qed.

  Lemma set_digits_m_definition (f1 : float) (dm : Z) {f2 : float} :
    not_zero f1 ->
    set_digits_m f1 dm = Some f2 <->
    float_eq f1 f2 /\ digits (Fnum f2) = dm.
  Proof.
    intros NZ1.
    split; intro.
    - split.
      apply (set_digits_m_eq f1 dm H).
      apply (set_digits_m_correct f1 dm NZ1 H).
    - destruct H as [EQ FEXP].
      subst.
      apply (float_eq_set_digits_m f1 f2 NZ1 EQ).
  Qed.
  
  Theorem normalize_correct (prec emax : Z) (f : float) (NZ : not_zero f)
        (prec_gt_0 : FLX.Prec_gt_0 prec) (Hmax : prec < emax) :
    match (normalize_float prec emax f NZ) with
    | Some nf => (float_eq f nf) /\ (valid_float prec emax nf = true)
    | None => forall (xf : float),
        float_eq f xf -> valid_float prec emax xf = false
    end.
  Proof.
    unfold FLX.Prec_gt_0 in prec_gt_0.
    break_match. rename f0 into nf.
    - (* successful normalization - equal and valid? *)
      unfold normalize_float in Heqo.
      repeat break_match; inversion Heqo; subst.
      + (* subnormal *)
        split.
        * (* same float? *)
          apply set_e_eq with (e := 3 - emax - prec).
          assumption.
        * (* valid float? *)
          apply Z.leb_le in Heqb.
          rewrite valid_float_closed_form.
          apply set_e_correct in Heqo0.
          lia.
          apply not_zero_eq with (f1 := f). assumption.
          apply set_e_eq in Heqo0. assumption.
          unfold FLX.Prec_gt_0; lia.
          assumption.
      + (* normal *)
        split.
        * (* same float? *)
          apply set_digits_m_eq with (dm := prec).
          assumption.
        * (* valid float? *)
          apply andb_prop in Heqb0; destruct Heqb0 as [H1 H2].
          apply Z.leb_le in H1; apply Z.leb_le in H2.
          rewrite valid_float_closed_form.
          right.
          apply set_e_correct in Heqo0.
          apply set_digits_m_correct in Heqo1.
          lia.
          assumption.
          apply not_zero_eq with (f1 := f). assumption.
          apply set_digits_m_eq in Heqo1. assumption.
          unfold FLX.Prec_gt_0; lia.
          assumption.
    - (* unsuccesful normalization - impossible to normalize? *)
      intros xf H.
      apply Bool.not_true_is_false.
      intros V.
      (* TODO: probably no need to copy *)
      copy_apply valid_float_superset V; rename H0 into S.
      destruct S as [S | S].
      + (* xf is normal *)
        unfold normalize_float in Heqo.
        repeat break_match; try discriminate.
        * clear Heqo.
          clear Heqo0 Heqb f0.
          remember (3 - emax - prec) as emin.
          copy_apply (not_zero_eq) H; [| assumption].
          apply set_digits_m_definition in Heqo1; [| assumption]; destruct Heqo1.
          copy_apply (float_eq_trans_l f f1 xf H1) H.
          assert (f1 = xf).
          apply digits_m_unique.
  Admitted.
  
End normalization.
