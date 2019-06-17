(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)

From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

(* Specification of the strlen function *)

(* size_t *)
Proposition int_ptrofs_mod_eq : (Int.modulus = Ptrofs.modulus).
Proof.
  vm_compute. auto.
Qed.

Proposition ptrofs_mod_1_0 : 0 <= 1 < Ptrofs.modulus.
Proof.
  cbv. destruct Archi.ptr64; split; congruence.
Qed.

Definition Int_succ := fun i : int => Int.add i Int.one.
Definition Ptrofs_succ := fun p : ptrofs => Ptrofs.add p Ptrofs.one.

(* Int.int type is 32b integer type *) 

Inductive strlen (m : mem) (b : block) (ofs : ptrofs) : int -> Prop :=
| LengthZeroMem_int: Mem.loadv Mint8unsigned m (Vptr b ofs) = Some (Vint Int.zero) -> strlen m b ofs Int.zero
| LengthSuccMem_int: forall n c,
    strlen m b (Ptrofs.add ofs Ptrofs.one) n ->
    Mem.loadv Mint8unsigned m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen m b ofs (Int_succ n).

(* strlen C light AST *)

Definition _output : ident := 4%positive.
Definition _input : ident := 3%positive.
Definition _t'1 : ident := 7%positive.
Definition _t'2 : ident := 8%positive.

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_input, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_output, tuint) :: (_t'1, (tptr tuchar)) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _output (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tuchar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar))
            (Sifthenelse (Etempvar _t'2 tuchar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip)
    (Sreturn (Some (Etempvar _output tuint)))))
                          |}.

Definition f_strlen_loop :=
  (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tuchar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar))
            (Sifthenelse (Etempvar _t'2 tuchar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip).

(* Our goal is to prove that the C light AST is equivalent satisfies the spec: in this context it means that the C light AST evaluates to the correct value wrt to big step operational semantics *)

(* Some useful notation and tactics *)

Definition chunk : memory_chunk := Mint8unsigned.
Definition VintZ := fun (z : Z) => Vint (Int.repr z).
Definition VintN:= fun n => Vint (Int.repr(Z_of_nat n)).

Notation gso := PTree.gso.
Notation gss := PTree.gss.

Ltac seq1 := eapply exec_Sseq_1.
Ltac seq2 := eapply exec_Sseq_2.
Ltac sset := eapply exec_Sset.
Ltac loop := eapply exec_Sloop_loop.

Proposition char_not_zero : forall c, c <> Int.zero -> true = (negb (Int.eq c Int.zero)).
Proof.
  intros.
  replace (Int.eq c Int.zero) with false.
  auto.
  rewrite Int.eq_false; intuition.
Qed.  

 (* add more lemmas from Compcert to ptrofs hints *)

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.

(* Induction principle for integers *)

Lemma int_induction : forall (P : int -> Prop), P Int.zero ->
                                       (forall i, P i -> P (Int.add i Int.one)) -> forall i, P i.
Proof.
  induction i.
  generalize intrange.
  eapply (natlike_ind (fun intval0 => forall intrange0 : -1 < intval0 < Int.modulus,
                           P {| Int.intval := intval0; Int.intrange := intrange0 |}) ).
  (* Base case *)
  - intro.
  unfold Int.zero in H.
  assert ((Int.repr 0) = {| Int.intval := 0; Int.intrange := intrange0 |}).
  assert (Int.unsigned {| Int.intval := 0; Int.intrange := intrange0 |} = Int.unsigned  (Int.repr (0))).
  { simpl.
  rewrite Int.unsigned_repr.
  auto.
  unfold Int.max_unsigned.
  nia. }
  
  destruct (Int.repr 0) eqn: S0.
  apply Int.mkint_eq.
  simpl in H1.
  nia.
  
  rewrite  H1 in H.
  assumption.
  -
  intros.
  assert (-1 < x < Int.modulus) by nia.
  pose (H2 H3).
  pose (H0 {| Int.intval := x; Int.intrange := H3 |} p).
  assert (  {| Int.intval := Z.succ x; Int.intrange := intrange0 |} =  (Int.add {| Int.intval := x; Int.intrange := H3 |}
                                                                                Int.one)  ).
  unfold Int.add.
  unfold Int.one.
  unfold Int.unsigned.
  replace (Int.intval (Int.repr 1)) with 1 by (auto with ints).
  simpl.
  replace (x + 1) with (Z.succ x) by nia.
  assert (Int.unsigned {| Int.intval := Z.succ x; Int.intrange := intrange0 |} = Int.unsigned
                                                                                   (Int.repr (Z.succ x))).
  simpl.
  Search Int.repr.
  rewrite Int.unsigned_repr.
  auto.
  unfold Int.max_unsigned.
  nia.

  destruct (Int.repr (Z.succ x)) eqn: Sa.
  apply Int.mkint_eq.
  simpl in H4.
  assumption.
  rewrite <- H4 in p0.
  assumption.
  -  nia.
Qed.

Lemma intval_eq : forall (n i : int), match  n with
       | {| Int.intval := intval |} => intval
       end =
        match i with
       | {| Int.intval := intval |} => intval
       end ->  (n = i).
  intros.
   destruct (n) eqn: Sn.
     destruct (i) eqn: Si. 
      apply Int.mkint_eq.
      assumption.
Qed.

Lemma strlen_to_len_0 : forall len m b ofs, strlen m b ofs len -> strlen m b (Ptrofs.add ofs (Ptrofs.of_int len)) Int.zero.
Proof.
  induction len using int_induction; intros until ofs; intros Spec.
  - replace (Ptrofs.add ofs (Ptrofs.of_int Int.zero)) with ofs by (auto with ptrofs).
    assumption.
  - inversion Spec.
    + pose (E := intval_eq Int.zero (Int.add len Int.one) H).
      rewrite <- E in *.
      replace (Ptrofs.add ofs (Ptrofs.of_int Int.zero)) with ofs by (auto with ptrofs).
      assumption.
    + unfold Int_succ in *.
      pose (E := intval_eq (Int.add n Int.one) (Int.add len Int.one) H).
      assert (n = len) as Nlen.
      { destruct (Int.eq_dec n len).
        assumption.
        pose (Int.eq_false n len n0) as e.
        pose (Int.translate_eq n len Int.one) as e0.
        rewrite e in e0.
        pose (Int.eq_spec (Int.add n Int.one) (Int.add len Int.one)) as y.
        rewrite e0 in y.
        congruence.
      }
       rewrite Nlen in H0.
          replace (Ptrofs.add ofs (Ptrofs.of_int (Int.add len Int.one))) with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (Ptrofs.of_int len)).
     
      apply (IHlen m b (Ptrofs.add ofs Ptrofs.one) H0).
      {
        rewrite Ptrofs.add_assoc.
        f_equal.
        symmetry.
        apply Ptrofs.agree32_of_int_eq.
        rewrite Ptrofs.add_commut.
        apply Ptrofs.agree32_add.
        vm_compute. auto.
        auto with ptrofs.
        unfold Ptrofs.one.
        unfold Int.one.
        auto with ptrofs. }
Qed.


Hypothesis no_overflow_pointer_addition : forall i j, 0 < Ptrofs.unsigned i + Ptrofs.unsigned j < Ptrofs.modulus.

Hypothesis no_overflow_int_addition : forall i j, 0 < Int.unsigned i + Int.unsigned j < Int.modulus.
(* Proof. 
  intros.
  (* pose (no_overflow_pointer_addition (Ptrofs.repr i) (Ptrofs.repr j)).
  assert (Ptrofs.agree32 (Ptrofs.of_int i) i) by (auto with ptrofs).
  assert (Ptrofs.agree32 (Ptrofs.of_int j) j) by (auto with ptrofs).
    Search Ptrofs.agree32.
  unfold Ptrofs.agree32 in H.
  unfold Ptrofs.agree32 in H0.
  rewrite <- H. rewrite <- H0.
  Check Ptrofs.agree32_of_int_eq. *)
  
  Admitted. *)

Lemma unsigned_to_add : forall z, 0 < Int.unsigned z + 1 < Int.modulus ->
                       Int.add z Int.one <> Int.zero.
  intros.

  unfold Int.zero.
  destruct (Int.eq (Int.add z Int.one) (Int.repr 0)) eqn: Sz.
  pose (Int.eq_spec (Int.add z Int.one) (Int.repr 0)) as E.
  unfold Int.eq in Sz.
  destruct (zeq (Int.unsigned (Int.add z Int.one))
                (Int.unsigned (Int.repr 0))).
  unfold Int.add in e.
  repeat rewrite Int.unsigned_repr_eq in e.
  rewrite Zmod_small in e.
  rewrite  Zmod_small in e.
  replace (Int.unsigned Int.one) with 1 in e by (auto with ints).  nia.
  nia.
  replace (Int.unsigned Int.one) with 1 by (auto with ints).  nia.
  congruence.
  pose (Int.eq_spec (Int.add z Int.one)  (Int.repr 0)).
  rewrite Sz in y.
  assumption.
  
Qed.

(* Lemma no_pointer_overflow : forall p, not ((Ptrofs_succ p) = Ptrofs.zero).
Proof.
  Admitted. *)

Lemma no_int_overflow : forall i, not (Int_succ i = Int.zero).
Proof.
  intro.
  apply unsigned_to_add.
  pose (no_overflow_int_addition i Int.one).
  replace (Int.unsigned Int.one) with 1 in a by (auto with ints).
  assumption.
Qed.


Lemma int_add_surj : forall i j, Int.unsigned (Int.add i j) = Int.unsigned i + Int.unsigned j.
  intros.
  unfold Int.add.
  rewrite Int.unsigned_repr_eq.
  replace (Int.unsigned Int.one) with 1 by (auto with ints).
  pose ( no_overflow_int_addition i j).
  rewrite Zmod_small.
  auto.
  nia.
  Qed.

  
(* This doesn't hold for a spec with wrapping. Counterexample: Int_succ i = Int.zero, there is an empty string at ofs and another empty string after it *)

Lemma impl_spec : forall i m b ofs, strlen m b ofs (Int_succ i) -> strlen m b (Ptrofs.add ofs Ptrofs.one) i.
Proof.
  intros until ofs; intro H.
  inversion H.
  - pose (intval_eq Int.zero (Int_succ i) H0).
    pose (no_int_overflow i).
    congruence. 
  -  assert (E: Int_succ n = Int_succ i) by (eapply (intval_eq (Int_succ n) (Int_succ i) H0)). 
     assert (J : n = i).
   
    { destruct (Int.eq_dec n i).
      assumption.
      pose (Int.eq_false n i n0).
      pose (Int.translate_eq n i Int.one).
      rewrite e in e0.
      Search Int.eq.
      pose (Int.eq_spec (Int.add n Int.one) (Int.add i Int.one)).
      rewrite e0 in y.
      unfold Int_succ in E.
      congruence.
    }
    rewrite <- J.
    assumption.
Qed.

    Lemma strlen_to_mem : forall len m b ofs,
    
    strlen m b ofs len ->
    forall i, 0 <= i -> i < Int.unsigned len -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr i))) = Some (Vint c) /\ c <> Int.zero.
  Proof.
    induction len using int_induction.
    - (* Base case len *)
      intros until ofs.
      intros Spec.
      intros i Prec1 Prec2.
      replace (Int.unsigned Int.zero) with 0 in Prec2 by (auto with ints).
      nia.
     
  - (* I.S. len *)
    intros until ofs.  intro Spec.
    apply (natlike_ind (fun i => i < Int.unsigned (Int.add len Int.one) ->
  exists c : int,
    Mem.loadv chunk m
      (Vptr b (Ptrofs.add ofs (Ptrofs.repr i))) =
    Some (Vint c) /\ c <> Int.zero)).
      + (* Base case i *)
        intro Ltu.
        inversion Spec.
        * pose (intval_eq Int.zero (Int.add len Int.one) H).
          pose (no_int_overflow len).
          unfold Int_succ in n.
          congruence.
        *  
          replace (Ptrofs.add ofs (Ptrofs.repr 0)) with ofs by (auto with ptrofs).
          exists c.  apply (conj H1 H2).  
      + (* I.S. i *)
        intros.
        pose (impl_spec  _ _ _ _ Spec) as Spec_impl.
        pose (IHlen m b (Ptrofs.add ofs Ptrofs.one) Spec_impl x) as IHip.
        replace (Ptrofs.add ofs (Ptrofs.repr (Z.succ x)))  with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one)
               (Ptrofs.repr x)).
        apply IHip.
        * assumption.
        * rewrite int_add_surj in H1.
          replace (Int.unsigned Int.one) with 1 in H1 by (auto with ints).
          nia.
          
        * 
          rewrite Ptrofs.add_assoc.
          f_equal.
          unfold Ptrofs.add.
          unfold Ptrofs.one.
          rewrite Ptrofs.unsigned_repr_eq.
          f_equal.
          rewrite Zmod_small.
          rewrite Ptrofs.unsigned_repr_eq.
          rewrite Zmod_small.
          nia.
          rewrite int_add_surj in H1.
          replace (Int.unsigned Int.one) with 1 in H1 by (auto with ints).
          assert (Int.unsigned len < Ptrofs.modulus).
          pose int_ptrofs_mod_eq.
          destruct len.
          simpl.
          nia.
          nia.
          apply ptrofs_mod_1_0.
          
Qed. (* one goal admitted *)
       
(* Correctness statements *)

Lemma strlen_to_mem_0 : forall m b ofs, strlen m b ofs Int.zero -> Mem.loadv Mint8unsigned m (Vptr b ofs) = Some (Vint Int.zero).
  Proof.
    intros.
    inversion H.
    * assumption.
    * pose (intval_eq (Int_succ n) Int.zero H0) as A.
      pose (no_int_overflow n).
       congruence.
  Qed.
   
(* A generalization of loop correctness *)

Lemma strlen_loop_correct_gen :
  forall len i ge e m b ofs le,
    
    (* we read a C string of length len + i from memory and len + i is a valid integer *)
   
    strlen m b ofs (Int.add len i) ->
    
    (* THEN there is a trace t and local environment le' such that: *)
    exists t le',
      (* if output equals i in the starting local environment le *)
      le!_output = Some (Vint i) ->
      (* if input is an address [b,ofs + i] in the starting local environment *)
      le!_input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) ->     (* then loop of strlen function executes to le' with output assigned len + i *)
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (Vint (Int.add len i)).
  Proof.
  induction len using int_induction; intros until le; intros Spec.
  - (* Base case *)
    replace  (Int.add Int.zero i) with i in *.
    pose (Spec_mem := strlen_to_len_0 i  m b ofs Spec).
    pose (Spec_mem0 := strlen_to_mem_0  m b (Ptrofs.add ofs (Ptrofs.of_int i)) Spec_mem).
   
    repeat eexists.
      (* Exit the loop *)
      eapply exec_Sloop_stop1. seq2. repeat econstructor.
      apply H0.
      eapply gss.
      repeat econstructor.
      rewrite gso. apply gss. cbv. congruence.
      apply Spec_mem0.
      apply gss.
      econstructor.
      replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).      
      econstructor.
      cbv; congruence. econstructor.
      repeat (rewrite gso).
      assumption.
      1-3: cbv; congruence.
    { rewrite Int.add_commut. rewrite Int.add_zero. auto. }
   
  - (* Ind. Step *)
    
    assert (exists char, Mem.loadv Mint8unsigned m (Vptr b  (Ptrofs.add ofs (Ptrofs.of_int i))) = Some (Vint char) /\ char <> Int.zero) as Mem.
    { refine (strlen_to_mem (Int.add (Int.add len Int.one) i) m b ofs Spec (Int.unsigned i) _ _).
      destruct i.
      simpl.
      nia.
      rewrite int_add_surj.
      rewrite int_add_surj.
      destruct i.
      destruct len.
      simpl.
      replace (Int.unsigned Int.one) with 1 by (auto with ints).
      nia.
   }
    destruct Mem as [char Mem].
    (* apply I.H. to le' after one step when starting with i and [b,ofs + i]  *)
    pose (le'' := (PTree.set _output (Vint (Int.add i (Int.repr 1)))
       (PTree.set _t'2 (Vint char)
          (PTree.set _input (Vptr b  (Ptrofs.add ofs (Ptrofs.of_int (Int.add i Int.one))))
             (PTree.set _t'1 (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) le))))).
    pose (IH := IHlen (Int.add i Int.one) ge e m b ofs le'' ).
    assert ( exists (t : trace) (le' : temp_env),
       le'' ! _output = Some (Vint (Int.add i Int.one)) ->
       le'' ! _input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.of_int (Int.add i Int.one)))) ->
       exec_stmt ge e le'' m f_strlen_loop t le' m Out_normal /\
       le' ! _output = Some (Vint (Int.add len (Int.add i Int.one)))) as Step.
    { eapply IH;
        replace (Int.add len (Int.add i Int.one)) with (Int.add (Int.add len Int.one) i).
      
      
      
      assumption.
      rewrite Int.add_assoc.
      f_equal.
      rewrite Int.add_commut.
      auto. }
    destruct Step as [s Step]. destruct Step as [t Step]. 
    (* Do one loop on the goal: then apply IH *)
    repeat eexists.
    loop. repeat econstructor.
    apply H0.
    eapply gss. 
    repeat econstructor.
    rewrite gso. apply gss. cbv; congruence.
    simpl.
    apply Mem.
    apply gss.
    econstructor.
    replace (negb (Int.eq char Int.zero)) with true by (apply (char_not_zero char); apply Mem).
    econstructor. 
    repeat (rewrite gso). apply H. 1-3: cbv; congruence.
    repeat econstructor. econstructor. econstructor.
    fold f_strlen_loop.
    replace (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
                        (ptrofs_of_int Signed (Int.repr 1))) with Ptrofs.one by (auto with ptrofs).
    
    replace  (PTree.set _output (Vint (Int.add i (Int.repr 1)))
       (PTree.set _t'2 (Vint char)
          (PTree.set _input (Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.of_int i)) Ptrofs.one))
             (PTree.set _t'1 (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) le)))) with le''.
  eapply Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso.
  apply gss.
  1-2: cbv; congruence.

  {  
    unfold le''.
    replace (Ptrofs.add (Ptrofs.add ofs (Ptrofs.of_int i)) Ptrofs.one) with (Ptrofs.add ofs (Ptrofs.of_int (Int.add i Int.one))).
    reflexivity.
    pose (Int64.int_unsigned_repr).
     rewrite Ptrofs.add_assoc.
     f_equal.
     apply Ptrofs.agree32_of_int_eq.
     apply Ptrofs.agree32_add.
     vm_compute; auto.
     auto with ptrofs.
     auto with ptrofs.
     unfold Ptrofs.one.
     unfold Int.one.
     auto with ptrofs.
      }
      
  destruct Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.
  replace (Int.add (Int.add len Int.one) i) with (Int.add len (Int.add i Int.one)). 
  assumption.
  { rewrite Int.add_assoc.
      f_equal.
      rewrite Int.add_commut.
      auto. }
Qed.      

(* Correctness of the loop execution *)  
Lemma strlen_loop_correct: forall len ge e m b ofs le, strlen m b ofs len -> exists t le', le!_output = Some (Vint Int.zero) ->
                                                                                    le!_input = Some (Vptr b ofs) ->
      
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (Vint len).
Proof.
  intros.
  replace ofs with (Ptrofs.add ofs (Ptrofs.of_int Int.zero)) by (auto with ptrofs).
  replace len with (Int.add len Int.zero).
  eapply strlen_loop_correct_gen.
  replace (Int.add len Int.zero) with len.
  assumption.
  rewrite Int.add_commut.
  rewrite Int.add_zero_l.
  auto.
  rewrite Int.add_commut.
  rewrite Int.add_zero_l.
  auto.
Qed.
  
(* Full correctness statement *)
Lemma strlen_correct: forall len ge e m b ofs le, strlen m b ofs len -> exists t le', le!_input = Some (Vptr b ofs) ->
                                                                               exec_stmt ge e le  m f_strlen.(fn_body) t le' m (Out_return (Some ((Vint len),tuint))).
Proof.
  intros.
  pose (Loop := strlen_loop_correct len ge e  _ _ _ (PTree.set _output (Vint Int.zero) le) H). destruct Loop as [t Loop]. destruct Loop as [le' Loop].
  repeat eexists.
  intro input.
  assert ((PTree.set _output (Vint Int.zero) le) ! _output =
          Some (Vint Int.zero)) as O by (apply gss).
  assert ((PTree.set _output (Vint Int.zero) le) ! _input =
          Some (Vptr b ofs)) as I.
  { rewrite gso. assumption. cbv; congruence. }
  destruct (Loop O I) as [Exec Out].
  seq1. 
  repeat econstructor.
  seq1. fold f_strlen_loop.
  eapply Exec.
  repeat econstructor.
  eapply Out.
Qed.
