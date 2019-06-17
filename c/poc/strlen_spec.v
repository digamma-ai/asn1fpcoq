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

(* Tactics for arithmetic on ptrofs, now they are ad hoc, TODO: automatize translation from ptrofs to Z *)

Ltac ints_to_Z :=
  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_to_Z :=
  repeat rewrite Ptrofs.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_compute_add_mul :=
      simpl; unfold Ptrofs.add; unfold Ptrofs.mul; unfold Ptrofs.of_intu; unfold Ptrofs.of_int;
      repeat rewrite Ptrofs.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ints_compute_add_mul :=
      simpl; unfold Int.add; unfold Int.mul;
      repeat rewrite Int.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac seq1 := eapply exec_Sseq_1.
Ltac seq2 := eapply exec_Sseq_2.
Ltac sset := eapply exec_Sset.
Ltac loop := eapply exec_Sloop_loop.

(* can make more generic to repeatedly apply gso *)
Ltac gso_assumption :=
  match goal with
  | [ H : ?P ! ?I = Some ?W |- (PTree.set _ _ ?P) ! ?I = Some ?Z ] => rewrite gso  
  | [ H : ?P ! ?Q = Some ?W |-  ?P ! ?Q = Some ?Z ] => apply H
  | [ |- _ <> _ ] => cbv ; congruence
  end.

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

Definition MaxInt (i : int) := Int_succ i = Int.zero.
Definition MaxPtrofs (p : ptrofs) := Ptrofs_succ p = Ptrofs.zero.
  
Lemma strlen_to_mem_int : forall len m b ofs,
    strlen m b ofs len ->
    Ptrofs.unsigned ofs + Int.unsigned len < Ptrofs.modulus ->
    forall i, Int.unsigned i < Int.unsigned len -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) = Some (Vint c) /\ c <> Int.zero.
  Proof.
    induction len using int_induction.
    - (* Base case len *)
      intros until ofs.
      intros Spec Bound.
      unfold Int.zero in *.
      intros i Prec.               
      rewrite Int.unsigned_repr in Prec.
      destruct i.
      simpl in Prec.
      nia.
      unfold Int.max_unsigned.
      vm_compute. 
      split; congruence. 
  - (* I.S. len *)
    intros until ofs.  intros Spec Bound.
    induction i using int_induction.
      + (* Base case i *)
        intro Ltu.
        inversion Spec.
        * pose (intval_eq Int.zero (Int.add len Int.one)).
        replace (Ptrofs.add ofs (Ptrofs.zero)) with ofs by (auto with ptrofs).
          exists c. apply (conj H2 H3).
          * admit.
      + (* I.S. i *)
        intros.
        assert (Int_succ len <> Int.zero) as B by admit.
        pose (impl_spec _ _ _ _ B Spec) as Spec_impl.
        pose (IHlen m b (Ptrofs.add ofs Ptrofs.one) Spec_impl i) as IHip.
        replace (Ptrofs.add ofs (Ptrofs.add i Ptrofs.one))  with  (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) i).
        apply IHip.
        unfold Ptrofs.add in H.
        * (* Int.ltu i len = true : follows from H0 and H1 *) admit.     * assumption.
        * (* Int_succ i <> Int.zero : follows from Int_succ (Int.add i Int.one) <> Int.zero *) admit.
        * assert (Int_succ i <> Int.zero) as J by admit.
          pose (non_zero_lt_mod1 _  J).
          rewrite Ptrofs.add_assoc.
          f_equal.
          assert (Int.unsigned i < Int.modulus).
          destruct i.
          simpl.
          apply intrange.
          Search Ptrofs.of_int.
          unfold Ptrofs.of_int.
          unfold Ptrofs.add.
          f_equal.
          rewrite Ptrofs.unsigned_repr_eq.
          rewrite Zmod_small.
          unfold Int.add.
          rewrite Int.unsigned_repr_eq.
          Print Ptrofs.agree32.
          Search Ptrofs.agree32.
          unfold Int_succ in l.
          unfold Int.add in l.
          rewrite Int.unsigned_repr_eq in l.
          rewrite Zmod_small in l.
          replace (Int.unsigned Int.one) with 1 in l by (auto with ints). 
          nia.
          
          rewrite Ptrofs.add_commut.
          apply Ptrofs.agree32_of_int_eq.
          Search Ptrofs.agree32.
          apply Ptrofs.agree32_add.
          admit. (* Archi.ptr64 = false *)
          auto with ptrofs.
          unfold Ptrofs.one.
          unfold Int.one.
          auto with ptrofs.
Admitted.
       
(* Correctness statements *)

Lemma strlen_to_mem_0 : forall len m b ofs, strlen m b (Ptrofs.add ofs (Ptrofs.of_int len)) Int.zero -> Mem.loadv Mint8unsigned m (Vptr b (Ptrofs.add ofs (Ptrofs.of_int len))) = Some (Vint Int.zero).
  Proof.
    intros.
    inversion H.
    * assumption.
    * pose (intval_eq_0 n  H0) as A.
       congruence.
   Qed.
              

(* A generalization of loop correctness *)

Lemma strlen_loop_correct_gen :
  forall len i ge e m b ofs le,
    (* we read a C string of length len + i from memory and len + i is a valid integer *)
    Int.add (Int.add len i) Int.one <> Int.zero ->  
   
    strlen m b ofs (Int.add len i) ->
    
    (* THEN there is a trace t and local environment le' such that: *)
    exists t le',
      (* if output equals i in the starting local environment le *)
      le!_output = Some (Vint i) ->
      (* if input is an address [b,ofs + i] in the starting local environment *)
      le!_input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) ->     (* then loop of strlen function executes to le' with output assigned len + i *)
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (Vint (Int.add len i)).
  Proof.
    assert  (Archi.ptr64 = false) as K by admit.
  induction len using int_induction; intros until le; intros Bound Spec.
  - (* Base case *)
    
    replace  (Int.add Int.zero i) with i in *.
    pose (Spec_mem := strlen_to_len_0 i m b ofs Bound Spec).
    pose (Spec_mem0 := strlen_to_mem_0 i m b ofs Spec_mem).
   
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
    { refine (strlen_to_mem_int (Int.add (Int.add len Int.one) i) m b ofs Spec i _). (* i < i + len + 1 *) admit. }
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
      auto.
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
    simpl. ptrofs_to_Z.
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
     Search Ptrofs.of_int.
     apply Ptrofs.agree32_of_int_eq.
     Search Ptrofs.agree32.
     apply Ptrofs.agree32_add.
     assumption.
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
Admitted.      

(* On empty string C light function evaluates to 0 *)

Lemma strlen_correct_loop_empty_string :
  forall ge e m b ofs le,                                           
    strlen m b ofs Int.zero ->

    exists t le',
      le!_output = Some (Vint Int.zero) ->
      le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (Vint Int.zero).
Proof.
  intros.
  replace O with (0 + 0)%nat by lia.
  replace ofs with (Ptrofs.add ofs Ptrofs.zero) by (auto with ptrofs).
  eapply strlen_loop_correct_gen.
  simpl.
  assumption.
Qed.    

(* Correctness of the loop execution *)
Lemma strlen_loop_correct: forall len ge e m b ofs le, strlen_mem m b ofs len -> exists t le', le!_output = Some (VintN O) ->
                                                                                    le!_input = Some (Vptr b ofs) ->
      
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN len).
Proof.
  intros.
  replace ofs with (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat O))) by (auto with ptrofs).
  replace len with (len + O)%nat by lia.
  eapply strlen_loop_correct_gen.
  replace (len + O)%nat with len by omega.
  assumption.
Qed.
  
(* Full correctness statement *)
Lemma strlen_correct: forall len ge e m b ofs le, strlen_mem m b ofs len -> exists t le', le!_input = Some (Vptr b ofs) ->
                                                                               exec_stmt ge e le  m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN len),tuint))).
Proof.
  intros.
  pose (Loop := strlen_loop_correct len ge e  _ _ _ (PTree.set _output (Vint Int.zero) le) H). destruct Loop as [t Loop]. destruct Loop as [le' Loop].
  repeat eexists.
  intro input.
  assert ((PTree.set _output (Vint Int.zero) le) ! _output =
          Some (VintN 0)) as O by (apply gss).
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

(* Conditions about the f_strlen loop: maybe keep as an illustration *)

(* If 0 is read from memory at [b,ofs + len] the output is set to len *)
Lemma strlen_loop_break_correct:  forall ge e m b ofs outp le,
      
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 <= ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->

      (* IF before the loop *s = [b,ofs + outp] and i = outp *)
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat outp))) ->
      le!_output = Some (VintN outp) ->
      
      (* and the guard condition is false *)
      Mem.load Mint8unsigned m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr 0)) ->

      (* THEN loop executes to an environment with i = outp [i.e., i stays unchanged] + memory is unchanged *)
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ (le'!_output) = Some (VintN outp).
Proof.
  intros.
  repeat eexists.
  eapply exec_Sloop_stop1.
  seq2. seq1. seq1.
  repeat econstructor.
  apply H2.
  repeat econstructor.
  apply gss.
  repeat econstructor.
  seq1.
  repeat econstructor.
  rewrite gso. apply gss. cbv ; congruence.
  simpl.
  replace (Ptrofs.unsigned (Ptrofs.repr (ofs + Z.of_nat outp))) with (ofs + Z.of_nat outp).
  apply H4.
  { ptrofs_compute_add_mul. all: lia. }
  repeat econstructor.
  apply gss.
  econstructor.
  replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).
  econstructor.
  cbv; congruence.
  econstructor.
  repeat (rewrite gso). assumption.
  all: cbv; congruence.
Qed.

   
Lemma strlen_loop_body_correct: Archi.ptr64 = false -> forall len ge e m b ofs le,
      0 <= ofs < Ptrofs.modulus ->
      Z_of_nat len < Int.modulus ->
      ofs + Z_of_nat len < Ptrofs.modulus ->
                       
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) ->
      le!_output = Some (VintN len) ->
    
      (exists c, Mem.load chunk m b (ofs + Z.of_nat len) = Some (Vint c) /\c <> Int.zero) ->
                                         
      exists t le', exec_stmt ge e le m f_strlen_loop_body t le' m Out_normal /\ le'!_output = Some (VintN (S len)).
Proof.
  intros.
  destruct H5 as [p].
  repeat eexists.
  repeat seq1.
  repeat econstructor. apply H3. repeat econstructor.
  apply gss.
  repeat econstructor.
  repeat econstructor.
  rewrite gso. apply gss. cbv; congruence.
  simpl.
  replace (Ptrofs.unsigned (Ptrofs.repr (ofs + Z.of_nat len))) with (ofs + Z.of_nat len). 
  apply H5.
  { ptrofs_compute_add_mul. all: lia. }
  repeat econstructor.
  apply gss.
  econstructor.
  replace (negb (Int.eq p Int.zero)) with true.
  repeat econstructor.
  { replace (Int.eq p Int.zero) with false.
          auto.
          rewrite Int.eq_false.
          reflexivity.
          apply H5. }
  repeat econstructor.
  repeat (rewrite gso).
  apply H4. 1-3: cbv; congruence.
  repeat econstructor.
  unfold VintN.
  replace (Int.add (Int.repr (Z.of_nat len)) (Int.repr 1)) with (Int.repr (Z.of_nat (S len))). 
  apply gss.
  { ints_compute_add_mul.
    f_equal.
    lia.
    split; try lia. cbv; auto.
    lia. }
Qed.
               


(* Test 
Lemma strlen_correct_test: forall ge e m b ofs le,
    strlen_mem m b ofs (int_of_nat 2) ->
    le!_input = Some (Vptr b ofs) ->

    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintZ 2),tuint))) /\ (le'!_output) = Some (VintZ 2).
Proof.
  intros until le. intro Spec.
  inversion Spec.
  assert (i = (Int.add Int.one Int.one)).
  

  inver inversion_clear H4.
  repeat eexists.
  - seq1.
    -- sset. (* evaluate expression *) repeat econstructor.
    -- seq1.   
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss. repeat econstructor.
        rewrite gso. apply gss. cbv. congruence. apply H1.
        apply gss.
        econstructor.
        replace (negb (Int.eq c Int.zero)) with true by (apply (char_not_zero c); assumption).
        econstructor.
         rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv; congruence.
        repeat econstructor. econstructor. econstructor.

        (* loop 2 *)
        loop. repeat econstructor. 
        rewrite gso. rewrite gso. apply gss. 1-2: cbv; congruence. apply gss.
        repeat econstructor.
        rewrite gso. apply gss. cbv; congruence.
        replace (Ptrofs.add ofs
          (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
             (ptrofs_of_int Signed (Int.repr 1)))) with (Ptrofs.add ofs Ptrofs.one) by (auto with ptrofs).
        apply H5.
        apply gss.
        econstructor.
        replace (negb (Int.eq c0 Int.zero)) with true by (apply (char_not_zero c0); assumption).      
        econstructor. 
        rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv; congruence.
        repeat econstructor. econstructor. econstructor.
            
         (* exit loop *)
        eapply exec_Sloop_stop1.
        seq2. seq1. seq1. econstructor. econstructor. rewrite gso. rewrite gso. apply gss. 1-2: cbv; congruence.
        repeat econstructor.
        apply gss.
        repeat econstructor.
        seq1. repeat econstructor.
        rewrite gso. apply gss. cbv ; congruence.
        replace (Ptrofs.add
          (Ptrofs.add ofs
             (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
                (ptrofs_of_int Signed (Int.repr 1))))
          (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
             (ptrofs_of_int Signed (Int.repr 1))))  with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) Ptrofs.one) by (auto with ptrofs).
        apply H0.
        repeat econstructor.
        apply gss.
        econstructor. 
        replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).
        econstructor.
        cbv; congruence.
        econstructor.
      * (* return statement *)
        repeat econstructor.  rewrite gso.  rewrite gso. rewrite gso.  eapply gss. all: cbv; congruence.
  - rewrite gso.  rewrite gso.  rewrite gso. eapply gss. all: cbv; congruence.
Qed.
(* Helper lemmas about the specification *)

 (* add more lemmas from Compcert to ptrofs hints *)
Proposition int_ptrofs_mod_eq : (Int.modulus <= Ptrofs.modulus).
Proof.
  cbv. destruct Archi.ptr64; congruence.
  Qed.

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.

Lemma strlen_to_len_0 : forall len m b ofs, strlen_mem m b ofs len -> strlen_mem m b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat len))) O.
Proof.
  induction len; intros.
  - simpl.  replace (Ptrofs.repr 0) with Ptrofs.zero by (auto with ptrofs).
    replace (Ptrofs.add ofs Ptrofs.zero) with ofs by (auto with ptrofs).
    assumption.
  - inversion_clear H.
    replace (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S len)))) with
    (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr 1)) (Ptrofs.repr (Z.of_nat len))).
    apply (IHlen m b (Ptrofs.add ofs Ptrofs.one) H1).
    { rewrite Nat2Z.inj_succ.
      replace  (Z.succ (Z.of_nat len)) with ((Z.of_nat len) + 1) by (auto with zarith).
      rewrite Ptrofs.add_assoc.
      f_equal.
      unfold Ptrofs.add.
      f_equal.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Zmod_small.
      all: (pose int_ptrofs_mod_eq) ; nia. }
Qed.

 *)

