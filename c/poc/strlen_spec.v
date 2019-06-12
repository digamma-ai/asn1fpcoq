(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)


From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

(* Specification of the strlen function *)

Proposition int_ptrofs_mod_eq : (Int.modulus <= Ptrofs.modulus).
Proof.
  cbv. destruct Archi.ptr64; congruence.
Qed.

Proposition ptrofs_mod_1_0 : 0 <= 1 < Ptrofs.modulus.
Proof.
  cbv. destruct Archi.ptr64; split; congruence.
Qed.

Definition int_of_nat :=  fun n => Int.repr (Z.of_nat n).

(* automatically generated induction principle *)
Hypothesis int_ind : forall P : int -> Prop,
       (forall (intval : Z) (intrange : -1 < intval < Int.modulus),
        P {| Int.intval := intval; Int.intrange := intrange |}) ->
       forall m : int, P m.
                            
Inductive strlen_mem (m : mem) (b : block) (ofs : ptrofs) : Z -> Prop :=
| LengthZeroMem: Mem.loadv Mint8unsigned m (Vptr b ofs) = Some (Vint Int.zero) ->   
                 strlen_mem m b ofs 0
| LengthSuccMem: forall n c,
    strlen_mem m b (Ptrofs.add ofs Ptrofs.one) n ->
    Mem.loadv Mint8unsigned m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen_mem m b ofs (Z.succ n).


Inductive strlen_mem_n (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZeroMem_n: Mem.loadv Mint8unsigned m (Vptr b ofs) = Some (Vint Int.zero) ->   
                 strlen_mem_n m b ofs 0
| LengthSuccMem_n: forall n c,
    Z.of_nat (S n) < Int.modulus ->
    strlen_mem_n m b (Ptrofs.add ofs Ptrofs.one) n ->
    Mem.loadv Mint8unsigned m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen_mem_n m b ofs (S n).


Definition Int_succ := fun i : int => Int.add i Int.one.

Inductive strlen_mem_int (m : mem) (b : block) (ofs : ptrofs) : int -> Prop :=
| LengthZeroMem_int: Mem.loadv Mint8unsigned m (Vptr b ofs) = Some (Vint Int.zero) ->   
                 strlen_mem_int m b ofs Int.zero
| LengthSuccMem_int: forall n c,
    strlen_mem_int m b (Ptrofs.add ofs Ptrofs.one) n ->
    Mem.loadv Mint8unsigned m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen_mem_int m b ofs (Int_succ n).


Require Import Coq.Logic.FunctionalExtensionality.

Lemma Int_eq
      (intval1 : Z)
      (intrange1 : and (Z.lt (Zneg xH) intval1) (Z.lt intval1 Int.modulus))
      (intval0 : Z)
      (intrange0 : and (Z.lt (Zneg xH) intval0) (Z.lt intval0 Int.modulus))
      (H: intval0 = intval1)
  :
    Int.mkint intval0 intrange0 = Int.mkint intval1 intrange1.
Proof.
  apply Int.mkint_eq.
  assumption.
  Qed.

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
  apply Int_eq.
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
  apply Int_eq.
  simpl in H4.
  assumption.
  rewrite <- H4 in p0.
  assumption.
  -  nia.
Qed.


Lemma impl_spec : forall i m b ofs, (Int_succ i) <> Int.zero -> strlen_mem_int m b ofs (Int_succ i) -> strlen_mem_int m b (Ptrofs.add ofs Ptrofs.one) i.
Proof.
  (* intro i.
  eapply (int_induction (fun i => forall (m : mem) (b : block) (ofs : ptrofs), Int_succ i <> Int.zero ->
  strlen_mem_int m b ofs (Int_succ i) ->
  strlen_mem_int m b (Ptrofs.add ofs Ptrofs.one) i)). *)
  intros.
  inversion H0.
  (* same strategy as before  to show that n = Int.zero *)
  - destruct (Int_succ i) eqn: Si.
    destruct (Int.zero) eqn: S0.
    assert ( {| Int.intval := intval0; Int.intrange := intrange0 |} = {| Int.intval := intval; Int.intrange := intrange |}
 ).
    apply (Int.mkint_eq intval0 intval intrange0 intrange H1).
    congruence. 
  - destruct (Int_succ n) eqn: Sn.
    destruct (Int_succ i) eqn: Si.

    assert(E: Int_succ n = Int_succ i).
    {
      rewrite Si, Sn.
      apply Int_eq.
      assumption.
    }

    assert (J : n = i).
    { 
      destruct (Int.eq_dec n i).
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

(* В C есть Undefined *) 
(* pre-condition to guarantee not undefined *)
        
Scheme int_ind_auto := Induction for Int.int Sort Prop.
Print Int.int.

Check int_ind_auto.

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

Definition f_strlen_loop_body := (Ssequence
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
                  tuint))).

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


 (* add more lemmas from Compcert to ptrofs hints *)

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.
Lemma strlen_to_mem_n : forall len m b ofs, strlen_mem_n m b ofs len ->
                                     forall i, (i < len)%nat -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) = Some (Vint c) /\ c <> Int.zero.
Proof.
  induction len.
  - intros until ofs. intro Spec. intros.  omega.
  -  induction i. intro. inversion_clear H.
     +  replace (Ptrofs.repr (Z.of_nat 0)) with Ptrofs.zero by (simpl; auto with ptrofs).
        replace (Ptrofs.add ofs Ptrofs.zero) with ofs by (auto with ptrofs).
       exists c. apply (conj H3 H4).
    +  intro. inversion_clear H. assert (i < len)%nat by omega. pose (IHlen m b (Ptrofs.add ofs (Ptrofs.repr 1)) H2 i H).
       replace (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))) with  (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr 1)) (Ptrofs.repr (Z.of_nat i))).
       assumption.
       {
          rewrite Nat2Z.inj_succ.
      replace  (Z.succ (Z.of_nat i)) with ((Z.of_nat i) + 1) by (auto with zarith).
      rewrite Ptrofs.add_assoc.
      f_equal.
      unfold Ptrofs.add.
      f_equal.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Zmod_small.
      all: (pose int_ptrofs_mod_eq); try nia.
       }
Qed.


Lemma strlen_to_mem : forall len, 0 <= len -> (forall m b ofs, strlen_mem m b ofs len ->
                                     forall i, 0 <= i -> i < len -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr i))) = Some (Vint c) /\ c <> Int.zero).
Proof.
    eapply (natlike_ind  (fun len => (forall m b ofs, strlen_mem m b ofs len ->
                                     forall i, 0 <= i -> i < len -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr i))) = Some (Vint c) /\ c <> Int.zero))) ; intros until ofs; intro Spec.
  - (* Base len *) intros. nia.
  - (* Ind. step len *) 
    eapply (natlike_ind  (fun i => i < Z.succ x ->
                                exists c : int, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr i))) = Some (Vint c) /\ c <> Int.zero)).
    +  (* Base case i *)
      intro Sn0.
      replace (Ptrofs.add ofs (Ptrofs.repr 0)) with ofs by (simpl; auto with ptrofs).
      inversion Spec.
      nia.
      exists c. apply (conj H3 H4).
    +  (* Ind. step i *)
      intros.
      assert (x0 < x) by nia.
      rename H0 into IHlen.
      inversion Spec.
      nia.
      assert (n = x) by nia.
      rewrite H8 in H5.
      pose (IHlen m b (Ptrofs.add ofs Ptrofs.one) H5 x0 H1 H4).
       replace  (Ptrofs.add ofs (Ptrofs.repr (Z.succ x0))) with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (Ptrofs.repr x0)).
       assumption.
       { 
    
     (*  replace  (Z.succ (Z.of_nat i)) with ((Z.of_nat i) + 1) by (auto with zarith). *)
      rewrite Ptrofs.add_assoc.
      f_equal.
      unfold Ptrofs.add.
      f_equal.
      unfold Ptrofs.one.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Zmod_small.
      nia.
      admit. (* intrange *)
      admit.
             }
Admitted.


Proposition int_intval_repr : forall i : Z, 0 <= Z.succ i < Int.modulus ->
                                Int.intval (Int.repr (Z.succ i)) = Z.succ i.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  rewrite Zmod_small.
  auto.
  assumption.
  Qed.
    
Lemma strlen_to_mem_int : forall len m b ofs, strlen_mem_int m b ofs len -> forall i, Int.ltu i len = true -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) = Some (Vint c) /\ c <> Int.zero.
  Proof.
  induction len using int_ind.
  eapply (natlike_ind
         (fun intval0 => 
    forall (intrange0: -1 < intval0 < Int.modulus) (m : mem) (b : block) (ofs : ptrofs),
  strlen_mem_int m b ofs
    {| Int.intval := intval0; Int.intrange := intrange0 |} ->
  forall i : int,
  Int.ltu i
    {| Int.intval := intval0; Int.intrange := intrange0 |} =
  true ->
  exists c : int,
    Mem.loadv chunk m
      (Vptr b (Ptrofs.add ofs (Ptrofs.of_int i))) =
    Some (Vint c) /\ c <> Int.zero)).
     - (* Base len *)
    intros. 
    unfold Int.ltu in H0.
    unfold Int.unsigned in H0.
    simpl in H0.
    destruct (zlt (Int.intval i) 0).
    pose (Int.intrange i).
    nia.
    intuition.
    
  - (* I.S. len *)
    intros until ofs. intro Spec.
    induction i using int_ind.
    eapply (natlike_ind (fun intval0 =>
                           forall intrange2 : -1 < intval0 < Int.modulus,
  Int.ltu
    {| Int.intval := intval0; Int.intrange := intrange2 |}
    {| Int.intval := Z.succ x; Int.intrange := intrange1 |} =
  true ->
  exists c : int,
    Mem.loadv chunk m
      (Vptr b
         (Ptrofs.add ofs
            (Ptrofs.of_int
               {|
               Int.intval := intval0;
               Int.intrange := intrange2 |}))) = 
    Some (Vint c) /\ c <> Int.zero)).
   
      + (* Base i *)
        intros.
        inversion Spec.
        replace (match Int.zero with
       | {| Int.intval := intval |} => intval
                 end) with 0 in H2.
        nia.
        { unfold Int.zero.
          unfold Int.intval.
          replace 0 with (Int.unsigned (Int.repr 0)) by (auto with ints). auto with ints. }                   
       replace (Ptrofs.add ofs
            (Ptrofs.of_int
               {|
               Int.intval := 0;
               Int.intrange := intrange3 |})) with ofs by (auto with ptrofs).
       exists c. apply (conj H4 H5).

      + (* Ind. step  i*)
      intros. 
      rename H0 into IHlen.
      assert (intrange_x : -1 < x < Int.modulus) by nia.
      assert (intrange_x0 : -1 < x0 < Int.modulus) by nia.
      assert (Int.ltu
         {|
         Int.intval := x0;
         Int.intrange := intrange_x0|}
         {|
         Int.intval := x;
         Int.intrange := intrange_x |} = true) by admit.
      (* follows from H3 *)
     assert ( {| Int.intval := Z.succ x; Int.intrange := intrange1 |} = Int.repr (Z.succ x)).
      { admit. } (* destruct (Int.repr (Z.succ x)) eqn: Sx.
        
                                              apply Int_eq.

        pose int_intval_repr.
        Search Int.unsigned.
        pose (Int.eqm_repr_eq). (Z.succ x) _ Sx).

        Search Int.repr.
      }
      
      pose (impl_spec _ _ _ _ _ Spec).
      replace (match Int.zero with
       | {| Int.intval := intval |} => intval
       end) with 0 in H4.
  nia.
  { unfold Int.zero.
          unfold Int.intval.
          replace 0 with (Int.unsigned (Int.repr 0)) by (auto with ints). auto with ints. }

  destruct (Int_succ n) eqn: Sn.
  unfold Int_succ in Sn.
  unfold Int.add in Sn.
     destruct (Int_succ i) eqn: Si.

    assert(E: Int_succ n = Int_succ i).
    {
      rewrite Si, Sn.
      apply Int_eq.
      assumption.
    }

    assert (J : n = i).
    { unfold Int_succ in E.
      destruct (Int.eq_dec n i).
      assumption.
      pose (Int.eq_false n i n0).
      pose (Int.translate_eq n i Int.one).
      rewrite e in e0.
      Search Int.eq.
      pose (Int.eq_spec (Int.add n Int.one) (Int.add i Int.one)).
      rewrite e0 in y.
      congruence.

    }
    rewrite <- J.
    assumption.
  
  (* We want to conclude that intval n = x from the fact that intval Int_succ n = Z.succ x *)
  
  replace (match Int.repr (Z.succ n) with
       | {| Int.intval := intval |} => intval
       end) with (Z.succ n) in H4.
  assert (n = x) by nia.
  rewrite H8 in H5.
  assert (Int.repr x = {| Int.intval := x; Int.intrange := intrange_x |}) by admit. rewrite H9 in H5. *)
      rewrite H4 in Spec.
      assert (Int.repr (Z.succ x) <> Int.zero) as A by admit.
      pose (impl_spec _ _ _  _ A Spec).
      pose (IHlen intrange_x m b (Ptrofs.add ofs Ptrofs.one) s {| Int.intval := x0; Int.intrange := intrange_x0 |} H0).
       replace 
       (Ptrofs.add ofs
            (Ptrofs.of_int
               {|
               Int.intval := Z.succ x0;
               Int.intrange := intrange2 |})) with  (Ptrofs.add (Ptrofs.add ofs Ptrofs.one)
               (Ptrofs.of_int
                  {|
                  Int.intval := x0;
                  Int.intrange := intrange_x0 |})).
       assumption.

       
       { 
    
      rewrite Ptrofs.add_assoc.
      f_equal.
      unfold Ptrofs.add.
      unfold Ptrofs.of_int.
      f_equal.
      unfold Ptrofs.one.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Zmod_small.
      unfold Int.unsigned.
      unfold Int.intval.
      nia.
      unfold Int.unsigned.
      unfold Int.intval.
      pose (int_ptrofs_mod_eq).
      nia.
      apply ptrofs_mod_1_0.
       }
       {
         
      
    admit.

  }
      + nia.
  - nia.
  

Admitted.


  (*   induction len.
  induction intval0.
  - (* Base len *)
    intros.
    unfold Int.ltu in H0.
    unfold Int.unsigned in H0.
    simpl in H0.
    destruct (zlt (Int.intval i) 0).
    pose (Int.intrange i).
    nia.
    intuition.    
  - (* I.S. len *)
    intros until ofs. intro Spec.
    induction i.
    induction intval0.
    + (* Base case i *)
      intros.
          induction p using positive_lt_ind.

      inversion Spec.
        replace (match Int.zero with
       | {| Int.intval := intval |} => intval
                 end) with 0 in H2.
        nia.
        { unfold Int.zero.
          unfold Int.intval.
          replace 0 with (Int.unsigned (Int.repr 0)) by (auto with ints). auto with ints. }
          
          
      
       replace (Ptrofs.add ofs
            (Ptrofs.of_int
               {|
               Int.intval := 0;
               Int.intrange := intrange2 |})) with ofs by (auto with ptrofs).
       exists c. apply (conj H4 H5).

      + (* Ind. step  i*)
      intros. 
      rename H0 into IHlen.
      assert (intrange_x : -1 < x < Int.modulus) by nia.
      assert (intrange_x0 : -1 < x0 < Int.modulus) by nia.
      assert (Int.ltu
         {|
         Int.intval := x0;
         Int.intrange := intrange_x0|}
         {|
         Int.intval := x;
         Int.intrange := intrange_x |} = true) by admit.
      inversion Spec.
  replace (match Int.zero with
       | {| Int.intval := intval |} => intval
       end) with 0 in H4.
  nia.
  { unfold Int.zero.
          unfold Int.intval.
          replace 0 with (Int.unsigned (Int.repr 0)) by (auto with ints). auto with ints. }

  unfold Int_succ in H4.
  unfold Int.add in H4.
  unfold Int.one in H4.
  replace (Int.unsigned (Int.repr 1)) with 1 in H4 by (auto with ints).
  replace (Int.unsigned n + 1) with (Z.succ (Int.unsigned n)) in H4 by (nia).
  
  (* We want to conclude that intval n = x from the fact that intval Int_succ = Z.succ x *)
  
  replace (match Int.repr (Z.succ n) with
       | {| Int.intval := intval |} => intval
       end) with (Z.succ n) in H4.
  assert (n = x) by nia.
  rewrite H8 in H5.
  assert (Int.repr x = {| Int.intval := x; Int.intrange := intrange_x |}) by admit. rewrite H9 in H5. 
      pose (IHlen intrange_x m b (Ptrofs.add ofs Ptrofs.one) H5 {| Int.intval := x0; Int.intrange := intrange_x0 |} H0).
       replace 
       (Ptrofs.add ofs
            (Ptrofs.of_int
               {|
               Int.intval := Z.succ x0;
               Int.intrange := intrange2 |})) with  (Ptrofs.add (Ptrofs.add ofs Ptrofs.one)
               (Ptrofs.of_int
                  {|
                  Int.intval := x0;
                  Int.intrange := intrange_x0 |})).
       assumption.

       
       { 
    
      rewrite Ptrofs.add_assoc.
      f_equal.
      unfold Ptrofs.add.
      unfold Ptrofs.of_int.
      f_equal.
      unfold Ptrofs.one.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Zmod_small.
      unfold Int.unsigned.
      unfold Int.intval.
      nia.
      unfold Int.unsigned.
      unfold Int.intval.
      pose (int_ptrofs_mod_eq).
      nia.
      apply ptrofs_mod_1_0.
       }
       {
         
      
    admit.

  }
      + nia.
  - nia.

  
  *)
(* Correctness statements *)

(* A generalization of loop correctness *)

Lemma strlen_loop_correct_gen :
  forall len i ge e m b ofs le,
    (* we read a C string of length len + i from memory and len + i is a valid integer *)

    strlen_mem m b ofs (len + i) ->
    
    (* THEN there is a trace t and local environment le' such that: *)
    exists t le',
      (* if output equals i in the starting local environment le *)
      le!_output = Some (VintN i) ->
      (* if input is an address [b,ofs + i] in the starting local environment *)
      le!_input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) ->     (* then loop of strlen function executes to le' with output assigned len + i *)
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN (len + i)).
Proof.
  assert (Int.modulus <= Ptrofs.modulus) as B.
  { cbv. destruct Archi.ptr64. 1-2: congruence. }
  induction len; intros until le; intro Spec. 
  - (* Base case *)    
    simpl in Spec.
    repeat eexists.
    (* Exit the loop *)
    eapply exec_Sloop_stop1. seq2. repeat econstructor.
    apply H0.
    eapply gss.
    repeat econstructor.
    rewrite gso. apply gss. cbv. congruence.
    (* Derive memory assumptions from the specification *)
    pose (Spec_mem := strlen_to_len_0 i m b ofs Spec).
    inversion_clear Spec_mem.
    apply H1.
    apply gss.
    econstructor.
    replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).      
    econstructor.
    cbv; congruence. econstructor.
    repeat (rewrite gso).
    replace (0 + i)%nat with i by lia.
    assumption.
    1-3: cbv; congruence.
  - (* Ind. Step *)
    assert (exists char, Mem.loadv Mint8unsigned m (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) = Some (Vint char) /\ char <> Int.zero) as Mem. 
    { refine (strlen_to_mem (S len + i) m b ofs Spec i _). omega. }
    destruct Mem as [char Mem].
    (* apply I.H. to le' after one step when starting with i and [b,ofs + i]  *)
    pose (le'' :=  (PTree.set _output (VintN (S i))
       (PTree.set _t'2 (Vint char) (PTree.set _input
               (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))))
          (PTree.set _t'1
               (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i))))
                      le))))).
    pose (IH := IHlen (S i) ge e m b ofs le'').
    assert ( exists (t : trace) (le' : temp_env),
       le'' ! _output = Some (VintN (S i)) -> 
       le''! _input = Some (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i))))) ->               
       exec_stmt ge e le'' m f_strlen_loop t le' m
         Out_normal /\
       le' ! _output = Some (VintN (len + S i))) as Step.
    { eapply IH.
      replace (len + S i)%nat with (S len + i)%nat by omega.
      assumption. }
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
    replace (PTree.set _output
       (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)))
       (PTree.set _t'2 (Vint char)
          (PTree.set _input
             (Vptr b
                (Ptrofs.add
                   (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))
                   (Ptrofs.mul
                      (Ptrofs.repr (sizeof ge tuchar))
                      (ptrofs_of_int Signed (Int.repr 1)))))
             (PTree.set _t'1
                (Vptr b
                   (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i))))
                le)))) with le''.
  eapply Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.

  {  inversion Spec.
    (* destruct Mem as [Mem C]. destruct C as [C Inc]. *)

    unfold le''.
    replace (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1))) with (VintN (S i)).

    replace (Ptrofs.add
                (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))
                (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
                            (ptrofs_of_int Signed (Int.repr 1)))) with (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))).
    reflexivity.
     + replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by nia.
       simpl.
       replace (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))) with (Ptrofs.repr 1) by (auto with ptrofs).
       Search (Ptrofs.repr ( _ + _ )).
       SearchAbout Ptrofs.add.
       rewrite Ptrofs.add_assoc.
       f_equal.
       unfold Ptrofs.add.
       f_equal.
       rewrite Ptrofs.unsigned_repr_eq.
       rewrite Ptrofs.unsigned_repr_eq.
       rewrite Zmod_small.
       rewrite Zmod_small.
       all: nia.
  
     + unfold VintN.
       
      f_equal.
      ints_compute_add_mul.
      f_equal.
      lia.

      cbv. econstructor. 1-2: congruence.
      nia.
      }
  destruct Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.
  replace (S len + i)%nat with (len + S i)%nat by omega.
  assumption.
Qed.      

(* On empty string C light function evaluates to 0 *)

Lemma strlen_correct_loop_empty_string :
  forall ge e m b ofs le,                                           
    strlen_mem m b ofs O ->

    exists t le',
      le!_output = Some (VintN O) ->
      le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN O).
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
               

