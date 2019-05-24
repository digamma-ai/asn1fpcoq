
(* towards loop invariant *)


 Inductive pre_strlen_mem (m : Mem.mem) (b : block) (ofs : Z) : Z -> nat -> Prop :=
| PreLengthZeroMem: Mem.load Mint8signed m b ofs = Some (VintZ 0) -> pre_strlen_mem m b ofs ofs O
| PreLengthOneMem: forall p, Mem.load Mint8signed m b ofs = Some (VintP p) -> pre_strlen_mem m b ofs ofs 1%nat
| PreLengthSuccMem: forall n p z,
    pre_strlen_mem m b ofs z n ->
    Mem.load Mint8signed m b (z + 1) = Some (VintP p) ->
    pre_strlen_mem m b ofs (z + 1) (S n).

Lemma strlen_loop_correct_inv : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall len ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *)
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
                       (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintN len) ->
                       
       (* Precondition: reading C pre-string of length len from memory *)
    pre_strlen_mem m b ofs (ofs + Z.of_nat len) (S len) ->
               
      exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN (S len)) le) m Out_normal.
Proof.



(* testing inversion: *)
Goal forall len ge e le m x, exec_stmt ge e le m
         (Sifthenelse
            (Ebinop One
               (Ederef
                  (Ebinop Oadd (Etempvar _input (tptr tschar)) (Etempvar _output tuint)
                     (tptr tschar)) tschar) (Econst_int (Int.repr 0) tint) tint) Sskip Sbreak) x
         (PTree.set _output (VintN len) le) m Out_normal -> False.
Proof.
  intros.
  inversion H ; subst ; clear H.
  inversion H6 ; subst ; clear H6.
  inversion H5 ; subst ; clear H5.
  inversion H4 ; subst ; clear H4.
  inversion H ; subst ; clear H.
  inversion H0 ; subst ; clear H0.
  inversion H5 ; subst ; clear H5.
  inversion H8 ; subst ; clear H8.
  inversion H9 ; subst ; clear H9.
  destruct v2. admit.
  assert (le ! _input = Some (Vint Int.zero)). admit.
  assert (i <> Int.zero). admit.
  congruence.
Admitted.


(* Lemma used in the induction step below *)

(* if executing f_strlen_loop with output = 0 and input = [b,ofs + 1] outputs len
    then executing f_strlen_loop with output = 0 and input = [b,ofs] outputs (S outp) *)


Lemma exec_trans : forall len ge e le m b ofs,  strlen_mem m b ofs (S len) ->
    
    (exists t, exec_stmt ge e (PTree.set _output (VintN O) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le))  m f_strlen_loop t (PTree.set _output (VintN (len)) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)) m Out_normal) ->
    
    (exists p : positive, Mem.load chunk m b ofs = Some (VintP p)) ->
    
    exists t, exec_stmt ge e (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le) m f_strlen_loop t (PTree.set _output (VintN (S len)) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m Out_normal.
    
    Proof.
      intros.
      destruct H0.
      inversion_clear H.
       solve_by_inverts 5%nat. solve_by_inverts 5%nat. rewrite gss in H.  inversion H. rewrite <- H10 in *. rewrite gso in H8. rewrite gss in H8. inversion H8. rewrite <- H11 in *. clear H H8 H10 H11.
      inversion H9. rewrite <- H0 in *. rewrite <- H8 in *. clear H0 H8. clear v3 v4. inversion H6.
                                                                                              
      subst. clear ofs0 loc. 

      
      simpl in H0.
      replace  (Ptrofs.unsigned
            (Ptrofs.add (Ptrofs.repr (ofs + 1))
                        (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with (ofs + 1) in H0 by (admit).
     
    Admitted.

    Lemma exec_trans2 : forall ge e m le t _o n, exec_stmt ge e (PTree.set _o (VintN O) le) m f_strlen_loop t (PTree.set _o (VintN n) le) m Out_normal ->
                                    exec_stmt ge e (PTree.set _o (VintN n) le) m f_strlen_loop t (PTree.set _o (VintN (S n)) le) m Out_normal ->
   
   exec_stmt ge e (PTree.set _o (VintN O) le) m f_strlen_loop t (PTree.set _o (VintN (S n)) le) m Out_normal.
Proof.
      Admitted.

Lemma strlen_non_empty_corr : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall ge e m b ofs le len,
                       
               (* Preconditions on the length of the string and valid offset *)
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat (S len) < Int.modulus ->
    ofs + Z_of_nat (S len) < Ptrofs.modulus ->
                       
                       (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->

                       
       (* Precondition: reading C string from memory *)
    forall i z, (i < S len)%nat ->
           Mem.load chunk m b (ofs + Z.of_nat i) = Some (VintN (S z)) ->
           Mem.load chunk m b (ofs + Z.of_nat (S len)) = Some (VintN O) ->
           
      exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN (S len)),tuint))) /\
                    (le'!_output) = Some (VintN (S len)).
Proof.
  induction len.
  - (* Base case *) intro L. intros.
     repeat eexists.
 
  -- seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss.        repeat econstructor. simpl. replace (Ptrofs.unsigned
                                               (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. assert (i = O). omega. rewrite H7 in H5. simpl in H5. replace (ofs) with (ofs + 0) by lia. apply H5.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. } repeat econstructor. simpl. replace  (negb
          (Int.eq (Int.repr (Z.pos (Pos.of_succ_nat z)))
                  (Int.repr 0))) with true.  repeat econstructor. { admit.  } econstructor. repeat econstructor. repeat econstructor. apply gss. repeat econstructor.

        (* exit loop *)
        eapply exec_Sloop_stop1. (* break from the loop *)
        repeat econstructor.  rewrite gso; repeat gso_assumption.  eapply gss.
        repeat econstructor. simpl.
        replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.add (Int.repr 0) (Int.repr 1)))))) with (ofs + 1). apply H6.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: admit. }
                                                                                                                                  repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
    + (* return statement *)
      repeat econstructor. eapply gss.
      -- eapply gss.

   -. intros. repeat eexists. -- seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss.        repeat econstructor. simpl.
        induction i.
        replace (Ptrofs.unsigned
                                               (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. simpl in H6. replace ofs with  (ofs + 0) by lia. apply H6. { admit. } apply IHi. omega.
                                                                                                                                  
    apply (strlen_loop_break_correct H _  _ _ b ofs _ _).
    (* 1,2,3: nia. *)    
     all: try nia ; try assumption. inversion H3. simpl; unfold VintZ in H5; replace (ofs + 0) with ofs by lia. assumption. inversion H3. simpl; unfold VintZ in H5; replace (ofs + 0) with ofs by lia. assumption.
  - (* Induction Step *) intro L. intros.
    assert (C_string m b ofs len).
    { inversion H3. admit. }
    assert  (0 <= Z_of_nat len < Int.modulus ). { clear IHlen. lia. }
    assert (ofs + Z.of_nat len < Ptrofs.modulus). { clear IHlen. nia. }                                   
    pose (H8:= IHlen H7 H0 H1 H2 H5 H6).
    destruct H8. destruct H8. destruct H8. clear IHlen.
    assert  (exists t, exec_stmt ge e x0 m f_strlen_loop t (PTree.set _output (VintN (S len)) x0) m Out_normal /\ le ! _output = Some (Vint_of_nat (Datatypes.S len))).
    { repeat eexists.
      +  Print exec_stmt. eapply exec_Sloop_loop.
         repeat econstructor. Admitted.


(* TODO : fix this *)
Inductive C_string (m : Mem.mem) (b : block) (ofs : Z) (len : nat) :=
  is_C_string : forall n i, (0 < Z.of_nat n < Int.modulus) ->
                        (0 <= i < len)%nat ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat i) = Some (VintN n) ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat len) = Some (VintZ 0) ->
                        C_string m b ofs len.


Lemma strlen_correct_with_C_string : Archi.ptr64 = false -> forall ge e m b ofs le len,
      
      (0 <= Z_of_nat len < Int.modulus ) -> (* len is within bounds *)
      0 < ofs < Ptrofs.modulus -> 
      (ofs + Z_of_nat len) < Ptrofs.modulus ->  (* the offsets are valid *)
  
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) -> (* input is an address [b,ofs] *) 
      le!_output = Some (VintZ 0) -> (* we start from 0 *)
      
      C_string m b ofs len -> (* [b,ofs] points to a string of length len in memory m *)
      
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m (Out_return (Some (VintN len, tuint))) /\
               (le'!_output) = Some (VintN len).
(* the C light expression evaluates to outcome Out_return (Some VintN len) and output is set to len *)
Admitted.


(* non-empty string *)
Lemma strlen_loop_continue_correct : Archi.ptr64 = false -> forall len ge e m b ofs le,
      
      1 <= Z.of_nat (S len) < Ptrofs.modulus ->
      ofs + Z.of_nat (S len) < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat (S len) < Ptrofs.modulus ->

      strlen_mem m b ofs (S len) -> (* assume we have a string of length (S len) at [b,ofs] in m *)
      
      forall i, (i < S len)%nat ->  (* then the loop continues until len and outputs i++ *)
           
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) -> 
      le!_output = Some (VintN i) ->
      
      exists t, exec_stmt ge e le m f_strlen_loop t (Maps.PTree.set _output (VintN (S i)) le) m Out_normal.
Proof.
  induction len.
  -  (* Base case *)
    intros. assert (i = 0)%nat by omega. rewrite H8 in *. replace (ofs + Z.of_nat 0) with ofs in H6 by nia. inversion_clear H4.
   destruct (strlen_loop_break_correct2 H ge e m b ofs 1 (PTree.set _output (VintN 1) le)). 
        1-3: nia.
        repeat gso_assumption.
        apply gss.
        simpl.
        inversion H9.
        assumption.   
        eexists.
        loop. repeat econstructor. repeat gso_assumption. gso_assumption.   repeat econstructor. simpl. replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. apply H10.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. } repeat econstructor. simpl. repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos v)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. repeat econstructor. repeat econstructor.
        gso_assumption. repeat econstructor.
        fold f_strlen_loop.
        replace (Int.add (Int.repr (Z.of_nat 0)) (Int.repr 1)) with (Int.repr 1) by (auto with ints).      apply H4.
    
  - induction i ; intros. replace (ofs + Z.of_nat 0) with ofs in * by nia.
    inversion_clear H4. 
    eexists.
    
        loop. repeat econstructor. repeat gso_assumption. gso_assumption. repeat econstructor. simpl. replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. apply H9.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. } repeat econstructor. simpl. repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos v)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. repeat econstructor. repeat econstructor.
        gso_assumption. repeat econstructor.
        
        fold f_strlen_loop.
        
        replace (Int.add (Int.repr (Z.of_nat 0)) (Int.repr 1)) with (Int.repr 1) by (auto with ints).
         replace ofs with  (ofs + Z.of_nat 0) in H6 by nia.
         assert (exists t : trace,
   exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN 1) le) m Out_normal).

    (*     refine  (IHlen ge e m b ofs le _ _ _ _ _ O _ H6 H7).
         1-4: nia.
         
        destruct (strlen_loop_break_correct2 H ge e m b ofs 1 (PTree.set _output (VintN 1) le)). 
        1-3: nia.
        repeat gso_assumption.
        apply gss.
        simpl.
        inversion_clear H8.
        (* wrong : Mem.load Mint8signed m b (ofs + 1) = Some (VintP v0) with v0 positive *)
        assumption.  

        apply H4.
    
    + intros. inversion_clear H4.
      pose (IHlen ge e m b (ofs + 1) le).
      assert (1 <= Z.of_nat (S len) < Ptrofs.modulus) by nia. 
      assert (ofs + 1 + Z.of_nat (S len) < Ptrofs.modulus) by nia.
      assert (0 < ofs + 1 < Ptrofs.modulus) by nia.
      assert (0 <= Z.of_nat (S len) < Ptrofs.modulus) by nia.
      apply (e0 H4 H10 H11 H12).
      assumption.
      admit. (* (0 < len)%nat *) 
      admit. (* le ! _input = Some (Vptr b (Ptrofs.repr (ofs + 1))) *)
      assumption.
    +   *)
       
Admitted.


Lemma exec_trans : forall ge e le m t b ofs outp,
    le!_output = Some (VintZ 0) ->
    exec_stmt ge e (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le) m f_strlen_loop t  (PTree.set _output (VintN outp)(PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)) m Out_normal ->

    le ! _input = Some (Vptr b (Ptrofs.repr ofs)) ->
    exec_stmt ge e (PTree.set _output (VintZ 1) le) m f_strlen_loop t (PTree.set _output (VintN outp) le) m Out_normal. 
  Admitted.


                        
(* Old stuff: One direction of correctness, using functional spec, below relational with proof attempt *)

 Definition strlen_C_fun_corr_r :
  forall (ge :genv) (m : Mem.mem) (b : block) (ofs : Z) (e : env) (le : temp_env) (z : Z),
    strlen_C_fun_spec m b ofs = Some (z,m) ->
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> (* input parameter _s assigned value of address (b,ofs) in le *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr z),tuint))) /\ le'!_i = Some (Vint (Int.repr z)).
               (* in environments ge, e (local env), le and memory m with output trace t, output _i assigned value z *)
Admitted.

 (* Find proofs on arithmetic on ptrofs type to rewrite this *)
      Hypothesis ptr_ofs_eq : forall ofs, ofs = (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))). 

      
Definition strlen_C_rel_corr_r : forall n m b ofs e le ge,
    strlen_C_rel_spec m b ofs (Some (n,m)) ->
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> 
    exists t le', le'!_i = Some (Vint_of_nat n) /\ 
           exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((Vint_of_nat n),tuint))).
Proof.
  induction n.
  (* Base case. *)
    intros.
    inversion H. unfold chunk in *. destruct H4.
    eexists.
    exists (Maps.PTree.set _i (Vint (Int.repr (Z.of_nat 0))) le).
    split.
    - apply Maps.PTree.gss.
    - repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply PTree.gss.
    + repeat econstructor.
    + simpl. rewrite <- ptr_ofs_eq. apply H3.
    + cbn. rewrite -> H4. reflexivity.
    + cbn. unfold Val.of_bool. simpl in H8. rewrite H4 in H3.  rewrite Z.add_0_r in H8.  rewrite H8 in H3. inversion H3. reflexivity.
    + Hypothesis fls : negb (Int.eq Int.zero Int.zero) = false.
      rewrite fls. econstructor.
    + apply PTree.gss.
      (* Ind step *)
     -   intros.
        inversion H. unfold chunk in *. destruct H4.
        eexists.
        exists (Maps.PTree.set _i (Vint (Int.repr (Z.of_nat (S n)))) le).
    split.
      + apply Maps.PTree.gss.
    + repeat econstructor.
     rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
     apply PTree.gss.
     repeat econstructor.
     simpl. rewrite <- ptr_ofs_eq. apply H3.
     cbn. rewrite -> H4. reflexivity.
     cbn. unfold Val.of_bool. simpl in H8. rewrite H4 in H3. destruct (negb (Int.eq x (Int.repr 0))). simpl.  Hypothesis tr : negb (Int.eq Int.one Int.zero) = true. rewrite tr. constructor. simpl. rewrite fls. (* false goal: prove the correctness of the loop *) 
Admitted.

(* Tactic for inversion  *)

 Ltac invertSem :=
        match goal with
          | [H : context[exec_stmt] |- _] =>
            inversion H ; clear H 
          | [H : context[eval_expr] |- _] =>
            inversion H ; clear H
          | [H : context[eval_lvalue] |- _] =>
            inversion H ; clear H 
          | [H : context[bool_val] |- _] =>
            inversion H ; clear H
          | [H : context[deref_loc] |- _] =>
            inversion H ; clear H  
          | [H : context[sem_binary_operation] |- _] =>
            inversion H ; clear H  
          | [H : context[access_mode] |- _] =>
            inversion H ; clear H  
          | _ => idtac
        end.    
 

 Ltac solve_by_inverts n :=
   match n with
   | O => idtac
   | S (?n') => invertSem ; subst ; solve_by_inverts n'
   end.

 (* behaves differently than the above: 

  Ltac invert_clear :=
        match goal with
          | [H : context[exec_stmt] |- _] =>
            inversion_clear H 
          | [H : context[eval_expr] |- _] =>
            inversion_clear H 
          | [H : context[eval_lvalue] |- _] =>
            inversion_clear H 
          | [H : context[bool_val] |- _] =>
            inversion_clear H  
          | [H : context[deref_loc] |- _] =>
            inversion_clear H  
          | [H : context[sem_binary_operation] |- _] =>
           inversion_clear H  
          | [H : context[access_mode] |- _] =>
            inversion_clear H  
          | _ => idtac
        end.    


 Ltac solve_by_inverts n :=
   match n with
   | O => subst
   | S (?n') =>  invert_clear; solve_by_inverts n'
   end.

  *)
 
 Definition strlen_C_rel_corr_l : forall n m b ofs e le,
     (n < INTSIZE)%nat ->
     le!_s = Some (Vptr b (Ptrofs.repr ofs)) ->
     (exists le', le'!_i = Some (Vint (Int.repr (Z_of_nat n))) /\ 
                bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr (Z_of_nat n)),tuint))))
           -> strlen_C_spec m b ofs (Some (n,m)).
Proof.
  intros.
  repeat destruct H1.
  inversion H2.
  solve_by_inverts 5%nat. solve_by_inverts 15%nat. (* TODO: fix the tactic *)  Admitted.


Definition strlen_C_exec_corr_l :
  forall (m : Mem.mem) (b : block) (ofs : Z) (e : env) (le : temp_env) (z : Z),
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> 
    (exists le', le'!_i = Some (Vint (Int.repr z)) /\ 
                bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr z),tuint))))
           -> strlen_C m b ofs = Some (z,m).
Proof.
  intros.
  repeat destruct H0.
  inversion H1.
  solve_by_inverts 5%nat. solve_by_inverts 15%nat. 
  unfold strlen_C.  unfold strlen_fun_C. unfold Mem.loadv in H9.
  Admitted.
              
(* Examples of running a program: to see what assumptions need in the proof, experiments *)

Parameter hi : Z.
Definition init_mem := fst (Mem.alloc Mem.empty 0 hi).
Definition b' := snd (Mem.alloc Mem.empty 0 hi).
Parameter ofs' : Z.
Hypothesis ofs_le_hi : ofs' < hi.

(* Example 1 : output on empty string is correct *)

Definition init_mem1 := 
  Mem.store Mint8signed init_mem b' ofs' (Vint (Int.repr 0)).


Lemma example_comp : forall m le e, init_mem1 = Some m ->
                             le!_s = Some (Vptr b' (Ptrofs.repr ofs')) ->
                             exists le', bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr 0),tuint))).
Proof.
  intros.
  exists (Maps.PTree.set _i (Vint (Int.repr 0)) le).
  repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply Maps.PTree.gss.
    + econstructor.
    + unfold init_mem1 in H. simpl. rewrite (Mem.load_store_same  Mint8signed init_mem b' _ (Vint (Int.repr 0))). constructor. rewrite <- ptr_ofs_eq. assumption.
    + econstructor.
    + econstructor.
    + econstructor.
    + apply Maps.PTree.gss.
Qed. 

(* Running on a non-empty string: TODO prove the loop  *)

Definition init_mem0 := fst (Mem.alloc Mem.empty 0 hi).
Definition init_mem2 := Mem.store Mint8signed init_mem0 b' ofs' (Vint (Int.repr 1)).
Definition init_mem3 := match init_mem2 with
                        | None => None
                        | Some m => Mem.store Mint8signed m b' (ofs'+1) (Vint (Int.repr 0))
                        end.

Lemma example_comp2 : forall m le e,
                          init_mem2 = Some m ->
                          init_mem3 = Some m -> 
                          le!_s = Some (Vptr b' (Ptrofs.repr ofs')) ->
                          exists le', bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr 1),tuint))).
Proof.
  intros.
  exists (Maps.PTree.set _i (Vint (Int.repr 1)) le).
  repeat econstructor.
    + rewrite PTree.gso. apply H1. eapply Pos.succ_discr. 
    + apply Maps.PTree.gss.
    + econstructor.
    + unfold init_mem3 in H0. rewrite H in H0. simpl. rewrite <- ptr_ofs_eq.
      unfold init_mem2 in H. rewrite <- H in H0. rewrite -> (Mem.load_store_same Mint8signed init_mem0 b' ofs' (Vint (Int.repr 1))). econstructor. assumption.
    + econstructor.      
    + econstructor.
    + Print exec_stmt. admit. 
Admitted.

     
(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)



(* 

                                                
   
      
  
Lemma strlen_loop_continue_correct : Archi.ptr64 = false -> forall z ge e m b ofs outp le,
      1 <= Z.of_nat outp + 1 < Ptrofs.modulus ->
      0 < z ->
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      1 <= Z.of_nat outp < Ptrofs.modulus ->
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (Vint_of_nat outp) ->
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr z)) ->
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\
               (le'!_output) = Some (Vint_of_nat (outp + 1)).

Proof.
  intro Arch.
  intros z ge e m b ofs outp le.
  intro P.
  intro Z.
  intro S.
  intros.
  repeat eexists.
  Print exec_stmt.
  - eapply exec_Sloop_loop.

    eapply exec_Sifthenelse. econstructor. econstructor. econstructor.
    econstructor.
    econstructor.
    apply H1.
    econstructor.
    apply H2. econstructor. econstructor. econstructor. simpl.
    assert ( (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) = (ofs + (Z_of_nat outp)) ) as E1. 
    { pose (Ptrofs.modulus_eq32 Arch).
      rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.  unfold Ptrofs.of_intu. unfold Ptrofs.of_int. repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Zmod_small ; nia. }
    rewrite E1. apply H3.
    econstructor.
    econstructor. simpl.
    cut ((negb (Int.eq (Int.repr z) (Int.repr 0))) = true). intro aux. rewrite aux. simpl. econstructor. {  admit. }
    econstructor.
    econstructor.
    econstructor.
    econstructor. 
   
    econstructor.
    apply H2.
     econstructor.
     econstructor.
     eapply exec_Sloop_stop1. repeat econstructor. rewrite PTree.gso. apply H1. cbv. congruence. 
     apply PTree.gss. econstructor. simpl.

      assert ( 
    (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
          (Ptrofs.mul (Ptrofs.repr 1)
             (Ptrofs.of_intu (Int.add (Int.repr (Z.of_nat outp)) (Int.repr 1)))))) = (ofs + (Z_of_nat outp + 1)) ) as E1. 
    { pose (Ptrofs.modulus_eq32 Arch).
      rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.  unfold Ptrofs.of_intu. unfold Ptrofs.of_int. repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Zmod_small; unfold Int.add; repeat rewrite Int.unsigned_repr_eq ;  repeat rewrite Zmod_small;  admit. } 
    rewrite E1. (* Mem.load Mint8signed m b (ofs + (Z.of_nat outp + 1)) = Some ?v10 *)

                                                                       

Admitted.

 *)


(* WRONG *)
Lemma exec_trans1 : forall ge e m le len b ofs, 
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      strlen_mem m b ofs (S len) ->
      (exists t, exec_stmt ge e  (PTree.set _output (VintZ 1) le) m f_strlen_loop t (PTree.set _output (VintN len) le) m Out_normal) ->
      
      (exists p, Mem.load chunk m b ofs = Some (VintP p)) ->  
      exists t, exec_stmt ge e (PTree.set _output (VintZ 0) le) m f_strlen_loop t (PTree.set _output (VintN (S len)) le) m Out_normal.
Proof.
  Hypothesis F: Archi.ptr64 = false.
  intros.
  destruct H2.
  
  induction len.
  assert (exists t, exec_stmt ge e (PTree.set _output (VintN 1) le) m f_strlen_loop t
                               (PTree.set _output (VintN 1) le) m Out_normal).
        pose (strlen_loop_break_correct2).
        
        apply (strlen_loop_break_correct2 F ge e m b ofs 1 (PTree.set _output (VintN 1) le)).
        1-3: admit.
        repeat gso_assumption. apply gss.
        inversion_clear H0. inversion_clear H3. simpl. assumption.
        destruct  H3.                                               
  - eexists. (* Base case *)
   (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss.        repeat econstructor. simpl. replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with (ofs).  apply H2. { (* pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia.*) admit. } repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos x)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. repeat econstructor. repeat econstructor. apply gss. repeat econstructor. fold f_strlen_loop.
        replace  (Int.add (Int.repr 0) (Int.repr 1)) with (Int.repr 1) by (auto with ints).
        replace (PTree.set _output (Vint (Int.repr 1)) (PTree.set _output (VintZ 0) le)) with
            (PTree.set _output (VintN 1) le).
        apply H3.

        {rewrite PTree.set2. auto. }
  -. (* Induction Step *)
    
        
        
  (*
  induction len.
  - (* Base case *)
    destruct H0.
    inversion e0. 
    inversion H11. clear H11.
    clear H0.
    inversion H6. clear H6.
    inversion H13. clear H13.
    inversion H7.
    inversion H29.
    subst.
    inversion H3.
    
    solve_by_inverts 5%nat.
    
    eapply strlen_loop_break_correct2.
    1-4: admit.
    repeat gso_assumption.
    apply gss.
    solve_by_inverts 5%nat. *)
  Admitted.



      (* small-step semantics 
      pose (exec_stmt_steps p e (PTree.set _o (VintZ 0) le) m f_strlen_loop t (PTree.set _o (VintZ n) le) m Out_normal).
      assert ((globalenv p) = ge). admit.
      rewrite H0 in e0.
      pose (e0 H).
       *)

    Lemma exec_trans : forall len ge e le m b ofs,
        
    le!_output = Some (VintZ 0) ->
    le!_input = Some (Vptr b (Ptrofs.repr (ofs + 1))) ->
    
    strlen_mem m b ofs (S len) ->
    
    (exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN len) le) m Out_normal) ->
    
    (exists p : positive, Mem.load chunk m b ofs = Some (VintP p)) ->
    
    exists t, exec_stmt ge e (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le) m f_strlen_loop t (PTree.set _output (VintN (S len)) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m Out_normal.
    
    Proof.
      intros.
      inversion_clear H2.
  
  induction len.
   - intros. (* Base case *)
  assert (exists t, exec_stmt ge e (PTree.set _output (VintN 1) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m f_strlen_loop t
                               (PTree.set _output (VintN 1) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m Out_normal).
        pose (strlen_loop_break_correct2).
       (* 
        apply (strlen_loop_break_correct2 F ge e m b ofs 1 (PTree.set _output (VintN 1) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le))).
        1-3: admit.
        admit. apply gss.
       inversion_clear H2.  inversion_clear H4. simpl. assumption.
        destruct  H4.
        inversion_clear H2.   inversion_clear H5.
        
        
  eexists. 
   (* loop 1 *)
        loop. repeat econstructor. eapply gss. repeat gso_assumption.        repeat econstructor. simpl. replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with (ofs).  apply H6. { (* pose (Ptrofs.modulus_eq32 F). ptrofs_compute_add_mul. all: nia. *) admit. } repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos v)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. repeat econstructor. repeat econstructor.
         repeat gso_assumption. repeat econstructor. fold f_strlen_loop.
         replace  (Int.add (Int.repr 0) (Int.repr 1)) with (Int.repr 1) by (auto with ints).
         apply H4.
         (* done! *)

    -.     intros.
           pose (IHlen ge e le m b (ofs + 1) )
*)
 
 (* 
  destruct H2. (* positive *)
  destruct H1. (* trace *)
  eexists.
 (* loop *)
  loop. repeat econstructor. apply gss. repeat gso_assumption. simpl.
  repeat econstructor. simpl. replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs.
   
   apply H2.
  { (* pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia.  *)  admit. } repeat econstructor. simpl. repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos x)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. econstructor. repeat econstructor.
        repeat gso_assumption. repeat econstructor.

        fold f_strlen_loop. replace (Int.add (Int.repr 0) (Int.repr 1)) with (Int.repr 1) by (auto with ints).

        assert (( forall ge e le, (exists t, exec_stmt ge e  (PTree.set _output (VintZ 0) le) m f_strlen_loop t (PTree.set _output (VintN len) le) m Out_normal) -> exists t, exec_stmt ge e  (PTree.set _output (VintZ 1) le) m f_strlen_loop t (PTree.set _output (VintN (S len)) le) m Out_normal)).  
        induction len.
  - (* Base case *)
    (* Break condition *)
    apply strlen_loop_break_correct2. 
*)
    Admitted.

(* Lemma strlen_correct_loop_empty_string_r :
  (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall ge e m b ofs le len,                       
    (* Preconditions on the length of the string and valid offset *)
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->                      
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->
       
    (* C light expression f_strlen returns O and assigns O to output variable *)
    (exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintZ 0) le) m Out_normal) ->
         (* Precondition: reading empty C string from memory *)
    strlen_mem m b ofs O.
Proof.
  intros.
  destruct H5.
  inversion_clear H5.
  inversion H7. rewrite <- H5 in H6.
  clear H5. clear H7.
  clear out'.

  inversion_clear H6.
  inversion_clear H5.
  inversion_clear H6.
  inversion H5.
  subst
  
  simpl in H8.
  econstructor.
  
  
                                                                                                                                                                         
  econstructor.
  assumption.
Qed. *)


    
    (* Old stuff from strlen_spec *)

    (** High-level functional specification *)

Inductive string_length : string -> nat -> Prop :=
| ZeroLen : string_length EmptyString 0
| SuccLen : forall (n : nat) (s : string) (c : Ascii.ascii) , string_length s n -> string_length (String c s) (S n).
    
Definition strlen_fun := String.length.

Parameter strlen_fun_correct : forall (s : string), string_length s (strlen_fun s).

(* Strings as list of bytes *)

Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
  end.

Definition strlen_byte (bs : list byte) := List.length bs.

Definition c_string (s : string) := (string_to_list_byte s)++(Byte.repr 0)::nil.
Definition example := c_string "Hello".

Lemma length_string_byte_equiv : forall s, String.length s = strlen_byte (string_to_list_byte s).
Proof.
  induction s.
  - simpl. reflexivity.
  - simpl. rewrite <- IHs. reflexivity.
Qed.

Parameter strlen_byte_correct : forall (s : string), string_length s (strlen_byte (string_to_list_byte s)).

(* Connection high-level and low-level specification *)

(* Address (b,ofs) is a block b an offset ofs *)

Definition addr : Type := (Values.block*Z).
Definition block_of (addr : addr) := match addr with (b,_) => b end.
(* Valid block in m *)
Definition valid_block_b (m : mem) (b : Values.block):=
  plt b (Memory.Mem.nextblock m).

(* Assume the low-level spec outputs the values read *)
Parameter strlen_C_byte : mem -> addr -> option (Z*mem*list byte).

Definition strlen_C_correct := forall m p z m' bs, strlen_C_byte m p = Some (z,m',bs) -> Z.of_nat (strlen_byte bs) = z.

(** Low-level specification *)

(* true if the integer value read is zero - end of string *)
Definition is_null (v : Values.val) :=
  match v with
  | Vint zero => true
  | _ => false
  end.


Definition INTSIZE := (nat_of_Z Int.modulus).

Fixpoint strlen_fun_C (m : mem) (b : block) (ofs : Z) (l: Z) (intrange : nat) {struct intrange} : option (Z*mem):= (* maybe nat output? *)
      match intrange with
      | O => None (* out of int range *)
      | S n => match Mem.load chunk m b ofs with (*  loading value from memory *)
              | Some v =>
                if is_null v
                then Some (l, m) else strlen_fun_C m b (ofs + 1) (l + 1) n  
              | None => None (* address not readable or b not allocated *)
              end
      end.

Definition strlen_C_fun_spec (m : mem) (b: block) (ofs : Z) :=  strlen_fun_C m b ofs 0 INTSIZE.

(* Coercion Int.intval : Int.int >-> Z.*)
