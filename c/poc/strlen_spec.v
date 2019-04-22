(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)


From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
(* Local Open Scope Z_scope.*)


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

Definition chunk : memory_chunk := Mint8signed. (* that's what we read from memory *)
Definition INTSIZE := (nat_of_Z Int.modulus).


Fixpoint strlen_fun_C (m : mem) (b : block) (ofs : Z) (l: Z) (intrange : nat) {struct intrange} : option (Z*mem):= (* maybe nat output? *)
      match intrange with
      | O => None (* out of int range *)
      | S n => match valid_block_b m b, Mem.load chunk m b ofs with (* checking if b is a valid reference in m, loading value from memory *)
              | left _, Some v =>
                if is_null v
                then Some (l, m) else strlen_fun_C m b (ofs + 1) (l + 1) n  
              | _, _ => None (* address not readable or b not allocates *)
              end
      end.

Definition strlen_C_fun_spec (m : mem) (b: block) (ofs : Z) :=  strlen_fun_C m b ofs 0 INTSIZE.


(* Relational spec, to use in the proofs *)

Inductive strlen_C_rel_spec : Mem.mem -> block -> Z -> option (nat * mem)-> Prop
  := | CorrectRun :  forall n m b ofs,
    (n < INTSIZE)%nat ->
    forall v, (* Mem.valid_block m b -> *) (* ignore for now *)
              Mem.load chunk m b ofs = Some v ->
              (exists z, v = Vint z) -> (* not Undef *)
              Mem.load chunk m b (ofs + (Z_of_nat n)) = Some (Vint (Int.repr 0)) ->
              strlen_C_rel_spec m b ofs (Some (n,m))
  | OutOfRange :   forall n m b ofs,
    (n > INTSIZE)%nat ->
    forall v, (* Mem.valid_block m b -> *)
              Mem.load chunk m b ofs = Some v ->
              Mem.load chunk m b (ofs + (Z_of_nat n)) = Some (Vint (Int.repr 0)) ->
              strlen_C_rel_spec m b ofs None


  | MemoryLoadZero :  forall n m b ofs,
    (n < INTSIZE)%nat ->
              (* Mem.valid_block m b -> *)
              Mem.load chunk m b ofs = None ->
              strlen_C_rel_spec m b ofs None

  | MemoryLoadSucc : forall n m b ofs,
       (n < INTSIZE)%nat ->
      forall v, (* Mem.valid_block m b -> *)
              Mem.load chunk m b ofs = Some v ->
              Mem.load chunk m b (ofs + (Z_of_nat n)) = Some (Vint (Int.repr 0)) ->
              (exists n', (n' < n)%nat /\ Mem.load chunk m b (ofs + (Z_of_nat n')) = None) ->
              strlen_C_rel_spec m b ofs None.
                                                                           
                            
(* Semantics of a C light function: *)

(* strlen C light AST *)

Definition _i : ident := 54%positive.
Definition _s : ident := 53%positive.
Definition _strlen : ident := 55%positive.

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Sifthenelse (Ebinop One
                     (Ederef
                       (Ebinop Oadd (Etempvar _s (tptr tschar))
                         (Etempvar _i tuint) (tptr tschar)) tschar)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        Sbreak)
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Sreturn (Some (Etempvar _i tuint))))
                      |}.

(* Big step semantics *)

Definition Vint_of_nat := fun n => Vint (Int.repr(Z_of_nat n)).

(* One direction of correctness, using functional spec, below relational with proof attempt *)

 Definition strlen_C_fun_corr_r :
  forall (ge :genv) (m : Mem.mem) (b : block) (ofs : Z) (e : env) (le : temp_env) (z : Z),
    strlen_C_fun_spec m b ofs = Some (z,m) ->
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> (* input parameter _s assigned value of address (b,ofs) in le *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr z),tuint))) /\ le'!_i = Some (Vint (Int.repr z)).
               (* in environments ge, e (local env), le and memory m with output trace t, output _i assigned value z *)
Proof.
  intros.
  repeat eexists.
  (* econstructor can choose a wrong case in exec_stmt *)
  eapply exec_Sseq_1. eapply exec_Sseq_1. econstructor. econstructor.
  (* loop *)
  (* - apply Maps.PTree.gss.
    - repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply PTree.gss.
    + repeat econstructor. *)
Admitted.

 (* Find proofs on arithmetic on ptrofs type to rewrite this *)
      Hypothesis ptr_ofs_eq : forall ofs, ofs = (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))). 

      
Definition strlen_C_rel_corr_r : forall n m b ofs e le,
    strlen_C_rel_spec m b ofs (Some (n,m)) ->
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> 
    exists le', le'!_i = Some (Vint_of_nat n) /\ 
           bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((Vint_of_nat n),tuint))).
Proof.
  induction n.
  (* Base case. *)
    intros.
    inversion H. unfold chunk in *. destruct H4.
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