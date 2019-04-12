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

Inductive strlen_spec_C : mem -> addr -> option (Z*mem) -> Prop :=
| UninitMemory : forall m addr, not (Mem.valid_block m (block_of addr)) -> strlen_spec_C m addr None. (* Block of addr is not initialized in m *)
(*TODO *)

(* true if the integer value read is zero - end of string *)
Definition is_null (v : Values.val) :=
  match v with
  | Vint zero => true
  | _ => false
  end.

Definition chunk : memory_chunk := Mint8signed. (* not quite sure how to deal with the memory chunks *)
Definition INTSIZE := (nat_of_Z Int.modulus).


Definition strlen_C (m : mem) (b: block) (ofs : Z) := 
  let fix strlen_fun_C (m : mem) (b : block) (ofs : Z) (l: Z) (intrange : nat) {struct intrange} : option (Z*mem):=
      match intrange with
      | O => None (* out of int range *)
      | S n => match valid_block_b m b, Mem.load chunk m b ofs with (* checking if b is a valid reference in m, loading value from memory *)
              | left _, Some v =>
                if is_null v
                then Some (l, m) else strlen_fun_C m b (ofs + 1) (l + 1) n  
              | _, _ => None (* address not readable or b not allocates *)
              end
      end
  in strlen_fun_C m b ofs 0 INTSIZE.


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

(* Require Import strlen Maps.
Definition ge := globalenv prog. *)

Parameter ge : genv. (* global environment *)
Definition bigStepExec := ClightBigstep.exec_stmt.
Definition t := ((E0**E0)**E0). (* trace, E0 is an empty trace *)

(* Find proofs on arithmetic on ptrofs type *)
Hypothesis ptr_ofs_eq : forall ofs, ofs = (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))).

(* One direction of correctness, for now the statement is wrong *)

Definition strlen_C_exec_corr :
  forall m b ofs (e : env) le z,
    strlen_C m b ofs = Some (z,m) -> 
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) ->
             exists le', le'!_i = Some (Vint (Int.repr z)) /\ bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr z),tuint))).
Proof.
  intros.
  exists (Maps.PTree.set _i (Vint (Int.repr z)) le).
  split.
  - apply Maps.PTree.gss.
  - repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply PTree.gss.
    + repeat econstructor. 
    + simpl. rewrite <- (ptr_ofs_eq ofs). (* now need assumptions on memory, get from a lemma about strlen *) admit.
    + simpl.  admit.
    + simpl. admit.
    + simpl.  admit.
      Admitted.

(* Examples of running a program: to see what assumptions need in the proof *)

Parameter hi : Z.
Definition init_mem := fst (Mem.alloc Mem.empty 0 hi).
Definition b' := snd (Mem.alloc Mem.empty 0 hi).
Parameter ofs' : Z.
Hypothesis ofs_le_hi : ofs' < hi.

(* Example 1 : output on empty string is correct *)

Definition init_mem1 := 
  Mem.store Mint8signed init_mem b' ofs' (Vint (Int.repr 0)).

Lemma example_comp : forall m le, init_mem1 = Some m ->
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

(* Running on a non-empty string: some problem with the loop  *)

Definition init_mem0 := fst (Mem.alloc Mem.empty 0 hi).
Definition init_mem2 := Mem.store Mint8signed init_mem0 b' ofs' (Vint (Int.repr 1)).
Definition init_mem3 := match init_mem2 with
                        | None => None
                        | Some m => Mem.store Mint8signed m b' (ofs'+1) (Vint (Int.repr 0))
                        end.

Lemma example_comp2 : forall m le,
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
    + Print exec_stmt. admit. (* false *)
Admitted.

     
(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)