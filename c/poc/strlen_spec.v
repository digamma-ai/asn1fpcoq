(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)


From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values.
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

Print memory_chunk.

Definition chunk : memory_chunk := Mint8unsigned. (* not quite sure how to deal with the memory chunks *)
Definition INTSIZE := (nat_of_Z Int.modulus).

Definition strlen_C (m : mem) (b: block) (ofs : Z) := 
  let fix strlen_fun_C (m : mem) (b : block) (ofs : Z) (l: Z) (intrange : nat) {struct intrange} : option (Z*mem):=
      match intrange with
      | O => None (* out of int range *)
      | S n => match valid_block_b m b, Mem.load chunk m b ofs with (* checking if b is a valid reference in m, loading value from memory *)
              | left _, Some v =>
                match is_null v, Mem.store chunk m b ofs (Vint (Int.repr l)) with (* storing value, TODO: need to allocate memory? *)
                | false, Some m' => strlen_fun_C m' b (ofs + 1) (l + 1) n
                | true, Some m' => Some (l, m')
                | _, None => None (* cannot store the result in m *)
                end
              | _, _ => None (* address not readable or b not allocates *)
              end
      end
  in strlen_fun_C m b ofs 0 INTSIZE.

(* See Clight.v for semantics *)

Print eval_expr.