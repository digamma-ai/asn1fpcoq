From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

(* This is a tutorial to help you start using CompCert's C light language and its sematics *)

(** 
 
I. C light syntax: 
  1) C light types 
     - integers
     - pointer offsets
  2) C light expressions and statements
II. Big-step semantics of C light:
  1) Values
  2) Memory model
  3) Execution of statements

 **)

(* In C light all expressions are annotated with their types. For the types see Ctypes *)
(* Expressions start with E, statements with S *)

(** * Abstract syntax *)

(** * Syntax of types *)

(** Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16, or 32 bits, or the special [IBool] size
  standing for the C99 [_Bool] type.  64-bit integers are treated separately. *)

Print Ctypes.type.

Inductive type : Type :=
  | Tvoid: type                                    (**r the [void] type *)
  | Tint: intsize -> signedness -> attr -> type    (**r integer types *)
  | Tlong: signedness -> attr -> type              (**r 64-bit integer types *)
  | Tfloat: floatsize -> attr -> type              (**r floating-point types *)
  | Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
  | Tstruct: ident -> attr -> type                 (**r struct types *)
  | Tunion: ident -> attr -> type                  (**r union types *)
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.

(** ** Expressions *)

(** Clight expressions correspond to the "pure" subset of C expressions.
  The main omissions are string literals and assignment operators
  ([=], [+=], [++], etc).  In Clight, assignment is a statement,
  not an expression.  Additionally, an expression can also refer to
  temporary variables, which are a separate class of local variables
  that do not reside in memory and whose address cannot be taken.

  As in Compcert C, all expressions are annotated with their types,
  as needed to resolve operator overloading and type-dependent behaviors. *)

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr.       (**r alignment of a type *)


Print Clight.statement.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

(** The C loops are derived forms. *)

Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor (s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).

(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
                            }.
(* Our goal is to prove that programs written in C light behave as intented. To do this we need to formalize the notion of meaning of a C light program. We do this using what is called operational semantics.

In C light everything is an abstract syntax tree. First, we want to assign meaning to expressions and statements. We have primitive values:
 *)

(* Values *)

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vlong: int64 -> val
  | Vfloat: float -> val
  | Vsingle: float32 -> val
  | Vptr: block -> ptrofs -> val.

(* Constants evaluate to values *) 

(* ``` Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Vlong i).``` *)

(* TODO: l-value and r-value *)
(* Variable and pointer values depend on the local and global environments and memory *)
(*  le!id means get a value associated to the key `id` from the local environment *)


(* ```| eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v``` *) 

(*
``` | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs).```  *)

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

(** [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. *)

(* Local environment. Uses Maps.Ptree *)

(** Applicative finite maps. A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned. *)

Parameter le : temp_env.

Print temp_env.

Locate PTree.tree.

Notation "a ! b" := (PTree.get b a) (at level 1).

(* 
Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Vlong i)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) m = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Esizeof: forall ty1 ty,
      eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | eval_Ealignof: forall ty1 ty,
      eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs ->
      deref_loc (typeof a) m loc ofs v ->
      eval_expr a v. *)


(* | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs *)

(* To evaluate pointers we need to access memory *)

Print deref_loc.

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

(* with eval_lvalue: expr -> block -> ptrofs -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs
 | eval_Efield_struct:   forall a i ty l ofs id co att delta,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tstruct id att ->
      ge.(genv_cenv)!id = Some co ->
      field_offset ge i (co_members co) = OK delta ->
      eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta))
 | eval_Efield_union:   forall a i ty l ofs id co att,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tunion id att ->
      ge.(genv_cenv)!id = Some co ->
      eval_lvalue (Efield a i ty) l ofs. *)

(* Now we want to say smth about how to evaluate statements. There are several ways to do it. Here we consider big-step operational semantics. We recursively specify how a statement is evaluated. See ClightBigstep.v  *)

(** ** Big-step semantics for terminating statements and functions *)

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

(** [exec_stmt ge e m1 s t m2 out] describes the execution of
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

Parameter ge : genv. (* explain global, local and temp environment *)
Print exec_stmt.

(* Inductive exec_stmt: env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e le m,
      exec_stmt e le m Sskip
               E0 le m Out_normal
  | exec_Sassign:   forall e le m a1 a2 loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      exec_stmt e le m (Sassign a1 a2)
               E0 le m' Out_normal
  | exec_Sset:     forall e le m id a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sset id a)
               E0 (PTree.set id v le) m Out_normal
  | exec_Scall:   forall e le m optid a al tyargs tyres cconv vf vargs f t m' vres,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      eval_funcall m f vargs t m' vres ->
      exec_stmt e le m (Scall optid a al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sbuiltin:   forall e le m optid ef al tyargs vargs t m' vres,
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      exec_stmt e le m (Sbuiltin optid ef tyargs al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sseq_1:   forall e le m s1 s2 t1 le1 m1 t2 le2 m2 out,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out ->
      exec_stmt e le m (Ssequence s1 s2)
                (t1 ** t2) le2 m2 out
  | exec_Sseq_2:   forall e le m s1 s2 t1 le1 m1 out,
      exec_stmt e le m s1 t1 le1 m1 out ->
      out <> Out_normal ->
      exec_stmt e le m (Ssequence s1 s2)
                t1 le1 m1 out
  | exec_Sifthenelse: forall e le m a s1 s2 v1 b t le' m' out,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      exec_stmt e le m (if b then s1 else s2) t le' m' out ->
      exec_stmt e le m (Sifthenelse a s1 s2)
                t le' m' out
  | exec_Sreturn_none:   forall e le m,
      exec_stmt e le m (Sreturn None)
               E0 le m (Out_return None)
  | exec_Sreturn_some: forall e le m a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sreturn (Some a))
                E0 le m (Out_return (Some (v, typeof a)))
  | exec_Sbreak:   forall e le m,
      exec_stmt e le m Sbreak
               E0 le m Out_break
  | exec_Scontinue:   forall e le m,
      exec_stmt e le m Scontinue
               E0 le m Out_continue
  | exec_Sloop_stop1: forall e le m s1 s2 t le' m' out' out,
      exec_stmt e le m s1 t le' m' out' ->
      out_break_or_return out' out ->
      exec_stmt e le m (Sloop s1 s2)
                t le' m' out
  | exec_Sloop_stop2: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt e le m (Sloop s1 s2)
                (t1**t2) le2 m2 out
  | exec_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 Out_normal ->
      exec_stmt e le2 m2 (Sloop s1 s2) t3 le3 m3 out ->
      exec_stmt e le m (Sloop s1 s2)
                (t1**t2**t3) le3 m3 out
  | exec_Sswitch:   forall e le m a t v n sl le1 m1 out,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      exec_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t le1 m1 out ->
      exec_stmt e le m (Sswitch a sl)
                t le1 m1 (outcome_switch out). *)

(* Operational semantics example: factorial, see factorial.v *)
