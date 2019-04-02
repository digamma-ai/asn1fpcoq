From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition silly := fun z : Z => z + 1.


Require Import silly.

Definition silly_int := fun n : tuint => 