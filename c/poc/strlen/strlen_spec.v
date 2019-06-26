Inductive strlen (m : mem) (b : block) (ofs : ptrofs) : int -> Prop :=
| LengthZero: load m [b,ofs] = Some 0 -> strlen m b ofs 0
| LengthSucc: forall (n : int) (c : char),
    strlen m b ofs + 1 n ->
    load m [b,ofs]  = Vint c ->
    c <> Int.zero ->
    no_int_overflow n ->
    strlen m b ofs n + 1.
