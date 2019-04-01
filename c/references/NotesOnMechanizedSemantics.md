### Section 1: Intro
Deep embedding of C light to Coq := the abstract syntax is defined as inductive datatypes

### Section 2: Abstract syntax of C light

Definitions of Types, Expressions, Statements and Programs.

Unsupported features: 

- `extern` declaration of arrays
- structs and unions cannot be passed by value
- type qualifiers (`const`, `volatile`, `restrict`) are erased at parsing
- within expressions no side-effects nor function calls (_meaning all C light expressions always terminate and are pure_)
- statements: in `for(s1, a, s2)` s1 and s2 are statements, that do not terminate by break
- `extern` functions are only declared and not defined,used to model system calls
there are more - see p. 2-7 for details.

### Section 3: Formal semantics for C light

Natural semantics aka big-step operational semantics.
No typing rules ("static semantics") - see `Ctyping.v` in compcert
Dynamic semantics: 

- final result of a program execution
- trace of invocation of external functions
- deterministic (since expressions are pure)

Evaluation done in a context with global vars (G), loval vars (E) and memory state (M). Rules described in Fig.6-10.		   		   
For memory model cf. [29] Leroy, X., Blazy, S.: Formal verification of a C-like memory model and its uses for verifying program transformations. J. Autom. Reason. 41(1), 1–31 (2008)

