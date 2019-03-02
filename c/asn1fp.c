#include <stdio.h>

#include <REAL.h>
#include <check-REAL.h>

#include <caml/callback.h>
#include <caml/mlvalues.h>

int coq_double2REAL(double *d, REAL_t *asnreal) {
    static value *closure = NULL;
    if (closure == NULL) {
        closure = caml_named_value("ocaml_double_to_ber");
    }

    return 1;
}

int coq_REAL2double(REAL_t *asnreal, double *d) {
    static value *closure = NULL;
    if (closure == NULL) {
        closure = caml_named_value("ocaml_ber_to_double");
    }

    return 1;
}