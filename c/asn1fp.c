#include <stdio.h>
#include <caml/callback.h>
#include <caml/mlvalues.h>

int asn_double2REAL(double *d, char *asnreal) {
    static value *closure = NULL;
    if (closure == NULL) {
        closure = caml_named_value("ocaml_double_to_ber");
    }

    value arg;

    value result;
    result = caml_callback(*closure, arg);

    return 1;
}

int asn_REAL2double(char *asnreal, double *d) {
    static value *closure = NULL;
    if (closure == NULL) {
        closure = caml_named_value("ocaml_ber_to_double");
    }

    return 1;
}

int main(int argc, char const *argv[])
{
    caml_main((char **) argv);
    printf("kek\n");
    return 0;
}