(*
 * Parse the number in the given string until the given *end position,
 * returning the position after the last parsed character back using the
 * same (*end) pointer.
 * WARNING: This behavior is different from the standard strtol/strtoimax(3).
 *)

(* STRTOIMAX(3)               Linux Programmer's Manual              STRTOIMAX(3)

NAME
       strtoimax, strtoumax - convert string to integer

SYNOPSIS
       #include <inttypes.h>

       intmax_t strtoimax(const char *nptr, char **endptr, int base);
       uintmax_t strtoumax(const char *nptr, char **endptr, int base);

DESCRIPTION
       These  functions  are  just  like strtol(3) and strtoul(3), except that
       they return a value of type intmax_t and uintmax_t, respectively.

RETURN VALUE
       On success, the converted value is returned.  If nothing was  found  to
       convert, zero is returned.  On overflow or underflow INTMAX_MAX or INT‐
       MAX_MIN or UINTMAX_MAX is returned, and errno is set to ERANGE.
 *)

(* /* Largest integral types.  */
#if __WORDSIZE == 64
typedef long int		intmax_t;
typedef unsigned long int	uintmax_t;
#else
__extension__
typedef long long int		intmax_t;
__extension__
typedef unsigned long long int	uintmax_t;
#endif 

*)
