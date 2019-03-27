
File *REAL.v* contains output of clightgen on REAL.c. Options ```-fstruct-passing -flongdouble``` are needed due to the features unsupported by compcert: functions returning a struct or union and long double:

```./clightgen -normalize -I ~/asn1c/skeletons/ -fstruct-passing -flongdouble ~/asn1c/skeletons/REAL.c -o REAL.v ```


To build clightgen go to compcert folder 

   ```make clightgen```

Usage: ```clightgen [options] <C source files>```

Some useful options: 
```
   -I<dir>     search <dir> for include files
   -D<symbol>  define preprocessor macro
   -U<symbol>  undefine preprocessor macro

```
   
