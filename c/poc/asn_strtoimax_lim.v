From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "/home/olga/asn1c/skeletons/asn_strtoimax_lim.c"%string.
  Definition normalized := true.
End Info.

Definition _ASN__PRIMITIVE_TYPE_free : ident := 138%positive.
Definition _INTEGER_compare : ident := 142%positive.
Definition _INTEGER_decode_oer : ident := 146%positive.
Definition _INTEGER_decode_uper : ident := 148%positive.
Definition _INTEGER_decode_xer : ident := 144%positive.
Definition _INTEGER_encode_der : ident := 143%positive.
Definition _INTEGER_encode_oer : ident := 147%positive.
Definition _INTEGER_encode_uper : ident := 149%positive.
Definition _INTEGER_encode_xer : ident := 145%positive.
Definition _INTEGER_print : ident := 141%positive.
Definition _INTEGER_random_fill : ident := 150%positive.
Definition ___builtin_ais_annot : ident := 81%positive.
Definition ___builtin_annot : ident := 88%positive.
Definition ___builtin_annot_intval : ident := 89%positive.
Definition ___builtin_bswap : ident := 82%positive.
Definition ___builtin_bswap16 : ident := 84%positive.
Definition ___builtin_bswap32 : ident := 83%positive.
Definition ___builtin_bswap64 : ident := 114%positive.
Definition ___builtin_clz : ident := 115%positive.
Definition ___builtin_clzl : ident := 116%positive.
Definition ___builtin_clzll : ident := 117%positive.
Definition ___builtin_ctz : ident := 118%positive.
Definition ___builtin_ctzl : ident := 119%positive.
Definition ___builtin_ctzll : ident := 120%positive.
Definition ___builtin_debug : ident := 132%positive.
Definition ___builtin_fabs : ident := 85%positive.
Definition ___builtin_fmadd : ident := 123%positive.
Definition ___builtin_fmax : ident := 121%positive.
Definition ___builtin_fmin : ident := 122%positive.
Definition ___builtin_fmsub : ident := 124%positive.
Definition ___builtin_fnmadd : ident := 125%positive.
Definition ___builtin_fnmsub : ident := 126%positive.
Definition ___builtin_fsqrt : ident := 86%positive.
Definition ___builtin_membar : ident := 90%positive.
Definition ___builtin_memcpy_aligned : ident := 87%positive.
Definition ___builtin_nop : ident := 131%positive.
Definition ___builtin_read16_reversed : ident := 127%positive.
Definition ___builtin_read32_reversed : ident := 128%positive.
Definition ___builtin_va_arg : ident := 92%positive.
Definition ___builtin_va_copy : ident := 93%positive.
Definition ___builtin_va_end : ident := 94%positive.
Definition ___builtin_va_start : ident := 91%positive.
Definition ___builtin_write16_reversed : ident := 129%positive.
Definition ___builtin_write32_reversed : ident := 130%positive.
Definition ___compcert_i64_dtos : ident := 99%positive.
Definition ___compcert_i64_dtou : ident := 100%positive.
Definition ___compcert_i64_sar : ident := 111%positive.
Definition ___compcert_i64_sdiv : ident := 105%positive.
Definition ___compcert_i64_shl : ident := 109%positive.
Definition ___compcert_i64_shr : ident := 110%positive.
Definition ___compcert_i64_smod : ident := 107%positive.
Definition ___compcert_i64_smulh : ident := 112%positive.
Definition ___compcert_i64_stod : ident := 101%positive.
Definition ___compcert_i64_stof : ident := 103%positive.
Definition ___compcert_i64_udiv : ident := 106%positive.
Definition ___compcert_i64_umod : ident := 108%positive.
Definition ___compcert_i64_umulh : ident := 113%positive.
Definition ___compcert_i64_utod : ident := 102%positive.
Definition ___compcert_i64_utof : ident := 104%positive.
Definition ___compcert_va_composite : ident := 98%positive.
Definition ___compcert_va_float64 : ident := 97%positive.
Definition ___compcert_va_int32 : ident := 95%positive.
Definition ___compcert_va_int64 : ident := 96%positive.
Definition _all_tags : ident := 66%positive.
Definition _all_tags_count : ident := 67%positive.
Definition _asn_TYPE_descriptor_s : ident := 4%positive.
Definition _asn_TYPE_member_s : ident := 69%positive.
Definition _asn_TYPE_operation_s : ident := 57%positive.
Definition _asn_TYPE_outmost_tag : ident := 137%positive.
Definition _asn_bit_data_s : ident := 15%positive.
Definition _asn_bit_outp_s : ident := 22%positive.
Definition _asn_codec_ctx_s : ident := 2%positive.
Definition _asn_dec_rval_s : ident := 10%positive.
Definition _asn_enc_rval_s : ident := 7%positive.
Definition _asn_encoding_constraints_s : ident := 54%positive.
Definition _asn_generic_no_constraint : ident := 133%positive.
Definition _asn_generic_unknown_constraint : ident := 134%positive.
Definition _asn_oer_constraint_number_s : ident := 38%positive.
Definition _asn_oer_constraints_s : ident := 39%positive.
Definition _asn_per_constraint_s : ident := 28%positive.
Definition _asn_per_constraints_s : ident := 33%positive.
Definition _asn_random_fill_result_s : ident := 35%positive.
Definition _asn_strtoimax_lim : ident := 158%positive.
Definition _asn_type_selector_result_s : ident := 42%positive.
Definition _ber_decode_primitive : ident := 139%positive.
Definition _ber_decoder : ident := 46%positive.
Definition _buffer : ident := 11%positive.
Definition _code : ident := 8%positive.
Definition _code2value : ident := 32%positive.
Definition _compare_struct : ident := 45%positive.
Definition _consumed : ident := 9%positive.
Definition _d : ident := 157%positive.
Definition _default_value_cmp : ident := 79%positive.
Definition _default_value_set : ident := 80%positive.
Definition _der_encode_primitive : ident := 140%positive.
Definition _der_encoder : ident := 47%positive.
Definition _effective_bits : ident := 25%positive.
Definition _elements : ident := 70%positive.
Definition _elements_count : ident := 71%positive.
Definition _encoded : ident := 3%positive.
Definition _encoding_constraints : ident := 68%positive.
Definition _end : ident := 152%positive.
Definition _failed_type : ident := 5%positive.
Definition _flags : ident := 23%positive.
Definition _flushed_bytes : ident := 21%positive.
Definition _free_struct : ident := 43%positive.
Definition _general_constraints : ident := 60%positive.
Definition _intp : ident := 153%positive.
Definition _last_digit_max : ident := 156%positive.
Definition _length : ident := 34%positive.
Definition _lower_bound : ident := 26%positive.
Definition _main : ident := 159%positive.
Definition _max_stack_size : ident := 1%positive.
Definition _memb_offset : ident := 74%positive.
Definition _moved : ident := 14%positive.
Definition _name : ident := 61%positive.
Definition _nbits : ident := 13%positive.
Definition _nboff : ident := 12%positive.
Definition _oer_constraints : ident := 58%positive.
Definition _oer_decode_primitive : ident := 135%positive.
Definition _oer_decoder : ident := 50%positive.
Definition _oer_encode_primitive : ident := 136%positive.
Definition _oer_encoder : ident := 51%positive.
Definition _op : ident := 63%positive.
Definition _op_key : ident := 20%positive.
Definition _optional : ident := 73%positive.
Definition _outmost_tag : ident := 56%positive.
Definition _output : ident := 19%positive.
Definition _per_constraints : ident := 59%positive.
Definition _positive : ident := 37%positive.
Definition _presence_index : ident := 41%positive.
Definition _print_struct : ident := 44%positive.
Definition _random_fill : ident := 55%positive.
Definition _range_bits : ident := 24%positive.
Definition _refill : ident := 16%positive.
Definition _refill_key : ident := 17%positive.
Definition _sign : ident := 154%positive.
Definition _size : ident := 30%positive.
Definition _specifics : ident := 72%positive.
Definition _str : ident := 151%positive.
Definition _structure_ptr : ident := 6%positive.
Definition _tag : ident := 75%positive.
Definition _tag_mode : ident := 76%positive.
Definition _tags : ident := 64%positive.
Definition _tags_count : ident := 65%positive.
Definition _tmpspace : ident := 18%positive.
Definition _type : ident := 77%positive.
Definition _type_descriptor : ident := 40%positive.
Definition _type_selector : ident := 78%positive.
Definition _uper_decoder : ident := 52%positive.
Definition _uper_encoder : ident := 53%positive.
Definition _upper_bound : ident := 27%positive.
Definition _upper_boundary : ident := 155%positive.
Definition _value : ident := 29%positive.
Definition _value2code : ident := 31%positive.
Definition _width : ident := 36%positive.
Definition _xer_decoder : ident := 48%positive.
Definition _xer_encoder : ident := 49%positive.
Definition _xml_tag : ident := 62%positive.
Definition _t'1 : ident := 160%positive.
Definition _t'2 : ident := 161%positive.
Definition _t'3 : ident := 162%positive.
Definition _t'4 : ident := 163%positive.
Definition _t'5 : ident := 164%positive.
Definition _t'6 : ident := 165%positive.

Definition f_asn_strtoimax_lim := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_end, (tptr (tptr tschar))) ::
                (_intp, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_sign, tint) :: (_value, tlong) ::
               (_upper_boundary, tlong) :: (_last_digit_max, tlong) ::
               (_d, tint) :: (_t'6, (tptr tschar)) ::
               (_t'5, (tptr tschar)) :: (_t'4, tschar) ::
               (_t'3, (tptr tschar)) :: (_t'2, tschar) :: (_t'1, tschar) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _sign (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sset _upper_boundary
      (Ebinop Odiv
        (Ebinop Oshr
          (Eunop Onotint (Ecast (Econst_int (Int.repr 0) tint) tulong)
            tulong) (Econst_int (Int.repr 1) tint) tulong)
        (Econst_int (Int.repr 10) tint) tulong))
    (Ssequence
      (Sset _last_digit_max
        (Ebinop Omod
          (Ebinop Oshr
            (Eunop Onotint (Ecast (Econst_int (Int.repr 0) tint) tulong)
              tulong) (Econst_int (Int.repr 1) tint) tulong)
          (Econst_int (Int.repr 10) tint) tulong))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar)))
          (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                         (Etempvar _t'6 (tptr tschar)) tint)
            (Sreturn (Some (Econst_int (Int.repr (-2)) tint)))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'4 (Ederef (Etempvar _str (tptr tschar)) tschar))
            (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
              (LScons (Some 45)
                (Ssequence
                  (Sset _last_digit_max
                    (Ebinop Oadd (Etempvar _last_digit_max tlong)
                      (Econst_int (Int.repr 1) tint) tlong))
                  (Sset _sign
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
                (LScons (Some 43)
                  (Ssequence
                    (Sset _str
                      (Ebinop Oadd (Etempvar _str (tptr tschar))
                        (Econst_int (Int.repr 1) tint) (tptr tschar)))
                    (Ssequence
                      (Sset _t'5
                        (Ederef (Etempvar _end (tptr (tptr tschar)))
                          (tptr tschar)))
                      (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                                     (Etempvar _t'5 (tptr tschar)) tint)
                        (Ssequence
                          (Sassign
                            (Ederef (Etempvar _end (tptr (tptr tschar)))
                              (tptr tschar)) (Etempvar _str (tptr tschar)))
                          (Sreturn (Some (Econst_int (Int.repr (-1)) tint))))
                        Sskip)))
                  LSnil))))
          (Ssequence
            (Ssequence
              (Sset _value (Ecast (Econst_int (Int.repr 0) tint) tlong))
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Ederef (Etempvar _end (tptr (tptr tschar)))
                        (tptr tschar)))
                    (Sifthenelse (Ebinop Olt (Etempvar _str (tptr tschar))
                                   (Etempvar _t'3 (tptr tschar)) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sset _t'1 (Ederef (Etempvar _str (tptr tschar)) tschar))
                    (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
                      (LScons (Some 48)
                        Sskip
                        (LScons (Some 49)
                          Sskip
                          (LScons (Some 50)
                            Sskip
                            (LScons (Some 51)
                              Sskip
                              (LScons (Some 52)
                                Sskip
                                (LScons (Some 53)
                                  Sskip
                                  (LScons (Some 54)
                                    Sskip
                                    (LScons (Some 55)
                                      Sskip
                                      (LScons (Some 56)
                                        Sskip
                                        (LScons (Some 57)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'2
                                                (Ederef
                                                  (Etempvar _str (tptr tschar))
                                                  tschar))
                                              (Sset _d
                                                (Ebinop Osub
                                                  (Etempvar _t'2 tschar)
                                                  (Econst_int (Int.repr 48) tint)
                                                  tint)))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _value tlong)
                                                             (Etempvar _upper_boundary tlong)
                                                             tint)
                                                (Sset _value
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Etempvar _value tlong)
                                                      (Econst_int (Int.repr 10) tint)
                                                      tlong)
                                                    (Etempvar _d tint) tlong))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _value tlong)
                                                               (Etempvar _upper_boundary tlong)
                                                               tint)
                                                  (Sifthenelse (Ebinop Ole
                                                                 (Etempvar _d tint)
                                                                 (Etempvar _last_digit_max tlong)
                                                                 tint)
                                                    (Sifthenelse (Ebinop Ogt
                                                                   (Etempvar _sign tint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Sset _value
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Etempvar _value tlong)
                                                            (Econst_int (Int.repr 10) tint)
                                                            tlong)
                                                          (Etempvar _d tint)
                                                          tlong))
                                                      (Ssequence
                                                        (Sset _sign
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Sset _value
                                                          (Ebinop Osub
                                                            (Ebinop Omul
                                                              (Eunop Oneg
                                                                (Etempvar _value tlong)
                                                                tlong)
                                                              (Econst_int (Int.repr 10) tint)
                                                              tlong)
                                                            (Etempvar _d tint)
                                                            tlong))))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Etempvar _end (tptr (tptr tschar)))
                                                          (tptr tschar))
                                                        (Etempvar _str (tptr tschar)))
                                                      (Sreturn (Some (Econst_int (Int.repr (-3)) tint)))))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Etempvar _end (tptr (tptr tschar)))
                                                        (tptr tschar))
                                                      (Etempvar _str (tptr tschar)))
                                                    (Sreturn (Some (Econst_int (Int.repr (-3)) tint))))))
                                              Scontinue))
                                          (LScons None
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Etempvar _end (tptr (tptr tschar)))
                                                  (tptr tschar))
                                                (Etempvar _str (tptr tschar)))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Etempvar _intp (tptr tlong))
                                                    tlong)
                                                  (Ebinop Omul
                                                    (Etempvar _sign tint)
                                                    (Etempvar _value tlong)
                                                    tlong))
                                                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
                                            LSnil))))))))))))))
                (Sset _str
                  (Ebinop Oadd (Etempvar _str (tptr tschar))
                    (Econst_int (Int.repr 1) tint) (tptr tschar)))))
            (Ssequence
              (Sassign
                (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar))
                (Etempvar _str (tptr tschar)))
              (Ssequence
                (Sassign (Ederef (Etempvar _intp (tptr tlong)) tlong)
                  (Ebinop Omul (Etempvar _sign tint) (Etempvar _value tlong)
                    tlong))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _asn_codec_ctx_s Struct ((_max_stack_size, tuint) :: nil) noattr ::
 Composite _asn_enc_rval_s Struct
   ((_encoded, tint) ::
    (_failed_type, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_structure_ptr, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_dec_rval_s Struct
   ((_code, tint) :: (_consumed, tuint) :: nil)
   noattr ::
 Composite _asn_bit_data_s Struct
   ((_buffer, (tptr tuchar)) :: (_nboff, tuint) :: (_nbits, tuint) ::
    (_moved, tuint) ::
    (_refill,
     (tptr (Tfunction (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil)
             tint cc_default))) :: (_refill_key, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_bit_outp_s Struct
   ((_buffer, (tptr tuchar)) :: (_nboff, tuint) :: (_nbits, tuint) ::
    (_tmpspace, (tarray tuchar 32)) ::
    (_output,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons tuint (Tcons (tptr tvoid) Tnil)))
             tint cc_default))) :: (_op_key, (tptr tvoid)) ::
    (_flushed_bytes, tuint) :: nil)
   noattr ::
 Composite _asn_per_constraint_s Struct
   ((_flags, tint) :: (_range_bits, tint) :: (_effective_bits, tint) ::
    (_lower_bound, tint) :: (_upper_bound, tint) :: nil)
   noattr ::
 Composite _asn_per_constraints_s Struct
   ((_value, (Tstruct _asn_per_constraint_s noattr)) ::
    (_size, (Tstruct _asn_per_constraint_s noattr)) ::
    (_value2code, (tptr (Tfunction (Tcons tuint Tnil) tint cc_default))) ::
    (_code2value, (tptr (Tfunction (Tcons tuint Tnil) tint cc_default))) ::
    nil)
   noattr ::
 Composite _asn_random_fill_result_s Struct
   ((_code, tint) :: (_length, tuint) :: nil)
   noattr ::
 Composite _asn_oer_constraint_number_s Struct
   ((_width, tuint) :: (_positive, tuint) :: nil)
   noattr ::
 Composite _asn_oer_constraints_s Struct
   ((_value, (Tstruct _asn_oer_constraint_number_s noattr)) ::
    (_size, tint) :: nil)
   noattr ::
 Composite _asn_type_selector_result_s Struct
   ((_type_descriptor, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_presence_index, tuint) :: nil)
   noattr ::
 Composite _asn_TYPE_operation_s Struct
   ((_free_struct,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid cc_default))) ::
    (_print_struct,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid)
                 (Tcons tint
                   (Tcons
                     (tptr (Tfunction
                             (Tcons (tptr tvoid)
                               (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                             cc_default)) (Tcons (tptr tvoid) Tnil))))) tint
             cc_default))) ::
    (_compare_struct,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) tint
             cc_default))) ::
    (_ber_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (tptr tvoid))
                     (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil)))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_der_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr tvoid)
                   (Tcons tint
                     (Tcons tuint
                       (Tcons
                         (tptr (Tfunction
                                 (Tcons (tptr tvoid)
                                   (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                 tint cc_default)) (Tcons (tptr tvoid) Tnil)))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_xer_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (tptr tvoid))
                     (Tcons (tptr tschar)
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_xer_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr tvoid)
                   (Tcons tint
                     (Tcons tint
                       (Tcons
                         (tptr (Tfunction
                                 (Tcons (tptr tvoid)
                                   (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                 tint cc_default)) (Tcons (tptr tvoid) Tnil)))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_oer_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
                     (Tcons (tptr (tptr tvoid))
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_oer_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
                   (Tcons (tptr tvoid)
                     (Tcons
                       (tptr (Tfunction
                               (Tcons (tptr tvoid)
                                 (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                               tint cc_default)) (Tcons (tptr tvoid) Tnil))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_uper_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
                     (Tcons (tptr (tptr tvoid))
                       (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_uper_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
                   (Tcons (tptr tvoid)
                     (Tcons (tptr (Tstruct _asn_bit_outp_s noattr)) Tnil)))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_random_fill,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_random_fill_result_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr (tptr tvoid))
                   (Tcons (tptr (Tstruct _asn_encoding_constraints_s noattr))
                     (Tcons tuint Tnil))))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_outmost_tag,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))) tuint
             cc_default))) :: nil)
   noattr ::
 Composite _asn_encoding_constraints_s Struct
   ((_oer_constraints, (tptr (Tstruct _asn_oer_constraints_s noattr))) ::
    (_per_constraints, (tptr (Tstruct _asn_per_constraints_s noattr))) ::
    (_general_constraints,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid)
                 (Tcons
                   (tptr (Tfunction
                           (Tcons (tptr tvoid)
                             (Tcons
                               (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                               (Tcons (tptr tvoid)
                                 (Tcons (tptr tschar) Tnil)))) tvoid
                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                   (Tcons (tptr tvoid) Tnil)))) tint cc_default))) :: nil)
   noattr ::
 Composite _asn_TYPE_descriptor_s Struct
   ((_name, (tptr tschar)) :: (_xml_tag, (tptr tschar)) ::
    (_op, (tptr (Tstruct _asn_TYPE_operation_s noattr))) ::
    (_tags, (tptr tuint)) :: (_tags_count, tuint) ::
    (_all_tags, (tptr tuint)) :: (_all_tags_count, tuint) ::
    (_encoding_constraints, (Tstruct _asn_encoding_constraints_s noattr)) ::
    (_elements, (tptr (Tstruct _asn_TYPE_member_s noattr))) ::
    (_elements_count, tuint) :: (_specifics, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_TYPE_member_s Struct
   ((_flags, tint) :: (_optional, tuint) :: (_memb_offset, tuint) ::
    (_tag, tuint) :: (_tag_mode, tint) ::
    (_type, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_type_selector,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_type_selector_result_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr tvoid) Tnil))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_encoding_constraints, (Tstruct _asn_encoding_constraints_s noattr)) ::
    (_default_value_cmp,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))) ::
    (_default_value_set,
     (tptr (Tfunction (Tcons (tptr (tptr tvoid)) Tnil) tint cc_default))) ::
    (_name, (tptr tschar)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_asn_generic_no_constraint,
   Gfun(External (EF_external "asn_generic_no_constraint"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons
           (tptr (Tfunction
                   (Tcons (tptr tvoid)
                     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                       (Tcons (tptr tvoid) (Tcons (tptr tschar) Tnil))))
                   tvoid
                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
           (Tcons (tptr tvoid) Tnil)))) tint cc_default)) ::
 (_asn_generic_unknown_constraint,
   Gfun(External (EF_external "asn_generic_unknown_constraint"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons
           (tptr (Tfunction
                   (Tcons (tptr tvoid)
                     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                       (Tcons (tptr tvoid) (Tcons (tptr tschar) Tnil))))
                   tvoid
                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
           (Tcons (tptr tvoid) Tnil)))) tint cc_default)) ::
 (_oer_decode_primitive,
   Gfun(External (EF_external "oer_decode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_oer_encode_primitive,
   Gfun(External (EF_external "oer_encode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons
               (tptr (Tfunction
                       (Tcons (tptr tvoid)
                         (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                       cc_default)) (Tcons (tptr tvoid) Tnil)))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_asn_TYPE_outmost_tag,
   Gfun(External (EF_external "asn_TYPE_outmost_tag"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))) tuint
     cc_default)) ::
 (_ASN__PRIMITIVE_TYPE_free,
   Gfun(External (EF_external "ASN__PRIMITIVE_TYPE_free"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid cc_default)) ::
 (_ber_decode_primitive,
   Gfun(External (EF_external "ber_decode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_der_encode_primitive,
   Gfun(External (EF_external "der_encode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tuint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_print,
   Gfun(External (EF_external "INTEGER_print"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons tint
           (Tcons
             (tptr (Tfunction
                     (Tcons (tptr tvoid)
                       (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                     cc_default)) (Tcons (tptr tvoid) Tnil))))) tint
     cc_default)) ::
 (_INTEGER_compare,
   Gfun(External (EF_external "INTEGER_compare"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) tint cc_default)) ::
 (_INTEGER_encode_der,
   Gfun(External (EF_external "INTEGER_encode_der"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tuint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_decode_xer,
   Gfun(External (EF_external "INTEGER_decode_xer"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tschar) (Tcons (tptr tvoid) (Tcons tuint Tnil)))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_encode_xer,
   Gfun(External (EF_external "INTEGER_encode_xer"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_decode_oer,
   Gfun(External (EF_external "INTEGER_decode_oer"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_encode_oer,
   Gfun(External (EF_external "INTEGER_encode_oer"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons
               (tptr (Tfunction
                       (Tcons (tptr tvoid)
                         (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                       cc_default)) (Tcons (tptr tvoid) Tnil)))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_decode_uper,
   Gfun(External (EF_external "INTEGER_decode_uper"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_encode_uper,
   Gfun(External (EF_external "INTEGER_encode_uper"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons (tptr (Tstruct _asn_bit_outp_s noattr)) Tnil))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_INTEGER_random_fill,
   Gfun(External (EF_external "INTEGER_random_fill"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_random_fill_result_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (tptr tvoid))
           (Tcons (tptr (Tstruct _asn_encoding_constraints_s noattr))
             (Tcons tuint Tnil))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_asn_strtoimax_lim, Gfun(Internal f_asn_strtoimax_lim)) :: nil).

Definition public_idents : list ident :=
(_asn_strtoimax_lim :: _INTEGER_random_fill :: _INTEGER_encode_uper ::
 _INTEGER_decode_uper :: _INTEGER_encode_oer :: _INTEGER_decode_oer ::
 _INTEGER_encode_xer :: _INTEGER_decode_xer :: _INTEGER_encode_der ::
 _INTEGER_compare :: _INTEGER_print :: _der_encode_primitive ::
 _ber_decode_primitive :: _ASN__PRIMITIVE_TYPE_free ::
 _asn_TYPE_outmost_tag :: _oer_encode_primitive :: _oer_decode_primitive ::
 _asn_generic_unknown_constraint :: _asn_generic_no_constraint ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


