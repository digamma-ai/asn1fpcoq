From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "REAL.c"%string.
  Definition normalized := true.
End Info.

Definition _ASN__PRIMITIVE_TYPE_free : ident := 165%positive.
Definition _ASN__PRIMITIVE_TYPE_s : ident := 82%positive.
Definition _E : ident := 217%positive.
Definition _OCTET_STRING_compare : ident := 172%positive.
Definition _OCTET_STRING_decode_ber : ident := 173%positive.
Definition _OCTET_STRING_decode_oer : ident := 180%positive.
Definition _OCTET_STRING_decode_uper : ident := 182%positive.
Definition _OCTET_STRING_decode_xer_binary : ident := 176%positive.
Definition _OCTET_STRING_decode_xer_hex : ident := 175%positive.
Definition _OCTET_STRING_decode_xer_utf8 : ident := 177%positive.
Definition _OCTET_STRING_encode_der : ident := 174%positive.
Definition _OCTET_STRING_encode_oer : ident := 181%positive.
Definition _OCTET_STRING_encode_uper : ident := 183%positive.
Definition _OCTET_STRING_encode_xer : ident := 178%positive.
Definition _OCTET_STRING_encode_xer_utf8 : ident := 179%positive.
Definition _OCTET_STRING_free : ident := 169%positive.
Definition _OCTET_STRING_print : ident := 170%positive.
Definition _OCTET_STRING_print_utf8 : ident := 171%positive.
Definition _OCTET_STRING_random_fill : ident := 184%positive.
Definition _REAL__dump : ident := 231%positive.
Definition _REAL__xer_body_decode : ident := 258%positive.
Definition _REAL_compare : ident := 194%positive.
Definition _REAL_decode_oer : ident := 191%positive.
Definition _REAL_decode_uper : ident := 189%positive.
Definition _REAL_decode_xer : ident := 193%positive.
Definition _REAL_encode_oer : ident := 190%positive.
Definition _REAL_encode_uper : ident := 188%positive.
Definition _REAL_encode_xer : ident := 192%positive.
Definition _REAL_print : ident := 195%positive.
Definition _REAL_random_fill : ident := 187%positive.
Definition ___assert_fail : ident := 154%positive.
Definition ___builtin_ais_annot : ident := 86%positive.
Definition ___builtin_annot : ident := 93%positive.
Definition ___builtin_annot_intval : ident := 94%positive.
Definition ___builtin_bswap : ident := 87%positive.
Definition ___builtin_bswap16 : ident := 89%positive.
Definition ___builtin_bswap32 : ident := 88%positive.
Definition ___builtin_bswap64 : ident := 119%positive.
Definition ___builtin_clz : ident := 120%positive.
Definition ___builtin_clzl : ident := 121%positive.
Definition ___builtin_clzll : ident := 122%positive.
Definition ___builtin_ctz : ident := 123%positive.
Definition ___builtin_ctzl : ident := 124%positive.
Definition ___builtin_ctzll : ident := 125%positive.
Definition ___builtin_debug : ident := 137%positive.
Definition ___builtin_fabs : ident := 90%positive.
Definition ___builtin_fmadd : ident := 128%positive.
Definition ___builtin_fmax : ident := 126%positive.
Definition ___builtin_fmin : ident := 127%positive.
Definition ___builtin_fmsub : ident := 129%positive.
Definition ___builtin_fnmadd : ident := 130%positive.
Definition ___builtin_fnmsub : ident := 131%positive.
Definition ___builtin_fsqrt : ident := 91%positive.
Definition ___builtin_membar : ident := 95%positive.
Definition ___builtin_memcpy_aligned : ident := 92%positive.
Definition ___builtin_nop : ident := 136%positive.
Definition ___builtin_read16_reversed : ident := 132%positive.
Definition ___builtin_read32_reversed : ident := 133%positive.
Definition ___builtin_va_arg : ident := 97%positive.
Definition ___builtin_va_copy : ident := 98%positive.
Definition ___builtin_va_end : ident := 99%positive.
Definition ___builtin_va_start : ident := 96%positive.
Definition ___builtin_write16_reversed : ident := 134%positive.
Definition ___builtin_write32_reversed : ident := 135%positive.
Definition ___compcert_i64_dtos : ident := 104%positive.
Definition ___compcert_i64_dtou : ident := 105%positive.
Definition ___compcert_i64_sar : ident := 116%positive.
Definition ___compcert_i64_sdiv : ident := 110%positive.
Definition ___compcert_i64_shl : ident := 114%positive.
Definition ___compcert_i64_shr : ident := 115%positive.
Definition ___compcert_i64_smod : ident := 112%positive.
Definition ___compcert_i64_smulh : ident := 117%positive.
Definition ___compcert_i64_stod : ident := 106%positive.
Definition ___compcert_i64_stof : ident := 108%positive.
Definition ___compcert_i64_udiv : ident := 111%positive.
Definition ___compcert_i64_umod : ident := 113%positive.
Definition ___compcert_i64_umulh : ident := 118%positive.
Definition ___compcert_i64_utod : ident := 107%positive.
Definition ___compcert_i64_utof : ident := 109%positive.
Definition ___compcert_va_composite : ident := 103%positive.
Definition ___compcert_va_float64 : ident := 102%positive.
Definition ___compcert_va_int32 : ident := 100%positive.
Definition ___compcert_va_int64 : ident := 101%positive.
Definition ___errno_location : ident := 164%positive.
Definition ___finite : ident := 155%positive.
Definition ___finitef : ident := 160%positive.
Definition ___finitel : ident := 162%positive.
Definition ___func__ : ident := 202%positive.
Definition ___func____1 : ident := 274%positive.
Definition ___isnan : ident := 156%positive.
Definition ___isnanf : ident := 161%positive.
Definition ___isnanl : ident := 163%positive.
Definition ___stringlit_1 : ident := 197%positive.
Definition ___stringlit_10 : ident := 230%positive.
Definition ___stringlit_11 : ident := 237%positive.
Definition ___stringlit_12 : ident := 238%positive.
Definition ___stringlit_13 : ident := 289%positive.
Definition ___stringlit_2 : ident := 199%positive.
Definition ___stringlit_3 : ident := 200%positive.
Definition ___stringlit_4 : ident := 201%positive.
Definition ___stringlit_5 : ident := 225%positive.
Definition ___stringlit_6 : ident := 226%positive.
Definition ___stringlit_7 : ident := 227%positive.
Definition ___stringlit_8 : ident := 228%positive.
Definition ___stringlit_9 : ident := 229%positive.
Definition __res : ident := 247%positive.
Definition __res__1 : ident := 262%positive.
Definition _a : ident := 241%positive.
Definition _accum : ident := 283%positive.
Definition _adbl : ident := 243%positive.
Definition _all_tags : ident := 66%positive.
Definition _all_tags_count : ident := 67%positive.
Definition _app_key : ident := 206%positive.
Definition _aptr : ident := 239%positive.
Definition _asn_DEF_REAL : ident := 196%positive.
Definition _asn_DEF_REAL_tags : ident := 185%positive.
Definition _asn_OP_REAL : ident := 186%positive.
Definition _asn_REAL2double : ident := 236%positive.
Definition _asn_TYPE_descriptor_s : ident := 4%positive.
Definition _asn_TYPE_member_s : ident := 69%positive.
Definition _asn_TYPE_operation_s : ident := 57%positive.
Definition _asn_TYPE_outmost_tag : ident := 153%positive.
Definition _asn_bit_data_s : ident := 15%positive.
Definition _asn_bit_outp_s : ident := 22%positive.
Definition _asn_codec_ctx_s : ident := 2%positive.
Definition _asn_dec_rval_s : ident := 10%positive.
Definition _asn_double2REAL : ident := 257%positive.
Definition _asn_double2float : ident := 292%positive.
Definition _asn_enc_rval_s : ident := 7%positive.
Definition _asn_encoding_constraints_s : ident := 54%positive.
Definition _asn_generic_no_constraint : ident := 146%positive.
Definition _asn_generic_unknown_constraint : ident := 147%positive.
Definition _asn_oer_constraint_number_s : ident := 38%positive.
Definition _asn_oer_constraints_s : ident := 39%positive.
Definition _asn_per_constraint_s : ident := 28%positive.
Definition _asn_per_constraints_s : ident := 33%positive.
Definition _asn_random_between : ident := 148%positive.
Definition _asn_random_fill_result_s : ident := 35%positive.
Definition _asn_type_selector_result_s : ident := 42%positive.
Definition _assertion_buffer1 : ident := 278%positive.
Definition _assertion_buffer2 : ident := 279%positive.
Definition _b : ident := 242%positive.
Definition _baseF : ident := 272%positive.
Definition _bdbl : ident := 244%positive.
Definition _ber_decode_primitive : ident := 166%positive.
Definition _ber_decoder : ident := 46%positive.
Definition _bmsign : ident := 282%positive.
Definition _bptr : ident := 240%positive.
Definition _buf : ident := 81%positive.
Definition _buf_ptr : ident := 261%positive.
Definition _buffer : ident := 11%positive.
Definition _buflen : ident := 208%positive.
Definition _calloc : ident := 141%positive.
Definition _canonical : ident := 204%positive.
Definition _cb : ident := 205%positive.
Definition _chunk_buf : ident := 251%positive.
Definition _chunk_size : ident := 252%positive.
Definition _code : ident := 8%positive.
Definition _code2value : ident := 32%positive.
Definition _compare_struct : ident := 45%positive.
Definition _constraints : ident := 293%positive.
Definition _consumed : ident := 9%positive.
Definition _copysign : ident := 158%positive.
Definition _d : ident := 203%positive.
Definition _d__1 : ident := 285%positive.
Definition _dbl_value : ident := 263%positive.
Definition _default_value_cmp : ident := 79%positive.
Definition _default_value_set : ident := 80%positive.
Definition _der_encode_primitive : ident := 167%positive.
Definition _der_encoder : ident := 47%positive.
Definition _dot : ident := 211%positive.
Definition _dscr : ident := 277%positive.
Definition _dv : ident := 84%positive.
Definition _effective_bits : ident := 25%positive.
Definition _elements : ident := 70%positive.
Definition _elements_count : ident := 71%positive.
Definition _elen : ident := 270%positive.
Definition _encoded : ident := 3%positive.
Definition _encoding_constraints : ident := 68%positive.
Definition _end : ident := 212%positive.
Definition _end__1 : ident := 221%positive.
Definition _endptr : ident := 254%positive.
Definition _er : ident := 248%positive.
Definition _expptr : ident := 218%positive.
Definition _expval : ident := 269%positive.
Definition _f : ident := 291%positive.
Definition _failed_type : ident := 5%positive.
Definition _first_zero_in_run : ident := 214%positive.
Definition _flags : ident := 23%positive.
Definition _float_big_endian : ident := 276%positive.
Definition _flushed_bytes : ident := 21%positive.
Definition _fmt : ident := 209%positive.
Definition _free : ident := 142%positive.
Definition _free_struct : ident := 43%positive.
Definition _general_constraints : ident := 60%positive.
Definition _i : ident := 255%positive.
Definition _ilevel : ident := 234%positive.
Definition _ilogb : ident := 159%positive.
Definition _ishift : ident := 287%positive.
Definition _last_zero : ident := 213%positive.
Definition _last_zero__1 : ident := 222%positive.
Definition _ldexp : ident := 157%positive.
Definition _len_len : ident := 294%positive.
Definition _length : ident := 34%positive.
Definition _local_buf : ident := 207%positive.
Definition _lower_bound : ident := 26%positive.
Definition _lz_state : ident := 216%positive.
Definition _m : ident := 268%positive.
Definition _main : ident := 308%positive.
Definition _malloc : ident := 140%positive.
Definition _max_length : ident := 304%positive.
Definition _max_stack_size : ident := 1%positive.
Definition _memb_offset : ident := 74%positive.
Definition _memchr : ident := 145%positive.
Definition _memcmp : ident := 144%positive.
Definition _memcpy : ident := 143%positive.
Definition _moved : ident := 14%positive.
Definition _mptr : ident := 288%positive.
Definition _mstop : ident := 280%positive.
Definition _mval : ident := 281%positive.
Definition _name : ident := 61%positive.
Definition _nbits : ident := 13%positive.
Definition _nboff : ident := 12%positive.
Definition _octv : ident := 264%positive.
Definition _oer_constraints : ident := 58%positive.
Definition _oer_decode_primitive : ident := 151%positive.
Definition _oer_decoder : ident := 50%positive.
Definition _oer_encode_primitive : ident := 152%positive.
Definition _oer_encoder : ident := 51%positive.
Definition _oer_fetch_length : ident := 149%positive.
Definition _oer_serialize_length : ident := 150%positive.
Definition _ok : ident := 296%positive.
Definition _op : ident := 63%positive.
Definition _op_key : ident := 20%positive.
Definition _opt_codec_ctx : ident := 259%positive.
Definition _opt_mname : ident := 260%positive.
Definition _optional : ident := 73%positive.
Definition _outcome : ident := 290%positive.
Definition _outmost_tag : ident := 56%positive.
Definition _output : ident := 19%positive.
Definition _p : ident := 267%positive.
Definition _pd : ident := 301%positive.
Definition _per_constraints : ident := 59%positive.
Definition _po : ident := 302%positive.
Definition _positive : ident := 37%positive.
Definition _presence_index : ident := 41%positive.
Definition _print_struct : ident := 44%positive.
Definition _ptr : ident := 273%positive.
Definition _ra : ident := 245%positive.
Definition _random_fill : ident := 55%positive.
Definition _range_bits : ident := 24%positive.
Definition _rb : ident := 246%positive.
Definition _real_body_len : ident := 297%positive.
Definition _refill : ident := 16%positive.
Definition _refill_key : ident := 17%positive.
Definition _result_failed : ident := 306%positive.
Definition _result_ok : ident := 305%positive.
Definition _result_skipped : ident := 307%positive.
Definition _ret : ident := 210%positive.
Definition _s : ident := 215%positive.
Definition _s__1 : ident := 219%positive.
Definition _scaleF : ident := 271%positive.
Definition _shift_count : ident := 286%positive.
Definition _sign : ident := 220%positive.
Definition _size : ident := 30%positive.
Definition _snprintf : ident := 138%positive.
Definition _source : ident := 265%positive.
Definition _specialRealValue__1 : ident := 198%positive.
Definition _specialRealValue_s : ident := 85%positive.
Definition _specifics : ident := 72%positive.
Definition _sptr : ident := 233%positive.
Definition _srv : ident := 256%positive.
Definition _st : ident := 235%positive.
Definition _start : ident := 284%positive.
Definition _stoplooking : ident := 223%positive.
Definition _string : ident := 83%positive.
Definition _strtod : ident := 139%positive.
Definition _structure_ptr : ident := 6%positive.
Definition _tag : ident := 75%positive.
Definition _tag_mode : ident := 76%positive.
Definition _tags : ident := 64%positive.
Definition _tags_count : ident := 65%positive.
Definition _td : ident := 232%positive.
Definition _test : ident := 275%positive.
Definition _tmp_error : ident := 249%positive.
Definition _tmp_error__1 : ident := 250%positive.
Definition _tmp_error__2 : ident := 295%positive.
Definition _tmp_error__3 : ident := 298%positive.
Definition _tmp_error__4 : ident := 299%positive.
Definition _tmp_error__5 : ident := 300%positive.
Definition _tmpspace : ident := 18%positive.
Definition _type : ident := 77%positive.
Definition _type_descriptor : ident := 40%positive.
Definition _type_selector : ident := 78%positive.
Definition _uper_decoder : ident := 52%positive.
Definition _uper_encoder : ident := 53%positive.
Definition _upper_bound : ident := 27%positive.
Definition _used_malloc : ident := 266%positive.
Definition _value : ident := 29%positive.
Definition _value2code : ident := 31%positive.
Definition _values : ident := 303%positive.
Definition _width : ident := 36%positive.
Definition _xer_decode_primitive : ident := 168%positive.
Definition _xer_decoder : ident := 48%positive.
Definition _xer_encoder : ident := 49%positive.
Definition _xerdata : ident := 253%positive.
Definition _xml_tag : ident := 62%positive.
Definition _z : ident := 224%positive.
Definition _t'1 : ident := 309%positive.
Definition _t'10 : ident := 318%positive.
Definition _t'11 : ident := 319%positive.
Definition _t'12 : ident := 320%positive.
Definition _t'13 : ident := 321%positive.
Definition _t'14 : ident := 322%positive.
Definition _t'15 : ident := 323%positive.
Definition _t'16 : ident := 324%positive.
Definition _t'17 : ident := 325%positive.
Definition _t'18 : ident := 326%positive.
Definition _t'19 : ident := 327%positive.
Definition _t'2 : ident := 310%positive.
Definition _t'20 : ident := 328%positive.
Definition _t'21 : ident := 329%positive.
Definition _t'22 : ident := 330%positive.
Definition _t'23 : ident := 331%positive.
Definition _t'24 : ident := 332%positive.
Definition _t'25 : ident := 333%positive.
Definition _t'26 : ident := 334%positive.
Definition _t'27 : ident := 335%positive.
Definition _t'28 : ident := 336%positive.
Definition _t'29 : ident := 337%positive.
Definition _t'3 : ident := 311%positive.
Definition _t'30 : ident := 338%positive.
Definition _t'31 : ident := 339%positive.
Definition _t'32 : ident := 340%positive.
Definition _t'33 : ident := 341%positive.
Definition _t'34 : ident := 342%positive.
Definition _t'35 : ident := 343%positive.
Definition _t'36 : ident := 344%positive.
Definition _t'37 : ident := 345%positive.
Definition _t'38 : ident := 346%positive.
Definition _t'39 : ident := 347%positive.
Definition _t'4 : ident := 312%positive.
Definition _t'40 : ident := 348%positive.
Definition _t'41 : ident := 349%positive.
Definition _t'42 : ident := 350%positive.
Definition _t'43 : ident := 351%positive.
Definition _t'44 : ident := 352%positive.
Definition _t'45 : ident := 353%positive.
Definition _t'46 : ident := 354%positive.
Definition _t'47 : ident := 355%positive.
Definition _t'48 : ident := 356%positive.
Definition _t'49 : ident := 357%positive.
Definition _t'5 : ident := 313%positive.
Definition _t'50 : ident := 358%positive.
Definition _t'51 : ident := 359%positive.
Definition _t'52 : ident := 360%positive.
Definition _t'53 : ident := 361%positive.
Definition _t'54 : ident := 362%positive.
Definition _t'55 : ident := 363%positive.
Definition _t'56 : ident := 364%positive.
Definition _t'57 : ident := 365%positive.
Definition _t'58 : ident := 366%positive.
Definition _t'59 : ident := 367%positive.
Definition _t'6 : ident := 314%positive.
Definition _t'60 : ident := 368%positive.
Definition _t'61 : ident := 369%positive.
Definition _t'62 : ident := 370%positive.
Definition _t'63 : ident := 371%positive.
Definition _t'64 : ident := 372%positive.
Definition _t'65 : ident := 373%positive.
Definition _t'66 : ident := 374%positive.
Definition _t'67 : ident := 375%positive.
Definition _t'68 : ident := 376%positive.
Definition _t'69 : ident := 377%positive.
Definition _t'7 : ident := 315%positive.
Definition _t'70 : ident := 378%positive.
Definition _t'8 : ident := 316%positive.
Definition _t'9 : ident := 317%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 89) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 89) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_asn_DEF_REAL_tags := {|
  gvar_info := (tarray tuint 1);
  gvar_init := (Init_int32 (Int.repr 36) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_asn_OP_REAL := {|
  gvar_info := (Tstruct _asn_TYPE_operation_s noattr);
  gvar_init := (Init_addrof _ASN__PRIMITIVE_TYPE_free (Ptrofs.repr 0) ::
                Init_addrof _REAL_print (Ptrofs.repr 0) ::
                Init_addrof _REAL_compare (Ptrofs.repr 0) ::
                Init_addrof _ber_decode_primitive (Ptrofs.repr 0) ::
                Init_addrof _der_encode_primitive (Ptrofs.repr 0) ::
                Init_addrof _REAL_decode_xer (Ptrofs.repr 0) ::
                Init_addrof _REAL_encode_xer (Ptrofs.repr 0) ::
                Init_addrof _REAL_decode_oer (Ptrofs.repr 0) ::
                Init_addrof _REAL_encode_oer (Ptrofs.repr 0) ::
                Init_addrof _REAL_decode_uper (Ptrofs.repr 0) ::
                Init_addrof _REAL_encode_uper (Ptrofs.repr 0) ::
                Init_addrof _REAL_random_fill (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_asn_DEF_REAL := {|
  gvar_info := (Tstruct _asn_TYPE_descriptor_s noattr);
  gvar_init := (Init_addrof ___stringlit_1 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_1 (Ptrofs.repr 0) ::
                Init_addrof _asn_OP_REAL (Ptrofs.repr 0) ::
                Init_addrof _asn_DEF_REAL_tags (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 1) :: Init_space 4 ::
                Init_addrof _asn_DEF_REAL_tags (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 1) :: Init_space 4 ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_addrof _asn_generic_no_constraint (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_space 4 :: Init_int64 (Int64.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_specialRealValue__1 := {|
  gvar_info := (tarray (Tstruct _specialRealValue_s noattr) 3);
  gvar_init := (Init_addrof ___stringlit_4 (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 15) :: Init_int64 (Int64.repr 0) ::
                Init_addrof ___stringlit_3 (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 17) :: Init_int64 (Int64.repr (-1)) ::
                Init_addrof ___stringlit_2 (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 16) :: Init_int64 (Int64.repr 1) ::
                nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_REAL__dump := {|
  fn_return := tlong;
  fn_callconv := cc_default;
  fn_params := ((_d, tdouble) :: (_canonical, tint) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_local_buf, (tarray tschar 64)) :: nil);
  fn_temps := ((_buf, (tptr tschar)) :: (_buflen, tlong) ::
               (_fmt, (tptr tschar)) :: (_ret, tlong) ::
               (_dot, (tptr tschar)) :: (_end, (tptr tschar)) ::
               (_last_zero, (tptr tschar)) ::
               (_first_zero_in_run, (tptr tschar)) :: (_s, (tptr tschar)) ::
               (_lz_state, tint) :: (_E, (tptr tschar)) ::
               (_expptr, (tptr tschar)) :: (_s__1, (tptr tschar)) ::
               (_sign, tint) :: (_end__1, (tptr tschar)) ::
               (_last_zero__1, (tptr tschar)) :: (_stoplooking, tint) ::
               (_z, (tptr tschar)) :: (_t'32, tlong) :: (_t'31, tint) ::
               (_t'30, (tptr tschar)) :: (_t'29, (tptr tint)) ::
               (_t'28, (tptr tschar)) :: (_t'27, (tptr tint)) ::
               (_t'26, (tptr tschar)) :: (_t'25, (tptr tschar)) ::
               (_t'24, (tptr tint)) :: (_t'23, (tptr tschar)) ::
               (_t'22, (tptr tvoid)) :: (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, tint) :: (_t'18, tint) :: (_t'17, tint) ::
               (_t'16, tint) :: (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tlong) :: (_t'8, tint) ::
               (_t'7, tdouble) :: (_t'6, tlong) :: (_t'5, tint) ::
               (_t'4, tdouble) :: (_t'3, tlong) :: (_t'2, tint) ::
               (_t'1, (tptr tschar)) :: (_t'40, tschar) :: (_t'39, tschar) ::
               (_t'38, tschar) :: (_t'37, tschar) :: (_t'36, tschar) ::
               (_t'35, tschar) :: (_t'34, tschar) :: (_t'33, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _buf (Evar _local_buf (tarray tschar 64)))
  (Ssequence
    (Sset _buflen (Esizeof (tarray tschar 64) tulong))
    (Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _canonical tint)
          (Sset _t'1
            (Ecast (Evar ___stringlit_6 (tarray tschar 6)) (tptr tschar)))
          (Sset _t'1
            (Ecast (Evar ___stringlit_5 (tarray tschar 6)) (tptr tschar))))
        (Sset _fmt (Etempvar _t'1 (tptr tschar))))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                         (Esizeof tfloat tulong) tint)
            (Ssequence
              (Scall (Some _t'17)
                (Evar ___isnanf (Tfunction (Tcons tfloat Tnil) tint
                                  cc_default))
                ((Etempvar _d tdouble) :: nil))
              (Sset _t'16 (Ecast (Etempvar _t'17 tint) tint)))
            (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                           (Esizeof tdouble tulong) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'19)
                    (Evar ___isnan (Tfunction (Tcons tdouble Tnil) tint
                                     cc_default))
                    ((Etempvar _d tdouble) :: nil))
                  (Sset _t'18 (Ecast (Etempvar _t'19 tint) tint)))
                (Sset _t'16 (Ecast (Etempvar _t'18 tint) tint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'20)
                    (Evar ___isnanl (Tfunction (Tcons tdouble Tnil) tint
                                      cc_default))
                    ((Etempvar _d tdouble) :: nil))
                  (Sset _t'18 (Ecast (Etempvar _t'20 tint) tint)))
                (Sset _t'16 (Ecast (Etempvar _t'18 tint) tint)))))
          (Sifthenelse (Etempvar _t'16 tint)
            (Ssequence
              (Sset _buf
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _specialRealValue_s noattr)))
                    (Tstruct _specialRealValue_s noattr)) _string
                  (tptr tschar)))
              (Ssequence
                (Sset _buflen
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (Tstruct _specialRealValue_s noattr)))
                      (Tstruct _specialRealValue_s noattr)) _length tulong))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Etempvar _cb (tptr (Tfunction
                                            (Tcons (tptr tvoid)
                                              (Tcons tulong
                                                (Tcons (tptr tvoid) Tnil)))
                                            tint cc_default)))
                      ((Etempvar _buf (tptr tschar)) ::
                       (Etempvar _buflen tlong) ::
                       (Etempvar _app_key (tptr tvoid)) :: nil))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'2 tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Sset _t'3
                        (Ecast
                          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                          tlong))
                      (Sset _t'3 (Ecast (Etempvar _buflen tlong) tlong))))
                  (Sreturn (Some (Etempvar _t'3 tlong))))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                             (Esizeof tfloat tulong) tint)
                (Ssequence
                  (Scall (Some _t'12)
                    (Evar ___finitef (Tfunction (Tcons tfloat Tnil) tint
                                       cc_default))
                    ((Etempvar _d tdouble) :: nil))
                  (Sset _t'11 (Ecast (Etempvar _t'12 tint) tint)))
                (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                               (Esizeof tdouble tulong) tint)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'14)
                        (Evar ___finite (Tfunction (Tcons tdouble Tnil) tint
                                          cc_default))
                        ((Etempvar _d tdouble) :: nil))
                      (Sset _t'13 (Ecast (Etempvar _t'14 tint) tint)))
                    (Sset _t'11 (Ecast (Etempvar _t'13 tint) tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'15)
                        (Evar ___finitel (Tfunction (Tcons tdouble Tnil) tint
                                           cc_default))
                        ((Etempvar _d tdouble) :: nil))
                      (Sset _t'13 (Ecast (Etempvar _t'15 tint) tint)))
                    (Sset _t'11 (Ecast (Etempvar _t'13 tint) tint)))))
              (Sifthenelse (Eunop Onotbool (Etempvar _t'11 tint) tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _copysign (Tfunction
                                        (Tcons tdouble (Tcons tdouble Tnil))
                                        tdouble cc_default))
                      ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                       (Etempvar _d tdouble) :: nil))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'4 tdouble)
                                   (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                   tint)
                      (Ssequence
                        (Sset _buf
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                                (Econst_int (Int.repr 1) tint)
                                (tptr (Tstruct _specialRealValue_s noattr)))
                              (Tstruct _specialRealValue_s noattr)) _string
                            (tptr tschar)))
                        (Sset _buflen
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                                (Econst_int (Int.repr 1) tint)
                                (tptr (Tstruct _specialRealValue_s noattr)))
                              (Tstruct _specialRealValue_s noattr)) _length
                            tulong)))
                      (Ssequence
                        (Sset _buf
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                                (Econst_int (Int.repr 2) tint)
                                (tptr (Tstruct _specialRealValue_s noattr)))
                              (Tstruct _specialRealValue_s noattr)) _string
                            (tptr tschar)))
                        (Sset _buflen
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                                (Econst_int (Int.repr 2) tint)
                                (tptr (Tstruct _specialRealValue_s noattr)))
                              (Tstruct _specialRealValue_s noattr)) _length
                            tulong)))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Etempvar _cb (tptr (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons tulong
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tint cc_default)))
                        ((Etempvar _buf (tptr tschar)) ::
                         (Etempvar _buflen tlong) ::
                         (Etempvar _app_key (tptr tvoid)) :: nil))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'5 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sset _t'6
                          (Ecast
                            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                            tlong))
                        (Sset _t'6 (Ecast (Etempvar _buflen tlong) tlong))))
                    (Sreturn (Some (Etempvar _t'6 tlong)))))
                (Ssequence
                  (Scall (Some _t'10)
                    (Evar _ilogb (Tfunction (Tcons tdouble Tnil) tint
                                   cc_default))
                    ((Etempvar _d tdouble) :: nil))
                  (Sifthenelse (Ebinop Ole (Etempvar _t'10 tint)
                                 (Eunop Oneg
                                   (Ecast
                                     (Ebinop Oshr
                                       (Ecast
                                         (Eunop Oneg
                                           (Econst_int (Int.repr 1) tint)
                                           tint) tuint)
                                       (Econst_int (Int.repr 1) tint) tuint)
                                     tint) tint) tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _copysign (Tfunction
                                            (Tcons tdouble
                                              (Tcons tdouble Tnil)) tdouble
                                            cc_default))
                          ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                           (Etempvar _d tdouble) :: nil))
                        (Sifthenelse (Ebinop Olt (Etempvar _t'7 tdouble)
                                       (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                       tint)
                          (Ssequence
                            (Sset _buf
                              (Evar ___stringlit_8 (tarray tschar 3)))
                            (Sset _buflen
                              (Ecast (Econst_int (Int.repr 2) tint) tlong)))
                          (Ssequence
                            (Sset _buf
                              (Evar ___stringlit_7 (tarray tschar 2)))
                            (Sset _buflen
                              (Ecast (Econst_int (Int.repr 1) tint) tlong)))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'8)
                            (Etempvar _cb (tptr (Tfunction
                                                  (Tcons (tptr tvoid)
                                                    (Tcons tulong
                                                      (Tcons (tptr tvoid)
                                                        Tnil))) tint
                                                  cc_default)))
                            ((Etempvar _buf (tptr tschar)) ::
                             (Etempvar _buflen tlong) ::
                             (Etempvar _app_key (tptr tvoid)) :: nil))
                          (Sifthenelse (Ebinop Olt (Etempvar _t'8 tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Sset _t'9
                              (Ecast
                                (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                  tint) tlong))
                            (Sset _t'9
                              (Ecast (Etempvar _buflen tlong) tlong))))
                        (Sreturn (Some (Etempvar _t'9 tlong)))))
                    Sskip))))))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Scall (Some _t'21)
                  (Evar _snprintf (Tfunction
                                    (Tcons (tptr tschar)
                                      (Tcons tulong
                                        (Tcons (tptr tschar) Tnil))) tint
                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _buf (tptr tschar)) ::
                   (Etempvar _buflen tlong) ::
                   (Etempvar _fmt (tptr tschar)) :: (Etempvar _d tdouble) ::
                   nil))
                (Sset _ret (Ecast (Etempvar _t'21 tint) tlong)))
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _ret tlong)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Sset _buflen
                      (Ebinop Oshl (Etempvar _buflen tlong)
                        (Econst_int (Int.repr 1) tint) tlong))
                    (Sifthenelse (Ebinop Ogt (Etempvar _buflen tlong)
                                   (Econst_int (Int.repr 4096) tint) tint)
                      (Ssequence
                        (Sifthenelse (Ebinop One
                                       (Etempvar _buf (tptr tschar))
                                       (Evar _local_buf (tarray tschar 64))
                                       tint)
                          (Scall None
                            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                          tvoid cc_default))
                            ((Etempvar _buf (tptr tschar)) :: nil))
                          Sskip)
                        (Sreturn (Some (Eunop Oneg
                                         (Econst_int (Int.repr 1) tint) tint))))
                      Sskip))
                  (Sifthenelse (Ebinop Oge (Etempvar _ret tlong)
                                 (Etempvar _buflen tlong) tint)
                    (Sset _buflen
                      (Ebinop Oadd (Etempvar _ret tlong)
                        (Econst_int (Int.repr 1) tint) tlong))
                    (Ssequence (Sset _buflen (Etempvar _ret tlong)) Sbreak)))
                (Ssequence
                  (Sifthenelse (Ebinop One (Etempvar _buf (tptr tschar))
                                 (Evar _local_buf (tarray tschar 64)) tint)
                    (Scall None
                      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                      ((Etempvar _buf (tptr tschar)) :: nil))
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'22)
                        (Evar _malloc (Tfunction (Tcons tulong Tnil)
                                        (tptr tvoid) cc_default))
                        ((Etempvar _buflen tlong) :: nil))
                      (Sset _buf
                        (Ecast (Etempvar _t'22 (tptr tvoid)) (tptr tschar))))
                    (Sifthenelse (Eunop Onotbool
                                   (Etempvar _buf (tptr tschar)) tint)
                      (Sreturn (Some (Eunop Oneg
                                       (Econst_int (Int.repr 1) tint) tint)))
                      Sskip)))))
            Sskip)
          (Ssequence
            (Sifthenelse (Etempvar _canonical tint)
              (Ssequence
                (Sset _end
                  (Ebinop Oadd (Etempvar _buf (tptr tschar))
                    (Etempvar _buflen tlong) (tptr tschar)))
                (Ssequence
                  (Sset _lz_state (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'40
                          (Ederef
                            (Ebinop Oadd (Etempvar _buf (tptr tschar))
                              (Econst_int (Int.repr 0) tint) (tptr tschar))
                            tschar))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'40 tschar)
                                       (Econst_int (Int.repr 45) tint) tint)
                          (Sset _t'23
                            (Ecast
                              (Ebinop Oadd (Etempvar _buf (tptr tschar))
                                (Econst_int (Int.repr 2) tint) (tptr tschar))
                              (tptr tschar)))
                          (Sset _t'23
                            (Ecast
                              (Ebinop Oadd (Etempvar _buf (tptr tschar))
                                (Econst_int (Int.repr 1) tint) (tptr tschar))
                              (tptr tschar)))))
                      (Sset _dot (Etempvar _t'23 (tptr tschar))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'39
                          (Ederef (Etempvar _dot (tptr tschar)) tschar))
                        (Sifthenelse (Ebinop Oge (Etempvar _t'39 tschar)
                                       (Econst_int (Int.repr 48) tint) tint)
                          (Ssequence
                            (Sifthenelse (Ebinop One
                                           (Etempvar _buf (tptr tschar))
                                           (Evar _local_buf (tarray tschar 64))
                                           tint)
                              (Scall None
                                (Evar _free (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                                ((Etempvar _buf (tptr tschar)) :: nil))
                              Sskip)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'24)
                                  (Evar ___errno_location (Tfunction Tnil
                                                            (tptr tint)
                                                            cc_default)) nil)
                                (Sassign
                                  (Ederef (Etempvar _t'24 (tptr tint)) tint)
                                  (Econst_int (Int.repr 22) tint)))
                              (Sreturn (Some (Eunop Oneg
                                               (Econst_int (Int.repr 1) tint)
                                               tint)))))
                          Sskip))
                      (Ssequence
                        (Sassign
                          (Ederef (Etempvar _dot (tptr tschar)) tschar)
                          (Econst_int (Int.repr 46) tint))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'25
                                      (Ecast
                                        (Ebinop Oadd
                                          (Etempvar _dot (tptr tschar))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr tschar)) (tptr tschar)))
                                    (Sset _s (Etempvar _t'25 (tptr tschar))))
                                  (Sset _t'26
                                    (Ecast (Etempvar _t'25 (tptr tschar))
                                      (tptr tschar))))
                                (Sset _last_zero
                                  (Etempvar _t'26 (tptr tschar))))
                              (Sset _first_zero_in_run
                                (Etempvar _t'26 (tptr tschar))))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _s (tptr tschar))
                                               (Etempvar _end (tptr tschar))
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'38
                                      (Ederef (Etempvar _s (tptr tschar))
                                        tschar))
                                    (Sswitch (Ederef
                                               (Etempvar _s (tptr tschar))
                                               tschar)
                                      (LScons (Some 69)
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _lz_state tint)
                                                         (Econst_int (Int.repr 1) tint)
                                                         tint)
                                            (Sset _last_zero
                                              (Etempvar _first_zero_in_run (tptr tschar)))
                                            Sskip)
                                          Sbreak)
                                        (LScons (Some 48)
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _lz_state tint)
                                                           (Econst_int (Int.repr 0) tint)
                                                           tint)
                                              (Sset _first_zero_in_run
                                                (Etempvar _s (tptr tschar)))
                                              Sskip)
                                            (Ssequence
                                              (Sset _lz_state
                                                (Econst_int (Int.repr 1) tint))
                                              Scontinue))
                                          (LScons None
                                            (Ssequence
                                              (Sset _lz_state
                                                (Econst_int (Int.repr 0) tint))
                                              Scontinue)
                                            LSnil)))))
                                  Sbreak))
                              (Sset _s
                                (Ebinop Oadd (Etempvar _s (tptr tschar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tschar)))))
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _s (tptr tschar))
                                           (Etempvar _end (tptr tschar))
                                           tint)
                              (Ssequence
                                (Sifthenelse (Ebinop One
                                               (Etempvar _buf (tptr tschar))
                                               (Evar _local_buf (tarray tschar 64))
                                               tint)
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _buf (tptr tschar)) :: nil))
                                  Sskip)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'27)
                                      (Evar ___errno_location (Tfunction Tnil
                                                                (tptr tint)
                                                                cc_default))
                                      nil)
                                    (Sassign
                                      (Ederef (Etempvar _t'27 (tptr tint))
                                        tint)
                                      (Econst_int (Int.repr 22) tint)))
                                  (Sreturn (Some (Eunop Oneg
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint)))))
                              Sskip)
                            (Ssequence
                              (Ssequence
                                (Sset _t'37
                                  (Ederef (Etempvar _s (tptr tschar)) tschar))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'37 tschar)
                                               (Econst_int (Int.repr 69) tint)
                                               tint)
                                  Sskip
                                  (Scall None
                                    (Evar ___assert_fail (Tfunction
                                                           (Tcons
                                                             (tptr tschar)
                                                             (Tcons
                                                               (tptr tschar)
                                                               (Tcons tuint
                                                                 (Tcons
                                                                   (tptr tschar)
                                                                   Tnil))))
                                                           tvoid cc_default))
                                    ((Evar ___stringlit_10 (tarray tschar 11)) ::
                                     (Evar ___stringlit_9 (tarray tschar 7)) ::
                                     (Econst_int (Int.repr 231) tint) ::
                                     (Evar ___func__ (tarray tschar 11)) ::
                                     nil))))
                              (Ssequence
                                (Sset _E (Etempvar _s (tptr tschar)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'28
                                        (Ecast
                                          (Ebinop Oadd
                                            (Etempvar _E (tptr tschar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tschar)) (tptr tschar)))
                                      (Sset _E
                                        (Etempvar _t'28 (tptr tschar))))
                                    (Sset _expptr
                                      (Etempvar _t'28 (tptr tschar))))
                                  (Ssequence
                                    (Sset _s__1
                                      (Etempvar _expptr (tptr tschar)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'36
                                          (Ederef
                                            (Etempvar _expptr (tptr tschar))
                                            tschar))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _t'36 tschar)
                                                       (Econst_int (Int.repr 43) tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _buflen
                                              (Ebinop Osub
                                                (Etempvar _buflen tlong)
                                                (Econst_int (Int.repr 1) tint)
                                                tlong))
                                            (Sset _sign
                                              (Econst_int (Int.repr 0) tint)))
                                          (Ssequence
                                            (Sset _sign
                                              (Econst_int (Int.repr 1) tint))
                                            (Sset _s__1
                                              (Ebinop Oadd
                                                (Etempvar _s__1 (tptr tschar))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tschar))))))
                                      (Ssequence
                                        (Sset _expptr
                                          (Ebinop Oadd
                                            (Etempvar _expptr (tptr tschar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tschar)))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _expptr (tptr tschar))
                                                         (Etempvar _end (tptr tschar))
                                                         tint)
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _buf (tptr tschar))
                                                             (Evar _local_buf (tarray tschar 64))
                                                             tint)
                                                (Scall None
                                                  (Evar _free (Tfunction
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                                  ((Etempvar _buf (tptr tschar)) ::
                                                   nil))
                                                Sskip)
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'29)
                                                    (Evar ___errno_location 
                                                    (Tfunction Tnil
                                                      (tptr tint) cc_default))
                                                    nil)
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _t'29 (tptr tint))
                                                      tint)
                                                    (Econst_int (Int.repr 22) tint)))
                                                (Sreturn (Some (Eunop Oneg
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tint)))))
                                            Sskip)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'35
                                                (Ederef
                                                  (Etempvar _expptr (tptr tschar))
                                                  tschar))
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _t'35 tschar)
                                                             (Econst_int (Int.repr 48) tint)
                                                             tint)
                                                (Ssequence
                                                  (Sset _buflen
                                                    (Ebinop Osub
                                                      (Etempvar _buflen tlong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tlong))
                                                  (Sset _expptr
                                                    (Ebinop Oadd
                                                      (Etempvar _expptr (tptr tschar))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tschar))))
                                                Sskip))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _lz_state tint)
                                                             (Econst_int (Int.repr 1) tint)
                                                             tint)
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _last_zero (tptr tschar))
                                                      tschar)
                                                    (Econst_int (Int.repr 69) tint))
                                                  (Ssequence
                                                    (Sset _buflen
                                                      (Ebinop Osub
                                                        (Etempvar _buflen tlong)
                                                        (Ebinop Osub
                                                          (Etempvar _s__1 (tptr tschar))
                                                          (Ebinop Oadd
                                                            (Etempvar _last_zero (tptr tschar))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tschar))
                                                          tlong) tlong))
                                                    (Ssequence
                                                      (Sset _s__1
                                                        (Ebinop Oadd
                                                          (Etempvar _last_zero (tptr tschar))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tschar)))
                                                      (Sifthenelse (Etempvar _sign tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'30
                                                                (Etempvar _s__1 (tptr tschar)))
                                                              (Sset _s__1
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'30 (tptr tschar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tschar))))
                                                            (Sassign
                                                              (Ederef
                                                                (Etempvar _t'30 (tptr tschar))
                                                                tschar)
                                                              (Econst_int (Int.repr 45) tint)))
                                                          (Sset _buflen
                                                            (Ebinop Oadd
                                                              (Etempvar _buflen tlong)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tlong)))
                                                        Sskip))))
                                                Sskip)
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Ole
                                                                 (Etempvar _expptr (tptr tschar))
                                                                 (Etempvar _end (tptr tschar))
                                                                 tint)
                                                    Sskip
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sset _t'34
                                                      (Ederef
                                                        (Etempvar _expptr (tptr tschar))
                                                        tschar))
                                                    (Sassign
                                                      (Ederef
                                                        (Etempvar _s__1 (tptr tschar))
                                                        tschar)
                                                      (Etempvar _t'34 tschar))))
                                                (Ssequence
                                                  (Sset _s__1
                                                    (Ebinop Oadd
                                                      (Etempvar _s__1 (tptr tschar))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tschar)))
                                                  (Sset _expptr
                                                    (Ebinop Oadd
                                                      (Etempvar _expptr (tptr tschar))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tschar)))))))))))))))))))))
              (Ssequence
                (Sset _end__1
                  (Ebinop Oadd (Etempvar _buf (tptr tschar))
                    (Etempvar _buflen tlong) (tptr tschar)))
                (Ssequence
                  (Sset _last_zero__1 (Etempvar _end__1 (tptr tschar)))
                  (Ssequence
                    (Sset _stoplooking (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sset _z
                        (Ebinop Osub (Etempvar _end__1 (tptr tschar))
                          (Econst_int (Int.repr 1) tint) (tptr tschar)))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Ogt
                                         (Etempvar _z (tptr tschar))
                                         (Etempvar _buf (tptr tschar)) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _t'33
                                (Ederef (Etempvar _z (tptr tschar)) tschar))
                              (Sswitch (Ederef (Etempvar _z (tptr tschar))
                                         tschar)
                                (LScons (Some 48)
                                  (Ssequence
                                    (Sifthenelse (Eunop Onotbool
                                                   (Etempvar _stoplooking tint)
                                                   tint)
                                      (Sset _last_zero__1
                                        (Etempvar _z (tptr tschar)))
                                      Sskip)
                                    Scontinue)
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
                                                      (Sset _stoplooking
                                                        (Econst_int (Int.repr 1) tint))
                                                      Scontinue)
                                                    (LScons None
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Etempvar _z (tptr tschar))
                                                            tschar)
                                                          (Econst_int (Int.repr 46) tint))
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _last_zero__1 (tptr tschar))
                                                              (Ebinop Oadd
                                                                (Etempvar _z (tptr tschar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tschar))
                                                              tint)
                                                            (Sset _last_zero__1
                                                              (Ebinop Oadd
                                                                (Etempvar _last_zero__1 (tptr tschar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tschar)))
                                                            Sskip)
                                                          (Ssequence
                                                            (Sset _buflen
                                                              (Ebinop Osub
                                                                (Etempvar _last_zero__1 (tptr tschar))
                                                                (Etempvar _buf (tptr tschar))
                                                                tlong))
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Etempvar _last_zero__1 (tptr tschar))
                                                                  tschar)
                                                                (Econst_int (Int.repr 0) tint))
                                                              Sbreak))))
                                                      LSnil)))))))))))))
                            Sbreak))
                        (Sset _z
                          (Ebinop Osub (Etempvar _z (tptr tschar))
                            (Econst_int (Int.repr 1) tint) (tptr tschar)))))))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'31)
                  (Etempvar _cb (tptr (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tulong
                                            (Tcons (tptr tvoid) Tnil))) tint
                                        cc_default)))
                  ((Etempvar _buf (tptr tschar)) ::
                   (Etempvar _buflen tlong) ::
                   (Etempvar _app_key (tptr tvoid)) :: nil))
                (Sset _ret (Ecast (Etempvar _t'31 tint) tlong)))
              (Ssequence
                (Sifthenelse (Ebinop One (Etempvar _buf (tptr tschar))
                               (Evar _local_buf (tarray tschar 64)) tint)
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _buf (tptr tschar)) :: nil))
                  Sskip)
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _ret tlong)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sset _t'32
                      (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                        tlong))
                    (Sset _t'32 (Ecast (Etempvar _buflen tlong) tlong)))
                  (Sreturn (Some (Etempvar _t'32 tlong))))))))))))
|}.

Definition f_REAL_print := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_ilevel, tint) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_d, tdouble) :: nil);
  fn_temps := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_ret, tlong) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tlong) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'8, (tptr tuchar)) :: (_t'7, tdouble) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _st
    (Ecast (Etempvar _sptr (tptr tvoid))
      (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))))
  (Ssequence
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                     tint)
        (Sset _t'5 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef
                (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf (tptr tuchar)))
          (Sset _t'5
            (Ecast (Eunop Onotbool (Etempvar _t'8 (tptr tuchar)) tint) tbool))))
      (Sifthenelse (Etempvar _t'5 tint)
        (Ssequence
          (Scall (Some _t'1)
            (Etempvar _cb (tptr (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons tulong (Tcons (tptr tvoid) Tnil)))
                                  tint cc_default)))
            ((Evar ___stringlit_12 (tarray tschar 9)) ::
             (Econst_int (Int.repr 8) tint) ::
             (Etempvar _app_key (tptr tvoid)) :: nil))
          (Sset _ret (Ecast (Etempvar _t'1 tint) tlong)))
        (Ssequence
          (Scall (Some _t'4)
            (Evar _asn_REAL2double (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                       (Tcons (tptr tdouble) Tnil)) tint
                                     cc_default))
            ((Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
             (Eaddrof (Evar _d tdouble) (tptr tdouble)) :: nil))
          (Sifthenelse (Etempvar _t'4 tint)
            (Ssequence
              (Scall (Some _t'2)
                (Etempvar _cb (tptr (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons tulong
                                          (Tcons (tptr tvoid) Tnil))) tint
                                      cc_default)))
                ((Evar ___stringlit_11 (tarray tschar 8)) ::
                 (Econst_int (Int.repr 7) tint) ::
                 (Etempvar _app_key (tptr tvoid)) :: nil))
              (Sset _ret (Ecast (Etempvar _t'2 tint) tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'7 (Evar _d tdouble))
                (Scall (Some _t'3)
                  (Evar _REAL__dump (Tfunction
                                      (Tcons tdouble
                                        (Tcons tint
                                          (Tcons
                                            (tptr (Tfunction
                                                    (Tcons (tptr tvoid)
                                                      (Tcons tulong
                                                        (Tcons (tptr tvoid)
                                                          Tnil))) tint
                                                    cc_default))
                                            (Tcons (tptr tvoid) Tnil))))
                                      tlong cc_default))
                  ((Etempvar _t'7 tdouble) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Etempvar _cb (tptr (Tfunction
                                         (Tcons (tptr tvoid)
                                           (Tcons tulong
                                             (Tcons (tptr tvoid) Tnil))) tint
                                         cc_default))) ::
                   (Etempvar _app_key (tptr tvoid)) :: nil)))
              (Sset _ret (Etempvar _t'3 tlong)))))))
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _ret tlong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sset _t'6
          (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint))
        (Sset _t'6 (Ecast (Econst_int (Int.repr 0) tint) tint)))
      (Sreturn (Some (Etempvar _t'6 tint))))))
|}.

Definition f_REAL_compare := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_aptr, (tptr tvoid)) :: (_bptr, (tptr tvoid)) :: nil);
  fn_vars := ((_adbl, tdouble) :: (_bdbl, tdouble) :: nil);
  fn_temps := ((_a, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_b, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_ra, tint) :: (_rb, tint) :: (_t'19, tint) ::
               (_t'18, tint) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'32, tdouble) :: (_t'31, tdouble) :: (_t'30, tdouble) ::
               (_t'29, tdouble) :: (_t'28, tdouble) :: (_t'27, tdouble) ::
               (_t'26, tdouble) :: (_t'25, tdouble) :: (_t'24, tdouble) ::
               (_t'23, tdouble) :: (_t'22, tdouble) :: (_t'21, tdouble) ::
               (_t'20, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _a (Etempvar _aptr (tptr tvoid)))
  (Ssequence
    (Sset _b (Etempvar _bptr (tptr tvoid)))
    (Ssequence
      (Sifthenelse (Etempvar _a (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
        (Sset _t'19
          (Ecast (Etempvar _b (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
            tbool))
        (Sset _t'19 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'19 tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _asn_REAL2double (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                         (Tcons (tptr tdouble) Tnil)) tint
                                       cc_default))
              ((Etempvar _a (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (Eaddrof (Evar _adbl tdouble) (tptr tdouble)) :: nil))
            (Sset _ra (Etempvar _t'1 tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _asn_REAL2double (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                           (Tcons (tptr tdouble) Tnil)) tint
                                         cc_default))
                ((Etempvar _b (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                 (Eaddrof (Evar _bdbl tdouble) (tptr tdouble)) :: nil))
              (Sset _rb (Etempvar _t'2 tint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _ra tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _t'18
                  (Ecast
                    (Ebinop Oeq (Etempvar _rb tint)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset _t'18 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'18 tint)
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                   (Esizeof tfloat tulong) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'32 (Evar _adbl tdouble))
                          (Scall (Some _t'14)
                            (Evar ___isnanf (Tfunction (Tcons tfloat Tnil)
                                              tint cc_default))
                            ((Etempvar _t'32 tdouble) :: nil)))
                        (Sset _t'13 (Ecast (Etempvar _t'14 tint) tint)))
                      (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                     (Esizeof tdouble tulong) tint)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'31 (Evar _adbl tdouble))
                              (Scall (Some _t'16)
                                (Evar ___isnan (Tfunction
                                                 (Tcons tdouble Tnil) tint
                                                 cc_default))
                                ((Etempvar _t'31 tdouble) :: nil)))
                            (Sset _t'15 (Ecast (Etempvar _t'16 tint) tint)))
                          (Sset _t'13 (Ecast (Etempvar _t'15 tint) tint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'30 (Evar _adbl tdouble))
                              (Scall (Some _t'17)
                                (Evar ___isnanl (Tfunction
                                                  (Tcons tdouble Tnil) tint
                                                  cc_default))
                                ((Etempvar _t'30 tdouble) :: nil)))
                            (Sset _t'15 (Ecast (Etempvar _t'17 tint) tint)))
                          (Sset _t'13 (Ecast (Etempvar _t'15 tint) tint)))))
                    (Sifthenelse (Etempvar _t'13 tint)
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                       (Esizeof tfloat tulong) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'29 (Evar _bdbl tdouble))
                              (Scall (Some _t'4)
                                (Evar ___isnanf (Tfunction
                                                  (Tcons tfloat Tnil) tint
                                                  cc_default))
                                ((Etempvar _t'29 tdouble) :: nil)))
                            (Sset _t'3 (Ecast (Etempvar _t'4 tint) tint)))
                          (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                         (Esizeof tdouble tulong) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'28 (Evar _bdbl tdouble))
                                  (Scall (Some _t'6)
                                    (Evar ___isnan (Tfunction
                                                     (Tcons tdouble Tnil)
                                                     tint cc_default))
                                    ((Etempvar _t'28 tdouble) :: nil)))
                                (Sset _t'5 (Ecast (Etempvar _t'6 tint) tint)))
                              (Sset _t'3 (Ecast (Etempvar _t'5 tint) tint)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'27 (Evar _bdbl tdouble))
                                  (Scall (Some _t'7)
                                    (Evar ___isnanl (Tfunction
                                                      (Tcons tdouble Tnil)
                                                      tint cc_default))
                                    ((Etempvar _t'27 tdouble) :: nil)))
                                (Sset _t'5 (Ecast (Etempvar _t'7 tint) tint)))
                              (Sset _t'3 (Ecast (Etempvar _t'5 tint) tint)))))
                        (Sifthenelse (Etempvar _t'3 tint)
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          (Sreturn (Some (Eunop Oneg
                                           (Econst_int (Int.repr 1) tint)
                                           tint)))))
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                       (Esizeof tfloat tulong) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'26 (Evar _bdbl tdouble))
                              (Scall (Some _t'9)
                                (Evar ___isnanf (Tfunction
                                                  (Tcons tfloat Tnil) tint
                                                  cc_default))
                                ((Etempvar _t'26 tdouble) :: nil)))
                            (Sset _t'8 (Ecast (Etempvar _t'9 tint) tint)))
                          (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                         (Esizeof tdouble tulong) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'25 (Evar _bdbl tdouble))
                                  (Scall (Some _t'11)
                                    (Evar ___isnan (Tfunction
                                                     (Tcons tdouble Tnil)
                                                     tint cc_default))
                                    ((Etempvar _t'25 tdouble) :: nil)))
                                (Sset _t'10
                                  (Ecast (Etempvar _t'11 tint) tint)))
                              (Sset _t'8 (Ecast (Etempvar _t'10 tint) tint)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'24 (Evar _bdbl tdouble))
                                  (Scall (Some _t'12)
                                    (Evar ___isnanl (Tfunction
                                                      (Tcons tdouble Tnil)
                                                      tint cc_default))
                                    ((Etempvar _t'24 tdouble) :: nil)))
                                (Sset _t'10
                                  (Ecast (Etempvar _t'12 tint) tint)))
                              (Sset _t'8 (Ecast (Etempvar _t'10 tint) tint)))))
                        (Sifthenelse (Etempvar _t'8 tint)
                          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                          Sskip))))
                  (Ssequence
                    (Sset _t'20 (Evar _adbl tdouble))
                    (Ssequence
                      (Sset _t'21 (Evar _bdbl tdouble))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'20 tdouble)
                                     (Etempvar _t'21 tdouble) tint)
                        (Sreturn (Some (Eunop Oneg
                                         (Econst_int (Int.repr 1) tint) tint)))
                        (Ssequence
                          (Sset _t'22 (Evar _adbl tdouble))
                          (Ssequence
                            (Sset _t'23 (Evar _bdbl tdouble))
                            (Sifthenelse (Ebinop Ogt (Etempvar _t'22 tdouble)
                                           (Etempvar _t'23 tdouble) tint)
                              (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
                (Sifthenelse (Etempvar _ra tint)
                  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint)))
                  (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _a (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                       tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
|}.

Definition f_REAL_encode_xer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_ilevel, tint) :: (_flags, tint) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_er, (Tstruct _asn_enc_rval_s noattr)) :: (_d, tdouble) ::
              (_tmp_error, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_enc_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_t'4, tlong) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'7, (tptr tuchar)) :: (_t'6, tdouble) ::
               (_t'5, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _st
    (Ecast (Etempvar _sptr (tptr tvoid))
      (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                       tint)
          (Sset _t'1 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef
                  (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                (tptr tuchar)))
            (Sset _t'1
              (Ecast (Eunop Onotbool (Etempvar _t'7 (tptr tuchar)) tint)
                tbool))))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sset _t'2 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _asn_REAL2double (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                         (Tcons (tptr tdouble) Tnil)) tint
                                       cc_default))
              ((Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (Eaddrof (Evar _d tdouble) (tptr tdouble)) :: nil))
            (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))))
      (Sifthenelse (Etempvar _t'2 tint)
        (Sloop
          (Ssequence
            (Sassign
              (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                _encoded tlong)
              (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Sassign
                (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                  _failed_type
                  (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
              (Ssequence
                (Sassign
                  (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                    _structure_ptr (tptr tvoid))
                  (Etempvar _sptr (tptr tvoid)))
                (Ssequence
                  (Sloop Sskip Sbreak)
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                        (Tstruct _asn_enc_rval_s noattr))
                      (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr)))
                    (Sreturn None))))))
          Sbreak)
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'6 (Evar _d tdouble))
          (Scall (Some _t'4)
            (Evar _REAL__dump (Tfunction
                                (Tcons tdouble
                                  (Tcons tint
                                    (Tcons
                                      (tptr (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons tulong
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tint cc_default))
                                      (Tcons (tptr tvoid) Tnil)))) tlong
                                cc_default))
            ((Etempvar _t'6 tdouble) ::
             (Ebinop Oand (Etempvar _flags tint)
               (Econst_int (Int.repr 2) tint) tint) ::
             (Etempvar _cb (tptr (Tfunction
                                   (Tcons (tptr tvoid)
                                     (Tcons tulong (Tcons (tptr tvoid) Tnil)))
                                   tint cc_default))) ::
             (Etempvar _app_key (tptr tvoid)) :: nil)))
        (Sassign
          (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _encoded tlong)
          (Etempvar _t'4 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _encoded
              tlong))
          (Sifthenelse (Ebinop Olt (Etempvar _t'5 tlong)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sloop
              (Ssequence
                (Sassign
                  (Efield
                    (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                    _encoded tlong)
                  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                      _failed_type
                      (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                    (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                        _structure_ptr (tptr tvoid))
                      (Etempvar _sptr (tptr tvoid)))
                    (Ssequence
                      (Sloop Sskip Sbreak)
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                            (Tstruct _asn_enc_rval_s noattr))
                          (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr)))
                        (Sreturn None))))))
              Sbreak)
            Sskip))
        (Sloop
          (Ssequence
            (Sassign
              (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                _structure_ptr (tptr tvoid)) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                  _failed_type
                  (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                    (Tstruct _asn_enc_rval_s noattr))
                  (Evar _er (Tstruct _asn_enc_rval_s noattr)))
                (Sreturn None))))
          Sbreak)))))
|}.

Definition f_REAL__xer_body_decode := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_chunk_buf, (tptr tvoid)) ::
                (_chunk_size, tulong) :: nil);
  fn_vars := ((_endptr, (tptr tschar)) :: nil);
  fn_temps := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_value, tdouble) :: (_xerdata, (tptr tschar)) ::
               (_b, (tptr tschar)) :: (_i, tulong) ::
               (_srv, (tptr (Tstruct _specialRealValue_s noattr))) ::
               (_dv, tdouble) :: (_t'6, tint) :: (_t'5, tdouble) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'11, (tptr tschar)) :: (_t'10, tulong) ::
               (_t'9, tlong) :: (_t'8, tschar) :: (_t'7, (tptr tschar)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _st
    (Ecast (Etempvar _sptr (tptr tvoid))
      (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))))
  (Ssequence
    (Sset _xerdata (Ecast (Etempvar _chunk_buf (tptr tvoid)) (tptr tschar)))
    (Ssequence
      (Sassign (Evar _endptr (tptr tschar)) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sifthenelse (Eunop Onotbool (Etempvar _chunk_size tulong) tint)
          (Sreturn (Some (Econst_int (Int.repr 2) tint)))
          Sskip)
        (Ssequence
          (Ssequence
            (Sset _t'8
              (Ederef
                (Ebinop Oadd (Etempvar _xerdata (tptr tschar))
                  (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tschar)
                           (Econst_int (Int.repr 60) tint) tint)
              (Ssequence
                (Ssequence
                  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                     (Ebinop Odiv
                                       (Esizeof (tarray (Tstruct _specialRealValue_s noattr) 3) tulong)
                                       (Esizeof (Tstruct _specialRealValue_s noattr) tulong)
                                       tulong) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _srv
                          (Ebinop Oadd
                            (Evar _specialRealValue__1 (tarray (Tstruct _specialRealValue_s noattr) 3))
                            (Etempvar _i tulong)
                            (tptr (Tstruct _specialRealValue_s noattr))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'10
                                (Efield
                                  (Ederef
                                    (Etempvar _srv (tptr (Tstruct _specialRealValue_s noattr)))
                                    (Tstruct _specialRealValue_s noattr))
                                  _length tulong))
                              (Sifthenelse (Ebinop One
                                             (Etempvar _t'10 tulong)
                                             (Etempvar _chunk_size tulong)
                                             tint)
                                (Sset _t'1 (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'11
                                      (Efield
                                        (Ederef
                                          (Etempvar _srv (tptr (Tstruct _specialRealValue_s noattr)))
                                          (Tstruct _specialRealValue_s noattr))
                                        _string (tptr tschar)))
                                    (Scall (Some _t'2)
                                      (Evar _memcmp (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        (Tcons (tptr tvoid)
                                                          (Tcons tulong Tnil)))
                                                      tint cc_default))
                                      ((Etempvar _t'11 (tptr tschar)) ::
                                       (Etempvar _chunk_buf (tptr tvoid)) ::
                                       (Etempvar _chunk_size tulong) :: nil)))
                                  (Sset _t'1
                                    (Ecast (Etempvar _t'2 tint) tbool)))))
                            (Sifthenelse (Etempvar _t'1 tint)
                              Scontinue
                              Sskip))
                          (Ssequence
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _srv (tptr (Tstruct _specialRealValue_s noattr)))
                                    (Tstruct _specialRealValue_s noattr)) _dv
                                  tlong))
                              (Sswitch (Efield
                                         (Ederef
                                           (Etempvar _srv (tptr (Tstruct _specialRealValue_s noattr)))
                                           (Tstruct _specialRealValue_s noattr))
                                         _dv tlong)
                                (LScons (Some 18446744073709551615)
                                  (Ssequence
                                    (Sset _dv
                                      (Ecast
                                        (Eunop Oneg
                                          (Econst_single (Float32.of_bits (Int.repr 2139095040)) tfloat)
                                          tfloat) tdouble))
                                    Sbreak)
                                  (LScons (Some 0)
                                    (Ssequence
                                      (Sset _dv
                                        (Ecast
                                          (Ebinop Odiv
                                            (Econst_single (Float32.of_bits (Int.repr 0)) tfloat)
                                            (Econst_single (Float32.of_bits (Int.repr 0)) tfloat)
                                            tfloat) tdouble))
                                      Sbreak)
                                    (LScons (Some 1)
                                      (Ssequence
                                        (Sset _dv
                                          (Ecast
                                            (Econst_single (Float32.of_bits (Int.repr 2139095040)) tfloat)
                                            tdouble))
                                        Sbreak)
                                      (LScons None
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                        LSnil))))))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'3)
                                  (Evar _asn_double2REAL (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                             (Tcons tdouble
                                                               Tnil)) tint
                                                           cc_default))
                                  ((Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                                   (Etempvar _dv tdouble) :: nil))
                                (Sifthenelse (Etempvar _t'3 tint)
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                  Sskip))
                              (Sreturn (Some (Econst_int (Int.repr 4) tint))))))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))
                (Ssequence
                  (Sloop Sskip Sbreak)
                  (Sreturn (Some (Econst_int (Int.repr 2) tint)))))
              Sskip))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                cc_default))
                ((Ebinop Oadd (Etempvar _chunk_size tulong)
                   (Econst_int (Int.repr 1) tint) tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tschar))))
            (Ssequence
              (Sifthenelse (Eunop Onotbool (Etempvar _b (tptr tschar)) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip)
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Etempvar _b (tptr tschar)) ::
                   (Etempvar _chunk_buf (tptr tvoid)) ::
                   (Etempvar _chunk_size tulong) :: nil))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _b (tptr tschar))
                        (Etempvar _chunk_size tulong) (tptr tschar)) tschar)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _strtod (Tfunction
                                        (Tcons (tptr tschar)
                                          (Tcons (tptr (tptr tschar)) Tnil))
                                        tdouble cc_default))
                        ((Etempvar _b (tptr tschar)) ::
                         (Eaddrof (Evar _endptr (tptr tschar))
                           (tptr (tptr tschar))) :: nil))
                      (Sset _value (Etempvar _t'5 tdouble)))
                    (Ssequence
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _b (tptr tschar)) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'7 (Evar _endptr (tptr tschar)))
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _t'7 (tptr tschar))
                                         (Etempvar _b (tptr tschar)) tint)
                            (Sreturn (Some (Econst_int (Int.repr 2) tint)))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'6)
                              (Evar _asn_double2REAL (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                         (Tcons tdouble Tnil))
                                                       tint cc_default))
                              ((Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                               (Etempvar _value tdouble) :: nil))
                            (Sifthenelse (Etempvar _t'6 tint)
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                              Sskip))
                          (Sreturn (Some (Econst_int (Int.repr 4) tint))))))))))))))))
|}.

Definition f_REAL_decode_xer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) ::
                (_opt_mname, (tptr tschar)) :: (_buf_ptr, (tptr tvoid)) ::
                (_size, tulong) :: nil);
  fn_vars := ((__res__1, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _xer_decode_primitive (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _asn_dec_rval_s noattr))
                                      (Tcons
                                        (tptr (Tstruct _asn_codec_ctx_s noattr))
                                        (Tcons
                                          (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                          (Tcons (tptr (tptr tvoid))
                                            (Tcons tulong
                                              (Tcons (tptr tschar)
                                                (Tcons (tptr tvoid)
                                                  (Tcons tulong
                                                    (Tcons
                                                      (tptr (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))
                                                              tint
                                                              cc_default))
                                                      Tnil))))))))) tvoid
                                    {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
      ((Eaddrof (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))
         (tptr (Tstruct _asn_dec_rval_s noattr))) ::
       (Etempvar _opt_codec_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
       (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
       (Etempvar _sptr (tptr (tptr tvoid))) ::
       (Esizeof (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) tulong) ::
       (Etempvar _opt_mname (tptr tschar)) ::
       (Etempvar _buf_ptr (tptr tvoid)) :: (Etempvar _size tulong) ::
       (Evar _REAL__xer_body_decode (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                        (Tcons (tptr tvoid)
                                          (Tcons (tptr tvoid)
                                            (Tcons tulong Tnil)))) tint
                                      cc_default)) :: nil))
    (Sassign
      (Ederef (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
        (Tstruct _asn_dec_rval_s noattr))
      (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))))
  (Sreturn None))
|}.

Definition f_asn_REAL2double := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                (_dbl_value, (tptr tdouble)) :: nil);
  fn_vars := ((_endptr, (tptr tschar)) :: nil);
  fn_temps := ((_octv, tuint) :: (_d, tdouble) :: (_source, (tptr tschar)) ::
               (_used_malloc, tint) :: (_p, (tptr tuchar)) ::
               (_end, (tptr tuchar)) :: (_b, (tptr tschar)) ::
               (_m, tdouble) :: (_expval, tint) :: (_elen, tuint) ::
               (_scaleF, tint) :: (_baseF, tint) :: (_ptr, (tptr tuchar)) ::
               (_end__1, (tptr tuchar)) :: (_sign, tint) :: (_t'32, tint) ::
               (_t'31, tint) :: (_t'30, tint) :: (_t'29, tint) ::
               (_t'28, tint) :: (_t'27, (tptr tint)) :: (_t'26, tdouble) ::
               (_t'25, tdouble) :: (_t'24, tdouble) ::
               (_t'23, (tptr tint)) :: (_t'22, tint) ::
               (_t'21, (tptr tint)) :: (_t'20, (tptr tint)) ::
               (_t'19, (tptr tint)) :: (_t'18, tint) :: (_t'17, tint) ::
               (_t'16, tint) :: (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, (tptr tint)) :: (_t'12, (tptr tint)) ::
               (_t'11, tdouble) :: (_t'10, (tptr tvoid)) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, (tptr tschar)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tint) :: (_t'4, (tptr tint)) ::
               (_t'3, (tptr tint)) :: (_t'2, tint) :: (_t'1, (tptr tint)) ::
               (_t'61, (tptr tuchar)) :: (_t'60, tulong) ::
               (_t'59, (tptr tuchar)) :: (_t'58, tuchar) ::
               (_t'57, (tptr tuchar)) :: (_t'56, tulong) ::
               (_t'55, (tptr tuchar)) :: (_t'54, tuchar) ::
               (_t'53, tulong) :: (_t'52, (tptr tuchar)) ::
               (_t'51, tulong) :: (_t'50, (tptr tuchar)) ::
               (_t'49, tulong) :: (_t'48, (tptr tuchar)) ::
               (_t'47, tuchar) :: (_t'46, tuchar) ::
               (_t'45, (tptr tuchar)) :: (_t'44, tschar) ::
               (_t'43, (tptr tschar)) :: (_t'42, tulong) ::
               (_t'41, (tptr tuchar)) :: (_t'40, tulong) ::
               (_t'39, (tptr tuchar)) :: (_t'38, (tptr tuchar)) ::
               (_t'37, tschar) :: (_t'36, tuchar) :: (_t'35, tulong) ::
               (_t'34, (tptr tuchar)) :: (_t'33, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                   tint)
      (Sset _t'2 (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Sset _t'61
          (Efield
            (Ederef
              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf (tptr tuchar)))
        (Sset _t'2
          (Ecast (Eunop Onotbool (Etempvar _t'61 (tptr tuchar)) tint) tbool))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar ___errno_location (Tfunction Tnil (tptr tint) cc_default))
            nil)
          (Sassign (Ederef (Etempvar _t'1 (tptr tint)) tint)
            (Econst_int (Int.repr 22) tint)))
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'60
        (Efield
          (Ederef
            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _size tulong))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'60 tulong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sassign (Ederef (Etempvar _dbl_value (tptr tdouble)) tdouble)
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'59
          (Efield
            (Ederef
              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf (tptr tuchar)))
        (Sset _octv
          (Ederef
            (Ebinop Oadd (Etempvar _t'59 (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)))
      (Ssequence
        (Sswitch (Ebinop Oand (Etempvar _octv tuint)
                   (Econst_int (Int.repr 192) tint) tuint)
          (LScons (Some 64)
            (Ssequence
              (Ssequence
                (Sset _t'57
                  (Efield
                    (Ederef
                      (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                      (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                    (tptr tuchar)))
                (Ssequence
                  (Sset _t'58
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'57 (tptr tuchar))
                        (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
                  (Sswitch (Ederef
                             (Ebinop Oadd
                               (Efield
                                 (Ederef
                                   (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                   (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                 _buf (tptr tuchar))
                               (Econst_int (Int.repr 0) tint) (tptr tuchar))
                             tuchar)
                    (LScons (Some 64)
                      (Ssequence
                        (Sassign
                          (Ederef (Etempvar _dbl_value (tptr tdouble))
                            tdouble)
                          (Econst_single (Float32.of_bits (Int.repr 2139095040)) tfloat))
                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                      (LScons (Some 65)
                        (Ssequence
                          (Sassign
                            (Ederef (Etempvar _dbl_value (tptr tdouble))
                              tdouble)
                            (Eunop Oneg
                              (Econst_single (Float32.of_bits (Int.repr 2139095040)) tfloat)
                              tfloat))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                        (LScons (Some 66)
                          (Ssequence
                            (Sassign
                              (Ederef (Etempvar _dbl_value (tptr tdouble))
                                tdouble)
                              (Ebinop Odiv
                                (Econst_single (Float32.of_bits (Int.repr 0)) tfloat)
                                (Econst_single (Float32.of_bits (Int.repr 0)) tfloat)
                                tfloat))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                          (LScons (Some 67)
                            (Ssequence
                              (Sassign
                                (Ederef (Etempvar _dbl_value (tptr tdouble))
                                  tdouble)
                                (Eunop Oneg
                                  (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                  tdouble))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                            LSnil)))))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar ___errno_location (Tfunction Tnil (tptr tint)
                                              cc_default)) nil)
                  (Sassign (Ederef (Etempvar _t'3 (tptr tint)) tint)
                    (Econst_int (Int.repr 22) tint)))
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint)))))
            (LScons (Some 0)
              (Ssequence
                (Sset _source
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tschar)))
                (Ssequence
                  (Sset _used_malloc (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _octv tuint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sset _t'5 (Econst_int (Int.repr 1) tint))
                        (Sset _t'5
                          (Ecast
                            (Ebinop Oand (Etempvar _octv tuint)
                              (Econst_int (Int.repr 60) tint) tuint) tbool)))
                      (Sifthenelse (Etempvar _t'5 tint)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar ___errno_location (Tfunction Tnil
                                                        (tptr tint)
                                                        cc_default)) nil)
                            (Sassign
                              (Ederef (Etempvar _t'4 (tptr tint)) tint)
                              (Econst_int (Int.repr 22) tint)))
                          (Sreturn (Some (Eunop Oneg
                                           (Econst_int (Int.repr 1) tint)
                                           tint))))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'52
                            (Efield
                              (Ederef
                                (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                              (tptr tuchar)))
                          (Ssequence
                            (Sset _t'53
                              (Efield
                                (Ederef
                                  (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                _size tulong))
                            (Ssequence
                              (Sset _t'54
                                (Ederef
                                  (Ebinop Oadd (Etempvar _t'52 (tptr tuchar))
                                    (Etempvar _t'53 tulong) (tptr tuchar))
                                  tuchar))
                              (Sifthenelse (Ebinop One
                                             (Etempvar _t'54 tuchar)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Sset _t'9 (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'55
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _buf (tptr tuchar)))
                                    (Ssequence
                                      (Sset _t'56
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _size tulong))
                                      (Scall (Some _t'10)
                                        (Evar _memchr (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          (Tcons tint
                                                            (Tcons tulong
                                                              Tnil)))
                                                        (tptr tvoid)
                                                        cc_default))
                                        ((Etempvar _t'55 (tptr tuchar)) ::
                                         (Econst_int (Int.repr 44) tint) ::
                                         (Etempvar _t'56 tulong) :: nil))))
                                  (Sset _t'9
                                    (Ecast (Etempvar _t'10 (tptr tvoid))
                                      tbool)))))))
                        (Sifthenelse (Etempvar _t'9 tint)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'51
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _size tulong))
                                    (Scall (Some _t'6)
                                      (Evar _malloc (Tfunction
                                                      (Tcons tulong Tnil)
                                                      (tptr tvoid)
                                                      cc_default))
                                      ((Ebinop Oadd (Etempvar _t'51 tulong)
                                         (Econst_int (Int.repr 1) tint)
                                         tulong) :: nil)))
                                  (Sset _t'7
                                    (Ecast
                                      (Ecast (Etempvar _t'6 (tptr tvoid))
                                        (tptr tschar)) (tptr tschar))))
                                (Sset _source (Etempvar _t'7 (tptr tschar))))
                              (Sset _b (Etempvar _t'7 (tptr tschar))))
                            (Ssequence
                              (Sifthenelse (Eunop Onotbool
                                             (Etempvar _source (tptr tschar))
                                             tint)
                                (Sreturn (Some (Eunop Oneg
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)))
                                Sskip)
                              (Ssequence
                                (Sset _used_malloc
                                  (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'50
                                          (Efield
                                            (Ederef
                                              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                            _buf (tptr tuchar)))
                                        (Sset _p
                                          (Ebinop Oadd
                                            (Etempvar _t'50 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Ssequence
                                        (Sset _t'48
                                          (Efield
                                            (Ederef
                                              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                            _buf (tptr tuchar)))
                                        (Ssequence
                                          (Sset _t'49
                                            (Efield
                                              (Ederef
                                                (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                                (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                              _size tulong))
                                          (Sset _end
                                            (Ebinop Oadd
                                              (Etempvar _t'48 (tptr tuchar))
                                              (Etempvar _t'49 tulong)
                                              (tptr tuchar))))))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _p (tptr tuchar))
                                                       (Etempvar _end (tptr tuchar))
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'46
                                              (Ederef
                                                (Etempvar _p (tptr tuchar))
                                                tuchar))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _t'46 tuchar)
                                                           (Econst_int (Int.repr 44) tint)
                                                           tint)
                                              (Sset _t'8
                                                (Ecast
                                                  (Econst_int (Int.repr 46) tint)
                                                  tint))
                                              (Ssequence
                                                (Sset _t'47
                                                  (Ederef
                                                    (Etempvar _p (tptr tuchar))
                                                    tuchar))
                                                (Sset _t'8
                                                  (Ecast
                                                    (Etempvar _t'47 tuchar)
                                                    tint)))))
                                          (Sassign
                                            (Ederef
                                              (Etempvar _b (tptr tschar))
                                              tschar) (Etempvar _t'8 tint))))
                                      (Ssequence
                                        (Sset _b
                                          (Ebinop Oadd
                                            (Etempvar _b (tptr tschar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tschar)))
                                        (Sset _p
                                          (Ebinop Oadd
                                            (Etempvar _p (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))))
                                  (Sassign
                                    (Ederef (Etempvar _b (tptr tschar))
                                      tschar) (Econst_int (Int.repr 0) tint))))))
                          (Ssequence
                            (Sset _t'45
                              (Efield
                                (Ederef
                                  (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                _buf (tptr tuchar)))
                            (Sset _source
                              (Ecast
                                (Ebinop Oadd (Etempvar _t'45 (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)) (tptr tschar))))))
                      (Ssequence
                        (Sassign (Evar _endptr (tptr tschar))
                          (Etempvar _source (tptr tschar)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _strtod (Tfunction
                                              (Tcons (tptr tschar)
                                                (Tcons (tptr (tptr tschar))
                                                  Tnil)) tdouble cc_default))
                              ((Etempvar _source (tptr tschar)) ::
                               (Eaddrof (Evar _endptr (tptr tschar))
                                 (tptr (tptr tschar))) :: nil))
                            (Sset _d (Etempvar _t'11 tdouble)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'43 (Evar _endptr (tptr tschar)))
                              (Ssequence
                                (Sset _t'44
                                  (Ederef (Etempvar _t'43 (tptr tschar))
                                    tschar))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _t'44 tschar)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Ssequence
                                    (Sifthenelse (Etempvar _used_malloc tint)
                                      (Scall None
                                        (Evar _free (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        Tnil) tvoid
                                                      cc_default))
                                        ((Etempvar _source (tptr tschar)) ::
                                         nil))
                                      Sskip)
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'12)
                                          (Evar ___errno_location (Tfunction
                                                                    Tnil
                                                                    (tptr tint)
                                                                    cc_default))
                                          nil)
                                        (Sassign
                                          (Ederef
                                            (Etempvar _t'12 (tptr tint))
                                            tint)
                                          (Econst_int (Int.repr 22) tint)))
                                      (Sreturn (Some (Eunop Oneg
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)))))
                                  Sskip)))
                            (Ssequence
                              (Sifthenelse (Etempvar _used_malloc tint)
                                (Scall None
                                  (Evar _free (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                                  ((Etempvar _source (tptr tschar)) :: nil))
                                Sskip)
                              (Ssequence
                                (Sifthenelse (Ebinop Oeq
                                               (Esizeof tdouble tulong)
                                               (Esizeof tfloat tulong) tint)
                                  (Ssequence
                                    (Scall (Some _t'15)
                                      (Evar ___finitef (Tfunction
                                                         (Tcons tfloat Tnil)
                                                         tint cc_default))
                                      ((Etempvar _d tdouble) :: nil))
                                    (Sset _t'14
                                      (Ecast (Etempvar _t'15 tint) tint)))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Esizeof tdouble tulong)
                                                 (Esizeof tdouble tulong)
                                                 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'17)
                                          (Evar ___finite (Tfunction
                                                            (Tcons tdouble
                                                              Tnil) tint
                                                            cc_default))
                                          ((Etempvar _d tdouble) :: nil))
                                        (Sset _t'16
                                          (Ecast (Etempvar _t'17 tint) tint)))
                                      (Sset _t'14
                                        (Ecast (Etempvar _t'16 tint) tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'18)
                                          (Evar ___finitel (Tfunction
                                                             (Tcons tdouble
                                                               Tnil) tint
                                                             cc_default))
                                          ((Etempvar _d tdouble) :: nil))
                                        (Sset _t'16
                                          (Ecast (Etempvar _t'18 tint) tint)))
                                      (Sset _t'14
                                        (Ecast (Etempvar _t'16 tint) tint)))))
                                (Sifthenelse (Etempvar _t'14 tint)
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Etempvar _dbl_value (tptr tdouble))
                                        tdouble) (Etempvar _d tdouble))
                                    (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'13)
                                        (Evar ___errno_location (Tfunction
                                                                  Tnil
                                                                  (tptr tint)
                                                                  cc_default))
                                        nil)
                                      (Sassign
                                        (Ederef (Etempvar _t'13 (tptr tint))
                                          tint)
                                        (Econst_int (Int.repr 34) tint)))
                                    (Sreturn (Some (Eunop Oneg
                                                     (Econst_int (Int.repr 1) tint)
                                                     tint))))))))))))))
              LSnil)))
        (Ssequence
          (Ssequence
            (Sswitch (Ebinop Oshr
                       (Ebinop Oand (Etempvar _octv tuint)
                         (Econst_int (Int.repr 48) tint) tuint)
                       (Econst_int (Int.repr 4) tint) tuint)
              (LScons (Some 0)
                (Ssequence
                  (Sset _baseF (Econst_int (Int.repr 1) tint))
                  Sbreak)
                (LScons (Some 1)
                  (Ssequence
                    (Sset _baseF (Econst_int (Int.repr 3) tint))
                    Sbreak)
                  (LScons (Some 2)
                    (Ssequence
                      (Sset _baseF (Econst_int (Int.repr 4) tint))
                      Sbreak)
                    (LScons None
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'19)
                            (Evar ___errno_location (Tfunction Tnil
                                                      (tptr tint) cc_default))
                            nil)
                          (Sassign (Ederef (Etempvar _t'19 (tptr tint)) tint)
                            (Econst_int (Int.repr 22) tint)))
                        (Sreturn (Some (Eunop Oneg
                                         (Econst_int (Int.repr 1) tint) tint))))
                      LSnil)))))
            (Ssequence
              (Sset _sign
                (Ebinop Oand (Etempvar _octv tuint)
                  (Econst_int (Int.repr 64) tint) tuint))
              (Ssequence
                (Sset _scaleF
                  (Ebinop Oshr
                    (Ebinop Oand (Etempvar _octv tuint)
                      (Econst_int (Int.repr 12) tint) tuint)
                    (Econst_int (Int.repr 2) tint) tuint))
                (Ssequence
                  (Ssequence
                    (Sset _t'42
                      (Efield
                        (Ederef
                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _size
                        tulong))
                    (Sifthenelse (Ebinop Ole (Etempvar _t'42 tulong)
                                   (Ebinop Oadd
                                     (Econst_int (Int.repr 1) tint)
                                     (Ebinop Oand (Etempvar _octv tuint)
                                       (Econst_int (Int.repr 3) tint) tuint)
                                     tuint) tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'20)
                            (Evar ___errno_location (Tfunction Tnil
                                                      (tptr tint) cc_default))
                            nil)
                          (Sassign (Ederef (Etempvar _t'20 (tptr tint)) tint)
                            (Econst_int (Int.repr 22) tint)))
                        (Sreturn (Some (Eunop Oneg
                                         (Econst_int (Int.repr 1) tint) tint))))
                      Sskip))
                  (Ssequence
                    (Sset _elen
                      (Ebinop Oand (Etempvar _octv tuint)
                        (Econst_int (Int.repr 3) tint) tuint))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _elen tuint)
                                     (Econst_int (Int.repr 3) tint) tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'41
                              (Efield
                                (Ederef
                                  (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                _buf (tptr tuchar)))
                            (Sset _elen
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'41 (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)) tuchar)))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Oeq (Etempvar _elen tuint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Sset _t'22 (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sset _t'40
                                    (Efield
                                      (Ederef
                                        (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                        (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                      _size tulong))
                                  (Sset _t'22
                                    (Ecast
                                      (Ebinop Ole (Etempvar _t'40 tulong)
                                        (Ebinop Oadd
                                          (Econst_int (Int.repr 2) tint)
                                          (Etempvar _elen tuint) tuint) tint)
                                      tbool))))
                              (Sifthenelse (Etempvar _t'22 tint)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'21)
                                      (Evar ___errno_location (Tfunction Tnil
                                                                (tptr tint)
                                                                cc_default))
                                      nil)
                                    (Sassign
                                      (Ederef (Etempvar _t'21 (tptr tint))
                                        tint)
                                      (Econst_int (Int.repr 22) tint)))
                                  (Sreturn (Some (Eunop Oneg
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint))))
                                Sskip))
                            (Ssequence
                              (Sset _t'39
                                (Efield
                                  (Ederef
                                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                  _buf (tptr tuchar)))
                              (Sset _ptr
                                (Ebinop Oadd (Etempvar _t'39 (tptr tuchar))
                                  (Econst_int (Int.repr 2) tint)
                                  (tptr tuchar))))))
                        (Ssequence
                          (Sset _t'38
                            (Efield
                              (Ederef
                                (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                              (tptr tuchar)))
                          (Sset _ptr
                            (Ebinop Oadd (Etempvar _t'38 (tptr tuchar))
                              (Econst_int (Int.repr 1) tint) (tptr tuchar)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'37
                            (Ederef
                              (Ecast (Etempvar _ptr (tptr tuchar))
                                (tptr tschar)) tschar))
                          (Sset _expval (Ecast (Etempvar _t'37 tschar) tint)))
                        (Ssequence
                          (Sifthenelse (Ebinop Oge (Etempvar _elen tuint)
                                         (Ebinop Osub (Esizeof tint tulong)
                                           (Econst_int (Int.repr 1) tint)
                                           tulong) tint)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'23)
                                  (Evar ___errno_location (Tfunction Tnil
                                                            (tptr tint)
                                                            cc_default)) nil)
                                (Sassign
                                  (Ederef (Etempvar _t'23 (tptr tint)) tint)
                                  (Econst_int (Int.repr 34) tint)))
                              (Sreturn (Some (Eunop Oneg
                                               (Econst_int (Int.repr 1) tint)
                                               tint))))
                            Sskip)
                          (Ssequence
                            (Sset _end__1
                              (Ebinop Oadd
                                (Ebinop Oadd (Etempvar _ptr (tptr tuchar))
                                  (Etempvar _elen tuint) (tptr tuchar))
                                (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                            (Ssequence
                              (Ssequence
                                (Sset _ptr
                                  (Ebinop Oadd (Etempvar _ptr (tptr tuchar))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tuchar)))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _ptr (tptr tuchar))
                                                   (Etempvar _end__1 (tptr tuchar))
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'36
                                        (Ederef (Etempvar _ptr (tptr tuchar))
                                          tuchar))
                                      (Sset _expval
                                        (Ebinop Oadd
                                          (Ebinop Omul
                                            (Etempvar _expval tint)
                                            (Econst_int (Int.repr 256) tint)
                                            tint) (Etempvar _t'36 tuchar)
                                          tint))))
                                  (Sset _ptr
                                    (Ebinop Oadd
                                      (Etempvar _ptr (tptr tuchar))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuchar)))))
                              (Ssequence
                                (Sset _m
                                  (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'34
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _buf (tptr tuchar)))
                                    (Ssequence
                                      (Sset _t'35
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _size tulong))
                                      (Sset _end__1
                                        (Ebinop Oadd
                                          (Etempvar _t'34 (tptr tuchar))
                                          (Etempvar _t'35 tulong)
                                          (tptr tuchar)))))
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _ptr (tptr tuchar))
                                                       (Etempvar _end__1 (tptr tuchar))
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Scall (Some _t'24)
                                            (Evar _ldexp (Tfunction
                                                           (Tcons tdouble
                                                             (Tcons tint
                                                               Tnil)) tdouble
                                                           cc_default))
                                            ((Etempvar _m tdouble) ::
                                             (Econst_int (Int.repr 8) tint) ::
                                             nil))
                                          (Ssequence
                                            (Sset _t'33
                                              (Ederef
                                                (Etempvar _ptr (tptr tuchar))
                                                tuchar))
                                            (Sset _m
                                              (Ebinop Oadd
                                                (Etempvar _t'24 tdouble)
                                                (Etempvar _t'33 tuchar)
                                                tdouble)))))
                                      (Sset _ptr
                                        (Ebinop Oadd
                                          (Etempvar _ptr (tptr tuchar))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuchar))))
                                    (Ssequence
                                      (Sifthenelse (Econst_int (Int.repr 0) tint)
                                        (Sloop Sskip Sbreak)
                                        Sskip)
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'25)
                                            (Evar _ldexp (Tfunction
                                                           (Tcons tdouble
                                                             (Tcons tint
                                                               Tnil)) tdouble
                                                           cc_default))
                                            ((Etempvar _m tdouble) ::
                                             (Ebinop Oadd
                                               (Ebinop Omul
                                                 (Etempvar _expval tint)
                                                 (Etempvar _baseF tint) tint)
                                               (Etempvar _scaleF tint) tint) ::
                                             nil))
                                          (Sset _m (Etempvar _t'25 tdouble)))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oeq
                                                         (Esizeof tdouble tulong)
                                                         (Esizeof tfloat tulong)
                                                         tint)
                                            (Ssequence
                                              (Scall (Some _t'29)
                                                (Evar ___finitef (Tfunction
                                                                   (Tcons
                                                                    tfloat
                                                                    Tnil)
                                                                   tint
                                                                   cc_default))
                                                ((Etempvar _m tdouble) ::
                                                 nil))
                                              (Sset _t'28
                                                (Ecast (Etempvar _t'29 tint)
                                                  tint)))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Esizeof tdouble tulong)
                                                           (Esizeof tdouble tulong)
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'31)
                                                    (Evar ___finite (Tfunction
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil)
                                                                    tint
                                                                    cc_default))
                                                    ((Etempvar _m tdouble) ::
                                                     nil))
                                                  (Sset _t'30
                                                    (Ecast
                                                      (Etempvar _t'31 tint)
                                                      tint)))
                                                (Sset _t'28
                                                  (Ecast
                                                    (Etempvar _t'30 tint)
                                                    tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'32)
                                                    (Evar ___finitel 
                                                    (Tfunction
                                                      (Tcons tdouble Tnil)
                                                      tint cc_default))
                                                    ((Etempvar _m tdouble) ::
                                                     nil))
                                                  (Sset _t'30
                                                    (Ecast
                                                      (Etempvar _t'32 tint)
                                                      tint)))
                                                (Sset _t'28
                                                  (Ecast
                                                    (Etempvar _t'30 tint)
                                                    tint)))))
                                          (Sifthenelse (Etempvar _t'28 tint)
                                            (Ssequence
                                              (Sifthenelse (Etempvar _sign tint)
                                                (Sset _t'26
                                                  (Ecast
                                                    (Eunop Oneg
                                                      (Etempvar _m tdouble)
                                                      tdouble) tdouble))
                                                (Sset _t'26
                                                  (Ecast
                                                    (Etempvar _m tdouble)
                                                    tdouble)))
                                              (Sassign
                                                (Ederef
                                                  (Etempvar _dbl_value (tptr tdouble))
                                                  tdouble)
                                                (Etempvar _t'26 tdouble)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'27)
                                                  (Evar ___errno_location 
                                                  (Tfunction Tnil (tptr tint)
                                                    cc_default)) nil)
                                                (Sassign
                                                  (Ederef
                                                    (Etempvar _t'27 (tptr tint))
                                                    tint)
                                                  (Econst_int (Int.repr 34) tint)))
                                              (Sreturn (Some (Eunop Oneg
                                                               (Econst_int (Int.repr 1) tint)
                                                               tint)))))))))))))))))))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_asn_double2REAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                (_dbl_value, tdouble) :: nil);
  fn_vars := ((_dbl_value, tdouble) :: (_test, tdouble) ::
              (_buf, (tarray tuchar 16)) :: (_dscr, (tarray tuchar 8)) ::
              (_assertion_buffer1, (tarray tschar 1)) ::
              (_assertion_buffer2, (tarray tschar 1)) :: nil);
  fn_temps := ((_float_big_endian, tint) :: (_ptr, (tptr tuchar)) ::
               (_mstop, (tptr tuchar)) :: (_mval, tuint) ::
               (_bmsign, tuint) :: (_buflen, tuint) :: (_accum, tuint) ::
               (_expval, tint) :: (_s, (tptr tuchar)) ::
               (_end, (tptr tuchar)) :: (_d, (tptr tuchar)) ::
               (_s__1, (tptr tuchar)) :: (_start, (tptr tuchar)) ::
               (_d__1, (tptr tuchar)) :: (_shift_count, tint) ::
               (_ishift, tint) :: (_mptr, (tptr tuchar)) ::
               (_t'39, (tptr tvoid)) :: (_t'38, (tptr tuchar)) ::
               (_t'37, (tptr tuchar)) :: (_t'36, (tptr tuchar)) ::
               (_t'35, (tptr tuchar)) :: (_t'34, (tptr tuchar)) ::
               (_t'33, (tptr tuchar)) :: (_t'32, (tptr tuchar)) ::
               (_t'31, (tptr tuchar)) :: (_t'30, (tptr tuchar)) ::
               (_t'29, (tptr tuchar)) :: (_t'28, (tptr tuchar)) ::
               (_t'27, (tptr tuchar)) :: (_t'26, (tptr tuchar)) ::
               (_t'25, (tptr tuchar)) :: (_t'24, (tptr tuchar)) ::
               (_t'23, (tptr tuchar)) :: (_t'22, (tptr tuchar)) ::
               (_t'21, (tptr tuchar)) :: (_t'20, tint) ::
               (_t'19, (tptr tuchar)) :: (_t'18, (tptr tuchar)) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tdouble) ::
               (_t'5, tdouble) :: (_t'4, tint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tint) :: (_t'1, (tptr tint)) :: (_t'70, tschar) ::
               (_t'69, tdouble) :: (_t'68, tulong) ::
               (_t'67, (tptr tuchar)) :: (_t'66, (tptr tuchar)) ::
               (_t'65, (tptr tuchar)) :: (_t'64, tdouble) ::
               (_t'63, tdouble) :: (_t'62, tdouble) ::
               (_t'61, (tptr tuchar)) :: (_t'60, (tptr tuchar)) ::
               (_t'59, tdouble) :: (_t'58, tdouble) :: (_t'57, tdouble) ::
               (_t'56, tdouble) :: (_t'55, (tptr tuchar)) ::
               (_t'54, (tptr tuchar)) :: (_t'53, (tptr tuchar)) ::
               (_t'52, tdouble) :: (_t'51, (tptr tuchar)) ::
               (_t'50, (tptr tuchar)) :: (_t'49, (tptr tuchar)) ::
               (_t'48, tuchar) :: (_t'47, tuchar) :: (_t'46, tuchar) ::
               (_t'45, tuchar) :: (_t'44, tuchar) :: (_t'43, tuchar) ::
               (_t'42, tuchar) :: (_t'41, (tptr tuchar)) ::
               (_t'40, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _dbl_value tdouble) (Etempvar _dbl_value tdouble))
  (Ssequence
    (Sassign (Evar _test tdouble)
      (Eunop Oneg (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
        tdouble))
    (Ssequence
      (Ssequence
        (Sset _t'70
          (Ederef
            (Ecast (Eaddrof (Evar _test tdouble) (tptr tdouble))
              (tptr tschar)) tschar))
        (Sset _float_big_endian
          (Ebinop One (Etempvar _t'70 tschar) (Econst_int (Int.repr 0) tint)
            tint)))
      (Ssequence
        (Sset _ptr (Evar _buf (tarray tuchar 16)))
        (Ssequence
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                         tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar ___errno_location (Tfunction Tnil (tptr tint)
                                            cc_default)) nil)
                (Sassign (Ederef (Etempvar _t'1 (tptr tint)) tint)
                  (Econst_int (Int.repr 22) tint)))
              (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))
            Sskip)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'69 (Evar _dbl_value tdouble))
                (Scall (Some _t'2)
                  (Evar _ilogb (Tfunction (Tcons tdouble Tnil) tint
                                 cc_default))
                  ((Etempvar _t'69 tdouble) :: nil)))
              (Sset _expval (Etempvar _t'2 tint)))
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Ole (Etempvar _expval tint)
                               (Eunop Oneg
                                 (Ecast
                                   (Ebinop Oshr
                                     (Ecast
                                       (Eunop Oneg
                                         (Econst_int (Int.repr 1) tint) tint)
                                       tuint) (Econst_int (Int.repr 1) tint)
                                     tuint) tint) tint) tint)
                  (Sset _t'17 (Econst_int (Int.repr 1) tint))
                  (Sset _t'17
                    (Ecast
                      (Ebinop Oeq (Etempvar _expval tint)
                        (Ecast
                          (Ebinop Oshr
                            (Ecast
                              (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                tint) tuint) (Econst_int (Int.repr 1) tint)
                            tuint) tint) tint) tbool)))
                (Sifthenelse (Etempvar _t'17 tint)
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'67
                          (Efield
                            (Ederef
                              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                            (tptr tuchar)))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _t'67 (tptr tuchar)) tint)
                          (Sset _t'4 (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Sset _t'68
                              (Efield
                                (Ederef
                                  (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                _size tulong))
                            (Sset _t'4
                              (Ecast
                                (Ebinop Olt (Etempvar _t'68 tulong)
                                  (Econst_int (Int.repr 2) tint) tint) tbool)))))
                      (Sifthenelse (Etempvar _t'4 tint)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _malloc (Tfunction (Tcons tulong Tnil)
                                              (tptr tvoid) cc_default))
                              ((Econst_int (Int.repr 2) tint) :: nil))
                            (Sset _ptr
                              (Ecast (Etempvar _t'3 (tptr tvoid))
                                (tptr tuchar))))
                          (Ssequence
                            (Sifthenelse (Eunop Onotbool
                                           (Etempvar _ptr (tptr tuchar))
                                           tint)
                              (Sreturn (Some (Eunop Oneg
                                               (Econst_int (Int.repr 1) tint)
                                               tint)))
                              Sskip)
                            (Ssequence
                              (Ssequence
                                (Sset _t'65
                                  (Efield
                                    (Ederef
                                      (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                      (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                    _buf (tptr tuchar)))
                                (Sifthenelse (Etempvar _t'65 (tptr tuchar))
                                  (Ssequence
                                    (Sset _t'66
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _buf (tptr tuchar)))
                                    (Scall None
                                      (Evar _free (Tfunction
                                                    (Tcons (tptr tvoid) Tnil)
                                                    tvoid cc_default))
                                      ((Etempvar _t'66 (tptr tuchar)) :: nil)))
                                  Sskip))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                  _buf (tptr tuchar))
                                (Etempvar _ptr (tptr tuchar))))))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                       (Esizeof tfloat tulong) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'64 (Evar _dbl_value tdouble))
                              (Scall (Some _t'13)
                                (Evar ___isnanf (Tfunction
                                                  (Tcons tfloat Tnil) tint
                                                  cc_default))
                                ((Etempvar _t'64 tdouble) :: nil)))
                            (Sset _t'12 (Ecast (Etempvar _t'13 tint) tint)))
                          (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                         (Esizeof tdouble tulong) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'63 (Evar _dbl_value tdouble))
                                  (Scall (Some _t'15)
                                    (Evar ___isnan (Tfunction
                                                     (Tcons tdouble Tnil)
                                                     tint cc_default))
                                    ((Etempvar _t'63 tdouble) :: nil)))
                                (Sset _t'14
                                  (Ecast (Etempvar _t'15 tint) tint)))
                              (Sset _t'12 (Ecast (Etempvar _t'14 tint) tint)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'62 (Evar _dbl_value tdouble))
                                  (Scall (Some _t'16)
                                    (Evar ___isnanl (Tfunction
                                                      (Tcons tdouble Tnil)
                                                      tint cc_default))
                                    ((Etempvar _t'62 tdouble) :: nil)))
                                (Sset _t'14
                                  (Ecast (Etempvar _t'16 tint) tint)))
                              (Sset _t'12 (Ecast (Etempvar _t'14 tint) tint)))))
                        (Sifthenelse (Etempvar _t'12 tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'61
                                (Efield
                                  (Ederef
                                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                  _buf (tptr tuchar)))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Etempvar _t'61 (tptr tuchar))
                                    (Econst_int (Int.repr 0) tint)
                                    (tptr tuchar)) tuchar)
                                (Econst_int (Int.repr 66) tint)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'60
                                  (Efield
                                    (Ederef
                                      (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                      (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                    _buf (tptr tuchar)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _t'60 (tptr tuchar))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuchar)) tuchar)
                                  (Econst_int (Int.repr 0) tint)))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                  _size tulong)
                                (Econst_int (Int.repr 1) tint))))
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                                           (Esizeof tfloat tulong) tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'59 (Evar _dbl_value tdouble))
                                  (Scall (Some _t'8)
                                    (Evar ___finitef (Tfunction
                                                       (Tcons tfloat Tnil)
                                                       tint cc_default))
                                    ((Etempvar _t'59 tdouble) :: nil)))
                                (Sset _t'7 (Ecast (Etempvar _t'8 tint) tint)))
                              (Sifthenelse (Ebinop Oeq
                                             (Esizeof tdouble tulong)
                                             (Esizeof tdouble tulong) tint)
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'58 (Evar _dbl_value tdouble))
                                      (Scall (Some _t'10)
                                        (Evar ___finite (Tfunction
                                                          (Tcons tdouble
                                                            Tnil) tint
                                                          cc_default))
                                        ((Etempvar _t'58 tdouble) :: nil)))
                                    (Sset _t'9
                                      (Ecast (Etempvar _t'10 tint) tint)))
                                  (Sset _t'7
                                    (Ecast (Etempvar _t'9 tint) tint)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'57 (Evar _dbl_value tdouble))
                                      (Scall (Some _t'11)
                                        (Evar ___finitel (Tfunction
                                                           (Tcons tdouble
                                                             Tnil) tint
                                                           cc_default))
                                        ((Etempvar _t'57 tdouble) :: nil)))
                                    (Sset _t'9
                                      (Ecast (Etempvar _t'11 tint) tint)))
                                  (Sset _t'7
                                    (Ecast (Etempvar _t'9 tint) tint)))))
                            (Sifthenelse (Eunop Onotbool (Etempvar _t'7 tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'56 (Evar _dbl_value tdouble))
                                    (Scall (Some _t'5)
                                      (Evar _copysign (Tfunction
                                                        (Tcons tdouble
                                                          (Tcons tdouble
                                                            Tnil)) tdouble
                                                        cc_default))
                                      ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                                       (Etempvar _t'56 tdouble) :: nil)))
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _t'5 tdouble)
                                                 (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                                 tint)
                                    (Ssequence
                                      (Sset _t'55
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _buf (tptr tuchar)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'55 (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 65) tint)))
                                    (Ssequence
                                      (Sset _t'54
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _buf (tptr tuchar)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'54 (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 64) tint)))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'53
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _buf (tptr tuchar)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'53 (tptr tuchar))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuchar)) tuchar)
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                        (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                      _size tulong)
                                    (Econst_int (Int.repr 1) tint))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'52 (Evar _dbl_value tdouble))
                                  (Scall (Some _t'6)
                                    (Evar _copysign (Tfunction
                                                      (Tcons tdouble
                                                        (Tcons tdouble Tnil))
                                                      tdouble cc_default))
                                    ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                                     (Etempvar _t'52 tdouble) :: nil)))
                                (Sifthenelse (Ebinop Oge
                                               (Etempvar _t'6 tdouble)
                                               (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                               tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'51
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _buf (tptr tuchar)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'51 (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _size tulong)
                                      (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'50
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _buf (tptr tuchar)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'50 (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 67) tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'49
                                          (Efield
                                            (Ederef
                                              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                            _buf (tptr tuchar)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'49 (tptr tuchar))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuchar)) tuchar)
                                          (Econst_int (Int.repr 0) tint)))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                            (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                          _size tulong)
                                        (Econst_int (Int.repr 1) tint))))))))))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                  Sskip))
              (Ssequence
                (Sifthenelse (Etempvar _float_big_endian tint)
                  (Ssequence
                    (Sset _s
                      (Ebinop Oadd
                        (Ecast
                          (Eaddrof (Evar _dbl_value tdouble) (tptr tdouble))
                          (tptr tuchar)) (Econst_int (Int.repr 1) tint)
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _end
                        (Ebinop Oadd
                          (Ecast
                            (Eaddrof (Evar _dbl_value tdouble)
                              (tptr tdouble)) (tptr tuchar))
                          (Esizeof tdouble tulong) (tptr tuchar)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'48
                            (Ederef
                              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                  tint) (tptr tuchar)) tuchar))
                          (Sset _bmsign
                            (Ebinop Oor (Econst_int (Int.repr 128) tint)
                              (Ebinop Oand
                                (Ebinop Oshr (Etempvar _t'48 tuchar)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (Econst_int (Int.repr 64) tint) tint) tint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'18
                                (Ecast (Evar _dscr (tarray tuchar 8))
                                  (tptr tuchar)))
                              (Sset _d (Etempvar _t'18 (tptr tuchar))))
                            (Sset _mstop (Etempvar _t'18 (tptr tuchar))))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt
                                             (Etempvar _s (tptr tuchar))
                                             (Etempvar _end (tptr tuchar))
                                             tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'47
                                    (Ederef (Etempvar _s (tptr tuchar))
                                      tuchar))
                                  (Sassign
                                    (Ederef (Etempvar _d (tptr tuchar))
                                      tuchar) (Etempvar _t'47 tuchar)))
                                (Ssequence
                                  (Sset _t'46
                                    (Ederef (Etempvar _d (tptr tuchar))
                                      tuchar))
                                  (Sifthenelse (Etempvar _t'46 tuchar)
                                    (Sset _mstop (Etempvar _d (tptr tuchar)))
                                    Sskip))))
                            (Ssequence
                              (Sset _d
                                (Ebinop Oadd (Etempvar _d (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)))
                              (Sset _s
                                (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)))))))))
                  (Ssequence
                    (Sset _s__1
                      (Ebinop Osub
                        (Ebinop Oadd
                          (Ecast
                            (Eaddrof (Evar _dbl_value tdouble)
                              (tptr tdouble)) (tptr tuchar))
                          (Esizeof tdouble tulong) (tptr tuchar))
                        (Econst_int (Int.repr 2) tint) (tptr tuchar)))
                    (Ssequence
                      (Sset _start
                        (Ecast
                          (Eaddrof (Evar _dbl_value tdouble) (tptr tdouble))
                          (tptr tuchar)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'45
                            (Ederef
                              (Ebinop Oadd (Etempvar _s__1 (tptr tuchar))
                                (Econst_int (Int.repr 1) tint) (tptr tuchar))
                              tuchar))
                          (Sset _bmsign
                            (Ebinop Oor (Econst_int (Int.repr 128) tint)
                              (Ebinop Oand
                                (Ebinop Oshr (Etempvar _t'45 tuchar)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (Econst_int (Int.repr 64) tint) tint) tint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'19
                                (Ecast (Evar _dscr (tarray tuchar 8))
                                  (tptr tuchar)))
                              (Sset _d__1 (Etempvar _t'19 (tptr tuchar))))
                            (Sset _mstop (Etempvar _t'19 (tptr tuchar))))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Oge
                                             (Etempvar _s__1 (tptr tuchar))
                                             (Etempvar _start (tptr tuchar))
                                             tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'44
                                    (Ederef (Etempvar _s__1 (tptr tuchar))
                                      tuchar))
                                  (Sassign
                                    (Ederef (Etempvar _d__1 (tptr tuchar))
                                      tuchar) (Etempvar _t'44 tuchar)))
                                (Ssequence
                                  (Sset _t'43
                                    (Ederef (Etempvar _d__1 (tptr tuchar))
                                      tuchar))
                                  (Sifthenelse (Etempvar _t'43 tuchar)
                                    (Sset _mstop
                                      (Etempvar _d__1 (tptr tuchar)))
                                    Sskip))))
                            (Ssequence
                              (Sset _d__1
                                (Ebinop Oadd (Etempvar _d__1 (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)))
                              (Sset _s__1
                                (Ebinop Osub (Etempvar _s__1 (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar))))))))))
                (Ssequence
                  (Ssequence
                    (Sset _t'42
                      (Ederef
                        (Ebinop Oadd (Evar _dscr (tarray tuchar 8))
                          (Econst_int (Int.repr 0) tint) (tptr tuchar))
                        tuchar))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _dscr (tarray tuchar 8))
                          (Econst_int (Int.repr 0) tint) (tptr tuchar))
                        tuchar)
                      (Ebinop Oor (Econst_int (Int.repr 16) tint)
                        (Ebinop Oand (Etempvar _t'42 tuchar)
                          (Econst_int (Int.repr 15) tint) tint) tint)))
                  (Ssequence
                    (Sset _expval
                      (Ecast
                        (Ebinop Osub (Etempvar _expval tint)
                          (Ebinop Osub
                            (Ebinop Omul (Econst_int (Int.repr 8) tint)
                              (Ebinop Oadd
                                (Ebinop Osub (Etempvar _mstop (tptr tuchar))
                                  (Evar _dscr (tarray tuchar 8)) tlong)
                                (Econst_int (Int.repr 1) tint) tlong) tlong)
                            (Econst_int (Int.repr 4) tint) tlong) tlong)
                        tint))
                    (Ssequence
                      (Sset _mval
                        (Ederef (Etempvar _mstop (tptr tuchar)) tuchar))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Etempvar _mval tuint)
                            (Sset _t'20
                              (Ecast
                                (Eunop Onotbool
                                  (Ebinop Oand (Etempvar _mval tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)
                                  tint) tbool))
                            (Sset _t'20 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _t'20 tint)
                            (Ssequence
                              (Sset _shift_count
                                (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Sifthenelse (Eunop Onotbool
                                               (Ebinop Oand
                                                 (Etempvar _mval tuint)
                                                 (Econst_int (Int.repr 15) tint)
                                                 tuint) tint)
                                  (Sset _shift_count
                                    (Econst_int (Int.repr 4) tint))
                                  Sskip)
                                (Ssequence
                                  (Swhile
                                    (Ebinop Oeq
                                      (Ebinop Oand
                                        (Ebinop Oshr (Etempvar _mval tuint)
                                          (Etempvar _shift_count tint) tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)
                                      (Econst_int (Int.repr 0) tint) tint)
                                    (Sset _shift_count
                                      (Ebinop Oadd
                                        (Etempvar _shift_count tint)
                                        (Econst_int (Int.repr 1) tint) tint)))
                                  (Ssequence
                                    (Sset _ishift
                                      (Ebinop Osub
                                        (Econst_int (Int.repr 8) tint)
                                        (Etempvar _shift_count tint) tint))
                                    (Ssequence
                                      (Sset _accum
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _mptr
                                            (Evar _dscr (tarray tuchar 8)))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Ole
                                                             (Etempvar _mptr (tptr tuchar))
                                                             (Etempvar _mstop (tptr tuchar))
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Ssequence
                                                (Sset _mval
                                                  (Ederef
                                                    (Etempvar _mptr (tptr tuchar))
                                                    tuchar))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _mptr (tptr tuchar))
                                                      tuchar)
                                                    (Ebinop Oor
                                                      (Etempvar _accum tuint)
                                                      (Ebinop Oshr
                                                        (Etempvar _mval tuint)
                                                        (Etempvar _shift_count tint)
                                                        tuint) tuint))
                                                  (Sset _accum
                                                    (Ebinop Oshl
                                                      (Etempvar _mval tuint)
                                                      (Etempvar _ishift tint)
                                                      tuint)))))
                                            (Sset _mptr
                                              (Ebinop Oadd
                                                (Etempvar _mptr (tptr tuchar))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuchar)))))
                                        (Sset _expval
                                          (Ebinop Oadd
                                            (Etempvar _expval tint)
                                            (Etempvar _shift_count tint)
                                            tint))))))))
                            Sskip))
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _expval tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Sifthenelse (Ebinop Oeq
                                           (Ebinop Oshr
                                             (Etempvar _expval tint)
                                             (Econst_int (Int.repr 7) tint)
                                             tint)
                                           (Eunop Oneg
                                             (Econst_int (Int.repr 1) tint)
                                             tint) tint)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'21
                                      (Etempvar _ptr (tptr tuchar)))
                                    (Sset _ptr
                                      (Ebinop Oadd
                                        (Etempvar _t'21 (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar))))
                                  (Sassign
                                    (Ederef (Etempvar _t'21 (tptr tuchar))
                                      tuchar)
                                    (Ebinop Oor (Etempvar _bmsign tuint)
                                      (Econst_int (Int.repr 0) tint) tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'22
                                      (Etempvar _ptr (tptr tuchar)))
                                    (Sset _ptr
                                      (Ebinop Oadd
                                        (Etempvar _t'22 (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar))))
                                  (Sassign
                                    (Ederef (Etempvar _t'22 (tptr tuchar))
                                      tuchar) (Etempvar _expval tint))))
                              (Sifthenelse (Ebinop Oeq
                                             (Ebinop Oshr
                                               (Etempvar _expval tint)
                                               (Econst_int (Int.repr 15) tint)
                                               tint)
                                             (Eunop Oneg
                                               (Econst_int (Int.repr 1) tint)
                                               tint) tint)
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'23
                                        (Etempvar _ptr (tptr tuchar)))
                                      (Sset _ptr
                                        (Ebinop Oadd
                                          (Etempvar _t'23 (tptr tuchar))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuchar))))
                                    (Sassign
                                      (Ederef (Etempvar _t'23 (tptr tuchar))
                                        tuchar)
                                      (Ebinop Oor (Etempvar _bmsign tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'24
                                          (Etempvar _ptr (tptr tuchar)))
                                        (Sset _ptr
                                          (Ebinop Oadd
                                            (Etempvar _t'24 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t'24 (tptr tuchar))
                                          tuchar)
                                        (Ebinop Oshr (Etempvar _expval tint)
                                          (Econst_int (Int.repr 8) tint)
                                          tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'25
                                          (Etempvar _ptr (tptr tuchar)))
                                        (Sset _ptr
                                          (Ebinop Oadd
                                            (Etempvar _t'25 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t'25 (tptr tuchar))
                                          tuchar) (Etempvar _expval tint)))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'26
                                        (Etempvar _ptr (tptr tuchar)))
                                      (Sset _ptr
                                        (Ebinop Oadd
                                          (Etempvar _t'26 (tptr tuchar))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuchar))))
                                    (Sassign
                                      (Ederef (Etempvar _t'26 (tptr tuchar))
                                        tuchar)
                                      (Ebinop Oor (Etempvar _bmsign tuint)
                                        (Econst_int (Int.repr 2) tint) tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'27
                                          (Etempvar _ptr (tptr tuchar)))
                                        (Sset _ptr
                                          (Ebinop Oadd
                                            (Etempvar _t'27 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t'27 (tptr tuchar))
                                          tuchar)
                                        (Ebinop Oshr (Etempvar _expval tint)
                                          (Econst_int (Int.repr 16) tint)
                                          tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'28
                                            (Etempvar _ptr (tptr tuchar)))
                                          (Sset _ptr
                                            (Ebinop Oadd
                                              (Etempvar _t'28 (tptr tuchar))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuchar))))
                                        (Sassign
                                          (Ederef
                                            (Etempvar _t'28 (tptr tuchar))
                                            tuchar)
                                          (Ebinop Oshr
                                            (Etempvar _expval tint)
                                            (Econst_int (Int.repr 8) tint)
                                            tint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'29
                                            (Etempvar _ptr (tptr tuchar)))
                                          (Sset _ptr
                                            (Ebinop Oadd
                                              (Etempvar _t'29 (tptr tuchar))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuchar))))
                                        (Sassign
                                          (Ederef
                                            (Etempvar _t'29 (tptr tuchar))
                                            tuchar) (Etempvar _expval tint))))))))
                            (Sifthenelse (Ebinop Ole (Etempvar _expval tint)
                                           (Econst_int (Int.repr 127) tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'30
                                      (Etempvar _ptr (tptr tuchar)))
                                    (Sset _ptr
                                      (Ebinop Oadd
                                        (Etempvar _t'30 (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar))))
                                  (Sassign
                                    (Ederef (Etempvar _t'30 (tptr tuchar))
                                      tuchar)
                                    (Ebinop Oor (Etempvar _bmsign tuint)
                                      (Econst_int (Int.repr 0) tint) tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'31
                                      (Etempvar _ptr (tptr tuchar)))
                                    (Sset _ptr
                                      (Ebinop Oadd
                                        (Etempvar _t'31 (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar))))
                                  (Sassign
                                    (Ederef (Etempvar _t'31 (tptr tuchar))
                                      tuchar) (Etempvar _expval tint))))
                              (Sifthenelse (Ebinop Ole
                                             (Etempvar _expval tint)
                                             (Econst_int (Int.repr 32767) tint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'32
                                        (Etempvar _ptr (tptr tuchar)))
                                      (Sset _ptr
                                        (Ebinop Oadd
                                          (Etempvar _t'32 (tptr tuchar))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuchar))))
                                    (Sassign
                                      (Ederef (Etempvar _t'32 (tptr tuchar))
                                        tuchar)
                                      (Ebinop Oor (Etempvar _bmsign tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'33
                                          (Etempvar _ptr (tptr tuchar)))
                                        (Sset _ptr
                                          (Ebinop Oadd
                                            (Etempvar _t'33 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t'33 (tptr tuchar))
                                          tuchar)
                                        (Ebinop Oshr (Etempvar _expval tint)
                                          (Econst_int (Int.repr 8) tint)
                                          tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'34
                                          (Etempvar _ptr (tptr tuchar)))
                                        (Sset _ptr
                                          (Ebinop Oadd
                                            (Etempvar _t'34 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t'34 (tptr tuchar))
                                          tuchar) (Etempvar _expval tint)))))
                                (Ssequence
                                  (Sifthenelse (Ebinop Ole
                                                 (Etempvar _expval tint)
                                                 (Econst_int (Int.repr 8388607) tint)
                                                 tint)
                                    Sskip
                                    (Scall None
                                      (Evar ___assert_fail (Tfunction
                                                             (Tcons
                                                               (tptr tschar)
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 (Tcons tuint
                                                                   (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))
                                                             tvoid
                                                             cc_default))
                                      ((Evar ___stringlit_13 (tarray tschar 19)) ::
                                       (Evar ___stringlit_9 (tarray tschar 7)) ::
                                       (Econst_int (Int.repr 805) tint) ::
                                       (Evar ___func____1 (tarray tschar 16)) ::
                                       nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'35
                                          (Etempvar _ptr (tptr tuchar)))
                                        (Sset _ptr
                                          (Ebinop Oadd
                                            (Etempvar _t'35 (tptr tuchar))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuchar))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t'35 (tptr tuchar))
                                          tuchar)
                                        (Ebinop Oor (Etempvar _bmsign tuint)
                                          (Econst_int (Int.repr 2) tint)
                                          tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'36
                                            (Etempvar _ptr (tptr tuchar)))
                                          (Sset _ptr
                                            (Ebinop Oadd
                                              (Etempvar _t'36 (tptr tuchar))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuchar))))
                                        (Sassign
                                          (Ederef
                                            (Etempvar _t'36 (tptr tuchar))
                                            tuchar)
                                          (Ebinop Oshr
                                            (Etempvar _expval tint)
                                            (Econst_int (Int.repr 16) tint)
                                            tint)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'37
                                              (Etempvar _ptr (tptr tuchar)))
                                            (Sset _ptr
                                              (Ebinop Oadd
                                                (Etempvar _t'37 (tptr tuchar))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuchar))))
                                          (Sassign
                                            (Ederef
                                              (Etempvar _t'37 (tptr tuchar))
                                              tuchar)
                                            (Ebinop Oshr
                                              (Etempvar _expval tint)
                                              (Econst_int (Int.repr 8) tint)
                                              tint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'38
                                              (Etempvar _ptr (tptr tuchar)))
                                            (Sset _ptr
                                              (Ebinop Oadd
                                                (Etempvar _t'38 (tptr tuchar))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuchar))))
                                          (Sassign
                                            (Ederef
                                              (Etempvar _t'38 (tptr tuchar))
                                              tuchar)
                                            (Etempvar _expval tint))))))))))
                          (Ssequence
                            (Sset _buflen
                              (Ecast
                                (Ebinop Oadd
                                  (Ebinop Osub
                                    (Etempvar _mstop (tptr tuchar))
                                    (Evar _dscr (tarray tuchar 8)) tlong)
                                  (Econst_int (Int.repr 1) tint) tlong)
                                tuint))
                            (Ssequence
                              (Scall None
                                (Evar _memcpy (Tfunction
                                                (Tcons (tptr tvoid)
                                                  (Tcons (tptr tvoid)
                                                    (Tcons tulong Tnil)))
                                                (tptr tvoid) cc_default))
                                ((Etempvar _ptr (tptr tuchar)) ::
                                 (Evar _dscr (tarray tuchar 8)) ::
                                 (Etempvar _buflen tuint) :: nil))
                              (Ssequence
                                (Sset _ptr
                                  (Ebinop Oadd (Etempvar _ptr (tptr tuchar))
                                    (Etempvar _buflen tuint) (tptr tuchar)))
                                (Ssequence
                                  (Sset _buflen
                                    (Ecast
                                      (Ebinop Osub
                                        (Etempvar _ptr (tptr tuchar))
                                        (Evar _buf (tarray tuchar 16)) tlong)
                                      tuint))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'39)
                                        (Evar _malloc (Tfunction
                                                        (Tcons tulong Tnil)
                                                        (tptr tvoid)
                                                        cc_default))
                                        ((Ebinop Oadd
                                           (Etempvar _buflen tuint)
                                           (Econst_int (Int.repr 1) tint)
                                           tuint) :: nil))
                                      (Sset _ptr
                                        (Ecast (Etempvar _t'39 (tptr tvoid))
                                          (tptr tuchar))))
                                    (Ssequence
                                      (Sifthenelse (Eunop Onotbool
                                                     (Etempvar _ptr (tptr tuchar))
                                                     tint)
                                        (Sreturn (Some (Eunop Oneg
                                                         (Econst_int (Int.repr 1) tint)
                                                         tint)))
                                        Sskip)
                                      (Ssequence
                                        (Scall None
                                          (Evar _memcpy (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            (Tcons
                                                              (tptr tvoid)
                                                              (Tcons tulong
                                                                Tnil)))
                                                          (tptr tvoid)
                                                          cc_default))
                                          ((Etempvar _ptr (tptr tuchar)) ::
                                           (Evar _buf (tarray tuchar 16)) ::
                                           (Etempvar _buflen tuint) :: nil))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _buf (tarray tuchar 16))
                                                (Etempvar _buflen tuint)
                                                (tptr tuchar)) tuchar)
                                            (Econst_int (Int.repr 0) tint))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'40
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                  _buf (tptr tuchar)))
                                              (Sifthenelse (Etempvar _t'40 (tptr tuchar))
                                                (Ssequence
                                                  (Sset _t'41
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                                        (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                      _buf (tptr tuchar)))
                                                  (Scall None
                                                    (Evar _free (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Etempvar _t'41 (tptr tuchar)) ::
                                                     nil)))
                                                Sskip))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                  _buf (tptr tuchar))
                                                (Etempvar _ptr (tptr tuchar)))
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                                      (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                    _size tulong)
                                                  (Etempvar _buflen tuint))
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))
|}.

Definition f_asn_double2float := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_d, tdouble) :: (_outcome, (tptr tfloat)) :: nil);
  fn_vars := nil;
  fn_temps := ((_f, tfloat) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _f (Ecast (Etempvar _d tdouble) tfloat))
  (Ssequence
    (Sassign (Ederef (Etempvar _outcome (tptr tfloat)) tfloat)
      (Etempvar _f tfloat))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                       (Esizeof tfloat tulong) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar ___finitef (Tfunction (Tcons tfloat Tnil) tint
                                 cc_default)) ((Etempvar _d tdouble) :: nil))
            (Sset _t'1 (Ecast (Etempvar _t'2 tint) tint)))
          (Sifthenelse (Ebinop Oeq (Esizeof tdouble tulong)
                         (Esizeof tdouble tulong) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar ___finite (Tfunction (Tcons tdouble Tnil) tint
                                    cc_default))
                  ((Etempvar _d tdouble) :: nil))
                (Sset _t'3 (Ecast (Etempvar _t'4 tint) tint)))
              (Sset _t'1 (Ecast (Etempvar _t'3 tint) tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar ___finitel (Tfunction (Tcons tdouble Tnil) tint
                                     cc_default))
                  ((Etempvar _d tdouble) :: nil))
                (Sset _t'3 (Ecast (Etempvar _t'5 tint) tint)))
              (Sset _t'1 (Ecast (Etempvar _t'3 tint) tint)))))
        (Sifthenelse (Ebinop Oeq (Esizeof tfloat tulong)
                       (Esizeof tfloat tulong) tint)
          (Ssequence
            (Scall (Some _t'7)
              (Evar ___finitef (Tfunction (Tcons tfloat Tnil) tint
                                 cc_default)) ((Etempvar _f tfloat) :: nil))
            (Sset _t'6 (Ecast (Etempvar _t'7 tint) tint)))
          (Sifthenelse (Ebinop Oeq (Esizeof tfloat tulong)
                         (Esizeof tdouble tulong) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar ___finite (Tfunction (Tcons tdouble Tnil) tint
                                    cc_default))
                  ((Etempvar _f tfloat) :: nil))
                (Sset _t'8 (Ecast (Etempvar _t'9 tint) tint)))
              (Sset _t'6 (Ecast (Etempvar _t'8 tint) tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'10)
                  (Evar ___finitel (Tfunction (Tcons tdouble Tnil) tint
                                     cc_default))
                  ((Etempvar _f tfloat) :: nil))
                (Sset _t'8 (Ecast (Etempvar _t'10 tint) tint)))
              (Sset _t'6 (Ecast (Etempvar _t'8 tint) tint))))))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint) (Etempvar _t'6 tint)
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))))))
|}.

Definition f_REAL_encode_oer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_oer_constraints_s noattr))) ::
                (_sptr, (tptr tvoid)) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_er, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error__2, (Tstruct _asn_enc_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_len_len, tlong) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tlong) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'12, (tptr tuchar)) :: (_t'11, tuint) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, (tptr tuchar)) ::
               (_t'7, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Etempvar _sptr (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                       tint)
          (Sset _t'1 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef
                  (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                (tptr tuchar)))
            (Sset _t'1
              (Ecast (Eunop Onotbool (Etempvar _t'12 (tptr tuchar)) tint)
                tbool))))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sset _t'2 (Econst_int (Int.repr 1) tint))
          (Sset _t'2
            (Ecast
              (Eunop Onotbool
                (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                tint) tbool))))
      (Sifthenelse (Etempvar _t'2 tint)
        (Sloop
          (Ssequence
            (Sassign
              (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                _encoded tlong)
              (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Sassign
                (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                  _failed_type
                  (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
              (Ssequence
                (Sassign
                  (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                    _structure_ptr (tptr tvoid))
                  (Etempvar _sptr (tptr tvoid)))
                (Ssequence
                  (Sloop Sskip Sbreak)
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                        (Tstruct _asn_enc_rval_s noattr))
                      (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr)))
                    (Sreturn None))))))
          Sbreak)
        Sskip))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _constraints (tptr (Tstruct _asn_oer_constraints_s noattr)))
                     tint)
        (Sset _constraints
          (Efield
            (Efield
              (Ederef
                (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                (Tstruct _asn_TYPE_descriptor_s noattr))
              _encoding_constraints
              (Tstruct _asn_encoding_constraints_s noattr)) _oer_constraints
            (tptr (Tstruct _asn_oer_constraints_s noattr))))
        Sskip)
      (Ssequence
        (Ssequence
          (Sifthenelse (Etempvar _constraints (tptr (Tstruct _asn_oer_constraints_s noattr)))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _constraints (tptr (Tstruct _asn_oer_constraints_s noattr)))
                      (Tstruct _asn_oer_constraints_s noattr)) _value
                    (Tstruct _asn_oer_constraint_number_s noattr)) _width
                  tuint))
              (Sset _t'3
                (Ecast
                  (Ebinop One (Etempvar _t'11 tuint)
                    (Econst_int (Int.repr 0) tint) tint) tbool)))
            (Sset _t'3 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'3 tint)
            (Sloop
              (Ssequence
                (Sassign
                  (Efield
                    (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                    _encoded tlong)
                  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                      _failed_type
                      (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                    (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                        _structure_ptr (tptr tvoid))
                      (Etempvar _sptr (tptr tvoid)))
                    (Ssequence
                      (Sloop Sskip Sbreak)
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                            (Tstruct _asn_enc_rval_s noattr))
                          (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr)))
                        (Sreturn None))))))
              Sbreak)
            Sskip))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef
                    (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                    (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _size tulong))
              (Scall (Some _t'4)
                (Evar _oer_serialize_length (Tfunction
                                              (Tcons tulong
                                                (Tcons
                                                  (tptr (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            (Tcons tulong
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil))) tint
                                                          cc_default))
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tlong cc_default))
                ((Etempvar _t'10 tulong) ::
                 (Etempvar _cb (tptr (Tfunction
                                       (Tcons (tptr tvoid)
                                         (Tcons tulong
                                           (Tcons (tptr tvoid) Tnil))) tint
                                       cc_default))) ::
                 (Etempvar _app_key (tptr tvoid)) :: nil)))
            (Sset _len_len (Etempvar _t'4 tlong)))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _len_len tlong)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _t'5 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef
                        (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                        (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _buf
                      (tptr tuchar)))
                  (Ssequence
                    (Sset _t'9
                      (Efield
                        (Ederef
                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _size
                        tulong))
                    (Scall (Some _t'6)
                      (Etempvar _cb (tptr (Tfunction
                                            (Tcons (tptr tvoid)
                                              (Tcons tulong
                                                (Tcons (tptr tvoid) Tnil)))
                                            tint cc_default)))
                      ((Etempvar _t'8 (tptr tuchar)) ::
                       (Etempvar _t'9 tulong) ::
                       (Etempvar _app_key (tptr tvoid)) :: nil))))
                (Sset _t'5
                  (Ecast
                    (Ebinop Olt (Etempvar _t'6 tint)
                      (Econst_int (Int.repr 0) tint) tint) tbool))))
            (Sifthenelse (Etempvar _t'5 tint)
              (Sloop
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error__2 (Tstruct _asn_enc_rval_s noattr))
                      _encoded tlong)
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__2 (Tstruct _asn_enc_rval_s noattr))
                        _failed_type
                        (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                      (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error__2 (Tstruct _asn_enc_rval_s noattr))
                          _structure_ptr (tptr tvoid))
                        (Etempvar _sptr (tptr tvoid)))
                      (Ssequence
                        (Sloop Sskip Sbreak)
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                              (Tstruct _asn_enc_rval_s noattr))
                            (Evar _tmp_error__2 (Tstruct _asn_enc_rval_s noattr)))
                          (Sreturn None))))))
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                        (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _size
                      tulong))
                  (Sassign
                    (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                      _encoded tlong)
                    (Ebinop Oadd (Etempvar _len_len tlong)
                      (Etempvar _t'7 tulong) tulong)))
                (Sloop
                  (Ssequence
                    (Sassign
                      (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                        _structure_ptr (tptr tvoid))
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                          _failed_type
                          (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                        (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                            (Tstruct _asn_enc_rval_s noattr))
                          (Evar _er (Tstruct _asn_enc_rval_s noattr)))
                        (Sreturn None))))
                  Sbreak)))))))))
|}.

Definition f_REAL_decode_oer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_oer_constraints_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) :: (_ptr, (tptr tvoid)) ::
                (_size, tulong) :: nil);
  fn_vars := ((_ok, (Tstruct _asn_dec_rval_s noattr)) ::
              (_real_body_len, tulong) ::
              (_tmp_error, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__2, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__3, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__4, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__5, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_buf, (tptr tuchar)) :: (_len_len, tlong) ::
               (_t'6, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tlong) :: (_t'1, tint) ::
               (_t'15, tuint) :: (_t'14, tulong) :: (_t'13, tulong) ::
               (_t'12, (tptr tvoid)) :: (_t'11, (tptr tuchar)) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, tulong) ::
               (_t'7, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _ok (Tstruct _asn_dec_rval_s noattr)) _code tint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield (Evar _ok (Tstruct _asn_dec_rval_s noattr)) _consumed tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _constraints (tptr (Tstruct _asn_oer_constraints_s noattr)))
                     tint)
        (Sset _constraints
          (Efield
            (Efield
              (Ederef
                (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                (Tstruct _asn_TYPE_descriptor_s noattr))
              _encoding_constraints
              (Tstruct _asn_encoding_constraints_s noattr)) _oer_constraints
            (tptr (Tstruct _asn_oer_constraints_s noattr))))
        Sskip)
      (Ssequence
        (Ssequence
          (Sifthenelse (Etempvar _constraints (tptr (Tstruct _asn_oer_constraints_s noattr)))
            (Ssequence
              (Sset _t'15
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _constraints (tptr (Tstruct _asn_oer_constraints_s noattr)))
                      (Tstruct _asn_oer_constraints_s noattr)) _value
                    (Tstruct _asn_oer_constraint_number_s noattr)) _width
                  tuint))
              (Sset _t'1
                (Ecast
                  (Ebinop One (Etempvar _t'15 tuint)
                    (Econst_int (Int.repr 0) tint) tint) tbool)))
            (Sset _t'1 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'1 tint)
            (Sloop
              (Ssequence
                (Sassign
                  (Efield (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr))
                    _code tint) (Econst_int (Int.repr 2) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr))
                      _consumed tulong) (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sloop Sskip Sbreak)
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                          (Tstruct _asn_dec_rval_s noattr))
                        (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr)))
                      (Sreturn None)))))
              Sbreak)
            Sskip))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _oer_fetch_length (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tulong
                                            (Tcons (tptr tulong) Tnil)))
                                        tlong cc_default))
              ((Etempvar _ptr (tptr tvoid)) :: (Etempvar _size tulong) ::
               (Eaddrof (Evar _real_body_len tulong) (tptr tulong)) :: nil))
            (Sset _len_len (Etempvar _t'2 tlong)))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _len_len tlong)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sloop
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr))
                      _code tint) (Econst_int (Int.repr 2) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr))
                        _consumed tulong) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sloop Sskip Sbreak)
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                            (Tstruct _asn_dec_rval_s noattr))
                          (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr)))
                        (Sreturn None)))))
                Sbreak)
              Sskip)
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _len_len tlong)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sloop
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__2 (Tstruct _asn_dec_rval_s noattr))
                        _code tint) (Econst_int (Int.repr 1) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error__2 (Tstruct _asn_dec_rval_s noattr))
                          _consumed tulong) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                            (Tstruct _asn_dec_rval_s noattr))
                          (Evar _tmp_error__2 (Tstruct _asn_dec_rval_s noattr)))
                        (Sreturn None))))
                  Sbreak)
                Sskip)
              (Ssequence
                (Sset _ptr
                  (Ebinop Oadd
                    (Ecast (Etempvar _ptr (tptr tvoid)) (tptr tschar))
                    (Etempvar _len_len tlong) (tptr tschar)))
                (Ssequence
                  (Sset _size
                    (Ebinop Osub (Etempvar _size tulong)
                      (Etempvar _len_len tlong) tulong))
                  (Ssequence
                    (Ssequence
                      (Sset _t'14 (Evar _real_body_len tulong))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'14 tulong)
                                     (Etempvar _size tulong) tint)
                        (Sloop
                          (Ssequence
                            (Sassign
                              (Efield
                                (Evar _tmp_error__3 (Tstruct _asn_dec_rval_s noattr))
                                _code tint) (Econst_int (Int.repr 1) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Evar _tmp_error__3 (Tstruct _asn_dec_rval_s noattr))
                                  _consumed tulong)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                                    (Tstruct _asn_dec_rval_s noattr))
                                  (Evar _tmp_error__3 (Tstruct _asn_dec_rval_s noattr)))
                                (Sreturn None))))
                          Sbreak)
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'13 (Evar _real_body_len tulong))
                          (Scall (Some _t'3)
                            (Evar _calloc (Tfunction
                                            (Tcons tulong
                                              (Tcons tulong Tnil))
                                            (tptr tvoid) cc_default))
                            ((Econst_int (Int.repr 1) tint) ::
                             (Ebinop Oadd (Etempvar _t'13 tulong)
                               (Econst_int (Int.repr 1) tint) tulong) :: nil)))
                        (Sset _buf (Etempvar _t'3 (tptr tvoid))))
                      (Ssequence
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _buf (tptr tuchar)) tint)
                          (Sloop
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Evar _tmp_error__4 (Tstruct _asn_dec_rval_s noattr))
                                  _code tint) (Econst_int (Int.repr 2) tint))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Evar _tmp_error__4 (Tstruct _asn_dec_rval_s noattr))
                                    _consumed tulong)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sloop Sskip Sbreak)
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                                        (Tstruct _asn_dec_rval_s noattr))
                                      (Evar _tmp_error__4 (Tstruct _asn_dec_rval_s noattr)))
                                    (Sreturn None)))))
                            Sbreak)
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'12
                                  (Ederef
                                    (Etempvar _sptr (tptr (tptr tvoid)))
                                    (tptr tvoid)))
                                (Sset _t'6
                                  (Ecast (Etempvar _t'12 (tptr tvoid))
                                    (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))))
                              (Sset _st
                                (Etempvar _t'6 (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))))
                            (Sifthenelse (Eunop Onotbool
                                           (Etempvar _t'6 (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'4)
                                        (Evar _calloc (Tfunction
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil))
                                                        (tptr tvoid)
                                                        cc_default))
                                        ((Econst_int (Int.repr 1) tint) ::
                                         (Esizeof (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) tulong) ::
                                         nil))
                                      (Sset _t'5
                                        (Ecast (Etempvar _t'4 (tptr tvoid))
                                          (tptr tvoid))))
                                    (Sassign
                                      (Ederef
                                        (Etempvar _sptr (tptr (tptr tvoid)))
                                        (tptr tvoid))
                                      (Etempvar _t'5 (tptr tvoid))))
                                  (Sset _st (Etempvar _t'5 (tptr tvoid))))
                                (Sifthenelse (Eunop Onotbool
                                               (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                               tint)
                                  (Ssequence
                                    (Scall None
                                      (Evar _free (Tfunction
                                                    (Tcons (tptr tvoid) Tnil)
                                                    tvoid cc_default))
                                      ((Etempvar _buf (tptr tuchar)) :: nil))
                                    (Sloop
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Evar _tmp_error__5 (Tstruct _asn_dec_rval_s noattr))
                                            _code tint)
                                          (Econst_int (Int.repr 2) tint))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Evar _tmp_error__5 (Tstruct _asn_dec_rval_s noattr))
                                              _consumed tulong)
                                            (Econst_int (Int.repr 0) tint))
                                          (Ssequence
                                            (Sloop Sskip Sbreak)
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                                                  (Tstruct _asn_dec_rval_s noattr))
                                                (Evar _tmp_error__5 (Tstruct _asn_dec_rval_s noattr)))
                                              (Sreturn None)))))
                                      Sbreak))
                                  Sskip))
                              (Ssequence
                                (Sset _t'11
                                  (Efield
                                    (Ederef
                                      (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                      (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                    _buf (tptr tuchar)))
                                (Scall None
                                  (Evar _free (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                                  ((Etempvar _t'11 (tptr tuchar)) :: nil)))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'10 (Evar _real_body_len tulong))
                              (Scall None
                                (Evar _memcpy (Tfunction
                                                (Tcons (tptr tvoid)
                                                  (Tcons (tptr tvoid)
                                                    (Tcons tulong Tnil)))
                                                (tptr tvoid) cc_default))
                                ((Etempvar _buf (tptr tuchar)) ::
                                 (Etempvar _ptr (tptr tvoid)) ::
                                 (Etempvar _t'10 tulong) :: nil)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'9 (Evar _real_body_len tulong))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _buf (tptr tuchar))
                                      (Etempvar _t'9 tulong) (tptr tuchar))
                                    tuchar) (Econst_int (Int.repr 0) tint)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                      (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                    _buf (tptr tuchar))
                                  (Etempvar _buf (tptr tuchar)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'8 (Evar _real_body_len tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                          (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                        _size tulong) (Etempvar _t'8 tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'7
                                        (Evar _real_body_len tulong))
                                      (Sassign
                                        (Efield
                                          (Evar _ok (Tstruct _asn_dec_rval_s noattr))
                                          _consumed tulong)
                                        (Ebinop Oadd
                                          (Etempvar _len_len tlong)
                                          (Etempvar _t'7 tulong) tulong)))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                                          (Tstruct _asn_dec_rval_s noattr))
                                        (Evar _ok (Tstruct _asn_dec_rval_s noattr)))
                                      (Sreturn None))))))))))))))))))))
|}.

Definition f_REAL_decode_uper := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_per_constraints_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) ::
                (_pd, (tptr (Tstruct _asn_bit_data_s noattr))) :: nil);
  fn_vars := ((__res__1, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _OCTET_STRING_decode_uper (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _asn_dec_rval_s noattr))
                                          (Tcons
                                            (tptr (Tstruct _asn_codec_ctx_s noattr))
                                            (Tcons
                                              (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                              (Tcons
                                                (tptr (Tstruct _asn_per_constraints_s noattr))
                                                (Tcons (tptr (tptr tvoid))
                                                  (Tcons
                                                    (tptr (Tstruct _asn_bit_data_s noattr))
                                                    Tnil)))))) tvoid
                                        {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
      ((Eaddrof (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))
         (tptr (Tstruct _asn_dec_rval_s noattr))) ::
       (Etempvar _opt_codec_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
       (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
       (Econst_int (Int.repr 0) tint) ::
       (Etempvar _sptr (tptr (tptr tvoid))) ::
       (Etempvar _pd (tptr (Tstruct _asn_bit_data_s noattr))) :: nil))
    (Sassign
      (Ederef (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
        (Tstruct _asn_dec_rval_s noattr))
      (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))))
  (Sreturn None))
|}.

Definition f_REAL_encode_uper := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_per_constraints_s noattr))) ::
                (_sptr, (tptr tvoid)) ::
                (_po, (tptr (Tstruct _asn_bit_outp_s noattr))) :: nil);
  fn_vars := ((__res__1, (Tstruct _asn_enc_rval_s noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _OCTET_STRING_encode_uper (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _asn_enc_rval_s noattr))
                                          (Tcons
                                            (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                            (Tcons
                                              (tptr (Tstruct _asn_per_constraints_s noattr))
                                              (Tcons (tptr tvoid)
                                                (Tcons
                                                  (tptr (Tstruct _asn_bit_outp_s noattr))
                                                  Tnil))))) tvoid
                                        {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
      ((Eaddrof (Evar __res__1 (Tstruct _asn_enc_rval_s noattr))
         (tptr (Tstruct _asn_enc_rval_s noattr))) ::
       (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
       (Econst_int (Int.repr 0) tint) :: (Etempvar _sptr (tptr tvoid)) ::
       (Etempvar _po (tptr (Tstruct _asn_bit_outp_s noattr))) :: nil))
    (Sassign
      (Ederef (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
        (Tstruct _asn_enc_rval_s noattr))
      (Evar __res__1 (Tstruct _asn_enc_rval_s noattr))))
  (Sreturn None))
|}.

Definition v_values := {|
  gvar_info := (tarray tdouble 29);
  gvar_init := (Init_float64 (Float.of_bits (Int64.repr 0)) ::
                Init_float64 (Float.of_bits (Int64.repr (-9223372036854775808))) ::
                Init_float64 (Float.of_bits (Int64.repr (-4616189618054758400))) ::
                Init_float64 (Float.of_bits (Int64.repr 4607182418800017408)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4610068591539890327))) ::
                Init_float64 (Float.of_bits (Int64.repr 4613303445314885481)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4609118966639786721))) ::
                Init_float64 (Float.of_bits (Int64.repr 4614253070214989087)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4609115380302729960))) ::
                Init_float64 (Float.of_bits (Int64.repr 4614256656552045848)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4580196005407883264))) ::
                Init_float64 (Float.of_bits (Int64.repr 4643176031446892544)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4386506037058863104))) ::
                Init_float64 (Float.of_bits (Int64.repr 4836865999795912704)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4382002437431492608))) ::
                Init_float64 (Float.of_bits (Int64.repr 4841369599423283200)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4165829655317708800))) ::
                Init_float64 (Float.of_bits (Int64.repr 5057542381537067008)) ::
                Init_float64 (Float.of_bits (Int64.repr (-5183643171103440896))) ::
                Init_float64 (Float.of_bits (Int64.repr 4039728865751334912)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4039728866288205824))) ::
                Init_float64 (Float.of_bits (Int64.repr 5183643170566569984)) ::
                Init_float64 (Float.of_bits (Int64.repr (-9218868437227405312))) ::
                Init_float64 (Float.of_bits (Int64.repr 4503599627370496)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4503599627370497))) ::
                Init_float64 (Float.of_bits (Int64.repr 9218868437227405311)) ::
                Init_float64 (Float.of_bits (Int64.repr 9218868437227405312)) ::
                Init_float64 (Float.of_bits (Int64.repr (-4503599627370496))) ::
                Init_float64 (Float.of_bits (Int64.repr (-2251799813685248))) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_REAL_random_fill := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_random_fill_result_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) ::
                (_constraints,
                 (tptr (Tstruct _asn_encoding_constraints_s noattr))) ::
                (_max_length, tulong) :: nil);
  fn_vars := ((_result_ok, (Tstruct _asn_random_fill_result_s noattr)) ::
              (_result_failed, (Tstruct _asn_random_fill_result_s noattr)) ::
              (_result_skipped, (Tstruct _asn_random_fill_result_s noattr)) ::
              nil);
  fn_temps := ((_st, (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
               (_d, tdouble) :: (_t'4, tint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tlong) ::
               (_t'11, (tptr tvoid)) ::
               (_t'10,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                          (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid
                        cc_default))) ::
               (_t'9, (tptr (Tstruct _asn_TYPE_operation_s noattr))) ::
               (_t'8,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                          (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid
                        cc_default))) ::
               (_t'7, (tptr (Tstruct _asn_TYPE_operation_s noattr))) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr))
      _code tint) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr))
        _length tulong) (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sassign
        (Efield
          (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr))
          _code tint) (Econst_int (Int.repr (-1)) tint))
      (Ssequence
        (Sassign
          (Efield
            (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr))
            _length tulong) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Evar _result_skipped (Tstruct _asn_random_fill_result_s noattr))
              _code tint) (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sassign
              (Efield
                (Evar _result_skipped (Tstruct _asn_random_fill_result_s noattr))
                _length tulong) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _max_length tulong)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                      (Tstruct _asn_random_fill_result_s noattr))
                    (Evar _result_skipped (Tstruct _asn_random_fill_result_s noattr)))
                  (Sreturn None))
                Sskip)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _asn_random_between (Tfunction
                                                (Tcons tlong
                                                  (Tcons tlong Tnil)) tlong
                                                cc_default))
                    ((Econst_int (Int.repr 0) tint) ::
                     (Ebinop Osub
                       (Ebinop Odiv (Esizeof (tarray tdouble 29) tulong)
                         (Esizeof tdouble tulong) tulong)
                       (Econst_int (Int.repr 1) tint) tulong) :: nil))
                  (Sset _d
                    (Ederef
                      (Ebinop Oadd (Evar _values (tarray tdouble 29))
                        (Etempvar _t'1 tlong) (tptr tdouble)) tdouble)))
                (Ssequence
                  (Ssequence
                    (Sset _t'11
                      (Ederef (Etempvar _sptr (tptr (tptr tvoid)))
                        (tptr tvoid)))
                    (Sifthenelse (Etempvar _t'11 (tptr tvoid))
                      (Sset _st
                        (Ederef (Etempvar _sptr (tptr (tptr tvoid)))
                          (tptr tvoid)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'2)
                                (Evar _calloc (Tfunction
                                                (Tcons tulong
                                                  (Tcons tulong Tnil))
                                                (tptr tvoid) cc_default))
                                ((Econst_int (Int.repr 1) tint) ::
                                 (Esizeof (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) tulong) ::
                                 nil))
                              (Sset _t'3
                                (Ecast (Etempvar _t'2 (tptr tvoid))
                                  (tptr tvoid))))
                            (Sassign
                              (Ederef (Etempvar _sptr (tptr (tptr tvoid)))
                                (tptr tvoid)) (Etempvar _t'3 (tptr tvoid))))
                          (Sset _st
                            (Ecast (Etempvar _t'3 (tptr tvoid))
                              (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                       tint)
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                                (Tstruct _asn_random_fill_result_s noattr))
                              (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr)))
                            (Sreturn None))
                          Sskip))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _asn_double2REAL (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                                                   (Tcons tdouble Tnil)) tint
                                                 cc_default))
                        ((Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                         (Etempvar _d tdouble) :: nil))
                      (Sifthenelse (Etempvar _t'4 tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'6
                              (Ederef (Etempvar _sptr (tptr (tptr tvoid)))
                                (tptr tvoid)))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                                           (Etempvar _t'6 (tptr tvoid)) tint)
                              (Ssequence
                                (Sset _t'9
                                  (Efield
                                    (Ederef
                                      (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                                      (Tstruct _asn_TYPE_descriptor_s noattr))
                                    _op
                                    (tptr (Tstruct _asn_TYPE_operation_s noattr))))
                                (Ssequence
                                  (Sset _t'10
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'9 (tptr (Tstruct _asn_TYPE_operation_s noattr)))
                                        (Tstruct _asn_TYPE_operation_s noattr))
                                      _free_struct
                                      (tptr (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                                (Tcons (tptr tvoid)
                                                  (Tcons tint Tnil))) tvoid
                                              cc_default))))
                                  (Scall None
                                    (Etempvar _t'10 (tptr (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                                              (Tcons
                                                                (tptr tvoid)
                                                                (Tcons tint
                                                                  Tnil)))
                                                            tvoid cc_default)))
                                    ((Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                                     (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                                     (Econst_int (Int.repr 2) tint) :: nil))))
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                                      (Tstruct _asn_TYPE_descriptor_s noattr))
                                    _op
                                    (tptr (Tstruct _asn_TYPE_operation_s noattr))))
                                (Ssequence
                                  (Sset _t'8
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'7 (tptr (Tstruct _asn_TYPE_operation_s noattr)))
                                        (Tstruct _asn_TYPE_operation_s noattr))
                                      _free_struct
                                      (tptr (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                                (Tcons (tptr tvoid)
                                                  (Tcons tint Tnil))) tvoid
                                              cc_default))))
                                  (Scall None
                                    (Etempvar _t'8 (tptr (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                                             (Tcons
                                                               (tptr tvoid)
                                                               (Tcons tint
                                                                 Tnil)))
                                                           tvoid cc_default)))
                                    ((Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                                     (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))) ::
                                     (Econst_int (Int.repr 0) tint) :: nil))))))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                                (Tstruct _asn_random_fill_result_s noattr))
                              (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr)))
                            (Sreturn None)))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Sset _t'5
                          (Efield
                            (Ederef
                              (Etempvar _st (tptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)))
                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) _size
                            tulong))
                        (Sassign
                          (Efield
                            (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr))
                            _length tulong) (Etempvar _t'5 tulong)))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                            (Tstruct _asn_random_fill_result_s noattr))
                          (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr)))
                        (Sreturn None)))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _asn_codec_ctx_s Struct ((_max_stack_size, tulong) :: nil) noattr ::
 Composite _asn_enc_rval_s Struct
   ((_encoded, tlong) ::
    (_failed_type, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_structure_ptr, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_dec_rval_s Struct
   ((_code, tint) :: (_consumed, tulong) :: nil)
   noattr ::
 Composite _asn_bit_data_s Struct
   ((_buffer, (tptr tuchar)) :: (_nboff, tulong) :: (_nbits, tulong) ::
    (_moved, tulong) ::
    (_refill,
     (tptr (Tfunction (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil)
             tint cc_default))) :: (_refill_key, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_bit_outp_s Struct
   ((_buffer, (tptr tuchar)) :: (_nboff, tulong) :: (_nbits, tulong) ::
    (_tmpspace, (tarray tuchar 32)) ::
    (_output,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons tulong (Tcons (tptr tvoid) Tnil)))
             tint cc_default))) :: (_op_key, (tptr tvoid)) ::
    (_flushed_bytes, tulong) :: nil)
   noattr ::
 Composite _asn_per_constraint_s Struct
   ((_flags, tint) :: (_range_bits, tint) :: (_effective_bits, tint) ::
    (_lower_bound, tlong) :: (_upper_bound, tlong) :: nil)
   noattr ::
 Composite _asn_per_constraints_s Struct
   ((_value, (Tstruct _asn_per_constraint_s noattr)) ::
    (_size, (Tstruct _asn_per_constraint_s noattr)) ::
    (_value2code, (tptr (Tfunction (Tcons tuint Tnil) tint cc_default))) ::
    (_code2value, (tptr (Tfunction (Tcons tuint Tnil) tint cc_default))) ::
    nil)
   noattr ::
 Composite _asn_random_fill_result_s Struct
   ((_code, tint) :: (_length, tulong) :: nil)
   noattr ::
 Composite _asn_oer_constraint_number_s Struct
   ((_width, tuint) :: (_positive, tuint) :: nil)
   noattr ::
 Composite _asn_oer_constraints_s Struct
   ((_value, (Tstruct _asn_oer_constraint_number_s noattr)) ::
    (_size, tlong) :: nil)
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
                               (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
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
                     (Tcons (tptr tvoid) (Tcons tulong (Tcons tint Tnil)))))))
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
                                   (Tcons tulong (Tcons (tptr tvoid) Tnil)))
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
                       (Tcons (tptr tvoid) (Tcons tulong Tnil))))))) tvoid
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
                                   (Tcons tulong (Tcons (tptr tvoid) Tnil)))
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
                       (Tcons (tptr tvoid) (Tcons tulong Tnil))))))) tvoid
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
                                 (Tcons tulong (Tcons (tptr tvoid) Tnil)))
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
                     (Tcons tulong Tnil))))) tvoid
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
   noattr ::
 Composite _ASN__PRIMITIVE_TYPE_s Struct
   ((_buf, (tptr tuchar)) :: (_size, tulong) :: nil)
   noattr ::
 Composite _specialRealValue_s Struct
   ((_string, (tptr tschar)) :: (_length, tulong) :: (_dv, tlong) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) None
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tuint
     cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tvoid) (Tcons tulong Tnil)) (tptr tvoid) cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tuint) Tnil) tuint
     cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
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
 (_snprintf,
   Gfun(External (EF_external "snprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) (Tcons tulong (Tcons (tptr tschar) Tnil))) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_strtod,
   Gfun(External (EF_external "strtod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons (tptr tschar) (Tcons (tptr (tptr tschar)) Tnil)) tdouble
     cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_calloc,
   Gfun(External (EF_external "calloc"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memcmp,
   Gfun(External (EF_external "memcmp"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) tint
     cc_default)) ::
 (_memchr,
   Gfun(External (EF_external "memchr"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
     cc_default)) ::
 (_asn_generic_no_constraint,
   Gfun(External (EF_external "asn_generic_no_constraint"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) (Some AST.Tint) cc_default))
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) (Some AST.Tint) cc_default))
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
 (_asn_random_between,
   Gfun(External (EF_external "asn_random_between"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (_oer_fetch_length,
   Gfun(External (EF_external "oer_fetch_length"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tvoid) (Tcons tulong (Tcons (tptr tulong) Tnil))) tlong
     cc_default)) ::
 (_oer_serialize_length,
   Gfun(External (EF_external "oer_serialize_length"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong
       (Tcons
         (tptr (Tfunction
                 (Tcons (tptr tvoid)
                   (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint cc_default))
         (Tcons (tptr tvoid) Tnil))) tlong cc_default)) ::
 (_oer_decode_primitive,
   Gfun(External (EF_external "oer_decode_primitive"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr tvoid) (Tcons tulong Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_oer_encode_primitive,
   Gfun(External (EF_external "oer_encode_primitive"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons
               (tptr (Tfunction
                       (Tcons (tptr tvoid)
                         (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                       cc_default)) (Tcons (tptr tvoid) Tnil)))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_asn_TYPE_outmost_tag,
   Gfun(External (EF_external "asn_TYPE_outmost_tag"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))) tuint
     cc_default)) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     None cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (___finite,
   Gfun(External (EF_external "__finite"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tdouble Tnil) tint cc_default)) ::
 (___isnan,
   Gfun(External (EF_external "__isnan"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tdouble Tnil) tint cc_default)) ::
 (_ldexp,
   Gfun(External (EF_external "ldexp"
                   (mksignature (AST.Tfloat :: AST.Tint :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tint Tnil)) tdouble cc_default)) ::
 (_copysign,
   Gfun(External (EF_external "copysign"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (_ilogb,
   Gfun(External (EF_external "ilogb"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tdouble Tnil) tint cc_default)) ::
 (___finitef,
   Gfun(External (EF_external "__finitef"
                   (mksignature (AST.Tsingle :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tfloat Tnil) tint cc_default)) ::
 (___isnanf,
   Gfun(External (EF_external "__isnanf"
                   (mksignature (AST.Tsingle :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tfloat Tnil) tint cc_default)) ::
 (___finitel,
   Gfun(External (EF_external "__finitel"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tdouble Tnil) tint cc_default)) ::
 (___isnanl,
   Gfun(External (EF_external "__isnanl"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tdouble Tnil) tint cc_default)) ::
 (___errno_location,
   Gfun(External (EF_external "__errno_location"
                   (mksignature nil (Some AST.Tlong) cc_default)) Tnil
     (tptr tint) cc_default)) ::
 (_ASN__PRIMITIVE_TYPE_free,
   Gfun(External (EF_external "ASN__PRIMITIVE_TYPE_free"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid cc_default)) ::
 (_ber_decode_primitive,
   Gfun(External (EF_external "ber_decode_primitive"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tvoid) (Tcons tulong (Tcons tint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_der_encode_primitive,
   Gfun(External (EF_external "der_encode_primitive"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tint ::
                      AST.Tint :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tuint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_xer_decode_primitive,
   Gfun(External (EF_external "xer_decode_primitive"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons tulong
               (Tcons (tptr tschar)
                 (Tcons (tptr tvoid)
                   (Tcons tulong
                     (Tcons
                       (tptr (Tfunction
                               (Tcons
                                 (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                 (Tcons (tptr tvoid)
                                   (Tcons (tptr tvoid) (Tcons tulong Tnil))))
                               tint cc_default)) Tnil))))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_free,
   Gfun(External (EF_external "OCTET_STRING_free"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid cc_default)) ::
 (_OCTET_STRING_print,
   Gfun(External (EF_external "OCTET_STRING_print"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong ::
                      AST.Tlong :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons tint
           (Tcons
             (tptr (Tfunction
                     (Tcons (tptr tvoid)
                       (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                     cc_default)) (Tcons (tptr tvoid) Tnil))))) tint
     cc_default)) ::
 (_OCTET_STRING_print_utf8,
   Gfun(External (EF_external "OCTET_STRING_print_utf8"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong ::
                      AST.Tlong :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons tint
           (Tcons
             (tptr (Tfunction
                     (Tcons (tptr tvoid)
                       (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                     cc_default)) (Tcons (tptr tvoid) Tnil))))) tint
     cc_default)) ::
 (_OCTET_STRING_compare,
   Gfun(External (EF_external "OCTET_STRING_compare"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) tint cc_default)) ::
 (_OCTET_STRING_decode_ber,
   Gfun(External (EF_external "OCTET_STRING_decode_ber"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tvoid) (Tcons tulong (Tcons tint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_encode_der,
   Gfun(External (EF_external "OCTET_STRING_encode_der"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tint ::
                      AST.Tint :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tuint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_decode_xer_hex,
   Gfun(External (EF_external "OCTET_STRING_decode_xer_hex"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tschar) (Tcons (tptr tvoid) (Tcons tulong Tnil)))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_decode_xer_binary,
   Gfun(External (EF_external "OCTET_STRING_decode_xer_binary"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tschar) (Tcons (tptr tvoid) (Tcons tulong Tnil)))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_decode_xer_utf8,
   Gfun(External (EF_external "OCTET_STRING_decode_xer_utf8"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tschar) (Tcons (tptr tvoid) (Tcons tulong Tnil)))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_encode_xer,
   Gfun(External (EF_external "OCTET_STRING_encode_xer"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tint ::
                      AST.Tint :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_encode_xer_utf8,
   Gfun(External (EF_external "OCTET_STRING_encode_xer_utf8"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tint ::
                      AST.Tint :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_decode_oer,
   Gfun(External (EF_external "OCTET_STRING_decode_oer"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr tvoid) (Tcons tulong Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_encode_oer,
   Gfun(External (EF_external "OCTET_STRING_encode_oer"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons
               (tptr (Tfunction
                       (Tcons (tptr tvoid)
                         (Tcons tulong (Tcons (tptr tvoid) Tnil))) tint
                       cc_default)) (Tcons (tptr tvoid) Tnil)))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_decode_uper,
   Gfun(External (EF_external "OCTET_STRING_decode_uper"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_encode_uper,
   Gfun(External (EF_external "OCTET_STRING_encode_uper"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons (tptr (Tstruct _asn_bit_outp_s noattr)) Tnil))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_OCTET_STRING_random_fill,
   Gfun(External (EF_external "OCTET_STRING_random_fill"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_random_fill_result_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (tptr tvoid))
           (Tcons (tptr (Tstruct _asn_encoding_constraints_s noattr))
             (Tcons tulong Tnil))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_asn_DEF_REAL_tags, Gvar v_asn_DEF_REAL_tags) ::
 (_asn_OP_REAL, Gvar v_asn_OP_REAL) ::
 (_asn_DEF_REAL, Gvar v_asn_DEF_REAL) ::
 (_specialRealValue__1, Gvar v_specialRealValue__1) ::
 (___func__, Gvar v___func__) ::
 (_REAL__dump, Gfun(Internal f_REAL__dump)) ::
 (_REAL_print, Gfun(Internal f_REAL_print)) ::
 (_REAL_compare, Gfun(Internal f_REAL_compare)) ::
 (_REAL_encode_xer, Gfun(Internal f_REAL_encode_xer)) ::
 (_REAL__xer_body_decode, Gfun(Internal f_REAL__xer_body_decode)) ::
 (_REAL_decode_xer, Gfun(Internal f_REAL_decode_xer)) ::
 (_asn_REAL2double, Gfun(Internal f_asn_REAL2double)) ::
 (___func____1, Gvar v___func____1) ::
 (_asn_double2REAL, Gfun(Internal f_asn_double2REAL)) ::
 (_asn_double2float, Gfun(Internal f_asn_double2float)) ::
 (_REAL_encode_oer, Gfun(Internal f_REAL_encode_oer)) ::
 (_REAL_decode_oer, Gfun(Internal f_REAL_decode_oer)) ::
 (_REAL_decode_uper, Gfun(Internal f_REAL_decode_uper)) ::
 (_REAL_encode_uper, Gfun(Internal f_REAL_encode_uper)) ::
 (_values, Gvar v_values) ::
 (_REAL_random_fill, Gfun(Internal f_REAL_random_fill)) :: nil).

Definition public_idents : list ident :=
(_REAL_random_fill :: _REAL_encode_uper :: _REAL_decode_uper ::
 _REAL_decode_oer :: _REAL_encode_oer :: _asn_double2float ::
 _asn_double2REAL :: _asn_REAL2double :: _REAL_decode_xer ::
 _REAL_encode_xer :: _REAL_compare :: _REAL_print :: _REAL__dump ::
 _asn_DEF_REAL :: _asn_OP_REAL :: _OCTET_STRING_random_fill ::
 _OCTET_STRING_encode_uper :: _OCTET_STRING_decode_uper ::
 _OCTET_STRING_encode_oer :: _OCTET_STRING_decode_oer ::
 _OCTET_STRING_encode_xer_utf8 :: _OCTET_STRING_encode_xer ::
 _OCTET_STRING_decode_xer_utf8 :: _OCTET_STRING_decode_xer_binary ::
 _OCTET_STRING_decode_xer_hex :: _OCTET_STRING_encode_der ::
 _OCTET_STRING_decode_ber :: _OCTET_STRING_compare ::
 _OCTET_STRING_print_utf8 :: _OCTET_STRING_print :: _OCTET_STRING_free ::
 _xer_decode_primitive :: _der_encode_primitive :: _ber_decode_primitive ::
 _ASN__PRIMITIVE_TYPE_free :: ___errno_location :: ___isnanl :: ___finitel ::
 ___isnanf :: ___finitef :: _ilogb :: _copysign :: _ldexp :: ___isnan ::
 ___finite :: ___assert_fail :: _asn_TYPE_outmost_tag ::
 _oer_encode_primitive :: _oer_decode_primitive :: _oer_serialize_length ::
 _oer_fetch_length :: _asn_random_between ::
 _asn_generic_unknown_constraint :: _asn_generic_no_constraint :: _memchr ::
 _memcmp :: _memcpy :: _free :: _calloc :: _malloc :: _strtod :: _snprintf ::
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


