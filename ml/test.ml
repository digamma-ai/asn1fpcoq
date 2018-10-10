open OcamlFPBER

let () =
  begin
    match ocaml_float64_to_BER_exact Float.neg_infinity with
    | None -> Printf.eprintf "FP->BER Conversion error!\n"
    | Some a ->
       match ocaml_BER_to_float64_exact a with
       | None -> Printf.eprintf "BER->FP Conversion error!\n"
       | Some f -> Printf.eprintf "Got: %f\n" f
  end ;
  exit 0
