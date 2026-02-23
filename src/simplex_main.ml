type expr =
  | Var of int
  | Const of int
  | Mult of expr * expr
  | Add of expr * expr
  | Neg of expr

let rec string_of_expr = function
  | Var v -> "Var(" ^ string_of_int v ^ ")"
  | Const c -> "Const(" ^ string_of_int c ^ ")"
  | Mult (e1, e2) -> "Mult(" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Add (e1, e2) -> "Add(" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Neg e -> "Neg(" ^ string_of_expr e ^ ")"

let extract_num env sigma t =
  let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t) in
  let is_digit c = (c >= '0' && c <= '9') || c = '-' in
  let len = String.length s in
  let buf = Buffer.create len in
  String.iter (fun c -> if is_digit c then Buffer.add_char buf c) s;
  int_of_string (Buffer.contents buf)

let rec parse_expr env sigma t =
  let open EConstr in
  match kind sigma t with
  | App (c, args) ->
      let c_str = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c) in
      let len = Array.length args in
      (match c_str with
       | "Add" | "@Add" -> Add (parse_expr env sigma args.(len - 2), parse_expr env sigma args.(len - 1))
       | "Mult" | "@Mult" -> Mult (parse_expr env sigma args.(len - 2), parse_expr env sigma args.(len - 1))
       | "Const" | "@Const" -> Const (extract_num env sigma args.(len - 1))
       | "Var" | "@Var" -> Var (extract_num env sigma args.(len - 1))
       | "Neg" | "@Neg" -> Neg (parse_expr env sigma args.(len - 1))
       | _ -> failwith ("Unknown App: " ^ c_str))
  | _ -> failwith "Unsupported AST node"

let rec parse_list env sigma t =
  let open EConstr in
  match kind sigma t with
  | Construct _ -> [] 
  | App (c, args) ->
      let c_str = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c) in
      if c_str = "@nil" || c_str = "nil" then []
      else if c_str = "@cons" || c_str = "cons" then
        let len = Array.length args in
        let head = args.(len - 2) in
        let tail = args.(len - 1) in
        let e = parse_expr env sigma head in
        let rest = parse_list env sigma tail in
        e :: rest
      else failwith ("List parse error, got: " ^ c_str)
  | _ -> 
      let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t) in
      if s = "[]" then [] else failwith ("Not a list structure: " ^ s)

let extract_multipliers result_str =
  let prefix = "Multipliers: [ " in
  let prefix_len = String.length prefix in
  if String.length result_str >= prefix_len && String.sub result_str 0 prefix_len = prefix then
    let nums_str = String.sub result_str prefix_len (String.length result_str - prefix_len) in
    let tokens = String.split_on_char ' ' nums_str in
    List.filter_map (fun s -> 
      let s = String.trim s in 
      if s = "" || s = "]" then None else Some (int_of_string s)
    ) tokens
  else []

let locate_construct name =
  match Nametab.locate (Libnames.qualid_of_string name) with
  | Names.GlobRef.ConstructRef c -> c
  | _ -> failwith ("Not a construct: " ^ name)

let mk_construct name = EConstr.UnsafeMonomorphic.mkConstruct (locate_construct name)
let mk_App name args = EConstr.mkApp (mk_construct name, Array.of_list args)

let rec mk_nat n =
  if n <= 0 then mk_construct "O"
  else mk_App "S" [mk_nat (n - 1)]

let rec mk_pos n =
  if n = 1 then mk_construct "xH"
  else if n mod 2 = 0 then mk_App "xO" [mk_pos (n / 2)]
  else mk_App "xI" [mk_pos (n / 2)]

let cert_of_multiplier idx m =
  let gen = mk_App "Cert_isGen" [mk_nat idx] in
  if m = 0 then mk_App "Cert_isMult" [mk_construct "Cert_IsZ0"; gen]
  else mk_App "Cert_isMult" [mk_App "Cert_isZpos" [mk_pos m]; gen]

let rec eval_ast_at_zero = function
  | Var _ -> 0
  | Const c -> c
  | Mult (e1, e2) -> eval_ast_at_zero e1 * eval_ast_at_zero e2
  | Add (e1, e2) -> eval_ast_at_zero e1 + eval_ast_at_zero e2
  | Neg e -> - (eval_ast_at_zero e)

let get_k multipliers ast_list =
  let sum = List.fold_left2 (fun acc m ast -> acc + m * eval_ast_at_zero ast) 0 multipliers ast_list in
  -sum

let build_certificate multipliers ast_list =
  let base_cert =
    match multipliers with
    | [] -> failwith "No multipliers"
    | [m] -> cert_of_multiplier 0 m
    | m :: ms ->
        let rec aux idx lst =
          match lst with
          | [] -> failwith "impossible"
          | [last_m] -> cert_of_multiplier idx last_m
          | next_m :: rest ->
              mk_App "Cert_isAdd" [cert_of_multiplier idx next_m; aux (idx + 1) rest]
        in
        mk_App "Cert_isAdd" [cert_of_multiplier 0 m; aux 1 ms]
  in
  let k = get_k multipliers ast_list in
  if k = 1 then base_cert
  else if k > 1 then mk_App "Cert_isAdd" [base_cert; mk_App "Cert_isZpos" [mk_pos (k - 1)]]
  else failwith "Math error: K is not positive"

let run_dummy_executable expr_list =
  let in_file = Filename.temp_file "rocq_in_" ".txt" in
  let out_file = Filename.temp_file "rocq_out_" ".txt" in
  let oc = open_out in_file in
  List.iter (fun e -> output_string oc (string_of_expr (Neg e) ^ "\n")) expr_list;
  close_out oc;
  let cmd = Printf.sprintf "./simplex_solver %s %s" in_file out_file in
  let exit_code = Sys.command cmd in
  if exit_code <> 0 then failwith "Executable failed";
  let ic = open_in out_file in
  let result = try input_line ic with End_of_file -> "" in
  close_in ic;
  Sys.remove in_file;
  Sys.remove out_file;
  result