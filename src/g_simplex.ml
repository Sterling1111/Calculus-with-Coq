let _ = Mltop.add_known_module "simplex_plugin.plugin"

# 3 "src/g_simplex.mlg"
 
open Pp
module Tacentries = Ltac_plugin.Tacentries

# 9 "src/g_simplex.ml"

let () = Tacentries.tactic_extend "simplex_plugin.plugin" "call_simplex_plugin" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("call_simplex_plugin", 
                            Tacentries.TyNil), (fun ist -> 
# 9 "src/g_simplex.mlg"
                                
    Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      
      let open EConstr in
      match kind sigma concl with
      | App (ev_f, args) ->
          let f_term = args.(1) in
          (try
            let ocaml_ast_list = Simplex_main.parse_list env sigma f_term in
            let result = Simplex_main.run_dummy_executable ocaml_ast_list in
            let multipliers = Simplex_main.extract_multipliers result in
            
            if multipliers = [] then
              Tacticals.tclZEROMSG (str ("Solver failed: " ^ result))
            else
              let cert_term = Simplex_main.build_certificate multipliers ocaml_ast_list in
              let name = Names.Name (Names.Id.of_string "c") in
              Tactics.pose_tac name cert_term
          with Failure msg ->
            Tacticals.tclZEROMSG (str msg))
      | _ -> Tacticals.tclZEROMSG (str "Goal is not of the form (eval_form env f)")
    )
  
# 41 "src/g_simplex.ml"
)))]

