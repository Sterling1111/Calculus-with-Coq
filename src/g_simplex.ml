let _ = Mltop.add_known_module "simplex_plugin.plugin"

# 3 "src/g_simplex.mlg"
 
open Pp
open Stdarg
module Tacentries = Ltac_plugin.Tacentries

# 10 "src/g_simplex.ml"

let () = Tacentries.tactic_extend "simplex_plugin.plugin" "call_simplex_plugin" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("call_simplex_plugin", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyNil))), (fun cert_name f_term ist
                                                 -> 
# 10 "src/g_simplex.mlg"
                                                                
    Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      
      (try
        let ocaml_ast_list = Simplex_main.parse_list env sigma f_term in
        let result = Simplex_main.run_dummy_executable ocaml_ast_list in
        let multipliers = Simplex_main.extract_multipliers result in
        
        if multipliers = [] then
          Tacticals.tclZEROMSG (str "Cannot find witness.")
        else
          let cert_term = Simplex_main.build_certificate multipliers ocaml_ast_list in
          let name = Names.Name cert_name in
          Tactics.pose_tac name cert_term
      with Failure msg ->
        Tacticals.tclZEROMSG (str msg))
    )
  
# 39 "src/g_simplex.ml"
)))]

