
import meta.rb_map
import tactic.basic

open interactive interactive.types lean.parser

meta def loc.to_string_aux : option name → string
| none := "⊢"
| (some x) := to_string x

meta def loc.to_string : loc → string
| (loc.ns []) := ""
| (loc.ns [none]) := ""
| (loc.ns ls) := string.join $ list.intersperse " " (" at" :: ls.map loc.to_string_aux)
| loc.wildcard := " at *"

namespace tactic
namespace interactive

meta def arg.to_tactic_format : simp_arg_type → tactic format
| (simp_arg_type.expr e) := pp e
| simp_arg_type.all_hyps := pure "*"
| (simp_arg_type.except n) := pure format!"-{n}"

meta def rec.to_tactic_format (e : pexpr) : tactic format :=
do r ← e.get_structure_instance_info,
   fs ← mzip_with (λ n v,
     do v ← to_expr v >>= pp,
        pure $ format!"{n} := {v}" )
     r.field_names r.field_values,
   let ss := r.sources.map (λ s, format!" .. {s}"),
   let x : format := format.join $ list.intersperse ", " (fs ++ ss),
   pure format!" {{{x}}"

local postfix `?`:9001 := optional

meta def squeeze_simp
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location)
  (cfg : parse texpr?) : tactic unit :=
do g ← main_goal,
   (cfg',c) ← do { cfg ← (cfg : tactic pexpr),
                   e ← to_expr ``(%%cfg : simp_config_ext),
                   fmt ← has_to_tactic_format.to_tactic_format cfg,
                   prod.mk <$> eval_expr simp_config_ext e
                           <*> rec.to_tactic_format cfg }
       <|> pure ({ }, ""),
   simp use_iota_eqn no_dflt hs attr_names locat cfg',
   g ← instantiate_mvars g,
   let vs := g.list_constant,
   vs ← vs.mfilter (succeeds ∘ has_attribute `simp),
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let loc := loc.to_string locat,
   hs ← hs.mmap arg.to_tactic_format,
   let args := hs ++ vs.to_list.map to_fmt,
   trace format!"simp{use_iota_eqn} only {args}{attrs}{loc}{c}"

end interactive
end tactic
