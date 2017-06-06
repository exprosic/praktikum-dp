theory Scratch imports        
  Main
keywords
  "gun" :: thy_decl
  
begin
  ML \<open>@{context}\<close>
ML \<open>
open Function_Lib
open Function_Common


val fun_config = FunctionConfig { sequential=true, default=NONE,
  domintros=false, partials=false }

fun add_fun_cmd_inline fixes specs config = fn int => fn lthy =>
  let
    val _ = writeln ("fixes : >>>");
    val _ = writeln (@{make_string} fixes);
    val _ = writeln ("<<<");
    val _ = writeln "";

    val _ = writeln ("specs : >>>");
    val _ = writeln (@{make_string} specs);
    val _ = writeln ("<<<");
    val _ = writeln "";

    val _ = writeln ("spec[0].1.2 : >>>");
    val _ = writeln ( (nth specs 0 |> #1 |> #2));
    val _ = writeln ("<<<");
    val _ = writeln "";

    val _ = writeln ("spec[1].1.2 : >>>");
    val _ = writeln ((nth specs 1 |> #1 |> #2));
    val _ = writeln ("<<<");
    val _ = writeln "";

    val _ = writeln ("lth: >>>");
    val _ = writeln (@{make_string} lthy);
    val _ = writeln ("<<<");
    val _ = writeln ("");

    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy
  in
    lthy
    |>  Function.add_function_cmd fixes specs config pat_completeness_auto int  |> snd
    |> prove_termination |> snd
  end;

val _ =
  Outer_Syntax.local_theory' @{command_keyword gun}
    "define general recursive functions (short version)"
    (function_parser fun_config
      >> (fn (config, (fixes, specs)) => add_fun_cmd_inline fixes specs config));
\<close>
  
  
gun f :: "nat \<Rightarrow> nat" where
  "f 0 = 0" |
  "f (Suc x) = f x + x"

ML \<open>
Function.add_function [(@{binding f}, SOME @{typ "nat => nat"}, NoSyn)];
val x: binding = @{binding f};
val x: typ = @{typ "nat \<Rightarrow> nat"};
type x = Specification.multi_specs;
type x' = ((Attrib.binding * term) * term list * (binding * typ option * mixfix) list) list;
type x = Specification.multi_specs_cmd;
type x' = ((Attrib.binding * string) * string list * (binding * string option * mixfix) list) list;
type x = Attrib.binding;
type x' = binding * Token.src list;
val x = Specification.read_multi_specs;
val x: function_config = FunctionConfig { sequential=true, default=NONE, domintros=false, partials=false };
open Function_Fun;
\<close>

ML_val \<open>
@{term "(Suc 0) + (Suc (Suc 0))"};
@{term Nil};
Specification.check_multi_specs;
Specification.check_multi_specs;
Parse_Spec.specification;
Parse.vars -- Parse_Spec.where_multi_specs;
Parse.vars;
Parse_Spec.where_multi_specs;
Parse.where_ |-- Parse.!!! Parse_Spec.multi_specs;
Parse_Spec.multi_specs;
  Parse.enum1 "|"
    ((Parse_Spec.opt_thm_name ":" -- Parse.prop -- Parse_Spec.if_assumes -- Parse.for_fixes >> Scan.triple1) --|
      Scan.option (Scan.ahead (Parse.name || Parse.$$$ "[") -- Parse.!!! (Parse.$$$ "|")));
\<close>
ML_val \<open>
Function_Common.split_def @{context} I;
val geq = @{term "\<And>x. f x = x"};
val qs = Term.strip_qnt_vars @{const_name Pure.all} geq;
val imp = Term.strip_qnt_body @{const_name Pure.all} geq;
val (gs, eq) = Logic.strip_horn imp;
Function_Common.split_def @{context} I eq;
type x = int Token.parser;
\<close>
term "HOL.Trueprop"
term "HOL.Trueprop x"
ML_val \<open>
Parse_Spec.where_multi_specs;

val multi_specs = Parse.enum1 "|"
    ((Parse_Spec.opt_thm_name ":" -- Parse.prop -- Parse_Spec.if_assumes -- Parse.for_fixes >> Scan.triple1) --|
      Scan.option (Scan.ahead (Parse.name || Parse.$$$ "[") -- Parse.!!! (Parse.$$$ "|")));

val where_multi_specs = Parse.where_ |-- Parse.!!! multi_specs;

val specification = Parse.vars -- where_multi_specs;
val vars = Parse.vars;
\<close>

ML_val \<open>
val tmp00 = Parse_Spec.opt_thm_name ":";
val tmp01 = tmp00 -- Parse.prop;
val tmp02 = tmp01 -- Parse_Spec.if_assumes;
val tmp03 = tmp02 -- Parse.for_fixes;
val tmp0' = tmp03;
val tmp0 = tmp0'  >> Scan.triple1;
val tmp1 = Scan.option (Scan.ahead (Parse.name || Parse.$$$ "[") -- Parse.!!! (Parse.$$$ "|"));
val tmp = tmp0 --| tmp1;
val multi_specs = Parse.enum1 "|" tmp;
val where_multi_specs = Parse.where_ |-- Parse.!!! multi_specs;
val specification = Parse.vars -- where_multi_specs;
\<close>
  
ML_val \<open>
Binding.empty_atts;
\<close>
  
ML \<open>
fun prove_termination lthy =
  Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy;

type x = Specification.multi_specs_cmd;
type x' = ( ( Attrib.binding (* fold_Nil / fold_Cons *)
            * string         (* fold [] = ... *)
            )
          * string list      (* if_assumes? *)
          * (binding * string option * mixfix) list (* for fixes? *)
          ) list;

type x = Specification.multi_specs;
type multi_spec = ( ( Attrib.binding
            * term
            )
          * term list
          * (binding * typ option * mixfix) list
          );
type multi_specs = multi_spec list;

val binding_sometyp_mixfix = (@{binding ff}, SOME @{typ "nat => nat"}, NoSyn);
val binding_sometyp_mixfix_cmd = (Binding.concealed (Binding.name "ff"), SOME "nat => nat", NoSyn);

val spec0: multi_spec = ( ( (Binding.concealed Binding.empty, [])
                          , @{prop "ff (0::nat) = (0::nat)"}
                          )
                        , []
                        , []
                        );
val spec_cmd0 = ( ( Binding.empty_atts
                 , "ff 0 = 0"
                 )
               , []
               , []
               );

 Function_Fun.add_fun [binding_sometyp_mixfix] [spec0] Function_Common.default_config; 
\<close>
datatype foo = Foo nat

local_setup{*
Function.add_function [(@{binding "baz"}, NONE, NoSyn)] [(Attrib.empty_binding, @{term "\<And>x. baz (Foo x) = x"})]
conf pat_completeness_auto #> snd*}
ML_val \<open>
open Pretty;
type x = Pretty.T
\<close>
ML {*
val x: string = (@{make_string} [3,4]);
val _ = writeln (@{make_string} @{term "[]"});
writeln (@{make_string} I);
*}
end   
