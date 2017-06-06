theory Cookbook
  imports Main "~~/src/HOL/Eisbach/Eisbach_Tools"
begin
  
ML \<open>
Proof_Context.print_abbrevs false @{context} = Proof_Context.print_abbrevs true @{context}
\<close>
  
ML \<open>
val foo_thm = @{lemma "True" and "False \<Longrightarrow> P" by simp_all};
foo_thm |> (fn thms => Proof_Context.pretty_fact @{context} ("xx", thms)) 
\<close>
  
ML \<open>
open Proof_Context;
\<close>
 
ML {*
val conf = Function_Common.default_config;
fun pat_completeness_auto ctxt = Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
*}
datatype foo = Foo nat
local_setup {*
Function_Fun.add_fun [(@{binding "baz"}, NONE, NoSyn)] [((Binding.empty_atts, @{term "\<And>x. baz (Foo x) = x"}), [], [])] conf
*}
term baz
thm baz.simps
ML\<open>
val x: string = @{method fastforce};
type x = Method.method;
\<close>
method
end