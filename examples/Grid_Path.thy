theory Grid_Path
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
begin

fun lift_option_choice :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "lift_option_choice f (Some x) (Some y) = Some (f x y)" |
  "lift_option_choice f (Some x) None = Some x" |
  "lift_option_choice f None (Some y) = Some y" |
  "lift_option_choice f None None = None"

abbreviation "min_opt \<equiv> lift_option_choice min"
abbreviation "min_opt\<^sub>s \<equiv> lift_binary min_opt"

context (* *)
  fixes W :: "nat\<times>nat \<Rightarrow> nat option"
begin
text \<open>Not primrec\<close>
text \<open>Dimensionality given by i, j\<close>
(*
fun ed :: "nat\<times>nat \<Rightarrow> nat option" where
  "ed (0, 0) = W (0, 0)"
| "ed (0, Suc j) = (case ed (0, j) of None => None | Some prev =>
                     (case W (0, Suc j) of None => None | Some here =>
                       Some (prev + here)))"
| "ed (Suc i, 0) = (case ed (i, 0) of None => None | Some prev =>
                     (case W (Suc i, 0) of None => None | Some here =>
                       Some (prev + here)))"
| "ed (Suc i, Suc j) = (case min_opt (ed (i, j)) (min_opt (ed (Suc i, j)) (ed (i, Suc j))) of None => None | Some prev =>
                         (case W (Suc i, Suc j) of None => None | Some here =>
                           Some (prev + here)))"
*)
fun ed :: "nat\<times>nat \<Rightarrow> nat option" where
  "ed (0, 0) = W (0, 0)"
| "ed (0, Suc j) = case_option None (\<lambda>prev.
                     case_option None (\<lambda>here.
                       Some (prev + here)
                     ) (W (0, Suc j))
                   ) (ed (0, j))"
| "ed (Suc i, 0) = case_option None (\<lambda>prev.
                     case_option None (\<lambda>here.
                       Some (prev + here)
                     ) (W (Suc i, 0))
                   ) (ed (i, 0))"
| "ed (Suc i, Suc j) = case_option None (\<lambda>prev.
                         case_option None (\<lambda>here.
                           Some (prev + here)
                         ) (W (Suc i, Suc j))
                       ) (min_opt (ed (i, j)) (min_opt (ed (Suc i, j)) (ed (i, Suc j))))"

fun ed'  :: "nat\<times>nat \<Rightarrow>\<^sub>s nat option" where
  "ed'$ (0, 0) =CHECKMEM= \<langle>W (0, 0)\<rangle>"
| "ed'$ (0, Suc j) =CHECKMEM= case_option\<^sub>s \<langle>None\<rangle> (\<lambda>prev.
                     case_option\<^sub>s \<langle>None\<rangle> (\<lambda>here.
                       \<langle>Some (prev + here)\<rangle>
                     ) \<langle>W (0, Suc j)\<rangle>
                   ) (ed' (0, j))"
| "ed'$ (Suc i, 0) =CHECKMEM= case_option\<^sub>s \<langle>None\<rangle> (\<lambda>prev.
                     case_option\<^sub>s \<langle>None\<rangle> (\<lambda>here.
                       \<langle>Some (prev + here)\<rangle>
                     ) \<langle>W (Suc i, 0)\<rangle>
                   ) (ed' (i, 0))"
| "ed'$ (Suc i, Suc j) =CHECKMEM= case_option\<^sub>s \<langle>None\<rangle> (\<lambda>prev.
                         case_option\<^sub>s \<langle>None\<rangle> (\<lambda>here.
                           \<langle>Some (prev + here)\<rangle>
                         ) \<langle>W (Suc i, Suc j)\<rangle>
                       ) (min_opt\<^sub>s (ed' (i, j)) (min_opt\<^sub>s (ed' (Suc i, j)) (ed' (i, Suc j))))"
  
thm ed.simps ed'.simps

lemma "consistentDF ed ed'"
  oops (*by (dp_match induct: ed.induct simp: ed.simps ed'.simps)*)

end

end