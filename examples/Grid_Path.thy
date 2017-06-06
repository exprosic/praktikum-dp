theory Grid_Path
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
begin

fun lift_option_choice :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "lift_option_choice f (Some x) (Some y) = Some (f x y)" |
  "lift_option_choice f (Some x) None = Some x" |
  "lift_option_choice f None (Some y) = Some y" |
  "lift_option_choice f None None = None"

abbreviation "min_opt \<equiv> lift_option_choice min"
  
context (* *)
  fixes W :: "nat\<times>nat \<Rightarrow> nat option"
begin
text \<open>Not primrec\<close>
text \<open>Dimensionality given by i, j\<close>
fun ed :: "nat\<times>nat \<Rightarrow> nat option" where
  "ed (0, 0) = W (0, 0)" |
  "ed (0, Suc j) = do {prev \<leftarrow> ed (0, j); here \<leftarrow> W (0, Suc j); Some (prev + here)}" |
  "ed (Suc i, 0) = do {prev \<leftarrow> ed (i, 0); here \<leftarrow> W (Suc i, 0); Some (prev + here)}" |
  "ed (Suc i, Suc j) = do {prev \<leftarrow> min_opt (ed (i, j)) (min_opt (ed (Suc i, j)) (ed (i, Suc j))); here \<leftarrow> W (Suc i, Suc j); Some (prev + here)}"

fun ed'  :: "nat\<times>nat \<Rightarrow>\<^sub>s nat option" where
  "ed'$ (0, 0) =CHECKMEM= \<langle>W (0, 0)\<rangle>" |
  "ed'$ (0, Suc j) =CHECKMEM= \<langle>Suc j\<rangle>" |
  "ed'$ (Suc i, 0) =CHECKMEM= \<langle>Suc i\<rangle>" |
  "ed'$ (Suc i, Suc j) =CHECKMEM= min\<^sub>s (ed' (i, j) +\<^sub>s \<langle>2\<rangle>) (min\<^sub>s (ed' (Suc i, j) +\<^sub>s \<langle>1\<rangle>) (ed' (i, Suc j) +\<^sub>s \<langle>1\<rangle>))"
term "bind (Some 0) (\<lambda>x. Some x) "
term "do {prev \<leftarrow> ed (0, j); here \<leftarrow> W (0, Suc j); Some (prev + here)}"
term 0 (*

lemma "consistentDF ed ed'"
  by (dp_match induct: ed.induct simp: ed.simps ed'.simps)

end

end