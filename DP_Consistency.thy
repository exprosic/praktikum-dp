theory DP_Consistency
  imports DP_Lift
begin

(* consistentM *)

definition consistentM :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<rightharpoonup> 'result) \<Rightarrow> bool" where
  "consistentM f M \<equiv> \<forall>param\<in>dom M. M param = Some (f param)"

lemma consistentM_I:
  assumes "\<And>param v. M param = Some v \<Longrightarrow> v = f param"
  shows "consistentM f M"
  using assms unfolding consistentM_def by (auto)

lemma consistentM_D:
  assumes "consistentM f M" "M param = Some v"
  shows "v = f param"
  using assms unfolding consistentM_def by (auto simp: dom_def)

(* consistentS *)

definition consistentS :: "('param \<Rightarrow> 'result) \<Rightarrow> 'a \<Rightarrow> ('param\<rightharpoonup>'result, 'a) state \<Rightarrow> bool" where
  "consistentS f v s \<equiv> \<forall>M. consistentM f M \<longrightarrow> fst (s M) = v \<and> consistentM f (snd (s M))"

lemma consistentS_I:
  assumes "\<And>M v' M'. \<lbrakk>consistentM f M; s M = (v',M')\<rbrakk> \<Longrightarrow> v'=v \<and> consistentM f M'"
  shows "consistentS f v s"
  using assms unfolding consistentS_def by (blast intro: prod.exhaust_sel)

lemma consistentS_E:
  assumes "consistentS f v s" "consistentM f M"
  obtains v' M' where "s M = (v',M')" "v'=v" "consistentM f M'"
  using assms unfolding consistentS_def by (blast intro: prod.exhaust_sel)

(* consistentDF *)

definition consistentDF :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<Rightarrow>\<^sub>s 'result) \<Rightarrow> bool" where
  "consistentDF f d \<equiv> \<forall>param. consistentS f (f param) (d param)"

lemma consistentDF_I:
  assumes "\<And>param. consistentS f (f param) (d param)"
  shows "consistentDF f d"
  using assms unfolding consistentDF_def by (blast)

(* lifts *)
lemma consistentM_upd: "consistentM f M \<Longrightarrow> v = f param \<Longrightarrow> consistentM f (M(param\<mapsto>v))"
  unfolding consistentM_def by (auto)

lemma consistentS_put:
  assumes "consistentS f v sf" "consistentM f M"
  shows "consistentS f v (put M \<circ>> sf)"
  unfolding put_def using assms by (fastforce intro: consistentS_I elim: consistentS_E)

lemma consistentS_get:
  assumes "\<And>M. consistentM f M \<Longrightarrow> consistentS f v (sf M)"
  shows "consistentS f v (get \<circ>\<rightarrow> sf)"
  unfolding get_def using assms by (fastforce intro: consistentS_I elim: consistentS_E)

lemma consistentS_app:
  assumes "consistentS f v s" "consistentS f v' (sf v)"
  shows "consistentS f v' (s \<circ>\<rightarrow> sf)"
  using assms by (fastforce intro: consistentS_I elim: consistentS_E split: prod.splits)

context
  includes lifting_syntax
begin

(* basics *)

lemma consistentS_return_transfer[transfer_rule]:
  "(op = ===> consistentS dp) (\<lambda>x. x) return"
  unfolding rel_fun_def return_def by (auto intro: consistentS_I)
lemmas consistentS_return = consistentS_return_transfer[unfolded rel_fun_def, rule_format]

lemma consistentS_app_transfer[transfer_rule]:
  "(consistentS dp ===> (op = ===> consistentS dp) ===> consistentS dp) (\<lambda>v f. f v) op \<circ>\<rightarrow>"
  unfolding rel_fun_def by (fastforce intro: consistentS_app)
    
lemma consistentS_lift_fun_app_transfer[transfer_rule]:
  "(consistentS f ===> consistentS f ===> consistentS f) (\<lambda> a b. a b) lift_fun_app"
  unfolding rel_fun_def by (fastforce intro: consistentS_I elim: lift_fun_appE consistentS_E)
    
lemma consistentS_binary_transfer[transfer_rule]:
  "(consistentS f ===> consistentS f ===> consistentS f) g (lift_binary g)"
  unfolding lift_binary_def by transfer_prover
lemmas consistentS_binary = consistentS_binary_transfer[unfolded rel_fun_def, rule_format]

(* else *)

lemma consistentS_cond_transfer[transfer_rule]:
  "(consistentS dp ===> consistentS dp ===> consistentS dp ===> consistentS dp) If If\<^sub>s"
  unfolding If\<^sub>s_def by transfer_prover
lemmas consistentS_cond = consistentS_cond_transfer[unfolded rel_fun_def, rule_format]

lemma consistentS_case_option_transfer:
  "(consistentS dp ===> (op = ===> consistentS dp) ===> consistentS dp ===> consistentS dp) case_option case_option\<^sub>s"
  unfolding case_option\<^sub>s_def by transfer_prover
lemmas consistentS_case_option = consistentS_case_option_transfer[unfolded rel_fun_def, rule_format]

end (* End of lifting syntax *)

lemmas consistentS_basic_intros =
  consistentS_return consistentS_app consistentS_get consistentS_put

lemma consistentS_checkmem:
  assumes "consistentS f v s" "v = f param"
  shows "consistentS f v (checkmem param s)"
  using assms by (fastforce intro: consistentS_basic_intros consistentM_upd dest: consistentM_D split: option.splits)

lemma consistentS_checkmem':
  assumes "consistentS f (f param) s"
  shows "consistentS f (f param) (checkmem param s)"
  using assms by (fastforce intro: consistentS_basic_intros consistentM_upd dest: consistentM_D split: option.splits)

lemmas consistency_rules =
  consistentS_cond consistentS_checkmem consistentS_return consistentS_binary

lemmas consistentS_lift_fun_app = consistentS_lift_fun_app_transfer[unfolded rel_fun_def, rule_format]

end