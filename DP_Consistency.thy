theory DP_Consistency
  imports DP_Lift
begin

definition consistentM :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<rightharpoonup> 'result) \<Rightarrow> bool" where
  "consistentM f M \<equiv> \<forall>param\<in>dom M. M param = Some (f param)"

lemma consistentM_I:
  assumes "\<And>param v. M param = Some v \<Longrightarrow> v = f param"
  shows "consistentM f M"
  using assms unfolding consistentM_def by auto

lemma consistentM_D:
  assumes "consistentM f M" "M param = Some v"
  shows "v = f param"
  using assms by (auto simp: consistentM_def dom_def)

lemma consistentM_E:
  assumes "consistentM f M" "M param = Some v"
  obtains "v = f param"
  using assms by (auto simp: consistentM_def dom_def)

definition consistentS :: "('param \<Rightarrow> 'result) \<Rightarrow> 'a \<Rightarrow> ('param\<rightharpoonup>'result, 'a) state \<Rightarrow> bool" where
  "consistentS f v s \<equiv> \<forall>M. consistentM f M \<longrightarrow> fst (s M) = v \<and> consistentM f (snd (s M))"

lemma consistentS_I:
  assumes "\<And>M v' M'. \<lbrakk>consistentM f M; s M = (v',M')\<rbrakk> \<Longrightarrow> v'=v \<and> consistentM f M'"
  shows "consistentS f v s"
  by (auto simp: consistentS_def intro!: assms)
lemma consistentS_E:
  assumes "consistentS f v s" "consistentM f M"
  obtains v' M' where "s M = (v',M')" "v'=v" "consistentM f M'"
  using assms by (force simp: consistentS_def)

definition consistentDF :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<Rightarrow>\<^sub>s 'result) \<Rightarrow> bool" where
  "consistentDF f d \<equiv> \<forall>param. consistentS f (f param) (d param)"

lemma consistentDF_I:
  assumes "\<And>param. consistentS f (f param) (d param)"
  shows "consistentDF f d"
  by (auto simp: consistentDF_def intro!: assms)

lemma consistentS_lift:
  assumes "consistentS dp f f'" "consistentS dp v v'"
  shows "consistentS dp (f v) (f' . v')"
  using assms by (fastforce intro: consistentS_I elim: lift_fun_appE consistentS_E)

lemma consistentM_upd: "consistentM f M \<Longrightarrow> v = f param \<Longrightarrow> consistentM f (M(param\<mapsto>v))"
  unfolding consistentM_def by auto

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

lemma consistentS_return:
  "v = v' \<Longrightarrow> consistentS dp v \<langle>v'\<rangle>"
  unfolding consistentS_def return_def by simp

lemmas consistentS_basics =
  consistentS_return consistentS_app consistentS_get consistentS_put

lemma consistentS_checkmem:
  assumes "consistentS f v s" "v = f param"
  shows "consistentS f v (checkmem param s)"
  using assms by (auto intro!: consistentS_basics consistentM_upd elim: consistentM_E split: option.splits)

text \<open>Generalized version of your fold lemma\<close>
lemma consistent_fold: 
  assumes
    "consistentS dp init init'"
    "list_all2 (consistentS dp) xs xs'"
    "f' = f" 
  shows
    "consistentS dp (fold f xs init) (fold\<^sub>s \<langle>f'\<rangle> xs' init')"
  using assms(2,1,3)
  by (induction arbitrary: init init' rule: list_all2_induct)
     (fastforce simp: assms(3) dest!: consistentS_return consistentS_lift)+

lemma consistent_fold':
  "\<lbrakk>consistentS dp init init';
    \<And>i. i\<in>set idx \<Longrightarrow> consistentS dp (ls i) (ls' i);
    f' = f\<rbrakk> \<Longrightarrow>
   consistentS dp (fold f (map ls idx) init) (fold\<^sub>s \<langle>f'\<rangle> (map ls' idx) init')"
  apply (rule consistent_fold)
    apply assumption
  by (induction idx) auto

lemma consistent_cond:
  assumes "consistentS dp b sb" "b \<Longrightarrow> consistentS dp v0 s0" "\<not>b \<Longrightarrow> consistentS dp v1 s1"
  shows "consistentS dp (if b then v0 else v1) (if\<^sub>s sb then\<^sub>s s0 else\<^sub>s s1)"
  using assms by (auto simp: If\<^sub>s_def intro: consistentS_app)

lemma consistent_cond':
  assumes "b \<Longrightarrow> consistentS dp v0 s0" "\<not>b \<Longrightarrow> consistentS dp v1 s1"
  shows "consistentS dp (if b then v0 else v1) (if b then s0 else s1)"
  using assms by auto


context
  includes lifting_syntax
begin

lemma consistentDF_alt_def: "consistentDF f d \<longleftrightarrow> (op = ===> consistentS f) f d"
  unfolding consistentDF_def rel_fun_def by simp

lemma consistentS_lift_fun_app_transfer:
  "(consistentS f ===> consistentS f ===> consistentS f) (\<lambda> a b. a b) lift_fun_app"
  by (auto simp: rel_fun_def intro: consistentS_lift)

lemma consistent_binary_transfer:
  "(consistentS f ===> consistentS f ===> consistentS f) g (lift_binary g)"
  unfolding lift_binary_def
  supply [transfer_rule] = consistentS_lift_fun_app_transfer consistentS_return
  by transfer_prover

lemma consistent_fold_alt:
  assumes
    "consistentS dp init init'"
    "list_all2 (consistentS dp) xs xs'"
    "f' = lift_binary f"
  shows
    "consistentS dp (fold f xs init) (fold f' xs' init')"
    apply (simp only: assms(3))
  supply [transfer_rule] = consistent_binary_transfer assms
  by transfer_prover

text \<open>
  We could prove a stronger version of this lemma by replacing @{term "op ="}
  by another relation.
\<close>
lemma consistent_fold_map:
  "\<lbrakk>consistentS dp init init';
    (op = ===> consistentS dp) ls ls';
    f' = lift_binary f\<rbrakk> \<Longrightarrow>
   consistentS dp (fold f (map ls idx) init) (fold f' (map ls' idx) init')"
  apply (rule consistent_fold_alt)
    apply assumption
  subgoal premises prems
    supply [transfer_rule] = prems
    by transfer_prover
  .

text \<open>And finally a 'big-bang version' of the last two proofs combined.\<close>
lemma consistent_fold_map_alt:
  assumes
    "consistentS dp init init'"
    "(op = ===> consistentS dp) ls ls'"
  shows
    "consistentS dp (fold f (map ls idx) init) (fold (lift_binary f) (map ls' idx) init')"
  supply [transfer_rule] = consistent_binary_transfer assms
  by (transfer_prover)

lemma consistent_cond_alt:
  assumes "consistentS dp v0 s0" "consistentS dp v1 s1"
  shows "consistentS dp (if b then v0 else v1) (if b then s0 else s1)"
  supply [transfer_rule] = assms
  by transfer_prover

lemma consistentS_binary:
  assumes "consistentS dp v0 s0" "consistentS dp v1 s1"
  shows "consistentS dp (f v0 v1) (lift_binary f s0 s1)"
  supply [transfer_rule] = consistent_binary_transfer assms
    by transfer_prover

text \<open>
  Conclusion: the default parametricity rules for \<open>map\<close> and \<open>if _ then _ else\<close> are too weak.
  Fold works out of the box.
\<close>

end (* End of lifting syntax *)

lemmas consistency_rules =
  consistent_cond consistent_fold' consistentS_checkmem consistentS_return consistentS_binary

end