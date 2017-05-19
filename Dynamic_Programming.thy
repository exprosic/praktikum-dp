theory Dynamic_Programming
  imports Main "~~/src/HOL/Library/State_Monad"
begin

type_synonym ('s, 'a) state = "'s \<Rightarrow> ('a \<times> 's)"
type_synonym ('param, 'result) dpstate = "('param \<rightharpoonup> 'result, 'result) state"
type_synonym ('param, 'result) dpfun = "'param \<Rightarrow> ('param, 'result) dpstate"

definition return :: "'a \<Rightarrow> ('s, 'a) state" ("\<langle>_\<rangle>") where
  "\<langle>x\<rangle> = (\<lambda>M. (x, M))"
fun get :: "('s, 's) state" where
  "get M = (M, M)"
fun put :: "'s \<Rightarrow> ('s, unit) state" where
  "put M _ = ((), M)"

fun update :: "'param \<Rightarrow> ('param, 'result) dpstate \<Rightarrow> ('param, 'result) dpstate" where
  "update params calcVal = exec {
    v \<leftarrow> calcVal;
    M' \<leftarrow> get;
    _ \<leftarrow> put (M'(params\<mapsto>v));
    \<langle>v\<rangle>
  }"

fun checkmem :: "'param \<Rightarrow> ('param, 'result) dpstate \<Rightarrow> ('param, 'result) dpstate" where
  "checkmem params calcVal = exec {
    M \<leftarrow> get;
    case M params of
      Some v => \<langle>v\<rangle> |
      None => update params calcVal
    }"

definition lift_fun_app :: "('M,'a\<Rightarrow>'b) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state" (infixl "." 51) where
  "lift_fun_app sf sv \<equiv> exec {f \<leftarrow> sf; v \<leftarrow> sv; \<langle>f v\<rangle>}"

lemma lift_fun_appE:
  assumes "(sf . sv) M = (v', M')"
  obtains f M'' v where "sf M = (f,M'')" and "sv M'' = (v,M')" and "v' = f v"
  using assms unfolding lift_fun_app_def return_def by (auto split: prod.splits)

primrec fold\<^sub>s :: "('M,'a \<Rightarrow> 'b \<Rightarrow> 'b) state \<Rightarrow> ('M,'a) state list \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'b) state" where
fold\<^sub>s_Nil:  "fold\<^sub>s f [] init = init" |
fold\<^sub>s_Cons: "fold\<^sub>s f (x # xs) init = fold\<^sub>s f xs (f . x . init)"

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
  assumes "consistentS f v s" "consistentM f M" "s M = (v',M')"
  obtains "v'=v" "consistentM f M'"
  using assms by(fastforce simp: consistentS_def)+

definition consistentDF :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param, 'result) dpfun \<Rightarrow> bool" where
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
  assumes "consistentS f v (sf ())" "consistentM f M"
  shows "consistentS f v (put M \<circ>\<rightarrow> sf)"
  using assms by (fastforce intro: consistentS_I elim: consistentS_E)

lemma consistentS_get:
  assumes "\<And>M. consistentM f M \<Longrightarrow> consistentS f v (sf M)"
  shows "consistentS f v (get \<circ>\<rightarrow> sf)"
  using assms by (fastforce intro: consistentS_I elim: consistentS_E)

lemma consistentS_app:
  assumes "consistentS f v s" "consistentS f v' (sf v)"
  shows "consistentS f v' (s \<circ>\<rightarrow> sf)"
  using assms by (fastforce intro: consistentS_I elim: consistentS_E split: prod.splits)

lemma consistentS_return:
  "v = v' \<Longrightarrow> consistentS dp v \<langle>v'\<rangle>"
  unfolding consistentS_def return_def by simp

lemmas consistentS_basics = consistentS_get consistentS_return consistentS_app consistentS_put

lemma consistentS_checkmem:
  assumes "consistentS f v s" "v = f param"
  shows "consistentS f v (checkmem param s)"
  by (fastforce intro: assms consistentS_basics consistentM_upd elim: consistentM_E split: option.splits)

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

definition lift_binary :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'c) state" where
  "lift_binary f s0 s1 \<equiv> \<langle>f\<rangle> . s0 . s1"

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

lemma consistent_cond:
  assumes "b \<Longrightarrow> consistentS dp v0 s0" "\<not>b \<Longrightarrow> consistentS dp v1 s1"
  shows "consistentS dp (if b then v0 else v1) (if b then s0 else s1)"
  using assms by auto

lemmas consistency_rules =
  consistent_cond consistent_fold' consistentS_checkmem consistentS_return consistentS_binary

term lift_binary
abbreviation "max\<^sub>s \<equiv> lift_binary max"
abbreviation "min\<^sub>s \<equiv> lift_binary min"
abbreviation plus_state (infixl "+\<^sub>s" 65) where "op +\<^sub>s \<equiv> lift_binary (op +)"

(* Fib *)

fun fib :: "nat \<Rightarrow> nat" where
"fib 0 = 0" |
"fib (Suc 0) = 1" |
"fib (Suc(Suc n)) = fib (Suc n) + fib n"

fun fib' :: "(nat, nat) dpfun" where
  "fib' 0 = checkmem 0 (\<langle>0\<rangle>)" |
  "fib' (Suc 0) = checkmem (Suc 0) (\<langle>1\<rangle>)" |
  "fib' (Suc (Suc n)) = checkmem (Suc (Suc n)) (fib' (Suc n) +\<^sub>s fib' n)"

lemma "consistentDF fib fib'"
  apply (rule consistentDF_I, induct_tac rule: fib.induct)

    apply (simp only: fib'.simps fib.simps)
    apply (assumption | rule consistency_rules | simp only: only: fib.simps)+

   apply (simp only: fib'.simps fib.simps)
   apply (assumption | rule consistency_rules | simp only: only: fib.simps)+

  apply (simp only: fib'.simps fib.simps)
  apply (assumption | rule consistency_rules | simp only: only: fib.simps)+
  done

(* Bellman Ford *)

context
  fixes W :: "nat \<Rightarrow> nat \<Rightarrow> int"
    and n :: nat
begin

text \<open>Could also be primrec\<close>
text \<open>Dimensionality as parameter\<close>

fun bf :: "(nat\<times>nat) \<Rightarrow> int" where
  "bf (0, j) = W 0 j" |
  "bf (Suc k, j) = fold min [bf (k, i) + W i j. i\<leftarrow>[0..<n]] (bf (k, j))"

fun bf' :: "(nat\<times>nat, int) dpfun" where
  "bf' (0, j) = checkmem (0,j) (\<langle>W 0 j\<rangle>)" |
  "bf' (Suc k, j) = checkmem (Suc k,j) (fold\<^sub>s \<langle>min\<rangle> [bf' (k, i) +\<^sub>s \<langle>W i j\<rangle>. i\<leftarrow>[0..<n]] (bf' (k, j)))"

lemma "consistentDF bf bf'"
  apply (rule consistentDF_I, induct_tac rule: bf.induct)
   apply (simp only: bf.simps bf'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: bf.simps)

   apply (simp only: bf.simps bf'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: bf.simps)
  done

end

text \<open>Not primrec\<close>
text \<open>Dimensionality given by i, j\<close>
fun ed :: "(nat\<times>nat) \<Rightarrow> nat" where
  "ed (0, 0) = 0" |
  "ed (0, Suc j) = Suc j" |
  "ed (Suc i, 0) = Suc i" |
  "ed (Suc i, Suc j) = min (ed (i, j) + 2) (min (ed (Suc i, j) + 1) (ed (i, Suc j) + 1))"

fun ed'  :: "(nat\<times>nat, nat) dpfun" where
  "ed' (0, 0) = checkmem (0,0) (\<langle>0\<rangle>)" |
  "ed' (0, Suc j) = checkmem (0,Suc j) (\<langle>Suc j\<rangle>)" |
  "ed' (Suc i, 0) = checkmem (Suc i,0) (\<langle>Suc i\<rangle>)" |
  "ed' (Suc i, Suc j) = checkmem (Suc i,Suc j) (min\<^sub>s (ed' (i, j) +\<^sub>s \<langle>2\<rangle>) (min\<^sub>s (ed' (Suc i, j) +\<^sub>s \<langle>1\<rangle>) (ed' (i, Suc j) +\<^sub>s \<langle>1\<rangle>)))"
thm minus_nat_inst.minus_nat

lemma "consistentDF ed ed'"
  apply (rule consistentDF_I, induct_tac rule: ed.induct)
   apply (simp only: ed.simps ed'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: ed.simps)

   apply (simp only: ed.simps ed'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: ed.simps)

   apply (simp only: ed.simps ed'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: ed.simps)

   apply (simp only: ed.simps ed'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: ed.simps)
  done
term "(a :: nat) - (b :: nat)"

context
  fixes w :: "nat \<Rightarrow> nat"
begin

fun su :: "(nat\<times>nat) \<Rightarrow> nat" where
  "su (0, W) = (if W < w 0 then 0 else w 0)" |
  "su (Suc i, W) = (if W < w (Suc i)
    then su (i, W)
    else max (su (i, W)) (w i + su (i, W - w i)))"

fun su' :: "(nat\<times>nat, nat) dpfun" where
  "su' (0, W) = checkmem (0,W) (if W < w 0 then \<langle>0\<rangle> else \<langle>w 0\<rangle>)" |
  "su' (Suc i, W) = checkmem (Suc i,W) (if W < w (Suc i)
    then su' (i, W)
    else max\<^sub>s (su' (i, W)) (\<langle>w i\<rangle> +\<^sub>s su' (i, W - w i)))"

lemma "consistentDF su su'"
  apply (unfold consistentDF_def, rule allI, induct_tac rule: su.induct)
   apply (simp only: su.simps su'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: su.simps)

   apply (simp only: su.simps su'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: su.simps)
  done
end

context
  fixes v :: "nat \<Rightarrow> nat"
    and p :: "nat \<Rightarrow> nat"
  assumes p_lt: "p (Suc j) < Suc j"
begin


text \<open>Dimensionality given by i\<close>
function wis :: "nat \<Rightarrow> nat" where
  "wis 0 = 0" |
  "wis (Suc i) = max (wis (p (Suc i)) + v i) (wis i)"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

function wis' :: "(nat, nat) dpfun" where
  "wis' 0 = checkmem 0 (\<langle>0\<rangle>)" |
  "wis' (Suc i) = checkmem (Suc i) (max\<^sub>s (wis' (p (Suc i)) +\<^sub>s \<langle>v i\<rangle>) (wis' i))"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

lemma "consistentDF wis wis'"
  apply (rule consistentDF_I, induct_tac param rule: wis.induct)
   apply (simp only: wis.simps wis'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: wis.simps)

   apply (simp only: wis.simps wis'.simps)
   apply (assumption | rule consistency_rules HOL.refl)+
   apply (simp only: wis.simps)
    
  done
end