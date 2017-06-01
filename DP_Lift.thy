theory DP_Lift
  imports Main "~~/src/HOL/Library/State_Monad"
begin

type_synonym ('s, 'a) state = "'s \<Rightarrow> ('a \<times> 's)"
type_synonym ('param, 'result) dpstate = "('param \<rightharpoonup> 'result, 'result) state"
type_synonym ('param, 'result) dpfun = "'param \<Rightarrow> ('param, 'result) dpstate" (infixr "\<Rightarrow>\<^sub>s" 2)

definition return :: "'a \<Rightarrow> ('s, 'a) state" ("\<langle>_\<rangle>") where
  "\<langle>x\<rangle> = (\<lambda>M. (x, M))"
fun get :: "('s, 's) state" where
  "get M = (M, M)"
fun put :: "'s \<Rightarrow> ('s, unit) state" where
  "put M _ = ((), M)"

definition lift_fun_app :: "('M,'a\<Rightarrow>'b) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state" (infixl "." 999) where
  "lift_fun_app sf sv \<equiv> exec {f \<leftarrow> sf; v \<leftarrow> sv; \<langle>f v\<rangle>}"
definition If\<^sub>s :: "('M,bool) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'a) state" ("(if\<^sub>s (_)/ then\<^sub>s (_)/ else\<^sub>s (_))" [0, 0, 10] 10)
  where "If\<^sub>s P x y \<equiv> exec {p \<leftarrow> P; if p then x else y}"
definition lift_binary :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'c) state" where
  "lift_binary f s0 s1 \<equiv> \<langle>f\<rangle> . s0 . s1"

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

abbreviation dpfun_checkmem_eq ("(_/ $ _/ =CHECKMEM= _)"  [1000, 51] 51) where
  "f $ param =CHECKMEM= result \<equiv> f param = checkmem param result"

lemma lift_fun_appE:
  assumes "(sf . sv) M = (v', M')"
  obtains f M'' v where "sf M = (f,M'')" and "sv M'' = (v,M')" and "v' = f v"
  using assms unfolding lift_fun_app_def return_def by (auto split: prod.splits)

primrec fold\<^sub>s :: "('M,'a \<Rightarrow> 'b \<Rightarrow> 'b) state \<Rightarrow> ('M,'a) state list \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'b) state" where
fold\<^sub>s_Nil:  "fold\<^sub>s f [] init = init" |
fold\<^sub>s_Cons: "fold\<^sub>s f (x # xs) init = fold\<^sub>s f xs (f . x . init)"

abbreviation "max\<^sub>s \<equiv> lift_binary max"
abbreviation "min\<^sub>s \<equiv> lift_binary min"
abbreviation plus_state (infixl "+\<^sub>s" 65) where "op +\<^sub>s \<equiv> lift_binary (op +)"

end