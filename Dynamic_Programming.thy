theory Dynamic_Programming
  imports Main "~~/src/HOL/Library/State_Monad"
begin
  
type_synonym ('s, 'a) state = "'s \<Rightarrow> ('a \<times> 's)"
type_synonym ('param, 'result) dpstate = "('param \<rightharpoonup> 'result, 'result) state"
type_synonym ('param, 'result) dpfun = "'param \<Rightarrow> ('param, 'result) dpstate"
  
fun return :: "'a \<Rightarrow> ('s, 'a) state" ("\<langle>_\<rangle>") where
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
  
definition lift_binary :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'c) state" where
  "lift_binary f s0 s1 \<equiv> exec {v0 \<leftarrow> s0; v1 \<leftarrow> s1; \<langle>f v0 v1\<rangle>}"
definition plus_state (infixl "+\<^sub>s" 65) where "op +\<^sub>s \<equiv> lift_binary (op +)"
definition min\<^sub>s where "min\<^sub>s \<equiv> lift_binary min"
definition max\<^sub>s where "max\<^sub>s \<equiv> lift_binary max"

definition consistentM :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<rightharpoonup> 'result) \<Rightarrow> bool" where
  "consistentM f M \<equiv> \<forall>param\<in>dom M. M param = Some (f param)"
  
definition consistentS :: "('param \<Rightarrow> 'result) \<Rightarrow> 'result \<Rightarrow> ('param, 'result) dpstate \<Rightarrow> bool" where
  "consistentS f v s \<equiv> \<forall>M. consistentM f M \<longrightarrow> fst (s M) = v \<and> consistentM f (snd (s M))"

definition consistentDF :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param, 'result) dpfun \<Rightarrow> bool" where
  "consistentDF f d \<equiv> \<forall>param. consistentS f (f param) (d param)"

lemma consistent_binary:
  assumes c0:"consistentS f v0 s0" and c1:"consistentS f v1 s1"
    shows "consistentS f (g v0 v1) (lift_binary g s0 s1)" (is ?case)
proof -
  {
    fix M assume m0: "consistentM f M"
    let ?gvv="g v0 v1" and ?gss="lift_binary g s0 s1"
      
    obtain v0' M0 where p0: "s0 M = (v0',M0)" by fastforce
    with c0 m0 have "v0=v0'" and m1: "consistentM f M0" unfolding consistentS_def by fastforce+
    moreover
    obtain v1' M1 where p1: "s1 M0 = (v1',M1)" by fastforce
    with c1 m1 have "v1=v1'" and m2: "consistentM f M1" unfolding consistentS_def by fastforce+
    moreover
    from p0 p1 have pg: "?gss M = (g v0' v1', M1)" unfolding lift_binary_def by simp
    ultimately
    have "fst (?gss M) = ?gvv" "consistentM f (snd (?gss M))" by auto
  }
  thus ?case unfolding consistentS_def by simp
qed
  
corollary consistent_plus:
  "consistentS f v0 s0 \<Longrightarrow> consistentS f v1 s1 \<Longrightarrow> consistentS f (v0+v1) (s0+\<^sub>ss1)"
  unfolding plus_state_def using consistent_binary[where g="op +"] .

lemma consistentM_upd: "consistentM f M \<Longrightarrow> consistentM f (M(param\<mapsto>f param))"
  unfolding consistentM_def by auto

lemma consistentS_update: 
  assumes prem: "consistentS f (f param) s"
  shows "consistentS f (f param) (update param s)" (is ?thesis)
proof -
  {
    fix M assume cm: "consistentM f M"
    have "fst (update param s M) = f param \<and> consistentM f (snd (update param s M))"
      using prem[unfolded consistentS_def, THEN spec, THEN mp, OF cm]
      by (auto simp: consistentM_upd split: prod.splits)
  }
  thus ?thesis unfolding consistentS_def by auto
qed

lemma consistent_checkmem:
  assumes prem: "consistentS f (f param) s"
  shows "consistentS f (f param) (checkmem param s)" (is ?case)
proof -
  {
    fix M assume *: "consistentM f M"
    have "fst (checkmem param s M) = f param \<and> consistentM f (snd (checkmem param s M))"
      apply (cases "param \<in> dom M")
        using * apply (auto simp: consistentM_def)[]
        using consistentS_update[OF prem] * by (auto simp: consistentS_def)
  }
  thus ?case unfolding consistentS_def by simp
qed

(* Fib *)

fun fib :: "nat \<Rightarrow> nat" where
"fib 0 = 0" |
"fib (Suc 0) = 1" |
"fib (Suc(Suc n)) = fib(Suc n) + fib n"

fun fib' :: "(nat, nat) dpfun" where
  "fib' param = checkmem param (case param of
    0 => \<langle>0\<rangle> |
    Suc 0 => \<langle>1\<rangle> |
    Suc (Suc n) => fib' (Suc n) +\<^sub>s fib' n
  )"

lemma fib'_simps:
  "fib' 0 = checkmem 0 \<langle>0\<rangle>"
  "fib' 1 = checkmem 1 \<langle>1\<rangle>"
  "fib' (Suc (Suc n)) = checkmem (Suc (Suc n)) (fib' (Suc n) +\<^sub>s fib' n)"
  by auto
  
lemma "fst (fib' 0 empty) = fib 0"
  by (auto)

lemma "consistentM fib M \<Longrightarrow> consistentM fib (snd (fib' n M))"
  apply (induction n arbitrary: M rule: fib.induct)
    apply (auto simp: dom_def consistentM_def split: option.splits)[]
   apply (auto simp: dom_def consistentM_def split: option.splits)[]
  oops

lemma "consistentDF fib fib'"
  unfolding consistentDF_def
    apply rule
  apply (induct_tac param rule: fib.induct)
    apply (auto simp: consistentS_def dom_def consistentM_def split: option.splits)[2]
proof -
    fix n
    show "consistentS fib (fib (Suc n)) (fib' (Suc n)) \<Longrightarrow>
          consistentS fib (fib n) (fib' n) \<Longrightarrow>
          consistentS fib (fib (Suc (Suc n))) (fib' (Suc (Suc n)))"
      apply (simp only: fib'_simps(3))
      apply (rule consistent_checkmem)
      apply (simp only: fib.simps(3))
      apply (rule consistent_plus)
      .
  qed

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
  "bf' params = checkmem params (case params of
    (0, j) => \<langle>W 0 j\<rangle> |
    (Suc k, j) => fold min\<^sub>s [bf' (k, i) +\<^sub>s \<langle>W i j\<rangle>. i\<leftarrow>[0..<n]] (bf' (k, j)))"

    

end

text \<open>Not primrec\<close>
text \<open>Dimensionality given by i, j\<close>
fun ed :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ed 0 0 = 0" |
  "ed 0 (Suc j) = Suc j" |
  "ed (Suc i) 0 = Suc i" |
  "ed (Suc i) (Suc j) = min (ed i j + 2) (min (ed (Suc i) j + 1) (ed i (Suc j) + 1))"

fun ed' :: "(nat\<times>nat, nat) dpfun" where
  "ed' params = checkmem params (case params of
    (0, 0) => \<langle>0\<rangle> |
    (0, Suc j) => \<langle>Suc j\<rangle> |
    (Suc i, 0) => \<langle>Suc i\<rangle> |
    (Suc i, Suc j) => min\<^sub>s (ed' (i, j) +\<^sub>s \<langle>2\<rangle>) (min\<^sub>s (ed' (Suc i, j) +\<^sub>s \<langle>1\<rangle>) (ed' (i, Suc j) +\<^sub>s \<langle>1\<rangle>)))"
thm minus_nat_inst.minus_nat

term "(a :: nat) - (b :: nat)"

context
  fixes w :: "nat \<Rightarrow> nat"
begin

fun su :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "su 0 W = (if W < w 0 then 0 else w 0)" |
  "su (Suc i) W = (if W < w (Suc i)
    then su i W
    else max (su i W) (w i + su i (W - w i)))"
  
fun su' :: "(nat\<times>nat, nat) dpfun" where
  "su' params = checkmem params (case params of
    (0, W) => if W < w 0 then \<langle>0\<rangle> else \<langle>w 0\<rangle> |
    (Suc i, W) => if W < w (Suc i)
      then su' (i, W)
      else max\<^sub>s (su' (i, W)) (\<langle>w i\<rangle> +\<^sub>s su' (i, W - w i)))"
end

context
  fixes v :: "nat \<Rightarrow> nat"
begin

definition p :: "nat \<Rightarrow> nat" where "p j = 0"

lemma p_lt:
  "p (Suc j) < (Suc j)"
  unfolding p_def by simp

text \<open>Dimensionality given by i\<close>
function wis :: "nat \<Rightarrow> nat" where
  "wis 0 = 0" |
  "wis (Suc i) = max (wis (p (Suc i)) + v i) (wis i)"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)
    
function wis' :: "(nat, nat) dpfun" where
  "wis' params = checkmem params (case params of
    0 => \<langle>0\<rangle> |
    Suc i => max\<^sub>s (wis' (p (Suc i)) +\<^sub>s \<langle>v i\<rangle>) (wis' i))"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

end