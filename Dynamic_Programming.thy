theory Dynamic_Programming
  imports Main "~~/src/HOL/Library/State_Monad"
begin
  
type_synonym ('s, 'a) state = "'s \<Rightarrow> ('a \<times> 's)"
type_synonym ('param, 'result) dpstate = "('param \<rightharpoonup> 'result, 'result) state"
type_synonym ('param, 'result) dpfun = "'param \<Rightarrow> ('param, 'result) dpstate"
  
fun return :: "'a \<Rightarrow> ('s, 'a) state" ("\<langle>_\<rangle>") where
  "\<langle>x\<rangle> = (\<lambda>M. (x, M))"
fun apply_function :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 51) where
  "f $ x = f x"
definition get :: "('s, 's) state" where
  "get \<equiv> \<lambda>M. (M, M)"
definition put :: "'s \<Rightarrow> ('s, unit) state" where
  "put s \<equiv> \<lambda>M. ((), s)"

definition checkmem :: "'param \<Rightarrow> ('param, 'result) dpstate \<Rightarrow> ('param, 'result) dpstate" where
  "checkmem params calcVal \<equiv> exec {
    M \<leftarrow> get;
    case M params of
      Some v => \<langle>v\<rangle> |
      None => exec {
        v \<leftarrow> calcVal;
        M' \<leftarrow> get;
        _ \<leftarrow> put (M'(params\<mapsto>v));
        \<langle>v\<rangle>
      }
    }"
  
lemma [elim!]:
  obtains v where "snd (checkmem params calcVal M) params = Some v"
  oops

(*
fun sequence :: "('param, 'result) state list \<Rightarrow> ('param, 'result list) state" where
  "sequence [] = return []" |
  "sequence (x#xs) = exec {
    v \<leftarrow> x;
    vs \<leftarrow> sequence xs;
    return$ v#vs
  }"

fun fold\<^sub>S' :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('M, 'a) state list \<Rightarrow> ('M, 'b) state \<Rightarrow> ('M, 'b) state" where
  "fold\<^sub>S' f [] init = init" |
  "fold\<^sub>S' f (x#xs) init = exec {
    v \<leftarrow> init;
    v' \<leftarrow> x;
    fold\<^sub>S' f xs (return$ f v' v)
  }"

definition fold\<^sub>S:: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('param, 'a) state list \<Rightarrow> ('param, 'b) state \<Rightarrow> ('param, 'b) state" where
  "fold\<^sub>S f xs init \<equiv> exec {
    initv \<leftarrow> init;
    vs \<leftarrow> sequence xs;
    return$ fold f vs initv
  }"

lemma "fold\<^sub>S = fold\<^sub>S'"
  oops
*)
(*
definition liftl :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('M,'a) state \<Rightarrow> 'b \<Rightarrow> ('M,'c) state" where
  "liftl f s v \<equiv> exec {v0 \<leftarrow> s; return$ f v0 v}"
definition liftr :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'c) state" where
  "liftr f v s \<equiv> exec {v0 \<leftarrow> s; return$ f v v0}"
abbreviation plus_state_val (infixl "\<^sub>s+" 65) where "op \<^sub>s+ \<equiv> liftl (op +)"
abbreviation plus_val_state (infixl "+\<^sub>s" 65) where "op +\<^sub>s \<equiv> liftr (op +)"
*)
definition lift_binary :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state \<Rightarrow> ('M,'c) state" where
  "lift_binary f s0 s1 \<equiv> exec {v0 \<leftarrow> s0; v1 \<leftarrow> s1; return$ f v0 v1}"
definition plus_state (infixl "+\<^sub>s" 65) where "op +\<^sub>s \<equiv> lift_binary (op +)"
definition min\<^sub>s where "min\<^sub>s \<equiv> lift_binary min"
definition max\<^sub>s where "max\<^sub>s \<equiv> lift_binary max"

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

definition pcorrect :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<rightharpoonup> 'result) \<Rightarrow> bool" where
  "pcorrect f M \<equiv> \<forall>param\<in>dom M. M param = Some (f param)"
  
definition consistentDF :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param, 'result) dpfun \<Rightarrow> bool" where
  "consistentDF f d\<equiv> \<forall>M. pcorrect f M \<longrightarrow> (\<forall>param. fst (d param M) = f param)"
  
lemma "consistentDF bf bfmem"
  oops
    
lemma pcorrect_upd:
  "pcorrect f M \<Longrightarrow> v = f param \<Longrightarrow> pcorrect f (M(param\<mapsto>v))"
  by (simp add: pcorrect_def)

lemma pcorrect_not_None:
  "pcorrect f M \<Longrightarrow> v = f param \<Longrightarrow> param \<in> dom M \<Longrightarrow> M param = Some (f param)"
  by(auto simp: pcorrect_def dom_def)

lemma map_le_updR: "M \<subseteq>\<^sub>m M' \<Longrightarrow> param \<notin> dom M \<Longrightarrow> M \<subseteq>\<^sub>m M'(param \<mapsto> v)"
  by (auto simp: dom_def map_le_def)

lemma map_le_id_upR: "pcorrect f M \<Longrightarrow> f param = v \<Longrightarrow> M \<subseteq>\<^sub>m M(param \<mapsto> v)"
  by (auto simp: pcorrect_def map_le_def)

lemma fib'_correct_aux: "pcorrect bf M \<Longrightarrow> M \<subseteq>\<^sub>m snd (bf' param M)"
  apply (induction arbitrary: M rule: bf.induct)
    

end
term 0 (*
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