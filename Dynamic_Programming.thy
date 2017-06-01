theory Dynamic_Programming
  imports DP_Lift DP_Consistency DP_Proof
begin

context (* Fibonacci *)
begin

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0" |
  "fib (Suc 0) = 1" |
  "fib (Suc(Suc n)) = fib (Suc n) + fib n"

fun fib' :: "nat \<Rightarrow>\<^sub>s nat" where
  "fib'$ 0 =CHECKMEM= \<langle>0\<rangle>" |
  "fib'$ (Suc 0) =CHECKMEM= \<langle>1\<rangle>" |
  "fib'$ (Suc (Suc n)) =CHECKMEM= fib' (Suc n) +\<^sub>s fib' n"

lemma "consistentDF fib fib'"
  by (dp_match induct: fib.induct simp: fib.simps fib'.simps)

end

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

fun bf' :: "nat\<times>nat \<Rightarrow>\<^sub>s int" where
  "bf'$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>" |
  "bf'$ (Suc k, j) =CHECKMEM= fold\<^sub>s \<langle>min\<rangle> [bf' (k, i) +\<^sub>s \<langle>W i j\<rangle>. i\<leftarrow>[0..<n]] (bf' (k, j))"

lemma "consistentDF bf bf'"
  by (dp_match induct: bf.induct simp: bf.simps bf'.simps)

end

context (* *)
begin

text \<open>Not primrec\<close>
text \<open>Dimensionality given by i, j\<close>
fun ed :: "(nat\<times>nat) \<Rightarrow> nat" where
  "ed (0, 0) = 0" |
  "ed (0, Suc j) = Suc j" |
  "ed (Suc i, 0) = Suc i" |
  "ed (Suc i, Suc j) = min (ed (i, j) + 2) (min (ed (Suc i, j) + 1) (ed (i, Suc j) + 1))"

fun ed'  :: "nat\<times>nat \<Rightarrow>\<^sub>s nat" where
  "ed'$ (0, 0) = \<langle>0\<rangle>" |
  "ed'$ (0, Suc j) = \<langle>Suc j\<rangle>" |
  "ed'$ (Suc i, 0) = \<langle>Suc i\<rangle>" |
  "ed'$ (Suc i, Suc j) = min\<^sub>s (ed' (i, j) +\<^sub>s \<langle>2\<rangle>) (min\<^sub>s (ed' (Suc i, j) +\<^sub>s \<langle>1\<rangle>) (ed' (i, Suc j) +\<^sub>s \<langle>1\<rangle>))"

lemma "consistentDF ed ed'"
  by (dp_match induct: ed.induct simp: ed.simps ed'.simps)

end

context (* Knapsack *)
  fixes w :: "nat \<Rightarrow> nat"
begin

fun su :: "(nat\<times>nat) \<Rightarrow> nat" where
  "su (0, W) = (if W < w 0 then 0 else w 0)" |
  "su (Suc i, W) = (if W < w (Suc i)
    then su (i, W)
    else max (su (i, W)) (w i + su (i, W - w i)))"

fun su' :: "nat\<times>nat \<Rightarrow>\<^sub>s nat" where
  "su'$ (0, W) =CHECKMEM= (if\<^sub>s \<langle>W < w 0\<rangle> then\<^sub>s \<langle>0\<rangle> else\<^sub>s \<langle>w 0\<rangle>)" |
  "su'$ (Suc i, W) =CHECKMEM= (if\<^sub>s \<langle>W < w (Suc i)\<rangle>
    then\<^sub>s su' (i, W)
    else\<^sub>s max\<^sub>s (su' (i, W)) (\<langle>w i\<rangle> +\<^sub>s su' (i, W - w i)))"
  
lemma "consistentDF su su'"
  by (dp_match induct: su.induct simp: su.simps su'.simps)

end

context (* Longest path *)
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

function wis' :: "nat \<Rightarrow>\<^sub>s nat" where
  "wis'$ 0 =CHECKMEM= \<langle>0\<rangle>" |
  "wis'$ (Suc i) =CHECKMEM= max\<^sub>s (wis' (p (Suc i)) +\<^sub>s \<langle>v i\<rangle>) (wis' i)"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

lemma "consistentDF wis wis'"
  by (dp_match induct: wis.induct simp: wis.simps wis'.simps)

end
  
end