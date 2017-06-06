theory Bellman_Ford
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
begin

(* Bellman Ford *)

context
  fixes W :: "nat \<Rightarrow> nat \<Rightarrow> int"
    and n :: nat
begin

text \<open>Could also be primrec\<close>
text \<open>Dimensionality as parameter\<close>

fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0, j) = W 0 j" |
  "bf (Suc k, j) = fold min [bf (k, i) + W i j. i\<leftarrow>[0..<n]] (bf (k, j))"

fun bf' :: "nat\<times>nat \<Rightarrow>\<^sub>s int" where
  "bf'$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>" |
  "bf'$ (Suc k, j) =CHECKMEM= fold\<^sub>s \<langle>min\<rangle> [bf' (k, i) +\<^sub>s \<langle>W i j\<rangle>. i\<leftarrow>[0..<n]] (bf' (k, j))"

lemma "consistentDF bf bf'"
  by (dp_match induct: bf.induct simp: bf.simps bf'.simps)

end

end