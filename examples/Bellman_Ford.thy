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

definition upt\<^sub>s :: "nat \<Rightarrow> nat \<Rightarrow> ('M,nat) state list" where
  "upt\<^sub>s l r \<equiv> map return (upt l r)"
definition fun_app :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 51) where
  "f$ x = f x"
definition rev_scomp :: "('a \<Rightarrow> ('M,'b) state) \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state" (infixl "\<leftarrow>\<circ>" 60) where
  "rev_scomp s f \<equiv> scomp f s"

fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0, j) = W 0 j" |
  "bf (Suc k, j) = fold min (map ((op $) (\<lambda>i. bf (k, i) + W i j)) (upt 0 n)) (bf (k, j))"
thm bf.simps
  
fun bf' :: "nat\<times>nat \<Rightarrow>\<^sub>s int" where
  "bf'$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>" |
  "bf'$ (Suc k, j) =CHECKMEM= fold min\<^sub>s (map ((op \<leftarrow>\<circ>) (\<lambda>i. bf' (k, i) +\<^sub>s \<langle>W i j\<rangle>)) (upt\<^sub>s 0 9)) (bf' (k, j))"


lemma "consistentDF bf bf'"
  oops
end