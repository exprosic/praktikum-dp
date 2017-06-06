theory Grid_Path
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
begin

context (* *)
begin

text \<open>Not primrec\<close>
text \<open>Dimensionality given by i, j\<close>
fun ed :: "nat\<times>nat \<Rightarrow> nat" where
  "ed (0, 0) = 0" |
  "ed (0, Suc j) = Suc j" |
  "ed (Suc i, 0) = Suc i" |
  "ed (Suc i, Suc j) = min (ed (i, j) + 2) (min (ed (Suc i, j) + 1) (ed (i, Suc j) + 1))"

fun ed'  :: "nat\<times>nat \<Rightarrow>\<^sub>s nat" where
  "ed'$ (0, 0) =CHECKMEM= \<langle>0\<rangle>" |
  "ed'$ (0, Suc j) =CHECKMEM= \<langle>Suc j\<rangle>" |
  "ed'$ (Suc i, 0) =CHECKMEM= \<langle>Suc i\<rangle>" |
  "ed'$ (Suc i, Suc j) =CHECKMEM= min\<^sub>s (ed' (i, j) +\<^sub>s \<langle>2\<rangle>) (min\<^sub>s (ed' (Suc i, j) +\<^sub>s \<langle>1\<rangle>) (ed' (i, Suc j) +\<^sub>s \<langle>1\<rangle>))"

lemma "consistentDF ed ed'"
  by (dp_match induct: ed.induct simp: ed.simps ed'.simps)

end

end