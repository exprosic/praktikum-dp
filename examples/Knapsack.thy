theory Knapsack
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
begin

context (* Knapsack *)
  fixes w :: "nat \<Rightarrow> nat"
begin

fun su :: "nat\<times>nat \<Rightarrow> nat" where
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

end