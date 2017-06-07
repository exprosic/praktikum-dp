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
  apply (rule consistentDF_I)
  apply (induct_tac rule: su'.induct)
  apply (simp only: su.simps su'.simps)
   apply (rule consistentS_checkmem)
    apply (rule consistentS_cond)
      apply (rule consistentS_return HOL.refl)+
   apply (simp only: su.simps su'.simps)
  apply (simp only: su.simps su'.simps)
  apply (rule consistentS_checkmem)
   apply (rule consistentS_cond)
     apply (rule consistentS_return HOL.refl | assumption)+
   apply (rule consistentS_binary)
    apply (rule consistentS_return HOL.refl | assumption)+
   apply (rule consistentS_binary)
    apply (rule consistentS_return)
    apply (rule consistentS_return HOL.refl | assumption)+
  apply (simp only: su.simps su'.simps)
  done
    
    
thm su.induct su'.induct
fun f :: "nat \<Rightarrow> nat" where
  "f 0 = 0" |
  "f (Suc x) = (let b=1 in (if 3<x then f x else b + x))"
thm f.induct
  term None
 (* by (dp_match induct: su.induct simp: su.simps su'.simps)*)

end

end