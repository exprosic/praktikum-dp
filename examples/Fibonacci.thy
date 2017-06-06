theory Fibonacci
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
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

end