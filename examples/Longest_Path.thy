theory Longest_Path
  imports "../DP_Lift" "../DP_Consistency" "../DP_Proof"
begin

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