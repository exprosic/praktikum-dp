theory Fib
imports Main
begin

subsection "Basic Functions"

text \<open>This set of basic functions assumes that the function to be tabulated (\<open>f\<close>)
has type \<open>nat \<Rightarrow> nat\<close>. This needs to be adjusted for other types.
In the worst case one may have to redefine these basic functions on the fly
to suit particular \<open>f\<close>'s.\<close>

type_synonym tab = "nat \<Rightarrow> nat option"

text \<open>Defined to avoid \<open>\<noteq> None\<close> because that gets modified by the standard
simplifier and rule setup.\<close>
definition is_None :: "'a option \<Rightarrow> bool" where
"is_None x = (x = None)"

text \<open>Partial correctness of table wrt function:\<close>
definition pcorrect :: "(nat \<Rightarrow> nat) \<Rightarrow> tab \<Rightarrow> bool" where
"pcorrect f t = (\<forall>i. \<not> is_None (t i) \<longrightarrow> the(t i) = f i)"

lemma pcorrect_upd:
  "pcorrect f t \<Longrightarrow> m = f n \<Longrightarrow> pcorrect f (t(n := Some m))"
by (simp add: pcorrect_def)

lemma pcorrect_not_None:
  "pcorrect f t \<Longrightarrow> m = f n \<Longrightarrow> \<not> is_None (t n) \<Longrightarrow> (t n = Some m) = True"
by(auto simp add: pcorrect_def is_None_def)

lemma map_le_updR: "t \<subseteq>\<^sub>m t' \<Longrightarrow> is_None (t n) \<Longrightarrow> t \<subseteq>\<^sub>m t'(n \<mapsto> m)"
by (metis is_None_def fun_upd_triv map_le_imp_upd_le)

lemma map_le_id_upR: "pcorrect f t \<Longrightarrow> f n = m \<Longrightarrow> t \<subseteq>\<^sub>m t(n \<mapsto> m)"
apply(simp add: pcorrect_def)
by (metis fun_upd_triv map_le_imp_upd_le map_le_refl map_le_updR option.exhaust_sel)

subsection "Application fib"

fun fib :: "nat \<Rightarrow> nat" where
"fib 0 = 0" |
"fib (Suc 0) = 1" |
"fib (Suc(Suc n)) = fib(Suc n) + fib n"

fun fib' :: "nat \<Rightarrow> tab \<Rightarrow> tab" where
"fib' 0 t = (if is_None (t 0) then t(0 := Some 0) else t)" |
"fib' (Suc 0) t = (if is_None (t 1) then t(1 := Some 1) else t)" |
"fib' (Suc(Suc n)) t = (if is_None(t (Suc(Suc n))) then
   let t1 = fib' (Suc n) t; t2 = fib' n t1
   in t2((Suc(Suc n)) := Some(the(t1(Suc n)) + the(t2 n))) else t)"

text \<open>A first proof where the proposition consists of 3 conjuncts:\<close>

lemma fib'_correct_aux: "pcorrect fib t \<Longrightarrow>
  t \<subseteq>\<^sub>m fib' n t \<and> pcorrect fib (fib' n t) \<and> fib' n t n = Some(fib n)"
proof(induction n arbitrary: t rule: fib.induct)
  case 1
  show ?case (is "?A \<and> ?B \<and> ?C")
  proof (intro conjI)
    show ?A using 1 by (simp add: map_le_id_upR del: fun_upd_apply)
    show ?B using 1 by(simp add: pcorrect_upd del: fun_upd_apply)
    show ?C using 1 using [[simp_depth_limit=3]] by (simp add: pcorrect_not_None)
  qed
next
  case 2
  show ?case (is "?A \<and> ?B \<and> ?C")
  proof (intro conjI)
    show ?A using 2 by (simp add: map_le_id_upR del: fun_upd_apply)
    show ?B using 2 by(simp add: pcorrect_upd del: fun_upd_apply)
    show ?C using 2 using [[simp_depth_limit=3]] by (simp add: pcorrect_not_None)
  qed
next
  case (3 n)
  note IH1 = "3.IH"(1)[OF "3.prems"]
  note IH2 = "3.IH"(2)[OF conjunct1[OF conjunct2[OF IH1]]]
  note map_le = map_le_trans[OF conjunct1[OF IH1] conjunct1[OF IH2]]
  note pcorr = conjunct1 [OF conjunct2[OF IH2]]
  note result1 = conjunct2 [OF conjunct2[OF IH1]]
  note result2 = conjunct2 [OF conjunct2[OF IH2]]
  show ?case (is "?A \<and> ?B \<and> ?C")
  proof (intro conjI)
    show ?A apply (auto simp: Let_def)
      by(erule map_le_updR[OF map_le])
    show ?B using "3.prems"
      apply(auto simp: result1 result2 Let_def)
      apply(rule pcorrect_upd[OF pcorr])
      apply simp
      done
    show ?C using "3.prems"
      by (simp add: result1 result2 Let_def pcorrect_not_None)
  qed
qed

corollary fib'_correct: "fib' n empty n = Some(fib n)"
using fib'_correct_aux[of empty n]
by(simp add: pcorrect_def is_None_def)

text \<open>Second proof where parts of the main proposition are hidden in a definition:\<close>

definition correct_tab :: "(nat \<Rightarrow> nat) \<Rightarrow> tab \<Rightarrow> tab \<Rightarrow> bool" where
"correct_tab f t t' = (t \<subseteq>\<^sub>m t' \<and> pcorrect f t')"

lemma pcorrect_if_correct_tab: "correct_tab f t t' \<Longrightarrow> pcorrect f t'"
by(simp add: correct_tab_def)

lemma correct_tab_id:
  "pcorrect f t \<Longrightarrow> correct_tab f t t"
by(auto simp: correct_tab_def)

lemma correct_tab_upd1:
  "pcorrect f t \<Longrightarrow> f n = m \<Longrightarrow> correct_tab f t (t(n \<mapsto> m))"
by(auto simp: correct_tab_def map_le_id_upR pcorrect_upd)

lemma correct_tab_upd2:
  "\<lbrakk> pcorrect f t; correct_tab f t t'; f n = m \<rbrakk>
  \<Longrightarrow> correct_tab f t (t'(n \<mapsto> m))"
by (meson correct_tab_def map_le_id_upR map_le_trans pcorrect_upd)

lemma correct_tab_trans:
  "correct_tab f t t' \<Longrightarrow> correct_tab f t' t'' \<Longrightarrow> correct_tab f t t''"
by(auto simp: correct_tab_def intro: map_le_trans)

lemma fib'_correct_aux2: "pcorrect fib t \<Longrightarrow>
  correct_tab fib t (fib' n t) \<and> fib' n t n = Some(fib n)"
proof(induction n arbitrary: t rule: fib.induct)
  case 1
  show ?case
    using 1 by (simp add: correct_tab_id correct_tab_upd1 pcorrect_not_None)
next
  case 2
  show ?case
    using 2 by (simp add: correct_tab_id correct_tab_upd1 pcorrect_not_None)
next
  case 3
  note IH1 = "3.IH"(1)[OF "3.prems"]
  note corrtab1 = conjunct1[OF IH1]
  note IH2 = "3.IH"(2)[OF pcorrect_if_correct_tab[OF corrtab1]]
  note corrtab2 = conjunct1[OF IH2]
  note corrtab12 = correct_tab_trans[OF corrtab1 corrtab2]
  note results = conjunct2[OF IH1] conjunct2[OF IH2]
  show ?case
    apply(auto simp: correct_tab_id[OF "3.prems"] pcorrect_not_None[OF "3.prems"] results Let_def)
    apply(rule correct_tab_upd2[OF "3.prems" corrtab12])
    by (simp add: results)
qed

corollary fib'_correct2: "fib' n empty n = Some(fib n)"
using fib'_correct_aux2[of empty n]
by(simp add: pcorrect_def is_None_def)

end