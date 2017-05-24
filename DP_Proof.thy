theory DP_Proof
  imports DP_Consistency "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

method dp_match uses induct simp =
  (
    rule consistentDF_I,
    induct_tac rule: induct,
    (
      simp only: simp,
      (assumption | rule consistency_rules HOL.refl)+,
      simp only: simp
    )+
  )
end