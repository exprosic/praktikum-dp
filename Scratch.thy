theory Scratch imports        
  Main
begin
  
abbreviation f where "f g \<equiv> g"

fun bf :: "nat \<Rightarrow> int" where
  "bf 0 = 0"

end