header {* Notation Fixes *}

theory FixNotation
imports Schonfinkel SKI
begin 

context SKI begin
no_notation
  vdash ("\<turnstile> _" [10] 10) and
  impl (infixr "\<rightarrow>" 85) and 
  ap (infixl "\<cdot>" 85) and
  interp ("\<rhd>") and
  comb_comp (infixl "\<circ>" 85)
end

context SKI_bot begin
no_notation
  vdash ("\<turnstile> _" [10] 10) and
  impl (infixr "\<rightarrow>" 85) and 
  ap (infixl "\<cdot>" 85) and
  neg ("\<not> _" [90] 90) and
  bot ("\<bottom>")
end

context SKI_top begin
no_notation
  vdash ("\<turnstile> _" [10] 10) and
  impl (infixr "\<rightarrow>" 85) and 
  ap (infixl "\<cdot>" 85) and
  top ("\<top>")
end

no_notation
 "Pair" ("_:_" [70, 71] 70) and
  At ("(1<_>)") and
  Comb (infixl "\<bullet>" 100) and
  S_ski ("S'") and 
  K_ski ("K'") and
  I_ski ("I'") and
  Schonfinkel0 ("\<Delta>0") and
  Schonfinkel ("\<Delta>") and
  LamAbs0 ("(\<Lambda>0_/ _)" [50, 51] 50) and
  LamAbs ("(\<Lambda>_/ _)" [50, 51] 50) and
  var1  ("X") and
  var2  ("Y") and
  var3  ("Z") and
  var4  ("X'") and
  var5  ("Y'") and
  var6  ("Z'")

notation
  "op :"  ("op \<in>") and
  "op :"  ("(_/ \<in> _)" [50, 51] 50) and 
  "op :"  ("(_/ : _)" [50, 51] 50) and 
  comp  (infixl "\<circ>" 55) and
  Not  ("\<not> _" [40] 40) and
  "op &"  (infixr "\<and>" 35)

end