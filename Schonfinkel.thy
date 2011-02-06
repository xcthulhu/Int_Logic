header {* Sch\"onfinkel's Embedding *}

theory Schonfinkel
imports Main
begin

text {*  In this article we provide the Sch\"onfinkel embedding of
         the $\lambda$-calculus into the $SKI$ combinator algebra. *}

section {* SKI Embedding *}

text {* The Curry Howard isomorphism, in its most basic form, 
is the observation that the theorems of minimal logic correspond to programs 
one may express in the pure typed functional $\lambda$ calculus. *}

text {* In this section we develop machinery which will allow us to give programs
as proofs for propositions in minimal logic.  We accomplish this by exhibiting two 
type-equivalent embeddings the $\lambda$ calculus in the SKI calculus, due to Sch\"onfinkel. 
We might eventually want to adapt Induct/Comb.thy for what we do below.  
On the other hand, since we are not really interested in the Church-Rosser confluence 
theorem here, it may be best to leave our developments seperate.  *}

datatype 'a ski = 
    At   "'a"                      ("(1<_>)")
  | Comb "'a ski" "'a ski"         (infixl "\<bullet>" 100)
  | S_ski ("S'") 
  | K_ski ("K'") 
  | I_ski ("I'")

--{* Sch\"onfinkel's abstraction *}
primrec Schonfinkel0 :: "'a \<Rightarrow> 'a ski \<Rightarrow> 'a ski"  ("\<Delta>0")
  where 
     "(\<Delta>0 x) <y> = (if (x = y) then I' else (K'\<bullet><y>))"
  |  "(\<Delta>0 x) S' = (K'\<bullet>S')"
  |  "(\<Delta>0 x) K' = (K'\<bullet>K')"
  |  "(\<Delta>0 x) I' = (K'\<bullet>I')"
  |  "(\<Delta>0 x) (A\<bullet>B) = (S'\<bullet>((\<Delta>0 x) A)\<bullet>((\<Delta>0 x) B))"

--{* Below is a refinement on Sch\"onfinkel's abstraction *}
--{* It includes a check to whether the abstracted variable is free *}
primrec Schonfinkel_free :: "'a ski \<Rightarrow> 'a set" ("free") where
     "free <y> = {y}"
  |  "free S' = {}"
  |  "free K' = {}"
  |  "free I' = {}"
  |  "free (A\<bullet>B) = (free A) \<union> (free B)"

fun Schonfinkel :: "'a \<Rightarrow> 'a ski \<Rightarrow> 'a ski"  ("\<Delta>")
  where 
     "(\<Delta> x) A = (if (x ~: free A) then (K'\<bullet>A) else
        (case A of   <y> \<Rightarrow> I' |
                   (C\<bullet>D) \<Rightarrow> (S'\<bullet>((\<Delta> x) C)\<bullet>((\<Delta> x) D))))"

--{* Repeated abstractions *}
primrec LamAbs0 :: "'a list \<Rightarrow> 'a ski \<Rightarrow> 'a ski"  ("(\<Lambda>0_/ _)" [50, 51] 50)
  where 
    "\<Lambda>0[] y = y"
  | "\<Lambda>0(x # xs) y = (\<Delta>0 x (\<Lambda>0 xs y))"

primrec LamAbs :: "'a list \<Rightarrow> 'a ski \<Rightarrow> 'a ski"  ("(\<Lambda>_/ _)" [50, 51] 50)
  where 
    "\<Lambda>[] y = y"
  | "\<Lambda>(x # xs) y = (\<Delta> x (\<Lambda> xs y))"

text {* In practice, this type can be used for to give variables, 
        which can be checked for equality with simp. As we will see, 
        these will let us quickly compose programs in the $\lambda$ 
        calculus we have developed above. *}

datatype vars =
    var1  ("X")
  | var2  ("Y")
  | var3  ("Z")
  | var4  ("X'")
  | var5  ("Y'")
  | var6  ("Z'")

end