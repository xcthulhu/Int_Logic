header {* Combinator Calculi *}

theory Combinator_Calculus
imports Main
begin

text {*  In this article we use the Curry-Howard isomorphism
  to provide a $\lambda$-calculus based \emph{Domain Specific Language} (DSL) for rapidly proving theorems 
  in intuitionistic logic. *}

section {* Preliminaries *}

text {* First, we will hijack the notation for @{term "op :"} so we can 
  use it to denote pairs.  We will then use pairs to denote combinator/type 
  combos in our locale for typed combinator calculus. *}

no_notation
  comp  (infixl "\<circ>" 55) and
  Not  ("\<not> _" [40] 40)

notation
  "Pair" ("_:_" [70, 71] 70)

--{* A sanity check *}
lemma "Pair a b = a : b" by auto

locale SKI =
  fixes
       vdash :: "'a \<times> 'b \<Rightarrow> bool"   ("\<turnstile> _" [10] 10)
    and impl :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"     (infixr "\<rightarrow>" 85) 
    and   ap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"     (infixl "\<cdot>" 85)
    and    S :: "'a"
    and    K :: "'a" 
  assumes
        Ktyp [intro]: "\<turnstile> K: \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
    and Styp [intro]: "\<turnstile> S: (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
    and mp [intro]:  "\<lbrakk> \<turnstile> a: \<phi> \<rightarrow> \<psi> ; \<turnstile> b: \<phi> \<rbrakk> \<Longrightarrow> \<turnstile> a\<cdot>b: \<psi> "

text {* As our first result, we define the identity combinator and provide its type. *}

context SKI begin
definition I :: "'a" 
  where "I == S\<cdot>K\<cdot>K"

lemma Ityp [intro]: "\<turnstile> I: \<phi> \<rightarrow> \<phi>"
    by (metis I_def Ktyp Styp mp)
end

section {* SKI Embedding *}

text {* The Curry-Howard isomorphism, in its most basic form, 
is the observation that the theorems of minimal logic correspond to programs 
one may express in the pure typed functional $\lambda$-calculus. *}

text {* In this section we develop machinery which will allow us to give programs
as proofs for propositions in minimal logic.  We accomplish this by exhibiting two 
type-equivalent embeddings the $\lambda$ calculus in the SKI calculus, due to Sch\"onfinkel. 
Unlike the theory developed in  "~~/src/HOL/Induct/Comb", we are not really interested in the Church-Rosser confluence 
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
                (case A of <y>   \<Rightarrow> I' |
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

--{* Some variables to use with simp *}
datatype vars =
    var1  ("X")
  | var2  ("Y")
  | var3  ("Z")
  | var4  ("X'")
  | var5  ("Y'")
  | var6  ("Z'")

context SKI begin

--{* We now show how our concrete SKI calculus 
     may be interpreted in our abstract axiom system. *}

primrec interp :: "'c ski \<Rightarrow> 'a"  ("\<rhd>")
  where 
    "\<rhd> <x> = undefined"
  | "\<rhd> S' = S"
  | "\<rhd> K' = K"
  | "\<rhd> I' = I"
  | "\<rhd> (A\<bullet>B) = (\<rhd>A)\<cdot>(\<rhd>B)"

--{* Sanity check I: an alternative to $K$ using the short embedding *}
lemma "\<turnstile> \<rhd> (\<Lambda>[X,Y] <X>) : \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
by (simp, metis Ityp Ktyp Styp mp)

--{* Sanity check II: $B$ Combinator using the long embedding *}
lemma "\<turnstile> \<rhd> (\<Lambda>0[X,Y,Z] <X>\<bullet>(<Y>\<bullet><Z>)) : (\<chi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  apply simp
  apply blast
done

text {* In practice we will try to use the more efficient Sch\"onfinkel embedding, 
  although it looks like blast does not have a problem with the more combersome
  embedding. *}

text {* While we do not have a formal verification of this, in practice the 
        two embeddings establish equivalent types under interpretation.

        As an aside, we now have at our disposal the sexiest way of proving theorems in 
        minimal logic: exhibit the combinator associated with the desired theorem in the $\lambda$-calculus, 
        and then prove its $SKI$ embedding has the desired type.  One cannot possibly perform this
        with pencil and paper -- but we aren't using pencil and paper, are we?  Since programming and
        type inference are easy, this is arguable the fastest way to coerce the computer to prove
        lots of elementary theorems.
 *}

definition B :: "'a" where
  "B = \<rhd> (\<Lambda>[X,Y,Z] <X>\<bullet>(<Y>\<bullet><Z>))"

lemma Btyp [intro]: "\<turnstile> B : (\<chi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (simp add: B_def, blast)

abbreviation comb_comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<circ>" 85)
where 
   "(x \<circ> y) \<equiv> B\<cdot>x\<cdot>y"

definition C :: "'a" where
  "C = \<rhd> (\<Lambda>[X,Y,Z] <X>\<bullet><Z>\<bullet><Y>)"

lemma Ctyp [intro]: "\<turnstile> C : (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> \<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>" 
 by (simp add: C_def, blast)

definition W :: "'a" where
  "W = \<rhd> (\<Lambda>[X,Y] <X>\<bullet><Y>\<bullet><Y>)"

lemma Wtyp [intro]: "\<turnstile> W : (\<phi> \<rightarrow> \<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>" 
 by (simp add: W_def, blast) 
end

locale SKI_bot = SKI + 
   fixes bot :: "'b" ("\<bottom>")
   assumes "\<bottom> \<rightarrow> \<bottom> = \<bottom> \<rightarrow> \<bottom>"

abbreviation (in SKI_bot) neg :: "'b \<Rightarrow> 'b" ("\<not> _" [90] 90)
  where "neg \<phi> \<equiv> \<phi> \<rightarrow> \<bottom>"

--{* Ex Falso Quodlibet *}

locale EFQ = SKI_bot +
  fixes EFQ :: "'a"
  assumes EFQtyp [intro]: "\<turnstile> EFQ : \<bottom> \<rightarrow> \<phi>"

--{* Three Classical Calculi *}

text{* Minimal logic with contraposition, due to Lukasiewicz, 
will be our principle classical calculus we will use in practice. 

Two other systems will be introduced (Double Negation and Reductio Ad Absurdem).
These will be shown to be instances of our primary system.  We will also demonstrate
that our primary system may be interpreted as these subsystems. *}

locale Classy = SKI_bot +
  fixes Contra :: "'a"
  assumes Contratyp [intro]: "\<turnstile> Contra : (\<not> \<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"

--{* Classy has DN and RAD combinators, and we don't want name collisions *}
--{* So we will want to have have fake names for these combinators *}
locale ClassyDN = SKI_bot +
  fixes DNa :: "'a"
  assumes DNatyp [intro]: "\<turnstile> DNa : \<not> \<not> \<phi> \<rightarrow> \<phi>"

locale ClassyRAD = SKI_bot +
  fixes RADa :: "'a"
  assumes RADatyp [intro]: "\<turnstile> RADa : (\<not> \<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not> \<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<phi>"

subsubsection{* ClassyDN and ClassyRAD are sublocales of Classy *}

context ClassyDN begin
(* FIXME:  This is ugly :( *)
definition Contraa :: "'a" where
  "Contraa = 
   \<rhd>(\<Lambda>[X,Y,X',Y'] <X>\<bullet>(<Y>\<bullet><X'>\<bullet><Y'>))\<cdot>DNa\<cdot>\<rhd>(\<Lambda>[X,Y,Z] <X>\<bullet><Z>\<bullet><Y>)"

lemma Contraatyp [intro]:
"\<turnstile> Contraa : (\<not> \<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  by (simp add: Contraa_def, blast)
end

sublocale ClassyDN < Classy "vdash" "op \<rightarrow>" "op \<cdot>" "S" "K" "\<bottom>" "Contraa"
  by (unfold_locales, rule Contraatyp)

context ClassyRAD begin
definition DNb :: "'a" where
  "DNb = C\<cdot>RADa\<cdot>(K\<cdot>I)"

lemma DNbtyp [intro]: "\<turnstile> DNb : \<not> \<not> \<phi> \<rightarrow> \<phi>"
  by (simp add: DNb_def, blast)
end

sublocale ClassyRAD < ClassyDN "vdash" "op \<rightarrow>" "op \<cdot>" "S" "K" "\<bottom>" "DNb"
  by (unfold_locales, rule DNbtyp)

subsection{* Contraposition Implies Double Negation and Reductio Ad Absurdem *}

context Classy begin
definition DN :: "'a" where
  "DN = Contra\<cdot>\<rhd>(\<Lambda>[X,Y] <Y>\<bullet><X>)"

lemma DNax [intro]: "\<turnstile> DN : \<not> \<not> \<phi> \<rightarrow> \<phi>"
  by (simp add: DN_def, blast)

lemma "ClassyDN vdash (op \<rightarrow>) (op \<cdot>) S K \<bottom> DN"
  by (unfold_locales, rule DNax)

definition RAD :: "'a" where
  "RAD = C\<cdot>(\<rhd>(\<Lambda>[Z,X,Y] <Z>\<bullet>(S'\<bullet><X>\<bullet><Y>))\<cdot>DN)"

lemma RADax [intro]: "\<turnstile> RAD : (\<not> \<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not> \<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<phi>"
  by (simp add: RAD_def, blast)

lemma "ClassyRAD vdash (op \<rightarrow>) (op \<cdot>) S K \<bottom> RAD"
  by (unfold_locales, rule RADax)
end

subsection{* Classical Calculi are Explosive *}

context Classy begin
definition EFQa :: "'a" where
  "EFQa = W\<cdot>(Contra \<circ> (K \<circ> K))"

lemma EFQaax [intro]: "\<turnstile> EFQa : \<bottom> \<rightarrow> a"
  by (simp add: EFQa_def, blast)
end

sublocale Classy < EFQ "vdash" "op \<rightarrow>" "op \<cdot>" "S" "K" "\<bottom>" "EFQa"
  by (unfold_locales, rule EFQaax)

context SKI begin
no_notation
   vdash ("\<turnstile> _" [10] 10) and
   impl (infixr "\<rightarrow>" 85) and 
   ap (infixl "\<cdot>" 85) and
   interp ("\<rhd>")
end

context SKI_bot begin
no_notation
  neg ("\<not> _" [90] 90) and
  bot ("\<bottom>")
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
   LamAbs ("(\<Lambda>_/ _)" [50, 51] 50) 

notation
  comp  (infixl "\<circ>" 55) and
  Not  ("\<not> _" [40] 40)

end