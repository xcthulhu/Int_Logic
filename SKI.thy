header {* SKI Calculus *}

theory SKI
imports Schonfinkel
begin

text {* In this section, we present the typed $SKI$ calculus, which corresponds
        to \emph{minimal logic}.  We will make use of Sch\"onfinkel's embedding of 
        the $\lambda$ calculus previously established to aid in composing proofs.  *}

section {* Preliminaries *}

text {* First, we will hijack the notation for @{term "op :"} so we can 
  use it to denote pairs.  We will then use pairs to denote combinator/type 
  combos in our locale for typed combinator calculus. *}

no_notation
  "op :"  ("op \<in>") and
  "op :"  ("(_/ \<in> _)" [50, 51] 50) and 
  "op :"  ("(_/ : _)" [50, 51] 50) and 
  comp  (infixl "\<circ>" 55) and
  Not  ("\<not> _" [40] 40) and
  "op &"  (infixr "\<and>" 35)

notation
  "Pair" ("_:_" [70, 71] 70)

--{* A sanity check *}
lemma "Pair a b = a : b" by auto

locale SKI =
  fixes
       vdash :: "'a \<times> 'b \<Rightarrow> bool"   ("\<turnstile> _" [10] 10)
    and impl :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"     (infixr "\<rightarrow>" 85) 
    and   ap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixl "\<cdot>" 85)
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

text {* We now show how our concrete SKI calculus 
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
by (simp, blast)

--{* Sanity check II: $B$ Combinator using the long embedding *}
lemma "\<turnstile> \<rhd> (\<Lambda>0[X,Y,Z] <X>\<bullet>(<Y>\<bullet><Z>)) : (\<chi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  apply simp
  --{* Rediculous subgoal! :D *}
  apply blast
done

text {* In practice we will try to use the more efficient Sch\"onfinkel embedding, 
  although it looks like the automation does not have a problem with the more combersome
  embedding. *}

text {* While we do not have a formal verification of this, in practice the 
        two embeddings establish equivalent types under interpretation. *}

text {* As an aside, we now have at our disposal the sexiest way of proving theorems in 
        minimal logic: exhibit the combinator associated with the desired theorem in the $\lambda$ calculus, 
        and then prove its $SKI$ embedding has the desired type.  One cannot possibly perform this
        with pencil and paper -- but we aren't using pencil and paper, are we?  Since programming and
        type inference are easy, this is arguable the fastest way to coerce the computer to prove
        lots of elementary theorems. *}

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
end