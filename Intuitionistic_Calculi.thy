header {* Intuitionistic Calculi *}

theory Intuitionistic_Calculi
imports SKI
begin

section {* Introduction *}

text {* In this section we introduce several miscellaneous Intuitionistic Calculi. *}

section {* Systems *}

subsection {* Base Classes *}

(* FIXME:  The "for" syntax for locales sucks *)
locale SKI_bot = SKI vdash impl ap S K 
  for  vdash :: "'a \<times> 'b \<Rightarrow> bool"    ("\<turnstile> _" [10] 10)
    and impl :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"     (infixr "\<rightarrow>" 85) 
    and   ap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"     (infixl "\<cdot>" 85)
    and    S :: "'a"
    and    K :: "'a" +
  fixes  bot :: "'b" ("\<bottom>")

abbreviation (in SKI_bot) neg :: "'b \<Rightarrow> 'b" ("\<not> _" [90] 90)
  where "neg \<phi> \<equiv> \<phi> \<rightarrow> \<bottom>"

locale SKI_top = SKI vdash impl ap S K 
  for  vdash :: "'a \<times> 'b \<Rightarrow> bool"    ("\<turnstile> _" [10] 10)
    and impl :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"     (infixr "\<rightarrow>" 85) 
    and   ap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"     (infixl "\<cdot>" 85)
    and    S :: "'a"
    and    K :: "'a" +
  fixes  top :: "'b" ("\<top>")

subsection {* Ex Falso Quodlibet \& Truthiness *}

locale EFQ = SKI_bot +
  fixes EFQ :: "'a"
  assumes EFQtyp [intro]: "\<turnstile> EFQ : \<bottom> \<rightarrow> \<phi>"

locale Truthiness = SKI_top +
  fixes Truth :: "'a"
  assumes Truthtyp [intro]: "\<turnstile> Truth : \<phi> \<rightarrow> \<top>"

subsection {* The $\wedge$-Fragment 
              and CCC-Calculus *}

locale ConjC = SKI +
  fixes Conj :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixr "\<and>" 95)
    and   \<pi>1 :: "'a" 
    and   \<pi>2 :: "'a"
    and pair :: "'a"
  assumes pairtyp [intro]: "\<turnstile> pair : \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi> \<and> \<psi>"
      and  \<pi>1typ [intro]: "\<turnstile> \<pi>1 : \<phi> \<and> \<psi> \<rightarrow> \<phi>"
      and  \<pi>2typ [intro]: "\<turnstile> \<pi>2 : \<phi> \<and> \<psi> \<rightarrow> \<psi>"

abbreviation (in ConjC) 
   makepair :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<times>" 95) where
  "(a \<times> b) \<equiv> (pair \<cdot> a \<cdot> b)"

locale CCCC = ConjC + SKI_top