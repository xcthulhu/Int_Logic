header {* Three Classical Calculi *}

theory Lukasiewicz
imports SKI
begin

section{* Classy Locales *}

text {* Minimal logic with contraposition, due to Lukasiewicz, 
will be our principle classical calculus we will use in practice. *}

text {* Two other equivalent systems will also be introduced: Double Negation and Reductio Ad Absurdem.
These will be shown to be instances of our primary system.  We will also demonstrate
that our primary system may be interpreted to be an instance of these subsystems. *}

locale Classy = SKI_bot +
  fixes Contra :: "'a"
  assumes Contratyp [intro]: "\<turnstile> Contra : (\<not> \<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"

text{* Classy has DN and RAD combinators, and we don't want name collisions. 
 So we will want to have have fake names for these combinators. *}

locale ClassyDN = SKI_bot +
  fixes DNa :: "'a"
  assumes DNatyp [intro]: "\<turnstile> DNa : \<not> \<not> \<phi> \<rightarrow> \<phi>"

locale ClassyRAD = SKI_bot +
  fixes RADa :: "'a"
  assumes RADatyp [intro]: "\<turnstile> RADa : (\<not> \<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not> \<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<phi>"

subsubsection{* ClassyDN and ClassyRAD are Sublocales of Classy *}

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