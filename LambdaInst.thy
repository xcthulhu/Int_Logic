header {* The Typed Lambda Calculus Instances SKI *}

theory LambdaInst
imports SKI "~~/src/HOL/Lambda/Type"
begin

text {* Here, we illustrate that the typed $\lambda$ calculus developed in the Isabelle/HOL library instantiates the SKI calculus *}

definition dB_S :: "dB" where
  "dB_S = Abs (Abs (Abs ((Var 2 \<degree> Var 0) \<degree> (Var 1 \<degree> Var 0))))"

definition dB_K :: "dB" where
  "dB_K = Abs (Abs (Var 1))"

declare dB_S_def [simp] and dB_K_def [simp]

(* FIXME: We could easily add a top element here *)
interpretation dB : SKI "\<lambda>(\<tau>,\<phi>). e \<turnstile> \<tau> : \<phi>" "Fun" "op \<degree>" "dB_S" "dB_K"
  by (simp, unfold_locales, force+)

--{* Sanity check *}
(* FIXME: Get automation working better for importing SKI results *)
lemma "e \<turnstile> dB.I : \<phi> \<Rightarrow> \<phi>"
  by (metis dB.Ityp split_conv)

end