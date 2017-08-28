theory Bool_Fold imports "~~/src/HOL/IMP/Fold" begin

text {*
\exercise
Strengthen and re-prove the congruence rules for conditional semantic equivalence 
to take the value of boolean expressions into account in the \texttt{IF} and
\texttt{WHILE} cases. As a reminder, the weaker rules are:

@{thm [display] equiv_up_to_if_weak}

@{thm [display] equiv_up_to_while_weak}

Find a formulation that takes @{text b} into account for equivalences about @{term c} or @{term d}.
*}

lemma equiv_up_to_if:
(* your definition/proof here *)



lemma equiv_up_to_while:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "(\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c'"
  assumes I: "\<And>s s'. (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b s \<Longrightarrow> P s'"
  shows "P \<Turnstile> WHILE b DO c \<sim> WHILE b' DO c'"
(* your definition/proof here *)

text {*
\endexercise

\exercise
Extend constant folding with analysing boolean expressions
and eliminate dead \texttt{IF} branches as well as loops whose body is
never executed. Use the contents of theory @{theory Fold} as a blueprint.
*}

fun bfold :: "bexp \<Rightarrow> tab \<Rightarrow> bexp"  where 
(* your definition/proof here *)


primrec bdefs :: "com \<Rightarrow> tab \<Rightarrow> tab"  where 
(* your definition/proof here *)

primrec fold' :: "com \<Rightarrow> tab \<Rightarrow> com"  where 
(* your definition/proof here *)



text {*
  Hint: you will need to make use of stronger congruence rules
        for conditional semantic equivalence.
*}

lemma fold'_equiv: "approx t \<Turnstile> c \<sim> fold' c t"
(* your definition/proof here *)

theorem constant_folding_equiv': "fold' c empty \<sim> c"
(* your definition/proof here *)

text {* \endexercise *}

end

