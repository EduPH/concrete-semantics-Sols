theory Chapter10_1
imports "~~/src/HOL/IMP/Def_Init"
begin

text{*
\section*{Chapter 10}

\exercise
Define the definite initialisation analysis as two recursive functions
*}

fun ivars :: "com \<Rightarrow> vname set" where
(* your definition/proof here *)

fun ok :: "vname set \<Rightarrow> com \<Rightarrow> bool" where
(* your definition/proof here *)

text{*
such that @{const ivars} computes the set of definitely initialised variables
and @{const ok} checks that only initialised variable are accessed.
Prove
*}

lemma "D A c A' \<Longrightarrow> A' = A \<union> ivars c \<and> ok A c"
(* your definition/proof here *)

lemma "ok A c \<Longrightarrow> D A c (A \<union> ivars c)"
(* your definition/proof here *)

text{*
\endexercise
*}

end

