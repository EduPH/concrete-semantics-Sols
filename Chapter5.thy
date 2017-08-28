theory Chapter5
imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_0: "iter r 0 x x" |
iter_Suc: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

text{*
\section*{Chapter 5}

\exercise
Give a readable, structured proof of the following lemma:
*}
lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
(* your definition/proof here *)

text{*
Each step should use at most one of the assumptions @{text T}, @{text A}
or @{text TA}.
\endexercise

\exercise
Give a readable, structured proof of the following lemma:
*}
lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs)
      \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
(* your definition/proof here *)

text{*
Hint: There are predefined functions @{const take} and {const drop} of type
@{typ "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"} such that @{text"take k [x\<^sub>1,\<dots>] = [x\<^sub>1,\<dots>,x\<^sub>k]"}
and @{text"drop k [x\<^sub>1,\<dots>] = [x\<^bsub>k+1\<^esub>,\<dots>]"}. Let sledgehammer find and apply
the relevant @{const take} and @{const drop} lemmas for you.
\endexercise

\exercise
Give a structured proof by rule inversion:
*}
inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
(* your definition/proof here *)

text{*
\exercise
Give a structured proof by rule inversions:
*}

lemma "\<not> ev(Suc(Suc(Suc 0)))"
(* your definition/proof here *)

text{*
If there are no cases to be proved you can close
a proof immediateley with \isacom{qed}.
\endexercise

\exercise
Recall predicate @{const star} from Section 4.5 and @{const iter}
from Exercise~\ref{exe:iter}.
*}

lemma "iter r n x y \<Longrightarrow> star r x y"
(* your definition/proof here *)

text{*
Prove this lemma in a structured style, do not just sledgehammer each case of the
required induction.
\endexercise

\exercise
Define a recursive function
*}

fun elems :: "'a list \<Rightarrow> 'a set" where
(* your definition/proof here *)

text{* that collects all elements of a list into a set. Prove *}

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Extend Exercise~\ref{exe:cfg} with a function that checks if some
\mbox{@{text "alpha list"}} is a balanced
string of parentheses. More precisely, define a recursive function *}
(* your definition/proof here *)
fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
(* your definition/proof here *)

text{* such that @{term"balanced n w"}
is true iff (informally) @{text"a\<^sup>n @ w \<in> S"}. Formally, prove *}

corollary "balanced n w \<longleftrightarrow> S (replicate n a @ w)"


text{* where @{const replicate} @{text"::"} @{typ"nat \<Rightarrow> 'a \<Rightarrow> 'a list"} is predefined
and @{term"replicate n x"} yields the list @{text"[x, \<dots>, x]"} of length @{text n}.
*}

end

