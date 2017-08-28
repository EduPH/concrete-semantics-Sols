theory Chapter12_2
imports "~~/src/HOL/IMP/Hoare_Examples"
begin

text{*
\section*{Chapter 12}

\setcounter{exercise}{1}

\exercise
Define @{text bsubst} and prove the Substitution Lemma:
*}

fun bsubst :: "bexp \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> bexp" where
(* your definition/proof here *)

lemma bsubstitution: "bval (bsubst b a x) s = bval b (s[a/x])"
(* your definition/proof here *)

text{*
This may require a similar definition and proof for @{typ aexp}.
\endexercise

\exercise
Define a command @{text cmax} that stores the maximum of the values of the IMP variables
@{text "x"} and @{text "y"} in the IMP variable @{text "z"} and prove that
@{text cmax} satisfies its specification:
*}

abbreviation cmax :: com where
(* your definition/proof here *)

lemma "\<turnstile> {\<lambda>s. True} cmax {\<lambda>s. s ''z'' = max (s ''x'') (s ''y'')}"
(* your definition/proof here *)

text{*
Function @{const max} is the predefined maximum function.
Proofs about @{const max} are often automatic when simplifying with @{thm[source] max_def}.
\endexercise

\exercise\label{exe:Hoare:sumeq}
Define an equality operation for arithmetic expressions
*}


definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
(* your definition/proof here *)

text{* such that *}

lemma bval_Eq[simp]: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
(* your definition/proof here *)

text{* Prove the following variant of the summation command correct: *}

lemma
  "\<turnstile> {\<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''y'' ::= N 0;;
     WHILE Not(Eq (V ''x'') (N 0))
     DO (''y'' ::= Plus (V ''y'') (V ''x'');;
           ''x'' ::= Plus (V ''x'') (N (-1)))
     {\<lambda>s. s ''y'' = sum i}"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Prove that the following command computes @{prop"y - x"} if @{prop"(0::nat) \<le> x"}:
*}

lemma
  "\<turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x}
     WHILE Less (N 0) (V ''x'')
     DO (''x'' ::= Plus (V ''x'') (N (-1));; ''y'' ::= Plus (V ''y'') (N (-1)))
     {\<lambda>t. t ''y'' = y - x}"
(* your definition/proof here *)

text{*
\endexercise

\exercise\label{exe:Hoare:mult}
Define and verify a command @{text cmult} that stores the product of
@{text "x"} and @{text "y"} in @{text "z"} assuming @{prop"(0::int)\<le>y"}:
*}

abbreviation cmult :: com where
(* your definition/proof here *)

lemma
  "\<turnstile> {\<lambda>s.  s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> y} cmult {\<lambda>t. t ''z'' = x*y}"
(* your definition/proof here *)

text{*
You may have to simplify with @{thm[source] algebra_simps} to deal with ``@{text"*"}''.
\endexercise

\exercise\label{exe:Hoare:sqrt}
The following command computes an integer approximation @{text r} of the square root
of @{text "i \<ge> 0"}, i.e.\ @{text"r\<^sup>2 \<le> i < (r+1)\<^sup>2"}. Prove
*}

lemma
  "\<turnstile> { \<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''r'' ::= N 0;; ''r2'' ::= N 1;;
     WHILE (Not (Less (V ''x'') (V ''r2'')))
     DO (''r'' ::= Plus (V ''r'') (N 1);;
            ''r2'' ::= Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1)))
     {\<lambda>s. (s ''r'')^2 \<le> i \<and> i < (s ''r'' + 1)^2}"
(* your definition/proof here *)

text{*
Figure out how @{text r2} is related to @{text r} before
formulating the invariant.
The proof may require simplification with @{thm[source] algebra_simps}
and @{thm[source] power2_eq_square}.
\endexercise

\exercise
Prove by induction:
*}

lemma "\<turnstile> {P} c {\<lambda>s. True}"
(* your definition/proof here *)

text{*
\endexercise

\exercise\label{exe:fwdassign}
Design and prove correct a forward assignment rule of the form
\ \mbox{@{text"\<turnstile> {P} x ::= a {?}"}} \
where @{text"?"} is some suitable postcondition that depends on @{text P},
@{text x} and @{text a}. Hint: @{text"?"} may need @{text"\<exists>"}.
*}

lemma "\<turnstile> {P} x ::= a {Questionmark}"
(* your definition/proof here *)
text{*
(In case you wonder if your @{text Questionmark} is strong enough: see Exercise~\ref{exe:sp})
\endexercise
*}
end

