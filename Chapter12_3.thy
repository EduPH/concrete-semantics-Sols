theory Chapter12_3
imports "~~/src/HOL/IMP/Hoare_Sound_Complete"
begin

text{*
\exercise
Prove
*}

lemma "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> wp c Q s)"
(* your definition/proof here *)

text{*
\endexercise

\begin{exercise}
Replace the assignment command with a new command \mbox{@{term"Do f"}} where
@{text "f ::"} @{typ "state \<Rightarrow> state"} can be an arbitrary state transformer.
Update the big-step semantics, Hoare logic and the soundness and completeness proofs.
\end{exercise}

\exercise
Which of the following rules are correct? Proof or counterexample!
*}


lemma "\<lbrakk>\<turnstile> {P} c {Q};  \<turnstile> {P'} c {Q'}\<rbrakk> \<Longrightarrow>
  \<turnstile> {\<lambda>s. P s \<or> P' s} c {\<lambda>s. Q s \<or> Q' s}"
(* your definition/proof here *)

lemma "\<lbrakk>\<turnstile> {P} c {Q};  \<turnstile> {P'} c {Q'}\<rbrakk> \<Longrightarrow>
  \<turnstile> {\<lambda>s. P s \<and> P' s} c {\<lambda>s. Q s \<and> Q' s}"
(* your definition/proof here *)

lemma "\<lbrakk>\<turnstile> {P} c {Q};  \<turnstile> {P'} c {Q'}\<rbrakk> \<Longrightarrow>
  \<turnstile> {\<lambda>s. P s \<longrightarrow> P' s} c {\<lambda>s. Q s \<longrightarrow> Q' s}"
(* your definition/proof here *)

text{*
\endexercise

\begin{exercise}
Based on Exercise~\ref{exe:IMP:OR}, extend Hoare logic and the soundness and completeness proofs
with nondeterministic choice.
\end{exercise}

\begin{exercise}
Based on Exercise~\ref{exe:IMP:REPEAT}, extend Hoare logic and the soundness and completeness proofs
with a @{text REPEAT} loop. Hint: think of @{text"REPEAT c UNTIL b"} as
equivalent to \noquotes{@{term[source]"c;; WHILE Not b DO c"}}.
\end{exercise}

\exercise\label{exe:sp}
The dual of the weakest precondition is the \concept{strongest postcondition}
@{text sp}. Define @{text sp} in analogy with @{const wp} via the big-step semantics:
*}

definition sp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
(* your definition/proof here *)

text{* Prove that @{const sp} really is the strongest postcondition: *}

lemma "(\<Turnstile> {P} c {Q}) \<longleftrightarrow> (\<forall>s. sp c P s \<longrightarrow> Q s)"
(* your definition/proof here *)

text{*
In analogy with the derived equations for @{const wp} given in the text,
give and prove equations for ``calculating'' @{const sp} for three constructs:
@{prop"sp (x ::= a) P = Q\<^sub>1"}, @{prop"sp (c\<^sub>1;;c\<^sub>2) P = Q\<^sub>2"}, and
@{prop"sp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) P = Q\<^sub>3"}.
The @{text Q\<^sub>i} must not involve the semantics and may only call
@{const sp} recursively on the subcommands @{text c\<^sub>i}.
Hint: @{text Q\<^sub>1} requires an existential quantifier.
*}

text{*
\endexercise
*}

end

