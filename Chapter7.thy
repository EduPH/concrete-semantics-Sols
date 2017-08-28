theory Chapter7
imports "~~/src/HOL/IMP/Small_Step"
begin

text{*
\section*{Chapter 7}

\exercise
Define a function that computes the set of variables that are assigned to
in a command:
*}

fun assigned :: "com \<Rightarrow> vname set" where
(* your definition/proof here *)

text{*
Prove that if some variable is not assigned to in a command,
then that variable is never modified by the command:
*}

lemma "\<lbrakk> (c, s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"
(* your definition/proof here *)

text {*
\endexercise

\exercise
Define a recursive function that determines if a command behaves like @{const SKIP}
and prove its correctness:
*}

fun skip :: "com \<Rightarrow> bool" where
(* your definition/proof here *)

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Define a recursive function
*}

fun deskip :: "com \<Rightarrow> com" where
(* your definition/proof here *)

text{*
that eliminates as many @{const SKIP}s as possible from a command. For example:
@{prop[display]"deskip (SKIP;; WHILE b DO (x::=a;; SKIP)) = WHILE b DO x::=a"}
Prove its correctness by induction on @{text c}: *}

lemma "deskip c \<sim> c"
(* your definition/proof here *)

text{*
Remember lemma @{thm[source]sim_while_cong} for the @{text WHILE} case.
\endexercise

\exercise
A small-step semantics for the evaluation of arithmetic expressions
can be defined like this:
*}

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x, s) \<leadsto> N (s x)" |
"(Plus (N i) (N j), s) \<leadsto> N (i + j)" |
(* your definition/proof here *)

text{*
Complete the definition with two rules for @{const Plus}
that model a left-to-right evaluation strategy:
reduce the first argument with @{text"\<leadsto>"} if possible,
reduce the second argument with @{text"\<leadsto>"} if the first argument is a number.
Prove that each @{text"\<leadsto>"} step preserves the value of the expression:
*}

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep.induct [split_format (complete)])
(* your definition/proof here *)

text{*
Do not use the \isacom{case} idiom but write down explicitly what you assume
and show in each case: \isacom{fix} \dots \isacom{assume} \dots \isacom{show} \dots.
\endexercise

\exercise
Prove or disprove (by giving a counterexample):
*}

lemma "IF And b\<^sub>1 b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 \<sim>
          IF b\<^sub>1 THEN IF b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 ELSE c\<^sub>2"
(* your definition/proof here *)

lemma "WHILE And b\<^sub>1 b\<^sub>2 DO c \<sim> WHILE b\<^sub>1 DO WHILE b\<^sub>2 DO c"
(* your definition/proof here *)

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b\<^sub>1 b\<^sub>2 = Not (And (Not b\<^sub>1) (Not b\<^sub>2))"


lemma "WHILE Or b\<^sub>1 b\<^sub>2 DO c \<sim>
          WHILE Or b\<^sub>1 b\<^sub>2 DO c;; WHILE b\<^sub>1 DO c"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Define a new loop construct @{text "DO c WHILE b"} (where @{text c} is
executed once before @{text b} is tested) in terms of the
existing constructs in @{typ com}:
*}

definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
(* your definition/proof here *)

text{*
Define a translation on commands that replaces all @{term "WHILE b DO c"}
by suitable commands that use @{term "DO c WHILE b"} instead:
*}

fun dewhile :: "com \<Rightarrow> com" where
(* your definition/proof here *)

text{* Prove that your translation preserves the semantics: *}

lemma "dewhile c \<sim> c"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Let @{text "C :: nat \<Rightarrow> com"} be an infinite sequence of commands and
@{text "S :: nat \<Rightarrow> state"} an infinite sequence of states such that
@{prop"C(0::nat) = c;;d"} and \mbox{@{prop"\<forall>n. (C n, S n) \<rightarrow> (C(Suc n), S(Suc n))"}}.
Then either all @{text"C n"} are of the form \mbox{@{term"c\<^sub>n;;d"}}
and it is always @{text c\<^sub>n} that is reduced or @{text c\<^sub>n} eventually becomes @{const SKIP}.
Prove
*}

lemma assumes "C 0 = c;;d" and "\<forall>n. (C n, S n) \<rightarrow> (C(Suc n), S(Suc n))"
shows "(\<forall>n. \<exists>c\<^sub>1 c\<^sub>2. C n = c\<^sub>1;;d \<and> C(Suc n) = c\<^sub>2;;d \<and>
                         (c\<^sub>1, S n) \<rightarrow> (c\<^sub>2, S(Suc n)))
     \<or> (\<exists>k. C k = SKIP;;d)" (is "(\<forall>i. ?P i) \<or> ?Q")
(* your definition/proof here *)

text{*
\endexercise
\bigskip

For the following exercises copy theories
@{theory Com}, @{theory Big_Step} and @{theory Small_Step}
and modify them as required. Those parts of the theories
that do not contribute to the results required in the exercise can be discarded.
If there are multiple proofs of the same result, you may update any one of them.

\begin{exercise}\label{exe:IMP:REPEAT}
Extend IMP with a @{text "REPEAT c UNTIL b"} command by adding the constructor
\begin{alltt}
  Repeat com bexp   ("(REPEAT _/ UNTIL _)"  [0, 61] 61)
\end{alltt}
to datatype @{typ com}.
Adjust the definitions of big-step and small-step semantics,
the proof that the big-step semantics is deterministic and
the equivalence proof between the two semantics.
\end{exercise}

\begin{exercise}\label{exe:IMP:OR}
Extend IMP with a new command @{text "c\<^sub>1 OR c\<^sub>2"} that is a
nondeterministic choice: it may execute either @{text
"c\<^sub>1"} or @{text "c\<^sub>2"}. Add the constructor
\begin{alltt}
  Or com com   ("_ OR/ _" [60, 61] 60)
\end{alltt}
to datatype @{typ com}. Adjust the definitions of big-step
and small-step semantics, prove @{text"(c\<^sub>1 OR c\<^sub>2) \<sim> (c\<^sub>2 OR c\<^sub>1)"}
and update the equivalence proof between the two semantics.
\end{exercise}

\begin{exercise}
Extend IMP with exceptions. Add two constructors @{text THROW} and
@{text "TRY c\<^sub>1 CATCH c\<^sub>2"} to datatype @{typ com}:
\begin{alltt}
  THROW  |  Try com com   ("(TRY _/ CATCH _)"  [0, 61] 61)
\end{alltt}
Command @{text THROW} throws an exception. The only command that can
catch an execption is @{text "TRY c\<^sub>1 CATCH c\<^sub>2"}: if an execption
is thrown by @{text c\<^sub>1}, execution continues with @{text c\<^sub>2},
otherwise @{text c\<^sub>2} is ignored.
Adjust the definitions of big-step and small-step semantics as follows.

The big-step semantics is now of type @{typ "com \<times> state \<Rightarrow> com \<times> state"}.
In a big step @{text "(c,s) \<Rightarrow> (x,t)"}, @{text x} can only be @{term SKIP}
(signalling normal termination) or @{text THROW} (signalling that an exception
was thrown but not caught).

The small-step semantics is of the same type as before. There are two final
configurations now, @{term "(SKIP, t)"} and @{term "(THROW, t)"}.
Exceptions propagate upwards until an enclosing handler is found.
That is, until a configuration @{text "(TRY THROW CATCH c, s)"}
is reached and @{text THROW} can be caught.

Adjust the equivalence proof between the two semantics such that you obtain
@{text "cs \<Rightarrow> (SKIP,t)  \<longleftrightarrow>  cs \<rightarrow>* (SKIP,t)"}
and @{text "cs \<Rightarrow> (THROW,t)  \<longleftrightarrow>  cs \<rightarrow>* (THROW,t)"}.
Also revise the proof of
\noquotes{@{prop [source] "(\<exists>cs'. cs \<Rightarrow> cs')  \<longleftrightarrow>  (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"}}.
\end{exercise}
*}

end

