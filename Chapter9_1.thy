theory Chapter9_1
imports "~~/src/HOL/IMP/Types"
begin

text{*
\section*{Chapter 9}

\exercise
Reformulate the inductive predicates \ @{prop"\<Gamma> \<turnstile> a : \<tau>"},
\ @{prop"\<Gamma> \<turnstile> (b::bexp)"} \
and \ \mbox{@{prop"\<Gamma> \<turnstile> (c::com)"}} \ as three recursive functions
*}

fun atype :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty option" where
(* your definition/proof here *)

fun bok :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" where
(* your definition/proof here *)

fun cok :: "tyenv \<Rightarrow> com \<Rightarrow> bool" where
(* your definition/proof here *)

text{* and prove *}

lemma atyping_atype: "(\<Gamma> \<turnstile> a : \<tau>) = (atype \<Gamma> a = Some \<tau>)"
(* your definition/proof here *)

lemma btyping_bok: "(\<Gamma> \<turnstile> b) = bok \<Gamma> b"
(* your definition/proof here *)

lemma ctyping_cok: "(\<Gamma> \<turnstile> c) = cok \<Gamma> c"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Modify the evaluation and typing of @{typ aexp} by allowing @{typ int}s to be coerced
to @{typ real}s with the predefined coercion function
\noquotes{@{term[source] "real_of_int :: int \<Rightarrow> real"}} where necessary.
Now every @{typ aexp} has a value. Define an evaluation function:
*}

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
(* your definition/proof here *)

text{*
Similarly, every @{typ aexp} has a type.
Define a function that computes the type of an @{typ aexp}
*}

fun atyp :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty" where
(* your definition/proof here *)

text{* and prove that it computes the correct type: *}

lemma  "\<Gamma> \<turnstile> s \<Longrightarrow>  atyp \<Gamma> a = type (aval a s)"
(* your definition/proof here *)

text{*
Note that Isabelle inserts the coercion @{typ real} automatically.
For example, if you write @{term "Rv(i+r)"} where @{text"i :: int"} and
@{text "r :: real"} then it becomes @{term "Rv(real i + x)"}.
\endexercise
\bigskip

For the following two exercises copy theory @{theory Types} and modify it as required.

\begin{exercise}
Add a @{text REPEAT} loop (see Exercise~\ref{exe:IMP:REPEAT}) to the typed version of IMP
and update the type soundness proof.
\end{exercise}

\begin{exercise}
Modify the typed version of IMP as follows. Values are now either integers or booleans.
Thus variables can have boolean values too. Merge the two expressions types
@{typ aexp} and @{typ bexp} into one new type @{text exp} of expressions
that has the constructors of both types (of course without real constants).
Combine @{const taval} and @{const tbval} into one evaluation predicate
@{text "eval :: exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"}. Similarly combine the two typing predicates
into one: @{text "\<Gamma> \<turnstile> e : \<tau>"} where @{text "e :: exp"} and the IMP-type @{text \<tau>} can
be one of @{text Ity} or @{text Bty}. 
Adjust the small-step semantics and the type soundness proof.
\end{exercise}
*}

end

