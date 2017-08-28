theory Chapter10_3
imports
  "~~/src/HOL/IMP/Live"
  "~~/src/HOL/IMP/Small_Step"
begin

text{*
\exercise
Prove the following termination-insensitive version of the correctness of
@{const L}:
*}

theorem "\<lbrakk> (c,s) \<Rightarrow> s';  (c,t) \<Rightarrow> t';  s = t on L c X \<rbrakk> \<Longrightarrow> s' = t' on X"
(* your definition/proof here *)

text{*
Do not derive it as a corollary of the original correctness theorem
but prove it separately. Hint: modify the original proof.
\endexercise

\exercise\label{exe:bury-not-idemp}
Find a command @{text c} such that @{prop"bury (bury c {}) {} \<noteq> bury c {}"}.
For an arbitrary command, can you put a limit on the amount of burying needed
until everything that is dead is also buried?
*}


text{*
\endexercise

\exercise
Let @{term"lvars c"} / @{term"rvars c"} be the set of variables that
occur on the left-hand / right-hand side of an assignment in @{text c}.
Let @{term "rvars c"} additionally including those variables mentioned in
the conditionals of @{text IF} and @{text WHILE}.
Both functions are predefined in theory @{theory Vars}.
Show the following two properties of the small-step semantics.
Variables that are not assigned to do not change their value:
*}

lemma "\<lbrakk>(c,s) \<rightarrow>* (c',s'); lvars c \<inter> X = {}\<rbrakk> \<Longrightarrow> s = s' on X"
(* your definition/proof here *)

text{*
The reduction behaviour of a command is only influenced by the variables
read by the command:
*}

lemma "\<lbrakk>(c,s) \<rightarrow>* (c',s'); s = t on X; rvars c \<subseteq> X\<rbrakk>
  \<Longrightarrow> \<exists>t'. (c,t) \<rightarrow>* (c',t') \<and> s' = t' on X"
(* your definition/proof here *)

text{*
Hint: prove single step versions of the lemmas first.
\endexercise

\exercise
An \concept{available definitions} analysis determines which previous
assignments \texttt{x := a} are valid equalities \texttt{x = a} at later
program points.  For example, after \texttt{x := y+1} the equality \texttt{x =
y+1} is available, but after \mbox{\texttt{x := y+1;}} \texttt{y := 2} the equality \texttt{x = y+1} is
no longer available. The motivation for the analysis is that if \texttt{x =
a} is available before \texttt{v := a} then \mbox{\texttt{v := a}} can be replaced by
\texttt{v := x}.

Define an available definitions analysis as a gen/kill analysis,
for suitably defined @{text gen} and @{text kill} (which may need to be
mutually recursive):
*}
hide_const (open) gen "kill"
fun gen :: "com \<Rightarrow> (vname * aexp) set"
and "kill" :: "com \<Rightarrow> (vname * aexp) set" where
(* your definition/proof here *)


definition AD :: "(vname * aexp) set \<Rightarrow> com \<Rightarrow> (vname * aexp) set" where
"AD A c = gen c \<union> (A - kill c)"

text{*
The defining equations for both @{const gen} and @{const kill} follow
the \isacom{where} and are separated by ``@{text "|"}'' as usual.

A call \ @{term"AD A c"} \ should compute the available definitions
after the execution of @{text c} assuming that the definitions in @{text A}
are available before the execution of @{text c}.

Prove correctness of the analysis:
*}

theorem "\<lbrakk> (c,s) \<Rightarrow> s';  \<forall> (x,a) \<in> A. s x = aval a s \<rbrakk>
  \<Longrightarrow> \<forall> (x,a) \<in> AD A c. s' x = aval a s'"
(* your definition/proof here *)

text{*
\endexercise
*}



end

