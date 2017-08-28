theory Chapter11       
imports "~~/src/HOL/IMP/Denotational" "~~/src/HOL/IMP/Vars"
begin

text{*
\section*{Chapter 11}

\begin{exercise}
Building on Exercise~\ref{exe:IMP:REPEAT}, extend the denotational
semantics and the equivalence proof with the big-step semantics
with a @{text REPEAT} loop.
\end{exercise}

\exercise
Consider Example~11.14 and prove the following equation by induction on @{text n}:
*}
lemma "((W (\<lambda>s. s ''x'' \<noteq> 0) ({(s,t). t = s(''x'' := s ''x'' - 1)}))^^n) {} =
  {(s,t). 0 \<le> s ''x'' & s ''x'' < int n & t = s(''x'' := 0)}"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Consider Example~11.14 but with the loop condition
@{prop"b = Less (N 0) (V ''x'')"}. Find a closed expression @{text M}
(containing @{text n})
for @{prop"(f ^^ n) {}"} and prove @{prop"(f ^^ n) {} = M"}.
*}

text {*
\endexercise

\exercise
Define an operator @{text B} such that you
can express the equation for @{term "D (IF b THEN c1 ELSE c2)"}
in a point free way. 
*}
definition B :: "bexp \<Rightarrow> (state \<times> state) set"  where 
(* your definition/proof here *)

lemma
  "D (IF b THEN c1 ELSE c2) = (B b O D c1) \<union> (B (Not b) O D c2)"
(* your definition/proof here *)

text {*
  Similarly, find a point free equation for @{term "W (bval b) dc"}
  and use it to write down a point free version of
  @{term "D (WHILE b DO c)"} (still using @{text lfp}).
  Prove that your equations are equivalent to the old ones. 
*}

(* your definition/proof here *)

text{*
\endexercise

\exercise
Let the `thin' part of a relation be its single-valued subset:
*}

definition thin :: "'a rel \<Rightarrow> 'a rel" where 
"thin R = {(a,b) . (a,b) \<in> R \<and> (\<forall> c. (a,c) \<in> R \<longrightarrow> c = b)}"

text{* Prove *}

lemma fixes f :: "'a rel \<Rightarrow> 'a rel"
assumes "mono f" and thin_f: "\<And> R. f (thin R) \<subseteq> thin (f R)" 
shows "single_valued (lfp f)"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Generalise our set-theoretic treatment of continuity and least fixpoints to
\concept{chain-complete partial order}s (\concept{cpo}s),
i.e.\ partial orders @{text"\<le>"} that have a least element @{text "\<bottom>"} and
where every chain @{text"c 0 \<le> c 1 \<le> \<dots>"} has a least upper bound
@{term"lub c"} where \noquotes{@{term[source]"c :: nat \<Rightarrow> 'a"}}.
This setting is described by the following type class @{text cpo}
which is an extension of the type class @{class order} of partial orders.
For details see the decription of type classes in Chapter~13.
*}

context order
begin
definition chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"chain c = (\<forall>n. c n \<le> c (Suc n))"
end

class cpo = order +
fixes bot :: 'a and lub :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
assumes bot_least: "bot \<le> x"
and lub_ub: "chain c \<Longrightarrow> c n \<le> lub c"
and lub_least: "chain c \<Longrightarrow> (\<And>n. c n \<le> u) \<Longrightarrow> lub c \<le> u"

text{*
A function \noquotes{@{term[source] "f :: 'a \<Rightarrow> 'b"}}
between two cpos @{typ 'a} and @{typ 'b}
is called \concept{continuous} if @{prop"f(lub c) = lub (f o c)"}.
Prove that if @{text f} is monotone and continuous then
\ \mbox{@{text"lub (\<lambda>n. (f ^^ n) \<bottom>)"}} \ is the least (pre)fixpoint of @{text f}:
*}


definition cont :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool" where
"cont f = (\<forall>c. chain c \<longrightarrow> f (lub c) = lub (f o c))"

abbreviation "fix f \<equiv> lub (\<lambda>n. (f^^n) bot)"

lemma fix_lpfp: assumes "mono f" and "f p \<le> p" shows "fix f \<le> p"
(* your definition/proof here *)

theorem fix_fp: assumes "mono f" and "cont f" shows "f(fix f) = fix f"
(* your definition/proof here *)

text{*
\endexercise

\exercise
We define a dependency analysis @{text Dep} that maps commands to relations
between variables such that @{term "(x,y) : Dep c"} means that in
the execution of @{text c}
the initial value of @{text x} can influence the final value of @{text y}:
*}

fun Dep :: "com \<Rightarrow> (vname * vname) set" where
"Dep SKIP = Id" |
"Dep (x::=a) = {(u,v). if v = x then u \<in> vars a else u = v}" |
"Dep (c1;;c2) = Dep c1 O Dep c2" |
"Dep (IF b THEN c1 ELSE c2) = Dep c1 \<union> Dep c2 \<union> vars b \<times> UNIV" |
"Dep (WHILE b DO c) = lfp(\<lambda>R. Id \<union> vars b \<times> UNIV \<union> Dep c O R)"

text{*
where @{text"\<times>"} is the cross product of two sets.
Prove monotonicity of the function @{const lfp} is applied to.
*}


text{* For the correctness statement define *}

abbreviation Deps :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"Deps c X \<equiv> (\<Union> x\<in>X. {y. (y,x) : Dep c})"

text{* and prove *}

lemma "\<lbrakk> (c,s) \<Rightarrow> s';  (c,t) \<Rightarrow> t';  s = t on Deps c X \<rbrakk> \<Longrightarrow> s' = t' on X"
(* your definition/proof here *)

text{*

Give an example that the following stronger termination-sensitive property
@{prop[display] "\<lbrakk> (c,s) \<Rightarrow> s'; s = t on Deps c X \<rbrakk>
  \<Longrightarrow> \<exists>t'. (c,t) \<Rightarrow> t' \<and> s' = t' on X"}
does not hold. Hint: @{prop"X = {}"}.

In the definition of @{term"Dep(IF b THEN c1 ELSE c2)"} the variables
in @{text b} can influence all variables (@{text UNIV}). However,
if a variable is not assigned to in @{text c1} and @{text c2}
it is not influenced by @{text b} (ignoring termination).
Theory @{theory Vars} defines a function @{const lvars} such
that @{term"lvars c"} is the set of variables on the left-hand side
of an assignment in @{text c}.
Modify the definition of @{const Dep} as follows:
replace @{const UNIV} by @{term"lvars c1 \<union> lvars c2"}
(in the case @{term"IF b THEN c1 ELSE c2"}) and by \mbox{@{term"lvars c"}}
(in the case @{term"WHILE b DO c"}).
Adjust the proof of the above correctness statement.
*}

text{*
\endexercise
*}

end

