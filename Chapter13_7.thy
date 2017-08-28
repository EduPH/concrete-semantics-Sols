theory Chapter13_7
imports "~~/src/HOL/IMP/Abs_Int2"
begin

text{*
\setcounter{exercise}{15}
\exercise
Give a readable proof that if @{text "\<gamma> ::"} \noquotes{@{typ[source]"'a::lattice \<Rightarrow> 'b::lattice"}}
is a monotone function, then @{prop "\<gamma> (a\<^sub>1 \<sqinter> a\<^sub>2) \<le> \<gamma> a\<^sub>1 \<sqinter> \<gamma> a\<^sub>2"}:
*}

lemma fixes \<gamma> :: "'a::lattice \<Rightarrow> 'b :: lattice"
assumes mono: "\<And>x y. x \<le> y \<Longrightarrow> \<gamma> x \<le> \<gamma> y"
shows "\<gamma> (a\<^sub>1 \<sqinter> a\<^sub>2) \<le> \<gamma> a\<^sub>1 \<sqinter> \<gamma> a\<^sub>2"
(* your definition/proof here *)

text{*
Give an example of two lattices and a monotone @{text \<gamma>}
where @{prop"\<gamma> a\<^sub>1 \<sqinter> \<gamma> a\<^sub>2 \<le> \<gamma> (a\<^sub>1 \<sqinter> a\<^sub>2)"} does not hold.
*}

text{*
\endexercise

\exercise
Consider a simple sign analysis based on this abstract domain:
*}

datatype sign = None | Neg | Pos0 | Any

fun \<gamma> :: "sign \<Rightarrow> val set" where
"\<gamma> None = {}" |
"\<gamma> Neg = {i. i < 0}" |
"\<gamma> Pos0 = {i. i \<ge> 0}" |
"\<gamma> Any = UNIV"

text{*
Define inverse analyses for ``@{text"+"}'' and ``@{text"<"}''
and prove the required correctness properties:
*}

fun inv_plus' :: "sign \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign * sign" where
(* your definition/proof here *)

lemma
  "\<lbrakk> inv_plus' a a1 a2 = (a1',a2');  i1 \<in> \<gamma> a1;  i2 \<in> \<gamma> a2; i1+i2 \<in> \<gamma> a \<rbrakk>
  \<Longrightarrow> i1 \<in> \<gamma> a1' \<and> i2 \<in> \<gamma> a2' "
(* your definition/proof here *)

fun inv_less' :: "bool \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign * sign" where
(* your definition/proof here *)

lemma
  "\<lbrakk> inv_less' bv a1 a2 = (a1',a2');  i1 \<in> \<gamma> a1;  i2 \<in> \<gamma> a2; (i1<i2) = bv \<rbrakk>
  \<Longrightarrow> i1 \<in> \<gamma> a1' \<and> i2 \<in> \<gamma> a2'"
(* your definition/proof here *)

text{*
\indent
For the ambitious: turn the above fragment into a full-blown abstract interpreter
by replacing the interval analysis in theory @{theory Abs_Int2}@{text"_ivl"}
by a sign analysis.
\endexercise
*}

end

