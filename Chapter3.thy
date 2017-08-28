theory Chapter3
imports "~~/src/HOL/IMP/BExp"
        "~~/src/HOL/IMP/ASM"
begin

text{*
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
*}

fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (Plus (N i) (N j)) = False" |
  "optimal (N i) = True" |
  "optimal (V str) = True" |
  "optimal (Plus a b) = conj (optimal a) (optimal b)"

text{*
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
*}

lemma "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)  
  done
    
text{*
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):
*}

fun sumN :: "aexp \<Rightarrow> int" where
  "sumN (N i) = i" |
  "sumN (Plus a b) = sumN a + sumN b"|
  "sumN (V str) = 0"

fun zeroN :: "aexp \<Rightarrow> aexp" where
  "zeroN (N i) = N 0" |
  "zeroN (Plus a b) = Plus (zeroN a) (zeroN b)" |
  "zeroN (V str) = V str"
      
text {*
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
*}
 
fun sepN :: "aexp \<Rightarrow> aexp" where
  "sepN a = Plus (N (sumN a)) (zeroN a)" 

value "asimp (sepN (Plus (V t) (Plus (N 3) (N 4))))"  

lemma aux_1: "aval t s = sumN t + aval (zeroN t) s"   
  apply (induction t arbitrary: s)
  apply auto  
  done  
    
lemma aux_2: "aval (sepN t) s = sumN t + aval (zeroN t) s"
  apply auto
  done  
    
lemma aval_sepN: "aval t s = aval (sepN t) s"
  apply (induction t)
  apply auto
  done  
    
text {*
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
*}

fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp a = asimp (sepN a)"

lemma aval_full_asimp: " aval (full_asimp t) s = aval t s  "
  apply (induction t)
  apply auto  
  done  

text{*
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
*}

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst v1 a (V v2)  = (if v1 = v2 then a else (V v2))" |
  "subst v1 a (Plus x y) = Plus (subst v1 a x) (subst v1 a y)" |
  "subst v1 a (N x) = N x"  
  
text{*
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example: {lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
*}

  
lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply auto  
  done
    
text {*
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
*}
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (induction e)
  apply auto
  done  
  

text{*
\endexercise

\exercise
Take a copy of theory @{theory AExp} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*}

  
datatype aexp1 = N1 int | V1 vname | Plus1 aexp1 aexp1 | Times aexp1 aexp1

fun aval1 :: "aexp1 \<Rightarrow> state \<Rightarrow> val" where
"aval1 (N1 n) s = n" |
"aval1 (V1 x) s = s x" |
"aval1 (Plus1 a\<^sub>1 a\<^sub>2) s = aval1 a\<^sub>1 s + aval1 a\<^sub>2 s" |
"aval1 (Times a\<^sub>1 a\<^sub>2) s = (aval1 a\<^sub>1 s) * (aval1 a\<^sub>2  s)"

value "aval1 (Times (N1 3) (Plus1 (N1 4) (N1 5))) (\<lambda>x. 0) "

fun plus1 :: "aexp1 \<Rightarrow> aexp1 \<Rightarrow> aexp1" where
"plus1 (N1 i\<^sub>1) (N1 i\<^sub>2) = N1 (i\<^sub>1+i\<^sub>2)" |
"plus1 (N1 i) a = (if i=0 then a else Plus1 (N1 i) a)" |
"plus1 a (N1 i) = (if i=0 then a else Plus1 a (N1 i))" |
"plus1 a\<^sub>1 a\<^sub>2 = Plus1 a\<^sub>1 a\<^sub>2"

fun mult :: "aexp1 \<Rightarrow> aexp1 \<Rightarrow> aexp1" where
"mult (N1 i\<^sub>1) (N1 i\<^sub>2) = N1 (i\<^sub>1*i\<^sub>2)" |
"mult (N1 i) a = 
  (if i=1 then a else if i=0 then (N1 0) else Times (N1 i) a)" |
"mult a (N1 i) = (if i=0 then (N1 0) else if i = 1 then a else Times a (N1 i))" |
"mult a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"


fun asimp1 :: "aexp1 \<Rightarrow> aexp1" where
"asimp1 (N1 n) = N1 n" |
"asimp1 (V1 x) = V1 x" |
"asimp1 (Plus1 a\<^sub>1 a\<^sub>2) = plus1 (asimp1 a\<^sub>1) (asimp1 a\<^sub>2)"|
"asimp1 (Times a\<^sub>1 a\<^sub>2) = mult (asimp1 a\<^sub>1) (asimp1 a\<^sub>2)"   


lemma aval1_plus[simp]:
  "aval1 (plus1 a1 a2) s = aval1 a1 s + aval1 a2 s"
apply(induction a1 a2 rule: plus1.induct)
apply simp_all (* just for a change from auto *)
done

lemma aval1_mult[simp]:
  "aval1 (mult a1 a2) s = aval1 a1 s * aval1 a2 s"
  apply (induction a1 a2 rule: mult.induct)
  apply simp_all
  done  

theorem aval1_asimp[simp]:
  "aval1 (asimp1 a) s = aval1 a s"
apply(induction a)
apply auto
done  

text{*
\endexercise

\exercise
Define a datatype @{text aexp2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text aexp2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
*}

  
  
  
text{*
\endexercise
\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
*}

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

text{* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
*}

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
(* your definition/proof here *)

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
(* your definition/proof here *)

text{*
and prove that they do what they are supposed to:
*}

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
(* your definition/proof here *)

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional: *}

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text {*  First define an evaluation function analogously to @{const bval}: *}

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
(* your definition/proof here *)

text{* Then define two translation functions *}

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
(* your definition/proof here *)

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
(* your definition/proof here *)

text{* and prove their correctness: *}

lemma "bval (if2bexp exp) s = ifval exp s"
(* your definition/proof here *)

lemma "ifval (b2ifexp exp) s = bval exp s"
(* your definition/proof here *)

text{*
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
*}

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text{*
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
*}

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)" 

text {* Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s: *}

fun is_nnf :: "pbexp \<Rightarrow> bool" where
(* your definition/proof here *)

text{*
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
*}

fun nnf :: "pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text{*
Prove that @{const nnf} does what it is supposed to do:
*}

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
(* your definition/proof here *)

lemma is_nnf_nnf: "is_nnf (nnf b)"
(* your definition/proof here *)

text{*
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
*}

fun is_dnf :: "pbexp \<Rightarrow> bool" where
(* your definition/proof here *)

text {*
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
*}

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text {* and prove that it behaves as follows: *}

lemma pbval_dist: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
(* your definition/proof here *)

lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
(* your definition/proof here *)

text {* Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
*}

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text {* Prove the correctness of your function: *}

lemma "pbval (dnf_of_nnf b) s = pbval b s"
(* your definition/proof here *)

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
(* your definition/proof here *)

text{*
\endexercise


\exercise\label{exe:stack-underflow}
A \concept{stack underflow} occurs when executing an @{text ADD}
instruction on a stack of size less than two. In our semantics
stack underflow leads to a term involving @{term "hd []"},
which is not an error or exception --- HOL does not
have those concepts --- but some unspecified value. Modify
theory @{theory ASM} such that stack underflow is modelled by @{const None}
and normal execution by @{text Some}, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find @{text"split: option.split"} useful in your proofs.
*}

text{*
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
*}
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

text {*
where type @{text reg} is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads @{text i} into register @{text r},
@{term "LD x r"} loads the value of @{text x} into register @{text r},
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds register @{text r\<^sub>2} to register @{text r\<^sub>1}.

Define the execution of an instruction given a state and a register state;
the result is the new register state: *}

type_synonym rstate = "reg \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
(* your definition/proof here *)

text{*
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into @{text r}. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "< r"} should be left alone.
Define the compiler and prove it correct:
*}

theorem "exec (comp a r) s rs r = aval a s"
(* your definition/proof here *)

text{*
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
*}

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text{*
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
*}

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
(* your definition/proof here *)

text{*
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
*}

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
(* your definition/proof here *)

text{*
\endexercise
*}

end

