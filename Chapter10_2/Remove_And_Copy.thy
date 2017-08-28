theory Remove_And_Copy
  imports "~~/src/HOL/IMP/Sem_Equiv" "~~/src/HOL/IMP/Vars"
begin

text {*
\exercise\label{exs:remove}
This exercise builds infrastructure for \autoref{exs:acopy}, where we
will have to manipulate partial maps from variable names to variable names.
*}
type_synonym tab = "vname \<Rightarrow> vname option"

text {*
  In addition to the function @{text merge} from theory @{text Fold},
  implement two functions @{text remove} and @{text remove_all} that
  remove one variable name from the range of a map, and a set of variable
  names from the domain and range of a map.
*}

definition
  merge :: "tab \<Rightarrow> tab \<Rightarrow> tab" where
  "merge t1 t2 = (\<lambda>m. if t1 m = t2 m then t1 m else None)"

definition remove :: "vname \<Rightarrow> tab \<Rightarrow> tab"  where 
(* your definition/proof here *)

definition remove_all :: "vname set \<Rightarrow> tab \<Rightarrow> tab"  where 
(* your definition/proof here *)

text {*
  Prove the following lemmas.
*}

lemma "ran (remove x t) = ran t - {x}"
(* your definition/proof here *)

lemma "ran (remove_all S t) \<subseteq> -S"
(* your definition/proof here *)

lemma "dom (remove_all S t) \<subseteq> -S"
(* your definition/proof here *)

lemma remove_all_update[simp]: 
"remove_all {x} (t (x:= y)) = remove_all {x} t"
(* your definition/proof here *)

lemma remove_all_remove[simp]:
"remove_all {x} (remove x t) = remove_all {x} t"
(* your definition/proof here *)

lemma remove_all_Un[simp]:
"remove_all A (remove_all B t) = remove_all (A \<union> B) t"
(* your definition/proof here *)

lemma merge_remove_all:
  assumes "remove_all S t1 = remove_all S t"
  assumes "remove_all S t2 = remove_all S t"
  shows "remove_all S (merge t1 t2) = remove_all S t"
(* your definition/proof here *)

text {*
  \endexercise

  \exercise\label{exs:acopy}
  This is a more challenging exercise.
  Define and prove correct \emph{copy propagation}. Copy propagation is
similar to constant folding, but propagates the right-hand side of assignments
if these right-hand sides are just variables. For instance, the program
\texttt{x := y; z := x + z} will be transformed into 
\texttt{x := y; z := y + z}. 
The assignment \texttt{x := y} can then be eliminated in a liveness
analysis. Copy propagation is useful for cleaning up after other optimisation
phases.

  To do this, take the definitions for constant folding from theory
  @{text Fold} and adjust
  them to do copy propagation instead (without constant folding).
  Use the functions from \autoref{exs:remove} in your definition.
  The general proof idea and structure of constant folding remains
  applicable. Adjust it according to your new definitions.
*}



primrec copy :: "com \<Rightarrow> tab \<Rightarrow> com" where
(* your definition/proof here *)

value "copy (''x'' ::= V ''y'';; ''z'' ::= Plus (V ''x'') (V ''z'')) empty"

lemma approx_merge:
  "approx t1 s \<or> approx t2 s \<Longrightarrow> approx (merge t1 t2) s"
  by (fastforce simp: merge_def approx_def)

lemma approx_map_le:
  "approx t2 s \<Longrightarrow> t1 \<subseteq>\<^sub>m t2 \<Longrightarrow> approx t1 s"
  by (clarsimp simp: approx_def map_le_def dom_def)



theorem "copy c empty \<sim> c"
(* your definition/proof here *)

text {* \endexercise *}

end

