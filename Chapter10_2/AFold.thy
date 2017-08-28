theory AFold
imports 
  "~~/src/HOL/IMP/Sem_Equiv"
  "~~/src/HOL/IMP/Vars"
begin
text {*

\exercise
Extend @{text afold} with simplifying addition of @{text 0}. That is, for any
expression $e$, $e+0$ and $0+e$ should be simplified to just $e$, including
the case where the $0$ is produced by knowledge of the content of variables.

*}
type_synonym  tab = "vname \<Rightarrow> val option"

fun afold :: "aexp \<Rightarrow> tab \<Rightarrow> aexp" where
(* your definition/proof here *)


text {*
Re-prove the results in this section with the extended version by
copying and adjusting the contents of theory @{text Fold}.
*}

theorem "fold c empty \<sim> c" 
(* your definition/proof here *)

text{*
\endexercise
*}

end

