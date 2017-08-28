theory Chapter12_5
imports "~~/src/HOL/IMP/Hoare_Total"
begin

text{*
\exercise
Prove total correctness of the commands in exercises~\ref{exe:Hoare:sumeq} to
\ref{exe:Hoare:sqrt}.
*}

text{*
\endexercise

\exercise
Modify the VCG to take termination into account. First modify type @{text acom}
by annotating  @{text WHILE} with a measure function in addition to an
invariant:
*}
datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile assn "state \<Rightarrow> nat" bexp acom
    ("({_, _}/ WHILE _/ DO _)"  [0, 0, 61] 61)

notation com.SKIP ("SKIP")

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_,_} WHILE b DO C) = (WHILE b DO strip C)"

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>s. if bval b s then pre C\<^sub>1 Q s else pre C\<^sub>2 Q s)" |
"pre ({I,f} WHILE b DO C) Q = I"

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1;; C\<^sub>2) Q = (vc C\<^sub>1 (pre C\<^sub>2 Q) \<and> vc C\<^sub>2 Q)" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |
(* your definition/proof here *)

text{*
Functions @{const strip} and @{const pre} remain almost unchanged.
The only significant change is in the @{text WHILE} case for @{const vc}.
Modify the old soundness proof to obtain 
*}

lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile>\<^sub>t {pre C Q} strip C {Q}"
(* your definition/proof here *)

text{*
You may need the combined soundness and completeness of @{text"\<turnstile>\<^sub>t"}:
@{thm hoaret_sc}
\endexercise
*}

end

