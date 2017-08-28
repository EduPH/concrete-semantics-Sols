theory Chapter8
imports "~~/src/HOL/IMP/Compiler"
begin

text{*
\section*{Chapter 8}

For the following exercises copy and adjust theory @{theory Compiler}.
Intrepid readers only should attempt to adjust theory @{text Compiler2} too.

\begin{exercise}
A common programming idiom is @{text "IF b THEN c"}, i.e.,
the @{text ELSE}-branch is a @{term SKIP} command.
Look at how, for example, the command @{term "IF Less (V ''x'') (N 5) THEN ''y'' ::= N 3 ELSE SKIP"}
is compiled by @{const ccomp} and identify a possible compiler optimization.
Modify the definition of @{const ccomp} such that it generates fewer instructions
for commands of the form @{term "IF b THEN c ELSE SKIP"}.
Ideally the proof of theorem @{thm[source] ccomp_bigstep} should still work;
otherwise adapt it.
\end{exercise}

\begin{exercise}
Building on Exercise~\ref{exe:IMP:REPEAT}, extend the compiler @{const ccomp}
and its correctness theorem @{thm[source] ccomp_bigstep} to @{text REPEAT}
loops. Hint: the recursion pattern of the big-step semantics
and the compiler for @{text REPEAT} should match.
\end{exercise}

\begin{exercise}\label{exe:COMP:addresses}
Modify the machine language such that instead of variable names to values,
the machine state maps addresses (integers) to values. Adjust the compiler
and its proof accordingly.

In the simple version of this exercise, assume the existence of a globally
bijective function @{term "addr_of :: vname => int"} with @{term "bij addr_of"}
to adjust the compiler. Use the @{text find_theorems} search to find applicable
theorems for bijectivte functions.

For the more advanced version and a slightly larger project, only assume that
the function works on a finite set of variables: those that occur in the
program. For the other, unused variables, it should return a suitable default
address. In this version, you may want to split the work into two parts:
first, update the compiler and machine language, assuming the existence of
such a function and the (partial) inverse it provides. Second, separately
construct this function from the input program, having extracted the
properties needed for it in the first part. In the end, rearrange you theory
file to combine both into a final theorem.
\end{exercise}

\begin{exercise}
This is a slightly more challenging project. Based on
\autoref{exe:COMP:addresses}, and similarly to \autoref{exe:register-machine}
and \autoref{exe:accumulator}, define a second machine language that does not
possess a built-in stack, but instead, in addition to the program counter, a
stack pointer register. Operations that previously worked on the stack now
work on memory, accessing locations based on the stack pointer.

For instance, let @{term "(pc, s, sp)"} be a configuration of this new machine consisting of
program counter, store, and stack pointer. Then the configuration after an @{const ADD} instruction
is \mbox{@{term "(pc + 1::int, s(sp + 1 := s (sp + 1::int) + s sp), sp + 1)"}}, that is, @{const ADD} dereferences
the memory at @{term "sp + 1::int"} and @{term sp}, adds these two values and stores them at
@{term "sp + 1::int"}, updating the values on the stack. It also increases the stack pointer by one
to pop one value from the stack and leave the result at the top of the stack. This means the stack grows downwards.

Modify the compiler from \autoref{exe:COMP:addresses} to work on this new machine language. Reformulate and reprove the easy direction of compiler correctness.

\emph{Hint:} Let the stack start below @{text 0}, growing downwards, and use type @{typ nat} for addressing variable in @{const LOAD} and @{const STORE} instructions, so that it is clear by type that these instructions do not interfere with the stack. 

\emph{Hint:} When the new machine pops a value from the stack, this now unused value is left behind in the store. This means, even after executing a purely arithmetic expression, the values in initial and final stores are not all equal. But: they are equal above a given address. Define an abbreviation for this concept and use it to express the intermediate correctness statements.

\end{exercise}

*}
end

