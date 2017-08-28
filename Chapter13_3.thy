theory Chapter13_3
imports "~~/src/HOL/IMP/Collecting_Examples"
begin

definition cex :: com where "cex =
  ''x'' ::= N 0;; ''y'' ::= N 2;;
  WHILE Less (N 0) (V ''y'')
  DO (''x'' ::= Plus (V ''x'') (V ''y'');;
      ''y'' ::= Plus (V ''y'') (N (-1)))"

definition Cex :: "state set acom" where "Cex = annotate (\<lambda>p. {}) cex"

value "show_acom ((step {<>} ^^ 12) Cex)"

end

