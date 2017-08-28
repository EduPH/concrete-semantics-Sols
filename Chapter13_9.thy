theory Chapter13_9
imports "~~/src/HOL/IMP/Abs_Int3"
begin

(* 13.19 *)
value "show_acom (step_up_ivl 3 (steps test3_ivl 4))"

(* 13.20 *)
value "show_acom ((step_ivl \<top> ^^ 4) (step_up_ivl 3 (steps test3_ivl 4)))"
value "show_acom (step_down_ivl 4 (step_up_ivl 3 (steps test3_ivl 4)))"

end

