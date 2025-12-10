def myFun (n : Nat) : String :=
  match n with
  | .zero => "hi"
  | .succ n => (myFun n) ++ "hi"
termination_by n

set_option trace.Meta.Tactic true
theorem two_plus_two_eq_four : myFun (.succ .zero) = "hihi" := by conv =>
  lhs
  cbv
