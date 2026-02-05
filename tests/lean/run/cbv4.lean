import Std
set_option cbv.warning false

def divisorsList (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun d => n % d = 0

set_option maxRecDepth 8000

-- set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler true

theorem test : divisorsList 3234 = [1, 3, 23, 29, 69, 87, 667, 2001] := by
  conv => lhs; cbv
