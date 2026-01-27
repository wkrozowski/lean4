set_option trace.Meta.Tactic.cbv true
set_option trace.Meta.Tactic true

def function (n : Nat) : Nat := match n with
  | 0 => 0 + 1
  | Nat.succ n => function n + 1
termination_by (n,0)

#check function.eq_1

def f : Unit -> Nat × Nat := fun _ => (1, 2)

example : function 150 = 151 := by
  conv =>
    lhs
    cbv

example : ((1,1).1,1).1 = 1 := by
  conv =>
    lhs
    cbv

example : (f ()).2 = 2 := by
  conv =>
    lhs
    cbv

def g : Unit → (Nat → Nat) × (Nat → Nat) := fun _ => (fun x => x + 1, fun x => x + 3)

theorem congrTest : (g ()).1 6 = 7 := by
  conv =>
    lhs
    cbv

#print congrTest
