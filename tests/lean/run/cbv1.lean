-- set_option trace.Meta.Tactic.cbv true

namespace test1

  def myFun (l : List α) : Nat := match l with
    | [] => 0
    | (_ :: _) => 1

  theorem test1 : (myFun ([] : List Nat) ).succ = 1 := by
    conv =>
      lhs
      cbv


end test1

namespace test2

  def test2 : (fun (α) (l : List α) => l) Nat ([] : List Nat) = [] := by
    conv =>
      lhs
      cbv

end test2

namespace test3

  theorem test3 : [2,3,4].length = 3 := by
    conv =>
      lhs
      cbv

end test3

namespace test4

  def myFun (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n + 1 => (myFun n) + 1
    termination_by id n
  set_option trace.Meta.Tactic.cbv true
  -- /- We need to be able to normalize this to a `OfNat.ofNat` -/
  theorem test4 : myFun 1 = 1 := by
    conv =>
      lhs
      cbv

end test4

namespace test5
  theorem test5 : (fun y => (fun _ : Nat => if true then y else true)) false = (fun _ => if true = true then false else true) := by
    conv =>
      lhs
      cbv
end test5

#print test4.test4

namespace test6

  theorem test6 : (let x := 5; x + 2) = 7 := by
    conv =>
      lhs
      cbv

#print test6

end test6

namespace test7

  def myFun (l : List Nat) : Nat := match l with
    | [] => 0
    | _ => 1

  theorem test7 : myFun [2] = 1 := by
    conv =>
      lhs
      cbv

end test7

theorem simp_add : @HAdd.hAdd _ _ _ _ = Nat.add := by rfl
