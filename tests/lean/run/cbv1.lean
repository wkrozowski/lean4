import Lean.Meta.Tactic.Cbv.Types
import Lean.Meta.Tactic.Cbv.CbvProc

open Lean.Meta.Tactic.Cbv


namespace test1

  def myFun (l : List α) : Nat := match l with
    | [] => 0
    | hd :: tl => 1



  set_option trace.Meta.Tactic.cbv.fun_congr true
  theorem test1 : (myFun ([] : List Nat) ).succ = 1 := by
    conv =>
      lhs
      cbv

  #print test1

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


#print test3
end test3

namespace test4

  def myFun (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n + 1 => (myFun n) + 1
    termination_by id n
  set_option trace.Debug.Meta.Tactic.cbv true
  -- /- We need to be able to normalize this to a `OfNat.ofNat` -/
  theorem test4 : myFun 100 = 100 := by
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

  #check test7._proof_1_6

end test7

-- Overapplied matcher
namespace test8

def myFun (n : Nat) : Nat → Nat :=
  match n with
  | 0 => fun m => m + 1
  | n + 1 => fun m => myFun n (m + 2)

-- Overapplied matcher
theorem test8 : myFun 1 3 = 6 := by
  conv =>
    lhs
    cbv

end test8

section test9

def allEqual : Nat → Nat → Prop := fun _ _ => True

theorem allEqual.refl : ∀ a, allEqual a a := fun _ => trivial
theorem allEqual.symm : ∀ a b, allEqual a b → allEqual b a := fun _ _ _ => trivial
theorem allEqual.trans : ∀ a b c, allEqual a b → allEqual b c → allEqual a c :=
  fun _ _ _ _ _ => trivial

def Unit' := Quot allEqual

example : Quot.mk allEqual 5 = Quot.mk allEqual 5 := by
  conv =>
    lhs
    cbv

def fromUnit' : Unit' → Nat :=
  Quot.lift (fun _ => 42) (fun _ _ _ => rfl)

example : fromUnit' (Quot.mk allEqual 10) = 42 := by
  conv =>
    lhs
    cbv

end test9

section test10

-- Can survive def-eq casts
example : Vector.cast (Nat.add_comm 1 2) (Vector.singleton 42 |>.push 7 |>.push 9) =
          Vector.cast rfl (Vector.singleton 42 |>.push 7 |>.push 9) := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

def myAdd (n m : Nat) : Nat := match n with
| .zero => m
| .succ n => (myAdd n m).succ
  termination_by n

def makeVec3 : Vector Nat 3 :=
  Vector.singleton 1 |>.push 2 |>.push 3

-- This fails as we force the result to be homogenous equal at the end, essentialy accounts to a diamond property

/--
error: AppBuilder for `eq_of_heq`, heterogeneous equality types are not definitionally equal
  Vector Nat (myAdd 2 1)
is not definitionally equal to
  Vector Nat 3
-/
#guard_msgs in
theorem example1 (h : 3 = myAdd 2 1) : Vector.cast h makeVec3 = Vector.cast h makeVec3 := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

theorem example2 : Vector.cast rfl (Vector.singleton 42) = Vector.singleton 42 := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

#print example2



end test10

section test11

/- Overapplied lambda -/
example : (id Nat.succ) 4 = 5 := by
  conv =>
    lhs
    cbv

example : ((id Nat.succ),5).1 4 = 5 := by
  conv =>
    lhs
    cbv

def matchFun (n : Nat) : Nat → Nat → Nat :=
  match id n with
  | 0 => Nat.add
  | _ => fun _ => id

-- Should unfold matchFun
example : matchFun 4 = sorry := by
  conv =>
    lhs
    cbv
  sorry

example : (fun x y => (id (matchFun x, matchFun y).1)) 3 4 = sorry := by
  conv =>
    lhs
    cbv
  sorry

def matchFun2 (α : Type) (l : List α) : Nat := match l with
| [] => 0
| _ => 1

example : List.length [1,2,3] = sorry := by
  conv =>
    lhs
    cbv
  sorry


theorem constantEvaluation : (fun _ => (HAdd.hAdd : Nat → Nat → Nat)) () 1 2 = 3 := by
  conv =>
    lhs
    cbv

#print constantEvaluation

end test11

namespace test12

/- Nat normalisation -/
theorem test12 : 142 + 157 = 157 + 142 := by
  conv =>
    lhs
    cbv

def myFun (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ n => (myFun n) + 1
termination_by n

theorem test12b : (fun x y => x + y) 250 250 = 500 := by
  conv =>
    lhs
    cbv

#print test12b

end test12

-- Some overapplication tests that can break my code
section test13

def myId {α : Type} (x : α) : α := x

-- This should reduce to: (fun _ => myId) 0 1 ~~> myId 1 ~~> 1
example : ((fun (_ : Nat) => myId) 0) 1 = 1 := by conv =>
  lhs
  cbv

-- A function that returns a function
def addCurried (x : Nat) : Nat → Nat := fun y => x + y

-- Triple nested lambda with overapplication
example : ((fun (_ : Nat) => fun (_ : Nat) => addCurried) 0 1) 2 3 = 5 := by
  conv =>
    lhs
    cbv

def constNat : Nat → Nat := fun x => 42

example : ((fun (_ : Nat) => constNat) 0) 1 = 42 := by
  conv =>
    lhs
    cbv

end test13

section test14

example : Nat.zero = 0 := by
  conv =>
    lhs
    cbv

-- @[cbv_proc Nat.zero] def helloWorld : CbvExt := {
--   eval e callback := do throwError "Hello there: called with {e}"
-- }

example : Nat.zero = 0 := by
  conv =>
    lhs
    cbv

end test14

section test15

  def myId2 (n : Nat) := match n with
  | 0 => 0
  | n + 1 => (myId2 n) + 1
    termination_by n

  example : myId2 1000 = 1000 := by
    conv =>
      lhs
      cbv

end test15

section test16

def fn (n : Nat) (v : Vector Nat n) : Nat := (v.size + 1)

def propEqFn (n : Nat) : Nat := match n with
  | 0 => 0
  | (n + 1) => propEqFn n + 1
  termination_by n

  axiom k : Vector Nat (propEqFn 1)

  set_option trace.Debug.Meta.Tactic.cbv true

 theorem test16 : fn (propEqFn 1) k = fn 1 #v[1] := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

  #print axioms test16

end test16

namespace test16b

def fn (n : Nat) (v : Vector Nat n) : Nat := (v.size + 1)

def propEqFn (n : Nat) : Nat := match n with
  | 0 => 0
  | (n + 1) => propEqFn n + 1
  termination_by n

  axiom k : Vector Nat (propEqFn 1)

  set_option trace.Debug.Meta.Tactic.cbv true

 theorem test16 : fn (propEqFn 1) k = 2 := by
  conv =>
    lhs
    cbv


  #print test16
  #check test16._proof_1_15

end test16b


theorem ite_reduce (p : Prop) [Decidable p] (h : decide p = true) : p = True := by
  grind

set_option trace.Meta.Tactic.cbv true
section test17
  theorem test17 : (if (2 < 5) then 7 else 42 : Nat) = (7 : Nat) := by
    conv =>
      lhs
      cbv

#print test17

end test17
