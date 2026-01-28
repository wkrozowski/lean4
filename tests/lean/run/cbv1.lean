import Std

def function (n : Nat) : Nat := match n with
  | 0 => 0 + 1
  | Nat.succ n => function n + 1
termination_by (n,0)

example : function 150 = 151 := by
  conv =>
    lhs
    cbv

example : ((1,1).1,1).1 = 1 := by
  conv =>
    lhs
    cbv


def f : Unit -> Nat × Nat := fun _ => (1, 2)

example : (f ()).2 = 2 := by
  conv =>
    lhs
    cbv

def g : Unit → (Nat → Nat) × (Nat → Nat) := fun _ => (fun x => x + 1, fun x => x + 3)

example : (g ()).1 6 = 7 := by
  conv =>
    lhs
    cbv

example : "b" ++ "c" = "bc" := by
  conv =>
    lhs
    cbv
  rfl

example : "abx" ++ "c" = "a" ++ "bxc" := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

example : instHDiv.1 97 64 = 1 := by
  conv =>
    lhs
    cbv

example : instHAdd.1 2 2 = 4 := by
  conv =>
    lhs
    cbv

example : (fun y : Nat → Nat => (fun x => y x)) Nat.succ 1 = 2 := by
  conv =>
    lhs
    cbv

example : (Std.TreeMap.empty.insert "a" "b" : Std.TreeMap String String).toList = [("a", "b")] := by
  conv =>
    lhs
    cbv

#check Std.HashMap.ofList


theorem test (v : Vector α n) : v.size = v.toArray.size := by
  grind

theorem array_test : (List.replicate 200 5 : List Nat).reverse = List.replicate 200 5 := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

def testFun (l : List Nat) : Nat := Id.run do
  let mut i := 0
  for _ in l do
    i := i + 1
  return i

-- Would be nice if we perfomed zeta reduction
example : testFun [1,2,3,4,5] = 5 := by
  conv =>
    lhs
    cbv

set_option trace.Meta.Tactic.cbv true

example : "a" ++ "a" = "aa" := by
  conv =>
    lhs
    cbv

#check String.utf8EncodeChar.eq_1

theorem concat_test : "ab".length + "ab".length = ("ab" ++ "ab").length := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv



structure myStruct where
  a : HDiv Nat Nat Nat

example : ({a := instHDiv} : myStruct) = sorry := by
  conv =>
    lhs
    cbv

example :  instHDiv.1 119 262144  = sorry := by
  conv =>
    lhs
    cbv

theorem std_test2 : (((Std.TreeMap.empty : Std.TreeMap Nat Nat).insert 2 4).toList ++ [(5, 6)]).reverse = [(5,6), (2,4)] := by
  conv =>
    lhs
    cbv

#print std_test2

example : "wojtek".1 = sorry := by
  conv =>
    lhs
    cbv

def h := ()

example : h = () := by
  conv =>
    lhs
    -- Does not unfold the constant, we need to figure out what is a good way of dealing with it
    cbv


example : ((Std.HashMap.emptyWithCapacity : Std.HashMap Nat Nat).insert 4 3).contains 4 = sorry := by
  conv =>
    lhs
    cbv

set_option trace.Meta.Tactic.cbv true
example : 2 + 2 = 4 := by
  conv =>
    lhs
    cbv
