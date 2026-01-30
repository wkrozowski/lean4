import Std
open Std

set_option trace.Meta.Tactic.cbv true
set_option trace.Meta.Tactic true
example : (#v[1] ++ #v[2]).size = 2 := by
  conv =>
    lhs
    cbv

example : Int.negSucc 2 = -3 := by
  conv =>
    lhs
    simp


theorem hashmap_test : (((∅ : DHashMap Nat (fun _ => Nat)).insert 5 4).insert 6 5).contains 5 = true := by
  conv =>
    lhs
    cbv

#print hashmap_test
