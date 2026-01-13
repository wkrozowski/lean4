set_option trace.Meta.Tactic true
-- def myId (n : myNat) : myNat := n

-- def natFun (n : Nat) : Nat := match n with
--   | 0 => 0
--   | n + 1 => (natFun n).succ


-- def test (b : Bool) : Bool := match b,(!b) with
-- | true, true => false
-- | false, true => false
-- | true, false => false
-- | false, false => true

-- #check test.match_1.congr_eq_4


-- theorem ite_test : (fun x => decide (x > 3)) 4 = true := by simp

-- #print ite_test

-- theorem myTest0 : "a" ++ "a" = "aa" := by
--   conv =>
--     lhs
--     cbv

-- def myFun (ls : List Nat) : Bool :=
--   match ls with
--   | [] => false
--   | _ :: tl => !(myFun tl)

-- theorem myFunTest : myFun [1] = true := by
--   conv =>
--     lhs
--     cbv

theorem projectionTest : ([] : List Nat).length = 0 := by
  conv =>
    lhs
    cbv
