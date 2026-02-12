import Std

example : 1 ∈ [1,2,3] := by decide_cbv

theorem le_test : 1 < 2 := by decide_cbv

#print le_test

example : 3 ∈ (Std.TreeSet.empty.insertMany [1,2,3,4,5] : Std.TreeSet Nat) := by decide_cbv

def minFacAux (n : Nat) : Nat → Nat
  | k =>
    if h : n < k * k then n
    else
      if h' : k ∣ n then k
      else
        have : k ≤ n := by have := Nat.le_mul_self k; omega
        minFacAux n (k + 2)
termination_by k => (n + 2 - k)

def Nat.minFac (n : Nat) : Nat :=
  if 2 ∣ n then 2 else minFacAux n 3

def Nat.log (b n : Nat) : Nat :=
  if b ≤ 1 then 0 else (go b n).2 where
  go : Nat → Nat → Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

theorem proof0 : ¬∃ k, k ≤ Nat.log 2 125555555555555 ∧ 0 < k ∧ 125555555555555 = Nat.minFac 12555555555555 ^ k := by decide_cbv

abbrev Nat.Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ (m : Nat), m < p → 2 ≤ m → ¬m ∣ p

abbrev IsPrimePow (n : Nat) : Prop :=
  ∃ p ≤ n, ∃ k ≤ n, Nat.Prime p ∧ 0 < k ∧ p ^ k = n

set_option exponentiation.threshold 500
set_option diagnostics true
set_option trace.Meta.Tactic true

theorem test0 : @LT.lt Nat instLTNat 0 1 := by decide_cbv
#print test0

theorem test : ¬ IsPrimePow 6 := by decide_cbv

theorem test3 : 1 < 3 ∧ 1 < 4 := by decide_cbv
