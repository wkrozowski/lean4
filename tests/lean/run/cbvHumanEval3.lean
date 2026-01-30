import Std.Data

/-- Computes the largest divisor in O(sqrt n) via trial divison. -/
def largestDivisor (n : Nat) : Nat :=
  go 2
where
  go (i : Nat) : Nat :=
    if h : n < i * i then
      1
    else if n % i = 0 then
      n / i
    else go (i + 1)
  termination_by n - i
  decreasing_by
    have : i < n := by
      match i with
      | 0 => omega
      | 1 => omega
      | i + 2 => exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) (Nat.not_lt.1 h)
    omega

example : largestDivisor 3 = 1 := by
  conv =>
    lhs
    cbv

example : largestDivisor 7 = 1 := by
  conv =>
    lhs
    cbv

example : largestDivisor 10 = 5 := by
  conv =>
    lhs
    cbv

example : largestDivisor 100 = 50 := by
  conv =>
    lhs
    cbv

example : largestDivisor 49 = 7 := by
  conv =>
    lhs
    cbv
