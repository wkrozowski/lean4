/- Minimized example extracted from verifying the Collatz conjecture for small numbers.
   Suggested by Bhavik Mehta (@b-mehta). -/
set_option cbv.warning false

def M := 12

def alg2 (n₀ m k f e : Nat) : List (Nat × Nat × Nat) :=
  if m < n₀ ∨ (e ≥ 2 ∧ e % 2 = 0) then [] else
  if k ≥ M then [(n₀, m, f)] else
  if m % 2 = 0 then
    alg2 n₀ (m / 2) (k + 1) f (e + 1) ++ alg2 (n₀ + 2 ^ k) ((3 * (m + 3 ^ f) + 1) / 2) (k + 1) (f + 1) 0
  else
    alg2 n₀ ((3 * m + 1) / 2) (k + 1) (f + 1) 0 ++ alg2 (n₀ + 2 ^ k) ((m + 3 ^ f) / 2) (k + 1) (f + 1) (e + 1)
  termination_by M - k

def collatzStep (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def manyStep (n m : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => m < n ∨ manyStep n (collatzStep m) k

def checkAll (gas : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (n₀, m, _) :: xs =>
    bif manyStep n₀ m gas then checkAll gas xs else false

set_option maxRecDepth 5000
set_option trace.Meta.Tactic true
example : checkAll 100 (alg2 3 8 2 2 0) = true := by
  cbv
