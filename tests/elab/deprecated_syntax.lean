-- Test 1: Direct usage of deprecated term syntax → warning
deprecated_syntax Lean.Parser.Term.let_fun "use `have` instead" (since := "2026-03-24")

-- Note: the paren macro expands to the inner expression, so the warning
-- is attributed to the paren macro call site
#check (let_fun x := 1; x)

-- Test 2: Macro that expands to deprecated syntax → warning at macro call site
syntax "my_wrapper " : term
macro_rules | `(my_wrapper) => `(let_fun x := 1; x)

#check (my_wrapper)

-- Test 3: Non-deprecated syntax → no warning
#check (42 : Nat)

-- Test 4: deprecated_syntax for a tactic
syntax "myDepTac" : tactic
macro_rules | `(tactic| myDepTac) => `(tactic| trivial)

deprecated_syntax tacticMyDepTac "use `trivial` instead" (since := "2026-03-24")

example : True := by myDepTac

-- Test 5: missing since emits a warning
deprecated_syntax Lean.Parser.Term.show
