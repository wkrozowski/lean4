-- Enable the deprecated syntax linter (test framework disables all linters)
set_option linter.deprecatedSyntax true

-- Test 1: Direct usage of deprecated term syntax → warning
deprecated_syntax Lean.Parser.Term.let_fun "use `have` instead" (since := "2026-03-24")

-- Note: the paren macro expands to the inner expression, so the warning
-- is attributed to the paren macro call site
#check (let_fun x := 1; x)

-- Test 2: Macro that expands to deprecated syntax → warning at macro call site
syntax "my_wrapper " : term
macro_rules | `(my_wrapper) => `(let_fun x := 1; x)

#check (my_wrapper)

-- Test 3: set_option linter.deprecatedSyntax false suppresses warnings
set_option linter.deprecatedSyntax false in
#check (let_fun x := 1; x)

-- Test 4: Non-deprecated syntax → no warning
#check (42 : Nat)

-- Test 5: deprecated_syntax for a tactic
syntax "myDepTac" : tactic
macro_rules | `(tactic| myDepTac) => `(tactic| trivial)

deprecated_syntax tacticMyDepTac "use `trivial` instead" (since := "2026-03-24")

example : True := by myDepTac

-- Test 6: missing since emits a warning
deprecated_syntax Lean.Parser.Term.show
