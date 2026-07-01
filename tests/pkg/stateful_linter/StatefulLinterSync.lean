import StatefulLinter.Def

/-!
Same as `StatefulLinter.lean`, but forces synchronous elaboration via
`set_option Elab.async false` to check that stateful linters also thread their
state correctly when linters do not run in dedicated async tasks.
-/

set_option Elab.async false

/--
info: 1 : Nat
---
info: prev was: 0, curr is: 1
-/
#guard_msgs in
#check 1

/--
info: 2 : Nat
---
info: prev was: 1, curr is: 2
-/
#guard_msgs in
#check 2

/--
info: 3 : Nat
---
info: prev was: 2, curr is: 3
-/
#guard_msgs in
#check 3
