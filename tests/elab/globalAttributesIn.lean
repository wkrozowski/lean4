def t : True := by simp

/--
warning: Despite the `in`, the attribute irreducible is added globally to t
please remove the `in` or make this a `local irreducible`
-/
#guard_msgs in
attribute [local simp, irreducible] t in
example : True := t

/--
warning: Despite the `in`, the attribute simp is added globally to t
please remove the `in` or make this a `local simp`
-/
#guard_msgs in
attribute [simp] t in
example : True := t

def t' : True := by simp

/--
warning: Despite the `in`, the attribute simp is added globally to t'
please remove the `in` or make this a `local simp`
---
warning: Despite the `in`, the attribute irreducible is added globally to t'
please remove the `in` or make this a `local irreducible`
-/
#guard_msgs in
attribute [simp, irreducible] t' in
example : True := t'

attribute [local simp] t in
example : True := t
