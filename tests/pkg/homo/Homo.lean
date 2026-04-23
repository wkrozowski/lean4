import Homo.Init

set_option warn.sorry false

opaque TSpec : (α : Type) × α := ⟨Unit, ()⟩
abbrev T : Type := TSpec.1
instance : Inhabited T := ⟨TSpec.2⟩
opaque add : T → T → T
opaque le : T → T → Prop
opaque pos : T → Prop
opaque small : T → Prop
opaque f : Nat → T
opaque toInt : T → Int

@[grind_homo] theorem T.eq (a b : T) : a = b ↔ toInt a = toInt b := sorry
@[grind_homo] theorem T.le (a b : T) : le a b ↔ toInt a ≤ toInt b := sorry
@[grind_homo] theorem T.pos (a : T) : pos a ↔ toInt a > 0 := sorry
@[grind_homo] theorem T.small (a : T) : small a ↔ toInt a < 8 := sorry
@[grind_homo] theorem T.add (a b : T) : toInt (add a b) = (toInt a + toInt b) % 128 := sorry
@[grind_homo] theorem cleanLeft (a b n : Int) : (a % n + b) % n = (a + b) % n := by simp
@[grind_homo] theorem cleanRight (a b n : Int) : (a + b % n) % n = (a + b) % n := by simp

set_option trace.homo true
example (b : T) : pos b → small b → le b (add b b) := by
  grind
