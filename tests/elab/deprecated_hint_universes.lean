def new1.{u,v} : Sort u → Sort v → Nat := fun _ _ => 0

@[deprecated new1 (since:="")]
def old1.{u, v} : Sort u → Sort v → Nat := fun _ _ => 0

/--
warning: `old1` has been deprecated: Use `new1` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲1
-/
#guard_msgs in
def test1 : Prop → Type → Nat := old1.{0,1}

def new2.{u,v} : Sort u → Sort v → Nat := fun _ _ => 0

@[deprecated new2 (since:="")]
def old2.{v, u} : Sort u → Sort v → Nat := fun _ _ => 0

/-- warning: `old2` has been deprecated: Use `new2` instead -/
#guard_msgs in
def test2 : Prop → Type → Nat := old2.{1,0}
