-- This works
namespace test1
coinductive Foo : {n : Nat} → Fin n → Prop
| one (x : Fin 1) : Foo x
end test1
namespace test2


coinductive Foo : {n : Nat} → Fin n → Prop
| one (x : Fin 1) : Foo x
| succ {m : Nat} (x : Fin (m + 1)) : Foo x


#print Foo._functor



#print Foo._functor.existential


#print Foo._functor.existential_equiv

end test2

namespace test3
coinductive Foo : (n : Nat) → Fin n → Prop
| one (x : Fin 1) : Foo 1 x
| succ (m : Nat) (x : Fin (m + 1)) : Foo (m + 1) x
end test3

set_option trace.Meta.MkIffOfInductiveProp true
coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a

/--
info: inductive infSeq._functor.{u_1} : {α : Sort u_1} → (α → α → Prop) → (α → Prop) → α → Prop
number of parameters: 3
constructors:
infSeq._functor.step : ∀ {α : Sort u_1} (r : α → α → Prop) (infSeq._functor.call : α → Prop) {a b : α},
  r a b → infSeq._functor.call b → infSeq._functor r infSeq._functor.call a
-/
#guard_msgs in
#print infSeq._functor
