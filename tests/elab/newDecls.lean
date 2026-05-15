set_option linter.newDecls true
/--
warning: new declarations: [hello]

Note: This linter can be disabled with `set_option linter.newDecls false`
-/
#guard_msgs in
def hello : String := "world"

/--
warning: new declarations: [function.match_1, function._f, function, function._unsafe_rec, function._sunfold]

Note: This linter can be disabled with `set_option linter.newDecls false`
-/
#guard_msgs in
def function (n : Nat) : Nat := match n with
  | 0 => 0
  | n + 1 => function n + 1

/--
warning: new declarations: [Hi,
 Hi.rec,
 Hi.Hello,
 Hi.recOn,
 Hi.casesOn,
 Hi.ctorIdx,
 Hi.toCtorIdx,
 Hi.noConfusionType,
 Hi.noConfusion,
 Hi._sizeOf_1,
 Hi._sizeOf_inst,
 Hi.Hello.sizeOf_spec]

Note: This linter can be disabled with `set_option linter.newDecls false`
-/
#guard_msgs in
inductive Hi : Type where
  | Hello : Hi

/--
warning: new declarations: [Hi2._functor,
 Hi2._functor.rec,
 Hi2._functor.Hello,
 Hi2._functor.recOn,
 Hi2._functor.casesOn,
 Hi2._functor.existential_equiv,
 Hi2._functor.existential,
 Hi2._proof_1,
 Hi2,
 Hi2._unsafe_rec,
 Hi2.eq_def,
 Hi2.eq_1,
 Hi2.functor_unfold,
 Hi2.Hello,
 Hi2.casesOn]

Note: This linter can be disabled with `set_option linter.newDecls false`
-/
#guard_msgs in
set_option trace.Elab false in
coinductive Hi2 : Prop where
  | Hello : Hi2

def hello3 : String := "world3"

private def hello2 : String := "world2"
