set_option diagnostics true
namespace Test1
  structure Foo where
    a : Nat := 0
    b : Nat := 0

  instance : EmptyCollection Foo where
    emptyCollection := {a := 1, b:=2}

  def foo : Foo := {}

end Test1
namespace Test2
  structure Foo where
    a : Nat
    b : Nat
  def foo : Foo := {}
end Test2
