set_option diagnostics true
namespace Test1
  --Provided with default values and an instance of EmptyCollection, it fails due to ambiguity
  structure Foo where
    a : Nat := 0
    b : Nat := 0

  instance my : EmptyCollection Foo where
    emptyCollection := {a := 1, b:=2}

  def foo : Foo := {}

end Test1

-- No default values, nor an instance of EmptyCollection
namespace Test2
  structure Foo where
    a : Nat
    b : Nat
  def foo : Foo := {}
end Test2

-- It doesn't fail due to correctly synthetising an instance of EmptyCollection from defult values
namespace Test3
  structure Foo where
  a : Nat := 0
  b : Nat := 0
  def foo : Foo := {}
end Test3
