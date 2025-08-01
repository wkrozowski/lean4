/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import all Std.Data.DHashMap.Raw

public section

/-!
# Dependent hash maps

This file develops the type `Std.DHashMap` of dependent hash maps.

The operations `map` and `filterMap` on `Std.Data.DHashMap` are defined in the module
`Std.Data.DHashMap.AdditionalOperations`.

Lemmas about the operations on `Std.Data.DHashMap` are available in the
module `Std.Data.DHashMap.Lemmas`.

See the module `Std.Data.DHashMap.Raw` for a variant of this type which is safe to use in
nested inductive types and the module `Std.Data.ExtDHashMap` for a variant with extensionality.

For implementation notes, see the docstring of the module `Std.Data.DHashMap.Internal.Defs`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

variable {_ : BEq α} {_ : Hashable α}

namespace Std

open DHashMap.Internal DHashMap.Internal.List

/--
Dependent hash maps.

This is a simple separate-chaining hash table. The data of the hash map consists of a cached size
and an array of buckets, where each bucket is a linked list of key-value pairs. The number of buckets
is always a power of two. The hash map doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

The hash table is backed by an `Array`. Users should make sure that the hash map is used linearly to
avoid expensive copies.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

These hash maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.DHashMap.Raw` and
`Std.DHashMap.Raw.WF` unbundle the invariant from the hash map. When in doubt, prefer
`DHashMap` over `DHashMap.Raw`.

For a variant that is more convenient for use in proofs because of extensionalities, see
`Std.ExtDHashMap` which is defined in the module `Std.Data.ExtDHashMap`.
-/
structure DHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash map. -/
  inner : DHashMap.Raw α β
  /-- Internal implementation detail of the hash map. -/
  wf : inner.WF

namespace DHashMap

@[inline, inherit_doc Raw.emptyWithCapacity] def emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) : DHashMap α β :=
  ⟨Raw.emptyWithCapacity capacity, .emptyWithCapacity₀⟩

@[deprecated emptyWithCapacity (since := "2025-03-12"), inherit_doc emptyWithCapacity]
abbrev empty := @emptyWithCapacity

instance [BEq α] [Hashable α] : EmptyCollection (DHashMap α β) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] : Inhabited (DHashMap α β) where
  default := ∅

@[inherit_doc Raw.Equiv]
structure Equiv (m₁ m₂ : DHashMap α β) where
  /-- Internal implementation detail of the hash map -/
  inner : m₁.1.Equiv m₂.1

@[inherit_doc] scoped infixl:50 " ~m " => Equiv

@[inline, inherit_doc Raw.insert] def insert (m : DHashMap α β) (a : α)
    (b : β a) : DHashMap α β :=
  ⟨Raw₀.insert ⟨m.1, m.2.size_buckets_pos⟩ a b, .insert₀ m.2⟩

instance : Singleton ((a : α) × β a) (DHashMap α β) := ⟨fun ⟨a, b⟩ => (∅ : DHashMap α β).insert a b⟩

instance : Insert ((a : α) × β a) (DHashMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton ((a : α) × β a) (DHashMap α β) :=
  ⟨fun _ => rfl⟩

@[inline, inherit_doc Raw.insertIfNew] def insertIfNew (m : DHashMap α β)
    (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insertIfNew ⟨m.1, m.2.size_buckets_pos⟩ a b, .insertIfNew₀ m.2⟩

@[inline, inherit_doc Raw.containsThenInsert] def containsThenInsert
    (m : DHashMap α β) (a : α) (b : β a) : Bool × DHashMap α β :=
  let m' := Raw₀.containsThenInsert ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .containsThenInsert₀ m.2⟩⟩

@[inline, inherit_doc Raw.containsThenInsertIfNew] def containsThenInsertIfNew
    (m : DHashMap α β) (a : α) (b : β a) : Bool × DHashMap α β :=
  let m' := Raw₀.containsThenInsertIfNew ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .containsThenInsertIfNew₀ m.2⟩⟩

@[inline, inherit_doc Raw.getThenInsertIfNew?] def getThenInsertIfNew?
    [LawfulBEq α] (m : DHashMap α β) (a : α) (b : β a) : Option (β a) × DHashMap α β :=
  let m' := Raw₀.getThenInsertIfNew? ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .getThenInsertIfNew?₀ m.2⟩⟩

@[inline, inherit_doc Raw.get?] def get? [LawfulBEq α] (m : DHashMap α β)
    (a : α) : Option (β a) :=
  Raw₀.get? ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.contains] def contains (m : DHashMap α β) (a : α) :
    Bool :=
  Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ a

instance [BEq α] [Hashable α] : Membership α (DHashMap α β) where
  mem m a := m.contains a

instance [BEq α] [Hashable α] {m : DHashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc Raw.get] def get [LawfulBEq α] (m : DHashMap α β) (a : α)
    (h : a ∈ m) : β a :=
  Raw₀.get ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline, inherit_doc Raw.get!] def get! [LawfulBEq α] (m : DHashMap α β)
    (a : α) [Inhabited (β a)] : β a :=
  Raw₀.get! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.getD] def getD [LawfulBEq α] (m : DHashMap α β)
    (a : α) (fallback : β a) : β a :=
  Raw₀.getD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

@[inline, inherit_doc Raw.erase] def erase (m : DHashMap α β) (a : α) :
    DHashMap α β :=
  ⟨Raw₀.erase ⟨m.1, m.2.size_buckets_pos⟩ a, .erase₀ m.2⟩

section

variable {β : Type v}

@[inline, inherit_doc Raw.Const.get?] def Const.get?
    (m : DHashMap α (fun _ => β)) (a : α) : Option β :=
  Raw₀.Const.get? ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.Const.get] def Const.get
    (m : DHashMap α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  Raw₀.Const.get ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline, inherit_doc Raw.Const.getD] def Const.getD
    (m : DHashMap α (fun _ => β)) (a : α) (fallback : β) : β :=
  Raw₀.Const.getD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

@[inline, inherit_doc Raw.Const.get!] def Const.get! [Inhabited β]
    (m : DHashMap α (fun _ => β)) (a : α) : β :=
  Raw₀.Const.get! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.Const.getThenInsertIfNew?] def Const.getThenInsertIfNew?
    (m : DHashMap α (fun _ => β)) (a : α) (b : β) :
    Option β × DHashMap α (fun _ => β) :=
  let m' := Raw₀.Const.getThenInsertIfNew? ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .constGetThenInsertIfNew?₀ m.2⟩⟩

end

@[inline, inherit_doc Raw.getKey?] def getKey? (m : DHashMap α β) (a : α) : Option α :=
  Raw₀.getKey? ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.getKey] def getKey (m : DHashMap α β) (a : α) (h : a ∈ m) : α :=
  Raw₀.getKey ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline, inherit_doc Raw.getKey!] def getKey! [Inhabited α] (m : DHashMap α β) (a : α) : α :=
  Raw₀.getKey! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.getKeyD] def getKeyD (m : DHashMap α β) (a : α) (fallback : α) : α :=
  Raw₀.getKeyD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

@[inline, inherit_doc Raw.size] def size (m : DHashMap α β) : Nat :=
  m.1.size

@[inline, inherit_doc Raw.isEmpty] def isEmpty (m : DHashMap α β) : Bool :=
  m.1.isEmpty

@[inline, inherit_doc Raw.keys] def keys (m : DHashMap α β) : List α :=
  m.1.keys

@[inline, inherit_doc Raw.toList] def toList (m : DHashMap α β) :
    List ((a : α) × β a) :=
  m.1.toList

@[inline, inherit_doc Raw.Const.toList] def Const.toList {β : Type v}
    (m : DHashMap α (fun _ => β)) : List (α × β) :=
  Raw.Const.toList m.1

@[inline, inherit_doc Raw.foldM] def foldM (f : δ → (a : α) → β a → m δ)
    (init : δ) (b : DHashMap α β) : m δ :=
  b.1.foldM f init

@[inline, inherit_doc Raw.fold] def fold (f : δ → (a : α) → β a → δ)
    (init : δ) (b : DHashMap α β) : δ :=
  b.1.fold f init

@[inline, inherit_doc Raw.forM] def forM (f : (a : α) → β a → m PUnit)
    (b : DHashMap α β) : m PUnit :=
  b.1.forM f

@[inline, inherit_doc Raw.forIn] def forIn
    (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : DHashMap α β) : m δ :=
  b.1.forIn f init

instance [BEq α] [Hashable α] : ForM m (DHashMap α β) ((a : α) × β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance [BEq α] [Hashable α] : ForIn m (DHashMap α β) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

namespace Const

variable {β : Type v}

/-!
We do not define `ForM` and `ForIn` instances that are specialized to constant `β`. Instead, we
define uncurried versions of `forM` and `forIn` that will be used in the `Const` lemmas and to
define the `ForM` and `ForIn` instances for `HashMap`.
-/

@[inline, inherit_doc forM] def forMUncurried (f : α × β → m PUnit)
    (b : DHashMap α (fun _ => β)) : m PUnit :=
  b.forM fun a b => f ⟨a, b⟩

@[inline, inherit_doc forIn] def forInUncurried
    (f : α × β → δ → m (ForInStep δ)) (init : δ) (b : DHashMap α (fun _ => β)) : m δ :=
  b.forIn (init := init) fun a b d => f ⟨a, b⟩ d

end Const

@[inline, inherit_doc Raw.filter] def filter (f : (a : α) → β a → Bool)
    (m : DHashMap α β) : DHashMap α β :=
  ⟨Raw₀.filter f ⟨m.1, m.2.size_buckets_pos⟩, .filter₀ m.2⟩

/--
Modifies in place the value associated with a given key.

This function ensures that the value is used linearly.
-/
@[inline] def modify [LawfulBEq α] (m : DHashMap α β) (a : α) (f : β a → β a) : DHashMap α β :=
  ⟨Raw₀.modify ⟨m.1, m.2.size_buckets_pos⟩ a f, Raw.WF.modify₀ m.2⟩

@[inline, inherit_doc DHashMap.modify] def Const.modify {β : Type v} (m : DHashMap α (fun _ => β))
    (a : α) (f : β → β) : DHashMap α (fun _ => β) :=
  ⟨Raw₀.Const.modify ⟨m.1, m.2.size_buckets_pos⟩ a f, Raw.WF.constModify₀ m.2⟩

/--
Modifies in place the value associated with a given key,
allowing creating new values and deleting values via an `Option` valued replacement function.

This function ensures that the value is used linearly.
-/
@[inline] def alter [LawfulBEq α] (m : DHashMap α β)
    (a : α) (f : Option (β a) → Option (β a)) : DHashMap α β :=
  ⟨Raw₀.alter ⟨m.1, m.2.size_buckets_pos⟩ a f, Raw.WF.alter₀ m.2⟩

@[inline, inherit_doc DHashMap.alter] def Const.alter {β : Type v}
    (m : DHashMap α (fun _ => β)) (a : α) (f : Option β → Option β) : DHashMap α (fun _ => β) :=
  ⟨Raw₀.Const.alter ⟨m.1, m.2.size_buckets_pos⟩ a f, Raw.WF.constAlter₀ m.2⟩

@[inline, inherit_doc Raw.insertMany] def insertMany {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] (m : DHashMap α β) (l : ρ) : DHashMap α β :=
  ⟨(Raw₀.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).1,
   (Raw₀.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline, inherit_doc Raw.Const.insertMany] def Const.insertMany {β : Type v}
    {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap α (fun _ => β)) (l : ρ) :
    DHashMap α (fun _ => β) :=
  ⟨(Raw₀.Const.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).1,
   (Raw₀.Const.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline, inherit_doc Raw.Const.insertManyIfNewUnit] def Const.insertManyIfNewUnit
    {ρ : Type w} [ForIn Id ρ α] (m : DHashMap α (fun _ => Unit)) (l : ρ) :
    DHashMap α (fun _ => Unit) :=
  ⟨(Raw₀.Const.insertManyIfNewUnit ⟨m.1, m.2.size_buckets_pos⟩ l).1,
   (Raw₀.Const.insertManyIfNewUnit ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insertIfNew₀ m.2⟩

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/-- Partition a hash map into two hash map based on a predicate. -/
@[inline] def partition (f : (a : α) → β a → Bool)
    (m : DHashMap α β) : DHashMap α β × DHashMap α β :=
  m.fold (init := (∅, ∅)) fun ⟨l, r⟩  a b =>
    if f a b then
      (l.insert a b, r)
    else
      (l, r.insert a b)

@[inline, inherit_doc Raw.toArray] def toArray (m : DHashMap α β) :
    Array ((a : α) × β a) :=
  m.1.toArray

@[inline, inherit_doc Raw.Const.toArray] def Const.toArray {β : Type v}
    (m : DHashMap α (fun _ => β)) : Array (α × β) :=
  Raw.Const.toArray m.1

@[inline, inherit_doc Raw.keysArray] def keysArray (m : DHashMap α β) :
    Array α :=
  m.1.keysArray

@[inline, inherit_doc Raw.values] def values {β : Type v}
    (m : DHashMap α (fun _ => β)) : List β :=
  m.1.values

@[inline, inherit_doc Raw.valuesArray] def valuesArray {β : Type v}
    (m : DHashMap α (fun _ => β)) : Array β :=
  m.1.valuesArray

/-- Computes the union of the given hash maps, by traversing `m₂` and inserting its elements into `m₁`. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : DHashMap α β) : DHashMap α β :=
  m₂.fold (init := m₁) fun acc x => acc.insert x

instance [BEq α] [Hashable α] : Union (DHashMap α β) := ⟨union⟩

@[inline, inherit_doc Raw.Const.unitOfArray] def Const.unitOfArray [BEq α] [Hashable α] (l : Array α) :
    DHashMap α (fun _ => Unit) :=
  Const.insertManyIfNewUnit ∅ l

@[inherit_doc Raw.Internal.numBuckets] def Internal.numBuckets
    (m : DHashMap α β) : Nat :=
  Raw.Internal.numBuckets m.1

instance [BEq α] [Hashable α] [Repr α] [(a : α) → Repr (β a)] : Repr (DHashMap α β) where
  reprPrec m prec := Repr.addAppParen ("Std.DHashMap.ofList " ++ reprArg m.toList) prec

end Unverified

@[inline, inherit_doc Raw.ofList] def ofList [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    DHashMap α β :=
  insertMany ∅ l

@[inline, inherit_doc Raw.Const.ofList] def Const.ofList {β : Type v} [BEq α] [Hashable α]
    (l : List (α × β)) : DHashMap α (fun _ => β) :=
  Const.insertMany ∅ l

@[inline, inherit_doc Raw.Const.unitOfList] def Const.unitOfList [BEq α] [Hashable α] (l : List α) :
    DHashMap α (fun _ => Unit) :=
  Const.insertManyIfNewUnit ∅ l

end Std.DHashMap
