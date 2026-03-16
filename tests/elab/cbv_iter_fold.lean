module

import Std.Data.Iterators

open Std

set_option cbv.warning false

-- Test fold on list iterator
example : [1, 2, 3].iter.fold (· + ·) 0 = (6 : Nat) := by cbv

-- Test fold on empty list
example : ([] : List Nat).iter.fold (· + ·) 0 = 0 := by cbv

-- Test fold with different accumulator
example : [1, 2, 3].iter.fold (· * ·) 1 = (6 : Nat) := by cbv

-- Test fold on mapped iterator
example : ([1, 2, 3].iter.map (· + 1)).fold (· + ·) 0 = (9 : Nat) := by cbv

-- Test any
example : [1, 2, 3].iter.any (· == 2) = true := by cbv
example : [1, 2, 3].iter.any (· == 5) = false := by cbv

-- Test all
example : [1, 2, 3].iter.all (· > 0) = true := by cbv
example : [1, 2, 3].iter.all (· > 2) = false := by cbv
