module

import Std.Data.Iterators

open Std

set_option cbv.warning false

-- Basic list iterator to array
example : [1, 2, 3].iter.toArray = #[1, 2, 3] := by cbv

-- Empty list
example : ([] : List Nat).iter.toArray = #[] := by cbv

-- Map with toList
example : ([1, 2, 3].iter.map (· + 1)).toList = [2, 3, 4] := by cbv

-- Map with toArray
example : ([1, 2, 3].iter.map (· + 1)).toArray = #[2, 3, 4] := by cbv

-- Map empty
example : (([] : List Nat).iter.map (· * 2)).toArray = #[] := by cbv

-- Map single element
example : ([10].iter.map (· - 3)).toList = [7] := by cbv
