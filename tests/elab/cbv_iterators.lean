module

import Std.Data.Iterators

open Std

set_option cbv.warning false

-- Basic list iterator to array
example : [1, 2, 3].iter.toArray = #[1, 2, 3] := by
  cbv

-- Empty list
example : ([] : List Nat).iter.toArray = #[] := by
  cbv

-- Single element
example : [42].iter.toList = [42] := by
  cbv

-- toListRev
example : [1, 2, 3].iter.toListRev = [3, 2, 1] := by
  cbv
