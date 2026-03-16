import Lean.Meta.Tactic.Cbv.BuiltinCbvEval.Iter
import Std.Data.Iterators.Combinators.Drop
import Std.Data.Iterators.Lemmas.Combinators.Drop

set_option cbv.warning false

/-! ### Basic producer tests -/

example : [1, 2, 3].iter.toList = [1, 2, 3] := by cbv
example : [1, 2, 3].iter.toArray = #[1, 2, 3] := by cbv
example : ([] : List Nat).iter.toList = [] := by cbv
example : ([] : List Nat).iter.toArray = #[] := by cbv

/-! ### Map tests -/

example : ([1, 2, 3].iter.map (· + 1)).toList = [2, 3, 4] := by cbv
example : ([1, 2, 3].iter.map (· + 1)).toArray = #[2, 3, 4] := by cbv
example : ([1, 2, 3].iter.map (· * 2)).toList = [2, 4, 6] := by cbv
example : (([] : List Nat).iter.map (· + 1)).toList = [] := by cbv



/-! ### Filter tests -/

example : ([1, 2, 3, 4].iter.filter (· % 2 == 0)).toList = [2, 4] := by cbv
example : ([1, 2, 3, 4].iter.filter (· % 2 == 0)).toArray = #[2, 4] := by cbv

/-! ### FilterMap tests -/

example : ([1, 2, 3, 4].iter.filterMap (fun x => if x % 2 == 0 then some (x * 10) else none)).toList
    = [20, 40] := by cbv

/-! ### Fold tests -/

example : [1, 2, 3].iter.fold (· + ·) 0 = 6 := by cbv
example : [1, 2, 3, 4].iter.fold (· * ·) 1 = 24 := by cbv
example : ([] : List Nat).iter.fold (· + ·) 0 = 0 := by cbv

/-! ### Composed combinator tests -/

example : ([1, 2, 3, 4].iter.filter (· % 2 == 0) |>.map (· * 10)).toList = [20, 40] := by cbv
example : ([1, 2, 3].iter.map (· + 1) |>.filter (· % 2 == 0)).toList = [2, 4] := by cbv
example : ([1, 2, 3].iter.map (· * 2) |>.map (· + 1)).toList = [3, 5, 7] := by cbv

/-! ### String operations using iterators internally -/

example : "abc".contains 'b' = true := by cbv
example : "abc".contains 'd' = false := by cbv
example : "hello".contains (· == 'l') = true := by cbv
example : String.toNat? "192" = some 192 := by cbv
example : String.toNat? "0" = some 0 := by cbv
example : String.toNat? "" = none := by cbv
example : "hello".foldl (fun n _ => n + 1) 0 = 5 := by cbv

def filterBySubstring (strings : Array String) (substring : String) : Array String :=
  -- Uses KMP string search!
  strings.filter (·.contains substring)

example : filterBySubstring #[] "john" = #[] := by cbv
example : filterBySubstring #["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" = #["xxx", "xxxAAA", "xxx"] := by cbv
example : filterBySubstring #["xxx", "asd", "aaaxxy", "john doe", "xxxAAA", "xxx"] "xx" = #["xxx", "aaaxxy", "xxxAAA", "xxx"] := by cbv
example : filterBySubstring #["grunt", "trumpet", "prune", "gruesome"] "run" = #["grunt", "prune"] := by cbv

def allPrefixes (string : String) : Array String.Slice :=
  if string = "" then
    #[]
  else
    ((string.positions.drop 1).map (string.sliceTo ·.1) |>.toArray).push string

example : allPrefixes "" = #[] := by cbv
example : allPrefixes "asdfgh" == #["a".toSlice, "as", "asd", "asdf", "asdfg", "asdfgh"] := by cbv
example : allPrefixes "WWW" == #["W".toSlice, "WW", "WWW"] := by cbv

def sumSquares (xs : List Rat) : Int :=
  xs.map (·.ceil ^ (2 : Nat)) |>.sum

/-! ### Rational arithmetic tests -/

example : sumSquares [1, 2, 3] = 14 := by cbv
example : sumSquares [1.0, 2, 3] = 14 := by cbv
example : sumSquares [1, 3, 5, 7] = 84 := by cbv
example : sumSquares [1.4, 4.2, 0] = 29 := by cbv
example : sumSquares [-2.4, 1, 1] = 6 := by cbv
example : sumSquares [100, 1, 15, 2] = 10230 := by cbv
example : sumSquares [10000, 10000] = 200000000 := by cbv
example : sumSquares [-1.4, 4.6, 6.3] = 75 := by cbv
example : sumSquares [-1.4, 17.9, 18.9, 19.9] = 1086 := by cbv
example : sumSquares [0] = 0 := by cbv
example : sumSquares [-1] = 1 := by cbv
example : sumSquares [-1, 1, 0] = 2 := by cbv

/-! ### String case swapping and reversal tests -/

def reverseString (s : String) : String :=
  s.revChars.fold (init := "") fun sofar c => sofar.push c

def swapCase (c : Char) : Char :=
  if c.isUpper then
    c.toLower
  else if c.isLower then
    c.toUpper
  else
    c

def solve (s : String) : String :=
  if s.contains Char.isAlpha then
    s.map swapCase
  else
    reverseString s

example : solve "AsDf" = "aSdF" := by cbv
example : solve "1234" = "4321" := by cbv
example : solve "ab" = "AB" := by cbv
example : solve "#a@C" = "#A@c" := by cbv
example : solve "#AsdfW^45" = "#aSDFw^45" := by cbv
example : solve "#6@2" = "2@6#" := by cbv
example : solve "#$a^D" = "#$A^d" := by cbv
example : solve "#ccc" = "#CCC" := by cbv

/-! ### Subarray iteration tests -/

def isSorted (xs : Array Nat) : Bool := Id.run do
  if h : xs.size > 0 then
    let mut last := xs[0]
    let mut repeated := false
    for x in xs[1...*] do
      match compare last x with
      | .lt =>
        last := x
        repeated := false
      | .eq =>
        if repeated then
          return false
        else
          repeated := true
      | .gt =>
        return false
  return true

example : isSorted #[5] = true := by cbv
example : isSorted #[1, 2, 3, 4, 5] = true := by cbv
example : isSorted #[1, 3, 2, 4, 5] = false := by cbv
example : isSorted #[1, 2, 3, 4, 5, 6] = true := by cbv
example : isSorted #[1, 2, 3, 4, 5, 6, 7] = true := by cbv
example : isSorted #[1, 3, 2, 4, 5, 6, 7] = false := by cbv
example : isSorted #[] = true := by cbv
example : isSorted #[1] = true := by cbv
example : isSorted #[3, 2, 1] = false := by cbv
example : isSorted #[1, 2, 2, 2, 3, 4] = false := by cbv
example : isSorted #[1, 2, 3, 3, 3, 4] = false := by cbv
example : isSorted #[1, 2, 2, 3, 3, 4] = true := by cbv
example : isSorted #[1, 2, 3, 4] = true := by cbv

/-! ### Inclusive range iteration tests -/

def f (n : Nat) : List Nat := Id.run do
  let mut ret : List Nat := []
  for i in 1...=n do
    if i % 2 = 0 then
      let mut x := 1
      for j in 1...=i do x := x * j
      ret := x :: ret
    else
      let mut x := 0
      for j in 1...=i do x := x + j
      ret := x :: ret
  return ret.reverse

example : f 5 = [1, 2, 6, 24, 15] := by cbv
example : f 7 = [1, 2, 6, 24, 15, 720, 28] := by cbv
example : f 1 = [1] := by cbv
example : f 3 = [1, 2, 6] := by cbv

def hasCloseElements (xs : Array Rat) (threshold : Rat) : Bool := Id.run do
  let sorted := xs.mergeSort
  for h : i in *...(sorted.size - 1) do
    if (sorted[i + 1] - sorted[i]).abs < threshold then
      return true
  return false

example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.3 = true := by cbv
example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.05 = false := by cbv
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.95 = true := by cbv
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.8 = false := by cbv
example : hasCloseElements #[1.0, 2.0, 3.0, 4.0, 5.0, 2.0] 0.1 = true := by cbv
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 1.0 = true := by cbv
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 0.5 = false := by cbv
