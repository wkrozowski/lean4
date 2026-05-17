import Lean.LibrarySuggestions.MePo

/-!
Regression test: the MePo premise selector must return suggestions in
score-descending order.

A stale `.reverse` in `mepoSelector` (left over from before the selector was
made score-sorting) flipped the order to score-ascending, so `.take` returned
the lowest-scoring premises instead of the best ones.
-/

open Lean Lean.Elab.Tactic Lean.LibrarySuggestions

example (a b : Int) : a + b = b + a := by
  run_tac do
    let sel : Selector := mepoSelector (useRarity := false)
    let s ← sel (← getMainGoal) {}
    let mut prev? : Option Float := none
    for x in s do
      if let some prev := prev? then
        unless prev ≥ x.score do
          throwError "MePo suggestions are not score-descending: \
            score {prev} precedes score {x.score}"
      prev? := some x.score
  sorry
