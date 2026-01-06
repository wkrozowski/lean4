module

prelude
public import Lean.Meta.Tactic.Delta
public import Lean.Meta.Tactic.Unfold
public import Lean.Meta.Tactic.Simp.Main
public import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Refl

public section

namespace Lean.Meta

partial def traverseHCongr (e : Expr) (patterns : Array Expr) (f : Array Expr → Array Expr  → Expr → MetaM α) : MetaM α :=
  go e patterns #[] #[]
    where
  go (e : Expr) (patterns : Array Expr) (accUr accHs : Array Expr) : MetaM α := match
    patterns with
    | #[] => f accUr accHs e
    | _ => do
      forallBoundedTelescope e (.some 1) fun xs body => do
        let accUr := accUr ++ xs
        forallBoundedTelescope (←instantiateForall body #[patterns[0]!]) (.some 1) fun ys body => do
          let accHs := accHs ++ ys
          go body (patterns.extract 1) accUr accHs

def genCongrHEqn (n : Name) : MetaM Expr := do
  trace[Meta.Tactic] "generating congruence eqn out of {n}"
  let e ← mkConstWithLevelParams n
  forallTelescope (← inferType e) fun xs eqBody => do
    let some (_, lhs, _) := eqBody.eq? | throwError "Expected equation"
    let func := lhs.getAppFn
    let patterns := lhs.getAppArgs
    let otherCongr ← mkHCongr func
    traverseHCongr otherCongr.type patterns fun unrestricted heqs _ => do
      let toApply := (unrestricted.zip patterns).zip heqs
      let mut res := otherCongr.proof
      for ((uf, pv), hv) in toApply do
        res := mkAppN res #[uf, pv, hv]
      res ← mkHEqTrans res (← mkHEqOfEq (mkAppN e xs))
      res ← mkLambdaFVars heqs res
      res ← mkLambdaFVars xs res
      res ← mkLambdaFVars unrestricted res
      return res

def genCongrEqns (n : Name) : MetaM (Array Expr) := do
  let some res ← getEqnsFor? n | throwError "no eqns found for {n}"
  let mut eqns := #[]
  for eqn in res do
    eqns := eqns.push (← genCongrHEqn eqn)
  return eqns

structure EvalResult where
  value : Expr
  proof : Expr

def mkRefl (e : Expr) : MetaM EvalResult := do
  return {value := e, proof := (← mkEqRefl e) }

def isValue (e : Expr) : MetaM Bool := do
  if (←inferType e).isProp then
    return true
  else
  match e with
  | .lam _ _ _ _ => return false
  | .const name _ =>
    let info ← getConstInfo name
    return info.isCtor
  | .app fn arg =>
    if (← isValue fn) then
        isValue arg
    else
      return false
  | .forallE _ _ _ _ => return false
  | .lit _ => return true
  | .proj _ _ _ => return false
  | .mdata _ e => isValue e
  | .bvar _ => return false
  | .letE _ _ _ _ _ => return false
  | .sort _ => return true
  | .mvar _ => return false
  | .fvar _  => return false

def tryCongEqns (e : Expr) : MetaM EvalResult := do
  let name := e.getAppFn.constName
  let eqns ← genCongrEqns name
  let rhsId ← mkFreshMVarId
  let rhs ← mkFreshExprMVarWithId rhsId

  trace[Meta.Tactic] "unfolded: {rhs}"
  let goalType ← mkHEq e rhs
  let goal ← mkFreshExprMVar goalType
  let state ← saveState
  for eqn in eqns do
    try
      let newGoals ← goal.mvarId!.apply eqn
      for goal in newGoals do
          let goalType ← goal.getType
          if goalType.isHEq then
            goal.hrefl
          if goalType.isEq then
            goal.refl
      break
    catch _ =>
      trace[Meta.Tactic] "Restoring state"
      restoreState state
  let goal ← instantiateMVars goal
  guard !goal.hasMVar
  trace[Meta.Tactic] "After applying eqns, goal: {goal}"
  let goal ← mkEqOfHEq goal
  trace[Meta.Tactic] "Final goal: {goal}"
  let some (_, _, rhs) := (← inferType goal).eq? | throwError "Expected equation"
  return {value := rhs, proof := goal}

def tryUnfold (e : Expr) (args : Array EvalResult) : MetaM EvalResult := do
  assert! e.getAppFn.isConst
  let name := e.getAppFn.constName
  let withValArguments := mkAppN (e.getAppFn) (args.map (·.value))
  trace[Meta.Tactic] "Trying to unfold {name} with args {withValArguments}"
  let otherCongr ← mkHCongr e.getAppFn
  trace[Meta.Tactic] "Congruence lemma: {otherCongr.proof}"
  let hCongrArgs := (e.getAppArgs.zip (args.map (·.value))).zip (args.map (·.proof))
  trace[Meta.Tactic] "hCongrArgs: {hCongrArgs}"
  let mut congrProof := otherCongr.proof
  for (((arg, val), prf), type) in hCongrArgs.zip otherCongr.argKinds do
    if type == .heq then
      congrProof := mkAppN congrProof #[arg, val, (←mkHEqOfEq prf)]
    else
      congrProof := mkAppN congrProof #[arg, val, prf]
  let unfoldRes ← unfold withValArguments name
  let goalType ← mkEq withValArguments unfoldRes.expr
  let proof ← mkFreshExprMVar goalType
  if unfoldRes.proof?.isSome then
    proof.mvarId!.assign unfoldRes.proof?.get!
  else
    proof.mvarId!.refl
  let proof ← instantiateMVars proof
  let proof ← mkHEqOfEq proof
  try
    let res ← mkHEqTrans congrProof proof
    let res ← mkEqOfHEq res
    return {value := unfoldRes.expr, proof := res}
  catch _ =>
    trace[Meta.Tactic] "proof: {proof}, congrProof: {congrProof}"
    throwError "Caught the error"




mutual
 partial def evalCbv (e : Expr) : MetaM EvalResult := do

  let isVal ← isValue e
  if isVal then
    trace[Meta.Tactic] "Returning, as detected a value {e}"
    mkRefl e
  else
    match e with
    | .lam _ _ _ _ => mkRefl e
    | .app _ _ =>
        evalApp e
    | .letE _ _ _ _ _ => return ⟨(← zetaReduce e), (← mkEqRefl e)⟩
    | .proj _ _ _ =>  do
      trace[Meta.Tactic] "Reducing projection {e}"
      let some reduced ← reduceProj? e | throwError "Failed to reduce projection {e}"
      return ⟨(reduced), (← mkEqRefl e)⟩
    | _ => mkRefl e

  partial def evalApp (e : Expr) : MetaM EvalResult := do
    trace[Meta.Tactic] "Evaluating application {e.getAppFn} {e.getAppArgs}"
    if e.getAppFn.isConst then
      trace[Meta.Tactic] "Function is a constant"
      let args ← e.getAppArgs.mapM evalCbv
      let reduceResult ← reduceRecMatcher? e
      if reduceResult.isSome then
        return ⟨reduceResult.get!, ←mkEqRefl e⟩
      else
        tryUnfold e args
    else
      if e.getAppFn.isLambda then
        let args := e.getAppArgs
        let ⟨argVal, argProof⟩ ← evalCbv args[0]!
        let remainingArgs := args.extract 1
        trace[Meta.Tactic] "body reduces to: {argVal}"
        let mut newBody ← instantiateLambda e.getAppFn #[argVal]
        let mut proof1 := argProof
        try
          proof1 ← mkCongrArg e.getAppFn argProof
        catch _ =>
          let hcongr ← mkHCongrWithArity e.getAppFn 1
          proof1 := mkAppN hcongr.proof #[args[0]!, argVal, ←mkHEqOfEq (argProof)]
          proof1 ← mkEqOfHEq proof1
        let goal2 ← mkEq (mkApp e.getAppFn argVal) newBody
        let proof2 ← mkFreshExprMVar goal2
        proof2.mvarId!.refl
        let mut proof3 ← mkEqTrans proof1 proof2
        for arg in remainingArgs do
          proof3 ← mkCongrFun proof3 arg
        newBody := mkAppN newBody remainingArgs
        return ⟨newBody, proof3⟩
      else
        let ⟨funVal, funProof⟩ ← evalCbv e.getAppFn
        let args := e.getAppArgs
        let newRes := mkAppN funVal args
        let mut newProof := funProof
        for arg in args do
          newProof ← mkCongrFun newProof arg
        return ⟨newRes, newProof⟩
end
def cbv (e : Expr) : MetaM EvalResult := do
  trace[Meta.Tactic] "Trying to evaluate expression {e}"
  trace[Meta.Tactic] "The function is: {e.getAppFn.constName}"
  evalCbv e



end Lean.Meta
