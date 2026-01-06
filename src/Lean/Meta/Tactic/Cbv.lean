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

def genCongrEqn (n : Name) : MetaM Expr := do
  trace[Meta.Tactic] "generating congruence eqn out of {n}"
  let e ← mkConstWithLevelParams n
  let eTy ← inferType e
  forallTelescope eTy fun xs eqBody => do
    let some (_, lhs, rhs) := eqBody.eq? | throwError "Expected equation"
    let func := lhs.getAppFn
    let patterns := lhs.getAppArgs
    trace[Meta.Tactic] "func: {func}, patterns: {patterns}, rhs: {rhs}"

    let patternTypes ← patterns.mapM inferType
    let unrestricatedNames ← patternTypes.mapM (fun _ => mkFreshUserName `x)

    withLocalDeclsDND (unrestricatedNames.zip patternTypes) fun unrestrictedFVars => do
      let eqTypes := unrestrictedFVars.zip patterns
      let eqTypes ← eqTypes.mapM (fun (ufv, pat) => mkEq ufv pat)
      let hypNames ← eqTypes.mapM (fun _ => mkFreshUserName `h)
      withLocalDeclsDND (hypNames.zip eqTypes) fun hFVars => do
        trace[Meta.Tactic] "unrestricted fvars: {unrestrictedFVars}, hFVars: {hFVars}"
        let otherCongr ← mkHCongr func
        let some congr ← mkCongrSimp? func | throwError "failed"
        trace[Meta.Tactic] "otherCongr: {otherCongr.type}, og: {congr.type}"
        let mut hp := congr.proof
        let toApply := (unrestrictedFVars.zip patterns).zip hFVars
        for ((ufv, pv), heq) in toApply do
          hp := mkAppN hp #[ufv, pv, heq]
        let res ← mkEqTrans hp (mkAppN e xs)
        let res ← mkLambdaFVars hFVars res
        let res ← mkLambdaFVars xs res
        mkLambdaFVars unrestrictedFVars res

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
    | .letE _ _ _ _ _ => evalCbv (← zetaReduce e)
    | .proj _ _ _ => mkRefl e

    | _ => mkRefl e

  partial def evalApp (e : Expr) : MetaM EvalResult := do
   trace[Meta.Tactic] "Evaluating application {e.getAppFn} {e.getAppArgs}"
   if e.getAppFn.isConst then
    let name := e.getAppFn.constName
    trace[Meta.Tactic] "name: {name}"
    let eqns ← genCongrEqns name
    trace[Meta.Tactic] "eqns: {eqns}"
    let rhsId ← mkFreshMVarId
    let rhs ← mkFreshExprMVarWithId rhsId

    trace[Meta.Tactic] "unfolded: {rhs}"
    let goalType ← mkEq e rhs
    let goal ← mkFreshExprMVar goalType
    let state ← saveState
    trace[Meta.Tactic] "goal: {goal}"
    for eqn in eqns do
      trace[Meta.Tactic] "Trying: {eqn}"
      try
        let newGoals ← goal.mvarId!.apply eqn
        for goal in newGoals do
          if !(← goal.isAssigned) then
            trace[Meta.Tactic] "Solving it using refl"
            goal.refl
            trace[Meta.Tactic] "Assigned after refl: {← goal.isAssigned}"
        break
      catch _ =>
        trace[Meta.Tactic] "Restoring state"
        restoreState state
    let goal ← instantiateMVars goal
    let some (_, _, rhs) := (← inferType goal).eq? | throwError "Expected equation"
    return {value := rhs, proof := goal}

   else
    mkRefl e

end
def cbv (e : Expr) : MetaM EvalResult := do
  let appFn := e.getAppFn
  let name := appFn.constName!
  let res ← genCongrEqns name
  trace[Meta.Tactic] "congr eqns for {name}: {res}"


  mkRefl e
  -- trace[Meta.Tactic] "Trying to evaluate expression {e}"
  -- trace[Meta.Tactic] "The function is: {e.getAppFn.constName}"
  -- evalCbv e



end Lean.Meta
