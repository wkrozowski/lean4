module

prelude
public import Lean.Meta.Tactic.Delta
public import Lean.Meta.Tactic.Unfold
public import Lean.Meta.Tactic.Simp.Main
public import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Tactic.Refl
import Lean.Meta.Basic
import Lean.Elab.PreDefinition.EqUnfold

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
  trace[Meta.Tactic] "The equation is {e}"
  forallTelescope (← inferType e) fun xs eqBody => do
    let some (_, lhs, _) := eqBody.eq? | throwError "Expected equation"
    let func := lhs.getAppFn
    let patterns := lhs.getAppArgs
    trace[Meta.Tactic] "patterns are: {patterns}"
    let otherCongr ← mkHCongrWithArity func patterns.size
    trace[Meta.Tactic] "HCongr theorem is of type: {otherCongr.type}"
    traverseHCongr otherCongr.type patterns fun unrestricted heqs _ => do
      let toApply := (unrestricted.zip patterns).zip heqs
      trace[Meta.Tactic] "to apply: {toApply}"
      let mut res := otherCongr.proof
      for ((uf, pv), hv) in toApply do
        res := mkAppN res #[uf, pv, hv]
      trace[Meta.Tactic] "applied equation: {mkAppN e xs}"
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

def mkReflProof (e : Expr) (heq : Bool) : MetaM Expr := do
  if heq then
    mkHEqRefl e
  else
    mkEqRefl e

def mkRefl (e : Expr) (heq : Bool) : MetaM EvalResult := do
  return { value := e, proof := (← mkReflProof e heq) }

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

def makeGoalFrom (e : Expr) : MetaM MVarId := do
  let rhs ← mkFreshExprMVarWithId (← mkFreshMVarId)
  let goalType ← mkHEq e rhs
  return (← mkFreshExprMVar goalType).mvarId!

def makeGoalWithRhs (e : Expr) : MetaM (MVarId × MVarId) := do
  let rhs ← mkFreshExprMVarWithId (← mkFreshMVarId)
  let goalType ← mkHEq e rhs
  return ((← mkFreshExprMVar goalType).mvarId!, rhs.mvarId!)

def mkMainGoalFrom (e : Expr) : MetaM MVarId := do
  let rhs ← mkFreshExprMVarWithId (← mkFreshMVarId)
  let goalType ← mkEq e rhs
  let eqMVar := (← mkFreshExprMVar goalType).mvarId!
  eqMVar.eqOfHEq

partial def cbvCore (goal : MVarId) : MetaM Unit := do
  trace[Meta.Tactic] "Called {← goal.getType}"
  let type ← goal.getType
  let some (_, e, _, f) := type.heq? | throwError "Expected HEq"
  trace[Meta.Tactic] "The expression is: {e}"
  if (← isValue e) then
    goal.hrefl
    let proof ← instantiateMVars (.mvar goal)
    trace[Meta.Tactic] "The resulting proof is : {proof}"
  else
    if e.isFVar then
      goal.assumption
    else
      if e.isApp then
        trace[Meta.Tactic] "{e} is an application"
        if e.getAppFn.isLambda then
          trace[Meta.Tactic] "evaluating lambda"
          let arg := e.getAppArgs
          assert! arg.size = 1 -- for now we assume that we can only apply lambdas of arity one
          let arg := arg[0]!
          goal.withContext do
            let newGoal ← makeGoalFrom arg
            cbvCore newGoal
            let (fvars, generalizedGoal) ← goal.generalize #[{expr := arg, hName? := ← mkFreshUserName `h}]
            generalizedGoal.withContext do
              let new ← mkEqSymm (.fvar fvars[1]!)
              let new ← mkHEqOfEq new
              let new ← mkHEqTrans new (.mvar newGoal)
              let ⟨_, uponReplacement, _⟩ ← generalizedGoal.replace fvars[1]! new
              let goalType ← uponReplacement.getType
              let some (_, lhs, _, rhs) := goalType.heq? | throwError "heq expected"
              let newGoal ← mkHEq (lhs.headBeta) rhs
              let uponSubst ← uponReplacement.change newGoal
              cbvCore uponSubst
              trace[Meta.Tactic] "evaluated lambda"
        else
          trace[Meta.Tactic] "is Assigned: {← goal.isAssigned}"
          if (e.getAppFn.isConst) then
            let info ← getConstInfo e.getAppFn.constName
            let matcherInfo ← getMatcherInfo? e.getAppFn.constName!
            if matcherInfo.isSome then
              let matcherInfo := matcherInfo.get!
              let levels := e.getAppFn.constLevels!
              let congrEqns ← Match.genMatchCongrEqns e.getAppFn.constName!
              let congrEqns := congrEqns.map (fun x => mkConst x levels)
              trace[Meta.Tactic] "congrEqns: {congrEqns}"
              trace[Meta.Tactic] "matcherInfo: {matcherInfo.numDiscrs}, {matcherInfo.numParams}"
              throwError "matcher case"
            else
              if info.isCtor then
                trace[Meta.Tactic] "is const"
                let numArgs := e.getAppNumArgs
                let levels := e.getAppFn.constLevels!
                let some congrThm ← mkHCongrWithArityForConst? e.getAppFn.constName levels numArgs | throwError "could not genereate congruence theorem for constructor"
                let args := e.getAppArgs
                goal.withContext do
                  let mut congrThmProof := congrThm.proof
                  for (arg, argKind) in args.zip congrThm.argKinds do
                    let (proof, rhs) ← makeGoalWithRhs arg
                    cbvCore proof
                    congrThmProof := mkAppN congrThmProof #[arg, (Expr.mvar rhs)]
                    if argKind == .eq then
                      congrThmProof := mkApp congrThmProof (← mkEqOfHEq (.mvar proof))
                    else
                      congrThmProof := (.mvar proof)
                    goal.assign congrThmProof
              else
                let name := e.getAppFn.constName
                let levels := e.getAppFn.constLevels!
                let some unfoldEq ← getConstUnfoldEqnFor? name | throwError
                "cannot be unfolded"
                let unfoldEq := mkConst unfoldEq levels
                let unfoldEqTy ← inferType unfoldEq
                trace[Meta.Tactic] "unfoldEqTy: {unfoldEqTy}"
                let some (_,_,rhs) := unfoldEqTy.eq? | throwError "equality expected"
                let newLhs := mkAppN rhs e.getAppArgs
                let newGoalType ← mkHEq newLhs f
                goal.withContext do
                  let newGoal ← mkFreshExprMVar newGoalType
                  cbvCore newGoal.mvarId!
                  -- We create fvar of the type of the lhs
                  let funType ← inferType e.getAppFn
                  let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default  funType fun var => do
                    let theoremLhs := mkAppN var e.getAppArgs
                    let theoremBody ← mkHEq theoremLhs f
                    mkLambdaFVars #[var] theoremBody
                  let congrArg ← mkCongrArg congrArgFun unfoldEq
                  let congrArg ← mkAppOptM ``Eq.mpr #[.none, .none, congrArg, newGoal]
                  goal.assign congrArg
                  trace[Meta.Tactic] "is Assigned: {← goal.isAssigned}"
                  return
          else
            throwError "Unhandled case"

def cbv (e : Expr) : MetaM EvalResult := do

  trace[Meta.Tactic] "Trying to evaluate expression {e}"
  let goal ← makeGoalFrom e
  cbvCore goal
  let proof ← instantiateMVars <| .mvar goal
  let proof ← mkEqOfHEq proof
  let some (_, _, value) := (← inferType proof).eq? | throwError "eq expected"
  trace[Meta.Tactic] "value: {value}, proof: {proof}"
  return ⟨value, proof⟩
end Lean.Meta
