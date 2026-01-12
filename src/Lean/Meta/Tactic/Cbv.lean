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
  | .mvar _ => throwError "Trying to evaluate an unassigned metavariable"
  | .fvar _  => return false

def makeGoalFrom (e : Expr) : MetaM MVarId := do
  let rhs ← mkFreshExprMVarWithId (← mkFreshMVarId)
  let goalType ← mkHEq e rhs
  return (← mkFreshExprMVar goalType).mvarId!


def extractLhsFromGoal (goal : MVarId) : MetaM Expr := do
  let type ← goal.getType
  let some (_, e, _, _) := type.heq? | throwError "Expected HEq"
  return e

def extractRhsFromGoal (goal : MVarId) : MetaM Expr := do
  let type ← goal.getType
  let some (_, _, _, e) := type.heq? | throwError "Expected HEq"
  return e

/- We expect that goal is a heterogenous equality -/
def tryValue (goal : MVarId) : MetaM Unit := do
  let e ← extractLhsFromGoal goal
  if (← isValue e) then
    goal.hrefl
  else
    throwError "The left hand side {e} of the goal {← goal.getType} is not a value."

def tryClosingGoal (candidates : Array Expr) (goal : MVarId) : MetaM Unit := do
  candidates.firstM (do let [] ← goal.apply · | throwError "Produces subgoals")

mutual
  partial def tryMatchCongrEqns (congrEqn : Expr) (solvedDiscriminants : Array Expr) : MetaM Expr := do
    let (hyps, _) ← forallMetaTelescope (← inferType congrEqn)
    let hyps := hyps.map (·.mvarId!)
    for hyp in hyps do
      hyp.withContext do
        let hypTy ← hyp.getType
        if (hypTy.isEq) then
          let heqGoal ← hyp.eqOfHEq
          tryClosingGoal solvedDiscriminants heqGoal <|> throwError "applying didnt work"
    unless (← hyps.allM (·.isAssigned)) do
      throwError "Not all goals are assigned"

    let hyps := hyps.map Expr.mvar
    let hyps ← hyps.mapM instantiateMVars
    let res := mkAppN congrEqn hyps
    if res.hasMVar then
      throwError "result has unassigned mvars"
    return mkAppN congrEqn hyps

  partial def tryMatcher (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    let f := e.getAppFn
    let args := e.getAppArgs
    let ctorName := f.constName
    let some matcherInfo ← getMatcherInfo? e.getAppFn.constName! | throwError "Not a matcher, skipping"

    -- For now we do not handle overappplied matchers
    assert! matcherInfo.arity = e.getAppNumArgs

    let congrEqns ← Match.genMatchCongrEqns ctorName
    let congrEqns := congrEqns.map (mkConst · f.constLevels!)
    let congrEqns := congrEqns.map (mkAppN · args)

    let ⟨discrLower, discrUpper⟩ := matcherInfo.getDiscrRange
    let discriminants := args.extract discrLower discrUpper
    goal.withContext do
      -- We construct goals for discriminants
      let discriminantsGoals ← discriminants.mapM (makeGoalFrom ·)
      -- And solve them
      discard <| discriminantsGoals.mapM (cbvCore)
      let solvedDiscriminants := discriminantsGoals.map (Expr.mvar ·)

      trace[Meta.Tactic] "Discriminants are: {solvedDiscriminants}"
      let solution ← congrEqns.firstM (tryMatchCongrEqns · solvedDiscriminants)
      let some (_, _, _, solutionValue) := (← inferType solution).heq? | throwError "Heterogenous equality expected"
      let newGoal ← makeGoalFrom solutionValue
      cbvCore newGoal
      let rhsResult ← instantiateMVars (.mvar newGoal)
      let toAssign ← mkHEqTrans solution rhsResult
      let [] ← goal.apply toAssign | throwError "could not apply"

  partial def handleCtor (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    let f := e.getAppFn
    let ctorName := f.constName
    let args := e.getAppArgs
    let some congrThm ← mkHCongrWithArityForConst? ctorName f.constLevels! e.getAppNumArgs | throwError "Could not genereate congruence theorem for constructor {ctorName}"
    goal.withContext do
      let mut congrThmProof := congrThm.proof
      for (arg, argKind) in args.zip congrThm.argKinds do
        let proof ← makeGoalFrom arg
        cbvCore proof
        let evalResult ← instantiateMVars (.mvar proof)
        let evalResultType ← inferType evalResult
        let some (_, _, _, value) := evalResultType.heq? | throwError "Expected heterogenous equality"
        trace[Meta.Tactic] "evalResult: {evalResult}, value: {value}"
        congrThmProof := mkAppN congrThmProof #[arg, value]
        if argKind == .eq then
          congrThmProof := mkApp congrThmProof (← mkEqOfHEq (evalResult))
        else
          congrThmProof := (.mvar proof)
      assert! (!congrThmProof.hasMVar)
      goal.assign congrThmProof
      trace[Meta.Tactic] "congrThmProof: {congrThmProof}"
      trace[Meta.Tactic] "ctor goal: {goal}"

  partial def handleUnfolding (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    let goalRhs ← extractRhsFromGoal goal
    guard e.isApp
    let f := e.getAppFn
    guard f.isConst
    let name := f.constName
    let some unfoldEq ← getConstUnfoldEqnFor? name | throwError
                  "Could not obtain unfold equation for: {name}"
    let unfoldEq := mkConst unfoldEq f.constLevels!
    let some (_,_,rhs) := (←inferType unfoldEq).eq? | throwError "fatal error : equality expected at {←inferType unfoldEq}"
    let newGoalType ← mkHEq (mkAppN rhs e.getAppArgs) goalRhs
    goal.withContext do
      let unfoldedGoal ← mkFreshExprMVar newGoalType
      cbvCore unfoldedGoal.mvarId!
      let unfoldedGoalMVarID := unfoldedGoal.mvarId!
      let unfoldedGoal ← instantiateMVars unfoldedGoal
      guard (← unfoldedGoalMVarID.isAssigned)
      -- Then we prepare to fill the goal
      let fType ← inferType f
      let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default fType fun var => do
        let theoremLhs := mkAppN var e.getAppArgs
        let theoremBody ← mkHEq theoremLhs goalRhs
        mkLambdaFVars #[var] theoremBody
      let congrArg ← mkCongrArg congrArgFun unfoldEq
      let congrArg ← mkAppOptM ``Eq.mpr #[.none, .none, congrArg, unfoldedGoal]
      goal.assign congrArg
      guard (← goal.isAssigned)
      trace[Meta.Tactic] "goal: {goal}"
    trace[Meta.Tactic] "Unfold equation is: {unfoldEq}"

  partial def handleLambda (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    let rhs ← extractRhsFromGoal goal
    guard e.isApp
    let lambdaFn := e.getAppFn
    let args := e.getAppArgs
    guard lambdaFn.isLambda
    -- For now we assume that there is only one argument to a lambda function
    guard (args.size == 1)
    let headArg := args[0]!
    goal.withContext do
      let valGoal ← makeGoalFrom headArg
      cbvCore valGoal
      let argType ← inferType headArg
      let newMVarType : Expr ← withLocalDeclD (← mkFreshUserName `x) argType fun argVar => do
        let eqType ← mkHEq argVar (←extractRhsFromGoal valGoal)
        withLocalDeclD (←mkFreshUserName `h) eqType fun eqType => do
          let body ← mkHEq (← instantiateLambda lambdaFn #[argVar]) rhs
          mkForallFVars #[argVar, eqType] body
      let newMVar ← mkFreshExprMVar newMVarType
      let toFill := mkAppN newMVar #[headArg, (.mvar valGoal)]
      goal.assign toFill
      let (_, generalizedGoal) ← newMVar.mvarId!.introN 2
      generalizedGoal.withContext do
        cbvCore generalizedGoal

  partial def cbvCore (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    trace[Meta.Tactic] "The expression is: {e}"
    tryValue goal <|> do
      if e.isFVar then
        goal.assumption
      else
        if e.isApp then
          trace[Meta.Tactic] "{e} is an application"
          if e.getAppFn.isLambda then
            handleLambda goal
          else
            trace[Meta.Tactic] "is Assigned: {← goal.isAssigned}"
            if (e.getAppFn.isConst) then
              let info ← getConstInfo e.getAppFn.constName
              let matcherInfo ← getMatcherInfo? e.getAppFn.constName!
              if matcherInfo.isSome then
                tryMatcher goal
              else
                if info.isCtor then
                  handleCtor goal
                else
                  handleUnfolding goal
            else
              throwError "Unhandled case"
end

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
