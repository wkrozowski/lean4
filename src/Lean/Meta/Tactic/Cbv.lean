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
    assert! (← hyps.allM (·.isAssigned))
    let hyps := hyps.map Expr.mvar
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
      trace[Meta.Tactic] "solution: {solution}"
      let [] ← goal.apply solution | throwError "didnt expect any subgoals"

      -- let some (_, _, _, b) := (← inferType solution).heq? | throwError "Heternogenous equality expected"
      -- let rhs ← extractRhsFromGoal goal
      -- let newGoalType ← mkHEq b rhs
      -- let continueGoal ← mkFreshExprMVar newGoalType
      -- cbvCore continueGoal.mvarId!
      -- trace[Meta.Tactic] "newGoalType: {newGoalType}, solution: {solution}"
      -- let res ← mkHEqTrans solution (← instantiateMVars continueGoal)
      -- let remaining ← goal.apply res
      -- discard <| remaining.mapM (MVarId.hrefl)


  partial def handleCtor (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    let f := e.getAppFn
    let ctorName := f.constName
    let args := e.getAppArgs
    let some congrThm ← mkHCongrWithArityForConst? ctorName f.constLevels! e.getAppNumArgs | throwError "Could not genereate congruence theorem for constructor {ctorName}"
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
      trace[Meta.Tactic] "UnfoldedGoal: {unfoldedGoal.mvarId!}"
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
      let evaluatedVal ← inferType (.mvar valGoal)
      let some (_, _, _, evaluatedVal) := evaluatedVal.heq? | throwError "heq expected"
      let (argFVar ,test) ← goal.note (← mkFreshUserName `x) headArg
      test.withContext do
        let (_, test2) ← test.note (← mkFreshUserName `h) (.mvar valGoal) (← mkEq (.fvar argFVar) evaluatedVal)
        trace[Meta.Tactic] "test2: {test2}, evaluatedVal: {evaluatedVal}"
        throwError "sorry"
      let (fvars, generalizedGoal) ← goal.generalize #[{expr := headArg, hName? := ← mkFreshUserName `h}]
      -- Since we abstract only one goal we should have two fvars in the context
      assert! (fvars.size = 2)
      generalizedGoal.withContext do
        let newHyp ← mkEqSymm (.fvar fvars[1]!)
        let newHyp ← mkHEqOfEq newHyp
        let newHyp ← mkHEqTrans newHyp (.mvar valGoal)
        let ⟨_, uponReplacement, _⟩ ← generalizedGoal.replace fvars[1]! newHyp
        -- We now perform a beta reduction
        let some (_, lhs, _, rhs) := (← uponReplacement.getType).heq? | throwError "Heternogenous equality expected, instead got {← uponReplacement.getType}"
        let betaReducedGoal ← mkHEq (lhs.headBeta) rhs
        let betaReduced ← uponReplacement.change betaReducedGoal
        trace[Meta.Tactic] "Continuing with goal: {betaReducedGoal}"
        cbvCore betaReduced

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
