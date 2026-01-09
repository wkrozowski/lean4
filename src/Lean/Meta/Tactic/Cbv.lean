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

mutual
  partial def handleUnfolding (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    guard e.isApp
    let f := e.getAppFn
    guard f.isConst
    let name := f.constName
    let some unfoldEq ← getConstUnfoldEqnFor? name | throwError
                  "Could not obtain unfold equation for: {name}"
    let unfoldEq := mkConst unfoldEq f.constLevels!
    let some (_,_,rhs) := (←inferType unfoldEq).eq? | throwError "fatal error : equality expected at {←inferType unfoldEq}"
    let newGoalType ← mkHEq (mkAppN rhs e.getAppArgs) (← extractRhsFromGoal goal)
    trace[Meta.Tactic] "newGoalType: {newGoalType}"


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
    trace[Meta.Tactic] "Called {← goal.getType}"
    let type ← goal.getType
    let some (_, e, _, f) := type.heq? | throwError "Expected HEq"
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
                let matcherInfo := matcherInfo.get!
                -- We do not handle overapplied matchers
                assert! e.getAppNumArgs = matcherInfo.arity
                let congrEqns ← Match.genMatchCongrEqns e.getAppFn.constName!
                let congrEqns := congrEqns.map (fun x => mkAppN (mkConst x e.getAppFn.constLevels!) e.getAppArgs)
                trace[Meta.Tactic] "congrEqns: {congrEqns}"
                let congrEqn := congrEqns[1]!
                trace[Meta.Tactic] "Processing equation: {congrEqn}"
                goal.withContext do
                  let (hyps, _, eqType) ← forallMetaTelescope (← inferType congrEqn)
                  let hyps := hyps.map (·.mvarId!)
                  for hyp in hyps do
                    let hypType ← hyp.getType
                    if hypType.isEq then
                      let res ← hyp.eqOfHEq
                      res.assumption
                  let res := mkAppN congrEqn (hyps.map (.mvar ·))
                  goal.assign res
                  let res ← instantiateMVars <| .mvar goal
                  trace[Meta.Tactic] "res: {res}"

                  throwError "stop processing"

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
                  handleUnfolding goal
                  throwError "breakpoint"
                  -- let name := e.getAppFn.constName
                  -- let levels := e.getAppFn.constLevels!
                  -- let some unfoldEq ← getConstUnfoldEqnFor? name | throwError
                  -- "cannot be unfolded"
                  -- let unfoldEq := mkConst unfoldEq levels
                  -- let unfoldEqTy ← inferType unfoldEq
                  -- trace[Meta.Tactic] "unfoldEqTy: {unfoldEqTy}"
                  -- let some (_,_,rhs) := unfoldEqTy.eq? | throwError "equality expected"
                  -- let newLhs := mkAppN rhs e.getAppArgs
                  -- let newGoalType ← mkHEq newLhs f
                  -- goal.withContext do
                  --   let newGoal ← mkFreshExprMVar newGoalType
                  --   cbvCore newGoal.mvarId!
                  --   -- We create fvar of the type of the lhs
                  --   let funType ← inferType e.getAppFn
                  --   let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default  funType fun var => do
                  --     let theoremLhs := mkAppN var e.getAppArgs
                  --     let theoremBody ← mkHEq theoremLhs f
                  --     mkLambdaFVars #[var] theoremBody
                  --   let congrArg ← mkCongrArg congrArgFun unfoldEq
                  --   let congrArg ← mkAppOptM ``Eq.mpr #[.none, .none, congrArg, newGoal]
                  --   goal.assign congrArg
                  --   trace[Meta.Tactic] "is Assigned: {← goal.isAssigned}"
                  --   return
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
