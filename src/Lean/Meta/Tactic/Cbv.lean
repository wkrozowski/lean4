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

/--
  Quotient reduction rules:
  Quot.lift (4 args) and Quot.ind (4 args) reduce if the 4th arg is Quot.mk
  -/
def isQuotRedex (info : QuotVal) (args : Array Expr) : MetaM Bool := do
  match info.kind with
  | .lift | .ind =>
    if args.size < 4 then return false
    let majorArg := args[3]!
    return majorArg.getAppFn.isConstOf ``Quot.mk
  | .ctor | .type => return false

partial def isValue (e : Expr) : MetaM Bool := do
  trace[Meta.Tactic] "checking if {e} is a value"
  -- 1. Propositions are types of "irrelevant" data, usually treated as values

  if ((← inferType e).isProp) then
    return true

  if (← isProof e) then
    return true

  -- 2. Handle Nat literals represented via OfNat.ofNat
  if Simp.isOfNatNatLit e then
    trace[Meta.Tactic] "It is nat literal"
    return true

  match e with
  | .lit _   => return true
  | .sort _  => return true
  | .lam ..  => return true -- Lambdas are values in CBV
  | .mdata _ e => isValue e

  -- 3. Handle Constants (No arguments)
  | .const name _ => isConstantValue name

  -- 4. Handle Applications
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    trace[Meta.Tactic] "Checking what kind of application {e} is"
    match fn with
    | .const name _ =>
      let info ← getConstInfo name
      match info with
      | .ctorInfo _ | .inductInfo _ | .axiomInfo _ =>
        -- Constructors, inductive types, and axioms applied to values are values
        args.allM isValue
       | .quotInfo quotVal =>
        if (← isQuotRedex quotVal args) then
          return false
        else
          args.allM isValue
      | .thmInfo _ => return true
      | .defnInfo _ | .opaqueInfo _ | .recInfo _ =>
        -- Definitions/Recursors are reducible; even if arguments are values, the call is not
        return false
    | _ => return false

  -- Explicitly not values
  | .letE .. | .proj .. | .forallE .. | .bvar .. | .fvar .. => return false
  | .mvar _ => throwError "Unassigned metavariable encountered: {e}"

where
  /-- Helper to determine if a standalone constant is a value based on its declaration type -/
  isConstantValue (name : Name) : MetaM Bool := do
    let info ← getConstInfo name
    return match info with
    | .ctorInfo _ | .axiomInfo _ | .thmInfo _ | .inductInfo _ | .quotInfo _ => true
    | .defnInfo _ | .opaqueInfo _ | .recInfo _ => false

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
  trace[Meta.Tactic] "Called tryValue"
  let e ← extractLhsFromGoal goal
  trace[Meta.Tactic] "lhs is: {e}"
  if (← isValue e) then
    trace[Meta.Tactic] "Stopping with value: {e}"
    goal.hrefl
  else
    throwError "The left hand side {e} of the goal {← goal.getType} is not a value."

def tryFilterMapM(f : α → MetaM β) (arr : Array α) : MetaM (Array β) :=
  arr.filterMapM fun x => do
    try
      let result ← f x
      return some result
    catch _ =>
      return none

def tryClosingGoal (candidates : Array Expr) (goal : MVarId) : MetaM Unit := do
  let mut candidates := candidates
  let oldCandidatesLen := candidates.size
  if (← goal.getType).isEq then
    candidates ← tryFilterMapM mkEqOfHEq candidates
    trace[Meta.Tactic] "Triggered: old: {oldCandidatesLen}, {candidates.size}, goal: {goal}, candidates: {candidates}"
  try
    for candidate in candidates do
      let isDefEq ← isDefEq (← inferType candidate) (← goal.getType)
      trace[Meta.Tactic] "isDefEq: {isDefEq}"

    candidates.firstM (do let [] ← goal.apply · | throwError "Produces subgoals")
  catch e =>
    trace[Meta.Tactic] "inner exception: {e.toMessageData}"
    throwError "rethrow"

mutual
  partial def tryMatchCongrEqns (congrEqn : Expr) (solvedDiscriminants : Array Expr) : MetaM Expr := do
    let (hyps, _) ← forallMetaTelescope (← inferType congrEqn)
    let hyps := hyps.map (·.mvarId!)
    for hyp in hyps do
      hyp.withContext do
        let hypTy ← hyp.getType
        if (hypTy.isEq) then
          let heqGoal ← hyp.eqOfHEq
          tryClosingGoal solvedDiscriminants heqGoal <|> do
            trace[Meta.Tactic] "I failed in closing goal heq: {heqGoal}"
            throwError "applying didnt work"
        if (hypTy.isHEq) then
          tryClosingGoal solvedDiscriminants hyp <|> do
            trace[Meta.Tactic] "I failed in closing goal eq: {hyp}"
            throwError "applying didnt work"

    unless (← hyps.allM (·.isAssigned)) do
      trace[Meta.Tactic] "found goals: {hyps}"
      throwError "Not all goals are assigned"

    let hyps := hyps.map Expr.mvar
    let hyps ← hyps.mapM instantiateMVars
    let res := mkAppN congrEqn hyps
    if res.hasMVar then
      trace[Meta.Tactic] "found unnasigned vars: {res}"
      throwError "result has unassigned mvars"
    return mkAppN congrEqn hyps

partial def tryMatcher (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
  let e ← extractLhsFromGoal goal
  let f := e.getAppFn
  let args := e.getAppArgs
  let ctorName := f.constName
  let some matcherInfo ← getMatcherInfo? e.getAppFn.constName! | throwError "Not a matcher, skipping"

  assert! matcherInfo.arity = e.getAppNumArgs

  let congrEqns ← Match.genMatchCongrEqns ctorName
  let congrEqns := congrEqns.map (mkConst · f.constLevels!)
  let congrEqns := congrEqns.map (mkAppN · args)
  trace[Meta.Tactic] "congrEqns: {congrEqns}"

  let ⟨discrLower, discrUpper⟩ := matcherInfo.getDiscrRange
  let discriminants := args.extract discrLower discrUpper

  goal.withContext do
    -- Evaluate discriminants
    let discriminantsGoals ← discriminants.mapM (makeGoalFrom ·)
    discard <| discriminantsGoals.mapM (cbvCore context ·)
    let solvedDiscriminants ← discriminantsGoals.mapM (instantiateMVars <| .mvar ·)

    -- Try to find a matching congruence equation
    try
      let solution ← congrEqns.firstM (tryMatchCongrEqns · solvedDiscriminants)
      let some (_, _, _, solutionValue) := (← inferType solution).heq? | throwError "Heterogenous equality expected"

      -- Continue evaluation on the matched branch
      let originalRhs ← extractRhsFromGoal goal
      let newGoalType ← mkHEq solutionValue originalRhs
      let continuedGoal ← mkFreshExprMVar newGoalType
      cbvCore context continuedGoal.mvarId!
      let continuedProof ← instantiateMVars continuedGoal

      -- Combine proofs
      let toAssign ← mkHEqTrans solution continuedProof
      goal.assign toAssign
    catch e =>
      throwError "caught: {e.toMessageData}"

  partial def handleCtor (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    let f := e.getAppFn
    let ctorName := f.constName
    trace[Meta.Tactic] "ctor {f} is: {ctorName} in expression {e} with args: {e.getAppArgs}"
    let args := e.getAppArgs
    let some congrThm ← mkHCongrWithArityForConst? ctorName f.constLevels! e.getAppNumArgs | throwError "Could not genereate congruence theorem for constructor {ctorName}"
    goal.withContext do
      let mut congrThmProof := congrThm.proof
      for (arg, argKind) in args.zip congrThm.argKinds do
        trace[Meta.Tactic] "ctor: arg: {arg}, arg.isFVar: {arg.isFVar}"
        let proof ← makeGoalFrom arg
        cbvCore context proof
        let evalResult ← instantiateMVars (.mvar proof)
        let evalResultType ← inferType evalResult
        let some (_, _, _, value) := evalResultType.heq? | throwError "Expected heterogenous equality"
        trace[Meta.Tactic] "evalResult: {evalResult}, value: {value}"
        congrThmProof := mkAppN congrThmProof #[arg, value]
        if argKind == .eq then
          congrThmProof := mkApp congrThmProof (← mkEqOfHEq (evalResult))
        else
          congrThmProof := mkApp congrThmProof evalResult
      goal.assign congrThmProof
      trace[Meta.Tactic] "ctor goal assigned"

partial def handleUnfolding (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
  let e ← extractLhsFromGoal goal
  let goalRhs ← extractRhsFromGoal goal
  assert! e.isApp
  let f := e.getAppFn
  assert! f.isConst
  let name := f.constName
  let some unfoldEqName ← getConstUnfoldEqnFor? name | throwError
                "Could not obtain unfold equation for: {name}"
  let unfoldEq := mkConst unfoldEqName f.constLevels!
  let some (_,_,rhs) := (←inferType unfoldEq).eq?
    | throwError "fatal error : equality expected at {←inferType unfoldEq}"
  let unfoldedExpr := mkAppN rhs e.getAppArgs

  let newGoalType ← mkHEq unfoldedExpr goalRhs
  goal.withContext do
    let unfoldedGoal ← mkFreshExprMVar newGoalType
    cbvCore context unfoldedGoal.mvarId!
    let unfoldedGoal ← instantiateMVars unfoldedGoal
    let some (_, _, _, unfoldedGoalValue) := (← inferType unfoldedGoal).heq? | throwError "Heterogenous equality expected"

    -- Build the congruence proof
    let fType ← inferType f
    let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default fType fun var => do
      let theoremLhs := mkAppN var e.getAppArgs
      let theoremBody ← mkHEq theoremLhs unfoldedGoalValue
      mkLambdaFVars #[var] theoremBody

    -- mkCongrArg gives us: (fun x => x args ≍ goalRhs) f = (fun x => x args ≍ goalRhs) rhs
    -- which beta-reduces to: (f args ≍ goalRhs) = (rhs args ≍ goalRhs)
    let congrArg ← mkCongrArg congrArgFun unfoldEq
    let finalProof ← mkAppOptM ``Eq.mpr #[none, none, congrArg, unfoldedGoal]
    goal.assign finalProof

  partial def handleLambda (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    trace[Meta.Tactic] "Evaluating lambda expression: {e} with arguments {e.getAppArgs} and type {← inferType e}"
    let rhs ← extractRhsFromGoal goal
    trace[Meta.Tactic] "Outer goal RHS: {rhs}, isMVar: {rhs.isMVar}"
    assert! e.isApp
    let lambdaFn := e.getAppFn
    let args := e.getAppArgs
    assert! lambdaFn.isLambda
    trace[Meta.Tactic] "Lambda arguments: {args}"
    let headArg := args[0]!
    let remainingArgs := args.extract 1
    goal.withContext do
      let valGoal ← makeGoalFrom headArg
      cbvCore context valGoal
      let valProof ← instantiateMVars <| .mvar valGoal
      let some (_, _, _, value) := (← inferType valProof).heq? | throwError "Heterogenous equality expected"
      assert! !value.hasMVar
      trace[Meta.Tactic] "valProof: {valProof}, value: {value}"

      let argType ← inferType headArg
      let newMVarType : Expr ← withLocalDeclD (← mkFreshUserName `x) argType fun argVar => do
        let eqType ← mkHEq argVar value
        withLocalDeclD (←mkFreshUserName `h) eqType fun eqType => do
          let newBody := (Expr.app lambdaFn argVar).headBeta
          let newBody := mkAppN newBody remainingArgs
          let body ← mkHEq newBody rhs
          trace[Meta.Tactic] "Created forall type with body: {body}"
          mkForallFVars #[argVar, eqType] body
      let newMVar ← mkFreshExprMVar newMVarType
      let toFill := mkAppN newMVar #[headArg, (← instantiateMVars <| .mvar valGoal)]
      goal.assign toFill
      let (#[value, fvar], generalizedGoal) ← newMVar.mvarId!.introN 2  | throwError "unexpected number of free variables"
      generalizedGoal.withContext do
        trace[Meta.Tactic] "Adding to context: {Expr.fvar value} : {Expr.fvar fvar} "
        cbvCore (context.insert value fvar) generalizedGoal
        trace[Meta.Tactic] "After solving generalizedGoal, checking if assigned: {← generalizedGoal.isAssigned}"
        let generalizedGoalProof ← instantiateMVars (.mvar generalizedGoal)
        trace[Meta.Tactic] "Generalized goal proof: {generalizedGoalProof}"

  partial def handleApplication (e : Expr) (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
    trace[Meta.Tactic] "{e} is an application with arguments {e.getAppArgs}"
          if e.getAppFn.isLambda then
            handleLambda context goal
          else
            trace[Meta.Tactic] "is Assigned: {← goal.isAssigned}"
            if (e.getAppFn.isConst) then
              let info ← getConstInfo e.getAppFn.constName
              let matcherInfo ← getMatcherInfo? e.getAppFn.constName!
              if matcherInfo.isSome then
                tryMatcher context goal
              else
                match info with
                | .defnInfo _ => handleUnfolding context goal
                | .ctorInfo _ => handleCtor context goal
                | .recInfo recInfo =>
                  let some congrThm ← mkHCongrWithArityForConst? recInfo.name (e.getAppFn.constLevels!) (← getFunInfo (e.getAppFn)).getArity | throwError "Could not get congruence theorems for recursor"
                   goal.withContext do
                    let mut congrThmProof := congrThm.proof
                    for (arg, argKind) in (e.getAppArgs).zip congrThm.argKinds do
                      trace[Meta.Tactic] "recursor: arg: {arg}, arg.isFVar: {arg.isFVar}"
                      let proof ← makeGoalFrom arg
                      cbvCore context proof
                      let evalResult ← instantiateMVars (.mvar proof)
                      let evalResultType ← inferType evalResult
                      let some (_, _, _, value) := evalResultType.heq? | throwError "Expected heterogenous equality"
                      trace[Meta.Tactic] "evalResult: {evalResult}, value: {value}"
                      congrThmProof := mkAppN congrThmProof #[arg, value]
                      if argKind == .eq then
                        congrThmProof := mkApp congrThmProof (← mkEqOfHEq (evalResult))
                      else
                        congrThmProof := mkApp congrThmProof evalResult

                    let some (_, _, _, congrThmValue) := (← inferType congrThmProof).heq? | throwError "heq expected"
                    let some reduced ← reduceRecMatcher? congrThmValue | throwError "Could not reduce recursor"
                    let continuedGoal ← makeGoalFrom reduced
                    cbvCore context continuedGoal
                    let continuedProof ← instantiateMVars <| .mvar continuedGoal
                    let finalResult ← mkHEqTrans congrThmProof continuedProof
                    goal.assign finalResult
                | .inductInfo _ => handleCtor context goal
                | .quotInfo _ => throwError "quotients are not implemented"
                | .axiomInfo _ => throwError "cannot reduce axioms"
                | .opaqueInfo _ => throwError "Cannot reduce opaque"
                | .thmInfo _ => throwError "Cannot reduce theorems"
            else
              goal.withContext do
                -- We evaluate the left hand side to a value
                let funArg ← makeGoalFrom e.getAppFn
                cbvCore context funArg
                let funArgProof ← instantiateMVars <| .mvar <| funArg
                let funArgProof ← mkEqOfHEq funArgProof
                let some (_, _, funArgValue) := (← inferType funArgProof).eq? | throwError "equality expected"

                -- We create a new goal
                let continuedGoal ← makeGoalFrom (mkAppN funArgValue e.getAppArgs)
                cbvCore context continuedGoal
                let continuedProof ← instantiateMVars <| .mvar continuedGoal
                let some (_, _, _, continuedValue) := (← inferType continuedProof).heq? | throwError "Heterogenous equality expected"

                let fType ← inferType e.getAppFn
                let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default fType fun var => do
                  let theoremLhs := mkAppN var e.getAppArgs
                  let theoremBody ← mkHEq theoremLhs continuedValue
                  mkLambdaFVars #[var] theoremBody

                -- mkCongrArg gives us: (fun x => x args ≍ goalRhs) f = (fun x => x args ≍ goalRhs) rhs
                -- which beta-reduces to: (f args ≍ goalRhs) = (rhs args ≍ goalRhs)
                let congrArg ← mkCongrArg congrArgFun funArgProof
                let finalProof ← mkAppOptM ``Eq.mpr #[none, none, congrArg, continuedProof]
                goal.assign finalProof

  partial def handleProjection (typeName : Name) (idx : Nat) (e : Expr) (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
    trace[Meta.Tactic] "Handling projection expression of the type {typeName}, index {idx} and inner expression {e}"
    goal.withContext do
      let innerGoal ← makeGoalFrom e
      trace[Meta.Tactic] "trying to evaluate: {innerGoal} in projection evaluation"
      cbvCore context innerGoal
      let innerGoalProof ← instantiateMVars <| .mvar <| innerGoal
      trace[Meta.Tactic] "Inner goal proof: {innerGoalProof}"
      let some (_, _, _, innerGoalValue) := (← inferType innerGoalProof).heq? | throwError "Expected heterogenous equality at {e}"

      -- We solve the projection
      let newGoalLhs := Expr.proj typeName idx innerGoalValue
      trace[Meta.Tactic] "newGoalLhs: {newGoalLhs}"
      let some newGoalLhs ← reduceProj? newGoalLhs | throwError "Could not reduce projection {newGoalLhs}"

      -- We continue evaluation
      let continuedGoal ← makeGoalFrom newGoalLhs
      cbvCore context continuedGoal
      let continuedProof ← instantiateMVars <| .mvar continuedGoal
      let some (_, _, _, continuedValue) := (← inferType continuedProof).heq? | throwError "Expected heq"
      assert! !continuedValue.hasMVar
      -- We force innerGoalProof to be an equality, so we can use it in congrArg
      let innerGoalProof ← mkEqOfHEq innerGoalProof

      -- we build the congruence proof
      let eType ← inferType e
      let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default eType fun var => do
        let theoremLhs := Expr.proj typeName idx var
        let theoremBody ← mkHEq theoremLhs continuedValue
        mkLambdaFVars #[var] theoremBody

      let congrArg ← mkCongrArg congrArgFun innerGoalProof

      let finalProof ← mkAppOptM ``Eq.mpr #[none, none, congrArg, continuedProof]
      goal.assign finalProof


  partial def cbvCore (context : FVarIdMap FVarId) (goal : MVarId) : MetaM Unit := do
    let e ← extractLhsFromGoal goal
    trace[Meta.Tactic] "The expression is: {e}"
    tryValue goal <|> do
      match e with
      | .fvar id =>
        let result := context.get? id
        if result.isSome then
          let proof := Expr.fvar result.get!
          let proof ← instantiateMVars proof
          let [] ← goal.apply proof | throwError "Could not unify"
        else
          goal.hrefl
      | .proj typeName idx val =>
        handleProjection typeName idx val context goal
      | .mvar _ => throwError "Cannot evaluate metavariables"
      | .bvar _ => throwError "Cannot evaluate bound variable"
      | .mdata .. => throwError "not implemented yet"
      | .letE .. => throwError "not implemented yet"
      | .lit _ | .lam .. | .sort .. | .forallE .. => goal.hrefl
      | .app .. => handleApplication e context goal
      | .const name levels =>
          let unfoldEq ← getConstUnfoldEqnFor? name
          if unfoldEq.isSome then
            let unfoldEq := unfoldEq.get!
            let unfoldEq := mkConst unfoldEq levels
            let newGoal ← goal.heqOfEq
            let [] ← newGoal.apply unfoldEq | throwError "Failed when applying the unrolling theorem"
          else
            goal.hrefl


end

def cbv (e : Expr) : MetaM EvalResult := do

  trace[Meta.Tactic] "Trying to evaluate expression {e}"
  let goal ← makeGoalFrom e
  let startTime ← IO.monoNanosNow
  cbvCore {} goal
  let proof ← instantiateMVars <| .mvar goal
  let proof ← mkEqOfHEq proof
  let endTime ← IO.monoNanosNow
  let some (_, _, value) := (← inferType proof).eq? | throwError "eq expected"
  trace[Meta.Tactic] "value: {value}, proof: {proof}"
  let timeMs := (endTime - startTime).toFloat / 1000000.0
  trace[Meta.Tactic] "proof size: {← proof.numObjs}, time elapsed: {timeMs}"
  return ⟨value, proof⟩
end Lean.Meta
