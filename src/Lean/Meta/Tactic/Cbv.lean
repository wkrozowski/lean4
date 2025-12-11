module

prelude
public import Lean.Meta.Tactic.Delta
public import Lean.Meta.Tactic.Unfold
public import Lean.Meta.Tactic.Simp.Main

public section

namespace Lean.Meta

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
 partial def evalCbv (e : Expr) (fuel : Nat) : MetaM EvalResult := do
  trace[Meta.Tactic] "Fuel is: {fuel}"
  if (fuel = 0) then
    throwError "ran out of fuel"
  let isVal ← isValue e
  if isVal then
    trace[Meta.Tactic] "Returning, as detected a value {e}"
    mkRefl e
  else
    match e with
    | .lam _ _ _ _ => mkRefl e
    | .app fn arg =>
        evalApp fn arg (fuel - 1)
    | .letE _ _ _ _ _ => evalCbv (← zetaReduce e) (fuel-1)
    | .proj _ _ _ =>
      let some reduced ← reduceProj? e | throwError "could not reduce projection"
      evalCbv (reduced) (fuel-1)

    | _ => mkRefl e

  partial def evalApp (f arg : Expr) (fuel : Nat) : MetaM EvalResult := do
    trace[Meta.Tactic] "fuel {fuel}, evaluating {f} with argument {arg}"
    let ⟨fRes, fProof⟩ ← evalCbv f (fuel - 1)
    let ⟨argRes, argProof⟩ ← evalCbv arg (fuel - 1)
    trace[Meta.Tactic] "lhs : {f} -*-> {fRes}, {arg} -*-> {argRes}"
    if fRes.isLambda then
      evalCbv (← instantiateLambda f #[arg]) (fuel - 1)
    else
      let appFn := fRes.getAppFn.constName
      let info ← getConstInfo appFn
      trace[Elab.Meta] "info for Fn: {info.isCtor}"
      match info with
      | .axiomInfo _ => throwError "not Supported axiom"
      | .thmInfo _   => throwError "not Supported thm"
      | .opaqueInfo _  => throwError "not Supported opaque"
      | .quotInfo _ => throwError "not Supported quot"
      | .inductInfo _ => throwError "not Supported induct"
      | .ctorInfo _ =>
          let ⟨bodyRes, bodyProof⟩ ← evalCbv arg (fuel - 1)

          let resProof ← mkCongrArg f bodyProof
          return {value := mkApp f bodyRes, proof := resProof}

      | .recInfo _ => throwError "not Supported rec"
      | .defnInfo info   =>
        let unfoldRes ← unfold (.app f arg) appFn
        let fallback ← mkEqRefl (.app f arg)
        let some proof := unfoldRes.proof? | throwError "Couldnt unfold"
        let resExpr := unfoldRes.expr
        if resExpr == (.app f arg) then
          throwError "Didnt unfold"
        trace[Meta.Tactic] "resExpr: {resExpr}"
        let ⟨finalRes, finalProof⟩ ← evalCbv resExpr (fuel - 1)
        let lhs ← mkCongr fProof argProof
        let final ← mkEqTrans (← mkEqTrans lhs proof) finalProof
        return {value := finalRes, proof := final}

end

def cbv (e : Expr) : MetaM EvalResult := do
  trace[Meta.Tactic] "Trying to evaluate expression {e}"

  evalCbv e 100


end Lean.Meta
