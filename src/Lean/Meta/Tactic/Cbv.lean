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

mutual
 partial def evalCbv (e : Expr) : MetaM EvalResult := do
  match e with
  | .lam _ _ _ _ => return {value := e, proof := (← mkEqRefl e) }
  | .app fn arg =>
      evalApp fn arg
  | .proj _ _ _ =>
    let some reduced ← reduceProj? e | throwError "Could not reduce projection"
    return {value := reduced, proof := (← mkEqRefl e) }
  | _ => return {value := e, proof := (← mkEqRefl e) }

  partial def evalApp (f arg : Expr) : MetaM EvalResult := do
    let ⟨fRes, fProof⟩ ← evalCbv f
    trace[Meta.Tactic] "Lhs: {f} -*-> {fRes}"
    let ⟨argRes, argProof⟩ ← evalCbv arg
    trace[Meta.Tactic] "Rhs: {arg} -*-> {argRes}"
    if fRes.isLambda then
      trace[Meta.Tactic] "{fRes} is a lambda expression"
      return {value := .app f arg, proof := (← mkEqRefl (.app f arg)) }
    else
      trace[Meta.Tactic] "{fRes} is a function application"
      let appFn := fRes.getAppFn.constName
      trace[Meta.Tactic] "We got: {appFn}"
      try
        let unfoldRes ← unfold (.app f arg) appFn
        trace[Meta.Tactic] "We got: {unfoldRes.expr}, {unfoldRes.proof?}"
      catch _ =>
        trace[Meta.Tactic] "Didnt succeed unfolding"



      return {value := .app f arg, proof := (← mkEqRefl (.app f arg)) }
end

def cbv (e : Expr) : MetaM EvalResult := do
  trace[Meta.Tactic] "Trying to evaluate expression {e}"

  evalCbv e


end Lean.Meta
