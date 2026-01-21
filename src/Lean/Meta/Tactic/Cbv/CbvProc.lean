module

prelude
public import Lean.Meta.Tactic.Cbv.Types
public import Lean.Elab.Term.TermElabM
public import Lean.Compiler.IR
public meta import Lean.Meta.Tactic.Cbv.Types
public section

namespace Lean.Meta.Tactic.Cbv

open Lean.Elab
open Lean.Elab.Term

def mkNormNumExt (n : Name) : ImportM CbvExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck CbvExt opts ``CbvExt n

initialize cbvExt : ScopedEnvExtension Entry (Entry × CbvExt) CbvExtState ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq CbvExt := ⟨fun _ _ ↦ false⟩
  /- Insert `v : NormNumExt` into the tree `dt` on all key sequences given in `kss`. -/
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt.1
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkNormNumExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree } ((kss, n), ext) ↦
      { tree := insert kss ext tree }
  }

syntax (name := cbv_proc) "cbv_proc " term,+ : attr

initialize registerBuiltinAttribute {
  name := `cbv_proc
  descr := "adds a norm_num extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
  | `(attr| cbv_proc $es,*) => do
    let env ← getEnv
    ensureAttrDeclIsMeta `cbv_proc declName kind
    unless (env.getModuleIdxFor? declName).isNone do
      throwError "invalid attribute 'norm_num', declaration is in an imported module"
    if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
    let ext ← mkNormNumExt declName
    let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
      let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
        withReader ({ · with ignoreTCFailures := true }) do
          let e ← elabTerm stx none
          let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
          return e
      DiscrTree.mkPath e
    cbvExt.add ((keys, declName), ext) kind
    -- TODO: track what `[cbv_proc]` decls are actually used at use sites
    recordExtraRevUseOfCurrentModule
  | _ => throwUnsupportedSyntax
  erase := fun declName => do throwError "not implemented: erasing"
}

def runCbvProcs (e : Expr) (callback : Expr → CbvM Result): CbvM <| Option Result := do
  let cbvProcs := cbvExt.getState (← getEnv)
  let arr ← cbvProcs.tree.getMatch e
  let mut res : Option Result := .none
  for ext in arr do
    let evalResult ← ext.eval e callback
    if (evalResult.isSome) then
      res := evalResult
      break
  return res

end Lean.Meta.Tactic.Cbv
