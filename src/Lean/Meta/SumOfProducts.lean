module

prelude

public import Lean.Meta
public import Lean.Elab.Term
public section

open Lean.Elab.Term

namespace Lean.Meta

private def mkExistsFVars (xs : Array Expr) (e : Expr) (levelParams : List Level := []): MetaM Expr := do
let mut res := e
for x in xs do
  res ← mkLambdaFVars #[x] res
  let level := (←inferType x).sortLevel!
  res := mkAppN (mkConst ``Exists [level]) #[(←inferType x),res]
return res

private def genDisj (e1 e2 : Expr) : MetaM Expr := do
  return mkApp2 (.const `Or []) e1 e2

private def mkDisj (xs : Array Expr) : MetaM Expr :=
  if xs.size = 0 then
    return (.const `False [])
  else
    PProdN.genMk genDisj xs

def mkSumOfProducts (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.injective (fun _ => return m!"{declName}") do
    let info ← getConstInfoInduct declName
    let isPropValued ← forallTelescopeReducing info.type fun _ targetType => return targetType.isProp
    if isPropValued then
      let value ← forallTelescope info.type fun params _ => do
        let levelParams := info.levelParams.map mkLevelParam
        let ctors ← info.ctors.mapM getConstInfoCtor
        let ctors ← ctors.mapM (instantiateForall ·.type params)
        let body := mkConst `True
        let ctors ← ctors.mapM (forallTelescope · fun premises _ => mkExistsFVars premises body levelParams)
        let ctors ← mkDisj ctors.toArray
        mkLambdaFVars params ctors
      let decl := Declaration.defnDecl { name := declName ++ `sop, levelParams := info.levelParams, type := ← inferType value, value := value, hints := .opaque, safety := .safe }
      addDecl decl



builtin_initialize
  registerTraceClass `Meta.SumOfProducts

end Lean.Meta
