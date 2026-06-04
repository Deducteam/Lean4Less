import Lean4Less.Methods
import Lean4Less.Quot
import Lean4Less.Inductive.Add
import Lean4Less.Primitive
import Lean4Lean.Environment.Basic

namespace Lean4Less
namespace Kernel.Environment
open TypeChecker

open private Lean.Kernel.Environment.add from Lean.Environment
open Lean
open Lean.Kernel.Environment

def checkConstantVal (env : Kernel.Environment) (v : ConstantVal) (allowPrimitive := false) : M (PExpr) := do
  env.checkName v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  -- Re-label an infeasible primitive Nat op encountered while checking the *type* so lean2dk
  -- can distinguish type-infeasible constants (whose declared type is itself unusable in Dedukti)
  -- from value-infeasible ones (whose type is fine and only the body/rule need stubbing).
  let (typeType, type'?) ← try check v.type v.levelParams catch
    | .other "large nat prim op" => throw (.other "large nat prim op type")
    | e => throw e
  let type' := type'?.getD v.type.toPExpr
  let (sort, typeTypeEqSort?) ← ensureSort typeType v.levelParams type'
  let type'' ← maybeCast typeTypeEqSort? typeType sort type' v.levelParams
  let ret ← insertInitLets type''
  -- isValidApp ret v.levelParams
  pure ret

def patchAxiom (env : Kernel.Environment) (v : AxiomVal) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  let type ← (checkConstantVal env v.toConstantVal).run env v.name (opts := opts)
    (safety := if v.isUnsafe then .unsafe else .safe)
  if type.toExpr.hasFVar then
    throw $ .other "fvar in translated term"
  let v := {v with type}
  return .axiomInfo v

def patchDefinition (env : Kernel.Environment) (v : DefinitionVal) (allowAxiomReplace := false) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    let type ← (checkConstantVal env v.toConstantVal).run env v.name (safety := .unsafe) (opts := opts)
    let env' := env.add (.defnInfo {v with type})
    checkNoMVarNoFVar env' v.name v.value
    M.run env' v.name (safety := .unsafe) (lctx := {}) opts do
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      let value' := value'?.getD v.value.toPExpr
      let (true, value) ← smartCast valueType type value' v.levelParams |
        if allowAxiomReplace then
          return .axiomInfo {v with type, isUnsafe := false}
        else
          throw <| .declTypeMismatch env' (.defnDecl v) valueType
      let value ← insertInitLets value
      if type.toExpr.hasFVar || value.toExpr.hasFVar then
        throw $ .other "fvar in translated term"
      -- isValidApp value v.levelParams
      let v := {v with type, value}
      return .defnInfo v
  else
    let type ← M.run env v.name (safety := .safe) (lctx := {}) opts do
      checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)

    M.run env v.name (safety := .safe) (lctx := {}) opts do
      -- dbg_trace s!"DBG[25]: Environment.lean:49: v.name={v.name}"
      checkNoMVarNoFVar env v.name v.value
      -- dbg_trace s!"DBG[34]: Environment.lean:52 (after checkNoMVarNoFVar env v.name v.value)"
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      -- dbg_trace s!"DBG[98]: Environment.lean:54: valueType={valueType}"
      let value' := value'?.getD v.value.toPExpr
      -- dbg_trace s!"DBG[33]: Environment.lean:54 (after let value := value?.getD v.value.toPExpr)"
      -- dbg_trace s!"DBG[31]: Environment.lean:57: valueTypeEqtype?={valueTypeEqtype?}"

      let (true, value) ← smartCast valueType type value' v.levelParams |
        if allowAxiomReplace then
          return .axiomInfo {v with type, isUnsafe := false}
        else
          throw <| .declTypeMismatch env (.defnDecl v) valueType
      -- dbg_trace s!"DBG[0]: Methods.lean:202: patch={(Lean.collectFVars default type.toExpr).fvarIds.map fun v => v.name}"
      -- dbg_trace s!"DBG[1]: Methods.lean:202: patch={(Lean.collectFVars default value'.toExpr).fvarIds.map fun v => v.name}"
      -- dbg_trace s!"DBG[2]: Methods.lean:202: patch={(Lean.collectFVars default valueType.toExpr).fvarIds.map fun v => v.name}"
      -- dbg_trace s!"DBG[3]: Methods.lean:202: patch={← (Lean.collectFVars default value.toExpr).fvarIds.mapM fun v => do pure (v.name, (← get).fvarRegistry.get? v.name)}"
      -- dbg_trace s!"DBG[15]: Environment.lean:65 (after let value ← smartCast valueType type v…)"
      let value ← insertInitLets value
      -- isValidApp value v.levelParams
      let v := {v with type, value}
      if type.toExpr.hasFVar || value.toExpr.hasFVar then
        throw $ .other "fvar in translated term"
      -- dbg_trace s!"DBG[35]: Environment.lean:64 (after let v := v with type, value)"
      return (.defnInfo v)

def patchTheorem (env : Kernel.Environment) (v : TheoremVal) (allowAxiomReplace := false) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  -- TODO(Leo): we must add support for handling tasks here
  let type ← M.run env v.name (safety := .safe) (lctx := {}) (opts := opts) do
    checkConstantVal env v.toConstantVal

  let (value?) ← M.run env v.name (safety := .safe) (lctx := {}) opts do
    checkNoMVarNoFVar env v.name v.value
    let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
    let value' := value'?.getD v.value.toPExpr
    let (true, ret) ← smartCast valueType type value' v.levelParams |
      if allowAxiomReplace then
        pure none
      else
        throw <| .declTypeMismatch env (.thmDecl v) valueType
    let ret ← insertInitLets ret
    -- isValidApp ret v.levelParams
    pure (.some ret)

  if let .some value := value? then
    let v := {v with type, value}
    if type.toExpr.hasFVar || value.toExpr.hasFVar then
      throw $ .other "fvar in translated theorem type/value"
    return .thmInfo v
  else
    let v := {v with type, isUnsafe := false}
    if type.toExpr.hasFVar then
      throw $ .other "fvar in translated axiom type"
    return .axiomInfo v

def patchOpaque (env : Kernel.Environment) (v : OpaqueVal) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  let type ← M.run env v.name (safety := .safe) (lctx := {}) opts do
    checkConstantVal env v.toConstantVal
  let value ← M.run env v.name (safety := .safe) (lctx := {}) opts do
    let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
    let value' := value'?.getD v.value.toPExpr
    let (true, ret) ← smartCast valueType type value' v.levelParams |
      throw <| .declTypeMismatch env (.opaqueDecl v) valueType
    let ret ← insertInitLets ret
    pure ret
  if type.toExpr.hasFVar || value.toExpr.hasFVar then
    throw $ .other "fvar in translated term"
  let v := {v with type, value}
  return .opaqueInfo v

def patchMutual (env : Kernel.Environment) (vs : List DefinitionVal) (opts : TypeCheckerOpts) :
    Except KernelException (List ConstantInfo) := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let types ← M.run env `mutual (safety := v₀.safety) (lctx := {}) opts do
    let mut types := []
    for v in vs do
      if v.safety != v₀.safety then
        throw <| .other
          "invalid mutual definition, declarations must have the same safety annotation"
      let type ← checkConstantVal env v.toConstantVal
      types := types.append [type]
    pure types
  let mut env' := env
  let mut vs' := []
  for (type, v) in types.zip vs do
    let v' := {v with type}
    env' := env'.add (.defnInfo v')
    vs' := vs'.append [v']
  let mut newvs' := #[]
  for (v', type) in vs'.zip types do
    let newv' ← M.run env' `mutual (safety := v₀.safety) (lctx := {}) opts do
      checkNoMVarNoFVar env' v'.name v'.value
      let (valueType, value'?) ← TypeChecker.check v'.value v'.levelParams
      let value' := value'?.getD v'.value.toPExpr
      let (true, value) ← smartCast valueType type value' vs[0]!.levelParams |
        throw <| .declTypeMismatch env' (.mutualDefnDecl vs') valueType
      let value ← insertInitLets value
      if type.toExpr.hasFVar || value.toExpr.hasFVar then
        throw $ .other "fvar in translated term"
      pure {v' with value}
    newvs' := newvs'.push newv'
  return newvs'.map .defnInfo |>.toList

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Kernel.Environment) (decl : @& Declaration) (opts : TypeCheckerOpts := {}) (allowAxiomReplace := false) :
    Except KernelException Kernel.Environment := do
  match decl with
  | .axiomDecl v =>
    let v ← patchAxiom env v opts
    return env.add v
  | .defnDecl v =>
    let v ← patchDefinition env v allowAxiomReplace opts
    return env.add v
  | .thmDecl v =>
    let v ← patchTheorem env v allowAxiomReplace opts
    return env.add v
  | .opaqueDecl v =>
    let v ← patchOpaque env v opts
    return env.add v
  | .mutualDefnDecl vs =>
    let vs ← patchMutual env vs opts
    return vs.foldl (init := env) (fun env v => env.add v)
  | .quotDecl =>
    addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe opts
    addInductive env lparams nparams types isUnsafe allowPrimitive -- TODO handle any possible patching in inductive type declarations (low priority)
