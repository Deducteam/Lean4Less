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

def getBigNums : Expr → Std.HashSet Nat
| .lam _ d b _ => (getBigNums d).union (getBigNums b)
| .forallE _ d b _ => (getBigNums d).union (getBigNums b)
| .letE _ d b v _ => (getBigNums d).union (getBigNums b) |>.union (getBigNums v)
| .mdata _ b => getBigNums b
| .app f a => (getBigNums f).union (getBigNums a)
| .proj _ _ s => (getBigNums s)
| .lit l => Id.run do
  let mut ret := default
  match l with
  | .natVal n =>
    if n > bigNumLimit then
      ret := ret.insert n
  | _ => pure ()
  return ret
| _ => default


def checkConstantVal (env : Kernel.Environment) (v : ConstantVal) (allowPrimitive := false) : M (PExpr) := do
  env.checkName v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let (typeType, type'?) ← check v.type v.levelParams
  let type' := type'?.getD v.type.toPExpr
  let (sort, typeTypeEqSort?) ← ensureSort typeType v.levelParams type'
  let type'' ← maybeCast typeTypeEqSort? typeType sort type' v.levelParams
  let ret ← insertInitLets type''
  -- isValidApp ret v.levelParams
  pure ret

def patchAxiom (env : Kernel.Environment) (v : AxiomVal) (opts : TypeCheckerOpts) :
    Except Kernel.Exception ConstantInfo := do
  let type ← (checkConstantVal env v.toConstantVal).run env v.name (opts := opts)
    (safety := if v.isUnsafe then .unsafe else .safe)
  if type.toExpr.hasFVar then
    throw $ .other "fvar in translated term"
  let v := {v with type}
  return .axiomInfo v

def patchDefinition (env : Kernel.Environment) (v : DefinitionVal) (allowAxiomReplace := false) (opts : TypeCheckerOpts) :
    Except Kernel.Exception ConstantInfo := do
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
    Except Kernel.Exception ConstantInfo := do
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
    Except Kernel.Exception ConstantInfo := do
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
    Except Kernel.Exception (List ConstantInfo) := do
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

def addBigNums (env : Kernel.Environment) (decl : @& Declaration) :
    Except Kernel.Exception Kernel.Environment := do
  let mut env := env
  let mut bignums : Std.HashSet Nat := default
  match decl with
  | .axiomDecl v =>
    -- let v ← patchAxiom env v opts
    bignums := bignums.union (getBigNums v.type)
  | .defnDecl v 
  | .thmDecl v
  | .opaqueDecl v =>
    bignums := bignums.union (getBigNums v.type)
    bignums := bignums.union (getBigNums v.value)
  | .mutualDefnDecl vs =>
    for v in vs do
      bignums := bignums.union (getBigNums v.type)
      bignums := bignums.union (getBigNums v.value)
  | .quotDecl =>
    pure ()
  | .inductDecl lparams nparams types isUnsafe =>
    pure () -- FIXME
  for num in bignums do
    let axName : Name := getBignumAxName num
    let ax : AxiomVal := {name := axName, levelParams := [], type := Expr.const ``Nat [], isUnsafe := false}
    if not (env.constants.contains axName) then
      env := env.add (.axiomInfo ax)
    -- let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe opts
    -- env ← addInductive env lparams nparams types isUnsafe allowPrimitive -- TODO handle any possible patching in inductive type declarations (low priority)
  pure env

def addDeclOrGenerateAx (m : Except Kernel.Exception ConstantInfo) (opts : TypeCheckerOpts) (type : Expr) (name : Name) (levelParams : List Name) : Except Kernel.Exception ConstantInfo := do
  let v ←
    try
      m
    catch e => 
      if opts.bignum then
        if let .other m := e then
          if m == bigNumAbortMsg then
            dbg_trace s!"axiomatized: {name}"
            pure (.axiomInfo {type, isUnsafe := false, name, levelParams})
          else
            throw e
        else
          throw e
      else
        throw e


/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Kernel.Environment) (decl : @& Declaration) (opts : TypeCheckerOpts := {}) (allowAxiomReplace := false) :
    Except Kernel.Exception Kernel.Environment := do
  -- let env := env.toStage₁
  let mut env := env
  if opts.bignum then
    env ← addBigNums env decl
  match decl with
  | .axiomDecl v =>
      let v ← addDeclOrGenerateAx (patchAxiom env v opts) opts v.type v.name v.levelParams
      return env.add v
  | .defnDecl v =>
    let v ← addDeclOrGenerateAx (patchDefinition env v false opts) opts v.type v.name v.levelParams
    return env.add v
  | .thmDecl v =>
    -- if v.name == ``Array.eraseIdx._unary.induct then
    --   dbg_trace s!"DBG[62]: Environment.lean:185 (after sorry)"
    let v ← addDeclOrGenerateAx (patchTheorem env v false opts) opts v.type v.name v.levelParams
    return env.add v
  | .opaqueDecl v =>
    let v ← addDeclOrGenerateAx (patchOpaque env v opts) opts v.type v.name v.levelParams
    return env.add v
  | .mutualDefnDecl vs =>
    -- FIXME FIXME generate axioms?
    let vs ← patchMutual env vs opts
    return vs.foldl (init := env) (fun env v => env.add v)
  | .quotDecl =>
    addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    -- FIXME FIXME generate axioms?
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe opts
    addInductive env lparams nparams types isUnsafe allowPrimitive -- TODO handle any possible patching in inductive type declarations (low priority)
