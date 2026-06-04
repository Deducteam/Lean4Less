import Lean4Less.Quot import Lean4Less.Inductive.Reduce
import Lean4Less.EExpr

import Lean4Lean.Environment
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Util
import Lean4Lean.Instantiate
import Lean4Lean.TypeChecker

import Lean4Less.App

-- 98
-- mkId 13

namespace Lean4Less
open Lean

abbrev InferCache := Std.HashMap Expr (PExpr × Option PExpr)
abbrev InferCacheP := Std.HashMap Expr (PExpr)

structure TypeChecker.State where
  nid : Nat := 0
  fvarTypeToReusedNamePrefix : Std.HashMap Expr Name := {}
  inferTypeI : InferCacheP := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : Std.HashMap PExpr (PExpr × Option (EExpr × LocalDeclE × Option FVarId)) := {}
  -- whnfCache : Std.HashMap (PExpr × Bool) (PExpr × Option (EExpr × LocalDeclE × Option FVarId)) := {}
  whnfCache : Std.HashMap (PExpr × Bool) (PExpr × Option (EExpr × LocalDeclE × Option FVarId)) := {}
  isDefEqCache : Std.HashMap (PExpr × PExpr) (EExpr × LocalDeclE × Option FVarId) := Std.HashMap.empty
  isDefEqAppCache : Std.HashMap (Array PExpr × Array PExpr) (Option (EExpr × LocalDeclE × Option FVarId × Array (Option (PExpr × PExpr × EExpr)))) := {}
  exprCache : Std.HashMap PExpr (LocalDeclE × Option FVarId) := Std.HashMap.empty
  fvarRegistry : Std.HashMap Name Nat := {} -- for debugging purposes
  initLets : Array LocalDeclE := {}
  fvarsToLets : Std.HashMap FVarId (Array LocalDeclE) := {}
  letsToBindVar : Std.HashMap FVarId FVarId := {}
  eqvManager : EquivManager := {}
  lctx : LocalContext := {}
  numCalls : Nat := 0
  leanMinusState : Lean.TypeChecker.State := {}
  failure : Std.HashSet (Expr × Expr) := {}

instance : ToString CallData where
toString
| .isDefEqCore t s     => s!"isDefEqCore ({t}) ({s})"
| .isDefEqCorePure t s => s!"isDefEqCorePure ({t}) ({s})"
| .quickIsDefEq t s h  => s!"quickIsDefEq ({t}) ({s}) {h}"
| .whnfCore e k p      => s!"whnfCore ({e}) {k} {p}"
| .whnf e k            => s!"whnf ({e}) {k}"
| .whnfPure e          => s!"whnfPure ({e})"
| .inferType e d       => s!"inferType ({e}) ({d})"
| .inferTypePure e     => s!"inferTypePure ({e})"
| _  => s!"TODO"

def CallData.name : CallData → String
| .isDefEqCore ..     => "isDefEqCore"
| .isDefEqApp ..      => "isDefEqApp"
| .isDefEqCorePure .. => "isDefEqCorePure"
| .quickIsDefEq ..    => "quickIsDefEq"
| .whnfCore ..        => "whnfCore"
| .whnf ..            => "whnf"
| .whnfPure ..        => "whnfPure"
| .inferType ..       => "inferType"
| .inferTypePure ..   => "inferTypePure"

@[reducible]
def CallDataT : CallData → Type
| .isDefEqCore ..     => Bool × Option EExpr
| .isDefEqApp ..      => Bool × Option EExpr
| .isDefEqCorePure .. => Bool
| .quickIsDefEq ..    => LBool × Option EExpr
| .whnfCore ..        => PExpr × Option EExpr
| .whnf ..            => PExpr × Option EExpr
| .whnfPure ..        => PExpr
| .inferType ..       => PExpr × Option PExpr
| .inferTypePure ..   => PExpr

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except KernelException
abbrev MPE := M (PExpr × Option PExpr)
abbrev MEE := M (PExpr × Option EExpr)
abbrev MB := M (Bool × Option EExpr)
abbrev MLB := M (LBool × Option EExpr)

def M.run (env : Kernel.Environment) (const : Name) (safety : DefinitionSafety := .safe) (lctx : LocalContext := {}) (opts : TypeCheckerOpts := {})
    (x : M α) : Except KernelException α :=
  x { env, safety, const, opts } |>.run' {lctx}

def getKEnv : M Kernel.Environment := do return (← read).env

instance : MonadLCtx M where
  getLCtx := return (← get).lctx
--
-- instance (priority := low) : MonadWithReaderOf LocalContext M where
--   withReader f := fun x => do
--     let sOrig ← get
--     modify fun s => { s with lctx := f s.lctx }
--     let ret ← x
--     modify fun s => { s with lctx := sOrig.lctx }
--     pure ret

instance (priority := low) : MonadWithReaderOf (Std.HashMap (FVarId × FVarId) FVarDataE) M where
  withReader f := withReader fun s => { s with eqFVars := f s.eqFVars }

structure Methods where
  isDefEqCore : Nat → PExpr → PExpr → MB
  isDefEqCorePure : Nat → PExpr → PExpr → M Bool
  quickIsDefEq : Nat → PExpr → PExpr → Bool → MLB
  whnfCore (n : Nat) (e : PExpr) (cheapK := false) (cheapProj := false) : MEE
  whnf (n : Nat) (e : PExpr) (cheapK : Bool) : MEE
  whnfPure (n : Nat) (e : PExpr) : M PExpr
  inferType (n : Nat) (e : Expr) (dbg : Bool) : MPE
  inferTypePure (n : Nat) (e : PExpr) : M PExpr
  isDefEqApp (n : Nat) (t s : PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr)) (tfEqsf? : Option (Option EExpr)) : M (Bool × Option EExpr)

abbrev RecM := ReaderT Methods M
abbrev RecPE := RecM (PExpr × (Option PExpr))
abbrev RecEE := RecM (PExpr × (Option EExpr))
abbrev RecB := RecM (Bool × (Option EExpr))
abbrev RecLB := RecM (LBool × (Option EExpr))

def shouldTrace : M Bool := do
  pure $ (← readThe Context).callStack.any (·.2.1 == (← readThe Context).dbgCallId)

def shouldTTrace : M Bool := do
  pure $ (← readThe Context).callId == (← readThe Context).dbgCallId

def traceM (msg : String) : M Unit := do
  if ← shouldTrace then
    dbg_trace msg

def trace (msg : String) : RecM Unit := do
  if ← shouldTrace then
    dbg_trace msg

def ttrace (msg : String) : RecM Unit := do
  if ← shouldTTrace then
    dbg_trace msg

def dotrace (msg : Unit → RecM String) : RecM Unit := do
  if ← shouldTrace then
    trace (← msg ())

def dottrace (msg : Unit → RecM String) : RecM Unit := do -- TODO macro to make this easier to use
  if ← shouldTTrace then
    dbg_trace (← msg ())

def callId : RecM Nat := do
  pure (← readThe Context).callId

def numCalls : RecM Nat := do
  pure (← get).numCalls

def mkIdNew (n : Nat) : RecM Name := do
  let nid := (← get).nid
  let fid := .mkNum `_kernel_fresh nid
  -- for id in (← readThe Context).dbgFIds do
  --   if id == fid then
  --     dbg_trace s!"DBG[1]: TypeChecker.lean:191 {fid}, {n}"
  modify fun st => { st with nid := st.nid + 1, fvarRegistry := st.fvarRegistry.insert fid n}
  pure fid

def mkId' (n : Nat) (lctx : LocalContext) (dom : Expr) : RecM Name := do
  let id ← if let some np := (← get).fvarTypeToReusedNamePrefix[dom]? then
    let mut count := 0
    while lctx.findFVar? (Expr.fvar $ .mk (Name.mkNum np count)) |>.isSome do
      count := count + 1
    pure $ Name.mkNum np count
  else
    let np ← mkIdNew n
    modify fun st => { st with fvarTypeToReusedNamePrefix := st.fvarTypeToReusedNamePrefix.insert dom np }
    pure $ Name.mkNum np 0
  modify fun st => { st with fvarRegistry := st.fvarRegistry.insert id n }
  pure id
  -- mkIdNew n -- FIXME FIXME need to handle let variables

def mkId (n : Nat) (dom : Expr) : RecM Name := do
  mkId' n (← getLCtx) dom

def _root_.Lean.LocalContext.mkLocalDecl' (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := 0
    let decl := LocalDecl.cdecl idx fvarId userName type bi kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

@[inline] def withUnderBinder [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with underBinder := true}) x

-- @[inline] def withLCtx' (lctx : LocalContext) (x : M α) : M α := do
--   let sOrig ← get
--   modify fun s => { s with lctx := f s.lctx }
--   withReader (fun _ => lctx) x
--
def withNewFVar' (id : FVarId) (m : LocalDecl → RecM α) : RecM α := do
  let some var := (← getLCtx).find? id | throw $ .other "unreachable!"
  let ret ← m var

  let afterLctx := (← getLCtx)
  let afterDecls := afterLctx.decls.toArray
  let afterMap := afterLctx.fvarIdToDecl
  -- delete this decl and all the lets after it without changing any prior part of the context
  -- (which may contain other injected let expressions)
  let varInd := (afterLctx.decls.toArray.findIdx? fun d? => if let some d := d? then d.fvarId == id else false).get!
  let mut resetMap := afterMap
  let resetDecls := afterDecls[:varInd].toArray.toPArray'
  for d? in afterDecls[varInd:] do
    if let some d := d? then
      resetMap := resetMap.erase d.fvarId
  let resetLctx := {decls := resetDecls, fvarIdToDecl := resetMap}
  modify fun s => { s with lctx := resetLctx}
  pure ret

def withNewFVar (n : Nat) (name : Name) (dom : PExpr) (bi : BinderInfo) (m : LocalDecl → RecM α) (id? : Option FVarId := none) : RecM α := do
  let id := id?.getD ⟨← mkIdNew n⟩
  let newLctx := ((← getLCtx).mkLocalDecl' id name dom bi)
  modify fun s => { s with lctx := newLctx }

  withUnderBinder $ withNewFVar' id m

def withNewLetVar (n : Nat) (name : Name) (type : Expr) (val : Expr) (m : LocalDecl → RecM α) : RecM α := do
  let id := ⟨← mkIdNew n⟩
  let newLctx := ((← getLCtx).mkLetDecl id name type val)
  modify fun s => { s with lctx := newLctx }

  withNewFVar' id m

def withNewLetVars (n : Nat) (vars : Array (Name × Expr × Expr)) (m : Array LocalDecl → RecM α) : RecM α := do
  let rec loop' (remVars : List (Name × Expr × Expr)) (vars : Array LocalDecl) (f : Array LocalDecl → RecM α) : RecM α := match remVars with
    | (name, type, val) :: remVars => withNewLetVar n name type val fun var => loop' remVars (vars.push var) f
    | [] => f vars
  loop' vars.toList #[] m

def runLeanMinus (M : Lean.TypeChecker.M T) : RecM T := do
  let trace := (← readThe Context).L4LTraceOverride || ((← readThe Context).L4LTrace && (← shouldTrace))
  let opts := (← readThe Context).opts
  let (ret, newState) ← Lean.TypeChecker.M.run (← getKEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := not opts.kLikeReduction, proofIrrelevance := not opts.proofIrrelevance}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams)
    (nid := (← get).nid) (fvarTypeToReusedNamePrefix := (← get).fvarTypeToReusedNamePrefix) (state := (← get).leanMinusState) (trace := trace) M
  modify fun s => {s with leanMinusState := newState, nid := newState.nid, fvarTypeToReusedNamePrefix := newState.fvarTypeToReusedNamePrefix}
  pure ret

def runLeanMinusRecM (M : Lean.TypeChecker.RecM T) : RecM T := do
  let trace := (← readThe Context).L4LTraceOverride || ((← readThe Context).L4LTrace && (← shouldTrace))
  let opts := (← readThe Context).opts
  let (ret, newState) ← Lean.TypeChecker.M.run (← getKEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := not opts.kLikeReduction, proofIrrelevance := not opts.proofIrrelevance}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams)
    (nid := (← get).nid) (fvarTypeToReusedNamePrefix := (← get).fvarTypeToReusedNamePrefix) (state := (← get).leanMinusState) (trace := trace)
    M.run
  modify fun s => {s with leanMinusState := newState, nid := newState.nid, fvarTypeToReusedNamePrefix := newState.fvarTypeToReusedNamePrefix}
  pure ret

def runLeanRecM' (M : Lean.TypeChecker.RecM T) : RecM (T × Lean.TypeChecker.State) := do
  let trace := (← readThe Context).L4LTraceOverride || ((← readThe Context).L4LTrace && (← shouldTrace))
  let eqFVars := (← readThe Context).eqFVars.keys.foldl (init := default) fun acc t => acc.insert t
  let (ret, s) ← Lean.TypeChecker.M.run (← getKEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := true, proofIrrelevance := true}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (nid := (← get).nid) (trace := trace) (fvarTypeToReusedNamePrefix := (← get).fvarTypeToReusedNamePrefix) (eqFVars := eqFVars)
    M.run
  pure (ret, s)

def runLeanRecM (M : Lean.TypeChecker.RecM T) : RecM T := do
  let trace := (← readThe Context).L4LTraceOverride || ((← readThe Context).L4LTrace && (← shouldTrace))
  let eqFVars := (← readThe Context).eqFVars.keys.foldl (init := default) fun acc t => acc.insert t
  let (ret, _) ← Lean.TypeChecker.M.run (← getKEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := true, proofIrrelevance := true}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (nid := (← get).nid) (trace := trace) (fvarTypeToReusedNamePrefix := (← get).fvarTypeToReusedNamePrefix) (eqFVars := eqFVars)
    M.run
  pure ret

-- def runLean (M : Lean.TypeChecker.M T) : RecM T := do
--   Lean.TypeChecker.M.run' (← getKEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := true, proofIrrelevance := true}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (nid := (← get).nid) M

inductive ReductionStatus where
  | continue (nltn nlsn : PExpr) (pltnEqnltn? plsnEqnlsn? : Option EExpr)
  | unknown (ltn lsn : PExpr) (tnEqltn? snEqlsn? : Option EExpr)
  | notDelta
  | bool (b : Bool) (p?: Option EExpr)
deriving Inhabited

namespace Inner

/--
Reduces `e` to its weak-head normal form.
-/
def whnf (n : Nat) (e : PExpr) (cheapK := false) : RecEE := fun m => m.whnf n e (cheapK := cheapK)

def whnfPure (n : Nat) (e : PExpr) : RecM PExpr := fun m => m.whnfPure n e 

@[inline] def withPure [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with pure := true}) x

@[inline] def withCheapK [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with cheapK := true}) x

@[inline] def withCallData [MonadWithReaderOf Context m] (i : Nat) (n : Nat) (d? : (Option CallData)) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, n, d?)}) x

@[inline] def withCallId [MonadWithReaderOf Context m] (id : Nat) (dbgCallId : Option Nat := none) (x : m α) : m α :=
  withReader (fun c => {c with callId := id, dbgCallId}) x

@[inline] def withCallIdx [MonadWithReaderOf Context m] (i : Nat) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, default)}) x

@[inline] def withL4LTrace [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun c => {c with L4LTrace := true}) x

@[inline] def withL4LTraceO [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun c => {c with L4LTraceOverride := true}) x

@[inline] def withForallOpt [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with forallOpt := true}) x

@[inline] def withNoCache [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with noCache := true}) x

def dbg_wrap (idx : Nat) (m : RecM α) : RecM α := do
  modify fun s => {s with numCalls := s.numCalls + 1} 
  let s ← get
  let ret ← withCallId s.numCalls (← readThe Context).dbgCallId do
    withCallData idx s.numCalls none do 
      m
  pure ret

def getTrace (callIds : Bool := false) : RecM String := do
  let callStrs :=  (← readThe Context).callStack.map (fun d =>
    if callIds then
      s!"{d.1}/{d.2.1}"
    else
      s!"{d.1}"
  )
  pure s!"{callStrs}"

/--
Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not,
throws an error with `s` (the expression required be a sort).
NOTE: e must be a patched expression
-/
def ensureSortCore (e : PExpr) (s : Expr) : RecEE := do
  if Expr.isSort e then return (e, none)
  let (e, p?) ← whnf 1 e
  if e.toExpr.isSort then return (e, p?)
  throw <| .typeExpected (← getKEnv) default s

def assert (n : Nat) (b : Bool) : RecM Unit := do if not b then throw $ .other s!"assert fail {n}"

@[inherit_doc ensureSortCore]
def ensureSortCorePure (e : PExpr) (s : Expr) : RecM PExpr := do
  try
    let res ← runLeanMinus $ Lean.TypeChecker.ensureSort e.toExpr s
    pure res.toPExpr
  catch e =>
    throw e

/--
Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not,
throws an error with `s := f a` (the application requiring `f` to be of
function type).
-/
def ensureForallCore (e : PExpr) (s : Expr) : RecEE := do
  if Expr.isForall e then return (e, none)
  let (e, p?) ← whnf 2 e
  if e.toExpr.isForall then return (e, p?)
  throw <| .funExpected (← getKEnv) (← getLCtx) s

@[inherit_doc ensureForallCore]
def ensureForallCorePure (e : PExpr) (s : Expr) : RecM PExpr := do
  try
    let res ← runLeanMinus $ Lean.TypeChecker.ensureForall e.toExpr s
    pure res.toPExpr
  catch e =>
    throw e

/--
Checks that `l` does not contain any level parameters not found in the context `tc`.
-/
def checkLevel (tc : Context) (l : Level) : Except KernelException Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}' {tc.lparams}"

def inferFVar (tc : State) (name : FVarId) (idx : Option Nat) : Except KernelException PExpr := do
  if let some decl := tc.lctx.find? name then
    return decl.type.toPExpr
  throw <| .other s!"unknown free variable (index {idx}, name {name.name})"

/--
Infers the type of `.const e ls`.
-/
def inferConstant (tc : Context) (name : Name) (ls : List Level) :
    Except KernelException PExpr := do
  let e := Expr.const name ls
  -- should be okay as the environment should only contain patched constants
  let info ← tc.env.get name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if info.isUnsafe && tc.safety != .unsafe then
    throw <| .other s!"invalid declaration, it uses unsafe declaration '{e}'"
  if let .defnInfo v := info then
    if v.safety == .partial && tc.safety == .safe then
      throw <| .other
        s!"invalid declaration, safe declaration must not contain partial declaration '{e}'"
  for l in ls do
    checkLevel tc l
  return info.instantiateTypeLevelParams ls |>.toPExpr

/--
Infers the type of expression `e`. If `inferOnly := false`, this function will
throw an error if and only if `e` is not typeable according to Lean's
algorithmic typing judgment. Setting `inferOnly := true` optimizes to avoid
unnecessary checks in the case that `e` is already known to be well-typed.
-/
def inferType (n : Nat) (e : Expr) (dbg := false) : RecPE := fun m => m.inferType n e dbg

def inferTypePure (n : Nat) (e : PExpr) : RecM PExpr := fun m => do
  let ret ← m.inferTypePure n e
  pure ret

def getConst (n : Name) (lvls : List Level) : RecM Expr := do
  pure $ .const n lvls
/--
Gets the universe level of the sort that the type of `e` inhabits.
-/
def getTypeLevel (e : PExpr) : RecM (Level × PExpr) := do
  let eType ← inferTypePure 1 e
  let eTypeSort ← inferTypePure 2 eType
  let eTypeSort' ← ensureSortCorePure eTypeSort eType
  pure (eTypeSort'.toExpr.sortLevel!, eType)

def appHEqSymm (theqs : EExpr) : RecM EExpr := do
  -- let (lvl, tType, sType) ← info.getDM do
  --   let (lvl, tType) ← getTypeLevel t
  --   let sType ← inferTypePure 3 s
  --   pure (lvl, tType, sType)
  pure $ .rev theqs

def appHEqSymm? (theqs? : Option EExpr) : RecM (Option EExpr) := do
  let some theqs := theqs? | return none
  appHEqSymm theqs

def inferTypeCheck (e : PExpr) : RecM PExpr := do -- TODO make more efficient/use inferOnly := true
  let eT ← runLeanMinus $ Lean.TypeChecker.inferTypeCheck e.toExpr
  pure eT.toPExpr

/--
Returns whether `t` and `s` are definitionally equal according to Lean's
algorithmic definitional equality judgment.

NOTE: This function does not do any typechecking of its own on `t` and `s`.
So, when this is used as part of a typechecking routine, it is expected that
they are already well-typed (that is, that `check t` and `check s` 
did not/would not throw an error). This ensures in particular that any calls to
`inferType e (inferOnly := false)` on subterms `e` would not fail, so we know
that `e` types as the return value of `inferType e (inferOnly := true)`.
-/
def isDefEqCore (n : Nat) (t s : PExpr) : RecB := fun m => do
  let ret ← m.isDefEqCore n t s
  pure ret


def isDefEqCorePure (n : Nat) (t s : PExpr) : RecM Bool := fun m => m.isDefEqCorePure n t s

def quickIsDefEq (n : Nat) (t s : PExpr) (useHash : Bool := false) : RecLB := fun m => m.quickIsDefEq n t s useHash

def isDefEqLean (t s : Expr) (fuel := 1000) : RecM Bool := do
  runLeanRecM $ Lean.TypeChecker.isDefEq t s fuel

def _root_.Lean.TypeChecker.Data.usedM : TypeChecker.Data → RecM Bool
| {usedProofIrrelevance, usedKLikeReduction, usedFVarEq, ..} => do
  let opts := (← readThe Context).opts
  pure $ (opts.proofIrrelevance && usedProofIrrelevance) || (opts.kLikeReduction && usedKLikeReduction) || usedFVarEq

def isDefEqArgsLean (t s : Expr) : RecM (Bool × Bool) := do
  let (ret, s) ← runLeanRecM' $ Lean.TypeChecker.Inner.isDefEqArgs t s
  pure (ret, ← s.data.usedM)

def isDefEqAppLean (t s : Expr) : RecM (Bool × Bool) := do
  let (ret, s) ← runLeanRecM' $ Lean.TypeChecker.Inner.isDefEqApp t s
  pure (ret, ← s.data.usedM)

def usesPrfIrrel' (t s : Expr) (fuel := 1000) : RecM (Bool × Bool) := do
  let (ret, s) ← runLeanRecM' $ Lean.TypeChecker.isDefEq t s fuel
  pure (ret, ← s.data.usedM)

def usesPrfIrrel (t s : Expr) (fuel := 1000) : RecM (Bool × Bool) := do
  let (defEq, s) ← runLeanRecM' $ Lean.TypeChecker.isDefEq t s fuel
  pure (defEq, ← s.data.usedM)

def usesPrfIrrelWhnf (t : Expr) : RecM (Expr × Bool) := do
  let (defEq, s) ← runLeanRecM' $ Lean.TypeChecker.whnf t
  pure (defEq, ← s.data.usedM)

def inferTypeLean (n : Nat) (t : Expr) : RecM Expr := do
  dbg_wrap (55000 + n) $ runLeanRecM $ Lean.TypeChecker.Inner.inferType 0 t (inferOnly := false)

def inferTypeOnlyLean (n : Nat) (t : Expr) : RecM Expr := do
  dbg_wrap (55000 + n) $ runLeanRecM $ Lean.TypeChecker.Inner.inferType 0 t (inferOnly := true)

def whnfLean (t : Expr) : RecM Expr := do
  runLeanRecM $ Lean.TypeChecker.whnf t

def whnfCoreLean (t : Expr) : RecM Expr := do
  runLeanRecM $ Lean.TypeChecker.Inner.whnfCore 0 t

def inferTypePure' (e : PExpr) : RecM PExpr := do -- TODO make more efficient/use inferOnly := true
  let eT ← runLeanMinus $ Lean.TypeChecker.inferType e.toExpr
  pure eT.toPExpr

def addLVarToCtx (decl : LocalDeclE) (lastVar? : Option FVarId) (idx? : Option Nat := none) : RecM Unit := do
  let decl' := decl.toLocalDecl
  if let some lastVar := lastVar? then
    let mut fvarsToLets := (← get).fvarsToLets
    let lets := fvarsToLets.get? lastVar |>.getD #[] |>.push decl
    fvarsToLets := fvarsToLets.insert lastVar lets
    let s ← get
    let idx ← idx?.getDM do
      let mut i := (← getLCtx).decls.size - 1
      for v? in (← getLCtx).decls.toList.reverse do
        if let some v := v? then
          if v.fvarId == lastVar then
            return i
        i := i - 1
      throw $ .other "could not find variable dependency in context"
    let newDecls := s.lctx.decls.toArray.insertAt! (idx + 1) decl' -- FIXME too inefficient to go back and forth between Array and PersistentArray?
    modify fun st => { st with fvarsToLets := fvarsToLets, lctx := {st.lctx with decls := newDecls.toPArray', fvarIdToDecl := st.lctx.fvarIdToDecl.insert decl.fvarId decl'}}
  else
    let s ← get
    let newDecls := s.lctx.decls.toArray.insertAt! 0 decl'
    modify fun st => { st with initLets := st.initLets.push decl, lctx := {st.lctx with decls := newDecls.toPArray', fvarIdToDecl := st.lctx.fvarIdToDecl.insert decl.fvarId decl'}}

def mkLetE (t s : PExpr) (p : EExpr) (n := 0) : RecM (EExpr × LocalDeclE × Option (FVarId × Nat)) := do
  -- let pe := p.toExpr
  let (u, A) ← getTypeLevel t
  let B ← inferTypePure 55503 s
  let type := mkAppN (.const `HEq [u]) #[A, t, B, s]
  -- let typeVars := type.collectFVars
  let decl := .mk 0 (.mk (← mkIdNew (600 + n))) default type p.usedLets fun ctx => p.toExpr'.run' ctx

  -- if decl.fvarId.name == "_kernel_fresh.460".toName then
  --   dbg_trace s!"DBG[4]: TypeChecker.lean:543 {(← getLCtx).any fun x => x.fvarId.name == "_kernel_fresh.445".toName}"
  --   dbg_trace s!"DBG[5]: TypeChecker.lean:543 {p.toExpr.containsFVar' (.mk "_kernel_fresh.445".toName)}"

  -- let pe := p.toExpr
  let mut lastVar? : Option (FVarId × Nat) := none
  let mut i := 0
  let mut fvars := #[]
  for v? in (← getLCtx).decls.toList do
    -- dbg_trace s!"DBG[1]: TypeChecker.lean:530 {(← get).nid}"
    if let some v := v? then
      fvars := fvars.push v.toExpr
    else
      throw $ .other "encountered null context variable"
  let bvarIdx := type.abstract fvars.reverse |>.looseBVarRange
  if bvarIdx > 0 then
    lastVar? := .some ((← getLCtx).decls.get! (bvarIdx - 1) |>.get!.fvarId, bvarIdx - 1)
  i := (← getLCtx).decls.size - 1
  for v? in (← getLCtx).decls.toList.reverse do
    if let some (_, lastIdx) := lastVar? then
      if lastIdx >= i then
        break
    if let some v := v? then
      let a := p.usedLets.contains v
      -- if pe.containsFVar' v then
      --   if not a then
      --     dbg_trace s!"DBG[50]: TypeChecker.lean:561 {v.fvarId.name}, {p.usedLets.toList.map (·.name)}, {type.containsFVar' v}"

      if a then
        lastVar? := .some (v, i)
        break
    i := i - 1
  -- if let some (_, origi) := lastVar'? then
  --   if let some (_, newi) := lastVar? then
  --     if newi != origi then
  --       dbg_trace s!"DBG[72]: TypeChecker.lean:592 {(newi, origi)}"
  if let some (lastVar, _) := lastVar? then
    modify fun st => { st with letsToBindVar := st.letsToBindVar.insert (.mk decl.fvarId.name) (st.letsToBindVar.get? lastVar |>.getD lastVar)}
  -- if (← readThe Context).dbgFIds.size > 0 && decl.fvarId.name == (← readThe Context).dbgFIds[0]! then
  --   dbg_trace s!"DBG[2]: TypeChecker.lean:544 {(← get).letsToBindVar.get? decl.fvarId |>.map (·.name)}"

  addLVarToCtx decl (lastVar?.map (·.1)) (lastVar?.map (·.2))
  let lv := .lvar {A, B, a := t, b := s, u, v := decl.fvarId}
  pure (lv, decl, lastVar?)

def mkLet (T v : PExpr) : RecM (PExpr × LocalDeclE × Option (FVarId × Nat)) := do
  -- let pe := p.toExpr
  let decl := .mk 0 (.mk (← mkIdNew 501)) default T default fun _ => v

  -- if decl.fvarId.name == "_kernel_fresh.460".toName then
  --   dbg_trace s!"DBG[4]: TypeChecker.lean:543 {(← getLCtx).any fun x => x.fvarId.name == "_kernel_fresh.445".toName}"
  --   dbg_trace s!"DBG[5]: TypeChecker.lean:543 {p.toExpr.containsFVar' (.mk "_kernel_fresh.445".toName)}"

  -- let pe := p.toExpr
  let mut lastVar? : Option (FVarId × Nat) := none
  let mut fvars := #[]
  for v? in (← getLCtx).decls.toList do
    -- dbg_trace s!"DBG[1]: TypeChecker.lean:530 {(← get).nid}"
    if let some v := v? then
      fvars := fvars.push v.toExpr
    else
      throw $ .other "encountered null context variable"
  let bvarIdx := (T.toExpr.abstract fvars.reverse |>.looseBVarRange).max (v.toExpr.abstract fvars.reverse |>.looseBVarRange)
  if bvarIdx > 0 then
    lastVar? := .some ((← getLCtx).decls.get! (bvarIdx - 1) |>.get!.fvarId, bvarIdx - 1)

  if (← readThe Context).dbgFIds.size > 0 && decl.fvarId.name == (← readThe Context).dbgFIds[0]! then
    dbg_trace s!"DBG[2]: TypeChecker.lean:544 {lastVar?.map (·.1.name)}"

  addLVarToCtx decl (lastVar?.map (·.1)) (lastVar?.map (·.2))
  pure ((Expr.fvar decl.fvarId).toPExpr, decl, lastVar?)

def checkIsDefEqCache (_n : Nat) (t s : PExpr) (m : RecB) : RecB := do
  if not (← readThe Context).noCache then
    if let some (lv, decl, lastVar?) := (← get).isDefEqCache.get? (t, s) then -- TODO let var abstraction optimization
      if not ((← getLCtx).containsFVar (Expr.fvar decl.fvarId)) then
        addLVarToCtx decl lastVar?
      return (true, .some $ lv)
    else if let some (lv, decl, lastVar?) := (← get).isDefEqCache.get? (s, t) then
      if not ((← getLCtx).containsFVar (Expr.fvar decl.fvarId)) then
        addLVarToCtx decl lastVar? -- TODO add reversed let variable to context instead?
      return (true, .some $ .rev lv)
  let (result, p?) ← m
  let newp? ←
    if result then
      if let some p := (← get).isDefEqCache.get? (t, s) then
        return (result, p.1)
      if let some p := p? then
        let (lv, decl, lastVar?) ← mkLetE t s p _n
        modify fun st => { st with isDefEqCache := st.isDefEqCache.insert (t, s) (lv, decl, lastVar?.map (·.1))}
        pure $ .some $ lv
      else
        modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
        pure none
    else
      pure none
  pure (result, newp?)

def checkExprCache (e : PExpr) (T? : Option PExpr := none) : RecM PExpr := do
  if let some (decl, lastVar?) := (← get).exprCache.get? e then -- TODO let var abstraction optimization
    if not ((← getLCtx).containsFVar (.fvar decl.fvarId)) then
      addLVarToCtx decl lastVar?
    modify fun st => { st with }
    return (Expr.fvar decl.fvarId).toPExpr
  let T ← T?.getDM do inferTypePure 0 e
  let (lv, decl, lastVar?) ← mkLet T e
  modify fun st => { st with exprCache := st.exprCache.insert e (decl, lastVar?.map (·.1))}
  pure lv

@[inherit_doc isDefEqCore]
def isDefEq (n : Nat) (t s : PExpr) : RecB := do
  checkIsDefEqCache n t s do
    isDefEqCore n t s

def reduceRecursorLean (t : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  runLeanRecM $ Lean.TypeChecker.Inner.reduceRecursor t cheapRec cheapProj

def isDefEqBinder (binDatas : Array (BinderData × BinderData)) (tBody sBody : PExpr)
(f : PExpr → PExpr → Option EExpr → Array LocalDecl → Array (Option (LocalDecl × LocalDecl × LocalDecl × (Option EExpr))) → RecM (Option T))
: RecM (Bool × (Option T)) := do
  let rec loop idx (tvars svars tvars' : Array LocalDecl) ds : RecM (Bool × (Option T)) := do
    let ({name := tName, dom := tDom, info := tBi},
      {name := sName, dom := sDom,  info := sBi}) := binDatas.get! idx
    let tDom := tDom.instantiateRev (tvars.map (·.toExpr.toPExpr))
    let sDom := sDom.instantiateRev (svars.map (·.toExpr.toPExpr))
    let p? ← if tDom != sDom then
      let (defEq, p?) ← isDefEq 4 tDom sDom
      if !defEq then return (false, none)
      pure p?
    else pure none
    let sort ← inferTypePure 5 tDom
    let .sort lvl := (← ensureSortCorePure sort tDom).toExpr | throw $ .other "unreachable 5"
    withNewFVar 1 tName tDom tBi fun tvar => do
      let tvars := tvars.push tvar

      let cont d? svar := do
        let svars := svars.push svar
        let ds := ds.push d?

        if _h : idx < binDatas.size - 1 then
          let tvars' := if d?.isSome then tvars'.push tvar else tvars'
          loop (idx + 1) tvars svars tvars' ds
        else
          let tBody := tBody.instantiateRev (tvars.map (·.toExpr.toPExpr))
          let sBody := sBody.instantiateRev (svars.map (·.toExpr.toPExpr))
          -- let (true, usesPI) ← usesPrfIrrel tBody sBody | return (false, none)
          let ptbodEqsbod? ← if true then
            let (true, ptbodEqsbod?) ← isDefEq 6 tBody sBody | return (false, none) -- TODO refactor isDefEq to return normalized terms that were finally compared (to eliminate unused fvar dependencies)
            -- if ptbodEqsbod?.isNone && usesPI then
            --   dbg_trace s!"HERE 2"
            pure ptbodEqsbod?
          else
            pure none
          let ret ← f tBody sBody ptbodEqsbod? tvars.reverse ds.reverse
          pure (true, ret) -- FIXME can iterate backwards instead of reversing lists?

      if p?.isSome || tvars'.any fun tvar' => tDom.containsFVar' tvar' then
        withNewFVar 2 sName sDom sBi fun svar => do
          let teqsType := mkAppN (.const `HEq [lvl]) #[tDom, tvar.toExpr, sDom, svar.toExpr]
          let seqtType := mkAppN (.const `HEq [lvl]) #[sDom, svar.toExpr, tDom, tvar.toExpr]
          withNewFVar 3 default teqsType.toPExpr default fun vtEqs => do
            withNewFVar 4 default seqtType.toPExpr default fun vsEqt => do
              withEqFVar tvar svar { aEqb := vtEqs, bEqa := vsEqt, a := tvar.toExpr.toPExpr, b := svar.toExpr.toPExpr, A := tDom, B := sDom, u := lvl } do
                cont (.some (svar, vtEqs, vsEqt, p?)) svar 
      else
        cont none tvar

  termination_by (binDatas.size - 1) - idx
  loop 0 #[] #[] #[] #[]

def mkHRefl (_n : Nat) (lvl : Level) (T : PExpr) (t : PExpr) : RecM EExpr := do -- 7
  pure $ .refl {u := lvl, A := T, a := t}

def isDefEqPure (n : Nat) (t s : PExpr) (fuel := 1000) : RecM Bool := do
  try
    let ret ← runLeanMinus $ Lean.TypeChecker.isDefEq t s fuel
    pure ret
  catch e =>
    match e with
    | .deepRecursion =>
      pure false -- proof irrelevance may be needed to avoid deep recursion (e.g. String.size_toUTF8)
    | _ => 
      dbg_trace s!"isDefEqPure error: {n}, {t}, {s}"
      throw e

def isValidApp (_n : Nat) (t : Expr) : RecM Bool := do
  try
    _ ← runLeanMinusRecM $ Lean.TypeChecker.Inner.inferType 0 t (inferOnly := false)
    pure true
  catch _e =>
    throw _e
    pure false

def appPrfIrrelHEq (P Q : PExpr) (hPQ : EExpr) (p q : PExpr) : RecM EExpr := do
  return .prfIrrel {P, p, q, extra := .HEq {Q, hPQ}}

def appPrfIrrel (P : PExpr) (p q : PExpr) : RecM EExpr := do
  return .prfIrrel {P, p, q}

def appHEqTrans? (t s r : PExpr) (theqs? sheqr? : Option EExpr) : RecM (Option EExpr) := do
  match theqs?, sheqr? with
  | none, none => return none
  | .some theqs, .some sheqr =>
    let (lvl, tType) ← getTypeLevel t
    let sType ← inferTypePure 7 s
    let rType ← inferTypePure 8 r

    return .some $ .trans {u := lvl, A := tType, B := sType, C := rType, a := t, b := s, c := r, aEqb := theqs, bEqc := sheqr}
  | none, .some sheqr => return sheqr
  | .some theqs, none => return theqs

def getLets (n : Nat) (fid : FVarId) : RecM (Array LocalDeclE) := do
  let some lets := (← get).fvarsToLets[fid]? | pure #[]
  let mut ret := #[]
  for l in lets.reverse do
    -- if l.fvarId.name == "_kernel_fresh.193".toName then
    --   dbg_trace s!"DBG[3]: TypeChecker.lean:966 {n}"
    ret := ret.push l ++ (← getLets n l.fvarId)
  pure ret
decreasing_by
  sorry -- TODO the index of fid in the local context is guaranteed to increase

def isDefEqForall' (t s : PExpr) (numBinds : Nat) (f : Option EExpr → RecM (Option T)) : RecM (Bool × Option T) := do
  -- assert! numBinds > 0
  let rec getData t s n := do
    match n, t, s with
    | n + 1, .forallE tName tDom tBody tBi, .forallE sName sDom sBody sBi =>
      let (datas, tBody, sBody) ← getData tBody sBody n
      pure (#[({name := tName, dom := tDom.toPExpr, info := tBi}, {name := sName, dom := sDom.toPExpr, info := sBi})] ++ datas, tBody, sBody)
    | _, tBody, sBody =>
      pure (#[], tBody.toPExpr, sBody.toPExpr)
  let (datas, tBody, sBody) ← getData t.toExpr s.toExpr numBinds
  isDefEqBinder datas tBody sBody fun Ua Vx UaEqVx? as ds => do
    let mut UaEqVx? := UaEqVx?
    let mut Ua := Ua
    let mut Vx := Vx

    let mut idx := 0
    for (a, d?) in as.zip ds do

      let x := if let some (b, _, _) := d? then b else a

      idx := idx + 1

      if d?.isSome || UaEqVx?.isSome then
        let (UaTypeLvl, UaType) ← getTypeLevel Ua
        let UaType ← whnfPure 9 UaType
        let UaLvl := UaType.toExpr.sortLevel!

        let (ALvl, A) ← getTypeLevel a.toExpr.toPExpr
        let u := ALvl
        let v := UaLvl

        let (U, V) := ((Ua, a), (Vx, x))
        let extra ← if let some UaEqVx := UaEqVx? then
          if let .some (b, aEqb, bEqa, hAB?) := d? then
            let B := b.type.toPExpr
            if let some hAB := hAB? then
              pure $ .ABUV {B, b, vaEqb := {aEqb, bEqa, lets := ← getLets 17 aEqb}, hAB, V, UaEqVx, blets := ← getLets 11 b}
            else -- (if explicit == true)
              let hAB ← mkHRefl 7 u.succ (Expr.sort u).toPExpr A
              pure $ .ABUV {B, b, vaEqb := {aEqb, bEqa, lets := ← getLets 16 aEqb}, hAB, V, UaEqVx, blets := ← getLets 12 b}
              -- pure $ .ABApp {b, vaEqb := {aEqb, bEqa}}
          else
            pure $ .UV {V, UaEqVx}
        else 
          let .some (b, aEqb, bEqa, hAB?) := d? | unreachable!
          let B := b.type.toPExpr
          let some hAB := hAB? | unreachable!

          -- Ua and Vb may still contain references to a and b despite being
          -- defeq, so we need to consider this case, and
          -- cannot immediately fall back to .AB (which has no dependent variant)
          let dep := Ua.containsFVar' a || Vx.containsFVar' x
          if dep then
            let UaEqVx ← mkHRefl 1 UaTypeLvl UaType Ua
            pure $ .ABUV {B, b, vaEqb := {aEqb, bEqa, lets := ← getLets 15 aEqb}, hAB, V, UaEqVx, blets := ← getLets 13 b}
          else
            pure $ .AB {B, b, vaEqb := {aEqb, bEqa, lets := ← getLets 14 aEqb}, hAB, blets := ← getLets 14 b}

        UaEqVx? := .some $ .forallE {u, v, A, a, U, extra, alets := ← getLets 18 a}

      Ua := (← getLCtx).mkForall #[a.toExpr] Ua |>.toPExpr
      Vx := (← getLCtx).mkForall #[x.toExpr] Vx |>.toPExpr

    -- if as.any fun a => a.toExpr.isFVar && a.toExpr.fvarId!.name == "_kernel_fresh.104".toName then

    f UaEqVx?

def alignForAll (numBinds : Nat) (ltl ltr : Expr) : RecM (Expr × Expr × Nat) := do
  match numBinds with
  | numBinds' + 1 => do
    match (← whnfPure 11 ltl.toPExpr).toExpr, (← whnfPure 12 ltr.toPExpr).toExpr with
    | .forallE nl tdl tbl bil, .forallE nr tdr tbr bir => do
      withNewFVar 6 nl tdl.toPExpr bil fun vl => do
        withNewFVar 7 nr tdr.toPExpr bir fun vr => do
          let ntbl := tbl.instantiate1 (.fvar vl)
          let ntbr := tbr.instantiate1 (.fvar vr)
          let (atbl, atbr, n) ← alignForAll numBinds' ntbl ntbr
          let nltl := (← getLCtx).mkForall #[(.fvar vl)] atbl
          let nltr := (← getLCtx).mkForall #[(.fvar vr)] atbr
          pure (nltl, nltr, n + 1)
    | _, _ => pure (ltl, ltr, 0)
  | _ => pure (ltl, ltr, 0)

def isDefEqApp (n : Nat) (t s : PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default)
  (tfEqsf? : Option (Option EExpr) := none) : RecM (Bool × Option EExpr) := fun m => m.isDefEqApp n t s targsEqsargs? tfEqsf?

def getInitLets : RecM (Array LocalDeclE) := do
  let lets := (← get).initLets
  let mut ret := #[]
  for l in lets.reverse do
    ret := ret.push l ++ (← getLets 0 l.fvarId)
  pure ret

/--
If `t` and `s` are lambda expressions, checks that their domains are defeq and
recurses on the bodies, substituting in a new free variable for that binder
(this substitution is delayed for efficiency purposes using the `subst`
parameter). Otherwise, does a normal defeq check.
-/
def isDefEqLambda (t s : PExpr) : RecB := do
  let rec getData t s := do
    match t, s with
    | .lam tName tDom tBody tBi, .lam sName sDom sBody sBi =>
      let (datas, tBody, sBody) ← getData tBody sBody
      pure (#[({name := tName, dom := tDom.toPExpr, info := tBi}, {name := sName, dom := sDom.toPExpr, info := sBi})] ++ datas, tBody, sBody)
    | tBody, sBody =>
      pure (#[], tBody.toPExpr, sBody.toPExpr)
  let (datas, tBody, sBody) ← getData t.toExpr s.toExpr
  let ret ← isDefEqBinder datas tBody sBody fun fa' gx' faEqgb? as ds => do
    let mut faEqgx? := faEqgb?
    let mut fa := fa'
    let mut gx := gx'
    for (a, d?) in as.zip ds do
      -- if a.fvarId == .mk "_kernel_fresh.2388".toName then
      --   dbg_trace s!"DBG[B]: TypeChecker.lean:819 (after if a == sirry then)"

      let f := (← getLCtx).mkLambda #[a.toExpr] fa |>.toPExpr
      -- gx was abstracted over a if A defeq B (instead of over a fresh (b : B))
      let x : LocalDecl := if let some (b, _, _) := d? then b else a
      let g := (← getLCtx).mkLambda #[x.toExpr] gx |>.toPExpr
      if d?.isSome || faEqgx?.isSome then
        let (ALvl, A) ← getTypeLevel a.toExpr.toPExpr
        let u := ALvl
        let (UaLvl, Ua) ← getTypeLevel fa
        let v := UaLvl
        let Vx ← inferTypePure 41 gx
        let faEqgx ← faEqgx?.getDM $ mkHRefl 6 UaLvl Ua fa
        let (U, V) := ((Ua, a), (Vx, x))
        let extra ← if let some (b, aEqb, bEqa, hAB?) := d? then
          let hAB ← hAB?.getDM (mkHRefl 8 u.succ (Expr.sort u).toPExpr A)
          let B := b.type.toPExpr
          pure $ .ABUV {B, b, hAB, vaEqb := {aEqb, bEqa, lets := ← getLets 10 aEqb}, blets := ← getLets 9 b} {V}
        else
          let (_, UaEqVx?) ← isDefEq 43 Ua Vx
          if UaEqVx?.isSome then
            pure $ .UV {V}
          else
            pure $ .none
        faEqgx? := .some $ .lam {u, v, A, a, U, f, g, faEqgx, extra, alets := ← getLets 8 a}

      fa := f
      gx := g
    pure faEqgx?
  pure ret

def meths : ExtMethods RecM := {
    isDefEq := isDefEq
    isDefEqApp := fun n t s m => isDefEqApp n t s (targsEqsargs? := m)
    isDefEqPure := isDefEqPure
    isDefEqPure' := fun n t s l => isDefEqPure n t s l
    isDefEqLean := isDefEqLean
    whnf  := whnf
    mkIdNew  := mkIdNew
    mkId  := fun n _ => mkIdNew n
    mkId'  := mkId'
    whnfPure := whnfPure
    mkHRefl := mkHRefl
    getTypeLevel := getTypeLevel
    ensureSortCorePure := ensureSortCorePure
    inferTypePure := inferTypePure
    inferTypeCheck := inferTypeCheck
    inferTypeLean := inferTypeLean
    inferType := inferType
    appPrfIrrelHEq := appPrfIrrelHEq
    appPrfIrrel := appPrfIrrel
    appHEqTrans? := appHEqTrans?
    withPure := withPure
    trace := trace
    ttrace := ttrace
    shouldTTrace := shouldTTrace
    callId := do pure (← readThe Context).callId
    numCalls := do pure (← get).numCalls
    shouldTrace := shouldTrace
    getTrace := fun b => getTrace b
    withNewFVar := withNewFVar
    getLets := getLets
    checkExprCache := @checkExprCache
    usesPrfIrrel := usesPrfIrrel
    isDefEqLambda := isDefEqLambda
    withNoCache := withNoCache
  }

def methsA : ExtMethodsA RecM := {
    meths with
    opt := true
    isDefEqForall := isDefEqForall'
    -- alignForAll := alignForAll 
  }

def isDefEqApp'' (tf sf : PExpr) (tArgs sArgs : Array PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default)
  (tfEqsf? : Option (Option EExpr) := none) (cache := true) : RecM (Bool × Option (EExpr × Array (Option (PExpr × PExpr × EExpr)))) := do
  let t := Lean.mkAppN tf (tArgs.map (·.toExpr)) |>.toPExpr
  let s := Lean.mkAppN sf (sArgs.map (·.toExpr)) |>.toPExpr
  if let some p? := (← get).isDefEqAppCache.get? (#[tf] ++ tArgs, #[sf] ++ sArgs) then
    if let some (lv, decl, lastVar?, p) := p? then
      if not ((← getLCtx).containsFVar (Expr.fvar decl.fvarId)) then
        addLVarToCtx decl lastVar?
      return (true, .some $ (lv, p))
    else
      return (true, none)
  else if let some p? := (← get).isDefEqAppCache.get? (#[sf] ++ sArgs, #[tf] ++ tArgs) then
    if let some (lv, decl, lastVar?, p) := p? then
      if not ((← getLCtx).containsFVar (Expr.fvar decl.fvarId)) then
        addLVarToCtx decl lastVar?
      return (true, .some $ (.rev lv, p.map fun d? => d?.map fun (t, s, p) => (s, t, .rev p)))
    else
      return (true, none)
  let (isDefEq, p?) ← App.isDefEqApp'' methsA tf sf tArgs sArgs targsEqsargs? tfEqsf?
  if cache && isDefEq then
    let cacheData? ← p?.mapM fun (p, d) => do
      let (lv, decl, lastVar?) ← mkLetE t s p 102
      pure (lv, decl, lastVar?.map (·.1), d)
    modify fun st => { st with isDefEqAppCache := st.isDefEqAppCache.insert (#[tf] ++ tArgs, #[sf] ++ sArgs) cacheData? }
  pure (isDefEq, p?)

-- def isDefEqApp'' (tf sf : PExpr) (tArgs sArgs : Array PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default)
--   (tfEqsf? : Option (Option EExpr) := none) : RecM (Bool × Option (EExpr × Array (Option (PExpr × PExpr × EExpr)))) := do
--   if let some p? := (← get).isDefEqAppCache.get? (#[tf] ++ tArgs, #[sf] ++ sArgs) then
--     let t := Lean.mkAppN tf (tArgs.map (·.toExpr))
--     let s := Lean.mkAppN sf (sArgs.map (·.toExpr))
--     let (u, A) ← getTypeLevel t.toPExpr
--     if let some p := p? then
--       return (true, .some $ (.sry {u, A, B := (← inferTypePure 0 s.toPExpr), a := t.toPExpr, b := s.toPExpr}, p.2)) -- TODO use let variables
--     else
--       return (true, none) -- TODO use let variables
--   let (isDefEq, p?) ← App.isDefEqApp'' methsA tf sf tArgs sArgs targsEqsargs? tfEqsf?
--   if isDefEq then
--     modify fun st => { st with isDefEqAppCache := st.isDefEqAppCache.insert (#[tf] ++ tArgs, #[sf] ++ sArgs) p? }
--   pure (isDefEq, p?)

def isDefEqApp' (t s : PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default)
  (tfEqsf? : Option (Option EExpr) := none) (cache := true) : RecM (Bool × Option (EExpr × Array (Option (PExpr × PExpr × EExpr)))) := do
  unless t.toExpr.isApp && s.toExpr.isApp do return (false, none)
  t.toExpr.withApp fun tf tArgs =>
  s.toExpr.withApp fun sf sArgs => 
    let tf := tf.toPExpr
    let sf := sf.toPExpr
    let tArgs := tArgs.map (·.toPExpr)
    let sArgs := sArgs.map (·.toPExpr)
    isDefEqApp'' tf sf tArgs sArgs targsEqsargs? tfEqsf? cache


/--
Checks if applications `t` and `s` (should be WHNF) are defeq on account of
their function heads and arguments being defeq.
-/
def _isDefEqApp (t s : PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default)
  (tfEqsf? : Option (Option EExpr) := none) : RecM (Bool × Option EExpr) := do
  checkIsDefEqCache 104 t s do
    let (isDefEq, data?) ← isDefEqApp' (cache := false) t s targsEqsargs? tfEqsf?
    let p? := data?.map (·.1)
    pure (isDefEq, p?)

def isDefEqBinOpt (t s : PExpr) (lambda : Bool): RecB := do
  let (.some (tAbsType, tAbsDomsVars, tAbsDoms, sAbsType, sAbsDomsVars, sAbsDoms, tAbsDomsEqsAbsDoms?, _)) ← App.binAbs methsA 2000 t s lambda |
    return (false, none)

  let tLCtx := tAbsDomsVars.foldl (init := (← getLCtx)) fun acc v => LocalContext.mkLocalDecl acc v.fvarId v.userName v.type default
  let sLCtx := sAbsDomsVars.foldl (init := (← getLCtx)) fun acc v => LocalContext.mkLocalDecl acc v.fvarId v.userName v.type default
  let tf' := tLCtx.mkLambda (tAbsDomsVars.map (.fvar ·.fvarId)) tAbsType
  let sf' := sLCtx.mkLambda (sAbsDomsVars.map (.fvar ·.fvarId)) sAbsType

  let mut tAbsDomsEqsAbsDomsMap := default
  let mut idx := 0
  for tAbsDomsEqsAbsDom? in tAbsDomsEqsAbsDoms? do
    tAbsDomsEqsAbsDomsMap := tAbsDomsEqsAbsDomsMap.insert idx tAbsDomsEqsAbsDom?
    idx := idx + 1

  if tAbsDoms.size == 0 then
    pure (true, none)
  else
    let (ret, dat?) ← dbg_wrap 9908 $ isDefEqApp'' tf'.toPExpr sf'.toPExpr tAbsDoms sAbsDoms tAbsDomsEqsAbsDomsMap
    pure (ret, dat?.map (·.1))

def isDefEqForallOpt (t s : PExpr) : RecB := isDefEqBinOpt t s false
def isDefEqLambdaOpt (t s : PExpr) : RecB := isDefEqBinOpt t s true

def lamCount : Expr → Nat
  | .lam _ _ b _ =>
    lamCount b + 1
  | _ => 0

/--
If `t` and `s` are for-all expressions, checks that their domains are defeq and
recurses on the bodies, substituting in a new free variable for that binder
(this substitution is delayed for efficiency purposes using the `subst`
parameter). Otherwise, does a normal defeq check.
-/
def isDefEqForall (t s : PExpr) (numBinds := 0) : RecB := do
  -- if numBinds == 0 then
  --   isDefEqForallOpt' t s
  -- else
    isDefEqForall' t s numBinds fun tEqs? => pure tEqs?

inductive WhnfIndex where
| fn : WhnfIndex
| arg (i : Nat) : WhnfIndex
| proj (i : Nat) : WhnfIndex

def _root_.Lean4Less.PExpr.getWhnfAt (l : List WhnfIndex) (e : PExpr) : RecM PExpr := do
  let e ← whnfPure 0 e
  match l with
  | i :: l =>
    match i with
    | .fn => getWhnfAt l e.toExpr.getAppFn.toPExpr
    | .arg i => getWhnfAt l e.toExpr.getAppArgs[i]!.toPExpr
    | .proj _ => match e.toExpr with
      | .proj _ _ e' =>
        getWhnfAt l e'.toPExpr
      | _ => unreachable!
  | [] => whnfPure 0 e

instance : OfNat WhnfIndex n where
ofNat := .arg n

def alignLets (remLets : List LocalDeclE) (vars vals : Array Expr) (f : Array Expr → Array Expr → RecM T) : RecM T := do
  let rec loop remLets letVars letVals := do
    match remLets with
    | l :: remLets =>
      let r e := e.replaceFVars (vars ++ letVars) (vals ++ letVals)
      let ltype := r l.type
      let lvalue := r (l.value {} )
      let letVars := letVars.push (.fvar l.fvarId)
      withNewLetVar 20 l.userName ltype lvalue fun lvar => do
        let letVals := letVals.push lvar.toExpr
        -- if lets'.size > 0 then
        --   dbg_trace s!"DBG[1]: TypeChecker.lean:977: lets'={lets'.size}"
        -- let mut lctx ← getLCtx
        -- for l in lets do
        --   lctx := lctx.addDecl l
        -- withLCtx lctx do
        loop remLets letVars letVals
    | [] => f letVars letVals
    termination_by remLets.length

  loop remLets #[] #[]

def smartCast' (n : Nat) (tl tr e : PExpr) (p? : Option EExpr := none) : RecM ((Bool × Option EExpr) × PExpr × Option (Option EExpr)) := do
  let getLvl tl := do
    let sort ← inferTypePure 13 tl
    let sort' ← ensureSortCorePure sort tl
    pure sort'.toExpr.sortLevel!

  let mkCast'' (_n : Nat) (nm : Name) (tl tr : Expr) (p : EExpr) e (prfVars prfVals : Array Expr) (lvl : Level) := do
    let pe := p.toExpr (dbg := (← shouldTTrace))
    -- dbg_trace s!"DBG[2]: TypeChecker.lean:825 {← getTrace}, {← callId}, {p?.isSome}"
    -- _ ← inferTypeCheck pe.toPExpr
    -- dbg_trace s!"DBG[3]: TypeChecker.lean:827 (after _ ← inferTypeCheck pe.toPExpr)"
    let app := Lean.mkAppN (← getConst nm [lvl]) #[tl, tr, pe, e]
    pure $ app.replaceFVars prfVars prfVals

  let mkCast' (n : Nat) (nm : Name) (tl tr : Expr) (p : EExpr) e (prfVars prfVals : Array Expr) := do
    let lvl ← getLvl tl.toPExpr
    mkCast'' n nm tl tr p e prfVars prfVals lvl

  let rec loop remLams e tl tr (lamVars prfVars prfVals letVars letVals : Array Expr) (lamLetVars : Array (Array LocalDecl)) p : RecM Expr := do
    match remLams, e, tl, tr, p with
    | remLams' + 1, .lam nm _ b bi, .forallE _ _ tbl .., .forallE _ tdr tbr .., .forallE forallData =>
      let {A, a, extra, u, alets, ..} := forallData
      withNewFVar 5 nm tdr.toPExpr bi fun var => do
        let (UaEqVx? : Option EExpr) := 
          match extra with
          | .ABUV {UaEqVx, ..}
          | .UV {UaEqVx, ..} => Option.some UaEqVx.1
          | _ => none

        let v := .fvar var
        let lamVars := lamVars.push v

        let (newPrfVars, newPrfVals, vCast, lets') ←
          match extra with
          | .ABUV {B, b, vaEqb, hAB, blets, ..}
          | .AB {B, b, vaEqb, hAB, blets, ..} =>
            let hBA ← appHEqSymm hAB
            let vCast ← mkCast'' (1000 + n) `L4L.castHEq B.toExpr A.toExpr hBA v (prfVars ++ letVars) (prfVals ++ letVals) u
            let vCastEqv ← mkCast'' (2000 + n) `L4L.castOrigHEq B.toExpr A.toExpr hBA v (prfVars ++ letVars) (prfVals ++ letVals) u

            let newPrfVars := #[a.toExpr, b.toExpr, vaEqb.aEqb.toExpr]
            let newPrfVals := #[vCast, v, vCastEqv]
            -- let r e := e.replaceFVars (prfVars ++ newPrfVars ++ letVars) (prfVals ++ newPrfVals ++ letVals)

            -- pure (newPrfVars, newPrfVals, vCast, (alets ++ blets ++ vaEqb.lets).map fun l => {l with type := r l.type, value := fun ctx => r (l.value ctx)})
            pure (newPrfVars, newPrfVals, vCast, alets ++ blets ++ vaEqb.lets)
          | _ => 
            let newPrfVars := #[a.toExpr]
            let newPrfVals := #[v]
            -- let r e := e.replaceFVars (prfVars ++ newPrfVars ++ letVars) (prfVals ++ newPrfVals ++ letVals)

            -- pure (#[a.toExpr], #[v], v, alets.map fun l => {l with type := r l.type, value := fun ctx => r (l.value ctx)})
            pure (newPrfVars, newPrfVals, v, alets)

        let prfVars := prfVars ++ newPrfVars
        let prfVals := prfVals ++ newPrfVals

        let b := b.instantiate1 vCast -- FIXME this may duplicate proofs
        let tbl := tbl.instantiate1 vCast
        let tbr := tbr.instantiate1 v

        alignLets lets'.toList (prfVars ++ letVars) (prfVals ++ letVals) fun newLetVars newLetVals => do
          let lamLetVars := lamLetVars.push (← newLetVals.mapM fun v => do
              let some decl := (← getLCtx).find? v.fvarId! | throw $ .other "unreachable!"
              pure decl
            )
          let letVars := letVars ++ newLetVars
          let letVals := letVals ++ newLetVals
          if let some (UaEqVx : EExpr) := UaEqVx? then
            let ret ← loop remLams' b tbl tbr lamVars prfVars prfVals letVars letVals lamLetVars UaEqVx
            -- if newLetVars.any fun l => l.fvarId!.name == "_kernel_fresh.2400".toName then
            --   dbg_trace s!"DBG[C]: EExpr.lean:858 {ret.containsFVar' (.mk "_kernel_fresh.2400".toName)}"
            --   for val in letVals do
            --     let some var := (← getLCtx).find? val.fvarId! | throw $ .other "unreachable!"
            --     dbg_trace s!"DBG[E]: EExpr.lean:858 {var.fvarId.name}, {var.type.containsFVar' (.mk "_kernel_fresh.2400".toName)}, {var.value.containsFVar' (.mk "_kernel_fresh.2400".toName)}"
            pure ret
          else
            -- let ret := (← getLCtx).mkLambda' (← letUseCount) lamVars b
            let bod := b.replaceFVars (prfVars ++ letVars) (prfVals ++ letVals)
            let ret := expandLetsLambda (← getLCtx) lamVars lamLetVars bod
            -- if letVars.any fun l => l.fvarId!.name == "_kernel_fresh.2400".toName then
            --   dbg_trace s!"DBG[D]: EExpr.lean:858 {ret.containsFVar' (.mk "_kernel_fresh.2400".toName)}, {bod.containsFVar' (.mk "_kernel_fresh.2400".toName)}"
            pure ret
    | _, _, _, _, _ =>
      let cast ← mkCast' (3000 + n) `L4L.castHEq tl tr p e (prfVars ++ letVars) (prfVals ++ letVals)
      -- let ret := (← getLCtx).mkLambda' (← letUseCount) lamVars cast
      let ret := expandLetsLambda (← getLCtx) lamVars lamLetVars cast
      -- if letVars.any fun l => l.fvarId!.name == "_kernel_fresh.2400".toName then
      --   dbg_trace s!"DBG[F]: EExpr.lean:858 {ret.containsFVar' (.mk "_kernel_fresh.2400".toName)}, {prfVals.any fun v => v.containsFVar' (.mk "_kernel_fresh.2400".toName)} {letVals.any fun v => v.containsFVar' (.mk "_kernel_fresh.2400".toName)}"
      pure ret
  termination_by remLams -- TODO why doesn't structural recursion on `p` work here?

  let nLams := lamCount e
  let tlEqtr? ← do
    pure ()
    if let some p := p? then
      pure $ (true, .some p)
    else
      let (tl', tr', nLams) ← try 
        alignForAll nLams tl tr
      catch ex =>
        -- dbg_trace s!"smartCast error: {n}, {nLams}"
        throw ex
      let tl' := tl'.toPExpr
      let tr' := tr'.toPExpr
      if nLams > 0 then
        let ret ← isDefEqForall tl' tr' nLams
        pure ret
      else
        let ret ← isDefEq (1000 + n) tl tr
        pure ret

  -- if let (true, some tlEqtr) := tlEqtr? then -- sanity check (TODO delete)
  --   let pT ← inferTypePure 0 tlEqtr
  --   let lvl ← getLvl tl tr
  --   let heq := (Lean.mkAppN (← getConst `HEq [.succ lvl]) #[(Expr.sort lvl).toPExpr, tl, (Expr.sort lvl).toPExpr, tr]).toPExpr
  --   if not (← isDefEqPure 0 pT heq) then
  --     let (true, some tlEqtr) ← isDefEq (1000 + n) tl tr | unreachable!
  --     throw $ .other s!"cast equality does not have expected type"
  let mut (ret, eEqCaste??) := (← tlEqtr?.2.mapM (fun (p : EExpr) => do
    if nLams == 0 then
      let cast ← mkCast' (4000 + n) `L4L.castHEq tl.toExpr tr.toExpr p e.toExpr #[] #[]
      let lvl ← getLvl tl
      -- let (true, eEqCaste?) ← checkIsDefEqCache 12345 e cast.toPExpr do pure $ (true, .some $ .rev $ .cast {A := tl, B := tr, p, e, u := lvl})  | unreachable!
      pure (cast.toPExpr, none)
    else
      pure ((← loop nLams e.toExpr tl.toExpr tr.toExpr #[] #[] #[] #[] #[] #[] p).toPExpr, none))).getD (e, none)

  pure $ (tlEqtr?, ret, eEqCaste??)

def insertInitLets (e : PExpr) : RecM PExpr := do
  let initLets ← getInitLets
  -- let n := (.mk "_kernel_fresh.38".toName)
  -- for v in initLets do
  --   match v with
  --   | .mk (fvarId := id) (type := t) (value := v) .. => dbg_trace s!"Y: TypeChecker.lean:1114 {id.name}, {(v {}).containsFVar' n} {t.containsFVar' n}"

  -- let ret := (← getLCtx).mkLambda' (← letUseCount) (initLets.map (Expr.fvar ·.fvarId)) e |>.toPExpr
  let ret := expandLets (initLets.map (·.toLocalDecl)) e |>.toPExpr
  pure ret

def smartCast (n : Nat) (tl tr e : PExpr) (p? : Option EExpr := none) : RecM (Bool × PExpr) := do
  let ret ← try
    smartCast' n tl tr e p?
  catch ex =>
    -- dbg_trace s!"smartCast error: {n}"
    throw ex
  pure (ret.1.1, ret.2.1)

def maybeCast (n : Nat) (p? : Option EExpr) (typLhs typRhs e : PExpr) : RecM PExpr := do
  pure $ (← p?.mapM (fun (p : EExpr) => do
        let (_, cast) ← smartCast n typLhs typRhs e p
        pure cast
      )
    ).getD e

def isDefEqProofIrrel' (t s tType sType : PExpr) (pt? : Option EExpr) (n : Nat) (useRfl := false) : RecM (Option EExpr) := do
  if ← isDefEqPure (2000 + n) t s 15 then -- limit maximum recursion depth to 15 to avoid incurring worst-case runtime
    if useRfl then
      let p := .refl {u := 0, A := tType, a := t}
      return .some p
    else
    return none
  else
    let p ← if let some pt := pt? then
      appPrfIrrelHEq tType sType pt t s
    else
      appPrfIrrel tType t s
    return (.some p)

def methsR : ExtMethodsR RecM := {
    meths with
    smartCast := smartCast'
    maybeCast := maybeCast
    isDefEqApp' := fun t s m => isDefEqApp' t s (targsEqsargs? := m)
    isDefEqProofIrrel' := isDefEqProofIrrel' (n := 2) (useRfl := true) -- need to use `useRfl` because of the lack of transitivity
  }

/--
Infers the type of lambda expression `e`.
-/
def inferLambda (e : Expr) (dbg := false) : RecPE := loop #[] false e where
  loop fvars domPatched : Expr → RecPE -- TODO OK that fvars is not `Array PExpr`?
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let (sort, d'?) ← inferType 14 d
    let (sort', p?) ← ensureSortCore sort d
    let d' ← maybeCast 20 p? sort sort' (d'?.getD d.toPExpr)

    withNewFVar 8 name d' bi fun id => do
      let fvars := fvars.push (.fvar id)
      loop fvars (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let e := e.instantiateRev fvars
    let (r, e'?) ← inferType 15 e dbg
    let e' := e'?.getD e.toPExpr
    let r := r.toExpr.cheapBetaReduce |>.toPExpr
    let (rSort) ← inferTypePure 16 r
    let (rSort', p?) ← ensureSortCore rSort r -- TODO need to test this
    let r' ← maybeCast 21 p? rSort rSort' r

      -- if fvar.fvarId!.name == "_kernel_fresh.273".toName then
      --   ttrace s!"DBG[1]: TypeChecker.lean:1064 {lets.map (·.fvarId.name)}"
      -- if ← shouldTTrace then
        -- let mut found := false
        -- ttrace s!"X': {fvar.fvarId!.name}, {(← get).fvarRegistry.get? fvar.fvarId!.name}"
        -- for l in lets do
        --   if not found then
        --     ttrace s!"X: {l.type.containsFVar' (.mk "_kernel_fresh.503".toName)}, {(l.value {}).containsFVar' (.mk "_kernel_fresh.503".toName)} {l.fvarId.name}"
        --   found := l.fvarId == (.mk "_kernel_fresh.503".toName)

    let mut lets := #[]
    for fvar in fvars do
      let lets' : Array LocalDeclE ← getLets 1 fvar.fvarId!
      lets := lets.push (lets'.map (·.toLocalDecl))
    let patch ←
      if domPatched || e'?.isSome then do
        -- let ret := ((← getLCtx).mkLambda' (← letUseCount) newfvars e').toPExpr
        let ret := (expandLetsLambda (← getLCtx) fvars lets e').toPExpr
        -- ttrace s!"DBG[2]: TypeChecker.lean:1067: ret={ret.toExpr.containsFVar' (.mk "_kernel_fresh.503".toName)} {← callId}"
        pure $ some ret
      else 
        pure none

    -- TODO only return .some if any of the fvars had domains that were patched, or if e'? := some e'
    -- return (( (← getLCtx).mkForall' (← letUseCount) newfvars r').toPExpr, patch)
    return ((expandLetsForall (← getLCtx) fvars lets r').toPExpr, patch)

/--
Infers the type of for-all expression `e`.
-/
def inferForall (e : Expr) : RecPE := do
    let ret ← loop #[] #[] false e
    -- if ← shouldTTrace then
    --   for v in (← getLCtx) do
    --     match v with
    --     | .cdecl (fvarId := id) (type := t) .. => dbg_trace s!"DBG[17]: TypeChecker.lean:1114 {id.name}, {t.containsFVar' (.mk "_kernel_fresh.37".toName)}"
    --     | .ldecl (fvarId := id) (type := t) (value := v) .. => dbg_trace s!"DBG[17]: TypeChecker.lean:1114 {id.name}, {v.containsFVar' (.mk "_kernel_fresh.37".toName)} {t.containsFVar' (.mk "_kernel_fresh.37".toName)}"
    pure ret
  where
    loop fvars us domPatched : Expr → RecPE
    | .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      let (sort, d'?) ← inferType 17 d
      let (sort', p?) ← ensureSortCore sort d
      let lvl := sort'.toExpr.sortLevel!
      let d' ← maybeCast 22 p? sort sort' (d'?.getD d.toPExpr)

      let us := us.push lvl
      withNewFVar 9 name d' bi fun id => do
        -- if id.fvarId.name == "_kernel_fresh.37".toName then
        --   dbg_trace s!"DBG[14]: TypeChecker.lean:1121: id={← callId}"
        let fvars := fvars.push (.fvar id)
        loop fvars us (domPatched || d'?.isSome || p?.isSome) body
    | e => do
      let e := e.instantiateRev fvars
      let (sort, e'?) ← inferType 18 e
      let (sort', p?) ← ensureSortCore sort e
      let lvl := sort'.toExpr.sortLevel!
      let e' ← maybeCast 23 p? sort sort' (e'?.getD e.toPExpr)

      let patch? ←
        if domPatched || e'?.isSome || p?.isSome then do

          let mut lets := #[]
          for fvar in fvars do
            let lets' : Array LocalDeclE ← getLets 1 fvar.fvarId!
            lets := lets.push $ lets'.map (·.toLocalDecl)
          -- let ret := ((← getLCtx).mkForall' (← letUseCount) newfvars e').toPExpr
          let ret := (expandLetsForall (← getLCtx) fvars lets e').toPExpr
          -- dbg_trace s!"DBG[15]: TypeChecker.lean:1139 (after let ret := {ret.toExpr.containsFVar' (.mk "_kernel_fresh.37".toName)}"
          pure $ .some ret
        else
          pure none
      return ((Expr.sort <| us.foldr mkLevelIMax' lvl ).toPExpr, patch?)

/--
Infers the type of application `e`, assuming that `e` is already well-typed.
-/
def inferApp (e : PExpr) : RecM PExpr := do
  e.toExpr.withApp fun f args => do
  let f := f.toPExpr
  let args := args.map (·.toPExpr)
  let mut fType ← inferTypePure 19 f
  let mut j := 0
  for i in [:args.size] do
    match fType.toExpr with
    | .forallE _ _ body _ =>
      fType := body.toPExpr
    | _ =>
      fType := fType.toExpr.instantiateRevRange j i args |>.toPExpr
      let fType' ← ensureForallCorePure fType e
      fType := fType'.toExpr.bindingBody!.toPExpr -- TODO ask on zulip about how to avoid this kind of double-casting
      j := i
  return fType.toExpr.instantiateRevRange j args.size args |>.toPExpr

/--
Infers the type of let-expression `e`.
-/
def inferLet (e : Expr) : RecPE := do
    let ret ← loop #[] false e
    pure ret
  where
    loop fvars typePatched : Expr → RecPE
    | .letE name type val body _ => do
      let type := type.instantiateRev fvars
      let (sort, type'?) ← inferType 20 type 
      let (sort', pType?) ← ensureSortCore sort type
      let type' ← maybeCast 16 pType? sort sort' (type'?.getD type.toPExpr)
      let val := val.instantiateRev fvars
      let (valType, val'?) ← inferType 21 val 
      let val' := val'?.getD val.toPExpr
      let ((true, pVal?), valC', _) ← smartCast' 17 valType type' val' |
        throw <| .letTypeMismatch (← getKEnv) (← getLCtx) name valType type'
      withNewLetVar 10 name type' valC' fun var => do
        let fvars := fvars.push (.fvar var)
        let ret ← loop fvars (typePatched || type'?.isSome || pType?.isSome || val'?.isSome || pVal?.isSome) body
        pure ret
    | e => do
      let e := (e.instantiateRev fvars)
      let (r, e'?) ← inferType 22 e
      let e' := e'?.getD e.toPExpr
      let r := r.toExpr.cheapBetaReduce.toPExpr

      let mut lets := #[]
      for fvar in fvars do
        let lets' : Array LocalDeclE ← getLets 1 fvar.fvarId!
        lets := lets.push $ lets'.map (·.toLocalDecl)
      let patch? ←
        if typePatched || e'?.isSome then do
          -- if lets.any fun l => l.fvarId.name == "_kernel_fresh.61".toName then
          --   dbg_trace s!"DBG[6]: TypeChecker.lean:1347 {fvars}"
          -- pure $ .some $ (← getLCtx).mkForall' (← letUseCount) newfvars e' |>.toPExpr -- TODO TODO
          pure $ .some $ (expandLetsForall (← getLCtx) fvars lets e') |>.toPExpr -- TODO TODO
        else
          pure none
      -- return ((← getLCtx).mkForall' (← letUseCount) newfvars r |>.toPExpr, patch?)
      return ((expandLetsForall (← getLCtx) fvars lets r) |>.toPExpr, patch?)

/--
Checks if the type of `e` is definitionally equal to `Prop`.
-/
def isPropPure (e : PExpr) : RecM Bool := do
  let t ← inferTypePure 23 e
  let t' ← whnfPure 24 t
  return t' == Expr.prop.toPExpr

/--
Infers the type of structure projection `e`.

FIXME: This does a lot of checking on the struct constructor type itself,
shouldn't that belong in Inductive/Add.lean instead?
-/
def inferProj (typeName : Name) (idx : Nat) (struct : PExpr) (patched : Bool) (structType : PExpr) : RecPE := do
  let e := Expr.proj typeName idx struct
  let (type, pType?) ← whnf 25 structType
  let mut struct := struct
  -- TODO if pType? := some _ then must cast struct
  type.toExpr.withApp fun I args => do
  let env ← getKEnv
  let fail {_} := do throw <| .invalidProj env (← getLCtx) e
  let .const I_name I_levels := I | fail
  if typeName != I_name then fail
  let .inductInfo I_val ← env.get I_name | fail
  let [c] := I_val.ctors | fail
  if args.size != I_val.numParams + I_val.numIndices then fail
  let c_info ← env.get c
  let mut r := c_info.instantiateTypeLevelParams I_levels |>.toPExpr
  for i in [:I_val.numParams] do
    let .mk (.forallE _ _ b _) ← whnfPure 26 r | fail -- FIXME use ensureForall?
    r := b.instantiate1 args[i]! |>.toPExpr
  let isPropType := ← isPropPure type
  for i in [:idx] do
    let .mk (.forallE _ dom b _) ← whnfPure 27 r | fail -- FIXME use ensureForall?
    if b.hasLooseBVars then
      -- prop structs cannot have non-prop dependent fields
      let isPropDom ← isPropPure dom.toPExpr
      if isPropType then if !isPropDom then fail
      r := b.instantiate1 (.proj I_name i struct) |>.toPExpr
    else
      r := b.toPExpr
  let (.mk (.forallE _ dom _ _)) ← whnfPure 28 r | fail -- FIXME use ensureForall?
  let isPropDom ← isPropPure dom.toPExpr
  if isPropType then if !isPropDom then fail
  let patched := patched || pType?.isSome
  let patch := if patched then some (Expr.proj typeName idx struct).toPExpr else none
  return (dom.toPExpr, patch)

@[inherit_doc inferType]
def inferType' (e : Expr) (_dbg := false) : RecPE := do
  if e.isBVar then
    throw <| .other
      s!"patcher does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert 5 $ !e.hasLooseBVars
  let state ← get
  if let some r := state.inferTypeC[e]? then
    return r
  let (r, ep?) ← match e with
    | .lit l => pure (l.type.toPExpr, none)
    | .mdata _ e => inferType'  e
    -- | .mdata _ e => inferType 95 e
    | .proj s idx e =>
      let (t, e'?) ← inferType' e
      -- let (t, e'?) ← inferType 96 e
      let e' := e'?.getD e.toPExpr
      inferProj s idx e' e'?.isSome t
    | .fvar n => pure (← inferFVar (← get) n ((← get).fvarRegistry.get? n.name), none)
    | .mvar _ => throw <| .other "patcher does not support meta variables"
    | .bvar _ => throw $ .other "unreachable 1"
    | .sort l =>
      checkLevel (← readThe Context) l
      pure <| (Expr.sort (.succ l) |>.toPExpr, none)
    | .const c ls => pure (← inferConstant (← readThe Context) c ls, none)
    | .lam .. => inferLambda e false
    | .forallE .. => inferForall e
    | .app f a =>
      let (fType, f'?) ← inferType' f
      -- let (fType, f'?) ← inferType 97 f
      let (fType', pf'?) ← ensureForallCore fType f
      let f' ← maybeCast 18 pf'? fType fType' (f'?.getD f.toPExpr)
      -- if (← readThe Context).const == `eq_of_heq' then if let .lam _ (.const `Ty _) _ _ := a then

      let (aType, a'?) ← inferType' a
      -- let (aType, a'?) ← inferType 98 a
      -- _ ← inferTypePure 5001 fType -- sanity check
      -- _ ← inferTypePure 5000 aType

      let dType := Expr.bindingDomain! fType' |>.toPExpr
      -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
      -- for some universe level `l`, so this use of `isDefEq` is valid
      let ((true, pa'?), a', _) ← smartCast' 19 aType dType (a'?.getD a.toPExpr) |
        -- if e'.isApp then if let .const `Bool.casesOn _ := e'.withApp fun f _ => f then
        -- dbg_trace s!"dbg: {(← whnf 0 dType.toExpr.getAppArgs[2]!.toPExpr).1} {(← whnf 0 aType.toExpr.getAppArgs[2]!.toPExpr).1}"
        throw <| .appTypeMismatch (← getKEnv) (← getLCtx) e fType' aType

      let patch := if f'?.isSome || a'?.isSome || pf'?.isSome || pa'?.isSome then .some (Expr.app f' a').toPExpr else none
      pure ((Expr.bindingBody! fType').instantiate1 a' |>.toPExpr, patch)
    | .letE .. => inferLet e
  modify fun s => { s with inferTypeC := s.inferTypeC.insert e (r, ep?) }
  return (r, ep?)

/--
Reduces `e` to its weak-head normal form, without unfolding definitions. This
is a conservative version of `whnf` (which does unfold definitions), to be used
for efficiency purposes.

Setting `cheapK` or `cheapProj` to `true` will cause the major premise/struct
argument to be reduced "lazily" (using `whnfCore` rather than `whnf`) when
reducing recursor applications/struct projections. This can be a useful
optimization if we're checking the definitional equality of two recursor
applications/struct projections of the same recursor/projection, where we
might save some work by directly checking if the major premises/struct
arguments are defeq (rather than eagerly applying a recursor rule/projection).
-/
def whnfCore (n : Nat) (e : PExpr) (cheapK := false) (cheapProj := false) : RecEE := fun m => do
  let ret ← m.whnfCore n e cheapK cheapProj
  pure ret

/--
Gets the weak-head normal form of the free variable `e`,
which is the weak-head normal form of its definition if `e` is a let variable and itself if it is a lambda variable.
-/
def whnfFVar (e : PExpr) (cheapK : Bool) (cheapProj : Bool) : RecEE := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.toExpr.fvarId! then
    return ← whnfCore 29 v.toPExpr cheapK cheapProj
  return (e, none)

def appProjThm? (structName : Name) (projIdx : Nat) (struct structN : PExpr) (structEqstructN? : Option EExpr) : RecM (Option EExpr) := do
  structEqstructN?.mapM fun _ => do
    let env ← getKEnv
    let structNType ← whnfPure 30 (← inferTypePure 31 structN)
    let structType ← whnfPure 32 (← inferTypePure 33 struct)
    let structTypeC := if structType.toExpr.isApp then structType.toExpr.withApp fun f _ => f else structType.toExpr
    let .const typeC lvls := structTypeC | unreachable!
    let .inductInfo {numParams, numIndices, type, levelParams, ..} ← env.get typeC | unreachable!
    let type := type.instantiateLevelParams levelParams lvls
    assert! numIndices == 0
    let paramsN := structNType.toExpr.getAppArgs
    let params := structType.toExpr.getAppArgs

    let rec loop remType (paramVars : Array Expr) n := do
      match (← whnfPure 34 remType.toPExpr).toExpr, n with
      | .forallE n d b i, m + 1 =>
        withNewFVar 11 n d.toPExpr i fun idr => do
          let rVar := (.fvar idr)
          let remCtorType := b.instantiate1 rVar
          let paramVars := paramVars.push rVar
          loop remCtorType paramVars m
      | _, 0 =>
        let structType := Lean.mkAppN structTypeC paramVars
        withNewFVar 12 default structType.toPExpr default fun ids => do
          let s := Expr.fvar ids

          let f := (← getLCtx).mkLambda (paramVars ++ #[s]) (.proj structName projIdx s) |>.toPExpr
          let mut targsEqsargs? := default
          targsEqsargs? := targsEqsargs?.insert numParams structEqstructN?
          let (true, ret?) ← isDefEqApp 3 (Lean.mkAppN f (params ++ #[struct.toExpr])).toPExpr (Lean.mkAppN f (paramsN ++ #[structN.toExpr])).toPExpr targsEqsargs? (some none) |
            -- dbg_trace s!"DBG[20]: TypeChecker.lean:1401 {← params.zip paramsN |>.mapM fun (p, pN) => do isDefEqLean p pN}"
            -- let (p, pN) := params.zip paramsN |>.get! 3
            -- let pT ← inferTypeLean 0 p
            -- let pNT ← inferTypeLean 0 pN
            -- dbg_trace s!"DBG[20]: TypeChecker.lean:1401 {(← isDefEqLean p pN)}\n\n {← whnfLean p}\n\n {← whnfLean pN}\n\n{pT}\n\n{pNT}\n\n{← inferTypeLean 0 pT}\n\n{← inferTypeLean 0 pNT} {← isValidApp 0 structNType}"
            -- dbg_trace s!"DBG[20]: TypeChecker.lean:1401 {← isValidApp 0 structType}"
            -- dbg_trace s!"DBG[20]: TypeChecker.lean:1401 {← isValidApp 0 structNType}"
            throw $ .other "appProjThm? failed"

          pure $ ret?.get!
      | _, _ => unreachable!

    loop type #[] numParams

/--
Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a
constructor application).
-/
def reduceProj (structName : Name) (projIdx : Nat) (struct : PExpr) (cheapK : Bool) (cheapProj : Bool) : RecM (Option (PExpr × Option EExpr)) := do
  let mut (structN, structEqc?) ← (if cheapProj then whnfCore 35 struct cheapK cheapProj else whnf 305 struct (cheapK := cheapK))
  -- if structEqc?.isNone then
  --   if not (← isDefEqPure 0 struct structN) then
  --     throw $ .other s!"reduceProj failed sanity check {(← get).numCalls}"

  -- -- TODO is this necessary? can we assume the type of c and struct are the same?
  -- -- if not, we will need to use a different patch theorem
  -- let cType ← inferTypePure c
  -- let (.true, cTypeEqstructType?) ← isDefEq cType structType | throw $ .other "unreachable 2"
  -- c ← maybeCast cTypeEqstructType? lvl cType structType c 

  if let (.lit (.strVal s)) := structN.toExpr then
    structN := Expr.strLitToConstructor s |>.toPExpr

  structN.toExpr.withApp fun mk args => do
    let .const mkC _ := mk | return none
    let .ctorInfo mkCtorInfo ← (← getKEnv).get mkC | return none
    let projstructEqprojstructN? ← appProjThm? structName projIdx struct structN structEqc?

    return args[mkCtorInfo.numParams + projIdx]?.map (·.toPExpr, projstructEqprojstructN?)

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

/--
Checks if `e` has a head constant that can be delta-reduced (that is, it is a
theorem or definition), returning its `ConstantInfo` if so.
-/
def isDelta (env : Kernel.Environment) (e : PExpr) : Option ConstantInfo := do
  if let .const c _ := e.toExpr.getAppFn then
    -- if c != `L4L.eq_of_heq then -- TODO have to block all of the patch theorems?
    if let some ci := env.find? c then
      if ci.hasValue then
        return ci
  none

/--
Checks if `e` has a head constant that can be delta-reduced (that is, it is a
theorem or definition), returning its value (instantiated by level parameters)
if so.
-/
def unfoldDefinitionCore (env : Kernel.Environment) (e : PExpr) : Option PExpr := do
  if let .const _ ls := e.toExpr then
    if let some d := isDelta env e then
      if ls.length == d.numLevelParams then
        -- can assume that any constant value added to the environment has been patched
        return d.instantiateValueLevelParams! ls |>.toPExpr
  none

/--
Unfolds the definition at the head of the application `e` (or `e` itself if it
is not an application).
-/
def unfoldDefinition (env : Kernel.Environment) (e : PExpr) : Option PExpr := do
  if e.toExpr.isApp then
    let f0 := e.toExpr.getAppFn
    if let some f := unfoldDefinitionCore env f0.toPExpr then
      let rargs := e.toExpr.getAppRevArgs
      return f.toExpr.mkAppRevRange 0 rargs.size rargs |>.toPExpr
    none
  else
    unfoldDefinitionCore env e

def reduceNative (_env : Kernel.Environment) (e : PExpr) : Except KernelException (Option (PExpr × Option EExpr)) := do
  let .app f (.const c _) := e.toExpr | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

-- def mkRefl (lvl : Level) (T : PExpr) (t : PExpr) : RecM EExpr := do
--   pure $ Lean.mkAppN (← getConst `Eq.refl [lvl]) #[T, t] |>.toEExprD

def natLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

/--
  Threshold above which a primitive `Nat` operation result/operand is deemed infeasible to
  re-check in Dedukti (which lacks native `Nat` arithmetic and would expand the value into a
  unary `Nat.succ` chain). Constants whose kernel check performs such an operation are aborted
  here and stubbed in the lean2dk output.
-/
def natPrimOpStubThreshold : Nat := 65536

/--
Reduces the application `f a b` to a Nat literal if `a` and `b` can be reduced
to Nat literals.

Note: `f` should have an (efficient) external implementation.
-/
def reduceBinNatOp (op : Name) (f : Nat → Nat → Nat) (a b : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  let (a', pa?) := (← whnf 36 a)
  let (b', pb?) := (← whnf 37 b)
  let some v1 := natLitExt? a' | return none
  let some v2 := natLitExt? b' | return none
  -- Dedukti has no primitive `Nat` arithmetic, so it would reduce a result this large to an
  -- infeasible unary `Nat.succ` chain (e.g. `UInt32.size = 2^32`). Abort here so the enclosing
  -- constant is recorded as aborted and stubbed (declared without its rewrite rule) in the output.
  if f v1 v2 > natPrimOpStubThreshold then throw $ .other "large nat prim op"
  let nat := (Expr.const `Nat []).toPExpr
  let mut (true, appEqapp'?) ← do
      let fab := Lean.mkAppN (.const op []) #[a, b] |>.toPExpr
      let fab' := Lean.mkAppN (.const op []) #[a', b'] |>.toPExpr
      let mut targsEqsargs? := default
      targsEqsargs? := targsEqsargs?.insert 0 pa?
      targsEqsargs? := targsEqsargs?.insert 1 pb?
      isDefEqApp 9901 fab fab' (targsEqsargs? := targsEqsargs?) (tfEqsf? := some none)
    | throw $ .other "reduceBinNatOp error"
  let result := (Expr.lit <| .natVal <| f v1 v2).toPExpr
  let app := Lean.mkAppN (.const op []) #[a, b] |>.toPExpr
  let app' := Lean.mkAppN (.const op []) #[a', b'] |>.toPExpr
  let sorryProof? ← if op == `Nat.gcd && (← readThe Context).opts.kLikeReduction then
      dbg_trace s!"dbg: GCD used: {v1} {v2}"
      pure $ .some $ .sry {u := 1, A := nat, a := a', B := nat, b := b'}
    else 
      pure none
  let ret? ← appHEqTrans? app app' result appEqapp'? sorryProof?

  return some <| (result, ret?)

/--
Reduces the application `f a b` to a boolean expression if `a` and `b` can be
reduced to Nat literals.

Note: `f` should have an (efficient) external implementation.
-/
def reduceBinNatPred (op : Name) (f : Nat → Nat → Bool) (a b : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  let (a', pa?) := (← whnf 38 a)
  let (b', pb?) := (← whnf 39 b)
  let some v1 := natLitExt? a' | return none
  let some v2 := natLitExt? b' | return none
  -- See `reduceBinNatOp`: a comparison on operands this large is infeasible for Dedukti.
  if v1 > natPrimOpStubThreshold || v2 > natPrimOpStubThreshold then throw $ .other "large nat prim op"
  let (true, ret?) ← do
      let fab := Lean.mkAppN (.const op []) #[a, b] |>.toPExpr
      let fab' := Lean.mkAppN (.const op []) #[a', b'] |>.toPExpr
      let mut targsEqsargs? := default
      targsEqsargs? := targsEqsargs?.insert 0 pa?
      targsEqsargs? := targsEqsargs?.insert 1 pb?
      isDefEqApp 9902 fab fab' (targsEqsargs? := targsEqsargs?) (tfEqsf? := some none)
    | throw $ .other "reduceBinNatPred error"
  return (toExpr (f v1 v2) |>.toPExpr, ret?)

def mkNatSuccAppArgHEq? (p? : Option EExpr) (t s : PExpr) : RecM (Option EExpr) := do
  p?.mapM fun p => do
    let extra := .Arg {b := s, aEqb := p}
    let N := Expr.const `Nat [] |>.toPExpr
    pure $ .app {u := .succ .zero, v := .succ .zero, A := N, U := (N, default), f := (Expr.const `Nat.succ []).toPExpr, a := t, extra}
    -- pure $ (mkAppN (← getConst `L4L.appArgHEq [.succ .zero, .succ .zero]) #[.const `Nat [], --FIXME
    -- .const `Nat [], .const `Nat.succ [], t, s, p.toExpr]).toEExpr

/--
Reduces `e` to a natural number literal if possible, where binary operations
and predicates may be applied (provided they have an external implementation).
These include: `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`,
`Nat.mod`, `Nat.div`, `Nat.beq`, `Nat.ble`.
-/
def reduceNat (e : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  if e.toExpr.hasFVar then return none
  let nargs := e.toExpr.getAppNumArgs
  if nargs == 1 then
    let f := e.toExpr.appFn!
    if f == .const ``Nat.succ [] then
      let prec := e.toExpr.appArg!.toPExpr
      let (prec', p?) ← whnf 40 prec
      let some v := natLitExt? prec' | return none
      return some <| ((Expr.lit <| .natVal <| v + 1).toPExpr, ← mkNatSuccAppArgHEq? p? prec prec')
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e.toExpr | return none
    if f == ``Nat.add then return ← reduceBinNatOp ``Nat.add Nat.add a.toPExpr b.toPExpr
    if f == ``Nat.sub then return ← reduceBinNatOp ``Nat.sub Nat.sub a.toPExpr b.toPExpr
    if f == ``Nat.mul then return ← reduceBinNatOp ``Nat.mul Nat.mul a.toPExpr b.toPExpr
    if f == ``Nat.pow then return ← reduceBinNatOp ``Nat.pow Nat.pow a.toPExpr b.toPExpr
    if f == ``Nat.gcd then 
      unless (← readThe Context).opts.kLikeReduction do return ← reduceBinNatOp ``Nat.gcd Nat.gcd a.toPExpr b.toPExpr
      let (a', _) := (← whnf 36 a.toPExpr)
      let (b', _) := (← whnf 37 b.toPExpr)
      let abort :=
        throw $ .other "translation aborted"
      let some v1 := natLitExt? a' | return none
      let some v2 := natLitExt? b' | return none
      if v1 > 300 || v2 > 300 then
        abort
      -- trace s!"dbg: GCD averted: {natLitExt? (← whnf 0 a.toPExpr).1} {natLitExt? (← whnf 0 a.toPExpr).1}"
      return none
      -- return ← reduceBinNatOp ``Nat.gcd Nat.gcd a.toPExpr b.toPExpr
    if f == ``Nat.mod then return ← reduceBinNatOp ``Nat.mod Nat.mod a.toPExpr b.toPExpr
    if f == ``Nat.div then return ← reduceBinNatOp ``Nat.div Nat.div a.toPExpr b.toPExpr
    if f == ``Nat.beq then return ← reduceBinNatPred ``Nat.beq Nat.beq a.toPExpr b.toPExpr
    if f == ``Nat.ble then return ← reduceBinNatPred ``Nat.ble Nat.ble a.toPExpr b.toPExpr
  return none


def isDefEqFVar (idt ids : FVarId) : RecLB := do
  if let some d := (← readThe Context).eqFVars.get? (idt, ids) then
    return (.true, some $ .fvar d)
  else if let some d := (← readThe Context).eqFVars.get? (ids, idt) then
    return (.true, some $ .rev $ .fvar d)
  return (.undef, none)

/--
If `t` and `s` have matching head constructors and are not projections or
(non-α-equivalent) applications, checks that they are definitionally equal.
Otherwise, defers to the calling function.
-/
def quickIsDefEq' (t s : PExpr) (useHash := false) : RecLB := do
  -- optimization for terms that are already α-equivalent
  if ← modifyGet fun (.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 (eqvManager := m)) => -- TODO why do I have to list these?
    let (b, m) := m.isEquiv useHash t s
    (b, .mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 (eqvManager := m))
  then
    return (.true, none)
  let res : Option (Bool × PExpr) ← match t.toExpr, s.toExpr with
  | .lam .., .lam .. => pure $ some $ ← isDefEqLambda t s
  | .fvar idt, .fvar ids =>
    match ← isDefEqFVar idt ids with
    | (.undef, _) => pure none
    | (.true, p?) => pure (true, p?)
    | (.false, p?) => pure (false, p?)
  | .forallE .., .forallE .. => pure $ some $ ← isDefEqForallOpt t s
  | .sort a1, .sort a2 => pure $ some $ ((a1.isEquiv a2), none)
  | .mdata _ a1, .mdata _ a2 => pure $ some $ ← isDefEq 44 a1.toPExpr a2.toPExpr
  | .mvar .., .mvar .. => throw $ .other "unreachable 6"
  | .lit a1, .lit a2 => pure $ some ((a1 == a2), none)
  | _, _ => pure none
  let some (defeq, p?) := res | return (.undef, none)
  pure (defeq.toLBool, p?)

/--
Checks if `t` and `s` are defeq after applying η-expansion to `s`.

Assuming that `s` has a function type `(x : A) -> B x`, it η-expands to
`fun (x : A) => s x` (which it is definitionally equal to by the η rule).
-/
def tryEtaExpansionCore (t s : PExpr) : RecB := do
  if t.toExpr.isLambda && !s.toExpr.isLambda then
    let .forallE name ty _ bi := (← whnfPure 45 (← inferTypePure 46 s)).toExpr | return (false, none)
    isDefEq 47 t (Expr.lam name ty (.app s (.bvar 0)) bi).toPExpr -- NOTE: same proof should be okay because of eta-expansion when typechecking
  else return (false, none)

@[inherit_doc tryEtaExpansionCore]
def tryEtaExpansion (t s : PExpr) : RecB := do
  match ← tryEtaExpansionCore t s with
  | ret@(true, _) => pure ret 
  | (false, _) => 
    let (true, sEqt?) ← tryEtaExpansionCore s t | return (false, none)
    return (true, ← appHEqSymm? sEqt?)

/--
Checks if `t` and `s` are application-defeq (as in `isDefEqApp`)
after applying struct-η-expansion to `t`.

Assuming that `s` has a struct type `S` constructor `S.mk` and projection
functions `pᵢ : S → Tᵢ`, it struct-η-expands to `S.mk (p₁ s) ... (pₙ s)` (which
it is definitionally equal to by the struct-η rule).
-/
def tryEtaStructCore (t s : PExpr) : RecB := do
  let ctor := s.toExpr.getAppFn
  let .const f _ := ctor | return (false, none)
  let env ← getKEnv
  let .ctorInfo fInfo ← env.get f | return (false, none)
  unless s.toExpr.getAppNumArgs == fInfo.numParams + fInfo.numFields do return (false, none)
  unless isStructureLike' env fInfo.induct do return (false, none)
  unless ← isDefEqPure 48 (← inferTypePure 49 t) (← inferTypePure 50 s) do return (false, none)
  let args := s.toExpr.getAppArgs
  let mut exptE := ctor
  for i in [:fInfo.numParams] do
    exptE := mkApp exptE (args[i]!)
  for i in [fInfo.numParams:args.size] do
    exptE := mkApp exptE (.proj fInfo.induct (i - fInfo.numParams) t)
  let expt := exptE.toPExpr
  
  let tEqexpt? := none -- TODO use proof here to eliminate struct eta
  let (true, exptEqs?) ← isDefEqApp 4 expt s | return (false, none) -- TODO eliminate struct eta
  return (true, ← appHEqTrans? t expt s tEqexpt? exptEqs?)

@[inherit_doc tryEtaStructCore]
def tryEtaStruct (t s : PExpr) : RecB := do
  match ← tryEtaStructCore t s with
  | ret@(true, _) => pure ret
  | (false, _) =>
    let (true, sEqt?) ← tryEtaStructCore s t | return (false, none)
    return (true, ← appHEqSymm? sEqt?)

def reduceRecursor (e : PExpr) (cheapK : Bool) : RecM (Option (PExpr × Option EExpr)) := do
  let env ← getKEnv
  if env.quotInit then
    if let some r ← quotReduceRec methsR e then
      -- _ ← inferTypePure 6001 r.1 -- sanity check TODO remove
      return r
  let whnf' := whnf (cheapK := cheapK)
  let meths := {methsR with whnf := whnf'}
  let recReduced? ← inductiveReduceRec meths (cheapK := cheapK) env e
  if let some r := recReduced? then
    return r
  return none

@[inherit_doc whnfCore]
private def _whnfCore' (_e : Expr) (cheapK := false) (cheapProj := false) : RecEE := do
  -- TODO whnfPure optimization
  let e := _e.toPExpr
  match _e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return (e, none)
  | .mdata _ e => 
    return ← _whnfCore' e cheapK cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return (e, none)
  | .app .. | .letE .. | .proj .. => pure ()
  if not (← readThe Context).noCache then
    if let some (e', eEqe'?) := (← get).whnfCoreCache.get? e then -- FIXME important to optimize this -- FIXME should this depend on cheapK?
      let eEqe'? ←
        if let some (lv, decl, lastVar?) := eEqe'? then
          if not ((← getLCtx).containsFVar (Expr.fvar decl.fvarId)) then
            addLVarToCtx decl lastVar?
          pure $ .some lv
        else
          pure none
      return (e', eEqe'?)
  let rec save r := do
    let (e', p?) := r
    if !cheapK && !cheapProj then
      let cacheData? ← p?.mapM fun p => do
        let (lv, decl, lastVar?) ← mkLetE e e' p 103
        pure (lv, decl, lastVar?.map (·.1))
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e (e', cacheData?) }
      -- if cheapK && r.2.isNone then
      --   modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    pure r
  let ret ← match _e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => throw $ .other "unreachable 9"
  | .fvar _ => return ← whnfFVar e cheapK cheapProj
  | .app .. => -- beta-reduce at the head as much as possible, apply any remaining `rargs` to the resulting expression, and re-run `whnfCore`
    _e.withAppRev fun f0 rargs => do
    let f0 := f0.toPExpr
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let (f, pf0Eqf?) ← whnfCore 52 f0 cheapK cheapProj
    let frargs := f.toExpr.mkAppRevRange 0 rargs.size rargs |>.toPExpr

    let (frargs', rargs', eEqfrargs'?) ←
      if f0 != f then -- the type may have changed, even if pf0Eqf? is none FIXME ?
        let f0T ← inferTypePure 91 f0
        let fT ← inferTypePure 92 f
        -- if ! (← isValidApp 0 frargs) then
        if ! (← isDefEqPure 93 f0T fT) then
          -- patch to cast rargs as necessary to agree with type of f
          let args := rargs.reverse
          let d? ← dbg_wrap 9911 $ replaceFType methsR f0T fT args
          let args' := d?.map (·.1)
          let mut argsEqargs'? := default
          let frargs' := Lean.mkAppN f args' |>.toPExpr
          let mut i := 0
          for (_, p?) in d? do
            argsEqargs'? := argsEqargs'?.insert i p?
            i := i + 1
          -- let rargs' := frargs'.toExpr.getAppArgs[f.toExpr.getAppArgs.size:].toArray.reverse
          assert 10 $ args'.size == rargs.size
          let (.true, data?) ← dbg_wrap 9909 $ isDefEqApp'' f0 f (args.map (·.toPExpr)) (args'.map (·.toPExpr)) (tfEqsf? := pf0Eqf?) (targsEqsargs? := argsEqargs'?) |
            throw $ .other "unreachable 10"
          let eEqfrargs'? := data?.map (·.1)
          pure (frargs', args'.reverse, eEqfrargs'?)
        else
          let mut m := default
          for i in [:rargs.size] do
            m := m.insert i none
          let (.true, data?) ← dbg_wrap 9910 $ isDefEqApp'' f0 f (rargs.map (·.toPExpr)).reverse (rargs.map (·.toPExpr)).reverse (tfEqsf? := pf0Eqf?) (targsEqsargs? := m)|
            throw $ .other "unreachable 10"
          let eEqfrargs'? := data?.map (·.1)
          pure (frargs, rargs, eEqfrargs'?)
      else
        pure (frargs, rargs, none)

    if let (.lam _ _ body _) := f.toExpr then
      -- if e'.isApp then if let .const `Bool.casesOn _ := e'.withApp fun f _ => f then
      let rec loop m (f : Expr) : RecEE :=
        let cont := do
          let r := f.instantiateRange (rargs'.size - m) rargs'.size rargs'
          let r := r.mkAppRevRange 0 (rargs'.size - m) rargs' |>.toPExpr
          let (r', rEqr'?) ← whnfCore 54 r cheapK cheapProj
          let eEqr'? ← appHEqTrans? e frargs' r' eEqfrargs'? rEqr'?
          save (r', eEqr'?)
        if let .lam _ _ body _ := f then
          if m < rargs'.size then loop (m + 1) body
          else cont
        else cont
      loop 1 body
    else if f == f0 then
      if let some (r, eEqr?) ← reduceRecursor e cheapK then
        let (r', rEqr'?) ← whnfCore 55 r cheapK cheapProj
        let eEqr'? ← appHEqTrans? e r r' eEqr? rEqr'?
        pure (r', eEqr'?)
      else
        pure (e, none)
    else
      -- FIXME replace with reduceRecursor? adding arguments can only result in further normalization if the head reduced to a partial recursor application
      let (r', frargsEqr'?) ← whnfCore 56 frargs' cheapK cheapProj
      let eEqr'? ← appHEqTrans? e frargs' r' eEqfrargs'? frargsEqr'?
      save (r', eEqr'?)
  | .letE _ _ val body _ =>
    save <|← whnfCore 57 (body.instantiate1 val).toPExpr cheapK cheapProj
  | .proj typeName idx s =>
    if let some (m, eEqm?) ← reduceProj typeName idx s.toPExpr cheapK cheapProj then
      let (r', mEqr'?) ← whnfCore 58 m cheapK cheapProj
      let eEqr'? ← appHEqTrans? e m r' eEqm? mEqr'?
      save (r', eEqr'?)
    else
      save (e, none)
  -- let (eNew, p?) := ret
  -- if p?.isNone then
  --   if not (← isDefEqPure 0 eNew e) then
  --     throw $ .other s!"whnfCore failed sanity check 3 {(← readThe Context).callId} {e'.ctorName}"
  pure ret

@[inherit_doc whnfCore]
def whnfCore' (e : PExpr) (cheapK := false) (cheapProj := false) : RecEE := do
  let ret ← _whnfCore' e cheapK cheapProj
  pure ret

@[inherit_doc whnf]
private def _whnf' (_e : Expr) (cheapK := false) : RecEE := do
  let e := _e.toPExpr
  -- Do not cache easy cases
  match _e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return (e, none)
  | .mdata _ e => return ← _whnf' e (cheapK := cheapK)
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return (e, none)
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache
  if not (← readThe Context).noCache then
    if let some (e', eEqe'?) := (← get).whnfCache.get? (e, cheapK) then
      let eEqe'? ←
        if let some (lv, decl, lastVar?) := eEqe'? then
          if not ((← getLCtx).containsFVar (Expr.fvar decl.fvarId)) then
            addLVarToCtx decl lastVar?
          pure $ .some lv
        else
          pure none
      return (e', eEqe'?)
  let rec loop le eEqle?
  | 0 =>
    throw .deterministicTimeout
  | fuel+1 => do
    let env ← getKEnv
    let (ler, leEqler?) ← whnfCore' le (cheapK := cheapK)
    let eEqler? ← appHEqTrans? e le ler eEqle? leEqler?
    if let some (ler', lerEqler'?) ← reduceNative env ler then return (ler', ← appHEqTrans? e ler ler' eEqler? lerEqler'?)
    if let some (ler', lerEqler'?) ← reduceNat ler then return (ler', ← appHEqTrans? e ler ler' eEqler? lerEqler'?)
    let some leru := unfoldDefinition env ler | return (ler, eEqler?)
    loop leru eEqler? fuel
  let r ← loop e none 1000
  let (e', p?) := r
  let cacheData? ← p?.mapM fun p => do
    let (lv, decl, lastVar?) ← mkLetE e e' p 101
    pure (lv, decl, lastVar?.map (·.1))
  modify fun s => { s with whnfCache := s.whnfCache.insert (e, cheapK) (e', cacheData?) }
  return r

@[inherit_doc whnf]
def whnf' (e : PExpr) (cheapK := false) : RecEE := _whnf' e (cheapK := cheapK)

def whnfPure' (e : PExpr) : RecM PExpr := do
  let leanMinusWhnf ← runLeanMinus $ Lean.TypeChecker.whnf e.toExpr
  pure leanMinusWhnf.toPExpr

/--
Checks if `t` and `s` are definitionally equivalent according to proof irrelevance
(that is, they are proofs of the same proposition).
-/
def isDefEqProofIrrel (t s : PExpr) : RecLB := do
  -- if ← shouldTrace then
  --   dbg_trace s!"HERE: {t.toExpr.containsFVar' (.mk "_kernel_fresh.15280".toName)}"
    -- let x ← withL4LTrace $ runLeanMinusRecM $ Lean.TypeChecker.inferTypeCheck t
  let tType ← inferTypePure 59 t
  let prop ← isPropPure tType
  if !prop then return (.undef, none)
  let sType ← inferTypePure 60 s
  -- let (ret, usesPI) ← usesPrfIrrel tType sType
  let (ret, pt?) ← isDefEq 61 tType sType
  if ret then
    if (← readThe Context).opts.proofIrrelevance then
      let tEqs? ←
        isDefEqProofIrrel' t s tType sType pt? 1
      pure (.true, tEqs?)
    else
      pure (.true, none)
  else
    pure (.false, none)

def failedBefore (failure : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    failure.contains (t, s)
  else if t.hash > s.hash then
    failure.contains (s, t)
  else
    failure.contains (t, s) || failure.contains (s, t)

def cacheFailure (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with failure := st.failure.insert k }

def tryUnfoldProjApp (e : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  let f := e.toExpr.getAppFn
  if !f.isProj then return none
  let (e', p?) ← whnfCore 62 e (cheapK := true) (cheapProj := true)
  return if e' != e then (e', p?) else none

/--
Performs a single step of δ-reduction on `tn`, `sn`, or both (according to
optimizations) followed by weak-head normalization (without further
δ-reduction). If the resulting terms have matching head constructors (excluding
non-α-equivalent applications and projections), or are applications with the
same function head and defeq args, returns whether `tn` and `sn` are defeq.
Otherwise, a return value indicates to the calling `lazyDeltaReduction` that
δ-reduction is to be continued.

If δ-reduction+weak-head-normalization cannot be continued (i.e. we have a
weak-head normal form (with cheapProj := true)), defers further defeq-checking
to `isDefEq`.
-/
def lazyDeltaReductionStep (ltn lsn : PExpr) : RecM ReductionStatus := do
  -- if (← callId) > 384  && ! (← shouldTrace) then
  --   if ltn.toExpr.containsFVar' (.mk "_kernel_fresh.37".toName) || lsn.toExpr.containsFVar' (.mk "_kernel_fresh.37".toName) then 
  --     throw $ .other "HERE A"
  let env ← getKEnv
  let delta e := do
    let (ne, eEqne?) ← whnfCore 63 (unfoldDefinition env e).get! (cheapK := true) (cheapProj := true)
    -- if ne.toExpr.containsFVar' (.mk "_kernel_fresh.86".toName) then 
    --   dbg_trace s!"DBG[44]: TypeChecker.lean:1997 (after if ! e.toExpr.containsFVar (.mk _kernel_…)"
    --   for var in ← getLCtx do
    --     match var with
    --     | .cdecl (fvarId := id) (type := type) .. => dbg_trace s!"DBG[A]: {id.name}, {type.containsFVar' (.mk "_kernel_fresh.37".toName)}"
    --     | .ldecl (fvarId := id) (type := type) (value := value) .. => dbg_trace s!"DBG[B]: {id.name}, {type.containsFVar' (.mk "_kernel_fresh.37".toName)} {value.containsFVar' (.mk "_kernel_fresh.37".toName)}"
    --   withNoCache do
    --     dbg_trace s!"DBG[1]: TypeChecker.lean:1932 {(unfoldDefinition env e).get!}"
    --   throw $ .other s!"HERE X"
    pure (ne, eEqne?)
  let cont (nltn nlsn : PExpr) (pltnEqnltn? plsnEqnlsn? : Option EExpr) := do
    match ← quickIsDefEq 90 nltn nlsn with
    | (.undef, _) =>
      pure $ .continue nltn nlsn pltnEqnltn? plsnEqnlsn?
    | (.true, pnltnEqnlsn?) => do
      pure $ .bool .true (← appHEqTrans? ltn nltn lsn pltnEqnltn? <| ← appHEqTrans? nltn nlsn lsn pnltnEqnlsn? <| ← appHEqSymm? plsnEqnlsn?)
    | (.false, _) => pure $ .bool false none
  let deltaCont_t := do
    pure () -- FIXME why is this needed to block `delta` below from being run immediately in the outer monad context?
    let (nltn, pltnEqnltn?) ← delta ltn
    -- if pltnEqnltn?.isNone then
    --   if not (← isDefEqPure 0 ltn nltn) then
    --     throw $ .other "lazyDeltaReduction failed sanity check 3"
    let ret ← cont nltn lsn pltnEqnltn? none
    pure ret
  let deltaCont_s := do
    pure ()
    let (nlsn, plsnEqnlsn?) ← delta lsn
    -- if plsnEqnlsn?.isNone then
    --   if not (← isDefEqPure 0 lsn nlsn) then
    --     throw $ .other "lazyDeltaReduction failed sanity check 4"
    cont ltn nlsn none plsnEqnlsn?
  let deltaCont_both := do
    pure ()
    let (nltn, pltnEqnltn?) ← delta ltn
    let (nlsn, plsnEqnlsn?) ← delta lsn
    -- if pltnEqnltn?.isNone then
    --   if not (← isDefEqPure 0 ltn nltn) then
    --     throw $ .other "lazyDeltaReduction failed sanity check 5"
    -- if plsnEqnlsn?.isNone then
    --   if not (← isDefEqPure 0 lsn nlsn) then
    --     throw $ .other s!"lazyDeltaReduction failed sanity check 6 {(← get).numCalls}"
    cont nltn nlsn pltnEqnltn? plsnEqnlsn?
  match isDelta env ltn, isDelta env lsn with
  | none, none =>
    return .notDelta
  | some _, none =>
    -- FIXME hasn't whnfCore already been called on sn? so when would this case arise?
    if let some (nlsn, plsnEqnlsn?) ← tryUnfoldProjApp lsn then
      cont ltn nlsn none plsnEqnlsn?
    else
      deltaCont_t
  | none, some _ =>
    if let some (nltn, pltnEqnltn?) ← tryUnfoldProjApp ltn then
      cont nltn lsn pltnEqnltn? none
    else
      deltaCont_s
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt' hs then
      deltaCont_s
    else if hs.lt' ht then
      deltaCont_t
    else
      if ltn.toExpr.isApp && lsn.toExpr.isApp && (unsafe ptrEq dt ds) && dt.hints.isRegular
        && !failedBefore (← get).failure ltn lsn
      then
        if Level.isEquivList ltn.toExpr.getAppFn.constLevels! lsn.toExpr.getAppFn.constLevels! then
          let (defeq, usedPI) ← isDefEqArgsLean ltn lsn
          if defeq then
            if true then
              let (r, proof?) ← isDefEqApp 5 ltn lsn (tfEqsf? := none)
              if r then
                return .bool true proof?
            else
              return .bool true none
        cacheFailure ltn lsn
      deltaCont_both

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? (e : PExpr) : Option PExpr :=
  match e.toExpr with
  | .lit (.natVal (n+1)) => return Expr.lit (.natVal n) |>.toPExpr
  | .app (.const ``Nat.succ _) e => return e.toPExpr
  | _ => none

/--
If `t` and `s` are both successors of natural numbers `t'` and `s'`, either as
literals or `Nat.succ` applications, checks that `t'` and `s'` are
definitionally equal. Otherwise, defers to the calling function.
-/
def isDefEqOffset (t s : PExpr) : RecLB := do
  if isNatZero t && isNatZero s then
    return (.true, none)
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' =>
    let (ret, p?) ← isDefEqCore 64 t' s'
    let p? ← mkNatSuccAppArgHEq? p? t' s'
    pure (ret.toLBool, p?)
  | _, _ => return (.undef, none)

/--
Returns whether the `cheapProj := true` weak-head normal forms of `tn` and
`sn` are defeq if:
- they have matching head constructors (excluding non-α-equivalent applications
  and projections)
- they're both natural number successors (as literals or `Nat.succ` applications)
- one of them can be converted to a natural number/boolean literal.
Otherwise, defers to the calling function with these normal forms.
-/
def lazyDeltaReduction (tn sn : PExpr) : RecM ReductionStatus := loop tn sn none none 1000 where
  loop ltn lsn (tnEqltn? snEqlsn? : Option EExpr)
  | 0 =>
    dbg_trace s!"DBG[66]: TypeChecker.lean:2241 (after | 0 =>)"
    throw .deterministicTimeout
  | fuel+1 => do
    let (r, proof?) ← isDefEqOffset ltn lsn
    if r != .undef then
      if (r == .true) then
        return .bool true proof?
      else
        return .bool false none
    if !ltn.toExpr.hasFVar && !lsn.toExpr.hasFVar then
      if let some (ltn', ltnEqltn'?) ← reduceNat ltn then
        let (ret, ptn'Eqsn?) ← isDefEqCore 65 ltn' lsn
        let tnEqsn? ← appHEqTrans? ltn ltn' lsn ltnEqltn'? ptn'Eqsn?
        return .bool ret tnEqsn?
      else if let some (lsn', lsnEqlsn'?) ← reduceNat lsn then
        let (ret, ptnEqsn'?) ← isDefEqCore 66 ltn lsn'
        let tnEqsn? ← appHEqTrans? ltn lsn' lsn ptnEqsn'? (← appHEqSymm? lsnEqlsn'?)
        return .bool ret tnEqsn?
    let env ← getKEnv
    if let some (ltn', pltnEqLtn'?) ← reduceNative env ltn then
      -- TODO does this case ever happen?
      let (ret, ptn'Eqsn?) ← isDefEqCore 67 ltn' lsn
      let tnEqsn? ← appHEqTrans? ltn ltn' lsn pltnEqLtn'? ptn'Eqsn?
      return .bool ret tnEqsn?
    else if let some (lsn', lsnEqlsn'?) ← reduceNative env lsn then
      -- TODO does this case ever happen?
      let (ret, ptnEqsn'?) ← isDefEqCore 68 ltn lsn'
      let tnEqsn? ← appHEqTrans? ltn lsn' lsn ptnEqsn'? (← appHEqSymm? lsnEqlsn'?)
      return .bool ret tnEqsn?

    match ← lazyDeltaReductionStep ltn lsn with
    | .continue nltn nlsn ltnEqnltn? lsnEqnlsn? =>

      let tnEqnltn? ← appHEqTrans? tn ltn nltn tnEqltn? ltnEqnltn?
      let snEqnlsn? ← appHEqTrans? sn lsn nlsn snEqlsn? lsnEqnlsn?

      let ret ← loop nltn nlsn tnEqnltn? snEqnlsn? fuel
      pure ret
    | .notDelta =>
      return .unknown ltn lsn tnEqltn? snEqlsn?
    | .bool .true ltnEqlsn? =>
      return .bool .true (← appHEqTrans? tn ltn sn tnEqltn? <| ← appHEqTrans? ltn lsn sn ltnEqlsn? <| ← appHEqSymm? snEqlsn?)
    | .bool .false _ =>
      return .bool .false none
    | .unknown .. => throw $ .other "unreachable 11"

/--
If `t` is a string literal and `s` is a string constructor application,
checks that they are defeq after turning `t` into a constructor application.
Otherwise, defers to the calling function.
-/
def tryStringLitExpansionCore (t s : PExpr) : RecM LBool := do
  let .lit (.strVal st) := t.toExpr | return .undef
  let .app sf _ := s.toExpr | return .undef
  unless sf == .const ``String.mk [] do return .undef
  toLBoolM <| isDefEqCorePure 69 (Expr.strLitToConstructor st).toPExpr s

@[inherit_doc tryStringLitExpansionCore]
def tryStringLitExpansion (t s : PExpr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

/--
Checks if `t` and `s` are defeq on account of both being of a unit type (a type
with one constructor without any fields or indices).
-/
-- NOTE: It is okay for this to be a non-congruence-proving function,
-- because any two instances of a unit type must be definitionally equal to a constructor application
def isDefEqUnitLike (t s : PExpr) : RecB := do
  let tType ← whnfPure 70 (← inferTypePure 71 t)
  let .const I _ := tType.toExpr.getAppFn | return (false, none)
  let env ← getKEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return (false, none)
  let .ctorInfo { numFields := 0, .. } ← env.get c | return (false, none)
  if ← isDefEqCorePure 72 tType (← inferTypePure 73 s) then
    return (true, none)
  else
    return (false, none)

@[inherit_doc isDefEqCore]
def isDefEqCore' (t s : PExpr) : RecM (Bool × (Option EExpr)) := do
  -- if (← callId) > 384  && ! (← shouldTrace) then
  --   if t.toExpr.containsFVar' (.mk "_kernel_fresh.37".toName) || s.toExpr.containsFVar' (.mk "_kernel_fresh.37".toName) then 
  --     throw $ .other "HERE"
  -- let (ret, usedPI) ← usesPrfIrrel' t s
  -- if not usedPI then
  --   return (ret, none)

  -- if ← isDefEqPure 74 t s 15 then -- NOTE: this is a tradeoff between runtime and output size -- TODO put back
  --   return (true, none)
  let (r, pteqs?) ← quickIsDefEq 88 t s (useHash := true)
  if r != .undef then return (r == .true, pteqs?)

  if !t.toExpr.hasFVar && s.toExpr.isConstOf ``true then
    let (t, p?) ← whnf 75 t
    if t.toExpr.isConstOf ``true then return (true, p?)

  let (tn, tEqtn?) ← whnfCore 76 t (cheapK := true) (cheapProj := true)
  let (sn, sEqsn?) ← whnfCore 77 s (cheapK := true) (cheapProj := true)

  let mktEqs? (t' s' : PExpr) (tEqt'? sEqs'? t'Eqs'? : Option EExpr) := do 
    let tEqs'? ← appHEqTrans? t t' s' tEqt'? t'Eqs'?
    let s'Eqs? ← appHEqSymm? sEqs'?
    appHEqTrans? t s' s tEqs'? s'Eqs?

  if (tn == t && sn == s) then
    if !(unsafe ptrEq tn t) then
      -- dbg_trace s!"ptrEq mismatch 3"
      pure ()
    if !(unsafe ptrEq sn s) then
      -- dbg_trace s!"ptrEq mismatch 4"
      pure ()
    pure ()
  else
    let (r, tnEqsn?) ← quickIsDefEq 89 tn sn
    if r == .false then
      return (false, none)
    else if r == .true then
      return (true, ← mktEqs? tn sn tEqtn? sEqsn? tnEqsn?)

  let (r, tnEqsn?) ← isDefEqProofIrrel tn sn
  if r != .undef then 
    if r == .true then
      return (true, ← mktEqs? tn sn tEqtn? sEqsn? tnEqsn?)
    return (false, none)

  match ← lazyDeltaReduction tn sn with
  | .continue ..
  | .notDelta => throw $ .other "unreachable 12"
  | .bool b tnEqsn? =>
    return (b, ← mktEqs? tn sn tEqtn? sEqsn? tnEqsn?)
  | .unknown tn' sn' tnEqtn'? snEqsn'? =>
  -- if snEqsn'?.isNone then
  --   if not (← isDefEqPure 0 sn sn') then
  --     throw $ .other "lazyDeltaReduction failed sanity check"

  let tEqtn'? ← appHEqTrans? t tn tn' tEqtn? tnEqtn'?
  let sEqsn'? ← appHEqTrans? s sn sn' sEqsn? snEqsn'?

  match tn'.toExpr, sn'.toExpr with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
  | .fvar tv, .fvar sv => if tv == sv then return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
  | .proj tTypeName ti te, .proj _ si se =>
    if ti == si then
      if !(unsafe ptrEq ti si) then
        -- ttrace s!"ptrEq mismatch 5"
        pure ()
      -- optimized by above functions using `cheapProj = true`
      let (r, teEqse?) ← isDefEq 78 te.toPExpr se.toPExpr

      if r then
        let tn'Eqsn'? ← appProjThm? tTypeName ti te.toPExpr se.toPExpr teEqse?
        return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | .app .., .app .. =>
    let tf := tn'.toExpr.getAppFn
    let sf := sn'.toExpr.getAppFn
    if let .const tn _ := tf then
      if let .const sn _ := sf then
        if tn == sn then
          if let some (.recInfo info) := (← getKEnv).find? tn then
            if info.k then
              -- optimized by above functions using `cheapK = true`
              match ← isDefEqApp 6 tn' sn' with
              | (true, tn'Eqsn'?) =>
                return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
              | _ =>
                pure ()
  | _, _ => pure ()

  -- above functions used `cheapProj = true`, `cheapK = true`, so we may not have a complete WHNF
  let (tn'', tn'Eqtn''?) ← whnfCore 79 tn'
  let (sn'', sn'Eqsn''?) ← whnfCore 80 sn'
  if (tn'' == tn' && sn'' == sn') then
    if !(unsafe ptrEq tn'' tn') then
      -- ttrace s!"ptrEq mismatch 1"
      pure ()
    if !(unsafe ptrEq sn'' sn') then
      -- ttrace s!"ptrEq mismatch 2"
      pure ()
    pure ()
  else
    -- if projection reduced, need to re-run (as we may not have a WHNF)
    let tEqtn''? ← appHEqTrans? t tn' tn'' tEqtn'? tn'Eqtn''?
    let sEqsn''? ← appHEqTrans? s sn' sn'' sEqsn'? sn'Eqsn''?
    let (true, tn''Eqsn''?) ← isDefEqCore 81 tn'' sn'' | return (false, none)
    let r? := ← mktEqs? tn'' sn'' tEqtn''? sEqsn''? tn''Eqsn''?
    return (true, r?)

  -- optimized by above functions using `cheapK = true`
  -- let (defeq, usedPI) ← isDefEqAppLean tn' sn'
  -- if defeq then
  --   if usedPI then
  --     let (r, tn'Eqsn'?) ← isDefEqApp 7 tn' sn'
  --     if r then
  --       return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  --   else
  --     return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
  match ← isDefEqApp 7 tn' sn' with
  | (true, tn'Eqsn'?) =>
    return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | _ =>
    pure ()

  match ← tryEtaExpansion tn' sn' with
  | (true, tn'Eqsn'?) => return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | _ => pure ()


  match ← tryEtaStruct tn' sn' with
  | (true, tn'Eqsn'?) => return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | _ => pure ()

  let r ← tryStringLitExpansion tn' sn'
  if r != .undef then
    if r == .true then 
      return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
    else
      return (false, none)
  let (r, tn'Eqsn'?) ← isDefEqUnitLike tn' sn'
  if r then
    return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  return (false, none)

def isDefEqCorePure' (t s : PExpr) : RecM Bool := do
  try
    let res ← runLeanMinus $ Lean.TypeChecker.isDefEqCore t.toExpr s.toExpr
    pure res
  catch e =>
    throw e

end Inner
