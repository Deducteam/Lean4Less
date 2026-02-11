import Lean
import Lean4Less.Replay
import Lean4Lean.Util
import Lean4Lean.Commands

open Lean
open Lean4Lean

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

def add' (env : Environment) (ci : ConstantInfo) : Environment :=
  let kenv := env.toKernelEnv
  let kenv := match ci with
    | .quotInfo _ =>
      markQuotInit kenv
    | _ => kenv
  let kenv := kenv.add ci
  updateBaseAfterKernelAdd env kenv.toMap₁

namespace Lean4Less

unsafe def withImportModuleInit (init : Environment) (mod : Name) (f : Environment → IO α) : IO α := do
  Lean.withImportModules #[{module := mod}] {} fun env => do
    let mut env := env
    for (_, c) in init.constants do
      env := add' env c
    f env

unsafe def withImportModuleAndPatchDefs (mod : Name) (f : Environment → IO α) (elabPatch := true) : IO α := do
  Lean.withImportModules #[{module := mod}] {} fun env => do
    let mut env := env
    if elabPatch then
      -- TODO how to add PatchTheorems.lean as a lake dependency?
      let .some patchEnv ← Lean.Elab.runFrontend (include_str ".." / "patch" / "PatchTheorems.lean") default default `Patch |
        throw $ IO.userError $ "elab of patching defs failed"
      for (_, c) in patchEnv.constants do
        env := add' env c
    f env

unsafe def withPatchDefs (f : Environment → IO α) : IO α := do
  let .some patchEnv ← Lean.Elab.runFrontend (include_str ".." / "patch" / "PatchTheorems.lean") default default `Patch |
    throw $ IO.userError $ "elab of patching defs failed"
  f patchEnv

def ppConst (env : Kernel.Environment) (n : Name) : IO Unit := do
  let options : Options := default
  let options := options.set `pp.proofs true
  let options := options.set `pp.explicit true
  let options := options.set `pp.funBinderTypes true
  let some info := env.find? n | unreachable!
  try
    IO.print s!"patched {info.name}: {← (PrettyPrinter.ppExprLegacy (Environment.ofKernelEnv env) default default options info.type)}"

    match info.value? with
    | .some v =>
      if v.approxDepth < 100 then
        IO.println s!"\n{← (PrettyPrinter.ppExprLegacy (Environment.ofKernelEnv env) default default options v)}"
      else
        IO.println s!"\n [[[expression too large]]]"
    | _ => IO.println ""
  catch
  | _ =>
    IO.print s!"patched {info.name}: {info.type}"
    match info.value? with
    | .some v =>
      if v.approxDepth < 100 then
        IO.println s!"\n{v}"
      else
        IO.println s!"\n [[[expression too large]]]"
    | _ => IO.println ""

/--
The set of all constants used to patch terms, in linearised order based on
dependencies in the patched versions of their types/values.
-/
def patchConsts : Array Name := #[
`L4L.prfIrrel,
`L4L.forallEqUV',
`L4L.appArgEq,
`eq_of_heq,
`cast,
`L4L.HEqRefl,
`L4L.castHEq,
`HEq,
`HEq.symm,
`HEq.refl,
`HEq.trans,
`Eq,
`Eq.refl,

`L4L.prfIrrelHEq,
`L4L.prfIrrelHEqPQ,

`L4L.forallHEqUV,
`L4L.forallHEqUV',
`L4L.forallHEqAB,
`L4L.forallHEqABUV,
`L4L.forallHEqABUV',
`L4L.appArgHEq,
`L4L.appArgHEq',
`L4L.appFunHEq,
`L4L.appFunHEq',
`L4L.appHEq,
`L4L.appHEq',
`L4L.appHEqUV,
`L4L.appHEqUV',
`L4L.appFunHEqUV,
`L4L.appFunHEqUV',
`L4L.appHEqAB,
`L4L.appHEqABUV,
`L4L.appHEqABUV',
`L4L.lambdaHEq,
`L4L.lambdaHEq',
`L4L.lambdaHEqUV,
`L4L.lambdaHEqUV',
`L4L.lambdaHEqABUV,
`L4L.lambdaHEqABUV',

`L4L.castOrigHEq,
`L4L.castOrigHEqSymm,

`L4L.appHEqBinNatFn,
-- `L4L.Nat.eq_or_lt_of_le,
`sorryAx --FIXME
]

def constOverrides' : Array (Name × Name) := #[
  (`eq_of_heq, `L4L.eq_of_heq)
  -- , (`Nat.eq_or_lt_of_le, `L4L.Nat.eq_or_lt_of_le)
]

-- theorem Nat.eq_or_lt_of_le {n m: Nat} (h : LE.le n m) : Or (Eq n m) (LT.lt n m) :=
--   match n, h with
--   | .zero, _ =>
--     match m with
--     | .zero => Or.inl rfl
--     | .succ _ => Or.inr (Nat.succ_le_succ (Nat.zero_le _))
--   | .succ n, h =>
--     match m, h with
--     | .zero, h => absurd h (Nat.not_succ_le_zero _)
--     | .succ m, h =>
--       have : LE.le n m := Nat.le_of_succ_le_succ h
--       match Nat.eq_or_lt_of_le this with
--       | Or.inl h => Or.inl (h ▸ rfl)
--       | Or.inr h => Or.inr (Nat.succ_le_succ h)

def constOverrides : Std.HashMap Name Name := constOverrides'.foldl (init := default) fun acc (n, n') => acc.insert n n'

-- def getOverrides (env : Environment) (overrides : Std.HashMap Name Name) : Std.HashMap Name ConstantInfo :=
def getOverrides (env : Kernel.Environment) : Std.HashMap Name ConstantInfo :=
  constOverrides.fold (init := default) fun acc n n' =>
    if env.constants.contains n then
      if let some ci := env.find? n' then
        acc.insert n ci
      else
        panic! s!"could not find override `{n'}` for '{n}'"
    else
      acc

def transL4L' (ns : Array Name) (env : Kernel.Environment) (pp := false) (printProgress := false) (interactive := false) (opts : TypeCheckerOpts := {}) (dbgOnly := false) : IO Environment := do
  let map := ns.foldl (init := default) fun acc n => .insert acc n
  let (_, newEnv) ← checkConstants (printErr := true) (Environment.ofKernelEnv env.toMap₁) map (@Lean4Less.addDecl (opts := opts)) (initConsts := patchConsts) (op := "patch") (printProgress := printProgress) (interactive := interactive) (overrides := getOverrides env) (dbgOnly := dbgOnly)
  for n in ns do
    if pp then
      ppConst newEnv.toKernelEnv n
  pure newEnv

def transL4L (n : Array Name) (env? : Option Kernel.Environment := none) : Lean.Elab.Command.CommandElabM Environment := do
  let env ← env?.getDM (do
      let e ← getEnv
      pure e.toKernelEnv
    )
  transL4L' n env

def checkL4L (ns : Array Name) (env : Kernel.Environment) (printOutput := true) (printProgress := false) (interactive := false) (opts : TypeCheckerOpts := {}) (dbgOnly := false) (deps := false) : IO Environment := do
  let env ← transL4L' ns env (pp := printOutput) (printProgress := printProgress) (interactive := interactive) (opts := opts) (dbgOnly := dbgOnly)
  let env := updateBaseAfterKernelAdd env env.toKernelEnv.toMap₁
  let ns := ns
  let nSet := ns.foldl (init := default) fun acc n => acc.insert n
  -- unsafe replayFromEnv Lean4Lean.addDecl env.mainModule env.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})


  let (_, checkEnv) ← checkConstants (printErr := true) env nSet Lean4Lean.addDecl (printProgress := printProgress) (opts := {proofIrrelevance := not opts.proofIrrelevance, kLikeReduction := not opts.kLikeReduction}) (interactive := interactive) (dbgOnly := false) (overrides := default) (deps := deps) (write := false)

  -- let env' ← transL4L' ns env
  -- for n in ns do
  --   let .some c  := env.find? n | unreachable!
  --   let .some c' := env'.find? n | unreachable!
  --
  --   let diffTypes := c.toConstantVal.type != c'.toConstantVal.type
  --   let diffVals := c.value? != c'.value?
  --   if diffTypes || diffVals then
  --     throw $ IO.userError $ s!"failed round-trip test: \n--- LHS\n {← ppConst env n} \n--- RHS\n {← ppConst env' n}"
  pure checkEnv

elab "#trans_l4l " i:ident : command => do
  _ ← transL4L #[i.getId]

elab "#check_only " i:ident : command => do
  _ ← checkConstants (printErr := true) (← getEnv) (.insert default i.getId) (Lean4Lean.addDecl (verbose := true)) (opts := {}) (interactive := true) (overrides := getOverrides (← getEnv).toKernelEnv)

elab "#check_off " i:ident : command => do
  _ ← checkConstants (printErr := true) (← getEnv) (.insert default i.getId) Lean4Lean.addDecl (opts := {proofIrrelevance := false, kLikeReduction := false}) (interactive := true) (overrides := getOverrides (← getEnv).toKernelEnv)

elab "#check_l4l " i:ident : command => do
  _ ← checkL4L #[i.getId] (← getEnv).toKernelEnv (interactive := true)

end Lean4Less
  -- match macroRes with
  -- | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  -- | none =>
  --   let kind := c.raw.getKind
  --   let elabs := commandElabAttribute.getEntries (←getEnv) kind
  --   match elabs with
  --   | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
  --   | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"
