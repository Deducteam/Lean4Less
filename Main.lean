/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Cli
import Lean.Util.FoldConsts
import Lean4Less.Environment
import Lean4Less.Fixtures.Tests -- FIXME should use separate fixtures dir
import Lean4Less.Replay
import Lean4Less.Commands

open Lean
open Lean4Lean
open Lean4Less
open Cli

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

def outDir : System.FilePath := System.mkFilePath [".", "out"]

structure ForEachModuleState where
  moduleNameSet : NameHashSet := {}
  env : Environment
  count := 0

-- def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx) (modIdx : Nat) (cname : Name) : IO α := do
--   let modName := s.moduleNames[modIdx]!
--   let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
--   throw <| IO.userError s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

abbrev ForEachModuleM := StateRefT ForEachModuleState IO

@[inline] nonrec def ForEachModuleM.run (env : Environment) (x : ForEachModuleM α) (s : ForEachModuleState := {env}) : IO (α × ForEachModuleState) :=
  x.run s

partial def getLeafModules (imports : Array Import) : ForEachModuleM $ Array (Name × ModuleData) := do
  let mut leafs := #[]
  for i in imports do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      continue
    let mFile ← findOLean i.module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
    let (mod, _) ← readModuleData mFile
    let modLeafs ← getLeafModules mod.imports
    if modLeafs.size == 0 then
      modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
      leafs := leafs.push (i.module, mod)
    leafs := leafs ++ modLeafs
  pure leafs

partial def forEachModule' (f : Name → ModuleData → NameSet → ForEachModuleM NameSet) (imports : Array Import) (aborted : NameSet) : ForEachModuleM NameSet := do
  let mut aborted := aborted
  while true do
    let leafs ← getLeafModules imports
    if leafs.size == 0 then break
    for (n, m) in leafs do
      modify fun s => { s with count := s.count + 1 }
      aborted ← f n m aborted
  pure aborted

def mkModuleData (imports : Array Import) (env : Environment) (newEntries : Array (Name × Array EnvExtensionEntry) := #[]) : IO ModuleData := do
  let pExts ← persistentEnvExtensionsRef.get
  let entries := pExts.map fun pExt => Id.run do
    -- get state from `checked` at the end if `async`; it would otherwise panic
    let mut asyncMode := pExt.toEnvExtension.asyncMode
    if asyncMode matches .async then
      asyncMode := .sync
    let state := pExt.getState (asyncMode := asyncMode) env
    (pExt.name, pExt.exportEntriesFn state)
  -- let pExts ← persistentEnvExtensionsRef.get
  -- let entries := pExts.map fun pExt =>
  --   let state := pExt.getState env
  --   (pExt.name, pExt.exportEntriesFn state)
  let constNames := env.toKernelEnv.constants.foldStage2 (fun names name _ => names.push name) #[]
  let constants  := env.toKernelEnv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
  return {
    extraConstNames := #[],
    imports, constNames, constants, entries := entries ++ newEntries
  }

def patchPreludeModName := `Init.PatchPrelude

/--
Run as e.g. `lake exe lean4lean` to check everything on the Lean search path,
or `lake exe lean4lean Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
-/
unsafe def runTransCmd (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mod : Name := p.positionalArg! "input" |>.value.toName
  let onlyConsts? := p.flag? "only" |>.map fun onlys => 
    onlys.as! (Array String)
  let cachedPath? := p.flag? "cached" |>.map fun sp => 
    System.FilePath.mk $ sp.as! String
  let pi : Bool := p.hasFlag "proof-irrel"
  let dbgOnly : Bool := p.hasFlag "dbg-only"
  let klr : Bool := p.hasFlag "klike-red"
  let slr : Bool := p.hasFlag "slike-red"
  let ue : Bool := p.hasFlag "unit-eta"
  let stub : Bool := p.hasFlag "stub"
  let opts : Lean4Less.TypeCheckerOpts := {proofIrrelevance := pi, kLikeReduction := klr, structLikeReduction := slr, unitEta := ue, stubInfeasibleNatOps := stub}
  match mod with
    | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
    | m =>
      let (lemmEnv, success) ← Lean.Elab.runFrontend (include_str "patch" / "PatchTheorems.lean") default default `Patch -- TODO how to add PatchTheorems.lean as a lake dependency?
      let overrides := Lean4Less.getOverrides lemmEnv.toKernelEnv
      if not success then
        throw $ IO.userError $ "elab of patching defs failed"
      if let some onlyConsts := onlyConsts? then
        Lean.withImportModules #[{module := mod}] {} 0 fun env => do
          let mut env := env
          for (_, c) in lemmEnv.constants do
            env := add' env c
          _ ← Lean4Less.checkL4L (onlyConsts.map (·.toName)) env.toKernelEnv (printProgress := true) (printOutput := p.hasFlag "print") (opts := opts) (dbgOnly := dbgOnly) (deps := not dbgOnly)
      else
        let outDir := ((← IO.Process.getCurrentDir).join "out")
        let abortedFile := outDir.join "aborted.txt"
        let abortedModsFile := outDir.join "aborted_mods.txt"
        if (← outDir.pathExists) && not cachedPath?.isSome then
          IO.FS.removeDirAll outDir
        let (aborted, abortedMods) ← do
          if let some _ := cachedPath? then
            let readNames (file : System.FilePath) := do
              if ← file.pathExists then do
                let txt : String ← IO.FS.readFile file
                let txtSplit := txt.splitOn "\n" |>.toArray
                pure $ txtSplit.foldl (init := default) fun (acc : NameSet) c =>
                  if c.length > 0 then
                    acc.insert c.toName
                  else
                    acc
              else
                pure default
            let aborted : NameSet ← readNames abortedFile
            let abortedMods : NameSet ← readNames abortedModsFile
            pure (aborted, abortedMods)
          else
            pure default
        -- dbg_trace s!"DBG[39]: Main.lean:117: abortedTxtSplit={aborted.toList}"
        IO.FS.createDirAll outDir
        let mkMod imports env n aborted (newEntries := #[]) := do
          let mod ← mkModuleData imports env newEntries
          let modPath := (modToFilePath outDir n "olean")
          let some modParent := modPath.parent | panic! s!"could not find parent dir of module {n}"
          IO.FS.createDirAll modParent
          let aborteds := aborted.toList
          let mut abortedTxt := ""
          for i in [:aborteds.length] do
            abortedTxt := abortedTxt ++ aborteds[i]!.toString
            if i < aborteds.length - 1 then
              abortedTxt := abortedTxt ++ "\n"
          IO.FS.writeFile abortedFile abortedTxt
          saveModuleData modPath n mod

        IO.println s!">>init module"
        let patchConsts ← getDepConstsEnv lemmEnv Lean4Less.patchConsts overrides
        let (kenv, aborted, _, _) ← replay (Lean4Less.addDecl (opts := opts)) {newConstants := patchConsts, opts := {}, overrides} (← mkEmptyEnvironment).toKernelEnv (printProgress := true) (op := "patch") (aborted := aborted)
        let env := updateBaseAfterKernelAdd lemmEnv kenv
        mkMod #[] env patchPreludeModName aborted
        

        let (aborted, s) ← ForEachModuleM.run env do
          forEachModule' (imports := #[m]) (aborted := aborted) fun n d aborted => do
            if abortedMods.contains n then
              pure $ d.constNames.foldl (init := aborted) fun acc cn => acc.insert cn
            else
              pure aborted
        let numMods := s.moduleNameSet.size

        let (_, s) ← ForEachModuleM.run env do
          forEachModule' (imports := #[m]) (aborted := aborted) fun dn d aborted => do
            let skip ←
              if let some cachedPath := cachedPath? then
                if let some mfile ← SearchPath.findWithExt [cachedPath] "olean" dn then
                  if ← mfile.pathExists then
                    let (mod, _) ← readModuleData mfile
                    let mut env := (← get).env
                    for c in mod.constants do
                      env := add' env c
                    modify fun s => {s with env}
                    pure true
                  else
                    pure false
                else
                  pure false
              else
                pure false
            unless not skip do return aborted

            let (newConstants, overrides) ← d.constNames.zip d.constants |>.foldlM (init := (default, Lean4Less.getOverrides env.toKernelEnv)) fun (accNewConstants, accOverrides) (n, ci) => do
              if not ((← get).env.constants.contains n) then
                if let some n' := constOverrides[n]? then
                  if let some ci' := lemmEnv.find? n' then
                    let accOverrides := accOverrides.insert n ci'

                    let overrideDeps ← getDepConstsEnv lemmEnv #[n'] overrides
                    let mut accNewConstants := accNewConstants
                    for (dep, depi) in overrideDeps do
                      if not ((← get).env.constants.contains dep) then
                        accNewConstants := accNewConstants.insert dep depi
                    pure (accNewConstants.insert n ci, accOverrides)
                  else
                    panic! "could not find override `{n'}` for '{n}'"
                else pure (accNewConstants.insert n ci, accOverrides)
              else
                pure $ (accNewConstants, accOverrides)
            IO.println s!">>{dn} module [{(← get).count}/{numMods}]"
            let (kenv, aborted, _, _) ← replay (Lean4Less.addDecl (opts := opts)) {newConstants := newConstants, opts := {}, overrides} (← get).env.toKernelEnv (printProgress := true) (op := "patch") (aborted := aborted)
            let imports := if dn == `Init.Prelude then
                #[{module := patchPreludeModName}] ++ d.imports
              else
                d.imports

            let env := updateBaseAfterKernelAdd env kenv
            mkMod imports env dn aborted (newEntries := d.entries)
            modify fun s => {s with env}
            pure aborted
        let env := s.env
        replayFromEnv Lean4Lean.addDecl m env.toKernelEnv.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := not opts.proofIrrelevance, kLikeReduction := not opts.kLikeReduction})
        -- forEachModule' (imports := #[m]) (init := env) fun e dn d => do
        --   -- let newConstants := d.constNames.zip d.constants |>.foldl (init := default) fun acc (n, ci) => acc.insert n ci
        --
        --   IO.println s!"{dn} module"
        --   pure e
          -- replay Lean4Less.addDecl {newConstants := newConstants, opts := {}} e (printProgress := true)
        -- replayFromInit' Lean4Less.addDecl m lemmEnv (op := "patch") (initConsts? := Lean4Less.patchConsts) fun env' =>
        --   replayFromEnv Lean4Lean.addDecl m env'.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})
  return 0

unsafe def transCmd : Cmd := `[Cli|
  transCmd VIA runTransCmd; ["0.0.1"]
  "Translate from Lean to Lean-."

  FLAGS:
    -- p, print;               "Print translation of specified constants to standard output (relevant only with '-o ...')."
    -- w, write;               "Also write translation of specified constants (with dependencies) to file (relevant only with '-p')."
    o, only : Array String; "Only translate the specified constants and their dependencies (output to directory 'only_out')."
    p, print; "Print translated constant specified by --only."
    O, "dbg-only"; "(for debugging)"
    pi, "proof-irrel"; "Eliminate proof irrelevance."
    klr, "klike-red"; "Eliminate K-like reduction."
    slr, "slike-red"; "Eliminate struct-like reduction."
    ue, "unit-eta"; "Eliminate unit-eta."
    st, "stub"; "Stub constants requiring infeasible primitive Nat ops (as in the lean2dk/Dedukti translation)."
    c, cached : String; "Use cached library translation files from specified directory."

  ARGS:
    input : String;         "Input .lean file."

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "rish987"
]

unsafe def main (args : List String) : IO UInt32 := do
  transCmd.validate args
