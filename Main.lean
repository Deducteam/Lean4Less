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

structure ForEachModuleCtx where
  origEnv : Environment

structure ForEachModuleState where
  moduleNameSet : NameHashSet := {}
  env : Environment
  count := 0

-- def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx) (modIdx : Nat) (cname : Name) : IO α := do
--   let modName := s.moduleNames[modIdx]!
--   let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
--   throw <| IO.userError s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

abbrev ForEachModuleM := ReaderT ForEachModuleCtx $ StateRefT ForEachModuleState IO

@[inline] nonrec def ForEachModuleM.run (origEnv env : Environment) (x : ForEachModuleM α) (s : ForEachModuleState := {env}) : IO (α × ForEachModuleState) :=
  x.run {origEnv} |>.run s

def findOLeanParts (mod : Name) : IO (Array (System.FilePath × String)) := do
  let mFile ← findOLean mod
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {mod} does not exist"
  let mut fnames := #[(mFile, "olean")]
  -- Opportunistically load all available parts.
  -- Necessary because the import level may be upgraded a later import.
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push (sFile, "olean.server")
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push (pFile, "olean.private")
  return fnames

partial def getLeafModules (imports : Array Import) : ForEachModuleM $ Array (Name × Array Import) := do
  let mut leafs : Array (Name × Array Import) := #[]
  for i in imports do
    if /- i.runtimeOnly ||  -/(← get).moduleNameSet.contains i.module then
      continue
    let mFiles ← findOLeanParts i.module
    let parts ← readModuleDataParts (mFiles.map (·.1))
    let some part0 := parts[0]? | unreachable!
    let imports := part0.1.imports 
    let modLeafs ← getLeafModules imports
    leafs := leafs ++ modLeafs
    if modLeafs.size == 0 then
      modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
      leafs := leafs.push (i.module, imports)
  pure leafs

def getModConsts (env : Environment) (m : Name) := 
  env.constants.map₁.toList.map (·.1) |>.filter fun n =>
    if let some nidx := env.const2ModIdx.get? n then
      if let some midx := env.getModuleIdx? m then
        if midx == nidx then
          true
        else
          false
      else
        false
    else
      false

unsafe def origEnv : ForEachModuleM Environment := do
    pure (← read).origEnv

unsafe def withModConstMap (mod : Name) (f : Std.HashMap Name ConstantInfo → ForEachModuleM α) : ForEachModuleM α := do
    let origEnv := (← read).origEnv
    let modConsts := getModConsts origEnv mod
    let mut map : Std.HashMap Name ConstantInfo := default
    for n in modConsts do
      if let some ci := (origEnv.constants.find? n) then
        map := map.insert n ci
    f map

unsafe def forEachModule' (rootMod : Name) (initEnv : Environment) (f : Name → Array Import → Std.HashMap Name ConstantInfo → Environment → NameSet → ForEachModuleM (Environment × NameSet)) (aborted : NameSet) (cont : NameSet → ForEachModuleState → IO α) : IO α := do
  Lean.withImportModules #[{module := rootMod}] {} fun origEnv => do
    let (aborted, state) ← ForEachModuleM.run origEnv initEnv do
      let mut aborted := aborted
      while true do
        let leafs ← getLeafModules #[rootMod]
        if leafs.size == 0 then
          break
        let rec r leafs env aborted : ForEachModuleM (Environment × NameSet) := do
          match leafs with
          | (m, imports) :: leafs => do withModConstMap m fun constMap => do
            modify fun s => { s with count := s.count + 1 }
            let (env, aborted) ← f m imports constMap env aborted
            r leafs env aborted
          | [] => pure (env, aborted)

        let (env, _aborted) ← r leafs.toList (← get).env aborted
        aborted := _aborted
        modify fun s => { s with env }
      pure aborted
    cont aborted state

unsafe def forEachModule (rootMod : Name) (initEnv : Environment)
  (f : Name → Array Import → Std.HashMap Name ConstantInfo → Environment → NameSet → ForEachModuleM (Environment × NameSet)) (aborted : NameSet) : IO NameSet := do
  forEachModule' rootMod initEnv f aborted fun aborted _ => pure aborted

def mkModuleData (imports : Array Import) (env : Environment) (newEntries : Array (Name × Array EnvExtensionEntry) := #[]) : IO ModuleData := do
  -- let pExts ← persistentEnvExtensionsRef.get
  -- let entries := pExts.map fun pExt => Id.run do
  --   -- get state from `checked` at the end if `async`; it would otherwise panic
  --   let mut asyncMode := pExt.toEnvExtension.asyncMode
  --   if asyncMode matches .async then
  --     asyncMode := .sync
  --   let state := pExt.getState (asyncMode := asyncMode) env
  --   (pExt.name, pExt.exportEntriesFn state)
  -- -- let pExts ← persistentEnvExtensionsRef.get
  -- -- let entries := pExts.map fun pExt =>
  -- --   let state := pExt.getState env
  -- --   (pExt.name, pExt.exportEntriesFn state)
  -- let constNames := env.toKernelEnv.constants.foldStage2 (fun names name _ => names.push name) #[]
  -- let constants  := env.toKernelEnv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
  -- return {
  --   extraConstNames := #[],
  --   imports, constNames, constants, entries := entries ++ newEntries,
  --   isModule := true
  -- }
  sorry

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
  let bnm : Bool := p.hasFlag "bignum"
  let opts : Lean4Less.TypeCheckerOpts := {proofIrrelevance := pi, kLikeReduction := klr, structLikeReduction := slr, bignum := bnm}
  match mod with
    | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
    | m =>
      let .some lemmEnv ← Lean.Elab.runFrontend (include_str "patch" / "PatchTheorems.lean") default default `Patch |
        throw $ IO.userError $ "elab of patching defs failed"
      let overrides := Lean4Less.getOverrides lemmEnv.toKernelEnv
      -- let m := `Init.Classical
      -- Lean.withImportModules #[{module := m}] {} fun env => do
      --   -- dbg_trace s!"DBG[41]: Main.lean:133 {env.constants.map₁.toList.map (·.1)}"
      --   dbg_trace s!"DBG[41]: Main.lean:133 {getModConsts env m}"
      if let some onlyConsts := onlyConsts? then
        Lean.withImportModules #[{module := mod}] {} fun env => do
          let mut env := env
          for (_, c) in lemmEnv.constants do
            env := add' env c
            -- dbg_trace s!"DBG[60]: Main.lean:118 {Lean.Environment.base env |>.get env |>.constants.map₁[c.name]? |>.isSome}, {c.name}"
          _ ← Lean4Less.checkL4L (onlyConsts.map (·.toName)) env.toKernelEnv (printProgress := true) (printOutput := p.hasFlag "print") (opts := opts) (dbgOnly := dbgOnly) (deps := not dbgOnly)
          -- dbg_trace s!"DBG[61]: Main.lean:121 (after _ ← Lean4Less.checkL4L (onlyConsts.map…)"
          --
        -- let parts ← findOLeanParts mod
        -- let mFile ← findOLean mod
        -- let (d, _) ← readModuleData mFile
        -- dbg_trace s!"DBG[63]: Main.lean:218 {d.extraConstNames.contains ``Array.eraseIdx._unary.induct}, {d.constants.any (·.name == `Array.eraseIdx._unary.induct)}, {d.constNames.contains `Array.eraseIdx._unary.induct}, {d.constNames.contains `Array.eraseIdx.induct}"
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
        -- let mkMod imports env n ext aborted (newEntries := #[]) := do
        --   let mod ← mkModuleData imports env newEntries
        --   let modPath := (modToFilePath outDir n ext)
        --   let some modParent := modPath.parent | panic! s!"could not find parent dir of module {n}"
        --   IO.FS.createDirAll modParent
        --   let aborteds := aborted.toList
        --   let mut abortedTxt := ""
        --   for i in [:aborteds.length] do
        --     abortedTxt := abortedTxt ++ aborteds[i]!.toString
        --     if i < aborteds.length - 1 then
        --       abortedTxt := abortedTxt ++ "\n"
        --   IO.FS.writeFile abortedFile abortedTxt
        --   saveModuleData modPath n mod
        let mkMod imports env m := do
          let newEnv := updateEnvHeader env (updateEnvHeaderImports env.header imports)
          let modPath := (modToFilePath outDir m "olean")
          let some modParent := modPath.parent | throw $ IO.userError s!"could not find parent dir of module {m}"
          IO.FS.createDirAll modParent
          let data ← mkModuleData newEnv
          saveModuleData modPath newEnv.mainModule data

        IO.println s!">>init module"
        let patchConsts ← getDepConstsEnv lemmEnv Lean4Less.patchConsts overrides
        let (kenv, aborted) ← replay (Lean4Less.addDecl (opts := opts)) {newConstants := patchConsts, opts := {}, overrides} (← mkEmptyEnvironment).toKernelEnv (printProgress := true) (op := "patch") (aborted := aborted)
        let env := updateBaseAfterKernelAdd lemmEnv kenv
        -- mkMod #[] env patchPreludeModName

        let (aborted, count) ← forEachModule' m (← mkEmptyEnvironment) (aborted := aborted) (fun n imports constMap env aborted => do
            if abortedMods.contains n then
              let aborted' := constMap.toList.foldl (init := aborted) fun acc (cn, _) => acc.insert cn
              pure (env, aborted')
            else
              pure (env, aborted))
          fun aborted s => pure (aborted, s.count)
        let numMods := count

        forEachModule' m (aborted := aborted) env (fun m imports constMap env aborted => do
          let currEnv := env
          let mut newEnv := currEnv
          let skip ←
            if let some cachedPath := cachedPath? then
              if let some mfile ← SearchPath.findWithExt [cachedPath] "olean" m then
                if ← mfile.pathExists then
                  let (mod, _) ← readModuleData mfile
                  let mut env := currEnv
                  for c in mod.constants do
                    env := add' env c
                  newEnv := env
                  pure true
                else
                  pure false
              else
                pure false
            else
              pure false
          unless not skip do return (newEnv, aborted)

          let (newConstants, overrides) ← constMap.toList |>.foldlM (init := (default, Lean4Less.getOverrides env.toKernelEnv)) fun (accNewConstants, accOverrides) (n, ci) => do
            if not (newEnv.constants.find? n).isSome then
              if let some n' := constOverrides[n]? then
                if let some ci' := lemmEnv.find? n' then
                  let accOverrides := accOverrides.insert n ci'

                  let overrideDeps ← getDepConstsEnv lemmEnv #[n'] overrides
                  let mut accNewConstants := accNewConstants
                  for (dep, depi) in overrideDeps do
                    if not (newEnv.constants.contains dep) then
                      accNewConstants := accNewConstants.insert dep depi
                  pure (accNewConstants.insert n ci, accOverrides)
                else
                  panic! "could not find override `{n'}` for '{n}'"
              else pure (accNewConstants.insert n ci, accOverrides)
            else
              pure $ (accNewConstants, accOverrides)
          -- if dn == `Init.Data.Nat.Basic then
          --   if let some ci := d.constants.find? (fun ci => ci.name == `Nat.repeatTR.loop) then
          --     let name := match ci with
          --       | .axiomInfo    .. => "axiom"
          --       | .defnInfo     .. => "def"
          --       | .thmInfo      .. => "thm"
          --       | .opaqueInfo   .. => "opaque"
          --       | .quotInfo     .. => "quot"
          --       | .inductInfo   .. => "induct"
          --       | .ctorInfo     .. => "ctor"
          --       | .recInfo      .. => "rec"
          --     dbg_trace s!"DBG[B]: TypeChecker.lean:1643 {name}"
          IO.println s!">>{m} module [{(← get).count}/{numMods}]"
          let (kenv, aborted) ← replay (Lean4Less.addDecl (opts := opts)) {newConstants := newConstants, opts := {}, overrides} newEnv.toKernelEnv (printProgress := true) (op := "patch") (aborted := aborted)
          newEnv := updateBaseAfterKernelAdd newEnv kenv

          let imports := if m == `Init.Prelude then
              #[{module := patchPreludeModName}] ++ imports
            else
              imports
          -- mkMod imports newEnv m

          pure (newEnv, aborted))
          fun aborted s => do
            let env := s.env
            replayFromEnv Lean4Lean.addDecl m env.toKernelEnv.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := not opts.proofIrrelevance, kLikeReduction := not opts.kLikeReduction, bignums := not opts.bignum})
        -- forEachModule' (imports := #[m]) (init := env) fun e dn d => do
        --   -- let newConstants := d.constNames.zip d.constants |>.foldl (init := default) fun acc (n, ci) => acc.insert n ci
        --
        --   IO.println s!"{dn} module"
        --   pure e
          -- replay Lean4Less.addDecl {newConstants := newConstants, opts := {}} e (printProgress := true)
        -- replayFromInit' Lean4Less.addDecl m lemmEnv (op := "patch") (initConsts? := Lean4Less.patchConsts) fun env' =>
        --   replayFromEnv Lean4Lean.addDecl m env'.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})
  return 0
-- #print Nat.brecOn
-- #print Nat.repeatTR.loop
-- #check_off Nat.repeatTR.loop.eq_1

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
    bnm, "bignum"; "Eliminate bignums."
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
