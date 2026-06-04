import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Less.Environment
import Lean4Lean.Replay

open Lean

namespace Lean4Less

open Lean4Less.Kernel.Environment
open Lean4Lean

/-- Add a declaration, possibly throwing a `KernelException`. -/
def addDecl (d : Declaration) (opts : TypeCheckerOpts := {}) : M Unit := do
  if (← read).verbose then
    println! "adding {d.name}"
  let t1 ← IO.monoMsNow
  match Lean4Less.Kernel.Environment.addDecl' (← get).env d opts with
  | .ok env =>
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      println! "{Lean4Lean.Ansi.resetLine}lean4less took {t2 - t1}:\t {d.name}"
    modify fun s => { s with env := env }
  | .error ex =>
    match ex with
    | .other "translation aborted" =>
      throw $ .otherError 165846 "translation aborted"
    | .other "large nat prim op" =>
      throw $ .otherError 165847 "large nat prim op"
    | .other "large nat prim op type" =>
      throw $ .otherError 165848 "large nat prim op type"
    | _ =>
      throwKernelException ex

end Lean4Less
