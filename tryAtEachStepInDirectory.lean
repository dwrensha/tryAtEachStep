/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Lean

namespace TryAtEachStepInDirectory

/--
Converts `path` to an absolute path.
-/
def toAbsolute (path : System.FilePath) : IO System.FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path

structure Config where
  tac : String := "exact?"
  directory : System.FilePath := ""
  outdir : System.FilePath := "tryAtEachStep-out"
  additionalImports : List String := []
  num_parallel : Nat := 7
  filter_by_fewer_steps : Bool := true

def spawnChild (config : Config) (p : System.FilePath) :
    IO (IO.Process.Child {}) := do
  let indir ← toAbsolute config.directory
  let pabs ← toAbsolute p
  let outrel := pabs.toString.drop indir.toString.length
  let outstem := outrel.dropRight ".lean".length
  let outfile := (config.outdir / System.FilePath.mk
      ("file:" ++ ((outstem.replace "/" "_").replace "." "") ++ ".json")).toString
  IO.eprintln s!"running tryAtEachStep on {p.toString}"
  IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "tryAtEachStep",
              config.tac,
              p.toString,
              "--outfile", outfile]
  }

def gatherResults (config : Config) : IO Unit := do
  let mut acc : Array Lean.Json := #[]
  for ⟨root, filename⟩ in ← config.outdir.readDir do
    if ¬ filename.startsWith "file:" then continue
    let contents ← IO.FS.readFile (root / filename)
    let r := Lean.Json.parse contents
    let j ← match r with
    | .error s => do
      IO.eprintln s
      continue
    | .ok j => pure j
    let .arr a := j | continue
    acc := acc ++ a

  acc := acc.filterMap fun obj => Id.run do
    if config.filter_by_fewer_steps then
      match (obj.getObjValD "fewerSteps").getBool? with
      | .ok false | .error _ => return .none
      | .ok true => pure ()

    match (obj.getObjValD "goalIsProp").getBool? with
    | .ok false | .error _ => return .none
    | .ok true => pure ()

    let .ok old_proof := (obj.getObjValD "oldProof").getStr? | return none
    let .ok new_proof := (obj.getObjValD "newProof").getStr? | return none

    let obj := obj.setObjVal! "oldProof" .null
    let obj := obj.setObjVal! "newProof" .null

    let lengthReduction := (old_proof.length : Int) - new_proof.length
    let obj := obj.setObjVal! "lengthReduction" (.num (Lean.JsonNumber.fromInt lengthReduction))

    .some obj

  acc := acc.qsort (fun o1 o2 => Id.run do
    let .ok lr1 := (o1.getObjValD "lengthReduction").getInt? | return false
    let .ok lr2 := (o2.getObjValD "lengthReduction").getInt? | return false
    return lr1 > lr2)

  let s := Lean.Json.pretty (.arr acc)
  let resultsPath := config.outdir / "RESULTS.json"
  IO.FS.writeFile resultsPath s
  IO.eprintln s!"Wrote results to {resultsPath}"

/--
Do a null run of `lake exe tryAtEachStep`.
Lake can get confused if multiple processes call `lake exe`
in parallel on an unbuilt target. Therefore, we make a null
call via this function before spawning any parallel work.
-/
def trialRun : IO Unit := do
  let child ← IO.Process.spawn {
    stdout := IO.Process.Stdio.null
    stderr := IO.Process.Stdio.null
    cmd := "lake"
    args := #["exe", "tryAtEachStep"]
  }
  let _ ← child.wait

unsafe def main (config : Config) : IO Unit := do
  trialRun
  IO.FS.createDirAll config.outdir
  let paths ← config.directory.walkDir
  let mut paths := (paths.filter (fun p => p.extension == some "lean")).toList
  let total := paths.length
  let mut children : Array (Option (IO.Process.Child {})) := #[];
  while children.size < config.num_parallel ∧ ¬ paths.isEmpty do
    match paths with
    | [] => break
    | p :: ps =>
      paths := ps
      children := children.push (some (← spawnChild config p))

  let mut num_finished := 0
  while children.any Option.isSome do
     for ii in [0:children.size] do
        if let some c := children[ii]!
        then
          if let some ret ← c.tryWait
          then
            num_finished := num_finished + 1
            IO.eprintln s!"\nChild finished with code {ret}. Progress: {num_finished} / {total}"
            children := children.set! ii none
            if let p :: ps := paths then
              paths := ps
              children := children.set! ii (some (← spawnChild config p))
            pure ()
        pure ()
     IO.sleep 50 -- don't spend too much cpu busy-waiting
  IO.println "\nDone! Now collecting results..."
  gatherResults config
  return ()

def parseArgs (args : Array String) : IO Config := do
  let mut cfg : Config := {}
  let mut idx := 0
  let mut positional_count := 0
  while idx < args.size do
    if args[idx]! == "--imports"
    then
      idx := idx + 1
      let imports := args[idx]!.splitOn ","
      cfg := {cfg with additionalImports := imports}
    else if args[idx]! == "--outdir"
    then
      idx := idx + 1
      cfg := {cfg with outdir := args[idx]!}
    else if args[idx]! == "-j"
    then
      idx := idx + 1
      cfg := {cfg with num_parallel := args[idx]!.toNat!}
    else if args[idx]! == "--filter-by-fewer-steps"
    then
      idx := idx + 1
      let v ← match args[idx]! with
      | "true" => pure true
      | "false" => pure false
      | _ => throw $ IO.userError s!"failed to parse bool from {args[idx]!}"
      cfg := {cfg with filter_by_fewer_steps := v}
    else if positional_count == 0
    then
      let tac := args[idx]!
      cfg := {cfg with tac := tac}
      positional_count := positional_count + 1
    else if positional_count == 1
    then
      let directory := ⟨args[idx]!⟩
      cfg := {cfg with directory := directory}
      positional_count := positional_count + 1
    else
      throw $ IO.userError "too many positional arguments!"

    idx := idx + 1
    pure ()

  if positional_count != 2
  then
    throw $ IO.userError "usage: tryAtEachStepInDirectory [OPTIONS] TACTIC DIRECTORY"
  return cfg

end TryAtEachStepInDirectory

unsafe def main (args : List String) : IO Unit := do
  let cfg ← TryAtEachStepInDirectory.parseArgs args.toArray
  TryAtEachStepInDirectory.main cfg
  pure ()
