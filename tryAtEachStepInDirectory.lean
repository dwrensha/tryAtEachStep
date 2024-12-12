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

def spawnChild (config : Config) (p : System.FilePath) :
    IO (IO.Process.Child {}) := do
  let indir ← toAbsolute config.directory
  let pabs ← toAbsolute p
  let outrel := pabs.toString.drop indir.toString.length
  let outstem := outrel.dropRight ".lean".length
  let outfile := (config.outdir / System.FilePath.mk
      (((outstem.replace "/" "_").replace "." "") ++ ".json")).toString
  IO.eprintln s!"running tryAtEachStep on {p.toString}"
  IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "tryAtEachStep",
              config.tac,
              p.toString,
              "--outfile", outfile]
  }

unsafe def main (config : Config) : IO Unit := do
  IO.FS.createDirAll config.outdir
  let paths ← config.directory.walkDir
  let total := paths.size
  let mut paths := (paths.filter (fun p => p.extension == some "lean")).toList
  let mut children : Array (Option (IO.Process.Child {})) := #[];
  while children.size < config.num_parallel ∧ ¬ paths.isEmpty do
    match paths with
    | [] => break
    | p :: ps =>
      paths := ps
      children := children.push (some (← spawnChild config p))

  let num_finished := 0
  while children.any Option.isSome do
     for ii in [0:children.size] do
        if let some c := children[ii]!
        then
          if let some ret ← c.tryWait
          then
            IO.eprintln s!"child finished with code {ret}. Progress: {num_finished} / {total}"
            children := children.set! ii none
            if let p :: ps := paths then
              paths := ps
              children := children.set! ii (some (← spawnChild config p))
            pure ()
        pure ()
     IO.sleep 50 -- don't spend too much cpu busy-waiting
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
