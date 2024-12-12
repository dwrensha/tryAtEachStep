/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Lean

namespace TryAtEachStepInDirectory

structure Config where
  tac : String := "exact?"
  directory : System.FilePath := ""
  outdir : Option System.FilePath := .none
  additionalImports : List String := []

unsafe def main (config : Config) : IO Unit := do
  let paths ← config.directory.walkDir
  let paths := paths.filter (fun p => p.extension == some "lean" )
  IO.println s!"paths = {paths}"
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
  IO.println "hello world"
  pure ()
