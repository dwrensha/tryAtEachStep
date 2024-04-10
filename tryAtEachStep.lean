/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Lean
import Std.Lean.Util.Path

/-!
Tool to try running a tactic (like `exact?` or `rw_search`) at every
proof step in a given file.
-/

open Lean Elab System

namespace Lean.Elab.TacticInfo

-- We borrow some stuff from
-- https://github.com/semorrison/lean-training-data/blob/master/TrainingData/InfoTree/Basic.lean
-- and
-- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none


/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

end Lean.Elab.TacticInfo

namespace TryAtEachStep

structure Config where
  tac : String := "exact?"
  probfile : FilePath := "."
  additionalImports : List String := []

def visitTacticInfo (tryTacticStx : Syntax) (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSubstantive then return ()
  let src := ci.fileMap.source
  let stx := ti.stx
  match stx.getHeadInfo? with
  | .some (.synthetic ..) =>
     -- Not actual concrete syntax the user wrote. Ignore.
    return ()
  | _ =>  pure ()
  let some sp := stx.getPos? | return ()
  let some ep := stx.getTailPos? | return ()
  let startPosition := ci.fileMap.toPosition sp
  let s := Substring.mk src sp ep
  for g in ti.goalsBefore do
    IO.print "."
    (← IO.getStdout).flush
    let mctx := ti.mctxBefore
    --let doprint : MetaM _ := Meta.ppGoal g
    --let x ← doprint.run' (s := { mctx := mctx })
    --IO.println x
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
                      <| Tactic.run g (Tactic.evalTactic tryTacticStx)
    try
      let ((mvars, _tstate), _mstate) ← dotac.run {} { mctx := mctx }
      let msgs := (← liftM (m := CoreM) get).messages
      if mvars.length == 0
      then
        println! "\nline {startPosition.line}, col {startPosition.column}:\n{s}"
        for msg in msgs.toList do
          println! "* {←msg.data.toString}"
        if 0 < ti.goalsAfter.length then
          println! "shortened proof!"
      let traceState := (← liftM (m := CoreM) get).traceState
      for t in traceState.traces.toList do
        println! "> {←t.msg.toString}"

      pure ()
    catch _e =>
      --println! "caught: {←e.toMessageData.toString}"
      pure ()

    pure ()

def visitInfo (tryTacticStx : Syntax) (env : Environment) (ci : ContextInfo)
    (info : Info) (acc : List (IO Unit))
    : List (IO Unit) :=
  match info with
  | .ofTacticInfo ti =>
    (ci.runMetaM default
     (do setEnv env
         try visitTacticInfo tryTacticStx ci ti
         catch e =>
            println! "caught: {←e.toMessageData.toString}")) :: acc
  | _ => acc

def traverseForest (tryTacticStx : Syntax) (steps : List (Environment × InfoState)) : List (IO Unit) :=
  let t := steps.map fun (env, infoState) ↦
    (infoState.trees.toList.map fun t ↦
      (Lean.Elab.InfoTree.foldInfo (visitInfo tryTacticStx env) [] t).reverse)
  t.join.join

partial def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  let env := (←get).commandState.env
  let done ← Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env, infoState)]
  else
    return (env, infoState) :: (←processCommands)

def parseTactic (env : Environment) (str : String) : IO Syntax := do
  let inputCtx := Parser.mkInputContext str "<argument>"
  let tokens := Parser.Module.updateTokens (Parser.getTokenTable env)
  let s := Parser.tacticParser.fn.run
              inputCtx {env := env, options := {}} tokens (Parser.mkParserState inputCtx.input)
  match s.errorMsg with
  | some errorMsg =>
    println! "parse error: {errorMsg}"
    panic! "parse error"
  | none =>
    pure (if s.stxStack.isEmpty then .missing else s.stxStack.back)

unsafe def processFile (config : Config) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let mut input ← IO.FS.readFile config.probfile
  for im in config.additionalImports do
    input := "import " ++ im ++ "\n" ++ input
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input config.probfile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  let tryTacticStx ← parseTactic env config.tac

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← moduleNameOfFileName config.probfile none)
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  for t in traverseForest tryTacticStx steps do
    try t
    catch e =>
      println! "caught top level: {e}"
  pure ()

def pathOfProbId (probId : String) : IO FilePath := do
  let path := FilePath.mk ("./Compfiles/" ++ probId ++ ".lean")
  let cwd ← IO.currentDir
  pure $ cwd / path

/--
Convert the path `path` to an absolute path.
-/
def toAbsolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path


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
    else if positional_count == 0
    then
      let tac := args[idx]!
      cfg := {cfg with tac := tac}
      positional_count := positional_count + 1
    else if positional_count == 1
    then
      let probfile := (← toAbsolute ⟨args[idx]!⟩)
      cfg := {cfg with probfile := probfile}
      positional_count := positional_count + 1
    else
      throw $ IO.userError "too many positional arguments!"

    idx := idx + 1
    pure ()

  if positional_count != 2
  then
    throw $ IO.userError "usage: tryAtEachStep [OPTIONS] TACTIC LEAN_FILE"
  return cfg

end TryAtEachStep

unsafe def main (args : List String) : IO Unit := do
  let cfg ← TryAtEachStep.parseArgs args.toArray
  TryAtEachStep.processFile cfg
