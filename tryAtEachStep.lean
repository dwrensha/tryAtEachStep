/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Lean

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
  | some ``Lean.Parser.Tactic.inductionAlt => false
  | some ``Lean.Parser.Tactic.case => false
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

instance : Lean.ToJson String.Pos where
  toJson x := x.1

structure Span where
  startPos: String.Pos
  endPos: String.Pos
deriving BEq, Hashable, Lean.ToJson

instance : Ord Span where
 compare sp1 sp2 := match sp1, sp2 with
 | ⟨s1, e1⟩, ⟨s2, e2⟩ =>
   match Ord.compare s1.1 s2.1 with
   | .lt => .lt
   | .gt => .gt
   | .eq =>
     -- we want bigger spans to come first
     match Ord.compare e1.1 e2.1 with
     | .lt => .gt
     | .gt => .lt
     | .eq => .eq

def Span.ofSyntax (stx: Syntax) : Option Span := do
  let startPos ← stx.getPos?
  let endPos ← stx.getTailPos?
  return ⟨startPos, endPos⟩

/-- An individual execution of a tactic. -/
structure FocusedStep where
  /-- environment from before the current command -/
  env: Environment

  ci: ContextInfo
  ti: TacticInfo

/--
A textual tactic step in a proof. May represent multiple actual
executions of the tactic, e.g. after `all_goals` or `<;>`.
-/
structure Step where
  stx: Syntax
  focused_steps: List FocusedStep

abbrev StepMap := RBMap Span Step Ord.compare

def StepMap.empty : StepMap := RBMap.empty

def StepMap.maybe_add (sm : StepMap) (env : Environment)
    (ci : ContextInfo) (ti : TacticInfo) : StepMap := Id.run do
  let some span := Span.ofSyntax ti.stx | return sm
  let fs : FocusedStep := ⟨env, ci, ti⟩
  match sm.find? span with
  | some step =>
    let step' := {step with focused_steps := step.focused_steps ++ [fs]}
    return sm.insert span step'
  | none => return sm.insert span ⟨ti.stx, [fs]⟩

def visitTacticInfo (env : Environment) (ci : ContextInfo) (ti : TacticInfo) (step_map: StepMap) :
    StepMap := Id.run do
  if not ti.isSubstantive then return step_map
  if let .some (.synthetic ..) := ti.stx.getHeadInfo? then
     -- Not actual concrete syntax the user wrote. Ignore.
     return step_map
  return StepMap.maybe_add step_map env ci ti

def visitInfo (env : Environment) (ci : ContextInfo)
    (info : Info) (step_map : StepMap)
    : StepMap :=
  match info with
  | .ofTacticInfo ti => visitTacticInfo env ci ti step_map
  | _ => step_map

def traverseForest (steps : List (Environment × InfoState)) : StepMap := Id.run do
  let mut step_map := StepMap.empty
  for (env, infoState) in steps do
    for t in infoState.trees.toList do
        step_map := Lean.Elab.InfoTree.foldInfo (visitInfo env) step_map t
  return step_map

structure TryTacticResult where
  filepath : String
  startLine : Nat
  startCol : Nat
  originalText : String
  oldProofLength : Nat
  newProofLength : Nat
  lengthReduction : Int
  fewerSteps: Bool
  message : Option String
deriving Lean.ToJson

def stringOfTerm (e : Expr) (mctx : MetavarContext) : CoreM String := do
  let mnd : MetaM String := do
      let e' ← instantiateMVars e
      return s!"{e'}"
  let (s, _) ← mnd.run {} { mctx := mctx }
  return s

def tryTactic (config : Config) (tryTacticStx : Syntax) (span : Span) (step : Step) :
    IO (List TryTacticResult) := do
  -- For now, we ignore cases where a tactic applies to multiple goals simultaneously.
  let [{ci, ti, env}] := step.focused_steps | do IO.eprint "_"; return []

  ci.runMetaM default do
  let mut results := []

  setEnv env
  let src := ci.fileMap.source

  let startPosition := ci.fileMap.toPosition span.startPos
  let s := Substring.mk src span.startPos span.endPos
  for g in ti.goalsBefore do
    let mut newResult : Option TryTacticResult := .none
    IO.eprint "."
    (← IO.getStderr).flush
    let mctx := ti.mctxBefore
    --let doprint : MetaM _ := Meta.ppGoal g
    --let x ← doprint.run' (s := { mctx := mctx })
    --IO.println x
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
                      <| Tactic.run g (Tactic.evalTactic tryTacticStx)
    let ((mvars, _tstate), after_state) ← try
        dotac.run {} { mctx := mctx }
       catch _e =>
        --println! "caught: {←e.toMessageData.toString}"
        continue
    let msgs := (← liftM (m := CoreM) get).messages
    if mvars.length == 0
    then
      let (e1, e2) ← match ti.mctxAfter.getExprAssignmentExp g,
                     after_state.mctx.getExprAssignmentExp g with
       | some e1, some e2 =>
          if e1 == e2 then
            IO.eprint "="
            continue
          else
            pure (e1, e2)
       | _, _ => continue
      IO.eprintln s!"\nline {startPosition.line}, col {startPosition.column}:\n{s}"
      let mut message := ""
      for msg in msgs.toList do
        IO.eprintln s!"* {←msg.data.toString}"
        message := message ++ s!"{←msg.data.toString}"
      let fewerSteps := 0 < ti.goalsAfter.length
      if fewerSteps then
        IO.eprintln "shortened proof!"
      let e1' ← stringOfTerm e1 ci.mctx
      let e2' ← stringOfTerm e2 after_state.mctx
      let oldProofLength := s!"{e1'}".length
      let newProofLength := s!"{e2'}".length

      let result : TryTacticResult := {
        filepath := config.probfile.toString
        startLine := startPosition.line
        startCol := startPosition.column
        originalText := s!"{s}"
        oldProofLength
        newProofLength
        lengthReduction := (oldProofLength : Int) - (newProofLength : Int)
        fewerSteps
        message
      }
      newResult := result
    let traceState := (← liftM (m := CoreM) get).traceState
    for t in traceState.traces.toList do
      IO.eprintln s!"> {←t.msg.toString}"

    if let .some nr := newResult
    then results := nr :: results
  return results

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
    println! "failed to parse {str}: {errorMsg}"
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
        IO.eprintln s!"ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← moduleNameOfFileName config.probfile none)
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  let step_map := traverseForest steps
  let mut results := []
  for (span, step) in step_map do
    let res ← tryTactic config tryTacticStx span step
    results := results ++ res
    pure ()
    --println! step.stx
  IO.println s!"{Lean.toJson results}"
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
