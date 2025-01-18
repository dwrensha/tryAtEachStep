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
  help : Bool := false
  tac : String := "exact?"
  infile : FilePath := "."
  outfile : Option FilePath := .none
  doneIfOutfileAlreadyExists : Bool := false
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
  ci: ContextInfo
  ti: TacticInfo

/--
A textual tactic step in a proof. May represent multiple actual
executions of the tactic, e.g. after `all_goals` or `<;>`.
-/
structure Step where
  /-- environment from before the current command -/
  env: Environment

  stx: Syntax

  /-- Syntax of the enclosing tacticSeq1Indented node, if there is one. -/
  seqStx : Option Syntax

  focused_steps: List FocusedStep

abbrev StepMap := RBMap Span Step Ord.compare
abbrev SpanSet := RBMap Span Unit Ord.compare

def StepMap.empty : StepMap := RBMap.empty

def StepMap.maybe_add (sm : StepMap) (env : Environment)
    (ci : ContextInfo) (ti : TacticInfo) (seqStx : Option Syntax) : StepMap := Id.run do
  let some span := Span.ofSyntax ti.stx | return sm
  let fs : FocusedStep := ⟨ci, ti⟩
  match sm.find? span with
  | some step =>
    let step' := {step with focused_steps := step.focused_steps ++ [fs]}
    return sm.insert span step'
  | none => return sm.insert span {
      env
      stx := ti.stx
      seqStx := seqStx
      focused_steps := [fs]
    }

def visitTacticInfo (env : Environment) (ci : ContextInfo)
    (ti : TacticInfo) (seqStx : Option Syntax) (step_map: StepMap) :
    StepMap := Id.run do
  if not ti.isSubstantive then return step_map
  if let .some (.synthetic ..) := ti.stx.getHeadInfo? then
     -- Not actual concrete syntax the user wrote. Ignore.
     return step_map
  return StepMap.maybe_add step_map env ci ti seqStx

def visitInfo (env : Environment) (ci : ContextInfo)
    (info : Info) (seqStx : Option Syntax) (step_map : StepMap)
    : StepMap :=
  match info with
  | .ofTacticInfo ti => visitTacticInfo env ci ti seqStx step_map
  | _ => step_map

partial def InfoTree.foldInfo' {α : Type} (f : ContextInfo → Info → (Option Syntax) → α → α)
    (init : α) : InfoTree → α :=
  go none none init
where go ctx? seqStx a
  | .context ctx t => go (ctx.mergeIntoOuter? ctx?) seqStx a t
  | .node i ts =>
    let a := match ctx? with
      | none => a
      | some ctx => f ctx i seqStx a
    let newSeqStx : Option Syntax := match i with
    | .ofTacticInfo ti =>
      if let some ``Lean.Parser.Tactic.tacticSeq1Indented := ti.name?
      then ti.stx
      else seqStx
    | _ => seqStx
    ts.foldl (init := a) (go (i.updateContext? ctx?) newSeqStx)
  | .hole _ => a

def traverseForest (steps : List (Environment × InfoState)) : StepMap := Id.run do
  let mut step_map := StepMap.empty
  for (env, infoState) in steps do
    for t in infoState.trees.toList do
        step_map := InfoTree.foldInfo' (visitInfo env) step_map t
  return step_map

/-- The result of trying a new tactic at a tactic step.
-/
structure TryTacticResult where
  filepath : String

  /-- The position in the file where the tactic step occurs. -/
  startLine : Nat
  startCol : Nat

  /-- The original tactic syntax as a string. -/
  oldText : String

  /-- The new tactic syntax as a string. -/
  newText : String

  /-- The old tactic plus the remaining tactics in the branch, as a string.-/
  oldToEndOfBranch : String := ""

  /-- The name of the declaration that is being elaborated. -/
  parentName : String

  /-- True is the goal is a proposition. -/
  goalIsProp : Bool

  /-- The original term that resulted from fully elaborating this step. -/
  oldProof : String

  /-- The new term. -/
  newProof : String

  /-- The number of steps the proof is shortened by. -/
  shortenedStepsCount: Nat

  /-- Message logged by the new tactic (e.g. 'try this ...'). -/
  message : Option String
deriving Lean.ToJson

def stringOfTerm (e : Expr) (mctx : MetavarContext) (g : MVarId) : CoreM String := do
  let mnd : MetaM String := g.withContext do
        let pe ← PrettyPrinter.ppExpr e
        return Std.Format.pretty pe
  let (s, _) ← mnd.run {} { mctx := mctx }
  return s

/-- Returns true if the goal has unassigned mvars in its hypothesis or its target type. -/
def hasUnassignedMVars (mctx : MetavarContext) (g : MVarId) : MetaM Bool := do
  let go : MetaM Bool := g.withContext  do
    let a ← Lean.Meta.getMVars (← g.getType)
    if a.size > 0 then
      return true
    for d in ← getLCtx do
      if !d.isImplementationDetail then
        let a ← Lean.Meta.getMVars d.type
        if a.size > 0 then
          return true
    return false
  let (b, _) ← go.run {} { mctx := mctx }
  return b

def tryTactic (config : Config) (tryTacticStx : Syntax) (span : Span) (step : Step) :
    IO (Option TryTacticResult) := do
  -- For now, we ignore cases where a tactic applies to multiple goals simultaneously.
  let [{ci, ti}] := step.focused_steps | do IO.eprint "_"; return none

  let some parentName := ci.parentDecl? | return none

  ci.runMetaM default do

  setEnv step.env
  let src := ci.fileMap.source

  let startPosition := ci.fileMap.toPosition span.startPos
  let s := Substring.mk src span.startPos span.endPos
  let [g] := ti.goalsBefore | return none
  if ← hasUnassignedMVars ti.mctxBefore g then return none

  let mut newResult : Option TryTacticResult := .none
  IO.eprint "."
  (← IO.getStderr).flush
  let mctx := ti.mctxBefore
  let goalIsProp : MetaM Bool := do
     g.withContext do
     try
       let ty ← g.getType
       let ty ← instantiateMVars ty
       Meta.isProp ty
     catch _ =>
       return false
  let goalIsProp ← goalIsProp.run' (s := { mctx := mctx })
  let dotac := Term.TermElabM.run' (ctx := {declName? := ci.parentDecl?})
                    <| Tactic.run g (Tactic.evalTactic tryTacticStx)
  let (mvars, after_state) ← try
      dotac.run {} { mctx := mctx }
     catch _e =>
      --println! "caught: {←e.toMessageData.toString}"
      return none
  let msgs := (← liftM (m := CoreM) get).messages
  if msgs.hasErrors then
    IO.eprint "X"
    return none
  if mvars.length == 0
  then
    let (e1, e2) ← match ti.mctxAfter.getExprAssignmentExp g,
                   after_state.mctx.getExprAssignmentExp g with
     | some e1, some e2 =>
        if e1 == e2 then
          IO.eprint "="
          return none
        else
          pure (e1, e2)
     | _, _ => return none
    IO.eprintln s!"\nline {startPosition.line}, col {startPosition.column}:\n{s}"
    let mut message := ""
    for msg in msgs.toList do
      IO.eprintln s!"* {←msg.data.toString}"
      message := message ++ s!"{←msg.data.toString}"
    if 0 < ti.goalsAfter.length then
      IO.eprintln s!"shortened proof by {ti.goalsAfter.length} \
      step{if 1 < ti.goalsAfter.length then "s" else ""}"
    let e1' ← stringOfTerm e1 ci.mctx g
    let e2' ← stringOfTerm e2 after_state.mctx g

    let oldText := s!"{s}"
    let mut oldToEndOfBranch := oldText
    if let some seqStx := step.seqStx then
      if let some tp := seqStx.getTailPos? then
        oldToEndOfBranch := (Substring.mk src span.startPos tp).toString

    let result : TryTacticResult := {
      filepath := config.infile.toString
      parentName := parentName.toString
      goalIsProp
      startLine := startPosition.line
      startCol := startPosition.column
      oldText
      newText := config.tac
      oldToEndOfBranch
      oldProof := e1'
      newProof := e2'
      shortenedStepsCount := ti.goalsAfter.length
      message
    }
    newResult := result
  let traceState := (← liftM (m := CoreM) get).traceState
  for t in traceState.traces.toList do
    IO.eprintln s!"> {←t.msg.toString}"

  return newResult

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
    IO.eprintln s!"failed to parse {str}: {errorMsg}"
    panic! "parse error"
  | none =>
    pure (if s.stxStack.isEmpty then .missing else s.stxStack.back)

def tryTacticAtSteps (config : Config) (tryTacticStx : Syntax) (step_map : StepMap) :
    IO (List TryTacticResult) := do
  let mut results := []
  let mut proved_branches : SpanSet := RBMap.empty
  for (span, step) in step_map do
    let seqSpan := if let .some seqStx := step.seqStx
                   then Span.ofSyntax seqStx
                   else none

    if let .some sp := seqSpan
    then
      -- Determine whether we've already proven a branch that subsumes this one.
      -- TODO: do this in a more efficient way.
      let mut skipThisOne := false
      for (k, ()) in proved_branches do
        if k.startPos ≤ sp.startPos ∧ sp.endPos ≤ k.endPos then
          skipThisOne := true
          break
      if skipThisOne then
        continue -- we've already proved this branch

    try
      if let .some res ← tryTactic config tryTacticStx span step then
         results := results ++ [res]
         if let .some sp := seqSpan
         then proved_branches := proved_branches.insert sp ()

    catch e =>
      IO.eprintln s!"{e}"
  return results

unsafe def processFile (config : Config) : IO Unit := do
  if let .some outfile := config.outfile then
    if (← outfile.pathExists) ∧ config.doneIfOutfileAlreadyExists then
      IO.eprintln s!"Already done because outfile {outfile} already exists."
      return ()

  searchPathRef.set compile_time_search_path%
  let mut input ← IO.FS.readFile config.infile
  for im in config.additionalImports do
    input := "import " ++ im ++ "\n" ++ input
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input config.infile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        IO.eprintln s!"ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let tryTacticStx ← parseTactic env config.tac

  let env := env.setMainModule (← moduleNameOfFileName config.infile none)
  let opts : Options := Options.empty.insert `maxHeartbeats (DataValue.ofNat 1000000)
  let commandState := { Command.mkState env messages opts with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  let results ← tryTacticAtSteps config tryTacticStx (traverseForest steps)
  if let .some outfile := config.outfile then
    IO.FS.writeFile outfile s!"{Lean.toJson results}\n"
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
    if args[idx]! == "--help"
    then
      return {cfg with help := true}
    else if args[idx]! == "--imports"
    then
      idx := idx + 1
      let imports := args[idx]!.splitOn ","
      cfg := {cfg with additionalImports := imports}
    else if args[idx]! == "--outfile"
    then
      idx := idx + 1
      cfg := {cfg with outfile := args[idx]!}
    else if args[idx]! == "--done-if-outfile-already-exists"
    then
      idx := idx + 1
      let v ← match args[idx]! with
      | "true" => pure true
      | "false" => pure false
      | _ => throw $ IO.userError s!"failed to parse bool from {args[idx]!}"
      cfg := {cfg with doneIfOutfileAlreadyExists := v}
    else if positional_count == 0
    then
      let tac := args[idx]!
      cfg := {cfg with tac := tac}
      positional_count := positional_count + 1
    else if positional_count == 1
    then
      let infile := (← toAbsolute ⟨args[idx]!⟩)
      cfg := {cfg with infile := infile}
      positional_count := positional_count + 1
    else
      throw $ IO.userError "too many positional arguments!"

    idx := idx + 1
    pure ()

  if positional_count != 2
  then
    throw $ IO.userError "usage: tryAtEachStep [OPTIONS] TACTIC LEAN_FILE"
  return cfg

def helpMessage : String :=
"tryAtEachStep: run a tactic at each proof step in a .lean file

  tryAtEachStep [OPTIONS] TACTIC LEAN_FILE

  Options:
    --outfile OUTFILE                   output JSON file
    --done-if-outfile-already-exists    exit early if outfile already exists
    --imports IMPORTS                   inject import statements for modules from this comma-separated list

"

end TryAtEachStep

unsafe def main (args : List String) : IO Unit := do
  let cfg ← TryAtEachStep.parseArgs args.toArray
  if cfg.help then
    IO.eprintln TryAtEachStep.helpMessage
    return
  TryAtEachStep.processFile cfg
