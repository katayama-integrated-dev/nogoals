/-
  HTML validation via `html-validate` — fail closed at the process boundary.

  NoGoals emits HTML from typed trees; the tree grammar is a theorem. But the
  HTML still has to land in browsers, where reality is messier than the
  grammar models — duplicate IDs across fragments, missing `alt` text,
  attribute typos in a raw slot. This module runs the pinned `html-validate`
  executable the consumer installed and promotes its JSON report to typed
  results.

  Everything that could make a broken run look clean is an error:
  - the executable is the caller's pinned binary, not `npx` resolving
    ambient state;
  - exit codes other than 0 (clean) and 1 (findings) fail;
  - the JSON is decoded strictly: every required field present and of the
    right type, severities only 1 (warning) or 2 (error), per-file counts
    equal to the messages they summarize;
  - every reported file must be one that was requested, reported once.

  html-validate's JSON formatter OMITS clean files, so "no result" cannot
  be told from "not processed" by the output alone. Every run therefore
  includes a CANARY — a deliberately broken document written into the
  requested files' own directory — and the run is accepted only if the
  canary's errors were reported: whatever would drop the requested files
  (an ignore file, an extension filter) drops the canary too. Requested
  files must exist. There is no "skip with warning" mode.
-/

import Lean.Data.Json
import NoGoals.IR.Route
import NoGoals.Verify.Json

namespace NoGoals.Verify.HtmlValidate

open Lean (Json)

/-- A single validation issue reported by html-validate. -/
structure Issue where
  filePath : String
  line     : Nat
  column   : Nat
  ruleId   : String
  message  : String
  /-- `"error"` (severity 2) or `"warning"` (severity 1). -/
  severity : String
deriving Repr, Inhabited

/-- Per-file aggregate: `{ filePath, errorCount, warningCount, messages }`. -/
structure FileResult where
  filePath     : String
  errorCount   : Nat
  warningCount : Nat
  issues       : List Issue
deriving Repr, Inhabited

structure Summary where
  totalFiles      : Nat
  filesWithErrors : Nat
  totalErrors     : Nat
  totalWarnings   : Nat
  failures        : List FileResult
deriving Repr, Inhabited

/-! ## Strict JSON decoding -/

open NoGoals.Verify.Json (parse getStr getNat)
open NoGoals (dupes)

private def parseIssue (filePath : String) (ctx : String) (j : Json) : Except String Issue := do
  let line ← getNat j "line" ctx
  let column ← getNat j "column" ctx
  let ruleId ← getStr j "ruleId" ctx
  let message ← getStr j "message" ctx
  let sev ← getNat j "severity" ctx
  let severity ← match sev with
    | 2 => pure "error"
    | 1 => pure "warning"
    | n => throw s!"{ctx}: severity {n} is not 1 (warning) or 2 (error)"
  pure { filePath, line, column, ruleId, message, severity }

private def parseFileResult (j : Json) : Except String FileResult := do
  let filePath ← getStr j "filePath" "result"
  let ctx := s!"result for {filePath}"
  let errorCount ← getNat j "errorCount" ctx
  let warningCount ← getNat j "warningCount" ctx
  let messages ← match j.getObjVal? "messages" with
    | .ok (.arr a) => pure a.toList
    | .ok _ => throw s!"{ctx}: `messages` must be an array"
    | .error _ => throw s!"{ctx}: missing `messages`"
  let issues ← messages.zipIdx.mapM fun (m, i) => parseIssue filePath s!"{ctx} message {i}" m
  let errors := issues.filter (·.severity == "error") |>.length
  let warnings := issues.filter (·.severity == "warning") |>.length
  unless errorCount == errors do
    throw s!"{ctx}: errorCount {errorCount} but {errors} error message(s)"
  unless warningCount == warnings do
    throw s!"{ctx}: warningCount {warningCount} but {warnings} warning message(s)"
  pure { filePath, errorCount, warningCount, issues }

/-- Decode html-validate's `--formatter=json` output: a top-level array with
    at most one result per requested file (clean files are omitted by the
    tool), and the canary's result PRESENT with at least one error. The
    canary is removed from the returned results. -/
def parseOutput (expectedFiles : List String) (canary : String) (stdout : String) :
    Except String (List FileResult) := do
  let j ← parse "html-validate output" stdout
  let arr ← match j.getArr? with
    | .ok a => pure a.toList
    | .error _ => throw "html-validate output is not a JSON array"
  let results ← arr.mapM parseFileResult
  let paths := results.map (·.filePath)
  match dupes paths with
  | p :: _ => throw s!"html-validate reported {p} more than once"
  | [] => pure ()
  for p in paths do
    unless expectedFiles.contains p || p == canary do
      throw s!"html-validate reported an unrequested file {p}"
  match results.find? (·.filePath == canary) with
  | none => throw "html-validate did not report the canary: the tool skipped its inputs"
  | some c =>
    unless c.errorCount > 0 do throw "html-validate reported the broken canary as clean"
  pure (results.filter (·.filePath != canary))

/-! ## Tool invocation -/

/-- A document no configuration accepts: unclosed `<p>`, stray `</div>`. -/
def canaryHtml : String := "<!DOCTYPE html><html><body><p><p></div></body></html>"

/-- Run the given `html-validate` executable over `files` plus a canary
    written INTO `canaryDir` — the directory the requested files live in —
    so any rule that would silently drop those files (an ignore file, an
    extension filter, a glob) drops the canary too and the run fails.
    Requested files must exist; paths are resolved to absolute form before
    the call because html-validate reports absolute paths.
    `.error` on any tool or schema failure or a missing canary result;
    `.ok` carries the results for `files` (clean files omitted, as the tool
    does), keyed by the ORIGINAL request strings. -/
def validate (exe : String) (files : List String) (canaryDir : System.FilePath) :
    IO (Except String (List FileResult)) := do
  if files.isEmpty then
    return .ok []
  for f in files do
    unless ← (System.FilePath.mk f).pathExists do
      return .error s!"requested file does not exist: {f}"
  let absOf : List (String × String) ← files.mapM fun (f : String) => do
    pure (f, (← IO.FS.realPath (System.FilePath.mk f)).toString)
  let canaryFile := canaryDir / ".NoGoals-html-validate-canary.html"
  IO.FS.writeFile canaryFile canaryHtml
  let canary := (← IO.FS.realPath canaryFile).toString
  -- The report goes to a FILE, not a pipe: Node exits without draining a
  -- pipe beyond 64 KiB, which truncates large reports mid-JSON.
  let outFile := canaryDir / ".NoGoals-html-validate-out.json"
  let result ← (IO.Process.output {
    cmd  := "/bin/sh"
    args := #["-c", "exec \"$0\" \"$@\" > \"$NOGOALS_HV_OUT\"", exe, "--formatter=json"] ++
      (absOf.map (·.2)).toArray ++ #[canary]
    env := #[("NOGOALS_HV_OUT", some outFile.toString)]
  } : IO IO.Process.Output).toBaseIO
  IO.FS.removeFile canaryFile
  let stdout ← (IO.FS.readFile outFile).toBaseIO
  let _ ← (IO.FS.removeFile outFile).toBaseIO
  match result, stdout with
  | .error e, _ => return .error s!"failed to spawn `{exe}`: {e}"
  | .ok _, .error e => return .error s!"`{exe}` produced no report: {e}"
  | .ok out, .ok stdout =>
    -- The canary guarantees findings, so 1 is the only clean exit; anything
    -- else is the tool failing (0 means it did not even see the canary).
    if out.exitCode != 1 then
      return .error s!"`{exe}` exited {out.exitCode} (expected 1: findings from the canary); stderr: {out.stderr.take 500}"
    match parseOutput (absOf.map (·.2)) canary stdout with
    | .error e => return .error e
    | .ok results =>
      -- Report under the caller's names.
      return .ok (results.map fun r =>
        { r with filePath := ((absOf.find? (·.2 == r.filePath)).map (·.1)).getD r.filePath })

/-! ## Summarization & rendering -/

def summarize (results : List FileResult) : Summary :=
  let totalFiles      := results.length
  let totalErrors     := results.foldl (fun n r => n + r.errorCount) 0
  let totalWarnings   := results.foldl (fun n r => n + r.warningCount) 0
  let failures        := results.filter (·.errorCount > 0)
  let filesWithErrors := failures.length
  { totalFiles, filesWithErrors, totalErrors, totalWarnings, failures }

private def formatIssue (i : Issue) : String :=
  s!"      [{i.severity}] {i.ruleId} ({i.line}:{i.column}): {i.message}"

private def formatFailure (r : FileResult) : String :=
  let header := s!"  ✗ {r.filePath} — {r.errorCount} error(s), {r.warningCount} warning(s)"
  String.intercalate "\n" (header :: r.issues.map formatIssue)

def formatSummary (s : Summary) : String :=
  if s.totalErrors = 0 ∧ s.totalWarnings = 0 then
    s!"✓ html-validate: {s.totalFiles} file(s) clean"
  else if s.totalErrors = 0 then
    s!"✓ html-validate: {s.totalFiles} file(s), 0 error(s), {s.totalWarnings} warning(s)"
  else
    let head := s!"✗ html-validate: {s.filesWithErrors}/{s.totalFiles} file(s) with errors " ++
                s!"({s.totalErrors} total error(s), {s.totalWarnings} warning(s))"
    String.intercalate "\n" (head :: s.failures.map formatFailure)

end NoGoals.Verify.HtmlValidate
