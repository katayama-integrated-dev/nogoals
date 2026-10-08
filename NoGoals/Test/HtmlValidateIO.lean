/-
  Process-boundary tests for the html-validate wrapper.

  Fake executables stand in for the tool: each writes a scripted stdout
  and exits with a scripted code. The wrapper must refuse every way a
  broken run could look clean — bad exit code, missing result, duplicate
  result, inconsistent counts, non-JSON — and accept exactly the clean
  shape. Run: `lake exe nogoals-test-io` (part of `lake script run test`).
-/

import NoGoals.Verify.HtmlValidate

open NoGoals.Verify.HtmlValidate

def writeFake (dir : System.FilePath) (name stdout : String) (exitCode : Nat) : IO String := do
  let path := dir / name
  IO.FS.writeFile path s!"#!/bin/sh\ncat <<'JSON'\n{stdout}\nJSON\nexit {exitCode}\n"
  let _ ← IO.Process.run { cmd := "chmod", args := #["+x", path.toString] }
  pure path.toString

def resultJson (file : String) (errorCount : Nat) (sev : Nat) : String :=
  s!"\{\"filePath\":\"{file}\",\"errorCount\":{errorCount},\"warningCount\":0,\"messages\":[\{\"line\":1,\"column\":1,\"ruleId\":\"r\",\"message\":\"m\",\"severity\":{sev}}]}"

def expectOk (label : String) (r : Except String (List FileResult)) : IO Bool := do
  match r with
  | .ok _ => IO.println s!"  ✓ {label}"; pure true
  | .error e => IO.println s!"  ✗ {label}: unexpectedly rejected: {e}"; pure false

def expectError (label : String) (r : Except String (List FileResult)) : IO Bool := do
  match r with
  | .ok _ => IO.println s!"  ✗ {label}: unexpectedly accepted"; pure false
  | .error e => IO.println s!"  ✓ {label} ({e.take 80})"; pure true

/-- A fake tool that echoes a scripted body but ALSO reports the canary it
    was handed (the last argument) — the shape of a tool that processed its
    inputs. `canaryErrors` = 0 simulates a tool that calls the broken
    canary clean. -/
def writeFakeWithCanary (dir : System.FilePath) (name body : String) (exitCode : Nat)
    (canaryErrors : Nat := 1) : IO String := do
  let path := dir / name
  let sev := if canaryErrors > 0 then 2 else 1
  let warn := if canaryErrors > 0 then 0 else 1
  let canaryJson := resultJson "@CANARY@" canaryErrors sev
  let canaryJson := if canaryErrors > 0 then canaryJson
    else canaryJson.replace "\"warningCount\":0" s!"\"warningCount\":{warn}"
  let sep := if body.isEmpty then "" else ","
  -- The last argument is the canary path; substitute it into the scripted body.
  IO.FS.writeFile path s!"#!/bin/sh\nfor last; do :; done\ncat <<'JSON' | sed \"s#@CANARY@#$last#\"\n[{body}{sep}{canaryJson}]\nJSON\nexit {exitCode}\n"
  let _ ← IO.Process.run { cmd := "chmod", args := #["+x", path.toString] }
  pure path.toString

def main : IO UInt32 := do
  let tmp ← IO.Process.run { cmd := "mktemp", args := #["-d"] }
  -- html-validate reports canonical absolute paths; the fakes echo what
  -- they are handed, so the fixture directory is canonical too.
  let dir : System.FilePath ← IO.FS.realPath tmp.trimAscii.toString
  -- Requested files must exist; create them in the temp dir, which is also
  -- where the canary is written.
  let files := [(dir / "a.html").toString, (dir / "b.html").toString]
  for f in files do IO.FS.writeFile f "<!DOCTYPE html><html><head><title>t</title></head><body></body></html>"
  let mut ok := true
  IO.println "html-validate wrapper — process boundary"
  ok := (← expectOk "exit 1 with findings for one file, the other clean (omitted), canary reported"
    (← validate (← writeFakeWithCanary dir "hv-ok" (resultJson (dir / "a.html").toString 1 2) 1) files dir)) && ok
  ok := (← expectOk "exit 1, every requested file clean (omitted), canary reported"
    (← validate (← writeFakeWithCanary dir "hv-clean" "" 1) files dir)) && ok
  ok := (← expectError "exit 0: the tool never saw the canary (inputs skipped)"
    (← validate (← writeFake dir "hv-zero" "[]" 0) files dir)) && ok
  ok := (← expectError "exit 1 but no canary result: inputs skipped"
    (← validate (← writeFake dir "hv-nocanary" s!"[{resultJson (dir / "a.html").toString 1 2}]" 1) files dir)) && ok
  ok := (← expectError "the broken canary reported clean"
    (← validate (← writeFakeWithCanary dir "hv-canaryclean" "" 1 0) files dir)) && ok
  ok := (← expectError "exit 2 is a tool failure even with plausible output"
    (← validate (← writeFakeWithCanary dir "hv-exit2" (resultJson (dir / "a.html").toString 1 2) 2) files dir)) && ok
  ok := (← expectError "a duplicate result"
    (← validate (← writeFakeWithCanary dir "hv-dup" s!"{resultJson (dir / "a.html").toString 1 2},{resultJson (dir / "a.html").toString 1 2}" 1) [files.head!] dir)) && ok
  ok := (← expectError "an unrequested file"
    (← validate (← writeFakeWithCanary dir "hv-extra" (resultJson "z.html" 1 2) 1) [files.head!] dir)) && ok
  ok := (← expectError "errorCount inconsistent with messages"
    (← validate (← writeFakeWithCanary dir "hv-count" (resultJson (dir / "a.html").toString 0 2) 1) [files.head!] dir)) && ok
  ok := (← expectError "unknown severity"
    (← validate (← writeFakeWithCanary dir "hv-sev" (resultJson (dir / "a.html").toString 1 7) 1) [files.head!] dir)) && ok
  ok := (← expectError "non-JSON output"
    (← validate (← writeFake dir "hv-garbage" "Segmentation fault" 1) [files.head!] dir)) && ok
  ok := (← expectError "missing executable"
    (← validate (dir / "does-not-exist").toString [files.head!] dir)) && ok
  ok := (← expectError "a requested file that does not exist"
    (← validate (← writeFakeWithCanary dir "hv-nofile" "" 1) [(dir / "nope.html").toString] dir)) && ok
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", dir.toString] }
  if ok then
    IO.println "✅ html-validate wrapper fails closed at every boundary."
    pure 0
  else
    IO.println "❌ html-validate wrapper accepted a broken run."
    pure 1
