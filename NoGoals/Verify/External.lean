/-
  External link liveness checks

  NoGoals sites accumulate outbound URLs over time — citations in news articles,
  source links in attestations, references on people/products pages. Bare
  strings in the source data make no promise that the targets still resolve;
  a year later the build still ships, even though half the citations 404.

  This module shells out to `curl` at build time and produces a typed
  `CheckResult` per URL. Sites collect these into a `Summary` and lift the
  whole thing to an `Attestation` so the verification report can record
  *when* and *how* the link sweep was performed.

  ## Why shell out

  Lean 4 has no built-in HTTP client and no in-tree TLS. Re-implementing
  either inside the verified core would be a massive surface for bugs and
  a maintenance treadmill against the wider TLS / HTTP ecosystem. Shelling
  to `curl` keeps the IO at the very edge: the verified core stays pure,
  and the link check is a thin parser over `curl`'s machine-readable
  output. The trust boundary is "you have curl on the build host."

  ## Usage

  ```lean
  import NoGoals.Verify.External

  def myUrls : List String := [
    "https://example.com/about",
    "https://example.com/contact"
  ]

  def main : IO Unit := do
    let results ← NoGoals.Verify.External.headCheckAll myUrls
    for r in results do
      IO.println (NoGoals.Verify.External.formatResult r)
    let s := NoGoals.Verify.External.summarize results
    if !s.failed.isEmpty then
      IO.Process.exit 1
  ```

  Sites typically run `headCheckAll` from a CLI subcommand (not from the
  pure build pipeline), capture today's date, and write the resulting
  attestation back into `data/*.json` so subsequent pure builds can prove
  freshness via `NoGoals.Verify.Attestation.isFresh`.
-/

import NoGoals.IR.Route
import NoGoals.Verify.Date
import NoGoals.Verify.Attestation

namespace NoGoals.Verify.External

/-- Result of checking one URL. Codes are kept as `Nat` rather than a
    closed enum so we don't have to enumerate every HTTP response code;
    the bucketing into ok/redirect/clientError/serverError is sufficient
    for build-log reporting. -/
inductive Status where
  /-- 2xx — target resolved and returned a success status. -/
  | ok          (httpCode : Nat)
  /-- Followed `chainLen` redirects to a final 2xx at `finalUrl`. Passing
      only when the final URL is on the ORIGINAL origin: a same-origin hop
      (a CDN versioning its script path) is how the web works; a
      cross-origin one means the recorded URL is stale or parked. -/
  | redirect    (httpCode : Nat) (chainLen : Nat) (finalUrl : String)
  /-- 4xx — target said no (404, 403, 410, …). -/
  | clientError (httpCode : Nat)
  /-- 5xx — target's server is broken right now. Worth re-checking before
      reporting as a permanent failure. -/
  | serverError (httpCode : Nat)
  /-- The check exceeded `timeoutSec`. -/
  | timeout
  /-- DNS failure, connection refused, TLS error, malformed response, etc.
      `msg` is curl's stderr (or our parse-failure reason). -/
  | networkError (msg : String)
deriving Repr, Inhabited

/-- One URL's result, with wall-clock duration measured around the curl
    invocation. Duration is informational — the build does not gate on it. -/
structure CheckResult where
  url        : String
  status     : Status
  durationMs : Nat
deriving Repr, Inhabited

/-! ## curl invocation -/

/-- Bucket the FINAL HTTP code (after curl followed redirects) into a
    `Status`. `chainLen` is the number of redirects followed; a 3xx here
    means the chain was cut off at `--max-redirs`. -/
private def classify (httpCode : Nat) (chainLen : Nat) (finalUrl : String) : Status :=
  if httpCode = 0 then
    -- curl prints `000` when it never received a status line. Treat as
    -- network error rather than misclassifying as a 0-bucket success.
    .networkError "no HTTP status received"
  else if httpCode < 200 then
    .networkError s!"unexpected 1xx-range status {httpCode}"
  else if httpCode < 300 then
    if chainLen = 0 then .ok httpCode else .redirect httpCode chainLen finalUrl
  else if httpCode < 400 then
    .networkError s!"redirect chain longer than 5 (last status {httpCode})"
  else if httpCode < 500 then
    .clientError httpCode
  else if httpCode < 600 then
    .serverError httpCode
  else
    .networkError s!"out-of-range HTTP status {httpCode}"

/-- curl exit code 28 = "operation timeout". See `man curl`. -/
private def curlTimeoutExit : UInt32 := 28

/-- HEAD request via `curl`, following up to 5 redirects, with a hard
    wall-clock timeout. Returns one `CheckResult`. The output format
    `%{http_code}\n%{num_redirects}\n%{url_effective}` is parsed
    line-by-line; a field missing → `networkError`. -/
def headCheck (url : String) (timeoutSec : Nat := 5) : IO CheckResult := do
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := "curl"
    args := #[
      "-I", "-s", "-L", "--max-redirs", "5",
      "-o", "/dev/null",
      "-w", "%{http_code}\n%{num_redirects}\n%{url_effective}",
      "--max-time", toString timeoutSec,
      url
    ]
  }
  let t1 ← IO.monoMsNow
  let durationMs := t1 - t0
  let mkResult (status : Status) : CheckResult :=
    { url, status, durationMs }
  if out.exitCode = curlTimeoutExit then
    return mkResult .timeout
  if out.exitCode ≠ 0 then
    -- Non-zero, non-timeout: DNS, TLS, refused, etc. Prefer stderr; fall
    -- back to a generic message tagged with the exit code.
    let msg := if out.stderr.isEmpty
      then s!"curl exit {out.exitCode}"
      else out.stderr.trimAscii.toString
    return mkResult (.networkError msg)
  -- Parse stdout. Expected: "<code>\n<redirects>\n<final url>".
  match out.stdout.trimAscii.toString.splitOn "\n" with
  | [codeStr, redirStr, finalUrl] =>
      match codeStr.trimAscii.toString.toNat?, redirStr.trimAscii.toString.toNat? with
      | some code, some redirs => return mkResult (classify code redirs finalUrl.trimAscii.toString)
      | _, _ =>
          return mkResult (.networkError s!"parse failure: {out.stdout}")
  | _ =>
      return mkResult (.networkError s!"unexpected curl output: {out.stdout}")

/-- Batch check. Sequential — one curl child per URL. Sites with many URLs
    may want to parallelize with `IO.asTask`; left as future work because
    sequential is deterministic and easy to reason about in a build log. -/
def headCheckAll (urls : List String) (timeoutSec : Nat := 5)
    : IO (List CheckResult) :=
  urls.mapM (fun u => headCheck u timeoutSec)

/-! ## Reporting -/

/-- Render a `Status` for the build log. Concise on purpose: one line per
    URL keeps long sweeps grep-able. -/
private def formatStatus : Status → String
  | .ok c            => s!"OK {c}"
  | .redirect c n u  => s!"OK {c} after {n} redirect(s) → {u}"
  | .clientError c   => s!"CLIENT-ERROR {c}"
  | .serverError c   => s!"SERVER-ERROR {c}"
  | .timeout         => "TIMEOUT"
  | .networkError m  => s!"NETWORK-ERROR {m}"

/-- True iff the outcome is build-passing: a direct 2xx, or a 2xx reached
    by redirects that never left the recorded URL's origin. A cross-origin
    redirect fails: the recorded URL is stale, or a parked domain. -/
def isPassing (url : String) (s : Status) : Bool :=
  match s with
  | .ok _              => true
  | .redirect _ _ final => NoGoals.originOf? final == NoGoals.originOf? url
  | _                  => false

/-- Pretty-print one result as a single log line. -/
def formatResult (r : CheckResult) : String :=
  let mark := if isPassing r.url r.status then "✓" else "✗"
  s!"  {mark} [{r.durationMs}ms] {r.url} — {formatStatus r.status}"

/-- A roll-up across many results: counts plus the failing entries kept
    intact so the report can name them. -/
structure Summary where
  total  : Nat
  passed : Nat
  failed : List CheckResult
deriving Repr, Inhabited

/-- Tally results into a `Summary`. -/
def summarize (results : List CheckResult) : Summary :=
  let failed := results.filter (fun r => !isPassing r.url r.status)
  { total := results.length
    passed := results.length - failed.length
    failed }

/-- Multi-line human-readable report, suitable for piping into the build
    log or a CI annotation. -/
def Summary.format (s : Summary) : String :=
  let header := s!"external links: {s.passed}/{s.total} passing"
  if s.failed.isEmpty then
    "✓ " ++ header
  else
    "✗ " ++ header ++ "\n" ++
    String.intercalate "\n" (s.failed.map formatResult)

/-! ## Attestation lift

    The attestation produced here is `.automated` because curl-checking is
    a fixed transform: given the URL list and the network state at run
    time, the result is determined by curl, not by editorial judgment.
    The trust bound is exactly "the network agreed on this date." -/

/-- Lift a `Summary` to a typed `NoGoals.Verify.Attestation`. The verifier name
    defaults to `"build:curl"` to make the source visible in reports, but
    sites with multiple checkers (e.g. `"build:curl"` plus
    `"build:archive"`) can override. -/
def toAttestation (_ : Summary) (today : NoGoals.Verify.IsoDate)
    (verifier : String := "build:curl") : NoGoals.Verify.Attestation :=
  { verifiedBy := verifier
    verifiedAt := today
    method     := .automated }

end NoGoals.Verify.External
