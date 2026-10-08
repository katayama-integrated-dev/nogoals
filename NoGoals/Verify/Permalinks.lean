/-
  Permalink permanence — no deploy may silently 404 a previously published URL.

  The publisher keeps a BASELINE of public URL obligations: the files the
  last production deploy served (with their hashes, for the deploy diff) and
  the redirect sources it honored. At build time, every obligation must
  either still be an emitted public file or have an entry in the typed
  redirect map — whose targets must themselves be public files, not be
  redirected in turn (no chains), not shadow a live file, and be declared
  once. A redirect source stays an obligation forever: the baseline written
  after a deploy carries the redirect sources of that deploy, so a redirect
  cannot be quietly deleted two releases later.

  The check is a decidable boolean; `permalinks_sound` converts a passing
  check into the ∀-statement — the same check→proof discipline as `refine`.

  `_redirects` — the host's redirect configuration — is RENDERED from the
  same typed map, so a redirect the check accepted is a redirect the host
  performs. Configuration files (`_headers`, `_redirects`) are never public
  obligations nor valid redirect targets.
-/

import Mathlib.Data.List.Basic
import NoGoals.IR.Route

namespace NoGoals.Verify.Permalinks

open NoGoals (dupes)

/-- One redirect: requests for the URL of `from_` should land on `target`.
    Both are output FILE paths (`old/index.html`), the currency of the
    baseline and the manifest; `urlOf` turns them into URLs. -/
structure Redirect where
  from_ : String
  target : String
deriving Repr, DecidableEq

/-- Everything wrong with a proposed deploy, permalink-wise. -/
inductive PermalinkError
  | lost (path : String)                     -- was published, now gone, no redirect
  | danglingRedirect (r : Redirect)          -- redirect target is not a public file of this build
  | chainedRedirect (r : Redirect)           -- redirect target is itself redirected
  | selfRedirect (r : Redirect)              -- from == to
  | duplicateSource (path : String)          -- two redirects for one source
  | shadowsLiveFile (r : Redirect)           -- redirect source is also an emitted file
deriving Repr, DecidableEq

def PermalinkError.render : PermalinkError → String
  | .lost p => s!"previously published URL would 404: {p} (add a redirect or restore the page)"
  | .danglingRedirect r => s!"redirect {r.from_} → {r.target}: target is not a public file of this build"
  | .chainedRedirect r => s!"redirect {r.from_} → {r.target}: target is itself redirected (chains forbidden)"
  | .selfRedirect r => s!"redirect {r.from_} → {r.target}: self-redirect"
  | .duplicateSource p => s!"redirect source {p} is declared more than once"
  | .shadowsLiveFile r => s!"redirect {r.from_} → {r.target}: source is also an emitted file (the file would win)"

/-- Deployment configuration files: emitted, hashed in the manifest, but
    never served as URLs — so never obligations and never redirect targets. -/
def configFiles : List String := ["_headers", "_redirects"]

def isPublic (path : String) : Bool := !configFiles.contains path

/-- All violations for a proposed deploy. `obligations` are the baseline's
    public paths (files and redirect sources); `current` the emitted files.
    Empty ⟺ permalinks are permanent. -/
def violations (obligations current : List String) (redirects : List Redirect) : List PermalinkError :=
  let served := current.filter isPublic
  let redirectFroms := redirects.map (·.from_)
  let lost := obligations.filter (fun p => decide (p ∉ served ∧ p ∉ redirectFroms))
    |>.map .lost
  let dupeSources := (dupes redirectFroms).map .duplicateSource
  let bad := redirects.filterMap (fun r =>
    if r.from_ = r.target then some (.selfRedirect r)
    else if r.from_ ∈ served then some (.shadowsLiveFile r)
    else if r.target ∉ served then some (.danglingRedirect r)
    else if r.target ∈ redirectFroms then some (.chainedRedirect r)
    else none)
  lost ++ dupeSources ++ bad

def check (obligations current : List String) (redirects : List Redirect) : Bool :=
  (violations obligations current redirects).isEmpty

/-- Soundness: a passing check means every obligation either is a public
    file of this build or is redirected to a live, public, unchained target
    that is not itself a live file. -/
theorem permalinks_sound (obligations current : List String) (redirects : List Redirect)
    (h : check obligations current redirects = true) :
    ∀ p ∈ obligations, p ∈ current.filter isPublic ∨
      ∃ r ∈ redirects, r.from_ = p ∧ r.target ∈ current.filter isPublic ∧
        r.target ∉ redirects.map (·.from_) ∧ r.from_ ∉ current.filter isPublic := by
  intro p hp
  unfold check violations at h
  simp only [List.isEmpty_iff, List.append_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, List.filterMap_eq_nil_iff] at h
  obtain ⟨⟨hlost, _⟩, hbad⟩ := h
  by_cases hc : p ∈ current.filter isPublic
  · exact Or.inl hc
  · have hthis := hlost p hp
    simp only [decide_eq_true_eq] at hthis
    push_neg at hthis
    have hmem : p ∈ redirects.map (·.from_) := hthis hc
    obtain ⟨r, hr, hfrom⟩ := List.mem_map.mp hmem
    have hb := hbad r hr
    split_ifs at hb with h1 h2 h3 h4
    exact Or.inr ⟨r, hr, hfrom, h3, h4, h2⟩

/-! ## URLs of files, and the host's `_redirects` -/

/-- The public URL of an emitted file: `x/index.html ↦ /x/`, `index.html ↦
    /`, anything else `↦ /path` (Cloudflare Pages serves `a.html` at `/a`
    via a redirect; we keep the exact file URL, which it also answers). -/
def urlOf (path : String) : String :=
  if path = "index.html" then "/"
  else if path.endsWith "/index.html" then "/" ++ path.dropEnd "index.html".length
  else "/" ++ path

/-- Every public URL the host answered for a file: the file URL, plus the
    extensionless URL Pages serves standalone `.html` files at (`/old.html`
    is redirected to `/old` by the host). -/
def publicUrlsOf (path : String) : List String :=
  let u := urlOf path
  if path.endsWith ".html" && !path.endsWith "/index.html" && path != "index.html" then
    [u, (u.dropEnd ".html".length).toString]
  else [u]

/-- Cloudflare Pages `_redirects`: one `source destination 301` line per
    public URL of each source. Rendered from the typed map — the check and
    the host see the same redirects. -/
def renderRedirects (redirects : List Redirect) : String :=
  String.intercalate "" (redirects.flatMap fun r =>
    (publicUrlsOf r.from_).map fun src => s!"{src} {urlOf r.target} 301\n")

/-! ## Baseline — parsed strictly, or not at all -/

inductive BaselineEntry
  | file (sha256 path : String)
  | redirect (path : String)
deriving Repr, DecidableEq

def BaselineEntry.path : BaselineEntry → String
  | .file _ p => p
  | .redirect p => p

inductive BaselineParseError
  | malformedLine (lineNo : Nat) (line : String)
  | badHash (lineNo : Nat) (hash : String)
  | badPath (lineNo : Nat) (path : String)
  | duplicatePath (path : String)
  | empty
deriving Repr, DecidableEq

def BaselineParseError.render : BaselineParseError → String
  | .malformedLine n l => s!"baseline line {n}: expected `<sha256>  <path>` or `redirect  <path>`, got `{l}`"
  | .badHash n h => s!"baseline line {n}: `{h}` is not a 64-hex sha256"
  | .badPath n p => s!"baseline line {n}: path `{p}` is not a contained relative path"
  | .duplicatePath p => s!"baseline lists `{p}` more than once"
  | .empty => "baseline is empty — a deployed site has obligations; bootstrap it from the production manifest"

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

def isSha256 (s : String) : Bool := s.length == 64 && s.toList.all isHex

/-- Relative, no empty, `.` or `..` segments. -/
def pathContained (p : String) : Bool :=
  !p.startsWith "/" && p != "" &&
    (p.splitOn "/").all (fun s => s != "" && s != "." && s != "..")

/-- Baseline format: one `sha256␠␠path` or `redirect␠␠path` per line. -/
def parseBaseline (text : String) : Except (List BaselineParseError) (List BaselineEntry) :=
  let lines := (text.splitOn "\n").zipIdx.filter (fun (l, _) => !l.trimAscii.toString.isEmpty)
  let parsed : List (Except BaselineParseError BaselineEntry) := lines.map fun (line, i) =>
    let n := i + 1
    match line.trimAscii.toString.splitOn "  " with
    | ["redirect", p] => if pathContained p then .ok (.redirect p) else .error (.badPath n p)
    | [h, p] =>
      if !isSha256 h then .error (.badHash n h)
      else if !pathContained p then .error (.badPath n p)
      else .ok (.file h p)
    | _ => .error (.malformedLine n line.trimAscii.toString)
  let errs := parsed.filterMap fun | .error e => some e | .ok _ => none
  let entries := parsed.filterMap fun | .ok e => some e | .error _ => none
  let paths := entries.map (·.path)
  let errs := errs ++ (dupes paths).map BaselineParseError.duplicatePath ++
    (if entries.isEmpty && errs.isEmpty then [.empty] else [])
  if errs.isEmpty then .ok entries else .error errs

/-- The obligations a baseline carries: public files and redirect sources. -/
def obligationsOf (entries : List BaselineEntry) : List String :=
  entries.filterMap fun
    | .file _ p => if isPublic p then some p else none
    | .redirect p => some p

/-- Render a baseline from the deployed manifest (`(sha, path)` pairs) and
    the redirect sources that deploy honored. Configuration files are kept
    for the deploy diff but are not obligations (see `obligationsOf`). -/
def renderBaseline (files : List (String × String)) (redirectSources : List String) : String :=
  String.intercalate "" (files.map (fun (h, p) => s!"{h}  {p}\n")) ++
  String.intercalate "" (redirectSources.map (fun p => s!"redirect  {p}\n"))

end NoGoals.Verify.Permalinks
