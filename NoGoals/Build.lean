/-
  NoGoals Build — the publisher's build, from a site spec to a promoted artifact.

  `NoGoals.Build.run spec args` is the build executable of any NoGoals site. A site
  supplies a `SiteBuild`: its `Bridge` (the `Site` plus the two proofs that
  NoGoals accepts it), chrome slots, feeds, redirects, its own guarantees and any
  custom gates; NoGoals owns the rest:

    1. `compile` — routes through the verified IR; every page is one typed
       tree (kernel chrome around the page's own body trees).
    2. Assemble the COMPLETE artifact (pages, assets, feeds, SEO/edge files,
       every reserved late path) as one list; check
       uniqueness (with multiplicity, case-folded) and containment BEFORE the
       first write.
    3. Stage everything whose bytes are known into a fresh candidate
       directory; assert the staged page/asset set equals the list the site
       proved unique.
    4. Gates against the candidate. HTML facts come from a pinned
       browser-grade parser (`html-facts.mjs`, parse5); every HTML-level gate
       reads those facts. Each gate records its result under a stable id; a
       gate that did not run stays a visible `.skipped` placeholder — a
       check that never executed can never appear as passed.
    5. Render the verification pages + receipt from the FINAL evidence; run
       the structural gates over those late bytes too (hard rejection on
       failure; no receipt entry claims anything about bytes that include
       the receipt).
    6. Manifest over the finished candidate; promote on green (rollback if
       the promotion rename fails), quarantine on red.

  Flags: `--audit` (every gate), `--offline` (skip the network gate),
  `--update-baseline` (bootstrap a permalink baseline for a first-ever
  deploy; ignored with a warning when one exists), `--force-gate-failure` (negative
  control for the transactional machinery), first positional = output dir.
-/

import NoGoals.Bridge
import NoGoals.Render.Feed
import NoGoals.Verify.External
import NoGoals.Verify.HtmlValidate
import NoGoals.Verify.SiteAudit
import NoGoals.Verify.Permalinks

namespace NoGoals.Build

open NoGoals (Lang Route dupes)
open NoGoals.DSL
open NoGoals.Compile
open NoGoals.Verify.SiteAudit
open NoGoals.Verify.HtmlFacts (Facts parseFacts)
open NoGoals.Verify.Permalinks (Redirect renderRedirects parseBaseline obligationsOf renderBaseline
  isPublic pathContained BaselineEntry)
open NoGoals.Meta (sitemapOf prodRobots stageRobots CspAllow cspOf prodHeaders stageHeaders Manifest ManifestEntry)
open NoGoals.Render.Feed (AtomFeed)
open NoGoals.Verify (IsoDate)
open NoGoals.Verify.Json (parse getStr getArr)

/-! ## Gates as values -/

/-- A publisher gate: stable id, display name, the claim it checks. -/
structure GateDef where
  id : String
  name : String
  desc : String

/-- The gate's evidence: `.checked` with what was established, or `.failed`
    with why. The description of a passed gate is the concrete claim. -/
def GateDef.result (g : GateDef) (ok : Bool) (okDesc failDesc : String) : Guarantee :=
  { category := "Runtime", name := g.name, description := if ok then okDesc else g.desc
    status := if ok then .checked else .failed failDesc, scope := .artifact, id := g.id }

def GateDef.skipped (g : GateDef) (reason : String) : Guarantee :=
  { category := "Runtime", name := g.name, description := g.desc
    status := .skipped reason, scope := .artifact, id := g.id }

def gateExternal := GateDef.mk "gate.external" "External link liveness"
  "Every external URL the site embeds answers a liveness check (same-origin redirects followed)"
def gateHtmlValidate := GateDef.mk "gate.html-validate" "HTML validity (every emitted page)"
  "html-validate (pinned) runs over every emitted HTML file, including the verification pages"
def gateHtmlFacts := GateDef.mk "gate.html-facts" "Parser facts available"
  "A browser-grade parser (parse5, pinned) produced facts for every emitted HTML file; the gates below read them"
def gateCsp := GateDef.mk "gate.csp" "CSP ↔ content consistency"
  "Every HTML-declared resource use on every page is allowed by the typed production CSP; inline script/style, event handlers and unmodelled elements fail"
def gateLinks := GateDef.mk "gate.links" "Internal reference closure"
  "Every internal href/src/srcset/poster/action on every page resolves (browser + host semantics) to an emitted file or a declared endpoint, and every fragment to an id the target declares"
def gateSeo := GateDef.mk "gate.seo" "SEO coherence"
  "Every route page's canonical link, hreflang alternates, og:url and og:locale equal the values its route predicts"
def gateMetadata := GateDef.mk "gate.metadata" "Metadata completeness"
  "Every route page declares its document language, one title, one non-empty description, og:title/description/type, and og:locale:alternate for the other languages"
def gateCjk := GateDef.mk "gate.i18n-cjk" "No CJK leaks on English pages"
  "Japanese text on EN pages only where deliberately allowed (visible text and human-facing attributes)"
def gateAssets := GateDef.mk "gate.assets" "Stylesheet asset reality"
  "Every url(/assets/…) reference in the declared stylesheets exists in the candidate artifact"
def gateNews := GateDef.mk "gate.news" "News invariants"
  "Articles sorted newest-first; none future-dated vs the wall clock"
def gateFeeds := GateDef.mk "gate.feeds" "Feed entries are emitted routes"
  "Every Atom entry route is a route this build emitted"
def gateCss := GateDef.mk "gate.css-contract" "CSS contract"
  "Every class on every page is styled or a declared semantic hook"
def gateEscaping := GateDef.mk "gate.escaping" "No double-escaped entities"
  "No double escaping in any page's visible text: an entity that was escaped twice shows up as literal entity text"
def gateReachability := GateDef.mk "gate.reachability" "Click-path reachability"
  "Every page is reachable from a declared root (pages declared redirect-reached and the not-found pages aside)"
def gatePermalinks := GateDef.mk "gate.permalinks" "Permalink permanence"
  "Every previously published URL obligation is live or typed-redirected; `_redirects` is rendered from the same map"

/-- The gates that read parser facts (besides the network gate): when the
    parser fails, every one of them fails with it. -/
def factGates : List GateDef :=
  [gateCsp, gateLinks, gateSeo, gateMetadata, gateCjk, gateCss, gateEscaping, gateReachability]

/-- NoGoals's own gates, in run order. -/
def builtinGates : List GateDef :=
  [gateExternal, gateHtmlValidate, gateHtmlFacts] ++ factGates ++
  [gateAssets, gateNews, gateFeeds, gatePermalinks]

/-- A site's own gate: its definition and how to run it. `run today?` gets
    the wall-clock date (`none` if it could not be parsed) and answers
    `.ok okDesc` (the concrete claim established) or `.error failDesc`. -/
structure CustomGate where
  gate : GateDef
  run : Option IsoDate → IO (Except String String)

/-! ## The site spec -/

inductive ArtifactContent
  | text (s : String)
  | copyFrom (src : System.FilePath)

structure ArtifactEntry where
  path : String
  content : ArtifactContent

/-- Everything a site tells the build. Defaults suit a site laid out like
    the template the `NoGoals` skill scaffolds (which depends on NoGoals by path, so
    it sets `nogoalsDir`). -/
structure SiteBuild where
  /-- The site and the two proofs that NoGoals accepts it. The theorem entries
      and the exact page/asset set the build must stage come from here. -/
  bridge : Bridge
  /-- Typed chrome slots per language (footer mark, footer nav, badge, head extras). -/
  chrome : Lang → SiteChrome := fun _ => {}
  /-- The site's own compile-time guarantees (closed enumerations it
      defined, theorems about its data). -/
  extraGuarantees : List Guarantee := []
  /-- Atom feeds; every entry route must be an emitted route. -/
  feeds : List AtomFeed := []
  /-- Typed redirects (file paths); rendered into `_redirects` and checked. -/
  redirects : List Redirect := []
  /-- Form actions served by functions, not files — exact strings. -/
  dynamicEndpoints : List String := []
  /-- Deliberate Japanese on English pages (each entry is a decision). -/
  cjkAllow : List String := []
  /-- Classes that deliberately carry no styles (JS hooks, third-party widgets). -/
  semanticClasses : List String := []
  /-- Origins the pages load from beyond `'self'`, per CSP directive. The
      pages are checked against exactly this policy and `_headers` ships it. -/
  csp : CspAllow := {}
  /-- Emitted files a visitor can start from (reachability roots). -/
  reachabilityRoots : List String := ["index.html"]
  /-- The site's own gates (provenance, review freshness, …). -/
  customGates : List CustomGate := []
  /-- Pinned `html-validate` executable. -/
  htmlValidateExe : String := "node_modules/.bin/html-validate"
  /-- Where NoGoals's checkout lives: the receipt's source identity and the home
      of `tools/html-facts.mjs`. The default is Lake's location for a git
      dependency; a path dependency names its own. -/
  nogoalsDir : System.FilePath := ".lake/packages/nogoals"
  /-- The permalink baseline (public URL obligations of the last production deploy). -/
  baselinePath : System.FilePath := "deploy/permalink-baseline.txt"
  /-- Where to regenerate staging overlays (`_headers`, `robots.txt` with
      noindex) on the green path, for a host that serves a staging branch
      with its own edge files. -/
  stagingOverlayDir : Option System.FilePath := none

def SiteBuild.gates (spec : SiteBuild) : List GateDef :=
  builtinGates ++ spec.customGates.map (·.gate)

/-- The pre-run report entries: one `.skipped` placeholder per gate, with
    the reason it will not run under the current profile (`required` empty
    means no audit was requested). Gates that WILL run also start as
    placeholders — their real results replace them after execution, so the
    written report can only ever describe checks that actually happened. -/
def gatePlaceholders (spec : SiteBuild) (required : List String) : List Guarantee :=
  spec.gates.map fun g =>
    g.skipped (if required.contains g.id then "check requested but result not recorded — build aborted before it ran"
      else if required.isEmpty then "not requested (run with --audit)"
      else "skipped by --offline (network profile)")

/-! ## Process helpers -/

/-- The wall clock, `YYYY-MM-DD HH:MM:SS`. Its date part is parsed through
    the `Except` boundary where a gate needs it: a garbled `date` output
    fails every clock-dependent gate instead of silently becoming ⟨0,0,0⟩. -/
def getTimestamp : IO String := do
  let now ← IO.Process.output { cmd := "date", args := #["+%Y-%m-%d %H:%M:%S"] }
  return now.stdout.trimAscii.toString

/-- Paths that would overwrite each other on write — as declared, and
    case-folded (case-insensitive filesystems). -/
def artifactCollisions (paths : List String) : List String :=
  dupes (paths.map String.toLower)

def writeArtifactEntry (root : System.FilePath) (e : ArtifactEntry) : IO Unit := do
  let dst := root / e.path
  IO.FS.createDirAll (dst.parent.getD root)
  match e.content with
  | .text s => IO.FS.writeFile dst s
  | .copyFrom src => IO.FS.writeBinFile dst (← IO.FS.readBinFile src)

/-- SHA-256 of every file (paths relative to `root`), one tool invocation
    for the whole artifact. The tool prints one `hash  path` line per file
    in argument order. -/
def sha256All (root : System.FilePath) (files : List String) : IO (List (String × String)) := do
  let tryCmd (cmd : String) (args : Array String) : IO (Option String) := do
    try
      let out ← IO.Process.output { cmd, args, cwd := some root }
      if out.exitCode == 0 then return some out.stdout else return none
    catch _ => return none
  let out ← match ← tryCmd "shasum" (#["-a", "256"] ++ files.toArray) with
    | some o => pure o
    | none => match ← tryCmd "sha256sum" files.toArray with
      | some o => pure o
      | none => throw (IO.userError "no SHA-256 tool available (tried shasum, sha256sum)")
  let hashes := (out.splitOn "\n").filter (· ≠ "") |>.map (fun h => (h.take 64).toString)
  unless hashes.length == files.length do
    throw (IO.userError s!"SHA-256 tool reported {hashes.length} hashes for {files.length} files")
  return files.zip hashes

partial def walkFiles (root : System.FilePath) : IO (List String) := do
  let rec go (dir : System.FilePath) : IO (List String) := do
    let entries ← dir.readDir
    let mut out : List String := []
    for e in entries do
      let md ← e.path.metadata
      if md.type == .dir then
        out := out ++ (← go e.path)
      else
        out := out ++ [e.path.toString]
    return out
  let all ← go root
  let rootStr := root.toString ++ "/"
  let rel := all.map (fun p => (p.dropPrefix rootStr).toString)
  return rel.toArray.qsort (· < ·) |>.toList

def buildManifest (buildDir : System.FilePath) (timestamp baseUrl : String) : IO Manifest := do
  let files ← walkFiles buildDir
  let entries ← (← sha256All buildDir files).mapM fun (rel, sha256) => do
    return ({ path := rel, sha256, size := (← (buildDir / rel).metadata).byteSize.toNat } : ManifestEntry)
  return { generator := "NoGoals", generatedAt := timestamp, canonicalBaseUrl := baseUrl, files := entries }

/-- `(commit, dirty)` of a git worktree; `("unknown", true)` when git fails —
    an unknown source state is a dirty one. Untracked files do not count:
    nothing untracked can reach the artifact (every input is a tracked Lean
    module, asset or script), and receipt archives live untracked. -/
def gitState (dir : System.FilePath) : IO (String × Bool) := do
  try
    let head ← IO.Process.output { cmd := "git", args := #["-C", dir.toString, "rev-parse", "HEAD"] }
    let st ← IO.Process.output { cmd := "git", args := #["-C", dir.toString, "status", "--porcelain", "--untracked-files=no"] }
    if head.exitCode != 0 || st.exitCode != 0 then return ("unknown", true)
    return (head.stdout.trimAscii.toString, !st.stdout.trimAscii.toString.isEmpty)
  catch _ => return ("unknown", true)

/-- A JSON string field of a file, `"unknown"` when the file or the field is
    not there (the receipt records what it could see; "unknown" is a fact). -/
def jsonFieldOf (file : System.FilePath) (get : Lean.Json → Except String String) : IO String := do
  unless ← file.pathExists do return "unknown"
  return ((parse file.toString (← IO.FS.readFile file)) >>= get).toOption.getD "unknown"

/-- The Mathlib rev NoGoals is pinned to, from its lake manifest. -/
def nogoalsMathlibRev (nogoalsDir : System.FilePath) : IO String :=
  jsonFieldOf (nogoalsDir / "lake-manifest.json") fun j => do
    let pkgs ← getArr j "packages" "lake-manifest"
    match pkgs.find? (fun p => (getStr p "name" "package").toOption == some "mathlib") with
    | some p => getStr p "rev" "mathlib"
    | none => throw "no mathlib package"

/-- The installed version of a node package the gates ran with. -/
def nodePackageVersion (name : String) : IO String :=
  jsonFieldOf (System.FilePath.mk "node_modules" / name / "package.json") (getStr · "version" name)

/-- Run the pinned parser over `files` (relative to `root`) and decode strictly. -/
def runFacts (script root : System.FilePath) (files : List String) : IO (Except String Facts) := do
  let out ← (IO.Process.output {
    cmd := "node", args := #[script.toString, root.toString] ++ files.toArray } : IO IO.Process.Output).toBaseIO
  match out with
  | .error e => return .error s!"could not run {script}: {e}"
  | .ok o =>
    if o.exitCode != 0 then return .error s!"{script} exited {o.exitCode}: {o.stderr.take 500}"
    return parseFacts files o.stdout

/-- html-validate (pinned binary) over staged files; the tool omits clean
    files, so the count of files processed is ours. -/
def validateStaged (exe : String) (stagingDir : System.FilePath) (files : List String) :
    IO (Except String NoGoals.Verify.HtmlValidate.Summary) := do
  match ← NoGoals.Verify.HtmlValidate.validate exe (files.map fun f => (stagingDir / f).toString) stagingDir with
  | .error e => return .error e
  | .ok results => return .ok { NoGoals.Verify.HtmlValidate.summarize results with totalFiles := files.length }

/-- The whole command line. An unknown flag is a usage error, never a
    silently different build: `--audti` must not ship an unaudited site. -/
def flags : List (String × String) :=
  [ ("--audit", "run every publisher gate; a red gate leaves the previous build in place")
  , ("--offline", "with --audit: skip the network gate (external-link liveness) only")
  , ("--update-baseline", "with --audit: bootstrap the permalink baseline (first deploy only)")
  , ("--force-gate-failure", "negative control: force a red gate to prove the build fails closed")
  , ("--force-late-failure", "negative control: fail the finalization pass over the report pages")
  , ("--help", "this text") ]

def usage : String :=
  "usage: build-site [OUTPUT_DIR] [flags]\n\n  OUTPUT_DIR defaults to `build`.\n\n" ++
  String.intercalate "\n" (flags.map fun (f, d) => s!"  {f.pushn ' ' (22 - f.length)}{d}")

/-! ## Late files — rendered after the gates, from the final evidence -/

inductive LateFile
  | page (kind : ReportKind) (lang : Lang) | quietCss | fullCss | textReport | receipt

/-- The one table of reserved late paths: what the collision/containment
    check reserves, what the finalization pass re-checks, and what gets
    written are the same list. The pages are routes (one per kind and
    language, paths from THE path function); the rest are shared files. -/
def lateFiles (d : Lang) : List (String × LateFile) :=
  (Lang.all.flatMap fun l => [ReportKind.quiet, .full].map fun k => ((k.route l).outputPath d, .page k l)) ++
  [ (ReportKind.quiet.cssPath, .quietCss), (ReportKind.full.cssPath, .fullCss),
    (textReportPath, .textReport), (receiptPath, .receipt) ]

def LateFile.route? : LateFile → Option Route
  | .page k l => some (k.route l)
  | _ => none

/-- A late file is either a page — a typed tree that must be well-formed
    before it is written, and the stylesheet it loads — or bytes. -/
inductive LateContent
  | page (tree : NoGoals.Render.Tree.Html) (css : String)
  | file (s : String)

def LateFile.content (c : ReportCtx) (report : VerificationReport) (controls : List ControlResult)
    (receipt : String) : LateFile → LateContent
  | .page k l => .page (k.tree c l report controls) k.css
  | .quietCss => .file ReportKind.quiet.css
  | .fullCss => .file ReportKind.full.css
  | .textReport => .file (formatReportWithControls report controls)
  | .receipt => .file receipt

/-! ## The build -/

def run (spec : SiteBuild) (args : List String) : IO UInt32 := do
  let site := spec.bridge.site
  if args.contains "--help" then
    IO.println usage; return 0
  match args.filter (fun a => a.startsWith "--" && !(flags.map (·.1)).contains a) with
  | [] => pure ()
  | bad => IO.eprintln s!"unknown flag(s): {bad}\n\n{usage}"; return 2
  let outputDir ← match args.filter (fun a => !a.startsWith "--") with
    | [] => pure (System.FilePath.mk "build")
    | [dir] => pure (System.FilePath.mk dir)
    | dirs => IO.eprintln s!"more than one output directory: {dirs}\n\n{usage}"; return 2
  let runAudit := args.contains "--audit"
  let offline := args.contains "--offline"
  let updateBaseline := args.contains "--update-baseline"
  let forceLate := args.contains "--force-late-failure"
  let profile := if !runAudit then "build" else if offline then "offline-audit" else "full-audit"
  let required := if !runAudit then [] else
    (spec.gates.map (·.id)).filter (fun id => !offline || id != gateExternal.id)

  IO.println s!"NoGoals build — {site.config.name.en}"
  IO.println s!"profile: {profile}\n"

  -- ── Phase 1: compile ────────────────────────────────────────────────────
  let timestamp ← getTimestamp
  let result := compile site timestamp spec.chrome
    (spec.bridge.guarantees ++ spec.extraGuarantees ++ gatePlaceholders spec required)
  IO.println (formatReport result.report)
  if !result.report.allPassed then
    IO.println "⚠ Build aborted due to verification failures."
    return 1
  if !result.controlsPassed then
    IO.println "⚠ Control tests failed - NoGoals verification system may be broken."
    return 1
  let files := result.files
  let d := site.config.defaultLang
  let origin := site.config.canonicalBaseUrl
  let factsScript := spec.nogoalsDir / "tools" / "html-facts.mjs"

  -- ── Phase 2: the complete artifact, checked before any write ───────────
  let routes := site.routes.map (·.2)
  let indexedRoutes := (site.routes.filter (·.1.indexed)).map (·.2)
  let routePages : List (Route × String) := routes.map fun r => (r, r.outputPath d)
  -- Not-found pages, one per language: outside the route set (no sitemap
  -- entry, no canonical), but staged, validated and gated like every page.
  let notFound : List OutputFile := Lang.all.map fun l =>
    { path := notFoundPath d l, content := notFoundHtml site l (spec.chrome l) }
  let htmlOut := files ++ notFound
  let htmlFiles := htmlOut.map (·.path)
  let manifestPath := "verification-manifest.json"
  -- Reserved late paths: rendered after the gates from their evidence.
  let lateTable := lateFiles d
  let latePaths := lateTable.map (·.1) ++ [manifestPath]
  let reportRoutePages : List (Route × String) := lateTable.filterMap fun (p, f) => f.route?.map (·, p)
  let lateHtml := reportRoutePages.map (·.2)
  let artifact : List ArtifactEntry :=
    (htmlOut.map fun f => { path := f.path, content := .text f.content }) ++
    (site.assets.map fun a =>
      { path := a.path.toString, content := .copyFrom (System.FilePath.mk a.path.toString) }) ++
    (spec.feeds.map fun f => { path := f.outputPath, content := .text (NoGoals.Render.Feed.render f) }) ++
    [ { path := "sitemap.xml", content := .text (sitemapOf origin d (indexedRoutes ++ reportRoutes)).toXml }
    , { path := "robots.txt", content := .text (prodRobots origin).render }
    , { path := "_headers", content := .text (prodHeaders spec.csp).render }
    , { path := "_redirects", content := .text (renderRedirects spec.redirects) } ]
  let allPaths := artifact.map (·.path) ++ latePaths
  let collisions := artifactCollisions allPaths
  unless collisions.isEmpty do
    throw (IO.userError s!"artifact path collision (case-folded): {collisions}")
  for p in allPaths do
    unless pathContained p do
      throw (IO.userError s!"artifact path escapes the output root: {p}")
  -- What an internal link may target: every public planned path (late
  -- pages included — the badge links to /verification/ on every page).
  let inventory := allPaths.filter isPublic

  -- ── Phase 3: stage the candidate ───────────────────────────────────────
  let stagingDir := System.FilePath.mk (outputDir.toString ++ ".staging")
  let failedDir := System.FilePath.mk (outputDir.toString ++ ".failed")
  if ← stagingDir.pathExists then IO.FS.removeDirAll stagingDir
  IO.println s!"Staging {artifact.length} files into {stagingDir}/ ({files.length} pages, {site.assets.length} assets)..."
  IO.FS.createDirAll stagingDir
  for e in artifact do
    writeArtifactEntry stagingDir e
  let staged := (files.map (·.path) ++ site.assets.map (·.path.toString)).toArray.qsort (· < ·) |>.toList
  let expected := spec.bridge.expectedOutputs.toArray.qsort (· < ·) |>.toList
  if staged ≠ expected then
    throw <| IO.userError s!"staged page/asset set does not match the proved list\n  missing: {expected.filter (· ∉ staged)}\n  extra: {staged.filter (· ∉ expected)}"
  IO.println "  ✓ Staged page/asset set matches the proved output list"

  -- ── Phase 4: gates, all against the staged candidate ───────────────────
  -- Each gate records its evidence; whether the build is red is READ from
  -- that evidence (`gateResults.any isFailed`), never tracked alongside it.
  let mut gateResults : List Guarantee := []
  -- Kept for the finalization pass: link and reachability graphs span the
  -- content pages and the report pages together.
  let mut earlyFacts : Facts := []
  -- What NoGoals's own chrome emits in Japanese on every page (the switcher's
  -- label for the Japanese variant) is not a leak; the site's allowances
  -- cover its own deliberate Japanese.
  let cjkAllow := spec.cjkAllow ++ Lang.all.map site.config.langName
  -- Pages a server redirect reaches declare it on their PageDef and are
  -- exceptions; so are the not-found pages, which the host serves on a miss.
  let redirectReached := (site.routes.filter fun (p, _) => p.reachedByRedirect).map fun (_, r) => r.outputPath d
  let exceptions := redirectReached ++ notFound.map (·.path)
  -- Japanese on the English pages among `pages`, beyond the allowances.
  let cjkOn (pages : List (Route × String)) (fs : Facts) : List String :=
    (fs.filter fun f => (pages.find? (·.2 == f.path)).any (·.1.lang == .en)).filterMap fun f =>
      let l := cjkLeaks (humanText f) cjkAllow
      if l.isEmpty then none else some s!"{f.path}: {l}"
  let report (label : String) (violations : List String) : IO Unit := do
    if violations.isEmpty then IO.println s!"  ✓ {label}"
    else
      IO.println s!"  ✗ {label}:"
      for v in violations do IO.println s!"      {v}"
  let todayStr := (timestamp.take 10).toString
  let today? := IsoDate.ofString? todayStr

  -- Stylesheets are CSS input for the CSS-contract and asset gates.
  let stylesheets := site.assets.filter (·.kind == .css)
  let css := String.join (← stylesheets.mapM fun a => IO.FS.readFile a.path.toString)

  if runAudit then
    IO.println "\n═══ AUDIT — publisher gate suite ═══"

    IO.println "Validating staged HTML (html-validate)..."
    match ← validateStaged spec.htmlValidateExe stagingDir htmlFiles with
    | .error e =>
      IO.println s!"  ✗ html-validate: {e}"
      gateResults := gateResults ++ [gateHtmlValidate.result false "" e]
    | .ok summary =>
      IO.println ("  " ++ NoGoals.Verify.HtmlValidate.formatSummary summary)
      gateResults := gateResults ++ [gateHtmlValidate.result (summary.totalErrors == 0)
        s!"html-validate: {htmlFiles.length} pages, 0 errors (verification pages checked in the finalization pass)"
        s!"{summary.totalErrors} HTML error(s) across {htmlFiles.length} pages"]

    -- Parser facts for every HTML file; every HTML-level gate reads them.
    match ← runFacts factsScript stagingDir htmlFiles with
    | .error e =>
      IO.println s!"  ✗ html-facts: {e}"
      gateResults := gateResults ++ [gateHtmlFacts.result false "" e] ++
        ((if offline then [] else [gateExternal]) ++ factGates).map
          (·.result false "" "parser facts unavailable")
    | .ok facts =>
      earlyFacts := facts
      IO.println s!"  ✓ html-facts: parser facts for {facts.length} HTML files"
      gateResults := gateResults ++ [gateHtmlFacts.result true
        s!"parse5 produced facts for all {facts.length} pages (verification pages: finalization pass)" ""]

      if !offline then
        let urls := (externalUrls origin facts).eraseDups
        IO.println s!"Verifying external link liveness ({urls.length} URLs)..."
        let summary := NoGoals.Verify.External.summarize (← NoGoals.Verify.External.headCheckAll urls)
        IO.println (NoGoals.Verify.External.Summary.format summary)
        gateResults := gateResults ++ [gateExternal.result summary.failed.isEmpty
          s!"All {urls.length} external URLs in the emitted HTML answered the liveness check"
          s!"{summary.failed.length} external URL(s) unreachable"]

      let cspV := (facts.flatMap (checkPageCsp (cspOf spec.csp) origin)).map (·.render)
      report s!"CSP ↔ content: {facts.length} pages against the typed policy" cspV
      gateResults := gateResults ++ [gateCsp.result cspV.isEmpty
        s!"{facts.length} pages: every HTML-declared resource use allowed by the typed production CSP; no inline script/style/handlers"
        s!"{cspV.length} violation(s)"]
      let stale := staleCspAllowances (cspOf spec.csp) facts
      unless stale.isEmpty do IO.println s!"  ⚠ CSP stale allowances (declared, never used): {stale}"

      let linkV := (linkViolations origin inventory spec.dynamicEndpoints facts).map (·.render)
      report s!"links: every internal reference on {facts.length} pages resolves" linkV
      gateResults := gateResults ++ [gateLinks.result linkV.isEmpty
        s!"Every internal reference on {facts.length} pages resolves to an emitted file or a declared endpoint ({spec.dynamicEndpoints}); every fragment to a declared id"
        s!"{linkV.length} broken reference(s)"]

      let seoV := (seoViolations origin d routePages facts).map (·.render)
      report s!"seo: canonical/hreflang/og on {routePages.length} route pages" seoV
      gateResults := gateResults ++ [gateSeo.result seoV.isEmpty
        s!"All {routePages.length} route pages carry the canonical, hreflang (+x-default), og:url and og:locale their route predicts"
        s!"{seoV.length} SEO mismatch(es)"]

      let metaV := (metadataViolations routePages facts).map (·.render)
      report s!"metadata: language, title, description, og basics on {routePages.length} route pages" metaV
      gateResults := gateResults ++ [gateMetadata.result metaV.isEmpty
        s!"All {routePages.length} route pages declare their language, one title, one description and the OpenGraph basics"
        s!"{metaV.length} metadata violation(s)"]

      -- What NoGoals's own chrome emits in Japanese on every page (the switcher's
      -- label for the Japanese variant) is not a leak; the site's allowances
      -- cover its own deliberate Japanese.
      let enPages := routePages.filter (fun (r, _) => r.lang == .en) |>.map (·.2)
      let leaks := cjkOn routePages facts
      report s!"i18n: no CJK leaks on {enPages.length} English pages" leaks
      gateResults := gateResults ++ [gateCjk.result leaks.isEmpty
        s!"No undeclared Japanese text on {enPages.length} EN pages ({spec.cjkAllow.length} declared allowances beyond the chrome's own labels)"
        s!"{leaks.length} EN page(s) with CJK leaks"]

      let esc := facts.filterMap fun f => let ds := doubleEscaped f; if ds.isEmpty then none else some s!"{f.path}: {ds}"
      report "escaping: no double-escaped entities in visible text" esc
      gateResults := gateResults ++ [gateEscaping.result esc.isEmpty
        s!"No double-escaped entities in the visible text of {facts.length} pages" s!"{esc.length} page(s) with double-escaped entities"]

      let undef := ((undefinedClasses css facts).filter (· ∉ spec.semanticClasses)).map (s!".{·}")
      report s!"css: every class styled or a declared semantic hook ({spec.semanticClasses.length} declared)" undef
      gateResults := gateResults ++ [gateCss.result undef.isEmpty
        s!"Every class on {facts.length} pages is styled or one of {spec.semanticClasses.length} declared semantic hooks"
        s!"{undef.length} class(es) styled nowhere"]

      let orphans := unreachableFrom origin facts spec.reachabilityRoots exceptions
      report s!"reachability: every page reachable from {spec.reachabilityRoots}" orphans
      gateResults := gateResults ++ [gateReachability.result orphans.isEmpty
        s!"All {facts.length} pages reachable from a declared root ({spec.reachabilityRoots.length} roots; {redirectReached.length} pages declared redirect-reached and {notFound.length} not-found pages exempt)"
        s!"{orphans.length} unreachable page(s)"]

    -- Stylesheet asset reality: url(/assets/…) in the declared stylesheets.
    let cssRefs := extractCssAssetRefs css
    let missing ← missingAssets stagingDir cssRefs
    report s!"assets: all {cssRefs.length} stylesheet url(/assets/…) references exist" missing
    gateResults := gateResults ++ [gateAssets.result missing.isEmpty
      s!"All {cssRefs.length} url(/assets/…) references in {stylesheets.length} stylesheets exist in the candidate"
      s!"{missing.length} referenced asset(s) missing"]

    -- News invariants against the wall clock.
    match today? with
    | none =>
      IO.println s!"  ✗ wall-clock date unparseable: {todayStr}"
      gateResults := gateResults ++ [gateNews.result false "" s!"wall-clock date unparseable: {todayStr}"]
    | some today =>
      let newsDates := site.news.map (·.date)
      let sortedOk := newsSorted newsDates
      let future := futureDated newsDates today
      report s!"news: {newsDates.length} articles sorted newest-first, none future-dated as of {today}"
        ((if sortedOk then [] else ["articles are not sorted newest-first"]) ++ future.map (s!"future-dated: {·}"))
      gateResults := gateResults ++ [gateNews.result (sortedOk && future.isEmpty)
        s!"{newsDates.length} articles sorted newest-first, none future-dated as of {today}"
        (if sortedOk then s!"{future.length} future-dated article(s)" else "articles not sorted newest-first")]

    -- Feed entries are emitted routes.
    let feedRoutes := spec.feeds.flatMap NoGoals.Render.Feed.entryRoutes
    let missingFeed := feedRoutes.filter (fun r => !routes.contains r)
    report s!"feeds: all {feedRoutes.length} Atom entry routes are emitted routes" (missingFeed.map toString)
    gateResults := gateResults ++ [gateFeeds.result missingFeed.isEmpty
      s!"All {feedRoutes.length} Atom entry routes are routes this build emitted" s!"{missingFeed.length} entry route(s) with no emitted page"]

    -- The site's own gates.
    for cg in spec.customGates do
      match ← cg.run today? with
      | .ok okDesc =>
        IO.println s!"  ✓ {cg.gate.name}: {okDesc}"
        gateResults := gateResults ++ [cg.gate.result true okDesc ""]
      | .error failDesc =>
        IO.println s!"  ✗ {cg.gate.name}: {failDesc}"
        gateResults := gateResults ++ [cg.gate.result false "" failDesc]

  -- Permalink permanence vs the baseline of public URL obligations.
  let mut baseline? : Option (List BaselineEntry) := none
  if runAudit then
    if ← spec.baselinePath.pathExists then
      match parseBaseline (← IO.FS.readFile spec.baselinePath) with
      | .error es =>
        report "permalinks: baseline parseable" (es.map (·.render))
        gateResults := gateResults ++ [gatePermalinks.result false "" s!"baseline unparseable: {es.length} error(s)"]
      | .ok entries =>
        baseline? := some entries
        let obligations := obligationsOf entries
        let permaV := NoGoals.Verify.Permalinks.violations obligations allPaths spec.redirects
        report s!"permalinks: all {obligations.length} obligations live or redirected (permalinks_sound applies); _redirects rendered from the same map"
          (permaV.map (·.render))
        gateResults := gateResults ++ [gatePermalinks.result permaV.isEmpty
          s!"All {obligations.length} previously published URL obligations live or typed-redirected; {spec.redirects.length} redirect(s) rendered into _redirects"
          s!"{permaV.length} violation(s)"]
    else if updateBaseline then
      IO.println s!"  ◌ permalinks: no baseline at {spec.baselinePath} — bootstrapping from this candidate (--update-baseline)"
      gateResults := gateResults ++ [gatePermalinks.skipped "no baseline: bootstrapped from this build by --update-baseline"]
    else
      IO.println s!"  ✗ permalinks: no baseline at {spec.baselinePath}. A deployed site has obligations: import them from the deployed receipt or, for a first-ever deploy, bootstrap with --update-baseline"
      gateResults := gateResults ++ [gatePermalinks.result false "" s!"no baseline at {spec.baselinePath}"]

  -- Negative control for the transactional machinery.
  if args.contains "--force-gate-failure" then
    gateResults := gateResults ++ [(GateDef.mk "gate.negative-control" "Forced gate failure (test)"
      "Negative control: proves a red gate cannot reach the output directory").result false "" "forced by --force-gate-failure"]
    IO.println "\n✗ negative control: gate failure FORCED by --force-gate-failure"

  let gatesFailed := gateResults.any (·.isFailed)
  if runAudit then
    if gatesFailed then IO.println "\n✗ AUDIT FAILED — violations above; the previous build stays in place."
    else IO.println "\n✓ AUDIT PASSED — every publisher gate is green."

  -- ── Phase 5: final report, receipt, late files — then re-check the late bytes
  let finalReport := { result.report with
    guarantees := updateGuarantees result.report.guarantees gateResults }
  IO.println "\nWriting verification reports (from final evidence)..."
  let (siteCommit, siteDirty) ← gitState "."
  let (nogoalsCommit, nogoalsDirty) ← gitState spec.nogoalsDir
  let sources : List SourceId := [⟨"consumer", siteCommit, siteDirty⟩, ⟨"nogoals", nogoalsCommit, nogoalsDirty⟩]
  let toolchainPin ← (do
    if ← (System.FilePath.mk "lean-toolchain").pathExists then
      pure (← IO.FS.readFile "lean-toolchain").trimAscii.toString
    else pure "unknown")
  let receipt := formatReceiptJson finalReport {
    profile, required
    source := sources.flatMap (·.pairs)
    pins := [("lean-toolchain", toolchainPin), ("nogoals.mathlib", ← nogoalsMathlibRev spec.nogoalsDir),
             ("html-validate", ← nodePackageVersion "html-validate"), ("parse5", ← nodePackageVersion "parse5")]
    evaluatedDate := if runAudit then (today?.map (·.toString)).getD "" else ""
    evaluatedSource := if runAudit && today?.isSome then "wall clock (date)" else ""
    redirects := spec.redirects.map (·.from_) }
  let ctx : ReportCtx := { origin, d, langName := site.config.langName, profile, sources }
  -- The report trees must be well-formed (no raw node, clean names) BEFORE
  -- they are written: `render_wf` then covers them like every other tree.
  -- Each page remembers the one stylesheet it loads, for the CSS contract.
  let mut lateFailures : List String := []
  let mut pageSheets : List (String × String) := []
  for (path, file) in lateTable do
    match file.content ctx finalReport result.controls receipt with
    | .page t css =>
      -- Negative control: a raw node in a report tree is exactly what the
      -- well-formedness check must reject.
      let t := if forceLate then NoGoals.Render.Tree.Html.el "div" [] [t, .raw "<!-- forced -->"] else t
      unless NoGoals.Render.Tree.wellFormed t do lateFailures := lateFailures ++ [s!"{path}: report tree is not well-formed"]
      pageSheets := pageSheets ++ [(path, css)]
      writeArtifactEntry stagingDir { path, content := .text ("<!DOCTYPE html>" ++ NoGoals.Render.Tree.render t) }
    | .file bytes => writeArtifactEntry stagingDir { path, content := .text bytes }
  IO.println s!"  ✓ verification pages + receipt.json ({lateTable.length} files, from post-gate evidence)"

  -- Finalization pass: the page gates over the report pages — html-validate,
  -- CSP, escaping, CSS contract, SEO and metadata on the late pages; link
  -- closure, fragments and click-path reachability over content AND report
  -- pages together; no Japanese on the English report. Not a receipt entry
  -- (the receipt is already written); a failure is a hard rejection of the
  -- candidate. Skipped when a gate already failed: the candidate is
  -- quarantined either way, and the same violations would print twice.
  if runAudit && !gatesFailed then
    IO.println "Finalization pass over the verification pages..."
    match ← validateStaged spec.htmlValidateExe stagingDir lateHtml with
    | .error e => lateFailures := lateFailures ++ [s!"html-validate: {e}"]
    | .ok summary =>
      if summary.totalErrors != 0 then
        lateFailures := lateFailures ++ [NoGoals.Verify.HtmlValidate.formatSummary summary]
    match ← runFacts factsScript stagingDir lateHtml with
    | .error e => lateFailures := lateFailures ++ [s!"html-facts: {e}"]
    | .ok lateFacts =>
      let allFacts := earlyFacts ++ lateFacts
      lateFailures := lateFailures ++
        (lateFacts.flatMap (checkPageCsp (cspOf spec.csp) origin)).map (·.render) ++
        (linkViolations origin inventory spec.dynamicEndpoints allFacts).map (·.render) ++
        (lateFacts.filterMap fun f => let ds := doubleEscaped f; if ds.isEmpty then none else some s!"{f.path}: double-escaped {ds}") ++
        (pageSheets.flatMap fun (p, sheet) => undefinedClasses sheet (lateFacts.filter (·.path == p))).map (s!"class styled nowhere: .{·}") ++
        (seoViolations origin d reportRoutePages lateFacts).map (·.render) ++
        (metadataViolations reportRoutePages lateFacts).map (·.render) ++
        (unreachableFrom origin allFacts spec.reachabilityRoots exceptions).map (s!"unreachable: {·}") ++
        (cjkOn reportRoutePages lateFacts).map (s!"CJK on an English report page — {·}")
    if lateFailures.isEmpty then IO.println s!"  ✓ {lateHtml.length} report pages pass html-validate, CSP, links and fragments (with the content pages), SEO, metadata, reachability, escaping and CSS contract"
  -- The well-formedness check above runs in every profile; say why a
  -- candidate is rejected whether or not an audit ran.
  unless lateFailures.isEmpty do
    IO.println "  ✗ report pages fail the finalization pass:"
    for f in lateFailures do IO.println s!"      {f}"

  -- ── Phase 6: manifest, deploy diff, promote or quarantine ──────────────
  IO.println "\nComputing SHA-256 manifest..."
  let manifest ← buildManifest stagingDir timestamp origin
  IO.FS.writeFile (stagingDir / manifestPath) manifest.toJson
  IO.println s!"  ✓ {manifestPath} ({manifest.files.length} files hashed)"
  let currentEntries := manifest.files.map (fun e => (e.sha256, e.path))
  match baseline? with
  | some entries =>
    IO.println "  — deploy diff vs baseline —"
    let dd := diffAgainstBaseline entries currentEntries
    IO.println ((dd.render.splitOn "\n").map (s!"      {·}") |> String.intercalate "\n")
  | none => pure ()

  if gatesFailed || !lateFailures.isEmpty then
    if ← failedDir.pathExists then IO.FS.removeDirAll failedDir
    IO.FS.rename stagingDir failedDir
    IO.println ""
    IO.println "═══════════════════════════════════════════════════════════════"
    IO.println s!"✗ BUILD REJECTED: a gate failed. {outputDir}/ is UNTOUCHED (last green build)."
    IO.println s!"  Failed candidate quarantined at {failedDir}/ for diagnosis."
    IO.println "═══════════════════════════════════════════════════════════════"
    return 1

  -- Staging overlays are regenerated from the typed stageHeaders / stageRobots
  -- on the green path only, before promotion (`stage_headers_superset_prod`
  -- proves they never weaken prod).
  if let some overlayDir := spec.stagingOverlayDir then
    IO.FS.createDirAll overlayDir
    IO.FS.writeFile (overlayDir / "_headers") (stageHeaders spec.csp).render
    IO.FS.writeFile (overlayDir / "robots.txt") stageRobots.render

  -- Promote: keep the previous output until the new one is in place; roll
  -- back if the second rename fails; cleanup of the backup is non-fatal.
  let previousDir := System.FilePath.mk (outputDir.toString ++ ".previous")
  if ← previousDir.pathExists then IO.FS.removeDirAll previousDir
  let hadPrevious ← outputDir.pathExists
  if hadPrevious then IO.FS.rename outputDir previousDir
  match ← (IO.FS.rename stagingDir outputDir).toBaseIO with
  | .error e =>
    if hadPrevious then IO.FS.rename previousDir outputDir
    throw (IO.userError s!"promotion failed ({e}); previous output restored, candidate left at {stagingDir}")
  | .ok () => pure ()
  if hadPrevious then
    match ← (IO.FS.removeDirAll previousDir).toBaseIO with
    | .error e => IO.println s!"  ⚠ promoted, but could not remove {previousDir}: {e}"
    | .ok () => pure ()

  -- Baseline bootstrap only: an existing baseline is written by the deploy
  -- script after a production deploy, never by a local build.
  if updateBaseline then
    if ← spec.baselinePath.pathExists then
      IO.println s!"  ⚠ --update-baseline ignored: {spec.baselinePath} exists; the baseline is rewritten after a production deploy"
    else
      if let some parent := spec.baselinePath.parent then IO.FS.createDirAll parent
      IO.FS.writeFile spec.baselinePath (renderBaseline currentEntries (spec.redirects.map (·.from_)))
      IO.println s!"  ✓ baseline bootstrapped: {spec.baselinePath} ({currentEntries.length} files, {spec.redirects.length} redirect obligations)"

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"BUILD COMPLETE: {manifest.files.length + 1} files promoted to {outputDir}/"
  IO.println "═══════════════════════════════════════════════════════════════"
  return 0

end NoGoals.Build
