/-
  Report renderers — the verification pages, the text report, the receipt.

  The HTML pages are typed `Render.Tree.Html` values (text escaped at
  render, no `raw` node anywhere), so the pages that carry the site's
  receipts are themselves covered by the same tree well-formedness the
  chrome is. The JSON receipt is the machine contract: deterministic, no
  timestamp, every string through `jsonEscape`.
-/

import NoGoals.Compile.Evidence
import NoGoals.Render.Tree
import NoGoals.Meta
import NoGoals.DSL

namespace NoGoals.Compile

open NoGoals.Render.Tree (Html)
open NoGoals.DSL (L)

/-! ## Control tests (result shape) -/

/-- Result of a control test -/
structure ControlResult where
  name : String
  description : String
  expectedFailures : List String
  actualFailures : List String
  passed : Bool  -- True if actual matches expected
deriving Repr

/-! ## Where the report lives

The verification report is a pair of reserved routes per language, derived
by THE path function like every content route: `/verification/` and
`/verification/full/` in the default language, prefixed in the other. Their
content is the post-gate evidence, so they are not pages of the `Site` and
sit outside the bridge's proofs; the build reserves their paths against
collision and the finalization pass runs the page gates over them. The
report says exactly that about itself. -/

/-- The two report pages. Everything about a page — its slug, its
    stylesheet, its tree — follows from this enumeration. -/
inductive ReportKind | quiet | full
deriving DecidableEq

def ReportKind.slug : ReportKind → Slug
  | .quiet => Slug.lit "verification"
  | .full => Slug.lit "verification/full"

def ReportKind.route (k : ReportKind) (lang : Lang) : Route := ⟨k.slug, lang⟩

def reportRoute (lang : Lang) : Route := ReportKind.quiet.route lang
def fullReportRoute (lang : Lang) : Route := ReportKind.full.route lang

/-- The report's shared files (one copy, no language). -/
def quietCssPath : String := "verification/style.css"
def fullCssPath : String := "verification/full/style.css"
def textReportPath : String := "verification-report.txt"
def receiptPath : String := "verification/receipt.json"

/-- One source tree of the build: `git rev-parse HEAD` and whether the
    worktree had uncommitted changes. -/
structure SourceId where
  name : String
  commit : String
  dirty : Bool

/-- The receipt's flat form: `name.commit` and `name.dirty`. -/
def SourceId.pairs (s : SourceId) : List (String × String) :=
  [(s!"{s.name}.commit", s.commit), (s!"{s.name}.dirty", toString s.dirty)]

/-- The page's stylesheet path and text. -/
def ReportKind.cssPath : ReportKind → String
  | .quiet => quietCssPath
  | .full => fullCssPath

/-- Both report kinds in every language. -/
def reportRoutes : List Route := Lang.all.flatMap fun l => [reportRoute l, fullReportRoute l]

/-- What the report needs to know about the build it describes. -/
structure ReportCtx where
  origin : String
  /-- The site's default language (decides which routes are unprefixed). -/
  d : Lang
  /-- Label of each language's variant, for the switcher. -/
  langName : Lang → String
  /-- The trees the artifact was built from. -/
  sources : List SourceId
  /-- The profile the build ran under (`build` / `offline-audit` / `full-audit`). -/
  profile : String

/-- The recorded commits identify the source only if every tree was clean
    (`gitState` reports an unknown commit as dirty). -/
def ReportCtx.sourceIdentified (c : ReportCtx) : Bool := c.sources.all (!·.dirty)

/-- A bilingual label in the page's language. -/
def txt (lang : Lang) (b : L) : Html := .text (b.get lang)

def scopeNote : L :=
  ⟨"概要レポートと詳細レポートは、ほかのページと同じパス関数を使う予約済みルートに配置されます。内容はゲート実行後の検証結果であるため、サイトのページ集合に関する証明の対象外です。ビルド時には、出力パスがほかのファイルと衝突しないようにし、監査プロファイルでは最終検査でほかのページと同じゲートを実行します。",
   "The summary and the full report are reserved routes derived by the same path function as every other page, but their content is the post-gate evidence, so they are outside the proofs about the site's page set. The build keeps their paths from colliding with any other file and, under an audit profile, runs the same gates over them in a finalization pass."⟩

/-! ## Text report -/

def formatStatus : GuaranteeStatus → String
  | .enforced mechanism => s!"✓ ENFORCED ({mechanism})"
  | .checked => "✓ PASSED"
  | .failed reason => s!"✗ FAILED: {reason}"
  | .notApplicable => "○ N/A"
  | .skipped reason => s!"◌ SKIPPED: {reason}"

def formatGuarantee (g : Guarantee) : String :=
  let loc := match g.location with | some l => s!" [{l}]" | none => ""
  let scopeTag := if g.scope == .kernel then " (kernel renderer only)" else ""
  s!"  {formatStatus g.status}\n    {g.name}{scopeTag}{loc}\n    {g.description}\n"

def reportCategories : List String := ["Type Safety", "Theorems", "Structure", "Security", "CSS", "Runtime"]

/-- Content routes: every content slug in every language. -/
def VerificationReport.routeCount (r : VerificationReport) : Nat := r.pageCount * Lang.all.length

/-- The verdict line, honest about what did not run: `allPassed` only means
    "no failures". -/
def verdict (r : VerificationReport) : L :=
  if !r.allPassed then ⟨s!"{r.failCount} 件のチェックに失敗", s!"{r.failCount} CHECK(S) FAILED"⟩
  else if r.skippedCount == 0 then ⟨"すべてのチェックに合格", "ALL CHECKS PASSED"⟩
  else ⟨s!"失敗なし — 未実行のチェック {r.skippedCount} 件", s!"NO FAILURES — {r.skippedCount} CHECK(S) NOT RUN"⟩

/-- Generate plain text verification report -/
def formatReport (r : VerificationReport) : String :=
  let header := s!"
╔══════════════════════════════════════════════════════════════════════════════╗
║                        NoGoals VERIFICATION REPORT                           ║
║      A static site generator with proved route invariants and                ║
║                     fail-closed build checks                                 ║
╚══════════════════════════════════════════════════════════════════════════════╝

Site:           {r.siteName}
Generated:      {r.timestamp}
Content slugs:  {r.pageCount}
Content routes: {r.routeCount} (slugs × {Lang.all.length} languages)
Report routes:  {reportRoutes.length}
Assets:         {r.assetCount}

{scopeNote.en}

"
  let categories := reportCategories.filterMap fun cat =>
    let gs := r.guarantees.filter (·.category == cat)
    if gs.isEmpty then none
    else some (s!"── {cat} ──\n" ++ String.join (gs.map formatGuarantee))
  let summary := s!"
Enforced: {r.enforcedCount}  Checked: {r.checkedCount}  Failed: {r.failCount}  Not run: {r.skippedCount}
{(verdict r).en}
"
  header ++ String.intercalate "\n" categories ++ summary

def formatControlText (controls : List ControlResult) : String :=
  let lines := controls.map fun c =>
    let status := if c.passed then "✓" else "✗"
    let kind := if c.expectedFailures.isEmpty then "positive control" else "negative control"
    s!"  {status} {c.name} ({kind}): expected {c.expectedFailures.length} failure(s), got {c.actualFailures.length}"
  "\n── Control tests ──\n" ++ String.intercalate "\n" lines ++ "\n"

/-- Generate plain text verification report with control tests -/
def formatReportWithControls (r : VerificationReport) (controls : List ControlResult) : String :=
  let controlStatus := if controls.all (·.passed) then
    "\n✓ CONTROL TESTS PASSED\n"
  else
    "\n✗ CONTROL TESTS FAILED\n"
  formatReport r ++ formatControlText controls ++ controlStatus

/-! ## Stylesheets (external: the CSP forbids `<style>`) -/

def reportCss : String :=
  ":root{--pass:#22c55e;--fail:#ef4444;--enforced:#3b82f6;--na:#9ca3af;--bg:#0f172a;--card:#1e293b;--text:#f8fafc;--muted:#94a3b8}" ++
  "*{box-sizing:border-box;margin:0;padding:0}" ++
  "body{font-family:system-ui,-apple-system,\"Noto Sans JP\",sans-serif;background:var(--bg);color:var(--text);line-height:1.6;padding:2rem}" ++
  ".container{max-width:900px;margin:0 auto}" ++
  "header{text-align:center;margin-bottom:2rem;padding:2rem;background:var(--card);border-radius:1rem}" ++
  "h1{font-size:1.5rem;margin-bottom:0.5rem}.tagline{color:var(--muted);font-size:0.9rem}" ++
  ".lang-switch{text-align:right;font-size:.85rem;margin-bottom:1rem}.lang-switch a{color:var(--muted)}" ++
  ".meta{margin-top:1rem;display:flex;flex-wrap:wrap;justify-content:center;gap:1.5rem}" ++
  ".meta-item{text-align:center}.meta-value{font-size:1.5rem;font-weight:bold}.meta-label{font-size:0.8rem;color:var(--muted)}" ++
  ".scope{color:var(--muted);font-size:.9rem;margin:0 auto 2rem;max-width:44rem;text-align:center}" ++
  ".result{padding:1.5rem;border-radius:0.5rem;text-align:center;margin:2rem 0;font-size:1.2rem;font-weight:bold}" ++
  ".result--banner{margin-top:1rem}" ++
  ".sv-enforced{color:var(--enforced)}.sv-checked{color:var(--pass)}.sv-failed{color:var(--fail)}.sv-skipped{color:var(--na)}" ++
  ".result.passed{background:rgba(34,197,94,0.2);color:var(--pass)}.result.failed{background:rgba(239,68,68,0.2);color:var(--fail)}" ++
  ".summary{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:1rem;margin-bottom:2rem}" ++
  ".summary-card{background:var(--card);padding:1rem;border-radius:0.5rem;text-align:center}" ++
  ".summary-value{font-size:2rem;font-weight:bold}.summary-label{font-size:0.8rem;color:var(--muted)}" ++
  ".category{margin-bottom:2rem}.category h2{font-size:1rem;color:var(--muted);border-bottom:1px solid var(--card);padding-bottom:0.5rem;margin-bottom:1rem}" ++
  ".guarantee{background:var(--card);padding:1rem;border-radius:0.5rem;margin-bottom:0.5rem;border-left:4px solid var(--muted)}" ++
  ".guarantee.enforced{border-left-color:var(--enforced)}.guarantee.checked{border-left-color:var(--pass)}.guarantee.failed{border-left-color:var(--fail)}" ++
  ".status{font-size:0.75rem;font-weight:bold;text-transform:uppercase;margin-bottom:0.25rem}" ++
  ".enforced .status{color:var(--enforced)}.checked .status{color:var(--pass)}.failed .status{color:var(--fail)}.na .status{color:var(--na)}.skipped .status{color:var(--na)}" ++
  ".scope-note{display:inline-block;font-size:0.7rem;color:var(--na);border:1px solid var(--na);border-radius:4px;padding:0 0.4em;margin-left:0.5em;vertical-align:middle}" ++
  ".name{font-weight:600}.name code{font-size:0.8rem;color:var(--muted)}.description{font-size:0.9rem;color:var(--muted)}" ++
  "footer{text-align:center;padding:2rem;color:var(--muted);font-size:0.8rem}footer a{color:var(--enforced)}"

def fullReportCss : String := reportCss

def quietVerificationCss : String :=
  "body{margin:0;background:#0f172a;color:#f8fafc;font-family:system-ui,-apple-system,\"Noto Sans JP\",sans-serif;line-height:1.7}" ++
  "main{max-width:38rem;margin:0 auto;padding:4rem 1.25rem}" ++
  ".lang-switch{font-size:.85rem;margin-bottom:1.5rem}.lang-switch a{color:#94a3b8}" ++
  "h1{font-size:1.4rem;margin:0 0 1rem;line-height:1.4}" ++
  "p{color:#cbd5e1}.scope{color:#94a3b8;font-size:.9rem}" ++
  ".counts{display:flex;flex-wrap:wrap;gap:.75rem;margin:1.5rem 0}.counts div{flex:1;min-width:8rem;background:#1e293b;border-radius:.5rem;padding:.8rem;text-align:center}" ++
  ".counts b{display:block;font-size:1.4rem;color:#f8fafc}.counts span{font-size:.75rem;color:#94a3b8}" ++
  ".tiers{display:flex;gap:1rem;margin:1.5rem 0}" ++
  ".tier{flex:1;background:#1e293b;border-radius:.5rem;padding:1rem;text-align:center}" ++
  ".tier b{display:block;font-size:1.6rem;color:#f8fafc}.tier span{font-size:.8rem;color:#94a3b8}" ++
  "ul{padding-left:1.2rem;color:#cbd5e1}li{margin:.4rem 0}" ++
  "code{background:#1e293b;padding:.1em .4em;border-radius:4px;font-size:.85em;color:#7dd3fc}" ++
  "a{color:#7dd3fc}.cmd{background:#1e293b;border-radius:.5rem;padding:.8rem 1rem;font-family:ui-monospace,monospace;font-size:.85rem;color:#e2e8f0}" ++
  ".source{font-family:ui-monospace,monospace;font-size:.8rem;color:#94a3b8;list-style:none;padding:0}" ++
  ".foot-link{margin-top:2.5rem;font-size:1rem}.foot-link a{text-decoration:underline}" ++
  ".foot{margin-top:.75rem;font-size:.8rem;color:#64748b}"

/-! ## Labels, rendered one language per page

Guarantee names, descriptions, mechanisms and anchors are English
identifiers and are shown in English on both pages, tagged `lang="en"`.
Everything around them is an `L`: both languages written once, the page's
language chosen at render time. -/

def categoryLabel : String → L
  | "Type Safety" => ⟨"型安全性", "Type Safety"⟩
  | "Theorems" => ⟨"定理", "Theorems"⟩
  | "Structure" => ⟨"構造", "Structure"⟩
  | "Security" => ⟨"セキュリティ", "Security"⟩
  | "CSS" => ⟨"CSS", "CSS"⟩
  | "Runtime" => ⟨"実行時", "Runtime"⟩
  | other => ⟨other, other⟩

def statusClass : GuaranteeStatus → String
  | .enforced _ => "enforced"
  | .checked => "checked"
  | .failed _ => "failed"
  | .notApplicable => "na"
  | .skipped _ => "skipped"

/-- An English identifier or message on a page of either language. -/
def en (s : String) : Html := .el "span" [("lang", "en")] [.text s]

/-- Status in the page's language, with the (English, technical) mechanism or reason. -/
def statusNodes (lang : Lang) : GuaranteeStatus → List Html
  | .enforced m => [txt lang ⟨"静的保証", "ENFORCED"⟩, .text " (", en m, .text ")"]
  | .checked => [txt lang ⟨"合格", "PASSED"⟩]
  | .failed reason => [txt lang ⟨"失敗", "FAILED"⟩, .text ": ", en reason]
  | .notApplicable => [txt lang ⟨"該当なし", "N/A"⟩]
  | .skipped reason => [txt lang ⟨"未実行", "NOT RUN"⟩, .text ": ", en reason]

def guaranteeTree (lang : Lang) (g : Guarantee) : Html :=
  let loc : List Html := match g.location with
    | some l => [.text " ", .el "code" [("lang", "en")] [.text s!"[{l}]"]]
    | none => []
  let scopeTag : List Html := if g.scope == .kernel then
    [.el "span" [("class", "scope-note")] [txt lang ⟨"カーネルレンダラーのみ", "kernel renderer only"⟩]] else []
  .el "div" [("class", "guarantee " ++ statusClass g.status)] [
    .el "div" [("class", "status")] (statusNodes lang g.status),
    .el "div" [("class", "name")] ([en g.name] ++ scopeTag ++ loc),
    .el "div" [("class", "description"), ("lang", "en")] [.text g.description]]

def metaItem (lang : Lang) (value : String) (label : L) : Html :=
  .el "div" [("class", "meta-item")] [
    .el "div" [("class", "meta-value")] [.text value],
    .el "div" [("class", "meta-label")] [txt lang label]]

def summaryCard (lang : Lang) (cls value : String) (label : L) : Html :=
  .el "div" [("class", "summary-card")] [
    .el "div" [("class", "summary-value " ++ cls)] [.text value],
    .el "div" [("class", "summary-label")] [txt lang label]]

def controlsTree (lang : Lang) (controls : List ControlResult) : List Html :=
  let items := controls.map fun c =>
    -- A control with no expected failures is the positive one.
    let name : L := if c.expectedFailures.isEmpty then ⟨"陽性対照", "Positive Control"⟩ else ⟨"陰性対照", "Negative Control"⟩
    let details : L :=
      if c.passed then
        if c.expectedFailures.isEmpty then ⟨"期待どおりすべて合格", "All checks passed as expected"⟩
        else ⟨s!"想定した{c.actualFailures.length}件の違反を検出", s!"Detected {c.actualFailures.length} expected violations"⟩
      else ⟨s!"期待値 {c.expectedFailures.length} 件、実際 {c.actualFailures.length} 件",
            s!"Expected {c.expectedFailures.length} failures, got {c.actualFailures.length}"⟩
    Html.el "div" [("class", "guarantee " ++ (if c.passed then "checked" else "failed"))] [
      .el "div" [("class", "status")] [.text (((if c.passed then ⟨"合格", "PASSED"⟩ else ⟨"失敗", "FAILED"⟩) : L).get lang)],
      .el "div" [("class", "name")] [txt lang name],
      .el "div" [("class", "description")] [txt lang details]]
  let passed := controls.all (·.passed)
  [.el "section" [("class", "category")] (Html.el "h2" [] [txt lang ⟨"対照テスト", "Control Tests"⟩] :: items),
   .el "div" [("class", if passed then "result passed result--banner" else "result failed result--banner")]
    [.text ((if passed then "✓ " else "✗ ") ++
      ((if passed then ⟨"対照テスト合格", "CONTROL TESTS PASSED"⟩ else ⟨"対照テスト失敗", "CONTROL TESTS FAILED"⟩) : L).get lang)]]

/-! ## Head and switcher — the same metadata every content page carries -/

def ogMeta (p v : String) : Html := .void "meta" [("property", p), ("content", v)]

/-- The canonical URL of a route. -/
def canonicalUrlOf (baseUrl : String) (d : Lang) (route : Route) : String := baseUrl ++ route.href d

/-- `<link rel="alternate" hreflang=…>` for every alternate of the slug, and
    the canonical entry — from the SAME `alternatesFor` the sitemap uses. -/
def alternateLinkTags (baseUrl : String) (d : Lang) (slug : Slug) : List Html :=
  (Meta.alternatesFor baseUrl d slug).map fun alt =>
    .void "link" [("rel", "alternate"), ("hreflang", alt.tag.code), ("href", alt.url)]

/-- The report page's head: what `metadataViolations` and `seoViolations`
    require of every route page. -/
def reportHead (c : ReportCtx) (route : Route) (title description cssPath : String) : Html :=
  let url := canonicalUrlOf c.origin c.d route
  .el "head" [] ([
    .void "meta" [("charset", "UTF-8")],
    .void "meta" [("name", "viewport"), ("content", "width=device-width,initial-scale=1.0")],
    .void "meta" [("name", "description"), ("content", description)],
    .el "title" [] [.text title],
    .void "link" [("rel", "canonical"), ("href", url)]] ++
    alternateLinkTags c.origin c.d route.slug ++
    [ogMeta "og:title" title, ogMeta "og:description" description, ogMeta "og:type" "website",
     ogMeta "og:url" url, ogMeta "og:locale" route.lang.ogLocale] ++
    (Meta.switcherTargets route.lang).map (fun l => ogMeta "og:locale:alternate" l.ogLocale) ++
    [.void "link" [("rel", "stylesheet"), ("href", "/" ++ cssPath)]])

/-- Links to the same report in the other language(s). -/
def langSwitch (c : ReportCtx) (slug : Slug) (lang : Lang) : Html :=
  .el "nav" [("class", "lang-switch"), ("aria-label", ((⟨"言語", "Language"⟩ : L).get lang))]
    ((Meta.switcherTargets lang).map fun l =>
      .el "a" [("href", (Route.mk slug l).href c.d), ("lang", l.code)] [.text (c.langName l)])


/-- The full report: one guarantee list, one language of labels. -/
def fullReportTree (c : ReportCtx) (lang : Lang) (r : VerificationReport) (controls : List ControlResult) : Html :=
  let resultClass := if r.allPassed then "passed" else "failed"
  let categories := reportCategories.filterMap fun cat =>
    let gs := r.guarantees.filter (·.category == cat)
    if gs.isEmpty then none
    else some (Html.el "section" [("class", "category")]
      (Html.el "h2" [] [txt lang (categoryLabel cat)] :: gs.map (guaranteeTree lang)))
  let title := (⟨s!"NoGoals 検証レポート | {r.siteName}", s!"NoGoals verification report | {r.siteName}"⟩ : L).get lang
  let description := (⟨"このビルドのすべての保証と検査結果。保証の区分と根拠を明記。", "Every guarantee and check result of this build, with its tier and basis."⟩ : L).get lang
  .el "html" [("lang", lang.code)] [
    reportHead c (fullReportRoute lang) title description ReportKind.full.cssPath,
    .el "body" [] [
      .el "div" [("class", "container")] ([
        langSwitch c ReportKind.full.slug lang,
        .el "header" [] [
          .el "h1" [] [txt lang ⟨"NoGoals 検証レポート", "NoGoals verification report"⟩],
          .el "p" [("class", "tagline")] [txt lang ⟨"ルートの不変条件を定理で証明し、--audit の検査に失敗すると出力ディレクトリを更新しない静的サイトジェネレーター",
            "A static site generator with proved route invariants and fail-closed build checks"⟩],
          .el "div" [("class", "meta")] [
            metaItem lang (toString r.pageCount) ⟨"コンテンツのスラッグ", "Content slugs"⟩,
            metaItem lang (toString r.routeCount) ⟨"コンテンツのルート", "Content routes"⟩,
            metaItem lang (toString reportRoutes.length) ⟨"レポートのルート", "Report routes"⟩,
            metaItem lang (toString r.assetCount) ⟨"アセット", "Assets"⟩,
            metaItem lang (toString r.guarantees.length) ⟨"保証・検査項目（全件）", "Guarantees (all evidence)"⟩]],
        .el "p" [("class", "scope")] [txt lang scopeNote],
        .el "div" [("class", "result " ++ resultClass)] [.text ((if r.allPassed then "✓ " else "✗ ") ++ (verdict r).get lang)],
        .el "div" [("class", "summary")] [
          summaryCard lang "sv-enforced" (toString r.enforcedCount) ⟨"型・定理による保証", "Enforced by types and theorems"⟩,
          summaryCard lang "sv-checked" (toString r.checkedCount) ⟨"実行時チェック合格", "Runtime checks passed"⟩,
          summaryCard lang "sv-failed" (toString r.failCount) ⟨"失敗", "Failed"⟩,
          summaryCard lang "sv-skipped" (toString r.skippedCount) ⟨"未実行", "Not run"⟩]] ++
        categories ++
        controlsTree lang controls ++
        [.el "footer" [] [
          .el "p" [] [.text (((⟨"生成日時", "Generated"⟩ : L).get lang) ++ s!": {r.timestamp}")],
          .el "p" [] [.text (((⟨"サイト", "Site"⟩ : L).get lang) ++ s!": {r.siteName}")],
          .el "p" [] [.text (((⟨"プロファイル", "Profile"⟩ : L).get lang) ++ ": "), en c.profile],
          .el "p" [] [txt lang ⟨"NoGoals による生成", "Generated by NoGoals"⟩]]])]]

/-! ## The quiet public verification page -/

def quietPageTree (c : ReportCtx) (lang : Lang) (r : VerificationReport) : Html :=
  -- Kernel-scope entries are excluded everywhere on this page: it speaks
  -- about THIS website, and a theorem about the IR renderer is not yet a
  -- property of the shipped bodies. The full report lists them, labeled.
  let siteScoped := r.guarantees.filter (·.scope != .kernel)
  let enforced := siteScoped.filter (fun g => match g.status with | .enforced _ => true | _ => false)
  let checked := siteScoped.filter (fun g => match g.status with | .checked => true | _ => false)
  -- One line per name: the same property may be vouched for at two layers.
  let headline := (enforced.filter (·.headline)).foldl
    (fun acc g => if acc.any (·.name == g.name) then acc else acc ++ [g]) []
  let items := headline.map fun g =>
    Html.el "li" [("lang", "en")] ([Html.el "strong" [] [.text g.name]] ++
      (match g.location with
        | some l => [Html.text " — ", Html.el "code" [] [.text l]]
        | none => []))
  let title := (⟨s!"検証 | {r.siteName}", s!"Verification | {r.siteName}"⟩ : L).get lang
  let description := (⟨"このサイトが型・定理・ビルド時の検査で保証していること、およびそのビルドの識別情報。",
    "What this site guarantees by types, theorems and build-time checks, and how this build is identified."⟩ : L).get lang
  let sourceLines := c.sources.flatMap fun src => src.pairs.map fun (k, v) => Html.el "li" [] [en s!"{k}: {v}"]
  let anchored := enforced.filter (·.location.isSome)
  let intro : L :=
    ⟨s!"このサイトは定理証明器 Lean 4 で構築されています。ページ構成、各テキストフィールドに日本語と英語の値が存在すること、出力パスの一意性は型と定理で保証されます。監査プロファイル（--audit）では、内部リンクの参照先、アセット、CSP を検査します。検査に失敗すると、出力ディレクトリは更新されず、失敗したビルドは隔離されます。型や定理による保証 {enforced.length} 件のうち {anchored.length} 件は、それを保証する Lean の型・定義・定理の名前を示しており、その名前が削除・改名されるとビルドが失敗します。",
     s!"This site is built with the Lean 4 theorem prover. Its page structure, the presence of both languages for every editorial field, and the uniqueness of output paths are guaranteed by types and theorems. Internal-link targets, assets and CSP are checked under an audit profile (--audit), and when a check fails the output directory is not updated and the failed build is quarantined. {anchored.length} of the {enforced.length} type and theorem guarantees identify the Lean type, definition or theorem that enforces them; renaming or deleting such a name fails the build."⟩
  .el "html" [("lang", lang.code)] [
    reportHead c (reportRoute lang) title description ReportKind.quiet.cssPath,
    .el "body" [] [.el "main" [] ([
      langSwitch c ReportKind.quiet.slug lang,
      .el "h1" [] [txt lang ⟨"このウェブサイトは機械検証されています", "This website is machine-verified"⟩],
      .el "p" [] [txt lang intro],
      .el "div" [("class", "counts")] [
        .el "div" [] [.el "b" [] [.text (toString r.pageCount)], .el "span" [] [txt lang ⟨"コンテンツのスラッグ", "content slugs"⟩]],
        .el "div" [] [.el "b" [] [.text (toString r.routeCount)], .el "span" [] [txt lang ⟨"コンテンツのルート（スラッグ × 言語）", "content routes (slugs × languages)"⟩]],
        .el "div" [] [.el "b" [] [.text (toString reportRoutes.length)], .el "span" [] [txt lang ⟨"レポートのルート", "report routes"⟩]]],
      .el "div" [("class", "tiers")] [
        .el "div" [("class", "tier")] [.el "b" [] [.text (toString enforced.length)], .el "span" [] [txt lang ⟨"このサイトに関する保証（型・定理）", "site-scoped guarantees (types, theorems)"⟩]],
        .el "div" [("class", "tier")] [.el "b" [] [.text (toString checked.length)], .el "span" [] [txt lang ⟨"合格したビルド時の検査", "build-time checks passed"⟩]]],
      .el "p" [("class", "scope")] [txt lang (if r.skippedCount == 0
        then ⟨s!"プロファイル「{c.profile}」: 要求されたすべての検査が実行されました。", s!"Profile \"{c.profile}\": every requested check ran."⟩
        else ⟨s!"プロファイル「{c.profile}」: {r.skippedCount} 件の検査はこのビルドでは実行されていません。詳細レポートに明示しています。",
              s!"Profile \"{c.profile}\": {r.skippedCount} check(s) did not run in this build; the full report lists them."⟩)],
      .el "p" [] [txt lang ⟨"主な保証（根拠となる Lean の宣言名付き）", "Headline guarantees (with the supporting Lean declaration)"⟩],
      .el "ul" [] items,
      .el "p" [] [txt lang ⟨"ビルドコマンドとソースの識別情報", "Build command and source identity"⟩],
      .el "div" [("class", "cmd"), ("lang", "en")] [.text "./scripts/build.sh --audit"],
      .el "ul" [("class", "source")] sourceLines] ++
      (if c.sourceIdentified then [] else
        [.el "p" [("class", "scope")] [txt lang ⟨"記録されたコミットでは、このビルドのソースを完全には特定できません（未コミットの変更、または不明なコミット）。",
          "The recorded commits do not fully identify this build's source (uncommitted changes or an unknown commit)."⟩]]) ++
      [.el "p" [("class", "scope")] [txt lang scopeNote],
      .el "p" [("class", "foot-link")] [
        .el "a" [("href", (fullReportRoute lang).href c.d)] [txt lang ⟨"詳細レポートを見る", "See the full report"⟩]],
      .el "p" [("class", "foot")] [txt lang ⟨s!"生成日時: {r.timestamp}", s!"Generated: {r.timestamp}"⟩]])]]

def ReportKind.css : ReportKind → String
  | .quiet => quietVerificationCss
  | .full => fullReportCss

def ReportKind.tree (k : ReportKind) (c : ReportCtx) (lang : Lang) (r : VerificationReport)
    (controls : List ControlResult) : Html :=
  match k with
  | .quiet => quietPageTree c lang r
  | .full => fullReportTree c lang r controls

/-! ## Machine receipt -/

/-- What the build knows about itself that a deploy must be able to check:
    the audit profile it ran under and the gate ids that profile REQUIRES
    (so a receipt missing a required result is refused, not trusted), the
    source identities the artifact was built from, toolchain pins, and the
    date the clock-dependent checks were evaluated against. -/
structure ReceiptMeta where
  /-- `build` / `offline-audit` / `full-audit`. -/
  profile : String
  /-- Every guarantee id this profile must have run; each must appear
      exactly once with a positive tier for a deploy to accept the receipt. -/
  required : List String
  /-- `(key, value)` source identities: consumer/nogoals commit + dirty flags. -/
  source : List (String × String)
  /-- Toolchain and dependency pins. -/
  pins : List (String × String)
  /-- The wall-clock date freshness checks were evaluated against, and how
      it was obtained (e.g. `date +%F`). Empty when no such check ran. -/
  evaluatedDate : String := ""
  evaluatedSource : String := ""
  /-- Redirect SOURCES this artifact honors (file paths). Public in the
      deployed receipt, so a baseline import can recover the obligations of
      a deployed revision without a local build. -/
  redirects : List String := []

/-- The machine-readable half of the verification report: a **deterministic**
    JSON receipt (no timestamp — two builds of the same tree produce the same
    bytes, so tree-comparison gates can hash it like any other output). -/
def formatReceiptJson (r : VerificationReport) (rm : ReceiptMeta) : String :=
  let esc := NoGoals.Meta.jsonEscape
  let tierOf : GuaranteeStatus → String
    | .enforced _ => "enforced"
    | .checked => "checked"
    | .failed _ => "failed"
    | .notApplicable => "not-applicable"
    | .skipped _ => "skipped"
  let mechanismOf : GuaranteeStatus → String
    | .enforced m => m
    | .checked => ""
    | .failed reason => reason
    | .notApplicable => ""
    | .skipped reason => reason
  let gJson (g : Guarantee) : String :=
    let loc := match g.location with
      | some l => s!",\"anchor\":\"{esc l}\""
      | none => ""
    let mech := let m := mechanismOf g.status
      if m.isEmpty then "" else s!",\"mechanism\":\"{esc m}\""
    s!"    \{\"id\":\"{esc g.key}\",\"category\":\"{esc g.category}\",\"name\":\"{esc g.name}\",\"tier\":\"{tierOf g.status}\",\"scope\":\"{esc g.scope.render}\"{mech}{loc}}"
  let guarantees := String.intercalate ",\n" (r.guarantees.map gJson)
  let kv (xs : List (String × String)) : String :=
    String.intercalate "," (xs.map fun (k, v) => s!"\"{esc k}\":\"{esc v}\"")
  let strList (xs : List String) : String :=
    String.intercalate "," (xs.map fun x => s!"\"{esc x}\"")
  s!"\{
  \"site\": \"{esc r.siteName}\",
  \"pages\": {r.pageCount},
  \"assets\": {r.assetCount},
  \"profile\": \{\"name\": \"{esc rm.profile}\", \"required\": [{strList rm.required}]},
  \"source\": \{{kv rm.source}},
  \"pins\": \{{kv rm.pins}},
  \"evaluated\": \{\"date\": \"{esc rm.evaluatedDate}\", \"source\": \"{esc rm.evaluatedSource}\"},
  \"redirects\": [{strList rm.redirects}],
  \"totals\": \{\"guarantees\": {r.guarantees.length}, \"enforced\": {r.enforcedCount}, \"checked\": {r.checkedCount}, \"failed\": {r.failCount}, \"skipped\": {r.skippedCount}},
  \"guarantees\": [
{guarantees}
  ]
}
"

end NoGoals.Compile
