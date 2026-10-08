/-
  Site audit — the publisher-facing gate suite, over parser FACTS.

  Pure checkers over what a real HTML parser saw (`NoGoals.Verify.HtmlFacts`),
  plus the CSS-input checks (stylesheets are not HTML) and the news/date
  invariants. Everything here FAILS CLOSED: each function returns the
  violations it found; an audit passes only when every list is empty, and
  a file with no facts is a failed gate, never a silently clean one.

  What is NOT here any more: substring extractors over markup. A fact
  about an href, an id, a class or a script came from the parser, with
  quoting, case, comments, entities and raw-text contexts handled the way a
  browser handles them.
-/

import NoGoals.IR.Route
import NoGoals.Meta
import NoGoals.Verify.Date
import NoGoals.Verify.Permalinks
import NoGoals.Verify.HtmlFacts

namespace NoGoals.Verify.SiteAudit

open NoGoals.Verify.HtmlFacts
open NoGoals (originOf?)

/-! ## Reference closure: every internal reference lands on an emitted file

`href`/`src`/`srcset`/`poster` are resolved from the page they appear on
(`NoGoals.resolveUrl`: browser + host semantics); a target must be an emitted
file and a fragment must be an id the target page declares. A form's
`action` may instead be one of the site's DECLARED dynamic endpoints — an
exact string, never a wildcard. -/

structure Violation where
  page : String
  problem : String
deriving Repr

def Violation.render (v : Violation) : String := s!"{v.page}: {v.problem}"

/-- The URL of every candidate in a `srcset`, per the HTML tokenization:
    skip whitespace and commas; a URL is a run of non-whitespace; if it ends
    in commas those end the candidate, otherwise descriptors follow up to the
    next comma (parentheses respected). Commas INSIDE a URL (`data:…;base64,AAAA`)
    are part of the URL. -/
def srcsetUrls (s : String) : List String :=
  let rec go (cs : List Char) (acc : List String) (fuel : Nat) : List String :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      let cs := cs.dropWhile (fun c => c.isWhitespace || c == ',')
      match cs with
      | [] => acc.reverse
      | _ =>
        let url := cs.takeWhile (fun c => !c.isWhitespace)
        let rest := cs.drop url.length
        let trailing := url.reverse.takeWhile (· == ',') |>.length
        if trailing > 0 then
          go rest (String.ofList (url.take (url.length - trailing)) :: acc) fuel
        else
          -- descriptors until an unparenthesized comma
          let rec skipDesc (xs : List Char) (depth : Nat) (fuel : Nat) : List Char :=
            match fuel, xs with
            | 0, _ => xs
            | _, [] => []
            | f + 1, '(' :: t => skipDesc t (depth + 1) f
            | f + 1, ')' :: t => skipDesc t (depth - 1) f
            | f + 1, ',' :: t => if depth == 0 then t else skipDesc t depth f
            | f + 1, _ :: t => skipDesc t depth f
          go (skipDesc rest 0 rest.length) (String.ofList url :: acc) fuel
  go s.toList [] s.length

/-- `(attribute, value)` pairs on an element that name a file. -/
def references (e : Element) : List (String × String) :=
  let one (a : String) : List (String × String) :=
    match e.attr a with | some v => [(a, v)] | none => []
  let many (a : String) (f : String → List String) : List (String × String) :=
    match e.attr a with | some v => (f v).map (a, ·) | none => []
  match e.tag with
  | "a" | "area" | "link" => one "href"
  | "img" => one "src" ++ many "srcset" srcsetUrls
  | "source" => one "src" ++ many "srcset" srcsetUrls
  | "script" | "iframe" | "embed" | "track" | "audio" => one "src"
  | "video" => one "src" ++ one "poster"
  | "object" => one "data"
  | "form" => one "action"
  | _ => []

/-- Every http(s) URL on another origin that the pages reference — the
    liveness gate's input, so an outbound link is checked by being written,
    not by being listed twice. -/
def externalUrls (origin : String) (facts : Facts) : List String :=
  facts.flatMap fun f => f.elements.flatMap fun e => (references e).filterMap fun (_, v) =>
    if (originOf? v).isSome then
      match resolveUrl origin f.path v with
      | .error .external => some v
      | _ => none
    else none

def linkViolations (origin : String) (inventory : List String)
    (dynamicEndpoints : List String) (facts : Facts) : List Violation :=
  facts.flatMap fun f =>
    f.elements.flatMap fun e =>
      (references e).filterMap fun (attr, value) =>
        if attr == "action" && dynamicEndpoints.contains value then none
        else
          match resolveUrl origin f.path value with
          | .error .external => none
          | .error (.malformed reason) => some ⟨f.path, s!"<{e.tag} {attr}=\"{value}\">: {reason}"⟩
          | .ok t =>
            match t.candidates.find? inventory.contains with
            | none => some ⟨f.path, s!"<{e.tag} {attr}=\"{value}\">: no emitted file at {String.intercalate " or " t.candidates}"⟩
            | some target =>
              match t.fragment with
              | none => none
              | some "" => none
              | some frag =>
                match facts.find? (·.path == target) with
                | some tf => if tf.ids.contains frag then none
                    else some ⟨f.path, s!"<{e.tag} {attr}=\"{value}\">: {target} declares no id=\"{frag}\""⟩
                | none => some ⟨f.path, s!"<{e.tag} {attr}=\"{value}\">: fragment #{frag} on a non-page target {target}"⟩

/-! ## Click-path reachability

Every page is a click-path away from a declared root; deliberately
unreachable pages (a form's redirect target) are declared, not
discovered. Wagahai is its own root: a separate site under one origin. -/

/-- Pages an `<a href>` on this page leads to (resolved, emitted, HTML). -/
def outLinks (origin : String) (pages : List String) (f : FileFacts) : List String :=
  ((f.elements.filter (·.tag == "a")).filterMap fun e =>
    match e.attr "href" with
    | none => none
    | some href =>
      match resolveUrl origin f.path href with
      | .ok t => t.candidates.find? pages.contains
      | .error _ => none).eraseDups

/-- Worklist BFS. Fuel is the page count: each step visits at least one new
    page or stops. -/
def reachablePages (adj : List (String × List String)) (roots : List String) : List String :=
  let rec go (fuel : Nat) (frontier visited : List String) : List String :=
    match fuel with
    | 0 => visited
    | fuel + 1 =>
      let next := frontier.flatMap (fun p =>
        ((adj.find? (·.1 == p)).map (·.2)).getD []) |>.eraseDups
        |>.filter (fun p => p ∉ visited)
      if next.isEmpty then visited
      else go fuel next (visited ++ next)
  go adj.length roots roots

def unreachableFrom (origin : String) (facts : Facts) (roots exceptions : List String) : List String :=
  let pages := facts.map (·.path)
  let adj := facts.map fun f => (f.path, outLinks origin pages f)
  let visited := reachablePages adj roots
  pages.filter (fun p => p ∉ visited && p ∉ exceptions)

/-! ## CSP ↔ content — a BOUNDED checker for the policy this site ships

Modelled: `script[src]` and inline `<script>` (script-src), `link[rel~=
stylesheet]`, `<style>` and `style=` (style-src), `img[src|srcset]`
(img-src), `iframe[src]` (frame-src), `form[action]` (form-action, which
does NOT fall back to default-src), inline `on*` handlers and
`javascript:` hrefs (inline script). Fetch directives fall back to
`default-src`. Elements this checker does not model (`base`, `video`,
`audio`, `source`, `track`, `object`, `embed`) FAIL the gate as
unsupported rather than passing silently; so do policies that use nonces,
hashes or `'strict-dynamic'`. Not checked: what scripts and stylesheets
themselves fetch (`font-src`, `connect-src`) — those are not declared in
HTML. -/

structure CspDirective where
  name : String
  values : List String
deriving Repr

def parseCsp (policy : String) : List CspDirective :=
  policy.splitOn ";" |>.filterMap (fun d =>
    match (d.trimAscii.toString.splitOn " ").filter (· ≠ "") with
    | [] => none
    | name :: vals => some { name, values := vals })

def directiveValues (csp : List CspDirective) (name : String) : Option (List String) :=
  (csp.find? (·.name == name)).map (·.values)

def fetchDirectives : List String :=
  ["script-src", "style-src", "img-src", "frame-src", "font-src", "connect-src", "media-src", "object-src"]

/-- Effective source list: the directive itself, else `default-src` for
    fetch directives only. `none` means the directive is absent and has no
    fallback (e.g. `form-action`), i.e. unrestricted. -/
def effectiveSources (csp : List CspDirective) (name : String) : Option (List String) :=
  match directiveValues csp name with
  | some vs => some vs
  | none => if fetchDirectives.contains name then directiveValues csp "default-src" else none

def hostMatches (source origin : String) : Bool :=
  source == origin || source == "*" ||
  (source.startsWith "https://*." && (origin.drop "https://".length).endsWith (source.drop "https://*".length))

/-- Does `sources` allow loading `url` from a page on `siteOrigin`? -/
def sourcesAllow (sources : List String) (siteOrigin url : String) : Bool :=
  if url.startsWith "data:" then sources.contains "data:"
  else match originOf? url with
    | none => sources.contains "'self'" || sources.contains "*"
    | some o =>
      (o == siteOrigin && sources.contains "'self'") || sources.any (hostMatches · o)

def unsupportedPolicyFeatures (csp : List CspDirective) : List String :=
  csp.flatMap fun d => d.values.filter fun v =>
    v.startsWith "'nonce-" || v.startsWith "'sha256-" || v.startsWith "'sha384-" ||
    v.startsWith "'sha512-" || v == "'strict-dynamic'"

def unmodelledTags : List String := ["base", "video", "audio", "source", "track", "object", "embed"]

def relTokens (e : Element) : List String :=
  ((e.attr "rel").getD "").splitOn " " |>.map String.toLower |>.filter (· ≠ "")

def checkPageCsp (policy siteOrigin : String) (f : FileFacts) : List Violation :=
  let csp := parseCsp policy
  let v (problem : String) : Violation := ⟨f.path, problem⟩
  let unsupported := (unsupportedPolicyFeatures csp).map fun feat =>
    v s!"policy uses {feat}, which this checker does not model"
  let allows (directive url : String) : Option Violation :=
    match effectiveSources csp directive with
    | none => none
    | some srcs => if sourcesAllow srcs siteOrigin url then none
        else some (v s!"loads {url} but {directive} does not allow it")
  let inlineAllowed (directive : String) : Bool :=
    ((effectiveSources csp directive).getD []).contains "'unsafe-inline'"
  let perElement := f.elements.flatMap fun e =>
    let handlers := e.attrs.filter (fun a => a.1.startsWith "on") |>.map fun a =>
      v s!"<{e.tag} {a.1}=…>: inline event handler (script-src has no 'unsafe-inline')"
    let styleAttr := match e.attr "style" with
      | some _ => if inlineAllowed "style-src" then [] else [v s!"<{e.tag} style=…>: inline style but style-src has no 'unsafe-inline'"]
      | none => []
    let jsHref := match e.attr "href" with
      | some h => if h.trimAscii.toString.toLower.startsWith "javascript:" then [v s!"<{e.tag} href=\"javascript:…\">: inline script"] else []
      | none => []
    let byTag : List Violation :=
      if unmodelledTags.contains e.tag then [v s!"<{e.tag}>: element not modelled by the CSP checker"]
      else match e.tag with
      | "script" =>
        match e.attr "src" with
        | some src => (allows "script-src" src).toList
        | none => if e.hasText && !inlineAllowed "script-src" then
            [v "inline <script> but script-src has no 'unsafe-inline'"] else []
      | "style" => if inlineAllowed "style-src" then [] else [v "<style> element but style-src has no 'unsafe-inline'"]
      | "link" =>
        if (relTokens e).contains "stylesheet" then
          match e.attr "href" with
          | some h => (allows "style-src" h).toList
          | none => []
        else []
      | "img" =>
        (match e.attr "src" with | some s => (allows "img-src" s).toList | none => []) ++
        (match e.attr "srcset" with | some s => (srcsetUrls s).filterMap (allows "img-src") | none => [])
      | "iframe" => match e.attr "src" with | some s => (allows "frame-src" s).toList | none => []
      | "form" => match e.attr "action" with | some a => (allows "form-action" a).toList | none => []
      | _ => []
    handlers ++ styleAttr ++ jsHref ++ byTag
  unsupported ++ perElement

/-- Stale allowances: script-src host sources no page's `<script src>` uses.
    (`frame-src` is not reported: widgets inject their iframes at runtime,
    so static HTML cannot show whether an allowance is used.) -/
def staleCspAllowances (policy : String) (facts : Facts) : List String :=
  let csp := parseCsp policy
  let used : List String :=
    (facts.flatMap fun f => (f.elements.filter (·.tag == "script")).filterMap fun e =>
      (e.attr "src").bind originOf?) |>.eraseDups
  let hosts := ((directiveValues csp "script-src").getD []).filter (·.startsWith "https://")
  hosts.filter fun h => !used.any (hostMatches h)

/-! ## SEO coherence: rendered head values equal the route's -/

def hrefsWhere (f : FileFacts) (tag : String) (pred : Element → Bool) (attr : String) : List String :=
  (f.elements.filter fun e => e.tag == tag && pred e).filterMap (·.attr attr)

def metaContent (f : FileFacts) (key value : String) : List String :=
  (f.elements.filter fun e => e.tag == "meta" && e.attr key == some value).filterMap (·.attr "content")

/-- Two lists agree as sets (small lists; the head of a page). -/
def sameSet {α} [BEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)

/-- For every route-generated page — route coherence: exactly one canonical
    link equal to the route's URL, the hreflang alternates equal to
    `alternatesFor` as a set,
    `og:url` equal to the canonical, `og:locale` equal to the language's. -/
def seoViolations (baseUrl : String) (d : Lang) (routePages : List (Route × String))
    (facts : Facts) : List Violation :=
  routePages.flatMap fun (route, path) =>
    match facts.find? (·.path == path) with
    | none => [⟨path, "no facts for a route page"⟩]
    | some f =>
      let canonical := baseUrl ++ route.href d
      let canon := hrefsWhere f "link" (fun e => (relTokens e).contains "canonical") "href"
      let alts := (f.elements.filter fun e => e.tag == "link" && (relTokens e).contains "alternate" && (e.attr "hreflang").isSome).filterMap fun e =>
        match e.attr "hreflang", e.attr "href" with
        | some tag, some href => some (tag, href)
        | _, _ => none
      let expected := (Meta.alternatesFor baseUrl d route.slug).map fun a => (a.tag.code, a.url)
      (if canon == [canonical] then [] else [⟨path, s!"canonical link is {canon}, expected [{canonical}]"⟩]) ++
      (if sameSet alts expected then [] else [⟨path, s!"hreflang alternates are {alts}, expected {expected}"⟩]) ++
      (if metaContent f "property" "og:url" == [canonical] then [] else [⟨path, s!"og:url is {metaContent f "property" "og:url"}, expected [{canonical}]"⟩]) ++
      (if metaContent f "property" "og:locale" == [route.lang.ogLocale] then [] else [⟨path, s!"og:locale is {metaContent f "property" "og:locale"}, expected [{route.lang.ogLocale}]"⟩])

/-- For every route-generated page — metadata completeness, the other half
    of the head contract: `<html lang>` is the route's language, exactly one
    `<title>`, one non-empty description, one each of og:title /
    og:description / og:type, and og:locale:alternate names exactly the
    other languages. Coherence with the route is `seoViolations`. -/
def metadataViolations (routePages : List (Route × String)) (facts : Facts) : List Violation :=
  routePages.flatMap fun (route, path) =>
    match facts.find? (·.path == path) with
    | none => [⟨path, "no facts for a route page"⟩]
    | some f =>
      let one (what : String) (vals : List String) : List Violation :=
        match vals with
        | [v] => if v.isEmpty then [⟨path, s!"{what} is empty"⟩] else []
        | [] => [⟨path, s!"no {what}"⟩]
        | _ => [⟨path, s!"{what} appears {vals.length} times"⟩]
      let htmlLang := (f.elements.filter (·.tag == "html")).filterMap (·.attr "lang")
      let otherLocales := (Meta.switcherTargets route.lang).map (·.ogLocale)
      let alternates := metaContent f "property" "og:locale:alternate"
      (if htmlLang == [route.lang.code] then [] else [⟨path, s!"<html lang> is {htmlLang}, expected [{route.lang.code}]"⟩]) ++
      (if (f.elements.filter (·.tag == "title")).length == 1 then [] else [⟨path, "no single <title>"⟩]) ++
      one "meta description" (metaContent f "name" "description") ++
      one "og:title" (metaContent f "property" "og:title") ++
      one "og:description" (metaContent f "property" "og:description") ++
      one "og:type" (metaContent f "property" "og:type") ++
      (if sameSet alternates otherLocales then [] else [⟨path, s!"og:locale:alternate is {alternates}, expected {otherLocales}"⟩])

/-! ## Untranslated-content detection

An English page containing CJK text is almost always an untranslated leak.
Callers pass an allowlist for deliberate Japanese on EN pages (the language
switcher label, the brand mark caption). Runs over VISIBLE text and
human-facing attributes — markup and URLs are not text. -/

def isCJK (c : Char) : Bool :=
  let n := c.toNat
  (0x3040 ≤ n && n ≤ 0x30FF) ||   -- hiragana + katakana
  (0x4E00 ≤ n && n ≤ 0x9FFF) ||   -- CJK unified ideographs
  (0x3000 ≤ n && n ≤ 0x303F) ||   -- CJK punctuation
  (0xFF00 ≤ n && n ≤ 0xFFEF)      -- fullwidth forms

/-- CJK runs found after removing allowlisted substrings; up to `limit`. -/
def cjkLeaks (text : String) (allowlist : List String) (limit : Nat := 5) : List String :=
  let cleaned := allowlist.foldl (fun h a => h.replace a "") text
  let rec runs (cs : List Char) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] => if cur.isEmpty then acc.reverse else (String.ofList cur.reverse :: acc).reverse
    | c :: rest =>
      if isCJK c then runs rest (c :: cur) acc
      else if cur.isEmpty then runs rest [] acc
      else runs rest [] (String.ofList cur.reverse :: acc)
  (runs cleaned.toList [] []).eraseDups.take limit

def humanText (f : FileFacts) : String :=
  f.text ++ " " ++ String.intercalate " " f.attrText

/-! ## Double-escaping detector

After the parser decoded entities, visible text that still contains
`&amp;`, `&lt;` … was escaped twice: each escape is correct in isolation,
so only the composition can be seen, and only here. -/

def doubleEscaped (f : FileFacts) : List String :=
  ["&amp;", "&lt;", "&gt;", "&quot;", "&#x27;"].filter
    (fun marker => ((humanText f).splitOn marker).length > 1)

/-! ## CSS contract (stylesheets are CSS input, not HTML facts) -/

/-- Every class token on every element of a page. -/
def classTokens (f : FileFacts) : List String :=
  (f.elements.filterMap (·.attr "class")).flatMap (·.splitOn " ") |>.filter (· ≠ "") |>.eraseDups

/-- Is `.token` mentioned anywhere in the stylesheet? Substring-level on
    `.token` with a non-name character after it — deliberately permissive
    (media queries, pseudo-classes, compound selectors all match). -/
def cssDefines (css token : String) : Bool :=
  (css.splitOn s!".{token}").drop 1 |>.any (fun rest =>
    match rest.toList.head? with
    | none => true
    | some c => !(c.isAlphanum || c == '-' || c == '_'))

/-- Classes used in pages but absent from the stylesheet. -/
def undefinedClasses (css : String) (facts : Facts) : List String :=
  (facts.flatMap classTokens).eraseDups.filter (fun t => !cssDefines css t)

/-- `/assets/...` references inside a STYLESHEET (`url(/assets/…)`, quoted
    or bare) — the hero backgrounds live in CSS. -/
def extractCssAssetRefs (css : String) : List String :=
  (css.splitOn "url(").drop 1 |>.filterMap (fun rest =>
    let body := rest.takeWhile (· ≠ ')')
    let path := (body.dropWhile (fun c => c == '"' || c == '\'')).takeWhile
      (fun c => c ≠ '"' && c ≠ '\'')
    if path.startsWith "/assets/" then some (path.drop 1).toString else none)
  |>.eraseDups

def missingAssets (buildDir : System.FilePath) (refs : List String) : IO (List String) := do
  let mut missing := []
  for r in refs do
    unless (← (buildDir / r).pathExists) do
      missing := missing ++ [r]
  return missing

/-! ## News invariants -/

open NoGoals.Verify (IsoDate)

def newsSorted (dates : List IsoDate) : Bool :=
  match dates with
  | [] | [_] => true
  | d1 :: d2 :: rest => (d2.daysSinceY0 ≤ d1.daysSinceY0) && newsSorted (d2 :: rest)

def futureDated (dates : List IsoDate) (today : IsoDate) : List IsoDate :=
  dates.filter (fun d => today.daysSinceY0 < d.daysSinceY0)

/-! ## Deploy diff vs baseline -/

open NoGoals.Verify.Permalinks (BaselineEntry)

structure DeployDiff where
  added : List String
  removed : List String
  changed : List String
deriving Repr

def diffAgainstBaseline (baseline : List BaselineEntry)
    (current : List (String × String)) : DeployDiff :=
  let baseFiles := baseline.filterMap fun | .file h p => some (h, p) | .redirect _ => none
  let basePaths := baseFiles.map (·.2)
  let curPaths := current.map (·.2)
  let added := curPaths.filter (· ∉ basePaths)
  let removed := basePaths.filter (· ∉ curPaths)
  let changed := current.filterMap (fun (h, p) =>
    match baseFiles.find? (·.2 == p) with
    | some (bh, _) => if bh ≠ h then some p else none
    | none => none)
  { added, removed, changed }

def DeployDiff.render (d : DeployDiff) : String :=
  let sec (label : String) (xs : List String) : List String :=
    if xs.isEmpty then [] else [s!"{label} ({xs.length}):"] ++ xs.map (s!"  {·}")
  let lines := sec "added" d.added ++ sec "removed" d.removed ++ sec "changed" d.changed
  if lines.isEmpty then "no changes vs baseline" else String.intercalate "\n" lines

end NoGoals.Verify.SiteAudit
