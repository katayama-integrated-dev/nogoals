import NoGoals.Render.Html
import NoGoals.IR.Route
import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.Meta
import NoGoals.Images.Srcset
import NoGoals.Nav.Reachability
import NoGoals.Verify.Date
import NoGoals.Verify.Attestation

/-!
# NoGoals Unit Tests

This module contains unit tests for the NoGoals static site generator library.
Tests verify that core functions behave correctly on representative inputs.

Run tests with: `lake build NoGoalsTest`
If the build succeeds, all tests pass (via #guard assertions).
-/

namespace NoGoals.Test

/-! ## HTML Escape Tests -/

section HtmlEscape

-- Basic escaping
#guard htmlEscape "" = ""
#guard htmlEscape "hello" = "hello"
#guard htmlEscape "a & b" = "a &amp; b"
#guard htmlEscape "a < b" = "a &lt; b"
#guard htmlEscape "a > b" = "a &gt; b"
#guard htmlEscape "say \"hi\"" = "say &quot;hi&quot;"
#guard htmlEscape "it's" = "it&#x27;s"

-- Multiple special characters
#guard htmlEscape "<script>alert('xss')</script>" =
  "&lt;script&gt;alert(&#x27;xss&#x27;)&lt;/script&gt;"

-- All special chars in one string
#guard htmlEscape "&<>\"'" = "&amp;&lt;&gt;&quot;&#x27;"

-- Unicode passthrough (should not be escaped)
#guard htmlEscape "日本語" = "日本語"
#guard htmlEscape "émoji 🎉" = "émoji 🎉"

-- Edge cases
#guard htmlEscape "&amp;" = "&amp;amp;"  -- Double-escape prevention test
#guard htmlEscape "&&&&" = "&amp;&amp;&amp;&amp;"

end HtmlEscape

/-! ## Heading Level Tests -/

section HeadingLevel

#guard hLevelToTag .h1 = "h1"
#guard hLevelToTag .h2 = "h2"
#guard hLevelToTag .h3 = "h3"
#guard hLevelToTag .h4 = "h4"
#guard hLevelToTag .h5 = "h5"
#guard hLevelToTag .h6 = "h6"

end HeadingLevel

/-! ## Display Class Tests -/

section DisplayClass

#guard displayToClass .xs = "text-xs"
#guard displayToClass .sm = "text-sm"
#guard displayToClass .md = "text-md"
#guard displayToClass .lg = "text-lg"
#guard displayToClass .xl = "text-xl"

end DisplayClass

/-! ## URL Rendering Tests -/

section UrlRender

#guard urlToString (.https "example.com" ⟨"/path"⟩) = "https://example.com/path"
#guard urlToString (.https "example.com" ⟨"/"⟩) = "https://example.com/"
#guard urlToString (.http "localhost" ⟨"/dev"⟩) = "http://localhost/dev"
#guard urlToString (.data "image/png" "base64data") = "data:image/png;base64,base64data"

-- Edge cases
#guard urlToString (.https "a.b.c.d" ⟨"/x/y/z"⟩) = "https://a.b.c.d/x/y/z"
#guard urlToString (.https "example.com" ⟨""⟩) = "https://example.com"

end UrlRender

/-! ## Routes — one path function, validated segments -/

section Routes

-- Segments: [a-z0-9-]+, nothing that could escape or collide.
#guard (Segment.parse? "about").isSome
#guard (Segment.parse? "zero-person-company").isSome
#guard (Segment.parse? "About").isNone      -- case
#guard (Segment.parse? "").isNone
#guard (Segment.parse? ".").isNone
#guard (Segment.parse? "..").isNone
#guard (Segment.parse? "a/b").isNone
#guard (Segment.parse? "a b").isNone
#guard (Segment.parse? "日本").isNone

-- Slugs: non-empty segment lists; `a//b`, `/a`, `a/` are rejected.
#guard (Slug.parse? "news/zero-person-company").isSome
#guard (Slug.parse? "index").isSome
#guard (Slug.parse? "a//b").isNone
#guard (Slug.parse? "/a").isNone
#guard (Slug.parse? "a/").isNone
#guard (Slug.parse? "../escape").isNone
#guard (Slug.parse? "").isNone
#guard (Slug.lit "news/x").toString = "news/x"
#guard (Slug.lit "index").isIndex
#guard !(Slug.lit "news/index").isIndex

-- File segments: lowercase, dots allowed, never `.`/`..`.
#guard (AssetPath.parse? "assets/images/logo.png").isSome
#guard (AssetPath.parse? "assets/images/derived/hero-x-1280.jpg").isSome
#guard (AssetPath.parse? "assets/Logo.png").isNone   -- case-insensitive filesystems
#guard (AssetPath.parse? "assets/./x.png").isNone
#guard (AssetPath.parse? "../x.png").isNone
#guard (AssetPath.parse? "assets//x.png").isNone
#guard (AssetPath.lit "assets/images/logo.png").href = "/assets/images/logo.png"

-- The one path function: href and output file are two views of one list.
def rIndexJa : Route := ⟨Slug.lit "index", .ja⟩
def rIndexEn : Route := ⟨Slug.lit "index", .en⟩
def rAboutJa : Route := ⟨Slug.lit "about", .ja⟩
def rNewsEn : Route := ⟨Slug.lit "news/x", .en⟩
#guard rIndexJa.href .ja = "/"
#guard rIndexJa.outputPath .ja = "index.html"
#guard rIndexEn.href .ja = "/en/"
#guard rIndexEn.outputPath .ja = "en/index.html"
#guard rAboutJa.href .ja = "/about/"
#guard rAboutJa.outputPath .ja = "about/index.html"
#guard rNewsEn.href .ja = "/en/news/x/"
#guard rNewsEn.outputPath .ja = "en/news/x/index.html"
-- default language flips which variant is unprefixed
#guard rIndexEn.href .en = "/"
#guard rIndexJa.href .en = "/ja/"

-- Browser + host resolution.
def origin := "https://x.test"
def resolvesTo (r : Except ResolveError Target) (t : Target) : Bool :=
  match r with | .ok t' => t' == t | .error _ => false
def isMalformed (r : Except ResolveError Target) : Bool :=
  match r with | .error (.malformed _) => true | _ => false
def isExternal (r : Except ResolveError Target) : Bool :=
  match r with | .error .external => true | _ => false
#guard resolvesTo (resolveUrl origin "index.html" "/about/") ⟨["about/index.html"], none⟩
#guard resolvesTo (resolveUrl origin "index.html" "/") ⟨["index.html"], none⟩
#guard resolvesTo (resolveUrl origin "news/a/index.html" "../b/") ⟨["news/b/index.html"], none⟩
#guard resolvesTo (resolveUrl origin "wagahai/index.html" "privacy.html") ⟨["wagahai/privacy.html"], none⟩
#guard resolvesTo (resolveUrl origin "wagahai/index.html" "wagahai.css") ⟨["wagahai/wagahai.css"], none⟩
#guard resolvesTo (resolveUrl origin "index.html" "/a/b") ⟨["a/b/index.html", "a/b.html"], none⟩
#guard resolvesTo (resolveUrl origin "index.html" "/feed.xml") ⟨["feed.xml"], none⟩
#guard resolvesTo (resolveUrl origin "about/index.html" "#team") ⟨["about/index.html"], some "team"⟩
#guard resolvesTo (resolveUrl origin "index.html" "/about/#team") ⟨["about/index.html"], some "team"⟩
#guard resolvesTo (resolveUrl origin "index.html" "/about/?q=1#te%61m") ⟨["about/index.html"], some "team"⟩
#guard resolvesTo (resolveUrl origin "index.html" "https://x.test/about/") ⟨["about/index.html"], none⟩
#guard isExternal (resolveUrl origin "index.html" "https://other.test/")
#guard isExternal (resolveUrl origin "index.html" "https://x.test.evil/")          -- origin is not a prefix match
#guard resolvesTo (resolveUrl origin "about/index.html" "https://x.test#home") ⟨["index.html"], some "home"⟩
#guard resolvesTo (resolveUrl origin "index.html" "/%61bout/") ⟨["about/index.html"], none⟩   -- unreserved escape
#guard resolvesTo (resolveUrl origin "index.html" "/a%2Fb/") ⟨["a%2Fb/index.html"], none⟩   -- %2F is not a separator
#guard isExternal (resolveUrl origin "index.html" "//cdn.test/x.js")
#guard isExternal (resolveUrl origin "index.html" "mailto:a@b.test")
#guard isMalformed (resolveUrl origin "index.html" "/../x/")
#guard isMalformed (resolveUrl origin "index.html" "/a//b/")

-- Alternates and sitemap from the same route set.
#guard (Meta.alternatesFor origin .ja (Slug.lit "about")).map (·.url) =
  ["https://x.test/about/", "https://x.test/en/about/", "https://x.test/about/"]
#guard (Meta.sitemapOf origin .ja [rIndexJa, rIndexEn]).entries.map (·.loc) =
  ["https://x.test/", "https://x.test/en/"]

end Routes

/-! ## Asset paths -/

section AssetPaths

def twoAssets : Assets 2 where
  name := fun i => if i.val = 0 then AssetPath.lit "assets/a.css" else AssetPath.lit "assets/b.js"
  kind := fun i => if i.val = 0 then .css else .js
  bytes := fun _ => ByteArray.empty
  unique := by decide

#guard (twoAssets.path 0).toString = "assets/a.css"
#guard (twoAssets.path 1).toString = "assets/b.js"

end AssetPaths

/-! ## Responsive Image Tests -/

section ResponsiveImages

-- Epsilon calculation
def testSlot : SlotResp := { Lmin := 320, Lmax := 1920, dmax := 3, epsNum := 1, epsDen := 4 }

#guard epsilon testSlot = (1 : Rat) / 4

-- Widths generation (should produce non-empty list for valid slot)
#guard (widths testSlot).length > 0

-- Widths should be sorted ascending
def isSorted (xs : List Nat) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)

#guard isSorted (widths testSlot)

-- Invalid slot (Lmin = 0) should produce empty list
#guard widths { Lmin := 0, Lmax := 1920, dmax := 3, epsNum := 1, epsDen := 4 } = []

-- Invalid slot (dmax = 0) should produce empty list
#guard widths { Lmin := 320, Lmax := 1920, dmax := 0, epsNum := 1, epsDen := 4 } = []

-- Select function
#guard select [100, 200, 300, 400] 150 = some 200
#guard select [100, 200, 300, 400] 100 = some 100
#guard select [100, 200, 300, 400] 500 = none
#guard select [] 100 = none

-- Select from generated widths
#guard (select (widths testSlot) 320).isSome

end ResponsiveImages

/-! ## NonEmptyStr Tests -/

section NonEmptyStr

-- Valid NonEmptyStr construction
def validStr : NonEmptyStr := ⟨"hello", by decide⟩
#guard validStr.s = "hello"

-- Single character is valid
def singleChar : NonEmptyStr := ⟨"x", by decide⟩
#guard singleChar.s = "x"

end NonEmptyStr

/-! ## Date arithmetic — Gregorian boundary tests

The leap-day regression these guard against: `daysBeforeYear` used to
credit the current year's leap day on January 1st, so 2023-12-31 →
2024-01-01 measured two days. Every boundary the calendar has is pinned
here: plain year, leap year, century non-leap, 400-year leap. -/

section DateArithmetic

open NoGoals.Verify (IsoDate Attestation)
open NoGoals.Verify.IsoDate (daysBetween lit ofString?)

-- Adjacent days across year boundaries are exactly one day apart.
#guard daysBetween (lit "2023-12-31") (lit "2024-01-01") = 1  -- into a leap year
#guard daysBetween (lit "2024-12-31") (lit "2025-01-01") = 1  -- out of a leap year
#guard daysBetween (lit "2024-02-28") (lit "2024-02-29") = 1  -- leap day exists
#guard daysBetween (lit "2024-02-29") (lit "2024-03-01") = 1
#guard daysBetween (lit "2023-02-28") (lit "2023-03-01") = 1  -- no leap day
-- Century rules: 1900 not leap, 2000 leap.
#guard daysBetween (lit "1899-12-31") (lit "1900-01-01") = 1
#guard daysBetween (lit "1900-02-28") (lit "1900-03-01") = 1
#guard daysBetween (lit "2000-02-28") (lit "2000-03-01") = 2
-- Whole-year spans.
#guard daysBetween (lit "2023-01-01") (lit "2024-01-01") = 365
#guard daysBetween (lit "2024-01-01") (lit "2025-01-01") = 366
#guard daysBetween (lit "1900-01-01") (lit "1901-01-01") = 365
#guard daysBetween (lit "2000-01-01") (lit "2001-01-01") = 366

-- Canonical field widths: the YYYY-MM-DD contract rejects noncanonical
-- shapes instead of silently reinterpreting them.
#guard (ofString? "1-2-3").isNone
#guard (ofString? "2026-8-07").isNone
#guard (ofString? "2026-08-7").isNone
#guard (ofString? "02026-08-07").isNone
#guard (ofString? "2026-08-07").isSome
#guard (ofString? "2026-13-01").isNone
#guard (ofString? "2026-02-30").isNone

-- Freshness is order-aware: a future-dated attestation is never fresh.
def attAt (d : IsoDate) : Attestation :=
  { verifiedBy := "test", verifiedAt := d, method := .human }
#guard Attestation.isFresh (lit "2026-08-07") 365 (attAt (lit "2026-08-07")) = true
#guard Attestation.isFresh (lit "2026-08-07") 365 (attAt (lit "2025-08-08")) = true
#guard Attestation.isFresh (lit "2026-08-07") 365 (attAt (lit "2025-08-06")) = false  -- too old
#guard Attestation.isFresh (lit "2026-08-07") 365 (attAt (lit "2026-08-08")) = false  -- future
#guard Attestation.isFresh (lit "2026-08-07") 365 (attAt (lit "2026-12-31")) = false  -- future

end DateArithmetic

/-! ## Test Summary -/

-- If this file compiles, all #guard assertions passed
#check "All NoGoals unit tests passed!"

end NoGoals.Test
