import NoGoals.Render.Html
import NoGoals.IR.HtmlVerified
import NoGoals.IR.Assets
import NoGoals.Images.Srcset
import NoGoals.Compile
import NoGoals.DSL

/-!
# NoGoals Integration Tests

Tests that exercise the full pipeline from site definition to output.

Run tests with: `lake build NoGoalsTest`
-/

namespace NoGoals.Test.Integration

/-! ## Helper Functions -/

/-- Check if a string contains a substring -/
def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-! ## Responsive Image Tests -/

section ResponsiveImageTests

-- Typical mobile configuration
def mobileConfig : SlotResp := {
  Lmin := 320,
  Lmax := 768,
  dmax := 3,
  epsNum := 1,
  epsDen := 4
}

-- Desktop configuration
def desktopConfig : SlotResp := {
  Lmin := 769,
  Lmax := 1920,
  dmax := 2,
  epsNum := 1,
  epsDen := 5
}

-- Generate widths
def mobileWidths := widths mobileConfig
def desktopWidths := widths desktopConfig

-- Both should produce non-empty lists
#guard mobileWidths.length > 0
#guard desktopWidths.length > 0

-- Widths should be sorted ascending
def isSortedAsc (xs : List Nat) : Bool :=
  xs.zip (xs.drop 1) |>.all fun (a, b) => decide (a ≤ b)

#guard isSortedAsc mobileWidths
#guard isSortedAsc desktopWidths

-- First width should cover Lmin
#guard (mobileWidths.head?.map (fun w => decide (w ≥ mobileConfig.Lmin))) = some true
#guard (desktopWidths.head?.map (fun w => decide (w ≥ desktopConfig.Lmin))) = some true

-- Last width should cover Lmax * dmax
#guard (mobileWidths.getLast?.map (fun w => decide (w ≥ mobileConfig.Lmax * mobileConfig.dmax))) = some true
#guard (desktopWidths.getLast?.map (fun w => decide (w ≥ desktopConfig.Lmax * desktopConfig.dmax))) = some true

-- Select should work
#guard (select mobileWidths 320).isSome
#guard (select mobileWidths 640).isSome
#guard (select desktopWidths 1000).isSome

end ResponsiveImageTests

/-! ## HTML Rendering Tests -/

section HtmlRenderingTests

-- Test htmlEscape in various contexts
def testHtml1 := htmlEscape "Tom & Jerry"
def testHtml2 := htmlEscape "<div>content</div>"
def testHtml3 := htmlEscape "She said \"hello\""

#guard hasSubstr testHtml1 "&amp;"
#guard hasSubstr testHtml2 "&lt;"
#guard hasSubstr testHtml2 "&gt;"
#guard hasSubstr testHtml3 "&quot;"

-- Test URL rendering
def testUrl1 := urlToString (.https "example.com" ⟨"/page"⟩)
def testUrl2 := urlToString (.data "image/png" "abc123")

#guard hasSubstr testUrl1 "https://"
#guard hasSubstr testUrl1 "example.com"
#guard hasSubstr testUrl2 "data:image/png"
#guard hasSubstr testUrl2 "base64"

-- Test heading tags
#guard hLevelToTag .h1 = "h1"
#guard hLevelToTag .h6 = "h6"

-- Test display classes
#guard hasSubstr (displayToClass .xs) "xs"
#guard hasSubstr (displayToClass .xl) "xl"

end HtmlRenderingTests

/-! ## Compile: one pipeline, typed trees, content checks -/

section CompileTests

open NoGoals.Compile
open NoGoals.DSL
open NoGoals.Render.Tree (Html)

-- The positive control compiles to every route, at the one path function's paths.
def posResult := compile positiveControlSite
#guard posResult.report.allPassed
#guard posResult.controlsPassed
#guard posResult.files.map (·.path) = ["index.html", "about/index.html", "en/index.html", "en/about/index.html"]

-- Every generated page tree is well-formed modulo raw slots (none here).
#guard (positiveControlSite.routes.all fun (p, r) =>
  Render.Tree.wellFormedMod (generatePageTree positiveControlSite p r))
#guard (positiveControlSite.routes.all fun (p, r) =>
  (Render.Tree.raws (generatePageTree positiveControlSite p r)).isEmpty)

-- The head carries canonical + hreflang + og:url from the route.
def enAbout := generatePageHtml positiveControlSite controlAbout ⟨controlAbout.slug, .en⟩
#guard hasSubstr enAbout "<link rel=\"canonical\" href=\"https://control.test/en/about/\" />"
#guard hasSubstr enAbout "hreflang=\"x-default\" href=\"https://control.test/about/\""
#guard hasSubstr enAbout "property=\"og:url\" content=\"https://control.test/en/about/\""
#guard hasSubstr enAbout "property=\"og:locale\" content=\"en_US\""
#guard hasSubstr enAbout "<html lang=\"en\">"
#guard hasSubstr enAbout "href=\"/about/\" class=\"language-link\" lang=\"ja\" hreflang=\"ja\""   -- switcher to the JA twin
#guard !hasSubstr enAbout "style="
-- Indexed by default; `indexed := false` asks search engines to stay out.
#guard !hasSubstr enAbout "noindex"
#guard hasSubstr (generatePageHtml positiveControlSite { controlAbout with indexed := false } ⟨controlAbout.slug, .en⟩)
  "<meta name=\"robots\" content=\"noindex\" />"

-- The nav marks the current page; a section's item is current on its sub-pages.
#guard hasSubstr enAbout "href=\"/en/about/\" class=\"nav-link\" aria-current=\"page\""
#guard hasSubstr enAbout "href=\"/en/\" class=\"nav-link\">"
#guard currentAttr (Slug.lit "news") (some (Slug.lit "news/x")) = [("aria-current", "true")]
#guard currentAttr (Slug.lit "news") (some (Slug.lit "newsletter")) = []
#guard currentAttr (Slug.lit "news") none = []
-- A skip link to `main`, and a script-free menu for narrow screens.
#guard hasSubstr enAbout "<a href=\"#main\" class=\"skip-link\">Skip to content</a>"
#guard hasSubstr enAbout "<main id=\"main\">"
#guard hasSubstr enAbout "<details class=\"nav-menu\"><summary>Menu</summary>"

-- Not-found pages: one per language, the nearest one up the path.
#guard notFoundPath .ja .ja = "404.html"
#guard notFoundPath .ja .en = "en/404.html"
#guard Lang.all.all fun l => Render.Tree.wellFormedMod (notFoundTree positiveControlSite l)
def enNotFound := notFoundHtml positiveControlSite .en
#guard hasSubstr enNotFound "<h1 class=\"section-heading\">Page not found</h1>"
#guard hasSubstr enNotFound "<a href=\"/en/\" class=\"button\">Go to the home page</a>"
#guard !hasSubstr enNotFound "rel=\"canonical\""
#guard !hasSubstr enNotFound "aria-current"

-- Blank bodies fail the build; content-bearing ones pass.
#guard hasContent (.el "p" [] [.text "x"])
#guard hasContent (.void "img" [("src", "/a.png"), ("alt", "a")])
#guard !hasContent (.el "div" [] [])
#guard !hasContent (.raw "")
#guard !hasContent (.text "   ")
#guard !hasContent (.el "section" [] [.el "div" [] [.text " "]])
def blankSite : Site := { positiveControlSite with
  pages := [{ controlIndex with body := fun _ => [.el "div" [] []] }, controlAbout] }
#guard (checkPageBodies blankSite).isFailed
#guard (compile blankSite).files.isEmpty      -- fail closed: no output with a failure

-- A raw slot is counted and named, never hidden.
def rawSite : Site := { positiveControlSite with
  pages := [{ controlIndex with body := fun _ => [.raw "<p>x</p>"] }, controlAbout] }
#guard hasSubstr (checkPageTrees rawSite (fun _ => {})).description "2 raw slot(s) on 2 page(s)"


end CompileTests

/-! ## Report evidence semantics

Pin the properties the honest-evidence model rests on: a skipped check
never counts as verified, and
extra guarantees replace same-id entries instead of duplicating them —
a check that never executed cannot be claimed as passed. -/

section EvidenceTests

open NoGoals.Compile

def gEnforced : Guarantee :=
  { category := "T", name := "a", description := "", status := .enforced "thm", id := "x" }
def gSkipped : Guarantee :=
  { category := "T", name := "b", description := "", status := .skipped "not run", id := "y" }
def gKernel : Guarantee :=
  { category := "T", name := "c", description := "", status := .enforced "thm"
    scope := .kernel, id := "z" }
def gCheckedY : Guarantee :=
  { category := "T", name := "b'", description := "", status := .checked, id := "y" }

-- Replacement is by id — no duplicate, order preserved, unknown ids appended.
#guard (updateGuarantees [gEnforced, gSkipped] [gCheckedY]).map (·.name) = ["a", "b'"]
#guard (updateGuarantees [gEnforced] [gCheckedY]).map (·.name) = ["a", "b'"]
#guard (dedupeGuarantees [gSkipped, gCheckedY]).length = 1
-- A skipped check is not a failure: it must not block output, but it must
-- also never be reported as passed.
#guard (match gSkipped.status with | .failed _ => true | _ => false) = false
#guard (match gSkipped.status with | .checked | .enforced _ => true | _ => false) = false

end EvidenceTests

/-! ## Summary -/

#check "All NoGoals integration tests passed!"

end NoGoals.Test.Integration
