import NoGoals.Compile
import NoGoals.Render.Feed
import Site.Blocks
import Site.Config

namespace MySite.Render

open NoGoals (Route Lang)
open NoGoals.DSL
open NoGoals.Render.Tree (Html)

def slug : PageId → NoGoals.Slug
  | .index => NoGoals.Slug.index
  | .about => NoGoals.Slug.lit "about"

/-- Root-relative href of a page — THE path function, so it cannot disagree
    with the emitted file. -/
def hrefP (lang : Lang) (id : PageId) : String :=
  (Route.mk (slug id) lang).href config.defaultLang

def txt (lang : Lang) (l : L) : Html := .text (l.get lang)

/-- Blocks → typed trees. Text and attribute values are escaped by the tree
    renderer; attribute NAMES must be `[a-z0-9-]`. Total: structural
    recursion through `section` via `attach`. -/
def renderBlock (lang : Lang) : Block → List Html
  | .heading t => [.el "h2" [("class", "section-heading")] [txt lang t]]
  | .prose ps => [.el "div" [("class", "prose")] (ps.map fun p => .el "p" [] [txt lang p])]
  | .cta target label =>
      [.el "p" [("class", "cta-row")] [.el "a" [("href", hrefP lang target), ("class", "button")] [txt lang label]]]
  | .section id? children =>
      let idAttr := match id? with | some i => [("id", i.s)] | none => []
      [.el "section" (idAttr ++ [("class", "section")])
        (children.attach.flatMap fun ⟨c, _⟩ => renderBlock lang c)]

def renderBody (lang : Lang) (blocks : List Block) : List Html :=
  blocks.flatMap (renderBlock lang)

/-- The chrome slots NoGoals leaves to the site. Trees, never strings. -/
def siteChrome (lang : Lang) : NoGoals.Compile.SiteChrome :=
  { footerNav := [.el "nav" [("class", "footer-nav")] [
      .el "a" [("href", hrefP lang .about)] [txt lang ⟨"私たちについて", "About"⟩]]] }

end MySite.Render
