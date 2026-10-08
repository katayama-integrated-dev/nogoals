import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlVerified
import NoGoals.Render.Escape
import NoGoals.Render.Tree
import NoGoals.Meta

namespace NoGoals

/- Escaping (`htmlEscape` + theorems) lives in `NoGoals.Render.Escape`; the typed
   HTML tree and its well-formedness grammar in `NoGoals.Render.Tree`. This module
   maps the verified IR onto trees and renders them — `Tree.render` is the
   only string emitter on this path. -/

open Render.Tree (Html)

/-- Render heading level to HTML tag -/
def hLevelToTag : HLevel → String
| .h1 => "h1"
| .h2 => "h2"
| .h3 => "h3"
| .h4 => "h4"
| .h5 => "h5"
| .h6 => "h6"

/-- Render display size to class attribute -/
def displayToClass : Display → String
| .xs => "text-xs"
| .sm => "text-sm"
| .md => "text-md"
| .lg => "text-lg"
| .xl => "text-xl"

/-- Render a URL to string -/
def urlToString : Url.Safe → String
| .https host path => s!"https://{host}{path.toString}"
| .http host path => s!"http://{host}{path.toString}"
| .data mediatype bytes => s!"data:{mediatype};base64,{bytes}"

variable {nP nA : Nat} {A : Assets nA}

/-- The href the kernel emits for an internal link: the target route's
    root-relative href, plus `#anchor` when the link names one. -/
def linkHref (S : SiteV nP nA A) (p : Fin nP)
    (anchor? : Option { a : AnchorId // a ∈ S.anchorsOf p }) : String :=
  match anchor? with
  | none => S.hrefOf p
  | some a => S.hrefOf p ++ "#" ++ a.1.s

/-- The `id` attribute a heading carries: exactly the anchor refinement
    recorded for its text, or nothing. -/
def headingIdAttr (txt : NonEmptyStr) : List (String × String) :=
  match anchorOf txt.s with
  | some a => [("id", a.s)]
  | none => []

/-- The typed tree of one inline node. Every constructor lands in
    `Html.text`/`Html.el` — never `Html.raw` — which is what makes
    `renderInline_wf` a theorem rather than an inspection. -/
def inlineToHtml (S : SiteV nP nA A) : InlineV nP nA A S.anchorsOf → Html
| .text s => .text s
| .code s => .el "code" [] [.text s]
| .link p anchor? label => .el "a" [("href", linkHref S p anchor?)] [.text label.s]
| .extlink url label =>
    .el "a" [("href", urlToString url), ("rel", "noopener noreferrer")] [.text label.s]

/-- The typed tree of one block (total — structural recursion via `attach`). -/
def blockToHtml (S : SiteV nP nA A) : BlockV nP nA A S.anchorsOf → Html
| .p xs => .el "p" [] (xs.map (inlineToHtml S))
| .ul items => .el "ul" [] (items.map (fun xs => .el "li" [] (xs.map (inlineToHtml S))))
| .heading lvl display txt =>
    .el (hLevelToTag lvl) (("class", displayToClass display) :: headingIdAttr txt) [.text txt.s]
| .img src alt =>
    .void "img" [("src", "/" ++ (A.path src.val).toString), ("alt", alt.s), ("loading", "lazy")]
| .section title? children =>
    let heading := match title? with
      | none => []
      | some t => [Html.el "h2" [] [.text t.s]]
    .el "section" [] (heading ++ children.map (blockToHtml S))

/-- Render inline content to HTML — through the typed tree. -/
def renderInline (S : SiteV nP nA A) (i : InlineV nP nA A S.anchorsOf) : String :=
  Render.Tree.render (inlineToHtml S i)

/-- Render block content to HTML — through the typed tree. -/
def renderBlock (S : SiteV nP nA A) (b : BlockV nP nA A S.anchorsOf) : String :=
  Render.Tree.render (blockToHtml S b)

/-! ### Well-formedness: the kernel renderer cannot emit unbalanced markup -/

theorem allWellFormed_append (a b : List Html) :
    Render.Tree.allWellFormed (a ++ b) =
      (Render.Tree.allWellFormed a && Render.Tree.allWellFormed b) := by
  induction a with
  | nil => simp [Render.Tree.allWellFormed]
  | cons c rest ih => simp [Render.Tree.allWellFormed, ih, Bool.and_assoc]

theorem inlineToHtml_wf (S : SiteV nP nA A)
    (i : InlineV nP nA A S.anchorsOf) : Render.Tree.wellFormed (inlineToHtml S i) = true := by
  cases i <;> simp only [inlineToHtml, Render.Tree.wellFormed, Render.Tree.allWellFormed,
    List.all_cons, List.all_nil, Bool.and_true] <;> decide

theorem allWellFormed_map_inline (S : SiteV nP nA A)
    (xs : List (InlineV nP nA A S.anchorsOf)) :
    Render.Tree.allWellFormed (xs.map (inlineToHtml S)) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [Render.Tree.allWellFormed, inlineToHtml_wf S x, ih]

theorem headingIdAttr_clean (txt : NonEmptyStr) :
    (headingIdAttr txt).all (fun a => Render.Tree.cleanToken a.1) = true := by
  rcases h : anchorOf txt.s with _ | a <;>
    simp only [headingIdAttr, h, List.all_cons, List.all_nil, Bool.and_true] <;> decide

theorem blockToHtml_wf (S : SiteV nP nA A) :
    (b : BlockV nP nA A S.anchorsOf) → Render.Tree.wellFormed (blockToHtml S b) = true
| .p xs => by
    simp [blockToHtml, Render.Tree.wellFormed, allWellFormed_map_inline S xs]
    decide
| .ul items => by
    simp only [blockToHtml, Render.Tree.wellFormed]
    have hli : Render.Tree.allWellFormed
        (items.map (fun xs => Html.el "li" [] (xs.map (inlineToHtml S)))) = true := by
      induction items with
      | nil => rfl
      | cons xs rest ih =>
        simp [Render.Tree.allWellFormed, Render.Tree.wellFormed,
          allWellFormed_map_inline S xs, ih]
        decide
    simp [hli]
    decide
| .heading lvl display txt => by
    have hid := headingIdAttr_clean txt
    cases lvl <;> (simp [blockToHtml, Render.Tree.wellFormed, hLevelToTag,
      Render.Tree.allWellFormed, hid]; decide)
| .img src alt => by
    simp [blockToHtml, Render.Tree.wellFormed]
    decide
| .section title? children => by
    have hkids : Render.Tree.allWellFormed (children.map (blockToHtml S)) = true := by
      rw [Render.Tree.allWellFormed_iff]
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact blockToHtml_wf S c'
    cases title? with
    | none =>
      simp [blockToHtml, Render.Tree.wellFormed, hkids]
      decide
    | some t =>
      simp [blockToHtml, Render.Tree.wellFormed, Render.Tree.allWellFormed, hkids]
      decide
  termination_by b => sizeOf b
  decreasing_by
    have := List.sizeOf_lt_of_mem hc'
    simp only [BlockV.section.sizeOf_spec]
    omega

/-- **Kernel output is well-formed markup**: whatever the IR contains, the
    rendered string of any block is a single properly-nested node — tags
    balance and text/attribute content cannot escape its context. Runtime
    HTML validation still runs on the shipped pages (the shell's slots are
    trusted, not proved), but for the kernel path this class of defect is
    now unrepresentable. -/
theorem renderBlock_wf (S : SiteV nP nA A)
    (b : BlockV nP nA A S.anchorsOf) : Render.Tree.NodeStr (renderBlock S b) :=
  Render.Tree.render_wf _ (blockToHtml_wf S b)

theorem renderInline_wf (S : SiteV nP nA A)
    (i : InlineV nP nA A S.anchorsOf) : Render.Tree.NodeStr (renderInline S i) :=
  Render.Tree.render_wf _ (inlineToHtml_wf S i)

/-! ### Declared anchors are emitted ids

`anchors_sound` says every anchor in a page's schema is a heading id of its
body; this lemma says every heading id of a body is an `id=` attribute in
the body's rendered tree. Together: a fragment a link may name is an id the
target page declares. -/

theorem heading_ids_emitted (S : SiteV nP nA A) :
    (b : BlockV nP nA A S.anchorsOf) → ∀ a ∈ headingIds b,
      a.s ∈ Render.Tree.ids (blockToHtml S b)
| .p _ => by intro a ha; simp [headingIds] at ha
| .ul _ => by intro a ha; simp [headingIds] at ha
| .img _ _ => by intro a ha; simp [headingIds] at ha
| .heading lvl display txt => by
    intro a ha
    simp only [headingIds, Option.mem_toList] at ha
    simp [blockToHtml, Render.Tree.ids, headingIdAttr, ha, Render.Tree.idsList]
| .section title? children => by
    intro a ha
    simp only [headingIds, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
      exists_prop] at ha
    obtain ⟨c, hc, hac⟩ := ha
    have hmem : a.s ∈ Render.Tree.idsList (children.map (blockToHtml S)) :=
      Render.Tree.mem_idsList_of_mem (List.mem_map_of_mem hc) (heading_ids_emitted S c a hac)
    cases title? with
    | none => simpa [blockToHtml, Render.Tree.ids] using hmem
    | some t =>
      simp only [blockToHtml, Render.Tree.ids, List.filterMap_nil, List.nil_append,
        Render.Tree.idsList_append]
      exact List.mem_append_right _ hmem
  termination_by b => sizeOf b
  decreasing_by
    have := List.sizeOf_lt_of_mem hc
    simp only [BlockV.section.sizeOf_spec]
    omega

theorem body_ids_emitted (S : SiteV nP nA A) (body : List (BlockV nP nA A S.anchorsOf)) :
    ∀ a ∈ bodyIds body, a.s ∈ Render.Tree.idsList (body.map (blockToHtml S)) := by
  intro a ha
  simp only [bodyIds, List.mem_flatMap] at ha
  obtain ⟨b, hb, hab⟩ := ha
  exact Render.Tree.mem_idsList_of_mem (List.mem_map_of_mem hb) (heading_ids_emitted S b a hab)

/-! ### Whole pages as trees -/

/-- `<link rel="alternate" hreflang=…>` for every alternate of the page's
    slug (root-relative), from the same `Meta.alternatesFor` the sitemap and
    the chrome use. -/
def hreflangLinks (S : SiteV nP nA A) (i : Fin nP) : List Html :=
  (Meta.alternatesFor "" S.defaultLang (S.slugOf i)).map fun alt =>
    .void "link" [("rel", "alternate"), ("hreflang", alt.tag.code), ("href", alt.url)]

/-- The whole page as one typed tree: head with the page's title and its
    hreflang alternates, body from the verified blocks. -/
def pageTree (S : SiteV nP nA A) (i : Fin nP) : Html :=
  let page := S.pages i
  .el "html" [("lang", (S.langOf i).code)] [
    .el "head" [] ([
      .void "meta" [("charset", "utf-8")],
      .void "meta" [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      .el "title" [] [.text page.title]] ++ hreflangLinks S i),
    .el "body" [] (page.body.map (blockToHtml S))]

/-- Render a page to a full HTML document. -/
def renderPageHtml (S : SiteV nP nA A) (i : Fin nP) : String :=
  "<!DOCTYPE html>\n" ++ Render.Tree.render (pageTree S i)

theorem hreflangLinks_wf (S : SiteV nP nA A) (i : Fin nP) :
    Render.Tree.allWellFormed (hreflangLinks S i) = true := by
  rw [Render.Tree.allWellFormed_iff]
  intro c hc
  simp only [hreflangLinks, List.mem_map] at hc
  obtain ⟨alt, _, rfl⟩ := hc
  simp only [Render.Tree.wellFormed, List.all_cons, List.all_nil, Bool.and_true]
  decide

/-- The kernel page tree is raw-free and well-formed, for every site and page. -/
theorem pageTree_wf (S : SiteV nP nA A) (i : Fin nP) :
    Render.Tree.wellFormed (pageTree S i) = true := by
  have hbody : Render.Tree.allWellFormed ((S.pages i).body.map (blockToHtml S)) = true := by
    rw [Render.Tree.allWellFormed_iff]
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨b, _, rfl⟩ := hc
    exact blockToHtml_wf S b
  simp only [pageTree, Render.Tree.wellFormed, Render.Tree.allWellFormed, allWellFormed_append,
    hbody, hreflangLinks_wf, List.all_cons, List.all_nil, Bool.and_true]
  decide

/-- **Kernel pages are well-formed documents** (fragment grammar): the
    rendered page is a single properly nested node. -/
theorem renderPage_wf (S : SiteV nP nA A) (i : Fin nP) :
    Render.Tree.NodeStr (Render.Tree.render (pageTree S i)) :=
  Render.Tree.render_wf _ (pageTree_wf S i)

end NoGoals
