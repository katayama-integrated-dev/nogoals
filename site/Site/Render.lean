import NoGoals.Compile
import Site.Blocks
import Site.Config

namespace NoGoalsSite.Render

open NoGoals (Route Lang)
open NoGoals.DSL
open NoGoals.Render.Tree (Html)

def slug : PageId → NoGoals.Slug
  | .index => NoGoals.Slug.index
  | .guarantees => NoGoals.Slug.lit "guarantees"
  | .start => NoGoals.Slug.lit "start"

/-- Root-relative href of a page — THE path function, so it cannot disagree
    with the emitted file. -/
def hrefP (lang : Lang) (id : PageId) : String :=
  (Route.mk (slug id) lang).href config.defaultLang

def txt (lang : Lang) (l : L) : Html := .text (l.get lang)

def Tone.cls : Tone → String
  | .plain => "tone-plain"
  | .comment => "tone-comment"
  | .good => "tone-good"
  | .bad => "tone-bad"

def codeTree (lang : Lang) (c : Code) : Html :=
  .el "figure" [("class", "code")] [
    .el "figcaption" [("class", "code-caption")] [txt lang c.caption],
    -- Long lines scroll inside the block: focusable and named, so a keyboard
    -- can scroll it; code and its comments are English on both pages.
    .el "pre" [("class", "code-pre"), ("lang", "en"), ("tabindex", "0"), ("role", "region"),
               ("aria-label", c.caption.get lang)] [
      .el "code" [] (c.lines.flatMap fun l =>
        [.el "span" [("class", Tone.cls l.tone)] [.text l.text], .text "\n"])]]

def entryTree (e : Entry) : Html :=
  .el "li" [("class", "entry")] [
    .el "div" [("class", "entry-head")] [
      .el "h3" [("class", "entry-name")] [.text e.name],
      .el "span" [("class", "chip")] [.text e.scope.render]],
    .el "p" [("class", "entry-desc")] [.text e.description],
    .el "p" [("class", "entry-mechanism")] [.el "code" [] [.text e.mechanism]]]

def stepTree (lang : Lang) (s : Step) : Html :=
  .el "li" [("class", "step")] (
    [.el "h3" [("class", "step-title")] [txt lang s.title],
     .el "p" [("class", "step-text")] [txt lang s.text]] ++
    s.code.toList.map (codeTree lang))

/-- Blocks → typed trees. Text and attribute values are escaped by the tree
    renderer. Total: recursion through `section` via `attach`. -/
def renderBlock (lang : Lang) : Block → List Html
  | .section id? heading children =>
      let idAttr := match id? with | some i => [("id", i.s)] | none => []
      [.el "section" (idAttr ++ [("class", "section")]) [
        .el "div" [("class", "container-wide")] (
          [.el "h2" [("class", "section-heading")] [txt lang heading]] ++
          children.attach.flatMap fun ⟨c, _⟩ => renderBlock lang c)]]
  | .prose ps => [.el "div" [("class", "prose")] (ps.map fun p => .el "p" [] [txt lang p])]
  | .code c => [codeTree lang c]
  | .compare l r => [.el "div" [("class", "compare")] [codeTree lang l, codeTree lang r]]
  | .cards items =>
      [.el "ul" [("class", "cards")] (items.map fun c =>
        .el "li" [("class", "card")] [
          .el "h3" [("class", "card-title")] [txt lang c.title],
          .el "p" [("class", "card-text")] [txt lang c.text]])]
  | .facts items source =>
      [.el "dl" [("class", "facts")] (items.map fun f =>
        .el "div" [("class", "fact")] [
          .el "dt" [("class", "fact-label")] [txt lang f.label],
          .el "dd" [("class", "fact-value")] [.text f.value]]),
       .el "p" [("class", "facts-source")] [txt lang source]]
  -- NoGoals states these in English; say so, so the Japanese page reads them right.
  | .entries items => [.el "ul" [("class", "entries"), ("lang", "en")] (items.map entryTree)]
  | .steps items => [.el "ol" [("class", "steps")] (items.map (stepTree lang))]
  | .verificationLink note =>
      [.el "p" [("class", "link-item")] [
        .el "a" [("href", (NoGoals.Compile.reportRoute lang).href config.defaultLang), ("class", "link-label")]
          [txt lang ⟨"このビルドの検証ページ", "This build's verification page"⟩],
        .el "span" [("class", "link-note")] [txt lang note]]]
  | .cta target label =>
      [.el "p" [("class", "cta-row")] [
        .el "a" [("href", hrefP lang target), ("class", "button")] [txt lang label]]]

def renderBody (lang : Lang) (blocks : List Block) : List Html :=
  blocks.flatMap (renderBlock lang)

end NoGoalsSite.Render
