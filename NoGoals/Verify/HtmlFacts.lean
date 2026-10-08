/-
  HTML facts — what a real HTML parser saw in the emitted pages.

  NoGoals does not parse HTML. The build runs a pinned browser-grade parser
  (parse5, via `tools/html-facts.mjs`) over every emitted `.html` file
  and writes one JSON document of FACTS: for each file, its elements in
  document order (lower-cased tag, entity-decoded attributes, whether the
  element has direct non-blank text), the `id` values it declares, its
  visible text (script/style excluded) and its human-facing attribute text.
  Raw-text and RCDATA contexts are the parser's business: a `<span id=…>`
  inside a `<textarea>` declares nothing, exactly as in a browser.

  This module decodes that document STRICTLY. A missing field, a wrong
  type, an unknown key, or a duplicated file path is a parse error, and a
  parse error fails every gate that depends on the facts. The substring
  extractors this replaces (`splitOn "href=\""` and friends) could not see
  quoting, case, comments or entities; a fact here means the parser saw it.
-/

import Lean.Data.Json
import NoGoals.IR.Route
import NoGoals.Verify.Json

namespace NoGoals.Verify.HtmlFacts

open Lean (Json)

structure Element where
  tag : String
  attrs : List (String × String)
  /-- The element has direct, non-blank text content (inline `<script>`/`<style>`). -/
  hasText : Bool
deriving Repr, Inhabited

def Element.attr (e : Element) (name : String) : Option String :=
  (e.attrs.find? (·.1 == name)).map (·.2)

structure FileFacts where
  path : String
  elements : List Element
  ids : List String
  text : String
  attrText : List String
deriving Repr, Inhabited

abbrev Facts := List FileFacts

/-! ## Strict decoding -/

open NoGoals.Verify.Json (parse getStr getBool getArr getStrList expectKeys)
open NoGoals (dupes)

private def parseAttrs (j : Json) (ctx : String) : Except String (List (String × String)) :=
  match j with
  | .obj kvs => kvs.toArray.toList.mapM fun (k, v) => match v with
      | .str s => pure (k, s)
      | _ => throw s!"{ctx}: attribute `{k}` must be a string"
  | _ => throw s!"{ctx}: `attrs` must be an object"

private def parseElement (ctx : String) (j : Json) : Except String Element := do
  expectKeys j ["tag", "attrs", "hasText"] ctx
  let tag ← getStr j "tag" ctx
  let attrs ← match j.getObjVal? "attrs" with
    | .ok a => parseAttrs a ctx
    | .error e => throw s!"{ctx}: {e}"
  let hasText ← getBool j "hasText" ctx
  pure { tag, attrs, hasText }

private def parseFile (j : Json) : Except String FileFacts := do
  let path ← getStr j "path" "file"
  let ctx := s!"file {path}"
  expectKeys j ["path", "elements", "ids", "text", "attrText"] ctx
  let elems ← getArr j "elements" ctx
  let elements ← elems.zipIdx.mapM fun (e, i) => parseElement s!"{ctx} element {i}" e
  let ids ← getStrList j "ids" ctx
  let text ← getStr j "text" ctx
  let attrText ← getStrList j "attrText" ctx
  pure { path, elements, ids, text, attrText }

/-- Decode a facts document. Every file that the caller expected must be
    present exactly once; the facts for a file the caller did not ask about
    are an error too (the producer and the consumer must agree on the set). -/
def parseFacts (expectedFiles : List String) (stdout : String) : Except String Facts := do
  let j ← parse "facts" stdout
  expectKeys j ["files"] "facts"
  let files ← getArr j "files" "facts"
  let facts ← files.mapM parseFile
  let paths := facts.map (·.path)
  match dupes paths with
  | p :: _ => throw s!"facts: file `{p}` reported more than once"
  | [] => pure ()
  for p in paths do
    unless expectedFiles.contains p do throw s!"facts: unexpected file `{p}`"
  for p in expectedFiles do
    unless paths.contains p do throw s!"facts: no facts for `{p}`"
  pure facts

end NoGoals.Verify.HtmlFacts
