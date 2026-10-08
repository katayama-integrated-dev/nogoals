import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlRaw
import NoGoals.IR.HtmlVerified
import Mathlib.Data.List.FinRange

/-!
# Refinement: raw → verified

`refine` turns an unverified `SiteRaw` into a `SiteV` whose proof fields
(`roundTrip₁`, `i18nComplete`, `disjointAssets`, `uniquePages`,
`anchors_sound`) are discharged from decidable checks.

**Errors are fatal, located, and complete.** Every broken link, missing
anchor and missing image on every page is reported in one pass, each with
the page's route and the block path (`[section index, child index, inline
index]`) it sits at. Nothing is ever silently dropped: if `refine` returns
`.ok`, every raw block is present in the verified site.

**Links resolve in the source page's language.** `/about` on an English
page is the English about page; the same href on a Japanese page is the
Japanese one. A bare `#team` is the current page. Every slug exists in
every language by construction (`i18nComplete`), so a same-language target
exists whenever any does.
-/

namespace NoGoals

inductive VError
| badLink (href : String) (didYouMean : List String)
| badAnchor (href : String) (anchor : String) (available : List AnchorId)
| badAnchorSyntax (href : String) (anchor : String)
| missingImage (p : String)
| duplicateAnchor (page : Route) (a : AnchorId)
| pathCollision (a b : Route) (path : String)
| assetCollision (page : Route) (path : String)
| roundTripFailed (page : Route)
| i18nMissing (slug : Slug) (lang : Lang)
| pageCount (expected actual : Nat)
/-- Error wrapped with its location: page route and block path. -/
| located (page : Route) (blockPath : List Nat) (e : VError)
deriving Repr, Inhabited

/-- Human-readable rendering (the publisher reads these). -/
def VError.render : VError → String
  | .badLink href [] => s!"broken internal link '{href}' (no similar slug exists)"
  | .badLink href sugg => s!"broken internal link '{href}' — did you mean {String.intercalate ", " (sugg.map (s!"'{·}'"))}?"
  | .badAnchor href a avail =>
      s!"link '{href}': anchor '#{a}' does not exist on the target page (available: {String.intercalate ", " (avail.map (·.s))})"
  | .badAnchorSyntax href a => s!"link '{href}': '#{a}' is not a valid anchor (ids are [a-z0-9-]+)"
  | .missingImage p => s!"missing image asset: {p}"
  | .duplicateAnchor pg a => s!"page {pg}: duplicate heading anchor '{a.s}'"
  | .pathCollision a b path => s!"pages {a} and {b} both emit {path}"
  | .assetCollision pg path => s!"page {pg} emits {path}, which is also an asset"
  | .roundTripFailed pg => s!"page {pg} is declared twice"
  | .i18nMissing slug lang => s!"slug {slug} has no {lang} variant"
  | .pageCount e a => s!"expected {e} pages, got {a}"
  | .located pg path e =>
      s!"page {pg}, block {String.intercalate "." (path.map toString)}: {e.render}"

/-! ## Did-you-mean (Levenshtein over slugs) -/

private def levGo (ca : Char) : List (Char × Nat) → Nat → Nat → List Nat
  | [], _, _ => []
  | (cb, up) :: rest, diag, left =>
    let v := min (up + 1) (min (left + 1) (diag + (if ca == cb then 0 else 1)))
    v :: levGo ca rest up v

/-- Levenshtein edit distance (runtime helper for error messages; unproved). -/
def editDistance (a b : String) : Nat :=
  let bs := b.toList
  let init := List.range (bs.length + 1)
  let last := a.toList.foldl (fun prev ca =>
    let first := prev.headD 0 + 1
    first :: levGo ca (bs.zip prev.tail) (prev.headD 0) first) init
  last.getLastD 0

/-- Up to three near-miss suggestions, closest first, distance ≤ 2. -/
def suggestSlugs (valid : List String) (attempt : String) : List String :=
  let scored := valid.map (fun s => (s, editDistance attempt s))
  let close := scored.filter (·.2 ≤ 2)
  (close.toArray.qsort (fun x y => x.2 < y.2)).toList.map (·.1) |>.take 3

/-! ## Anchors (from raw headings, before refinement) -/

def collectAnchorsRaw : BlockR → List AnchorId
  | .heading h    => (anchorOf h.text.s).toList
  | .section _ cs => cs.attach.flatMap (fun ⟨c, _⟩ => collectAnchorsRaw c)
  | _             => []

/-! ## Asset lookup -/

def findAssetByPath {n : Nat} (A : Assets n) (path : String) : Option (Fin n) :=
  (List.finRange n).find? (fun i => (A.path i).toString = path)

def findImageAsset {n : Nat} (A : Assets n) (path : String) : Except VError (AssetId n .image A) := do
  match findAssetByPath A path with
  | none => throw <| VError.missingImage path
  | some i =>
      if h : A.kind i = AssetKind.image then
        pure ⟨i, h⟩
      else
        throw <| VError.missingImage s!"{path} (asset exists but is not an image)"

/-! ## Href normalization

`"/about#team"`, `"about#team"`, `"/about/"`, `"about"` name slug `about`;
`"/"` names `index`; `""` and `"#team"` name the current page. -/

inductive HrefTarget
  | samePage
  | index
  | slug (s : String)
deriving Repr, DecidableEq

def normalizeHref (href : String) : HrefTarget × Option String :=
  let parts := href.splitOn "#"
  let rawSlug := parts.headD href
  let anchor? := if parts.length > 1 then some (parts[1]!) else none
  if rawSlug.isEmpty then (.samePage, anchor?)
  else
    let s := if rawSlug.startsWith "/" then (rawSlug.drop 1).toString else rawSlug
    let s := if s.endsWith "/" then (s.dropEnd 1).toString else s
    if s.isEmpty then (.index, anchor?) else (.slug s, anchor?)

/-! ## Inline refinement -/

def refineInline {nP nA : Nat} (A : Assets nA) (src : Route)
    (indexOf : Slug → Lang → Option (Fin nP))
    (Anc : Fin nP → List AnchorId)
    (validSlugs : List String) : InlineR → Except VError (InlineV nP nA A Anc)
  | .text s => .ok <| .text s
  | .code s => .ok <| .code s
  | .a ref label => match ref with
    | .internal href =>
        let (target, anchor?) := normalizeHref href
        let slug? : Option Slug := match target with
          | .samePage => some src.slug
          | .index => some Slug.index
          | .slug s => Slug.parse? s
        match slug? with
        | none => .error <| VError.badLink href (suggestSlugs validSlugs href)
        | some slug =>
          match indexOf slug src.lang with
          | none => .error <| VError.badLink href (suggestSlugs validSlugs slug.toString)
          | some pageIdx =>
              match anchor? with
              | none => .ok <| .link pageIdx none label
              | some a =>
                  match Segment.parse? a with
                  | none => .error <| VError.badAnchorSyntax href a
                  | some seg =>
                    if h : seg ∈ Anc pageIdx then
                      .ok <| .link pageIdx (some ⟨seg, h⟩) label
                    else
                      .error <| VError.badAnchor href a (Anc pageIdx)
    | .external url =>
        .ok <| .extlink url label

/-! ## Block refinement — total, and it collects EVERY error -/

/-- Run all, keep all errors (never stop at the first). -/
def collectAll {ε α : Type} (xs : List (Except (List ε) α)) : Except (List ε) (List α) :=
  let errs := xs.flatMap (fun | .error es => es | .ok _ => [])
  if errs.isEmpty then .ok (xs.filterMap (fun | .ok a => some a | .error _ => none))
  else .error errs

def refineInlines {nP nA : Nat} (A : Assets nA) (src : Route)
    (indexOf : Slug → Lang → Option (Fin nP)) (Anc : Fin nP → List AnchorId)
    (validSlugs : List String) (path : List Nat) (xs : List InlineR) :
    Except (List VError) (List (InlineV nP nA A Anc)) :=
  collectAll (xs.zipIdx.map fun (x, k) =>
    match refineInline A src indexOf Anc validSlugs x with
    | .ok v => .ok v
    | .error e => .error [.located src (path ++ [k]) e])

def refineBlock {nP nA : Nat} (A : Assets nA) (src : Route)
    (indexOf : Slug → Lang → Option (Fin nP)) (Anc : Fin nP → List AnchorId)
    (validSlugs : List String) (path : List Nat) : BlockR → Except (List VError) (BlockV nP nA A Anc)
  | .p xs => (refineInlines A src indexOf Anc validSlugs path xs).map .p
  | .ul items =>
      (collectAll (items.zipIdx.map fun (xs, k) =>
        refineInlines A src indexOf Anc validSlugs (path ++ [k]) xs)).map .ul
  | .heading h => .ok <| .heading h.level h.display h.text
  | .img src' alt =>
      match findImageAsset A src' with
      | .ok assetId => .ok <| .img assetId alt
      | .error e => .error [.located src path e]
  | .section title? children =>
      (collectAll (children.attach.zipIdx.map fun (⟨c, _⟩, k) =>
        refineBlock A src indexOf Anc validSlugs (path ++ [k]) c)).map (.section title?)

/-! ## Site refinement -/

def refine {nP nA : Nat} (A : Assets nA) (raw : SiteRaw) :
    Except (List VError) (SiteV nP nA A) := do
  if h : raw.pages.length = nP then
    have h_n : raw.pages.length = nP := h

    let getPage (i : Fin nP) : PageRaw :=
      have : i.val < raw.pages.length := by rw [h_n]; exact i.isLt
      raw.pages[i.val]

    let indexOf : Slug → Lang → Option (Fin nP) := fun slug lang =>
      List.findIdx? (fun p => p.route = ⟨slug, lang⟩) raw.pages
        |>.bind (fun idx => if h : idx < nP then some ⟨idx, h⟩ else none)

    let anchorsOf : Fin nP → List AnchorId := fun i =>
      (getPage i).body.flatMap collectAnchorsRaw

    let validSlugs : List String := (raw.pages.map (·.route.slug.toString)).eraseDups

    -- Every located error on every page, in one pass.
    let refinePage (p : PageRaw) : List VError × List (BlockV nP nA A anchorsOf) :=
      match collectAll (p.body.zipIdx.map fun (b, k) =>
          refineBlock A p.route indexOf anchorsOf validSlugs [k] b) with
      | .ok bs => ([], bs)
      | .error es => (es, [])
    let results := raw.pages.map refinePage
    let dupAnchors : List VError := (List.finRange nP).filterMap fun i =>
      (dupes (anchorsOf i)).head?.map (VError.duplicateAnchor (getPage i).route)
    let allErrors := results.flatMap (·.1) ++ dupAnchors
    if allErrors.isEmpty then
      let bodies := results.map (·.2)
      have h_blen : bodies.length = nP := by
        simpa [bodies, results] using h_n

      let pages : Fin nP → PageV nP nA A anchorsOf := fun i => {
        route := (getPage i).route
        title := (getPage i).title
        body := bodies.get ⟨i.val, by rw [h_blen]; exact i.isLt⟩ }

      let pathOf (i : Fin nP) : Path := ⟨(pages i).route.outputPath raw.defaultLang⟩

      -- Decidable checks, converted into the SiteV proof fields below.
      let checkRoundTrip : Bool :=
        (List.finRange nP).all fun i => indexOf (pages i).route.slug (pages i).route.lang = some i
      let checkUnique : Bool :=
        (List.finRange nP).all fun i => (List.finRange nP).all fun j =>
          if pathOf i = pathOf j then decide (i = j) else true
      let checkDisjoint : Bool :=
        (List.finRange nP).all fun i => (List.finRange nA).all fun j =>
          decide (pathOf i ≠ A.path j)
      let checkI18n : Bool :=
        (List.finRange nP).all fun i => Lang.all.all fun lang =>
          (List.finRange nP).any fun j => (pages j).route = ⟨(pages i).route.slug, lang⟩
      let checkAnchors : Bool :=
        (List.finRange nP).all fun i => (anchorsOf i).all fun a => a ∈ bodyIds (pages i).body

      -- Named witnesses for the error messages.
      let roundTripFailure : Option Route :=
        ((List.finRange nP).find? fun i =>
          indexOf (pages i).route.slug (pages i).route.lang ≠ some i).map (fun i => (pages i).route)
      let collision : Option (Route × Route × String) :=
        (List.finRange nP).findSome? fun i => (List.finRange nP).findSome? fun j =>
          if i ≠ j ∧ pathOf i = pathOf j then some ((pages i).route, (pages j).route, (pathOf i).toString)
          else none
      let assetClash : Option (Route × String) :=
        (List.finRange nP).findSome? fun i =>
          if (List.finRange nA).any (fun j => pathOf i = A.path j) then
            some ((pages i).route, (pathOf i).toString)
          else none

      match h_roundtrip : checkRoundTrip with
      | false => throw (match roundTripFailure with
          | some r => [VError.roundTripFailed r]
          | none => [VError.pageCount nP nP])
      | true =>
      match h_unique : checkUnique with
      | false => throw (match collision with
          | some (a, b, p) => [VError.pathCollision a b p]
          | none => [VError.pageCount nP nP])
      | true =>
      match h_disjoint : checkDisjoint with
      | false => throw (match assetClash with
          | some (r, p) => [VError.assetCollision r p]
          | none => [VError.pageCount nP nP])
      | true =>
      match h_i18n : checkI18n with
      | false =>
        -- Unreachable for sites built from `Site.routes` (every slug × every
        -- language); named here so a hand-built SiteRaw gets a real message.
        throw ((List.finRange nP).filterMap fun i =>
          let missing := Lang.all.filter fun lang =>
            !(List.finRange nP).any fun j => (pages j).route = ⟨(pages i).route.slug, lang⟩
          match missing with
          | [] => none
          | lang :: _ => some (VError.i18nMissing (pages i).route.slug lang))
      | true =>
      match h_anchors : checkAnchors with
      | false => throw [VError.pageCount nP nP]  -- cannot happen: same text, same anchorOf
      | true =>
        pure {
          defaultLang := raw.defaultLang
          anchorsOf := anchorsOf
          pages := pages
          indexOf := indexOf
          roundTrip₁ := fun i => by
            have h_all : (List.finRange nP).all (fun i =>
              indexOf (pages i).route.slug (pages i).route.lang = some i) = true := h_roundtrip
            simp only [List.all_eq_true, decide_eq_true_eq] at h_all
            exact h_all i (List.mem_finRange i)
          i18nComplete := fun slug h_exists lang => by
            obtain ⟨i, h_slug_eq⟩ := h_exists
            have h_all : (List.finRange nP).all (fun i => Lang.all.all fun lang =>
              (List.finRange nP).any fun j => (pages j).route = ⟨(pages i).route.slug, lang⟩) = true := h_i18n
            simp only [List.all_eq_true] at h_all
            have h_lang := h_all i (List.mem_finRange i) lang (Lang.mem_all lang)
            simp only [List.any_eq_true, decide_eq_true_eq] at h_lang
            obtain ⟨j, _, h_eq⟩ := h_lang
            exact ⟨j, by rw [h_eq, h_slug_eq]⟩
          disjointAssets := by
            intro i j
            have h_all : (List.finRange nP).all (fun i => (List.finRange nA).all fun j =>
              decide (pathOf i ≠ A.path j)) = true := h_disjoint
            simp only [List.all_eq_true, decide_eq_true_eq] at h_all
            exact h_all i (List.mem_finRange i) j (List.mem_finRange j)
          uniquePages := by
            intro i j heq
            have h_all : (List.finRange nP).all (fun i => (List.finRange nP).all fun j =>
              if pathOf i = pathOf j then decide (i = j) else true) = true := h_unique
            simp only [List.all_eq_true] at h_all
            have := h_all i (List.mem_finRange i) j (List.mem_finRange j)
            have heq' : pathOf i = pathOf j := heq
            simp only [heq', ↓reduceIte, decide_eq_true_eq] at this
            exact this
          anchors_sound := by
            intro i a ha
            have h_all : (List.finRange nP).all (fun i => (anchorsOf i).all fun a =>
              a ∈ bodyIds (pages i).body) = true := h_anchors
            simp only [List.all_eq_true, decide_eq_true_eq] at h_all
            exact h_all i (List.mem_finRange i) a ha
        }
    else
      throw allErrors
  else
    throw [VError.pageCount nP raw.pages.length]

end NoGoals
