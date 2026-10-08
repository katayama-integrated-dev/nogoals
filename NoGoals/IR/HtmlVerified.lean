import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlRaw

namespace NoGoals

/-- An anchor is the `id` of a heading — a validated segment, so it is
    always a legal `id` attribute and a legal URL fragment. -/
abbrev AnchorId := Segment

/-- Slugify one character stream: ASCII letters lower-cased, digits kept,
    any run of other characters becomes a single `-` between words. -/
def anchorChars : List Char → Bool → List Char → List Char
  | [], _, acc => acc.reverse
  | c :: cs, pendingDash, acc =>
    if c.isLower || c.isDigit || c.isUpper then
      let acc := if pendingDash && !acc.isEmpty then '-' :: acc else acc
      anchorChars cs false (c.toLower :: acc)
    else anchorChars cs true acc

/-- Heading text → its anchor id. `none` when nothing survives (a heading
    made of punctuation or non-ASCII text gets no id). -/
def anchorOf (text : String) : Option AnchorId :=
  Segment.parse? (String.ofList (anchorChars text.toList false []))

/-- `nP` indexes pages (so `Fin nP` is a page-link target); `nA` indexes
    assets; `Anc` is the anchor schema: the ids each page declares. A link's
    fragment is a *member* of the target page's schema — an undeclared
    fragment is unrepresentable (this is `AnchorIn`, wired). -/
inductive InlineV (nP : Nat) (nA : Nat) (A : Assets nA) (Anc : Fin nP → List AnchorId)
| text (s : String)
| code (s : String)
| link (target_page : Fin nP) (anchor : Option { a : AnchorId // a ∈ Anc target_page }) (label : NonEmptyStr)
| extlink (url : Url.Safe) (label : NonEmptyStr)

inductive BlockV (nP : Nat) (nA : Nat) (A : Assets nA) (Anc : Fin nP → List AnchorId)
| p        (xs : List (InlineV nP nA A Anc))
| ul       (items : List (List (InlineV nP nA A Anc)))
| heading  (lvl : HLevel) (display : Display) (txt : NonEmptyStr)
| img      (src : AssetId nA .image A) (alt : NonEmptyStr)
| section  (title? : Option NonEmptyStr) (children : List (BlockV nP nA A Anc))

/-- The ids the renderer will emit for a body: one per heading whose text
    yields an anchor, recursively through sections. -/
def headingIds {nP nA : Nat} {A : Assets nA} {Anc : Fin nP → List AnchorId} :
    BlockV nP nA A Anc → List AnchorId
  | .heading _ _ txt => (anchorOf txt.s).toList
  | .section _ children => children.attach.flatMap (fun ⟨c, _⟩ => headingIds c)
  | _ => []

def bodyIds {nP nA : Nat} {A : Assets nA} {Anc : Fin nP → List AnchorId}
    (body : List (BlockV nP nA A Anc)) : List AnchorId :=
  body.flatMap headingIds

structure PageV (nP : Nat) (nA : Nat) (A : Assets nA) (Anc : Fin nP → List AnchorId) : Type where
  route : Route
  title : String
  body  : List (BlockV nP nA A Anc)

/-- A verified site: `nP` pages over an asset palette of size `nA`.

    The anchor schema `anchorsOf` comes first so the page bodies can depend
    on it; `anchors_sound` is what makes a declared anchor an emitted id. -/
structure SiteV (nP : Nat) (nA : Nat) (A : Assets nA) : Type where
  defaultLang  : Lang
  anchorsOf    : Fin nP → List AnchorId
  pages        : Fin nP → PageV nP nA A anchorsOf
  /-- Look up a page by `(slug, lang)` — the unique key of a bilingual site. -/
  indexOf      : Slug → Lang → Option (Fin nP)
  roundTrip₁   : ∀ i, indexOf (pages i).route.slug (pages i).route.lang = some i
  /-- Every slug exists in every language (the product's language set is
      closed, so this quantifies over all of `Lang`). -/
  i18nComplete : ∀ slug, (∃ i, (pages i).route.slug = slug) → ∀ lang, ∃ j, (pages j).route = ⟨slug, lang⟩
  disjointAssets : ∀ (i : Fin nP) (j : Fin nA), Path.mk ((pages i).route.outputPath defaultLang) ≠ A.path j
  uniquePages : ∀ i j, Path.mk ((pages i).route.outputPath defaultLang) = Path.mk ((pages j).route.outputPath defaultLang) → i = j
  anchors_sound : ∀ i, ∀ a ∈ anchorsOf i, a ∈ bodyIds (pages i).body

namespace SiteV

variable {nP nA : Nat} {A : Assets nA}

def slugOf (S : SiteV nP nA A) (i : Fin nP) : Slug := (S.pages i).route.slug
def langOf (S : SiteV nP nA A) (i : Fin nP) : Lang := (S.pages i).route.lang

/-- The output file of page `i` — the one path function, applied. -/
def pathOf (S : SiteV nP nA A) (i : Fin nP) : Path :=
  ⟨(S.pages i).route.outputPath S.defaultLang⟩

/-- The root-relative href of page `i`. -/
def hrefOf (S : SiteV nP nA A) (i : Fin nP) : String :=
  (S.pages i).route.href S.defaultLang

end SiteV

end NoGoals
