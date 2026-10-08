/-
  NoGoals Bridge — from a site's `Site` to its verified `SiteV`, and from the NoGoals
  theorems to report entries about THIS site.

  A site proves two facts by `native_decide` on its concrete data — its
  asset paths are distinct, and `NoGoals.refine` accepts its route skeleton — and
  `Bridge.mk` turns them into: the `SiteV` value the theorems are about, the
  page/asset path list the build must emit exactly, and the guarantee
  entries that state each NoGoals theorem as a property of this build (they
  REPLACE the kernel-generic entries of the same id in the report).

  ```lean
  theorem assets_unique : NoGoals.Bridge.AssetsUnique site := by native_decide
  theorem refine_ok : NoGoals.Bridge.RefineOk site assets_unique := by native_decide
  def bridge : NoGoals.Bridge := NoGoals.Bridge.mk site assets_unique refine_ok
  ```
-/

import NoGoals.Compile

namespace NoGoals

open NoGoals.DSL
open NoGoals.Compile

namespace Bridge

/-- The raw skeleton: every route with an empty kernel body. -/
def raw (site : Site) : SiteRaw := toSiteRaw site

def nP (site : Site) : Nat := (raw site).pages.length
def nA (site : Site) : Nat := site.assets.length

def assetAt (site : Site) (i : Fin (nA site)) : AssetPath := site.assets[i.val].path

/-- The site's asset paths are pairwise distinct — decidable on the concrete list. -/
abbrev AssetsUnique (site : Site) : Prop :=
  ∀ (i j : Fin (nA site)), assetAt site i = assetAt site j → i = j

/-- The site's asset palette as a verified `Assets` value. -/
def assets (site : Site) (h : AssetsUnique site) : Assets (nA site) where
  name := assetAt site
  kind := fun i => site.assets[i.val].kind
  bytes := fun _ => ByteArray.empty
  unique := fun {i j} hn => h i j hn

/-- The site refined through NoGoals's verified pipeline. -/
def refined (site : Site) (h : AssetsUnique site) :
    Except (List VError) (SiteV (nP site) (nA site) (assets site h)) :=
  refine (nA := nA site) (nP := nP site) (assets site h) (raw site)

/-- `NoGoals.refine` accepts the site — decidable on the concrete data. -/
abbrev RefineOk (site : Site) (h : AssetsUnique site) : Prop :=
  (refined site h).toOption.isSome = true

end Bridge

/-- A site's verified bridge: the `SiteV`, the proved output list, and the
    report entries stating NoGoals's theorems about this build. -/
structure Bridge where
  site : Site
  assetsUnique : Bridge.AssetsUnique site
  refineOk : Bridge.RefineOk site assetsUnique

namespace Bridge

variable (b : Bridge)

def siteV : SiteV (nP b.site) (nA b.site) (assets b.site b.assetsUnique) :=
  (refined b.site b.assetsUnique).toOption.get b.refineOk

/-- The page and asset paths the build must emit exactly — read off the
    `SiteV` the theorems are about (`pathOf`, `Assets.path`), not re-derived
    from the `Site`, so the staged-set check compares the artifact with the
    proved object. -/
def expectedOutputs : List String :=
  (List.finRange (nP b.site)).map (fun i => (b.siteV.pathOf i).toString) ++
  (List.finRange (nA b.site)).map (fun j => ((assets b.site b.assetsUnique).path j).toString)

/-- Instances of the NoGoals theorems on this site's `SiteV`. -/
theorem roundTrip₁ : ∀ i, b.siteV.indexOf (b.siteV.pages i).route.slug (b.siteV.pages i).route.lang = some i :=
  b.siteV.roundTrip₁
theorem i18nComplete :
    ∀ slug, (∃ i, (b.siteV.pages i).route.slug = slug) → ∀ lang, ∃ j, (b.siteV.pages j).route = ⟨slug, lang⟩ :=
  b.siteV.i18nComplete
theorem uniquePages : ∀ i j, b.siteV.pathOf i = b.siteV.pathOf j → i = j := b.siteV.uniquePages
theorem disjointAssets : ∀ i j, b.siteV.pathOf i ≠ (assets b.site b.assetsUnique).path j := b.siteV.disjointAssets
theorem plan_unique_paths :
    ∀ i j hi hj, ((plan _ b.siteV).files.get ⟨i, hi⟩).path = ((plan _ b.siteV).files.get ⟨j, hj⟩).path → i = j :=
  unique_paths _ b.siteV
theorem plan_covers_pages : ∀ p ∈ List.finRange (nP b.site), ∃ f ∈ (plan _ b.siteV).files, f.path = b.siteV.pathOf p :=
  fun p hp => (coverage _ b.siteV).1 p hp

/-- The report entries: each NoGoals theorem as a fact about THIS build. Their
    `NoGoals.*` ids replace the kernel-generic entries. -/
def guarantees : List Guarantee :=
  let n := nP b.site
  let a := nA b.site
  [ { category := "Theorems", name := "Slug/(slug,lang) round-trip"
      description := s!"For all i, indexOf (slug i) (lang i) = some i — on this site's SiteV {n} {a}"
      status := .enforced "NoGoals.SiteV.roundTrip₁ (via NoGoals.Bridge.siteV)"
      location := some (toString ``NoGoals.Bridge.roundTrip₁), scope := .artifact, id := "nogoals.roundtrip" },
    { category := "Theorems", name := "i18n completeness"
      description := "Every page slug exists in both languages — NoGoals theorem on this site's SiteV"
      status := .enforced "NoGoals.SiteV.i18nComplete (via NoGoals.Bridge.siteV)"
      location := some (toString ``NoGoals.Bridge.i18nComplete), scope := .artifact, id := "nogoals.i18n-complete", headline := true },
    { category := "Theorems", name := "No duplicate page paths"
      description := s!"All {n} route paths in the verified site are distinct"
      status := .enforced "NoGoals.SiteV.uniquePages (via NoGoals.Bridge.siteV)"
      location := some (toString ``NoGoals.Bridge.uniquePages), scope := .artifact, id := "site.unique-page-paths", headline := true },
    { category := "Theorems", name := "Pages/assets path disjoint"
      description := s!"No route path collides with any of the {a} asset paths"
      status := .enforced "NoGoals.SiteV.disjointAssets (via NoGoals.Bridge.siteV)"
      location := some (toString ``NoGoals.Bridge.disjointAssets), scope := .artifact, id := "nogoals.disjoint-assets" },
    { category := "Theorems", name := "Asset path injectivity"
      description := s!"All {a} asset paths are distinct (native_decide on the concrete list)"
      status := .enforced "NoGoals.Bridge.AssetsUnique"
      location := some (toString ``NoGoals.Bridge.AssetsUnique), scope := .artifact, id := "nogoals.asset-injective" },
    { category := "Theorems", name := "No file collisions in build plan"
      description := s!"All {n + a} page and asset files in the NoGoals build plan have unique paths"
      status := .enforced "NoGoals.unique_paths (via NoGoals.Bridge.siteV)"
      location := some (toString ``NoGoals.Bridge.plan_unique_paths), scope := .artifact, id := "nogoals.unique-paths", headline := true },
    { category := "Theorems", name := "Build covers all pages"
      description := "Every route in the verified site has a corresponding file in the build plan"
      status := .enforced "NoGoals.coverage (via NoGoals.Bridge.siteV)"
      location := some (toString ``NoGoals.Bridge.plan_covers_pages), scope := .artifact, id := "nogoals.coverage" },
    { category := "Type Safety", name := "NoGoals.refine accepts this site"
      description := s!"NoGoals.refine produces a verified SiteV {n} {a} value at compile time"
      status := .enforced "NoGoals.Bridge.RefineOk (native_decide)"
      location := some (toString ``NoGoals.Bridge.RefineOk), scope := .artifact, id := "site.refine-ok" } ]

end Bridge

end NoGoals
