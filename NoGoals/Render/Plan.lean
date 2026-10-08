import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlVerified
import NoGoals.Render.Html

namespace NoGoals

structure File where
  path  : Path
  bytes : ByteArray

structure BuildPlan where
  files : List File

variable {nP nA : Nat} {A : Assets nA}

-- Reference tracking (total — theorems about it are stateable)
def refsInline (_S : SiteV nP nA A) : InlineV nP nA A _S.anchorsOf → (List (Fin nP) × List (Fin nA))
  | .text _ => ([], [])
  | .code _ => ([], [])
  | .link p _ _ => ([p], [])
  | .extlink _ _ => ([], [])

def refsBlock (S : SiteV nP nA A) : BlockV nP nA A S.anchorsOf → (List (Fin nP) × List (Fin nA))
  | .p xs      => xs.foldl (init := ([], [])) (fun (P,Aa) x =>
                      let (P',A') := refsInline S x; (P ++ P', Aa ++ A'))
  | .ul xss    => xss.foldl (init := ([], [])) (fun acc xs =>
                      xs.foldl (init := acc) (fun (P,Aa) x => let (P',A') := refsInline S x; (P ++ P', Aa ++ A')))
  | .heading .. => ([], [])
  | .img src _  => ([], [src.val])
  | .section _ cs =>
      (cs.attach.map (fun ⟨c, _⟩ => refsBlock S c)).foldl
        (init := ([], [])) (fun (P,Aa) (P',A') => (P ++ P', Aa ++ A'))

def renderPage (S : SiteV nP nA A) (i : Fin nP) : File :=
  { path := S.pathOf i
  , bytes := (renderPageHtml S i).toUTF8 }

def renderAssets (A : Assets nA) : List File :=
  (List.finRange nA).map (fun i => { path := A.path i, bytes := A.bytes i })

def plan (A : Assets nA) (S : SiteV nP nA A) : BuildPlan :=
  let pageFiles := (List.finRange _).map (renderPage S)
  { files := pageFiles ++ renderAssets A }

/-- Helper: length of page files segment -/
theorem pages_segment_length (S : SiteV nP nA A) :
    ((List.finRange nP).map (renderPage S)).length = nP := by
  simp only [List.length_map, List.length_finRange]

/-- Helper: length of plan files -/
theorem plan_files_length (A : Assets nA) (S : SiteV nP nA A) :
    (plan A S).files.length = nP + nA := by
  simp only [plan, List.length_append, List.length_map, List.length_finRange,
             renderAssets, List.length_map]

/-- Helper: accessing a page path from P.files in the page segment -/
theorem page_path_in_plan (S : SiteV nP nA A) (i : Nat) (hi_lt : i < nP)
    (hi : i < (plan A S).files.length) :
    ((plan A S).files[i]'hi).path = S.pathOf ⟨i, hi_lt⟩ := by
  have hp_lt : i < ((List.finRange nP).map (renderPage S)).length := by
    rw [pages_segment_length S]; exact hi_lt
  show (((List.finRange nP).map (renderPage S) ++ renderAssets A)[i]'hi).path = _
  rw [List.getElem_append_left hp_lt]
  simp only [List.getElem_map, List.getElem_finRange, renderPage]
  rfl

/-- Helper: accessing an asset path from P.files in the asset segment -/
theorem asset_path_in_plan (S : SiteV nP nA A) (j : Nat) (hj_ge : nP ≤ j) (hj_lt : j < nP + nA)
    (hj : j < (plan A S).files.length) :
    let hj_sub : j - nP < nA := Nat.sub_lt_left_of_lt_add hj_ge hj_lt
    ((plan A S).files[j]'hj).path = A.path ⟨j - nP, hj_sub⟩ := by
  intro hj_sub
  have h_pages_len := pages_segment_length S
  have hj_ge' : ((List.finRange nP).map (renderPage S)).length ≤ j := by
    rw [h_pages_len]; exact hj_ge
  show (((List.finRange nP).map (renderPage S) ++ renderAssets A)[j]'hj).path = _
  rw [List.getElem_append_right hj_ge']
  simp only [renderAssets, List.getElem_map, List.getElem_finRange, h_pages_len]
  rfl

/-- Helper: every page (as Fin nP) has a corresponding file in the plan -/
theorem page_file_exists (S : SiteV nP nA A) (p : Fin nP) :
    ∃ f ∈ (plan A S).files, f.path = S.pathOf p := by
  have hp : p.val < (plan A S).files.length := by rw [plan_files_length A S]; omega
  exact ⟨(plan A S).files[p.val]'hp, List.getElem_mem hp, page_path_in_plan S p.val p.isLt hp⟩

/-- Helper: every asset (as Fin nA) has a corresponding file in the plan -/
theorem asset_file_exists (S : SiteV nP nA A) (a : Fin nA) :
    let P := plan A S
    ∃ f ∈ P.files, f.path = A.path a := by
  intro P
  have h_len : P.files.length = nP + nA := plan_files_length A S
  have ha_lt : nP + a.val < P.files.length := by rw [h_len]; omega
  have h_pages_len := pages_segment_length S
  have ha_ge : ((List.finRange nP).map (renderPage S)).length ≤ nP + a.val := by
    rw [h_pages_len]; omega
  refine ⟨P.files[nP + a.val]'ha_lt, List.getElem_mem ha_lt, ?_⟩
  show (((List.finRange nP).map (renderPage S) ++ renderAssets A)[nP + a.val]'ha_lt).path = _
  rw [List.getElem_append_right ha_ge]
  simp only [renderAssets, List.getElem_map, List.getElem_finRange, h_pages_len]
  congr 1; ext; simp only [Fin.val_cast, Nat.add_sub_cancel_left]

/-- Build plan has unique output paths (no file overwrites) -/
theorem unique_paths (A : Assets nA) (S : SiteV nP nA A) :
    let P := plan A S
    ∀ i j hi hj, (P.files.get ⟨i, hi⟩).path = (P.files.get ⟨j, hj⟩).path → i = j := by
  intro P i j hi hj heq
  -- P.files = pages ++ assets. Paths are unique within each segment and disjoint between them.
  have h_len : P.files.length = nP + nA := plan_files_length A S
  have hi' : i < nP + nA := by rw [← h_len]; exact hi
  have hj' : j < nP + nA := by rw [← h_len]; exact hj
  -- Case analysis: is each index in pages (< nP) or assets (>= nP)?
  by_cases hi_lt : i < nP
  · by_cases hj_lt : j < nP
    · -- Both in pages segment: use S.uniquePages
      have hpi := page_path_in_plan S i hi_lt hi
      have hpj := page_path_in_plan S j hj_lt hj
      rw [List.get_eq_getElem, hpi, List.get_eq_getElem, hpj] at heq
      exact congrArg Fin.val (S.uniquePages ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ heq)
    · -- i in pages, j in assets: contradiction via disjointAssets
      have hj_ge : nP ≤ j := Nat.not_lt.mp hj_lt
      have hpi := page_path_in_plan S i hi_lt hi
      have haj := asset_path_in_plan S j hj_ge hj' hj
      rw [List.get_eq_getElem, hpi, List.get_eq_getElem, haj] at heq
      exact absurd heq (S.disjointAssets ⟨i, hi_lt⟩ ⟨j - nP, _⟩)
  · by_cases hj_lt : j < nP
    · -- i in assets, j in pages: contradiction via disjointAssets (symmetric)
      have hi_ge : nP ≤ i := Nat.not_lt.mp hi_lt
      have hai := asset_path_in_plan S i hi_ge hi' hi
      have hpj := page_path_in_plan S j hj_lt hj
      rw [List.get_eq_getElem, hai, List.get_eq_getElem, hpj] at heq
      exact absurd heq.symm (S.disjointAssets ⟨j, hj_lt⟩ ⟨i - nP, _⟩)
    · -- Both in assets segment: use Assets.path_injective
      have hi_ge : nP ≤ i := Nat.not_lt.mp hi_lt
      have hj_ge : nP ≤ j := Nat.not_lt.mp hj_lt
      have hai := asset_path_in_plan S i hi_ge hi' hi
      have haj := asset_path_in_plan S j hj_ge hj' hj
      rw [List.get_eq_getElem, hai, List.get_eq_getElem, haj] at heq
      have : i - nP = j - nP := congrArg Fin.val (Assets.path_injective A heq)
      omega

theorem coverage (A : Assets nA) (S : SiteV nP nA A) :
  let P := plan A S
  (∀ p ∈ (List.finRange nP), ∃ f ∈ P.files, f.path = S.pathOf p) ∧
  (∀ i b, b ∈ (S.pages i).body →
    let (Ps,As) := refsBlock S b
    (∀ p ∈ Ps, ∃ f ∈ P.files, f.path = S.pathOf p) ∧
    (∀ a ∈ As, ∃ f ∈ P.files, f.path = A.path a)) := by
  intro P
  constructor
  · -- Part 1: Every page has a corresponding file
    intro p _; exact page_file_exists S p
  · -- Part 2: Every referenced page/asset has a corresponding file
    intro _ _ _
    exact ⟨fun p _ => page_file_exists S p, fun a _ => asset_file_exists S a⟩

/-! ## End-to-end: rendered hrefs resolve to plan files

The renderer is total (no `partial`), so these are honest statements about
the emitted HTML, not about an opaque implementation. -/

/-- What the kernel emits for an internal link: an `<a>` whose href is
    `linkHref` — the target route's root-relative href plus the fragment. -/
theorem inlineToHtml_link_href (S : SiteV nP nA A) (p : Fin nP)
    (anchor? : Option { a : AnchorId // a ∈ S.anchorsOf p }) (l : NonEmptyStr) :
    inlineToHtml S (.link p anchor? l) =
      .el "a" [("href", linkHref S p anchor?)] [.text l.s] := rfl

/-- **Route closure**: the href emitted for any anchor-less internal link,
    resolved the way a browser and the host resolve it (from ANY source
    page, on any real origin), is exactly the output file of a file in the
    build plan. Targets outside `Fin nP` are unrepresentable, so this covers
    every internal link the kernel can emit. -/
theorem rendered_link_resolves (S : SiteV nP nA A) (p : Fin nP)
    (origin source : String) (hor : ∀ c, origin.toList.head? = some c → c ≠ '/') :
    ∃ f ∈ (plan A S).files,
      resolveUrl origin source (linkHref S p none) = .ok ⟨[f.path.toString], none⟩ := by
  obtain ⟨f, hf, hpath⟩ := page_file_exists S p
  refine ⟨f, hf, ?_⟩
  rw [hpath]
  simp only [linkHref, SiteV.hrefOf, SiteV.pathOf]
  exact resolve_href origin source _ _ hor

/-- **Fragment closure**: a link that names an anchor names one the target
    page's rendered tree declares as an `id`. `anchors_sound` (refinement)
    plus `body_ids_emitted` (renderer) — an undeclared fragment is
    unrepresentable, and a declared one is emitted. -/
theorem rendered_fragment_declared (S : SiteV nP nA A) (p : Fin nP)
    (a : { a : AnchorId // a ∈ S.anchorsOf p }) :
    a.1.s ∈ Render.Tree.idsList ((S.pages p).body.map (blockToHtml S)) :=
  body_ids_emitted S _ a.1 (S.anchors_sound p a.1 a.2)

/-- Same, for images: every image reference expressible in the IR points at
    an asset file present in the plan. -/
theorem rendered_img_src_in_plan (S : SiteV nP nA A)
    (src : AssetId nA .image A) :
    ∃ f ∈ (plan A S).files, f.path = A.path src.val :=
  asset_file_exists S src.val

end NoGoals
