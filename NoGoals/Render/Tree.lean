/-
  Typed HTML tree — well-formedness by construction.

  `Html` is the kernel renderer's output vocabulary: text (escaped at
  render), elements/voids with attribute lists (names must be clean tokens,
  values escaped at render), and an explicit `raw` escape hatch for the
  declared-trusted shell. `render` is the ONLY place trees become strings.

  The theorem `render_wf` is the tier promotion this module exists for:
  the rendered string of any raw-free tree lies in the inductive grammar
  `NodeStr` — properly nested tags whose text and attribute values contain
  no `< > " '`. Balanced markup stops being something html-validate checks
  at runtime and becomes something the kernel's output cannot violate.
-/

import NoGoals.Render.Escape

namespace NoGoals.Render.Tree

open NoGoals (htmlEscape htmlEscape_no_specials)

inductive Html where
  | text (s : String)
  | raw (s : String)
  | el (tag : String) (attrs : List (String × String)) (children : List Html)
  | void (tag : String) (attrs : List (String × String))
deriving Repr

/-- Tag and attribute names may appear verbatim, so they are restricted to
    ASCII alphanumerics plus `-`. Values need no such restriction — they are
    escaped. -/
def cleanToken (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '-')

/-- The HTML void elements: the only tags a `void` node may carry, and tags
    an `el` node may never carry. A browser does not treat `<div />` as
    closed nor `<img></img>` as balanced, so a tree that mixes them up is
    NOT well-formed even though its serialization balances. -/
def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]

def elTag (tag : String) : Bool := cleanToken tag && !voidTags.contains tag
def voidTag (tag : String) : Bool := cleanToken tag && voidTags.contains tag

theorem elTag_clean {tag : String} (h : elTag tag = true) : cleanToken tag = true := by
  simp only [elTag, Bool.and_eq_true] at h; exact h.1

theorem voidTag_clean {tag : String} (h : voidTag tag = true) : cleanToken tag = true := by
  simp only [voidTag, Bool.and_eq_true] at h; exact h.1

def renderAttrs (attrs : List (String × String)) : String :=
  attrs.foldl (fun acc a => acc ++ " " ++ a.1 ++ "=\"" ++ htmlEscape a.2 ++ "\"") ""

def render : Html → String
  | .text s => htmlEscape s
  | .raw s => s
  | .el tag attrs children =>
      "<" ++ tag ++ renderAttrs attrs ++ ">" ++
      ((children.map render).foldl (· ++ ·) "") ++
      "</" ++ tag ++ ">"
  | .void tag attrs =>
      "<" ++ tag ++ renderAttrs attrs ++ " />"

mutual
/-- Raw-free and clean-named, recursively: the fragment of `Html` the
    grammar theorem covers. The shell's `raw` slots are exactly what this
    excludes — that boundary is the declared trust boundary. -/
def wellFormed : Html → Bool
  | .text _ => true
  | .raw _ => false
  | .el tag attrs children =>
      elTag tag && attrs.all (fun a => cleanToken a.1) &&
      allWellFormed children
  | .void tag attrs =>
      voidTag tag && attrs.all (fun a => cleanToken a.1)

def allWellFormed : List Html → Bool
  | [] => true
  | c :: rest => wellFormed c && allWellFormed rest
end

theorem allWellFormed_iff (l : List Html) :
    allWellFormed l = true ↔ ∀ c ∈ l, wellFormed c = true := by
  induction l with
  | nil => simp [allWellFormed]
  | cons c rest ih =>
    simp [allWellFormed, Bool.and_eq_true, ih]

/-! ## The output grammar -/

/-- Attribute-string grammar: what `renderAttrs` can produce — a (possibly
    empty) run of ` name="value"` groups with clean names and special-free
    values. -/
inductive AttrsStr : String → Prop where
  | nil : AttrsStr ""
  | snoc (init name value : String)
      (hi : AttrsStr init)
      (hname : cleanToken name = true)
      (hvalue : ∀ c ∈ value.toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') :
      AttrsStr (init ++ " " ++ name ++ "=\"" ++ value ++ "\"")

/-- The output grammar, indexed: `Gram false s` — `s` is one well-formed
    node (special-free text, or a properly nested element); `Gram true s` —
    `s` is a fragment (a concatenation of zero or more nodes). One inductive
    rather than two mutual ones so `induction` applies directly. -/
inductive Gram : Bool → String → Prop where
  | text (s : String)
      (h : ∀ c ∈ s.toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') :
      Gram false s
  | el (tag attrs body : String)
      (htag : cleanToken tag = true)
      (hattrs : AttrsStr attrs)
      (hbody : Gram true body) :
      Gram false ("<" ++ tag ++ attrs ++ ">" ++ body ++ "</" ++ tag ++ ">")
  | void (tag attrs : String)
      (htag : cleanToken tag = true)
      (hattrs : AttrsStr attrs) :
      Gram false ("<" ++ tag ++ attrs ++ " />")
  | nil : Gram true ""
  | cons (s rest : String) : Gram false s → Gram true rest → Gram true (s ++ rest)

/-- One well-formed node. -/
abbrev NodeStr (s : String) : Prop := Gram false s
/-- A concatenation of zero or more well-formed nodes. -/
abbrev FragStr (s : String) : Prop := Gram true s

private theorem Gram.append_frag {flag : Bool} {a b : String}
    (ha : Gram flag a) (hb : FragStr b) : flag = true → FragStr (a ++ b) := by
  induction ha with
  | text s h => intro hc; simp at hc
  | el => intro hc; simp at hc
  | void => intro hc; simp at hc
  | nil => intro _; simpa using hb
  | cons s rest hn hf ih_n ih_f =>
    intro _
    rw [String.append_assoc]
    exact .cons s (rest ++ b) hn (ih_f rfl)

theorem FragStr.append {a b : String} (ha : FragStr a) (hb : FragStr b) :
    FragStr (a ++ b) :=
  Gram.append_frag ha hb rfl

theorem FragStr.single {s : String} (h : NodeStr s) : FragStr s := by
  simpa using Gram.cons s "" h .nil

/-- `renderAttrs` output is in the attribute grammar whenever every name is
    a clean token — values are arbitrary because they are escaped. -/
theorem renderAttrs_wf (attrs : List (String × String))
    (h : attrs.all (fun a => cleanToken a.1) = true) :
    AttrsStr (renderAttrs attrs) := by
  suffices general : ∀ (init : String), AttrsStr init →
      AttrsStr (attrs.foldl (fun acc a => acc ++ " " ++ a.1 ++ "=\"" ++ htmlEscape a.2 ++ "\"") init) by
    exact general "" .nil
  induction attrs with
  | nil => intro init hi; exact hi
  | cons a rest ih =>
    intro init hi
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ih h.2 _ (.snoc init a.1 (htmlEscape a.2) hi h.1 (htmlEscape_no_specials a.2))

/-- A left fold of node strings onto a fragment stays a fragment. -/
theorem FragStr.foldl (l : List String) (h : ∀ s ∈ l, NodeStr s)
    {init : String} (hi : FragStr init) :
    FragStr (l.foldl (· ++ ·) init) := by
  induction l generalizing init with
  | nil => exact hi
  | cons s rest ih =>
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (hi.append (FragStr.single (h s (List.mem_cons_self ..))))

mutual
/-- Every `raw` payload in a tree — the declared trusted slot contents. -/
def raws : Html → List String
  | .text _ => []
  | .raw s => [s]
  | .el _ _ children => rawsList children
  | .void _ _ => []

def rawsList : List Html → List String
  | [] => []
  | c :: rest => raws c ++ rawsList rest
end

theorem mem_rawsList_of_mem {c : Html} {l : List Html} (hc : c ∈ l)
    {s : String} (hs : s ∈ raws c) : s ∈ rawsList l := by
  induction l with
  | nil => simp at hc
  | cons c' rest ih =>
    simp only [rawsList, List.mem_append]
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact Or.inl hs
    · exact Or.inr (ih hmem)

mutual
/-- `wellFormed` with `raw` treated as a hole: the tree's own structure is
    clean; slot contents are someone else's obligation. -/
def wellFormedMod : Html → Bool
  | .text _ => true
  | .raw _ => true
  | .el tag attrs children =>
      elTag tag && attrs.all (fun a => cleanToken a.1) &&
      allWellFormedMod children
  | .void tag attrs =>
      voidTag tag && attrs.all (fun a => cleanToken a.1)

def allWellFormedMod : List Html → Bool
  | [] => true
  | c :: rest => wellFormedMod c && allWellFormedMod rest
end

theorem allWellFormedMod_append (a b : List Html) :
    allWellFormedMod (a ++ b) = (allWellFormedMod a && allWellFormedMod b) := by
  induction a with
  | nil => simp [allWellFormedMod]
  | cons c rest ih => simp [allWellFormedMod, ih, Bool.and_assoc]

theorem allWellFormedMod_iff (l : List Html) :
    allWellFormedMod l = true ↔ ∀ c ∈ l, wellFormedMod c = true := by
  induction l with
  | nil => simp [allWellFormedMod]
  | cons c rest ih =>
    simp [allWellFormedMod, Bool.and_eq_true, ih]

/-- A left fold of fragment strings onto a fragment stays a fragment. -/
theorem FragStr.foldl_frags (l : List String) (h : ∀ s ∈ l, FragStr s)
    {init : String} (hi : FragStr init) :
    FragStr (l.foldl (· ++ ·) init) := by
  induction l generalizing init with
  | nil => exact hi
  | cons s rest ih =>
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (hi.append (h s (List.mem_cons_self ..)))

/-- **The conditional tier promotion for slotted trees**: if every `raw`
    slot's content is itself a well-formed fragment, the rendered tree is
    one — the kernel's structure cannot introduce imbalance; only slot
    content could, and each slot is a named, declared trust obligation. -/
theorem render_wf_mod : (h : Html) → wellFormedMod h = true →
    (∀ s ∈ raws h, FragStr s) → FragStr (render h)
  | .text s, _, _ =>
      FragStr.single (by simpa [render] using Gram.text (htmlEscape s) (htmlEscape_no_specials s))
  | .raw s, _, hr => by
      simpa [render] using hr s (by simp [raws])
  | .el tag attrs children, hw, hr => by
      simp only [wellFormedMod, Bool.and_eq_true] at hw
      obtain ⟨⟨htag, hattrs⟩, hkids⟩ := hw
      have hbody : FragStr ((children.map render).foldl (· ++ ·) "") := by
        refine FragStr.foldl_frags _ ?_ .nil
        intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨c, hc, rfl⟩ := hs
        refine render_wf_mod c ((allWellFormedMod_iff children).mp hkids c hc) ?_
        intro s' hs'
        exact hr s' (by simpa [raws] using mem_rawsList_of_mem hc hs')
      exact FragStr.single (by
        simpa [render] using
          Gram.el tag (renderAttrs attrs) _ (elTag_clean htag) (renderAttrs_wf attrs hattrs) hbody)
  | .void tag attrs, hw, _ => by
      simp only [wellFormedMod, Bool.and_eq_true] at hw
      exact FragStr.single (by
        simpa [render] using
          Gram.void tag (renderAttrs attrs) (voidTag_clean hw.1) (renderAttrs_wf attrs hw.2))
  termination_by h => sizeOf h
  decreasing_by
    have := List.sizeOf_lt_of_mem hc
    simp only [Html.el.sizeOf_spec]
    omega

/-- **The tier promotion**: the rendered string of any raw-free tree is a
    single well-formed node — nested tags balance, text and attribute values
    cannot close or open a tag. `raw` slots (the declared trusted shell) are
    exactly the trees this theorem refuses to cover. -/
theorem render_wf : (h : Html) → wellFormed h = true → NodeStr (render h)
  | .text s, _ => by
      simpa [render] using Gram.text (htmlEscape s) (htmlEscape_no_specials s)
  | .raw _, hw => by simp [wellFormed] at hw
  | .el tag attrs children, hw => by
      simp only [wellFormed, Bool.and_eq_true] at hw
      obtain ⟨⟨htag, hattrs⟩, hkids⟩ := hw
      have hbody : FragStr ((children.map render).foldl (· ++ ·) "") := by
        refine FragStr.foldl _ ?_ .nil
        intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨c, hc, rfl⟩ := hs
        exact render_wf c ((allWellFormed_iff children).mp hkids c hc)
      simpa [render] using
        Gram.el tag (renderAttrs attrs) _ (elTag_clean htag) (renderAttrs_wf attrs hattrs) hbody
  | .void tag attrs, hw => by
      simp only [wellFormed, Bool.and_eq_true] at hw
      simpa [render] using
        Gram.void tag (renderAttrs attrs) (voidTag_clean hw.1) (renderAttrs_wf attrs hw.2)
  termination_by h => sizeOf h
  decreasing_by
    have := List.sizeOf_lt_of_mem hc
    simp only [Html.el.sizeOf_spec]
    omega

/-! ## Declared ids — what a fragment link may point at -/

mutual
/-- Every `id` attribute value in a tree, in document order. -/
def ids : Html → List String
  | .text _ => []
  | .raw _ => []
  | .el _ attrs children => (attrs.filterMap fun a => if a.1 = "id" then some a.2 else none) ++ idsList children
  | .void _ attrs => attrs.filterMap fun a => if a.1 = "id" then some a.2 else none

def idsList : List Html → List String
  | [] => []
  | c :: rest => ids c ++ idsList rest
end

theorem mem_idsList_of_mem {c : Html} {l : List Html} (hc : c ∈ l)
    {s : String} (hs : s ∈ ids c) : s ∈ idsList l := by
  induction l with
  | nil => simp at hc
  | cons c' rest ih =>
    simp only [idsList, List.mem_append]
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact Or.inl hs
    · exact Or.inr (ih hmem)

theorem idsList_append (a b : List Html) : idsList (a ++ b) = idsList a ++ idsList b := by
  induction a with
  | nil => simp [idsList]
  | cons c rest ih => simp [idsList, ih]

end NoGoals.Render.Tree
