/-
  Routes — the one place a URL or an output path comes from.

  Every page of a site is a `Route := (slug, lang)`. Its root-relative href
  (`/`, `/about/`, `/en/news/x/`) and its output file (`index.html`,
  `about/index.html`, `en/news/x/index.html`) are two views of the SAME
  segment list, computed by one function. There is no second path scheme
  anywhere — not in `Meta`, not in the consumer — so sitemap, switcher,
  canonical link, feed URL and emitted file cannot disagree.

  Segments are validated by type: a `Segment` is a non-empty run of
  `[a-z0-9-]`, so `.`, `..`, `/`, spaces and unicode are unrepresentable and
  a slug can never escape the output root. Asset file names (`FileSegment`)
  additionally allow `.` and `_` but reject `.` and `..`; both are
  lower-case only, so two distinct names are two distinct files on every
  filesystem.

  `resolveUrl` models how a browser resolves an href against the page it
  appears on and how Cloudflare Pages maps a URL onto an emitted file. The
  theorem `resolve_href` closes the loop for the kernel's own links: the
  href it emits for a route resolves to that route's output file.
-/

namespace NoGoals

/-- The elements that occur more than once, each once, in first-occurrence
    order. THE duplicate finder — every "is this list free of duplicates?"
    check in NoGoals and its consumer asks this one function. -/
def dupes {α : Type} [BEq α] (xs : List α) : List α :=
  (xs.filter (fun x => xs.count x > 1)).eraseDups

/-! ## Character-level helpers (structural, so `decide` reduces them) -/

def Segment.charOk (c : Char) : Bool := c.isLower || c.isDigit || c == '-'

def Segment.allOk : List Char → Bool
  | [] => true
  | c :: cs => Segment.charOk c && Segment.allOk cs

theorem Segment.allOk_iff (cs : List Char) :
    Segment.allOk cs = true ↔ ∀ c ∈ cs, Segment.charOk c = true := by
  induction cs with
  | nil => simp [Segment.allOk]
  | cons c rest ih => simp [Segment.allOk, ih]

/-- `[a-z0-9-]+` — a URL path segment that needs no escaping and cannot be
    `.` or `..`. -/
def Segment.valid (s : String) : Bool := !s.toList.isEmpty && Segment.allOk s.toList

structure Segment where
  s : String
  ok : Segment.valid s = true
deriving DecidableEq, Repr

namespace Segment

/-- Checked literal: `Segment.lit "about"`. A bad literal is a compile error. -/
def lit (s : String) (h : valid s = true := by decide) : Segment := ⟨s, h⟩

def parse? (s : String) : Option Segment :=
  if h : valid s = true then some ⟨s, h⟩ else none

instance : ToString Segment := ⟨(·.s)⟩

theorem data_ne_nil (a : Segment) : a.s.toList ≠ [] := by
  have h := a.ok
  simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  exact h.1

theorem no_slash (a : Segment) : '/' ∉ a.s.toList := by
  intro hmem
  have h := a.ok
  simp only [valid, Bool.and_eq_true] at h
  have := (allOk_iff _).mp h.2 '/' hmem
  simp [charOk] at this

theorem no_dot (a : Segment) : '.' ∉ a.s.toList := by
  intro hmem
  have h := a.ok
  simp only [valid, Bool.and_eq_true] at h
  have := (allOk_iff _).mp h.2 '.' hmem
  simp [charOk] at this

end Segment

/-! ## File segments (asset names) -/

def FileSegment.charOk (c : Char) : Bool :=
  c.isLower || c.isDigit || c == '-' || c == '_' || c == '.'

def FileSegment.allOk : List Char → Bool
  | [] => true
  | c :: cs => FileSegment.charOk c && FileSegment.allOk cs

theorem FileSegment.allOk_iff (cs : List Char) :
    FileSegment.allOk cs = true ↔ ∀ c ∈ cs, FileSegment.charOk c = true := by
  induction cs with
  | nil => simp [FileSegment.allOk]
  | cons c rest ih => simp [FileSegment.allOk, ih]

/-- `[a-z0-9._-]+`, but never `.` or `..`. Lower-case only: on a
    case-insensitive filesystem `Logo.png` and `logo.png` are one file. -/
def FileSegment.valid (s : String) : Bool :=
  !s.toList.isEmpty && FileSegment.allOk s.toList && s.toList != ['.'] && s.toList != ['.', '.']

structure FileSegment where
  s : String
  ok : FileSegment.valid s = true
deriving DecidableEq, Repr

namespace FileSegment

def lit (s : String) (h : valid s = true := by decide) : FileSegment := ⟨s, h⟩

def parse? (s : String) : Option FileSegment :=
  if h : valid s = true then some ⟨s, h⟩ else none

instance : ToString FileSegment := ⟨(·.s)⟩

theorem no_slash (a : FileSegment) : '/' ∉ a.s.toList := by
  intro hmem
  have h := a.ok
  simp only [valid, Bool.and_eq_true] at h
  have := (allOk_iff _).mp h.1.1.2 '/' hmem
  simp [charOk] at this

end FileSegment

/-! ## Splitting and joining on `/` — the inverse pair every theorem below rests on -/

/-- Prepend a character to the first part (there is always one). -/
def consHead (c : Char) : List (List Char) → List (List Char)
  | [] => [[c]]
  | h :: t => (c :: h) :: t

/-- Split on `/`. Total and structural: `splitSlash "a/b/" = [a, b, []]`,
    `splitSlash "" = [[]]`. -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => if c = '/' then [] :: splitSlash cs else consHead c (splitSlash cs)

theorem splitSlash_ne_nil (cs : List Char) : splitSlash cs ≠ [] := by
  induction cs with
  | nil => simp [splitSlash]
  | cons c rest ih =>
    simp only [splitSlash]
    split
    · simp
    · cases splitSlash rest with
      | nil => simp [consHead]
      | cons h t => simp [consHead]

/-- A slash-free word followed by `/` is peeled off whole. -/
theorem splitSlash_append_slash (w cs : List Char) (hw : '/' ∉ w) :
    splitSlash (w ++ '/' :: cs) = w :: splitSlash cs := by
  induction w with
  | nil => simp [splitSlash]
  | cons c w' ih =>
    have hc : c ≠ '/' := fun h => hw (by simp [h])
    have hw' : '/' ∉ w' := fun h => hw (List.mem_cons_of_mem _ h)
    simp only [List.cons_append, splitSlash, hc, ↓reduceIte, ih hw']
    rfl

/-- Every part joined with a trailing `/`: `[a, b] ↦ "a/b/"`. -/
def joinDirs (parts : List (List Char)) : List Char :=
  (parts.map (· ++ ['/'])).flatten

theorem splitSlash_joinDirs (parts : List (List Char)) (h : ∀ p ∈ parts, '/' ∉ p) :
    splitSlash (joinDirs parts) = parts ++ [[]] := by
  induction parts with
  | nil => simp [joinDirs, splitSlash]
  | cons p rest ih =>
    have hp : '/' ∉ p := h p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, '/' ∉ q := fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [joinDirs, List.map_cons, List.flatten_cons, List.append_assoc, List.singleton_append]
    rw [splitSlash_append_slash p _ hp]
    simp only [joinDirs] at ih
    rw [ih hrest]
    rfl

/-- Parts joined with `/` between them (no trailing slash): `[a, b] ↦ "a/b"`. -/
def joinSlash : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: rest => p ++ '/' :: joinSlash rest

/-- A single slash-free word splits to itself. -/
theorem splitSlash_word (w : List Char) (hw : '/' ∉ w) : splitSlash w = [w] := by
  induction w with
  | nil => rfl
  | cons c w' ih =>
    have hc : c ≠ '/' := fun h => hw (by simp [h])
    have hw' : '/' ∉ w' := fun h => hw (List.mem_cons_of_mem _ h)
    simp only [splitSlash, hc, ↓reduceIte, ih hw', consHead]

theorem splitSlash_joinSlash (parts : List (List Char)) (hne : parts ≠ [])
    (h : ∀ p ∈ parts, '/' ∉ p) : splitSlash (joinSlash parts) = parts := by
  induction parts with
  | nil => exact absurd rfl hne
  | cons p rest ih =>
    have hp : '/' ∉ p := h p (List.mem_cons_self ..)
    cases rest with
    | nil => simpa [joinSlash] using splitSlash_word p hp
    | cons q rest' =>
      have hrest : ∀ r ∈ q :: rest', '/' ∉ r := fun r hr => h r (List.mem_cons_of_mem _ hr)
      simp only [joinSlash]
      rw [splitSlash_append_slash p _ hp, ih (by simp) hrest]

/-! ## Slug, Lang, Route -/

structure Slug where
  segments : List Segment
  ne : segments ≠ []
deriving DecidableEq, Repr

namespace Slug

/-- Each part must be a valid `Segment`; `"a//b"` and `"/a"` are rejected. -/
def parse? (s : String) : Option Slug :=
  match (splitSlash s.toList).mapM (fun p => Segment.parse? (String.ofList p)) with
  | some segs => if h : segs ≠ [] then some ⟨segs, h⟩ else none
  | none => none

/-- Checked literal: `Slug.lit "news/zero-person-company"`. -/
def lit (s : String) (h : (parse? s).isSome = true := by decide) : Slug :=
  (parse? s).get h

def toString (sl : Slug) : String := String.ofList (joinSlash (sl.segments.map (·.s.toList)))

instance : ToString Slug := ⟨toString⟩

/-- The home page's slug: the single segment `index`. -/
def index : Slug := ⟨[Segment.lit "index"], by simp⟩

def isIndex (sl : Slug) : Bool := sl == index

/-- `parse? ∘ toString = some` — the slug's string form names exactly it. -/
theorem parse_toString (sl : Slug) : parse? sl.toString = some sl := by
  have hsplit : splitSlash (joinSlash (sl.segments.map (·.s.toList))) = sl.segments.map (·.s.toList) := by
    apply splitSlash_joinSlash
    · simpa using sl.ne
    · intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨a, _, rfl⟩ := hp
      exact a.no_slash
  have hmap : (sl.segments.map (·.s.toList)).mapM (fun p => Segment.parse? (String.ofList p)) = some sl.segments := by
    induction sl.segments with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
      have ha : Segment.parse? (String.ofList a.s.toList) = some a := by
        simp only [Segment.parse?]
        have : String.ofList a.s.toList = a.s := String.ofList_toList
        rw [this]
        simp [a.ok]
      rw [ha, ih]
      rfl
  simp only [parse?, toString, String.toList_ofList, hsplit, hmap]
  simp [sl.ne]

end Slug

/-- The product supports exactly two languages; `L` has exactly two fields.
    A site is bilingual by construction, not by configuration. -/
inductive Lang
  | ja
  | en
deriving DecidableEq, Repr, Inhabited

namespace Lang

def all : List Lang := [.ja, .en]

theorem mem_all (l : Lang) : l ∈ all := by cases l <;> decide

def code : Lang → String
  | .ja => "ja"
  | .en => "en"

instance : ToString Lang := ⟨code⟩

end Lang

structure Route where
  slug : Slug
  lang : Lang
deriving DecidableEq, Repr

namespace Route

/-- `about (en)` — how a route is named in every message. -/
instance : ToString Route := ⟨fun r => s!"{r.slug} ({r.lang})"⟩

/-- The directory segments of a route under default language `d`: a
    non-default language is a leading directory; the home slug contributes
    none. -/
def dirSegments (r : Route) (d : Lang) : List (List Char) :=
  (if r.lang = d then [] else [r.lang.code.toList]) ++
  (if r.slug.isIndex then [] else r.slug.segments.map (·.s.toList))

/-- Root-relative directory href: `/`, `/about/`, `/en/news/x/`. -/
def href (r : Route) (d : Lang) : String :=
  String.ofList ('/' :: joinDirs (r.dirSegments d))

/-- Output file: `index.html`, `about/index.html`, `en/news/x/index.html`. -/
def outputPath (r : Route) (d : Lang) : String :=
  String.ofList (joinDirs (r.dirSegments d) ++ "index.html".toList)

theorem dirSegments_no_slash (r : Route) (d : Lang) : ∀ p ∈ r.dirSegments d, '/' ∉ p := by
  intro p hp
  simp only [dirSegments, List.mem_append] at hp
  rcases hp with hp | hp
  · split at hp
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      cases r.lang <;> decide
  · split at hp
    · simp at hp
    · simp only [List.mem_map] at hp
      obtain ⟨a, _, rfl⟩ := hp
      exact a.no_slash

theorem dirSegments_no_dots (r : Route) (d : Lang) :
    ∀ p ∈ r.dirSegments d, p ≠ ['.'] ∧ p ≠ ['.', '.'] ∧ p ≠ [] := by
  intro p hp
  simp only [dirSegments, List.mem_append] at hp
  rcases hp with hp | hp
  · split at hp
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      cases r.lang <;> decide
  · split at hp
    · simp at hp
    · simp only [List.mem_map] at hp
      obtain ⟨a, _, rfl⟩ := hp
      refine ⟨?_, ?_, a.data_ne_nil⟩
      · intro h; exact a.no_dot (by simp [h])
      · intro h; exact a.no_dot (by simp [h])

end Route

/-! ## URL resolution — browser semantics + Cloudflare Pages serving rules

`resolveUrl origin source href` answers: when a visitor on the emitted file
`source` follows `href`, which emitted file will the host serve, and which
fragment must that file declare? `origin` is the site's own origin
(e.g. `https://nogoals.org`), so absolute same-origin URLs are internal.
References to other origins are `.external` (other gates own them);
references that cannot be resolved (`..` above the root, `a//b`) are
`.malformed` — a distinct failure, never silently external. -/

structure Target where
  /-- Files any one of which satisfies the request. This is the SHAPE the
      host tries (`/a/b` is served from `a/b/index.html` or `a/b.html`); the
      caller owns the inventory and decides whether one exists. -/
  candidates : List String
  fragment : Option String
deriving Repr, DecidableEq

inductive ResolveError
  | external
  | malformed (reason : String)
deriving Repr, DecidableEq

/-- Split at the first occurrence of `sep`. -/
def splitFirst (sep : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = sep then ([], some cs)
    else
      let (h, t) := splitFirst sep cs
      (c :: h, t)

/-- RFC 3986 dot-segment removal over an absolute segment list. `none` if
    `..` would climb above the root or a middle segment is empty (`a//b`). -/
def normalizeSegments : List (List Char) → List (List Char) → Option (List (List Char))
  | [], acc => some acc.reverse
  | p :: rest, acc =>
    if p = ['.'] then normalizeSegments rest acc
    else if p = ['.', '.'] then
      match acc with
      | [] => none
      | _ :: acc' => normalizeSegments rest acc'
    else if p = [] then none
    else normalizeSegments rest (p :: acc)

theorem normalizeSegments_clean (parts acc : List (List Char))
    (h : ∀ p ∈ parts, p ≠ ['.'] ∧ p ≠ ['.', '.'] ∧ p ≠ []) :
    normalizeSegments parts acc = some (acc.reverse ++ parts) := by
  induction parts generalizing acc with
  | nil => simp [normalizeSegments]
  | cons p rest ih =>
    obtain ⟨h1, h2, h3⟩ := h p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q ≠ ['.'] ∧ q ≠ ['.', '.'] ∧ q ≠ [] :=
      fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [normalizeSegments, h1, h2, h3, ↓reduceIte]
    rw [ih (p :: acc) hrest]
    simp

/-- `scheme://host` of an absolute `http(s)` URL; `none` for anything
    relative, root-relative, or another scheme. -/
def originOf? (url : String) : Option String :=
  if url.startsWith "https://" then
    some ("https://" ++ (url.drop "https://".length).takeWhile (· ≠ '/'))
  else if url.startsWith "http://" then
    some ("http://" ++ (url.drop "http://".length).takeWhile (· ≠ '/'))
  else none

/-- Does the path (as chars) look external: a scheme before any `/`, or a
    protocol-relative `//`? -/
def looksExternal (cs : List Char) : Bool :=
  match cs with
  | '/' :: '/' :: _ => true
  | _ => (cs.takeWhile (· ≠ '/')).contains ':'

/-- The directory part of an emitted file path, as segments. -/
def dirOf (file : List Char) : List (List Char) :=
  (splitSlash file).dropLast

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `%XX` → the ASCII character (non-ASCII escapes are left as written; ids
    are ASCII by type, so such a fragment can never match anyway). -/
def percentDecode : List Char → List Char
  | '%' :: a :: b :: rest =>
    match hexVal a, hexVal b with
    | some x, some y =>
      let n := x * 16 + y
      if n < 128 then Char.ofNat n :: percentDecode rest
      else '%' :: a :: b :: percentDecode rest
    | _, _ => '%' :: a :: b :: percentDecode rest
  | c :: rest => c :: percentDecode rest
  | [] => []

/-- The unreserved character a `%ab` escape denotes, if any (RFC 3986
    §2.3: letters, digits, `-` `.` `_` `~`). -/
def unreservedEscape (a b : Char) : Option Char :=
  match hexVal a, hexVal b with
  | some x, some y =>
    let n := x * 16 + y
    let d := Char.ofNat n
    if n < 128 && (d.isAlphanum || d == '-' || d == '.' || d == '_' || d == '~') then some d else none
  | _, _ => none

/-- RFC 3986 §6.2.2.2: decode only UNRESERVED escapes in a path
    (`%61` → `a`, `%2E` → `.`); `%2F` and the like stay encoded, because
    they are not separators. -/
def percentDecodeUnreserved : List Char → List Char
  | '%' :: a :: b :: rest =>
    match unreservedEscape a b with
    | some d => d :: percentDecodeUnreserved rest
    | none => '%' :: a :: b :: percentDecodeUnreserved rest
  | c :: rest => c :: percentDecodeUnreserved rest
  | [] => []

/-- Files that serve a normalized URL path. `dir = true` when the URL ended
    in `/`. A last segment with an extension is an exact file; an
    extensionless one is a pretty URL (`dir/index.html`, then `dir.html`). -/
def servedFiles (segs : List (List Char)) (dir : Bool) : List String :=
  match segs.getLast? with
  | none => [String.ofList "index.html".toList]
  | some last =>
    if dir then [String.ofList (joinDirs segs ++ "index.html".toList)]
    else if last.contains '.' then [String.ofList (joinSlash segs)]
    else
      [String.ofList (joinDirs segs ++ "index.html".toList),
       String.ofList (joinSlash segs ++ ".html".toList)]

/-- Resolve `href` as seen from emitted file `source` on site `origin`. -/
def resolveUrl (origin source href : String) : Except ResolveError Target :=
  let (pathAndQuery, frag) := splitFirst '#' href.toList
  let (path, _query) := splitFirst '?' pathAndQuery
  -- Absolute same-origin URL → root-relative. The origin must be followed
  -- by `/` or nothing (`https://x.test.evil` is NOT `https://x.test`); a
  -- bare origin means its root.
  let path :=
    if origin.toList ≠ [] ∧ origin.toList.isPrefixOf path then
      match path.drop origin.toList.length with
      | [] => ['/']
      | '/' :: rest => '/' :: rest
      | other => path.take origin.toList.length ++ other   -- a different host: leave it
    else path
  if looksExternal path then .error .external
  else
    let fragment := frag.map (fun f => String.ofList (percentDecode f))
    let path := percentDecodeUnreserved path
    if path.isEmpty then
      -- same-document reference
      .ok ⟨[source], fragment⟩
    else
      let absolute := path.head? = some '/'
      let raw := if absolute then path.tail else path
      let parts := splitSlash raw
      let dir := parts.getLast? = some []
      let parts := if dir then parts.dropLast else parts
      let base := if absolute then [] else dirOf source.toList
      match normalizeSegments (base ++ parts) [] with
      | none => .error (.malformed s!"'{href}' escapes the site root or has an empty segment")
      | some segs => .ok ⟨servedFiles segs dir, fragment⟩

theorem percentDecodeUnreserved_cons_ne (c : Char) (rest : List Char) (hc : c ≠ '%') :
    percentDecodeUnreserved (c :: rest) = c :: percentDecodeUnreserved rest := by
  match rest with
  | [] => simp [percentDecodeUnreserved]
  | [_] => simp [percentDecodeUnreserved]
  | _ :: _ :: _ => simp [percentDecodeUnreserved, hc]

theorem percentDecodeUnreserved_id (cs : List Char) (h : '%' ∉ cs) :
    percentDecodeUnreserved cs = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hc : c ≠ '%' := fun e => h (by simp [e])
    have hr : '%' ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    rw [percentDecodeUnreserved_cons_ne c rest hc, ih hr]

/-! ### The kernel's hrefs resolve to the kernel's files -/

theorem splitFirst_no_sep (sep : Char) (cs : List Char) (h : sep ∉ cs) :
    splitFirst sep cs = (cs, none) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hc : c ≠ sep := fun e => h (by simp [e])
    have hr : sep ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitFirst, hc, ih hr]

theorem href_data (r : Route) (d : Lang) :
    (r.href d).toList = '/' :: joinDirs (r.dirSegments d) := String.toList_ofList

theorem joinDirs_no_special (parts : List (List Char)) (c : Char) (hc : c ≠ '/')
    (h : ∀ p ∈ parts, c ∉ p) : c ∉ joinDirs parts := by
  induction parts with
  | nil => simp [joinDirs]
  | cons p rest ih =>
    intro hmem
    simp only [joinDirs, List.map_cons, List.flatten_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with (hmem | hmem) | hmem
    · exact h p (List.mem_cons_self ..) hmem
    · exact hc hmem
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hmem

theorem dirSegments_char_free (r : Route) (d : Lang) (c : Char)
    (hc : Segment.charOk c = false) (hcode : c ∉ "ja".toList ∧ c ∉ "en".toList) :
    ∀ p ∈ r.dirSegments d, c ∉ p := by
  intro p hp
  simp only [Route.dirSegments, List.mem_append] at hp
  rcases hp with hp | hp
  · split at hp
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      cases r.lang
      · exact hcode.1
      · exact hcode.2
  · split at hp
    · simp at hp
    · simp only [List.mem_map] at hp
      obtain ⟨a, _, rfl⟩ := hp
      intro hmem
      have h := a.ok
      simp only [Segment.valid, Bool.and_eq_true] at h
      have := (Segment.allOk_iff _).mp h.2 c hmem
      rw [hc] at this
      exact Bool.false_ne_true this

/-- A URL origin never begins with `/`, so a non-empty origin is never a
    prefix of a root-relative href. -/
theorem origin_not_prefix (origin rest : List Char)
    (hor : ∀ c, origin.head? = some c → c ≠ '/') :
    ¬ (origin ≠ [] ∧ origin.isPrefixOf ('/' :: rest) = true) := by
  rintro ⟨hne, hpre⟩
  cases origin with
  | nil => exact hne rfl
  | cons c cs =>
    have : c ≠ '/' := hor c rfl
    simp [List.isPrefixOf, this] at hpre

/-- **Route closure for the kernel**: the href the kernel emits for a route
    resolves — from any source page, on any real origin — to exactly that
    route's output file, with no fragment. -/
theorem resolve_href (origin source : String) (r : Route) (d : Lang)
    (hor : ∀ c, origin.toList.head? = some c → c ≠ '/') :
    resolveUrl origin source (r.href d) = .ok ⟨[r.outputPath d], none⟩ := by
  have hsegs := r.dirSegments_no_slash d
  have hdots := r.dirSegments_no_dots d
  have hhash : '#' ∉ (r.href d).toList := by
    rw [href_data]
    simp only [List.mem_cons, not_or]
    refine ⟨by decide, ?_⟩
    exact joinDirs_no_special _ _ (by decide)
      (dirSegments_char_free r d '#' (by decide) (by decide))
  have hq : '?' ∉ (r.href d).toList := by
    rw [href_data]
    simp only [List.mem_cons, not_or]
    refine ⟨by decide, ?_⟩
    exact joinDirs_no_special _ _ (by decide)
      (dirSegments_char_free r d '?' (by decide) (by decide))
  simp only [resolveUrl]
  rw [splitFirst_no_sep '#' _ hhash]
  simp only
  rw [splitFirst_no_sep '?' _ hq]
  simp only
  have hpre : ¬ (origin.toList ≠ [] ∧ origin.toList.isPrefixOf (r.href d).toList = true) := by
    rw [href_data]; exact origin_not_prefix _ _ hor
  rw [if_neg hpre]
  have hdec : percentDecodeUnreserved ('/' :: joinDirs (r.dirSegments d)) = '/' :: joinDirs (r.dirSegments d) := by
    have : '%' ∉ joinDirs (r.dirSegments d) :=
      joinDirs_no_special _ _ (by decide) (dirSegments_char_free r d '%' (by decide) (by decide))
    exact percentDecodeUnreserved_id _ (by simp [this])
  have hext : looksExternal (r.href d).toList = false := by
    rw [href_data]
    simp only [looksExternal]
    have hjoin : joinDirs (r.dirSegments d) ≠ [] → (joinDirs (r.dirSegments d)).head? ≠ some '/' := by
      intro _
      cases hd : r.dirSegments d with
      | nil => simp [joinDirs]
      | cons p rest =>
        have hp := hdots p (by simp [hd])
        have hps := hsegs p (by simp [hd])
        simp only [joinDirs, List.map_cons, List.flatten_cons]
        cases p with
        | nil => exact absurd rfl hp.2.2
        | cons c cs =>
          simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
          intro e; exact hps (by simp [e])
    split
    · rename_i h
      exfalso
      have : joinDirs (r.dirSegments d) ≠ [] := by
        intro e; rw [e] at h; simp at h
      have hh := hjoin this
      simp only [List.cons.injEq] at h
      rw [h.2] at hh
      simp at hh
    · simp only [List.takeWhile]
      simp
  rw [hext]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none, hdec, href_data, List.isEmpty_cons,
    List.head?_cons, List.tail_cons]
  rw [splitSlash_joinDirs _ hsegs]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, ↓reduceIte,
    List.dropLast_concat, List.nil_append, decide_true]
  rw [normalizeSegments_clean _ _ hdots]
  simp only [List.reverse_nil, List.nil_append, servedFiles]
  cases hl : (r.dirSegments d).getLast? with
  | none =>
    -- no segments at all: the home page of the default language
    have : r.dirSegments d = [] := List.getLast?_eq_none_iff.mp hl
    simp [this, Route.outputPath, joinDirs]
  | some last =>
    simp only [↓reduceIte]
    rfl

/-! ## Asset paths -/

structure AssetPath where
  segments : List FileSegment
  ne : segments ≠ []
deriving DecidableEq, Repr

namespace AssetPath

def parse? (s : String) : Option AssetPath :=
  match (splitSlash s.toList).mapM (fun p => FileSegment.parse? (String.ofList p)) with
  | some segs => if h : segs ≠ [] then some ⟨segs, h⟩ else none
  | none => none

/-- Checked literal: `AssetPath.lit "assets/images/logo.png"`. -/
def lit (s : String) (h : (parse? s).isSome = true := by decide) : AssetPath :=
  (parse? s).get h

def toString (p : AssetPath) : String := String.ofList (joinSlash (p.segments.map (·.s.toList)))

instance : ToString AssetPath := ⟨toString⟩

/-- Root-relative href for an asset: `/assets/images/logo.png`. -/
def href (p : AssetPath) : String := "/" ++ p.toString

theorem parse_toString (p : AssetPath) : parse? p.toString = some p := by
  have hsplit : splitSlash (joinSlash (p.segments.map (·.s.toList))) = p.segments.map (·.s.toList) := by
    apply splitSlash_joinSlash
    · simpa using p.ne
    · intro q hq
      simp only [List.mem_map] at hq
      obtain ⟨a, _, rfl⟩ := hq
      exact a.no_slash
  have hmap : (p.segments.map (·.s.toList)).mapM (fun q => FileSegment.parse? (String.ofList q)) = some p.segments := by
    induction p.segments with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
      have ha : FileSegment.parse? (String.ofList a.s.toList) = some a := by
        simp only [FileSegment.parse?]
        have : String.ofList a.s.toList = a.s := String.ofList_toList
        rw [this]
        simp [a.ok]
      rw [ha, ih]
      rfl
  simp only [parse?, toString, String.toList_ofList, hsplit, hmap]
  simp [p.ne]

theorem toString_injective {a b : AssetPath} (h : a.toString = b.toString) : a = b := by
  have := parse_toString a
  rw [h, parse_toString b] at this
  exact (Option.some.inj this).symm

end AssetPath

end NoGoals
