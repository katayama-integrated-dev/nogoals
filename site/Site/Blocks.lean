import NoGoals.DSL
import NoGoals.Compile.Evidence

namespace NoGoalsSite

open NoGoals (Segment)
open NoGoals.DSL

/-- Pages as a closed enumeration: a link names a constructor, so a link to
    a page that does not exist cannot be written. -/
inductive PageId
  | index
  | guarantees
  | start
deriving DecidableEq, Repr, Inhabited

def PageId.all : List PageId := [.index, .guarantees, .start]

/-- A page's title: its `<h1>`, its navigation label, and the label of a
    link that simply goes there. Said once. -/
def PageId.title : PageId → L
  | .index => ⟨"壊れたサイトは、ビルドできない。", "Broken websites don't build."⟩
  | .guarantees => ⟨"何を検査するか", "What is checked"⟩
  | .start => ⟨"はじめる", "Get started"⟩

theorem PageId.all_complete : ∀ p : PageId, p ∈ PageId.all := by
  intro p; cases p <;> decide

/-- How a line of code or terminal output reads. -/
inductive Tone | plain | comment | good | bad

/-- Code is code: one string, the same in both languages. -/
structure CodeLine where
  tone : Tone
  text : String

/-- A captioned block of code or terminal output. -/
structure Code where
  caption : L
  lines : List CodeLine

structure Card where
  title : L
  text : L

/-- A number the build computed, and what it counts. -/
structure Fact where
  value : String
  label : L

/-- One guarantee or gate definition, as NoGoals's code states it (in English,
    said once — the verification report does the same). -/
structure Entry where
  name : String
  description : String
  /-- What stands behind it: the type, the theorem, or the gate's id. -/
  mechanism : String
  scope : NoGoals.Compile.GuaranteeScope

structure Step where
  title : L
  text : L
  code : Option Code := none

/-- The site's presentational vocabulary. -/
inductive Block
  | section (id : Option Segment) (heading : L) (children : List Block)
  | prose (paragraphs : List L)
  | code (c : Code)
  | compare (left right : Code)
  | cards (items : List Card)
  | facts (items : List Fact) (source : L)
  | entries (items : List Entry)
  | steps (items : List Step)
  /-- The link to `/verification/`, the one page NoGoals itself emits. -/
  | verificationLink (note : L)
  | cta (target : PageId) (label : L)

end NoGoalsSite
