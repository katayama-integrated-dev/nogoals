import NoGoals.DSL

namespace MySite

open NoGoals (Segment)
open NoGoals.DSL

/-- Static pages as a closed enumeration: a link names a constructor, so a
    link to an unregistered page is unrepresentable. Add a constructor here
    and the compiler walks you through every match that must grow. -/
inductive PageId
  | index
  | about
deriving DecidableEq, Repr, Inhabited

def PageId.all : List PageId := [.index, .about]

theorem PageId.all_complete : ∀ p : PageId, p ∈ PageId.all := by
  intro p; cases p <;> decide

/-- The site's presentational vocabulary. Extend when a page needs a new
    shape, and render the new constructor in `Render.lean`. -/
inductive Block
  | heading (text : L)
  | prose (paragraphs : List L)
  | cta (target : PageId) (label : L)
  /-- A section with an optional anchor id and children. -/
  | section (id : Option Segment) (children : List Block)

end MySite
