import NoGoals.IR.Atoms

namespace NoGoals

inductive LinkRef
| internal (href : String)      -- "/about#team", "about", "#team"
| external (u : Url.Safe)
deriving Repr, DecidableEq

inductive InlineR
| text (s : String)
| code (s : String)
| a    (ref : LinkRef) (label : NonEmptyStr)

inductive Display where | xs | sm | md | lg | xl

inductive HLevel  where | h1 | h2 | h3 | h4 | h5 | h6

structure HeadingR where
  level   : HLevel
  display : Display
  text    : NonEmptyStr

inductive BlockR
| p        (xs : List InlineR)
| ul       (items : List (List InlineR))
| heading  (h : HeadingR)
| img      (src : String) (alt : NonEmptyStr)
| section  (title? : Option NonEmptyStr) (children : List BlockR)  -- OutlineRoot

/-- An unrefined page: its route is already typed (a `Route` cannot name an
    unsafe path); its body's links are still strings to be resolved. -/
structure PageRaw where
  route : Route
  title : String
  body  : List BlockR

structure SiteRaw where
  defaultLang : Lang
  pages : List PageRaw

end NoGoals
