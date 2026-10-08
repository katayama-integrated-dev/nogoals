import NoGoals.IR.Route

namespace NoGoals

structure NonEmptyStr where
  s  : String
  ne : s ≠ ""
deriving DecidableEq

/-- An output file path (`about/index.html`, `assets/images/logo.png`) or the
    path component of an external URL. Pages derive theirs from `Route`,
    assets from `AssetPath`; this wrapper is what the build plan compares. -/
structure Path where toString : String deriving DecidableEq, Repr

namespace Url
inductive Safe
| https (host : String) (path : Path)
| http  (host : String) (path : Path)  -- allow by policy toggle only
| data  (mediatype : String) (bytesB64 : String)
deriving DecidableEq, Repr
end Url

end NoGoals
