import NoGoals.IR.Atoms

namespace NoGoals

inductive AssetKind | image | css | js | font | other
deriving DecidableEq, Repr

/-- An asset palette: `n` files, each with a validated path (which IS its
    output location — `assets/images/logo.png`), a kind, and its bytes.
    Distinct assets have distinct paths by the `unique` field, so
    `path_injective` needs no string surgery. -/
structure Assets (n : Nat) where
  name   : Fin n → AssetPath
  kind   : Fin n → AssetKind
  bytes  : Fin n → ByteArray
  unique : ∀ {i j}, name i = name j → i = j

/-- Output path of an asset. -/
def Assets.path {n : Nat} (A : Assets n) (i : Fin n) : Path :=
  ⟨(A.name i).toString⟩

def AssetId (n : Nat) (k : AssetKind) (A : Assets n) := { i : Fin n // A.kind i = k }

/-- Asset paths are injective: equal paths imply equal indices. -/
theorem Assets.path_injective {n : Nat} (A : Assets n) {i j : Fin n}
    (h : A.path i = A.path j) : i = j := by
  unfold Assets.path at h
  simp only [Path.mk.injEq] at h
  exact A.unique (AssetPath.toString_injective h)

end NoGoals
