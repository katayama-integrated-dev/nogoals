import NoGoals.DSL

namespace NoGoalsSite

open NoGoals (AssetPath)
open NoGoals.DSL

def assets : List AssetDef := [
  { path := AssetPath.lit "assets/styles/site.css", kind := .css },
  { path := AssetPath.lit "assets/images/logo.png", kind := .image },
  { path := AssetPath.lit "assets/images/hero.jpg", kind := .image },
  { path := AssetPath.lit "assets/images/card.jpg", kind := .image }
]

end NoGoalsSite
