import NoGoals.DSL

namespace MySite

open NoGoals (AssetPath)
open NoGoals.DSL

/-- Every file the pages may reference. Stylesheets load in this order;
    scripts are deferred. A reference to an undeclared asset fails the build. -/
def assets : List AssetDef := [
  { path := AssetPath.lit "assets/styles/site.css", kind := .css },
  { path := AssetPath.lit "assets/images/logo.png", kind := .image },
  { path := AssetPath.lit "assets/images/hero.png", kind := .image }
]

end MySite
