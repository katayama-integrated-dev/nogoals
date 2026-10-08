import Site.Config
import Site.Assets
import Site.Render
import Site.Bodies.Index
import Site.Bodies.About

namespace MySite

open NoGoals (AssetPath)
open NoGoals.DSL

/-- Static page bodies — one arm per constructor. -/
def body : PageId → List Block
  | .index => Bodies.index
  | .about => Bodies.about

/-- Every static page's definition. `heroClass` names a stylesheet rule
    (the CSS-contract gate checks it exists). -/
def staticPage (id : PageId) : PageDef :=
  let page (title description : L) : PageDef :=
    { slug := Render.slug id, title, description
      socialImage := AssetPath.lit "assets/images/hero.png", heroClass := "hero-img-default"
      body := fun lang => Render.renderBody lang (body id) }
  match id with
  | .index => page ⟨"マイサイト", "My Site"⟩ ⟨"NoGoals で作ったサイト", "A site built with NoGoals"⟩
  | .about => page ⟨"私たちについて", "About"⟩ ⟨"チームの紹介", "Who we are"⟩

def pages : List PageDef := PageId.all.map staticPage

def navigation : Navigation :=
  { main := [.page (Render.slug .about) ⟨"私たちについて", "About"⟩] }

def site : Site := { config, pages, navigation, assets }

end MySite
