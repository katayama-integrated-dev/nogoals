import NoGoals.DSL

namespace MySite

open NoGoals (AssetPath)
open NoGoals.DSL

/-- Names, origin, default language, logo. Every absolute URL of the site
    (sitemap, canonical, hreflang, OpenGraph, feeds) derives from
    `canonicalBaseUrl`, so it is the one place the origin is written. -/
def config : SiteConfig := {
  name := ⟨"マイサイト", "My Site"⟩
  canonicalBaseUrl := "https://www.example.com"
  defaultLang := .ja
  logoPath := AssetPath.lit "assets/images/logo.png"
}

end MySite
