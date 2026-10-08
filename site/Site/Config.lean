import NoGoals.DSL

namespace NoGoalsSite

open NoGoals (AssetPath)
open NoGoals.DSL

/-- The product's name, written once: every sentence on the site that names
    it interpolates this. -/
def product : String := "NoGoals"

/-- English is the unprefixed language (the audience is wherever Lean and
    static sites are); Japanese lives under `/ja/`. -/
def config : SiteConfig := {
  name := L.same product
  copyrightHolder := some ⟨"片山総合開発合同会社", "Katayama Integrated Development LLC"⟩
  canonicalBaseUrl := "https://nogoals.org"
  defaultLang := .en
  logoPath := AssetPath.lit "assets/images/logo.png"
  langNames := ⟨"日本語", "English"⟩
}

end NoGoalsSite
