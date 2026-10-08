import NoGoals
import Site.Pages

namespace MySite.Verified

/-- Asset paths are pairwise distinct — decided on the concrete list. -/
theorem assets_unique : NoGoals.Bridge.AssetsUnique site := by native_decide

/-- NoGoals accepts the site: routes unique, disjoint from assets, both languages
    complete, anchors emitted. A failure here names the route. -/
theorem refine_ok : NoGoals.Bridge.RefineOk site assets_unique := by native_decide

def bridge : NoGoals.Bridge := ⟨site, assets_unique, refine_ok⟩

end MySite.Verified
