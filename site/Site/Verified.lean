import NoGoals.Bridge
import Site.Pages

namespace NoGoalsSite.Verified

theorem assets_unique : NoGoals.Bridge.AssetsUnique site := by native_decide
theorem refine_ok : NoGoals.Bridge.RefineOk site assets_unique := by native_decide

def bridge : NoGoals.Bridge := ⟨site, assets_unique, refine_ok⟩

end NoGoalsSite.Verified
