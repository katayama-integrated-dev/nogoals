import NoGoals
import Site

open MySite
open NoGoals.Build (SiteBuild)

/-- Everything specific to this site; `NoGoals.Build.run` owns the rest. -/
def spec : SiteBuild :=
  { bridge := Verified.bridge
    chrome := Render.siteChrome
    -- NoGoals is a path dependency checked out next to this site.
    nogoalsDir := "../nogoals" }

def main (args : List String) : IO UInt32 := NoGoals.Build.run spec args
