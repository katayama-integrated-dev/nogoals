import NoGoals
import Site

open NoGoalsSite
open NoGoals.Build (SiteBuild)

/-- Everything specific to this site; `NoGoals.Build.run` owns the rest. -/
def spec : SiteBuild :=
  { bridge := Verified.bridge
    -- This site lives inside the NoGoals checkout.
    nogoalsDir := ".." }

def main (args : List String) : IO UInt32 := NoGoals.Build.run spec args
