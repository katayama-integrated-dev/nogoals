import Site.Blocks

namespace MySite.Bodies

open NoGoals (Segment)

def about : List Block := [
  .section (some (Segment.lit "team")) [
    .heading ⟨"チーム", "Team"⟩,
    .prose [⟨"小さなチームです。", "We are a small team."⟩]
  ]
]

end MySite.Bodies
