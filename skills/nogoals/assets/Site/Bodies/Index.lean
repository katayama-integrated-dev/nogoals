import Site.Blocks

namespace MySite.Bodies


def index : List Block := [
  .section none [
    .heading ⟨"ようこそ", "Welcome"⟩,
    .prose [⟨"このサイトは NoGoals で構築されています。", "This site is built with NoGoals."⟩],
    .cta .about ⟨"私たちについて", "About us"⟩
  ]
]

end MySite.Bodies
