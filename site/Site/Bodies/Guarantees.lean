import NoGoals.Build
import Site.Blocks
import Site.Config

namespace NoGoalsSite.Bodies

open NoGoals.Compile (Guarantee typeLevelGuarantees theoremGuarantees securityGuarantees)

/-- A built-in guarantee definition, as NoGoals's code states it. -/
def ofGuarantee (g : Guarantee) : Entry :=
  { name := g.name, description := g.description
    mechanism := match g.status with | .enforced m => m | _ => g.id
    scope := g.scope }

/-- A gate, as the placeholder entry NoGoals itself writes before the gate runs:
    its scope and id come from NoGoals, not from this page. -/
def ofGate (g : NoGoals.Build.GateDef) : Entry := ofGuarantee (g.skipped "")

def guarantees : List Block := [
  .section none ⟨"一覧の出典と保証の対象範囲", "Sources and scope"⟩ [
    .prose [
      ⟨s!"このページでは、ビルド時に {product} に組み込まれた保証とゲートの定義をコードから直接読み込むため、一覧は実装と一致します。名前と説明は、実装中の英語をそのまま掲載しています。",
       s!"This page reads {product}'s built-in guarantee and gate definitions directly from the code at build time, keeping the list consistent with the implementation."⟩,
      ⟨"各ビルドのレポートは、この一覧の定義をもとに作成されます。サイトが証明した定理をそのサイトについての記述に置き換え、実行されたゲートの結果を記録します。このビルドの検証ページに、その根拠を掲載しています。",
       "A build's report uses these definitions. It restates theorems proved by the site as claims about that site and records the results of the gates that ran. The verification page contains the evidence for this build."⟩,
      ⟨"右のラベルは、各保証の対象範囲を示します。kernel は検証済みレンダラーを通った内容、chrome は全ページを包む型つきの枠、artifact はビルドが出力したファイルそのものを指します。",
       "The label on the right identifies each guarantee's scope. kernel applies to content routed through the verified renderer. chrome applies to the typed frame around every page. artifact applies to the files emitted by the build."⟩],
    .verificationLink ⟨"このサイトの検証結果", "Verification results for this site"⟩
  ],
  .section (some (NoGoals.Segment.lit "types")) ⟨"型による保証", "Guarantees enforced by types"⟩ [
    .entries (typeLevelGuarantees.map ofGuarantee)
  ],
  .section (some (NoGoals.Segment.lit "theorems")) ⟨"定理による保証", "Guarantees proved by theorems"⟩ [
    .entries (theoremGuarantees.map ofGuarantee)
  ],
  .section (some (NoGoals.Segment.lit "security")) ⟨"セキュリティ", "Security"⟩ [
    .prose [
      ⟨"この節では、エスケープの定理と型つきの配信ポリシーを示します。各項目に根拠を記載しています。",
       "This section lists escaping theorems and a typed delivery policy. Each entry states its basis."⟩],
    .entries (securityGuarantees.map ofGuarantee)
  ],
  .section (some (NoGoals.Segment.lit "gates")) ⟨"ビルド時に検査すること", "What is checked at build time"⟩ [
    .prose [
      ⟨"ゲートは --audit を指定した場合に実行され、出力先に反映する前のビルド成果物と、サイトで宣言したデータを検査します。HTML のゲートは、出力されたファイルをパーサーで読みます。サイトは独自のゲートを追加できます。ゲートが一つでも失敗すると、ファイルは出力ディレクトリにコピーされません。",
       "Gates run under --audit and check the candidate artifact and the data the site declared. The HTML gates read the emitted files through a parser. A site can add its own. If any gate fails, no files are copied to the output directory."⟩],
    .entries (NoGoals.Build.builtinGates.map ofGate),
    .cta .start PageId.start.title
  ]
]

end NoGoalsSite.Bodies
