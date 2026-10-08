import Site.Blocks
import Site.Config

namespace NoGoalsSite.Bodies

def start : List Block := [
  .section none ⟨"最初のサイトをビルドする", "Build your first site"⟩ [
    .steps [
      { title := ⟨"用意するもの", "What you need"⟩
        text :=
          ⟨s!"elan（Lean のバージョンは {product} が固定します）、Node（22 系なら 22.22 以上、または 24.8 以上）、jq。初回のビルドは Mathlib を取得するので時間がかかります。",
           s!"elan (the Lean version is pinned by {product}), Node (22.22 or newer within 22.x, or 24.8 or newer), and jq. The first build fetches Mathlib and takes a while."⟩ },
      { title := ⟨"ひな形をコピーする", "Copy the scaffold"⟩
        text :=
          ⟨s!"{product} をチェックアウトしたディレクトリの隣に、最小構成のサイトを置きます。このサイトは、そのままで監査に合格します。",
           s!"Place the minimal site next to a checkout of {product}. It passes the audit without modification."⟩
        code := some
          { caption := NoGoals.DSL.L.same "Shell"
            lines := [
              ⟨.plain, "cp -R nogoals/skills/nogoals/assets my-site"⟩,
              ⟨.plain, "cd my-site && npm ci"⟩] } },
      { title := ⟨"最初の監査を実行する", "Run the first audit"⟩
        text :=
          ⟨"新しいサイトには公開済みの URL がまだないので、最初の一回だけパーマリンクのベースラインを作ります。ベースラインがすでにあるとき、このフラグは警告を出すだけで、ベースラインには触れません。--offline は外部リンクのリンク切れチェックだけを省きます。",
           "A new site has no published URLs yet, so the first run bootstraps the permalink baseline. When a baseline already exists the flag prints a warning and leaves it alone. --offline skips only the external-link liveness check."⟩
        code := some
          { caption := NoGoals.DSL.L.same "Shell"
            lines := [
              ⟨.plain, "./scripts/build.sh --audit --offline --update-baseline"⟩,
              ⟨.good, "✓ AUDIT PASSED — every publisher gate is green."⟩] } },
      { title := ⟨"ページを追加する", "Add a page"⟩
        text :=
          ⟨"PageId にコンストラクタを一つ追加します。コンパイラは、スラッグ、本文、ページ定義の match 式で分岐の追加が必要な箇所をすべて報告します。必要な分岐が一つでも欠けていると、ビルドは失敗します。",
           "Add one constructor to PageId. The compiler reports every match expression that needs an additional branch for the slug, body or page definition. The build fails if any required branch is missing."⟩
        code := some
          { caption := NoGoals.DSL.L.same "Site/Blocks.lean"
            lines := [
              ⟨.plain, "inductive PageId"⟩,
              ⟨.plain, "  | index"⟩,
              ⟨.plain, "  | about"⟩,
              ⟨.good, "  | pricing"⟩] } },
      { title := ⟨"エージェントを使う", "Use an agent"⟩
        text :=
          ⟨s!"{product} には、モデルの説明、ひな形、ビルドが失敗したときの出力の読み方をまとめたエージェント用のスキルが付属しています。スキルへのリンクを作成してから、エージェントに「料金ページを追加して」と依頼してください。",
           s!"{product} includes an agent skill with an explanation of the model, a scaffold and instructions for interpreting build failures. Link the skill, then ask the agent to add a pricing page."⟩
        code := some
          { caption := NoGoals.DSL.L.same "Claude Code"
            lines := [
              ⟨.plain, "mkdir -p ~/.claude/skills"⟩,
              ⟨.plain, "ln -s \"$PWD/../nogoals/skills/nogoals\" ~/.claude/skills/nogoals"⟩] } }]
  ],
  .section (some (NoGoals.Segment.lit "limits")) ⟨"制限事項", "Limitations"⟩ [
    .cards [
      ⟨⟨"Markdown の入力機能はありません", "No Markdown front-end"⟩,
       ⟨"内容は Lean のデータとして表現され、証明の基礎になります。長い文章は、サイト側のスクリプトを使ってファイルから Lean のデータに変換できます。",
        "Content is represented as Lean data, which forms the basis of the proofs. A site-owned script can generate Lean data from files containing long prose."⟩⟩,
      ⟨⟨"対応言語は日本語と英語のみ", "Japanese and English only"⟩,
       ⟨"文言の型には ja と en の二つのフィールドがあります。言語構成を変えるには、ジェネレーターの変更が必要です。",
        "The text type has exactly two fields, ja and en. Supporting a different set of languages requires changing the generator."⟩⟩,
      ⟨⟨"Cloudflare Pages を前提とするホスティングモデル", "Cloudflare Pages hosting model"⟩,
       ⟨"このモデルは、/x/ で x/index.html を配信することや、_headers と _redirects の扱いについて、Cloudflare Pages の仕様を前提にしています。成果物はほかのホストでも配信できますが、リンク解決のモデルは Pages のものです。",
        "The model follows Cloudflare Pages conventions for serving x/index.html at /x/ and for _headers and _redirects. Other hosts can serve the artifact, but link resolution is modelled on Pages."⟩⟩,
      ⟨⟨"デザインは形式化の対象外", "Design is not formalized"⟩,
       ⟨"検証の対象は構造です。グラデーションやグリッドは形式化の対象に含まれません。",
        "Verification covers structure. Gradients and grids are not formalized."⟩⟩]
  ]
]

end NoGoalsSite.Bodies
