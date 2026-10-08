import NoGoals.Build
import Site.Blocks
import Site.Config
import Site.Counts

namespace NoGoalsSite.Bodies

def index : List Block := [
  .section none ⟨"定理・sorry・ビルド時ゲートの数", "Theorem, sorry and build-gate counts"⟩ [
    .facts [
      ⟨toString Counts.theorems, ⟨"定理", "theorems"⟩⟩,
      ⟨toString Counts.sorries, ⟨"sorry（未証明の穴）", "sorries"⟩⟩,
      ⟨toString NoGoals.Build.builtinGates.length, ⟨"ビルド時ゲート", "build gates"⟩⟩]
      ⟨"定理と sorry の数は verify.sh が集計します。ソースコードから集計した値と記録済みの値が一致しなければ、検証は失敗します。ゲートの数はこのページをビルドしたコードから読んでいます。これらの数値はすべて自動で取得しています。",
       "Theorems and sorries are counted by verify.sh, which fails on drift. The gate count is read from the code that built this page. All of these counts are generated automatically."⟩
  ],
  .section (some (NoGoals.Segment.lit "how")) ⟨"仕組み", "How it works"⟩ [
    .prose [
      ⟨"多くの静的サイトジェネレーターでは、リンク先や画像の参照先を文字列で指定します。任意の文字列を指定できるため、入力ミスがあってもそのまま受け入れられます。",
       "Most static site generators hold links and images as strings. A string can point anywhere, and nothing stops a typo."⟩,
      ⟨s!"{product} は Lean 4 で書かれています。各サイトでは、ページを列挙型として定義します。ひな形にはこの型が含まれています。リンク先には、その型のコンストラクタを指定します。存在しないページへのリンクは、コンパイル時にエラーになります。",
       s!"{product} is written in Lean 4. Each site defines a closed type for its pages, and the scaffold includes one. Links name constructors of this type. A link to a nonexistent page causes a compile error."⟩,
      ⟨"監査時には、リンク検査のゲートが、手書きの HTML を含む出力ファイル内のすべての href を解決します。",
       "During an audit, the link gate resolves every href in the emitted files, including hand-written HTML."⟩],
    .compare
      { caption := ⟨"文字列による参照", "String-based references"⟩
        lines := [
          ⟨.plain, "href : String"⟩,
          ⟨.comment, "-- \"/about\""⟩,
          ⟨.bad, "-- \"/prodcuts\"             a typo, and it ships"⟩,
          ⟨.bad, "-- \"javascript:alert(1)\"   ships too"⟩] }
      { caption := ⟨"型つきの値", "Typed values"⟩
        lines := [
          ⟨.plain, "target : PageId     -- a page that exists"⟩,
          ⟨.plain, "src    : AssetPath  -- path syntax checked at the literal"⟩,
          ⟨.plain, "title  : L          -- a Japanese AND an English field"⟩,
          ⟨.plain, "date   : IsoDate    -- a real calendar date"⟩,
          ⟨.good, "-- a wrong value is a compile error, with a line number"⟩] }
  ],
  .section (some (NoGoals.Segment.lit "methods")) ⟨"検証方法", "Verification methods"⟩ [
    .cards [
      ⟨⟨"型による保証", "Guarantees enforced by types"⟩,
       ⟨"不正な状態を表現できません。リンク先には、サイトのページ型のコンストラクタを指定します。スラッグ、アセットのパス、日付は、コンパイル時に書式を検査されるリテラルです。掲載する文言は日本語と英語のフィールドを持つレコードなので、一方のフィールドを省略するとコンパイルが通りません。",
        "The types prevent invalid states from being represented. A link names a constructor of the site's page type. Slugs, asset paths and dates are literals whose syntax is checked at compile time. Editorial text is a record with a Japanese and an English field, so neither can be left out."⟩⟩,
      ⟨⟨"定理による保証", "Guarantees proved by theorems"⟩,
       ⟨"証明は Lean のカーネルで検査されます。ジェネレーターが受け入れるどのサイトでも、出力パスは衝突せず、すべてのページが出力され、すべてのページに日本語版と英語版が存在します。検証済みレンダラーが生成するリンクは、出力されたファイルへの参照として解決されます。",
        "Lean's kernel checks the proofs. For every site the generator accepts, no two outputs share a path, every page is emitted, and every page exists in both languages. Inside the verified renderer, an emitted link resolves to an emitted file."⟩⟩,
      ⟨⟨"ビルド時の検査", "Build-time checks"⟩,
       ⟨"--audit を指定すると、ブラウザと同じ HTML の解析規則に従うパーサーが出力ファイルを読みます。すべてのリンクとアセット参照が解決するか、ページが配信時の CSP に従っているか、canonical と hreflang がルートと一致するかを検査します。HTML の妥当性と、公開済みのすべての URL が引き続き有効か、リダイレクトされているかも検査します。ゲートが一つでも失敗すると、ファイルは出力ディレクトリにコピーされません。",
        "With --audit, a parser that follows browsers' HTML rules reads the emitted files. The audit checks that every link and asset reference resolves, that pages comply with the delivered CSP, and that canonical and hreflang match the routes. It also checks HTML validity and whether every published URL is still live or redirected. If any gate fails, no files are copied to the output directory."⟩⟩],
    .prose [
      ⟨"レポートは、それぞれの主張がどの区分に属するかを示します。監査なしのビルドではゲートは走らず、レポートにはそのとおり「未実行」と出ます。実行されなかった検査が「合格」と表示されることはありません。",
       "The report says which tier each claim belongs to. A build without --audit runs no gates, and its report says so: a check that did not run is shown as skipped, never as passed."⟩],
    .cta .guarantees ⟨"検査項目の一覧を見る", "See the full list of checks"⟩
  ],
  .section (some (NoGoals.Segment.lit "failure")) ⟨"ビルドが失敗したとき", "When a build fails"⟩ [
    .prose [
      ⟨"ページの URL を変えて、手書きの HTML に古い URL へのリンクが一つ残ったとします。",
       "Say a page's URL is changed and one hand-written link to the old URL is left behind."⟩],
    .code
      { caption := ⟨"監査つきビルドの出力（例）", "Output of an audited build (example)"⟩
        lines := [
          ⟨.plain, "$ ./scripts/build.sh --audit"⟩,
          ⟨.comment, "  …"⟩,
          ⟨.bad, "  ✗ links: every internal reference on 12 pages resolves:"⟩,
          ⟨.bad, "      pricing/index.html: <a href=\"/plans/\">: no emitted file at plans/index.html"⟩,
          ⟨.good, "  ✓ seo: canonical/hreflang/og on 12 route pages"⟩,
          ⟨.comment, "  …"⟩,
          ⟨.bad, "  ✗ permalinks: all 31 obligations live or redirected (permalinks_sound applies); _redirects rendered from the same map:"⟩,
          ⟨.bad, "      previously published URL would 404: plans/index.html (add a redirect or restore the page)"⟩,
          ⟨.plain, ""⟩,
          ⟨.bad, "✗ AUDIT FAILED — violations above; the previous build stays in place."⟩,
          ⟨.comment, "  …"⟩,
          ⟨.bad, "✗ BUILD REJECTED: a gate failed. build/ is UNTOUCHED (last green build)."⟩] },
    .prose [
      ⟨"直前に成功したビルドはそのまま残ります。失敗したビルド成果物は隔離され、検証記録（receipt）には失敗したゲートが記録されます。この記録は機械可読なので、デプロイ用スクリプトでは、完全な監査に合格した記録だけを受け入れるようにできます。",
       "The previous successful build remains in place. The failed candidate is kept separate, and its receipt records the gate that failed. The receipt is machine-readable, so a deployment script can reject any receipt that does not record a successful full audit."⟩]
  ],
  .section (some (NoGoals.Segment.lit "results")) ⟨"このサイトの検証結果", "This site's verification results"⟩ [
    .prose [
      ⟨s!"このサイトは {product} でビルドされています。フッターのバッジは、このビルドの検証ページへのリンクです。",
       s!"This site is built with {product}. The badge in the footer links to this build's verification page."⟩],
    .verificationLink ⟨"保証の一覧、区分、根拠となる定理", "every guarantee, its tier, and the theorem behind it"⟩,
    .cta .start PageId.start.title
  ]
]

end NoGoalsSite.Bodies
