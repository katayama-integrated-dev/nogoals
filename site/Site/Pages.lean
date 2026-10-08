import Site.Config
import Site.Assets
import Site.Render
import Site.Bodies.Index
import Site.Bodies.Guarantees
import Site.Bodies.Start

namespace NoGoalsSite

open NoGoals (AssetPath)
open NoGoals.DSL

def body : PageId → List Block
  | .index => Bodies.index
  | .guarantees => Bodies.guarantees
  | .start => Bodies.start

def staticPage (id : PageId) : PageDef :=
  let page (description lead : L) (heroClass : String) (titleTag : Option L := none) : PageDef :=
    { slug := Render.slug id, title := id.title, titleTag, description, heroLead := .text lead
      socialImage := AssetPath.lit "assets/images/card.jpg", heroClass
      body := fun lang => Render.renderBody lang (body id) }
  match id with
  | .index => page
      ⟨s!"{product} は Lean 4 で書かれた静的サイトジェネレーターです。型と証明により、ルートの形式が正しいこと、出力パスの一意性、すべてのページに日本語版と英語版が存在することを保証します。監査では、出力ファイルのリンク、CSP、SEO、公開済み URL を検査します。監査に失敗した場合、出力ディレクトリは変更されません。",
       s!"{product} is a static site generator written in Lean 4. Types and proofs guarantee routes, output paths and bilingual completeness. An audit checks links, CSP, SEO and published URLs in the emitted files. If the audit fails, the output directory remains unchanged."⟩
      ⟨s!"{product} は Lean 4 で書かれた静的サイトジェネレーターです。型と証明により、ルートの形式が正しいこと、出力パスの一意性、すべてのページに日本語版と英語版が存在することを保証します。監査では、出力ファイルのリンク、CSP、SEO、公開済み URL を検査します。監査に失敗した場合、出力ディレクトリは変更されません。",
       s!"{product} is a static site generator written in Lean 4. Types and proofs guarantee routes, output paths and bilingual completeness. An audit checks links, CSP, SEO and published URLs in the emitted files. If the audit fails, the output directory remains unchanged."⟩
      "hero-home"
      (some ⟨s!"{product} — 検証つき静的サイトジェネレーター", s!"{product} — a verified static site generator"⟩)
  | .guarantees => page
      ⟨s!"このページでは、{product} が型で保証すること、定理で証明すること、ビルド時に検査することを一覧にしています。定義はコードから直接読み込んでいます。",
       s!"This page lists {product}'s type-enforced guarantees, theorem-proved guarantees and build-time checks. The definitions are read directly from the code."⟩
      ⟨"各保証とビルド時の検査を、それぞれの根拠とともに掲載しています。", "Each guarantee and build-time check is listed with its basis."⟩
      "hero-plain"
  | .start => page
      ⟨s!"ひな形をコピーして最初の監査に合格するまでの手順と、{product} の制限を説明します。",
       s!"This guide covers copying the scaffold, running the first successful audit and understanding {product}'s limitations."⟩
      ⟨"ひな形は、そのままで監査に合格します。", "The scaffold passes the audit without modification."⟩
      "hero-plain"

def pages : List PageDef := PageId.all.map staticPage

def navigation : Navigation :=
  { main := [PageId.guarantees, PageId.start].map fun id => .page (Render.slug id) id.title }

def site : Site := { config, pages, navigation, assets }

end NoGoalsSite
