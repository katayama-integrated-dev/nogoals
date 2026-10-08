/-
  Typed Atom feed (RFC 4287, the minimal valid core).

  A feed is a typed value, not a template: every text field passes through
  `Meta.xmlEscape` at render time, entry URLs are `canonicalBaseUrl ++
  Route.href` of the entry's own route — the one path function, so an entry
  cannot point anywhere but at an emitted page — and dates arrive as
  `IsoDate` so a malformed date cannot reach the XML.

  Deliberately not modelled: paged feeds, categories, enclosures — nothing
  the one production consumer doesn't ship.
-/

import NoGoals.IR.Route
import NoGoals.Meta
import NoGoals.Verify.Date

namespace NoGoals.Render.Feed

open NoGoals.Meta (xmlEscape)
open NoGoals.Verify (IsoDate)

structure FeedEntry where
  /-- Entry title (escaped at render). -/
  title : String
  /-- The entry's page. Its absolute URL is also the stable entry id. -/
  route : Route
  /-- Publication date; rendered as `YYYY-MM-DDT00:00:00Z`. -/
  date : IsoDate
  /-- Short summary (escaped at render). -/
  summary : String
  /-- Optional author name (escaped at render). -/
  author : Option String := none
deriving Repr

structure AtomFeed where
  /-- Feed title (escaped at render). -/
  title : String
  /-- Absolute origin of the site (`https://…`, no trailing slash). -/
  baseUrl : String
  /-- The site's default language (decides which routes are unprefixed). -/
  defaultLang : Lang
  /-- The feed's language; the feed lives at `<lang home>/feed.xml`. -/
  lang : Lang
  entries : List FeedEntry
deriving Repr

/-- The home route of the feed's language. -/
def AtomFeed.home (f : AtomFeed) : Route := ⟨Slug.index, f.lang⟩

def AtomFeed.siteUrl (f : AtomFeed) : String := f.baseUrl ++ f.home.href f.defaultLang

/-- Where the feed document itself is emitted (`feed.xml`, `en/feed.xml`). -/
def AtomFeed.outputPath (f : AtomFeed) : String :=
  String.ofList (joinDirs (f.home.dirSegments f.defaultLang) ++ "feed.xml".toList)

def AtomFeed.selfUrl (f : AtomFeed) : String := f.baseUrl ++ "/" ++ f.outputPath

def FeedEntry.url (baseUrl : String) (d : Lang) (e : FeedEntry) : String :=
  baseUrl ++ e.route.href d

/-- Atom timestamps require a time component; article dates are calendar
    dates, so midnight UTC is the honest rendering. -/
def atomStamp (d : IsoDate) : String := s!"{d.toString}T00:00:00Z"

def renderEntry (baseUrl : String) (d : Lang) (e : FeedEntry) : String :=
  let url := e.url baseUrl d
  let author := match e.author with
    | some a => s!"\n    <author><name>{xmlEscape a}</name></author>"
    | none => ""
  s!"  <entry>
    <title>{xmlEscape e.title}</title>
    <id>{xmlEscape url}</id>
    <link rel=\"alternate\" type=\"text/html\" href=\"{xmlEscape url}\"/>
    <updated>{atomStamp e.date}</updated>
    <summary>{xmlEscape e.summary}</summary>{author}
  </entry>"

/-- The feed's `updated` is the newest entry date (entries are expected
    newest-first; the news-sorted audit check enforces that upstream). -/
def feedUpdated (f : AtomFeed) : String :=
  match f.entries.head? with
  | some e => atomStamp e.date
  | none => "1970-01-01T00:00:00Z"

def render (f : AtomFeed) : String :=
  let entries := String.intercalate "\n" (f.entries.map (renderEntry f.baseUrl f.defaultLang))
  s!"<?xml version=\"1.0\" encoding=\"utf-8\"?>
<feed xmlns=\"http://www.w3.org/2005/Atom\" xml:lang=\"{xmlEscape f.lang.code}\">
  <title>{xmlEscape f.title}</title>
  <id>{xmlEscape f.siteUrl}</id>
  <link rel=\"alternate\" type=\"text/html\" href=\"{xmlEscape f.siteUrl}\"/>
  <link rel=\"self\" type=\"application/atom+xml\" href=\"{xmlEscape f.selfUrl}\"/>
  <updated>{feedUpdated f}</updated>
{entries}
</feed>
"

/-- The routes a rendered feed points at. The audit gate compares this
    against the emitted route set. -/
def entryRoutes (f : AtomFeed) : List Route := f.entries.map (·.route)

end NoGoals.Render.Feed
