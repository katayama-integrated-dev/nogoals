# Changelog

All notable changes to NoGoals are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/).

## 0.1.0 — October 8, 2026

Initial public release.

### Added

- An internal link is an index into the site's pages; a theorem proves every rendered link resolves.
- An asset reference names a declared asset of the right kind, which the type checker enforces; `--audit` checks the files on disk.
- Every text field carries a Japanese and an English value; a page missing either does not compile. Translation quality is not checked.
- Canonical links, hreflang alternates, the sitemap and the feeds are generated from one route set.
- Under `--audit`, CSP, HTML validity, SEO and permalink permanence are checked fail-closed on the emitted files; a failing build is quarantined in `build.failed/`.
- Every build writes a machine-readable receipt that a deploy script can require before publishing.
- The header marks the current page's nav link (`class="nav-link"`, `aria-current="page"`; `"true"` on the section that contains the page), carries a script-free `<details class="nav-menu">` copy of the nav for narrow screens, and opens with a skip link to `<main id="main">`. The language link declares `lang` and `hreflang`. A site's stylesheet styles `nav-link`, `nav-menu`, `nav-menu-list` and `skip-link`; the CSS-contract gate requires it.
- `PageDef.indexed` (default `true`): `false` serves the page with `<meta name="robots" content="noindex">` and leaves it out of the sitemap, for pages such as a form's receipt.
- `Division.summary`: one required sentence per division, for a directory of divisions.
- Every build emits a not-found page per language (`404.html`, and `en/404.html` or `ja/404.html` for the other language) in the site's chrome. They are outside the route set (no canonical, no sitemap entry) and pass html-validate, CSP, links and the CSS contract like every page.
- `PageDef.heroLead`: `.description` (the default), `.text lead`, or `.omitted`, which renders the hero with its title alone.
