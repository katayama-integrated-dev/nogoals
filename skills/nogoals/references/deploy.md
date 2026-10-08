# Deploying a NoGoals site

The artifact is `build/` after a green `--audit`. It is a plain static site
plus two Cloudflare Pages configuration files (`_headers`, `_redirects`),
`verification-manifest.json` (SHA-256 of every file) and
`verification/receipt.json`.

Rules the reference deploy script follows (copy them into any deploy):

1. **Preflight on the receipt**, not on hope: `profile.name == "full-audit"`,
   `totals.failed == 0`, every `profile.required` id present exactly once
   and positive, `source.consumer.commit == HEAD`, `source.nogoals.commit ==`
   NoGoals's HEAD, both `dirty == false`.
2. **Snapshot the artifact** before verifying so a concurrent build cannot
   swap the bytes you publish.
3. **Verify on a preview** first: upload to a preview branch, fetch every
   public manifest path (`x/index.html` at `/x/`, other `.html` files
   extensionless, `_headers`/`_redirects` not fetched) and compare hashes;
   check every `_redirects` line answers 301 with its `Location`.
4. **Then** upload the identical snapshot to the target branch.
5. **After production**, rewrite `deploy/permalink-baseline.txt` from the
   deployed manifest plus the receipt's `redirects` and commit it. The
   baseline is the record of what production has served; the permanence
   gate protects every path in it forever. Committing moves HEAD, so the
   next deploy needs a rebuild — that is the point.

Bootstrapping: a first-ever deploy has no baseline; run the audit once with
`--update-baseline`. A site already live without a baseline imports it from
production: the manifest for files, the receipt for redirect sources.
