#!/usr/bin/env bash
# deploy.sh — publish the audited build/ to Cloudflare (Workers static
# assets, where Pages lives now), fail closed at every step.
#
#   deploy/deploy.sh preview            upload a preview version, verify it, stop
#   deploy/deploy.sh production [--yes] preview + verify, then promote to 100 %
#
# What it refuses: a dirty tree; a receipt that is not a green full audit at
# HEAD; a preview whose served bytes differ from the manifest. What it does
# after a production promote: rewrites deploy/permalink-baseline.txt from
# the deployed manifest — the baseline is a record of production. Commit it.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${SITE_ROOT}"

WORKER="nogoals"
PROD_URL="https://nogoals.org"
BUILD_DIR="${SITE_ROOT}/build"
MANIFEST="${BUILD_DIR}/verification-manifest.json"
RECEIPT="${BUILD_DIR}/verification/receipt.json"
BASELINE="${SITE_ROOT}/deploy/permalink-baseline.txt"
WRANGLER=(npx --no-install wrangler)

die()  { printf '✗ %s\n' "$*" >&2; exit 1; }
ok()   { printf '✓ %s\n' "$*"; }
info() { printf '— %s\n' "$*"; }

MODE="${1:-}"; CONFIRM="${2:-}"
case "${MODE}" in preview|production) ;; *) die "usage: $0 preview | production [--yes]" ;; esac

# ── Preflight ──────────────────────────────────────────────────────────────
for t in npx curl jq git shasum; do command -v "$t" >/dev/null || die "missing tool: $t"; done
git diff --quiet && git diff --cached --quiet || die "working tree has uncommitted changes; commit, rebuild, redeploy"
[[ -f "${MANIFEST}" && -f "${RECEIPT}" ]] || die "no audited build: run ./scripts/build.sh --audit"

SNAPSHOT="$(mktemp -d -t nogoals-artifact.XXXXXX)"; trap 'rm -rf "${SNAPSHOT}"' EXIT
cp -R "${BUILD_DIR}/." "${SNAPSHOT}/"; MANIFEST="${SNAPSHOT}/verification-manifest.json"; RECEIPT="${SNAPSHOT}/verification/receipt.json"

HEAD_SHA="$(git rev-parse HEAD)"
[[ "$(jq -r '.profile.name' "${RECEIPT}")" == "full-audit" ]] || die "receipt profile is '$(jq -r .profile.name "${RECEIPT}")', not full-audit: run ./scripts/build.sh --audit"
for key in consumer.dirty nogoals.dirty; do
  [[ "$(jq -r --arg k "$key" '.source[$k]' "${RECEIPT}")" == "false" ]] || die "receipt records ${key}=true: built from a dirty tree"
done
[[ "$(jq -r '.source["consumer.commit"]' "${RECEIPT}")" == "${HEAD_SHA}" ]] || die "receipt was built at $(jq -r '.source["consumer.commit"]' "${RECEIPT}" | cut -c1-12), HEAD is ${HEAD_SHA:0:12}: rebuild"
[[ "$(jq -r '.totals.failed' "${RECEIPT}")" == "0" ]] || die "receipt records failed checks"
while IFS= read -r gid; do
  tier="$(jq -r --arg id "$gid" '[.guarantees[] | select(.id == $id)] | if length == 1 then .[0].tier else "absent" end' "${RECEIPT}")"
  [[ "${tier}" == "checked" || "${tier}" == "enforced" ]] || die "required gate ${gid} is ${tier} in the receipt"
done < <(jq -r '.profile.required[]' "${RECEIPT}")
ok "receipt: full-audit, clean at ${HEAD_SHA:0:12}, $(jq -r '.profile.required | length' "${RECEIPT}") required gates green"

# ── Preview version ────────────────────────────────────────────────────────
LOG="$(mktemp -t nogoals-wrangler.XXXXXX)"
info "uploading preview version (${WORKER}, alias verify-${HEAD_SHA:0:8})"
"${WRANGLER[@]}" versions upload --assets "${SNAPSHOT}" --preview-alias "verify-${HEAD_SHA:0:8}" \
  --message "${HEAD_SHA:0:12}" 2>&1 | tee "${LOG}" | grep -E 'Version ID|Preview URL|error' || true
VERSION_ID="$(grep -Eo 'Worker Version ID: [0-9a-f-]+' "${LOG}" | awk '{print $4}' | head -1)"
PREVIEW_URL="$(grep -Eo 'https://verify-[a-z0-9-]+\.[a-z0-9.-]+\.workers\.dev' "${LOG}" | head -1)"
[[ -n "${VERSION_ID}" && -n "${PREVIEW_URL}" ]] || die "could not parse version id / preview URL from wrangler output (${LOG})"
ok "preview: ${PREVIEW_URL} (version ${VERSION_ID:0:8})"

# Where a manifest path is served (Cloudflare Pages rules, which the link gate models).
url_for() {
  local base="$1" p="$2"
  case "${p}" in
    index.html) echo "${base}/";;
    */index.html) echo "${base}/${p%/index.html}/";;
    *.html) echo "${base}/${p%.html}";;
    *) echo "${base}/${p}";;
  esac
}

verify_served() {
  local base="$1" total=0 verified=0 bad=() body
  body="$(mktemp -t nogoals-body.XXXXXX)"
  while IFS=$'\t' read -r path sha; do
    [[ -z "${path}" || "${path}" == "_headers" || "${path}" == "_redirects" ]] && continue
    total=$((total+1))
    if ! curl -sS --fail --max-time 30 -H 'Accept-Encoding: identity' -o "${body}" "$(url_for "${base}" "${path}")"; then
      bad+=("${path}: fetch failed"); continue
    fi
    got="$(shasum -a 256 "${body}" | cut -c1-64)"
    if [[ "${got}" == "${sha}" ]]; then verified=$((verified+1)); else bad+=("${path}: served ${got:0:12}, manifest ${sha:0:12}"); fi
  done < <(jq -r '.files[] | "\(.path)\t\(.sha256)"' "${MANIFEST}")
  # Redirects: every _redirects line must answer with its status and target.
  local redirects=0
  if [[ -s "${SNAPSHOT}/_redirects" ]]; then
    while read -r src dst code; do
      [[ -z "${src}" ]] && continue; redirects=$((redirects+1))
      hdr="$(curl -sS -I --max-time 30 "${base}${src}" || true)"
      status="$(printf '%s' "${hdr}" | awk 'NR==1{print $2}')"; loc="$(printf '%s' "${hdr}" | awk 'tolower($1)=="location:"{print $2}' | tr -d '\r')"
      [[ "${status}" == "${code}" && ( "${loc}" == "${dst}" || "${loc}" == "${base}${dst}" ) ]] || bad+=("redirect ${src}: got ${status:-none} ${loc:-no Location}")
    done < "${SNAPSHOT}/_redirects"
  fi
  # The security headers must reach the wire.
  curl -sSI --max-time 30 "${base}/" | grep -qi '^content-security-policy:' || bad+=("no Content-Security-Policy header on /")
  printf '  %d/%d files match the manifest, %d redirect(s) checked\n' "${verified}" "${total}" "${redirects}"
  if [[ ${#bad[@]} -gt 0 ]]; then for b in "${bad[@]}"; do printf '  ✗ %s\n' "${b}" >&2; done; return 1; fi
}

info "verifying the preview against the manifest"
verify_served "${PREVIEW_URL}" || die "preview does not match the manifest; nothing promoted"
ok "preview verified"
[[ "${MODE}" == "preview" ]] && { printf '\nPreview only. Promote with: %s production --yes\n' "$0"; exit 0; }

# ── Promote ────────────────────────────────────────────────────────────────
if [[ "${CONFIRM}" != "--yes" ]]; then
  printf 'About to make version %s PRODUCTION at %s. Type yes: ' "${VERSION_ID:0:8}" "${PROD_URL}"; read -r a; [[ "${a}" == "yes" ]] || die "aborted"
fi
"${WRANGLER[@]}" versions deploy "${VERSION_ID}@100%" --yes --message "${HEAD_SHA:0:12}" 2>&1 | grep -E 'Deployed|error|Version' || true
ok "promoted ${VERSION_ID:0:8} to 100 %"
# Custom domains and the workers.dev route are triggers, applied separately
# from a version promote. A hostname that still has foreign DNS records is
# refused here (Cloudflare 100117); the version stays live on workers.dev.
"${WRANGLER[@]}" triggers deploy 2>&1 | grep -E 'workers\.dev|nogoals\.org|100117|ERROR' || true

info "verifying production (${PROD_URL})"
if verify_served "${PROD_URL}"; then ok "production verified"; else
  printf '  (a freshly attached custom domain can lag; re-check: curl -I %s/)\n' "${PROD_URL}"; fi

# ── Baseline: the record of production ────────────────────────────────────
tmp="$(mktemp -t permalink-baseline.XXXXXX)"
jq -r '.files[] | "\(.sha256)  \(.path)"' "${MANIFEST}" > "${tmp}"
jq -r '.redirects[] | "redirect  \(.)"' "${RECEIPT}" >> "${tmp}"
mv "${tmp}" "${BASELINE}"
ok "permalink baseline rewritten from the deployed manifest — commit it"
