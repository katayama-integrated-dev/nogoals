#!/usr/bin/env node
// html-facts — what a browser-grade parser saw in the emitted pages.
//
//   node <NoGoals>/tools/html-facts.mjs <root> <relative-path>...
//
// Ships with NoGoals; `parse5` is resolved from the SITE's working directory
// (its pinned node_modules), so one copy of this script serves every site.
//
// Parses every named file with parse5 (the WHATWG HTML parsing algorithm:
// quoting, case, comments, entities, raw-text and RCDATA contexts handled
// as a browser handles them) and prints ONE JSON document of facts to
// stdout, in the exact schema `NoGoals.Verify.HtmlFacts.parseFacts` decodes:
//
//   { "files": [ { "path", "elements": [ { "tag", "attrs", "hasText" } ],
//                  "ids", "text", "attrText" } ] }
//
// - elements: document order; tag lower-cased; attrs entity-decoded, names
//   lower-cased (a duplicate attribute keeps the first, as browsers do);
//   hasText: the element has a direct non-blank text child (inline <script>
//   / <style> detection).
// - ids: every `id` attribute value, in order (duplicates preserved so the
//   consumer can see them).
// - text: visible text — every text node outside <script>, <style>,
//   <template>, <noscript>, joined with spaces.
// - attrText: human-facing attribute values: alt, title, placeholder,
//   aria-label, and <meta name="description" content>.
//
// Any parse or IO failure exits nonzero with no output: a gate that depends
// on facts then fails, never passes.

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { createRequire } from "node:module";

const parse5 = createRequire(join(process.cwd(), "package.json"))("parse5");

const [root, ...files] = process.argv.slice(2);
if (!root || files.length === 0) {
  console.error("usage: html-facts.mjs <root> <relative-path>...");
  process.exit(2);
}

const SKIP_TEXT = new Set(["script", "style", "template", "noscript"]);
const HUMAN_ATTRS = new Set(["alt", "title", "placeholder", "aria-label"]);

function facts(path, html) {
  const doc = parse5.parse(html);
  const elements = [];
  const ids = [];
  const text = [];
  const attrText = [];

  function walk(node, inSkip) {
    if (node.nodeName === "#text") {
      if (!inSkip && node.value.trim() !== "") text.push(node.value.trim());
      return;
    }
    if (node.nodeName === "#comment" || node.nodeName === "#documentType") return;
    if (node.tagName) {
      const tag = node.tagName.toLowerCase();
      const attrs = {};
      for (const a of node.attrs ?? []) {
        const name = a.name.toLowerCase();
        if (!(name in attrs)) attrs[name] = a.value;
      }
      const hasText = (node.childNodes ?? []).some(
        (c) => c.nodeName === "#text" && c.value.trim() !== ""
      );
      elements.push({ tag, attrs, hasText });
      if ("id" in attrs) ids.push(attrs.id);
      for (const [k, v] of Object.entries(attrs)) {
        if (HUMAN_ATTRS.has(k) && v.trim() !== "") attrText.push(v);
      }
      if (tag === "meta" && attrs.name === "description" && attrs.content) attrText.push(attrs.content);
      inSkip = inSkip || SKIP_TEXT.has(tag);
    }
    const children = node.childNodes ?? [];
    for (const c of children) walk(c, inSkip);
    // <template> content lives on a separate fragment; nothing there is visible.
  }
  walk(doc, false);
  return { path, elements, ids, text: text.join(" "), attrText };
}

const out = { files: [] };
for (const rel of files) {
  const html = readFileSync(join(root, rel), "utf8");
  out.files.push(facts(rel, html));
}
process.stdout.write(JSON.stringify(out));
