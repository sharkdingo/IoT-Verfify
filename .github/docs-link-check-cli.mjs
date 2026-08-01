#!/usr/bin/env node
// Walks the repository's Markdown and reports every unresolvable cross-reference.
// Exits non-zero with the document, the link, and what to correct.

import { readdirSync, readFileSync } from 'node:fs';
import { join, relative, resolve, dirname } from 'node:path';
import {
  definedAnchors, isExternal, linksIn, shouldSkipDirectory
} from './docs-link-check.mjs';

const root = process.argv[2] ?? '.';

const markdownFiles = (directory) => readdirSync(directory, { withFileTypes: true })
  .flatMap((entry) => {
    if (entry.isDirectory()) {
      return shouldSkipDirectory(entry.name) ? [] : markdownFiles(join(directory, entry.name));
    }
    return entry.name.endsWith('.md') ? [join(directory, entry.name)] : [];
  });

const files = markdownFiles(root);
const anchorCache = new Map();
const anchorsOf = (file) => {
  if (!anchorCache.has(file)) {
    try {
      anchorCache.set(file, definedAnchors(readFileSync(file, 'utf8')));
    } catch {
      anchorCache.set(file, null); // unreadable; the missing-file check already reports it
    }
  }
  return anchorCache.get(file);
};

const problems = [];
for (const file of files) {
  const markdown = readFileSync(file, 'utf8');
  for (const { target, fragment } of linksIn(markdown)) {
    if (isExternal(target)) continue;

    const resolved = target === '' ? file : resolve(dirname(file), target);
    const anchors = anchorsOf(resolved);
    if (anchors === null || (target !== '' && !files.includes(resolved) && !safeExists(resolved))) {
      problems.push({
        file: relative(root, file),
        link: fragment ? `${target}#${fragment}` : target,
        reason: 'target does not exist',
        fix: 'point the link at an existing path, or remove it if the page it described is gone'
      });
      continue;
    }
    if (fragment && anchors && !anchors.has(fragment.toLowerCase())) {
      problems.push({
        file: relative(root, file),
        link: `${target}#${fragment}`,
        reason: `no heading in ${relative(root, resolved)} produces this anchor`,
        fix: 'match the target heading text, or add the section the link promises'
      });
    }
  }
}

function safeExists(path) {
  try {
    readFileSync(path);
    return true;
  } catch {
    try {
      readdirSync(path);
      return true; // a link to a directory is legitimate
    } catch {
      return false;
    }
  }
}

if (problems.length > 0) {
  console.error(`${problems.length} unresolvable documentation reference(s):\n`);
  for (const problem of problems) {
    console.error(`  ${problem.file}`);
    console.error(`    link:  ${problem.link}`);
    console.error(`    cause: ${problem.reason}`);
    console.error(`    fix:   ${problem.fix}\n`);
  }
  console.error('Documentation links between pages replace repeated facts, so a broken one hides');
  console.error('the authoritative source a reader was sent to find.');
  process.exit(1);
}

console.log(`All documentation links and anchors resolve (${files.length} files).`);
