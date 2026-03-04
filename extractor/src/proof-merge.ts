/**
 * Proof-preserving merge — when regenerating a .lean file, splice existing
 * proof bodies back into the freshly generated skeleton.
 *
 * Strategy: parse both files into top-level blocks (def, theorem, private def,
 * private theorem, other).  For theorems whose name matches and whose old body
 * is NOT `sorry`, keep the old proof body.  For defs, always take the new
 * version.  Private helpers from the old file that don't appear in the new
 * file are preserved (they typically support hand-written proofs).
 */

interface Block {
  kind: "import" | "open" | "def" | "abbrev" | "theorem" | "private" | "other";
  name: string;       // e.g. "foo_body" for def, "foo_no_leak" for theorem
  fullText: string;   // complete text of the block
  hasSorry: boolean;  // whether the block body contains `sorry`
}

/**
 * Split a Lean source file into top-level blocks.
 * A new block starts at any line matching one of the top-level keywords.
 */
function parseBlocks(source: string): Block[] {
  const lines = source.split("\n");
  const blocks: Block[] = [];
  let current: string[] = [];
  let currentKind: Block["kind"] = "other";
  let currentName = "";

  function flush() {
    if (current.length === 0) return;
    const text = current.join("\n");
    blocks.push({
      kind: currentKind,
      name: currentName,
      fullText: text,
      hasSorry: /\bsorry\b/.test(text),
    });
    current = [];
    currentKind = "other";
    currentName = "";
  }

  for (const line of lines) {
    const importMatch = line.match(/^import\s+/);
    const openMatch = line.match(/^open\s+/);
    const defMatch = line.match(/^def\s+(\S+)/);
    const abbrevMatch = line.match(/^abbrev\s+(\S+)/);
    const theoremMatch = line.match(/^theorem\s+(\S+)/);
    const privateMatch = line.match(/^private\s+(def|theorem)\s+(\S+)/);

    if (importMatch || openMatch || defMatch || abbrevMatch || theoremMatch || privateMatch) {
      flush();
      if (importMatch) {
        currentKind = "import";
        currentName = line.trim();
      } else if (openMatch) {
        currentKind = "open";
        currentName = "";
      } else if (privateMatch) {
        currentKind = "private";
        currentName = privateMatch[2];
      } else if (abbrevMatch) {
        currentKind = "abbrev";
        currentName = abbrevMatch[1];
      } else if (defMatch) {
        currentKind = "def";
        currentName = defMatch[1];
      } else if (theoremMatch) {
        currentKind = "theorem";
        currentName = theoremMatch[1];
      }
    }
    current.push(line);
  }
  flush();

  return blocks;
}

/**
 * Merge a newly generated Lean file with an existing one, preserving proofs.
 *
 * Rules:
 * - Imports/open: always use new version
 * - Defs: always use new version (expression tree may have changed)
 * - Theorems: if old file has a non-sorry proof for the same theorem name,
 *   use the old block; otherwise use the new block
 * - Private helpers from old file: preserved if they don't exist in new file
 *   (inserted right before the first theorem that might use them)
 */
export function mergeProofs(newSource: string, existingSource: string): string {
  const newBlocks = parseBlocks(newSource);
  const oldBlocks = parseBlocks(existingSource);

  // Union imports: collect all import lines from both files
  const newImports = new Set(
    newBlocks.filter((b) => b.kind === "import").map((b) => b.name)
  );
  const oldImports = oldBlocks
    .filter((b) => b.kind === "import")
    .filter((b) => !newImports.has(b.name));

  // Build lookup of old blocks by name (non-import)
  const oldByName = new Map<string, Block>();
  for (const b of oldBlocks) {
    if (b.name && b.kind !== "import") {
      oldByName.set(b.name, b);
    }
  }

  // Track which old blocks we've used
  const usedOldNames = new Set<string>();

  // Build result from new blocks, splicing in old proofs where appropriate
  const resultBlocks: string[] = [];
  let lastImportIdx = -1;

  for (let i = 0; i < newBlocks.length; i++) {
    const nb = newBlocks[i];

    if (nb.kind === "import") {
      lastImportIdx = resultBlocks.length;
      resultBlocks.push(nb.fullText);
      continue;
    }

    if (nb.kind === "theorem" && nb.name) {
      const old = oldByName.get(nb.name);
      if (old && !old.hasSorry) {
        // Use old proven theorem
        resultBlocks.push(old.fullText);
        usedOldNames.add(nb.name);
        continue;
      }
    }

    resultBlocks.push(nb.fullText);
    if (nb.name) usedOldNames.add(nb.name);
  }

  // Insert extra imports from old file right after the last new import
  if (oldImports.length > 0 && lastImportIdx >= 0) {
    const extraImportTexts = oldImports.map((b) => b.fullText);
    resultBlocks.splice(lastImportIdx + 1, 0, ...extraImportTexts);
  }

  // Collect private helpers and abbrevs from old file that aren't in the new file
  const extraBlocks: string[] = [];
  for (const ob of oldBlocks) {
    if ((ob.kind === "private" || ob.kind === "abbrev") && ob.name && !usedOldNames.has(ob.name)) {
      extraBlocks.push(ob.fullText);
    }
  }

  // Insert extra blocks before the first theorem block
  if (extraBlocks.length > 0) {
    const firstTheoremIdx = resultBlocks.findIndex((text) =>
      /^theorem\s/.test(text)
    );
    if (firstTheoremIdx >= 0) {
      resultBlocks.splice(firstTheoremIdx, 0, ...extraBlocks);
    } else {
      resultBlocks.push(...extraBlocks);
    }
  }

  return resultBlocks.join("\n\n") + "\n";
}
