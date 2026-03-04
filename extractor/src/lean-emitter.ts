/**
 * Lean Emitter — JsCoreExpr → Lean source text (pretty-printing each constructor).
 */

import { JsCoreExpr } from "./ast-to-jscore";

/**
 * Convert a JsCoreExpr to Lean 4 source text.
 */
export function emitLean(expr: JsCoreExpr, indent: number = 0): string {
  const pad = "  ".repeat(indent);

  switch (expr.tag) {
    case "var":
      return `${pad}(.var "${expr.name}")`;

    case "strLit":
      return `${pad}(.strLit "${escapeLeanString(expr.value)}")`;

    case "numLit":
      return `${pad}(.numLit ${expr.value})`;

    case "boolLit":
      return `${pad}(.boolLit ${expr.value})`;

    case "none":
      return `${pad}Expr.none`;

    case "letConst":
      return [
        `${pad}(.letConst "${expr.name}"`,
        emitLean(expr.value, indent + 1),
        emitLean(expr.body, indent + 1) + ")",
      ].join("\n");

    case "letMut":
      return [
        `${pad}(.letMut "${expr.name}"`,
        emitLean(expr.value, indent + 1),
        emitLean(expr.body, indent + 1) + ")",
      ].join("\n");

    case "assign":
      return [
        `${pad}(.assign "${expr.name}"`,
        emitLean(expr.value, indent + 1),
        emitLean(expr.body, indent + 1) + ")",
      ].join("\n");

    case "field":
      return [
        `${pad}(.field`,
        emitLean(expr.expr, indent + 1),
        `${pad}  "${expr.fieldName}")`,
      ].join("\n");

    case "obj":
      if (expr.fields.length === 0) {
        return `${pad}(.obj [])`;
      }
      return [
        `${pad}(.obj [`,
        expr.fields
          .map(([k, v]) => `${pad}  ("${k}", ${emitLean(v, 0).trim()})`)
          .join(",\n"),
        `${pad}])`,
      ].join("\n");

    case "spread":
      return [
        `${pad}(.spread`,
        emitLean(expr.base, indent + 1),
        `${pad}  [`,
        expr.overrides
          .map(([k, v]) => `${pad}    ("${k}", ${emitLean(v, 0).trim()})`)
          .join(",\n"),
        `${pad}  ])`,
      ].join("\n");

    case "arr":
      if (expr.elements.length === 0) {
        return `${pad}(.arr [])`;
      }
      return [
        `${pad}(.arr [`,
        expr.elements
          .map((e) => `${pad}  ${emitLean(e, 0).trim()}`)
          .join(",\n"),
        `${pad}])`,
      ].join("\n");

    case "index":
      return [
        `${pad}(.index`,
        emitLean(expr.expr, indent + 1),
        emitLean(expr.idx, indent + 1) + ")",
      ].join("\n");

    case "push":
      return [
        `${pad}(.push "${expr.arrName}"`,
        emitLean(expr.value, indent + 1) + ")",
      ].join("\n");

    case "seq":
      return [
        `${pad}(.seq`,
        emitLean(expr.first, indent + 1),
        emitLean(expr.second, indent + 1) + ")",
      ].join("\n");

    case "ite":
      return [
        `${pad}(.ite`,
        emitLean(expr.cond, indent + 1),
        emitLean(expr.then, indent + 1),
        emitLean(expr.else, indent + 1) + ")",
      ].join("\n");

    case "forOf":
      return [
        `${pad}(.forOf "${expr.varName}"`,
        emitLean(expr.arr, indent + 1),
        emitLean(expr.body, indent + 1) + ")",
      ].join("\n");

    case "whileLoop":
      return [
        `${pad}(.whileLoop ${expr.fuel}`,
        emitLean(expr.cond, indent + 1),
        emitLean(expr.body, indent + 1) + ")",
      ].join("\n");

    case "break":
      return `${pad}Expr.«break»`;

    case "ret":
      return [
        `${pad}(.ret`,
        emitLean(expr.value, indent + 1) + ")",
      ].join("\n");

    case "call":
      return [
        `${pad}(.call "${expr.target}"`,
        `${pad}  [${expr.args.map(([k, v]) => `("${k}", ${emitLean(v, 0).trim()})`).join(", ")}]`,
        `${pad}  "${expr.resultBinder}"`,
        emitLean(expr.body, indent + 1) + ")",
      ].join("\n");

    case "throw":
      return [
        `${pad}(.throw`,
        emitLean(expr.value, indent + 1) + ")",
      ].join("\n");

    case "tryCatch":
      return [
        `${pad}(.tryCatch`,
        emitLean(expr.body, indent + 1),
        `${pad}  "${expr.errName}"`,
        emitLean(expr.handler, indent + 1) + ")",
      ].join("\n");

    case "binOp":
      return [
        `${pad}(.binOp .${expr.op}`,
        emitLean(expr.left, indent + 1),
        emitLean(expr.right, indent + 1) + ")",
      ].join("\n");

    case "unOp":
      return [
        `${pad}(.unOp .${expr.op}`,
        emitLean(expr.operand, indent + 1) + ")",
      ].join("\n");

    case "sorry":
      return `${pad}-- sorry: ${expr.reason}\n${pad}Expr.none`;
  }
}

function escapeLeanString(s: string): string {
  return s
    .replace(/\\/g, "\\\\")
    .replace(/"/g, '\\"')
    .replace(/\n/g, "\\n")
    .replace(/\t/g, "\\t");
}

/**
 * Emit a complete Lean 4 file for a single function definition.
 */
export function emitLeanFile(
  functionName: string,
  expr: JsCoreExpr,
  params: string[],
  theorems: string[]
): string {
  return emitLeanFileMulti([{ name: functionName, expr, params, theorems }]);
}

export interface FunctionEntry {
  name: string;
  expr: JsCoreExpr;
  params: string[];
  theorems: string[];
}

/**
 * Emit a complete Lean 4 file with multiple function definitions + theorems.
 * Imports are emitted once at the top.
 */
export function emitLeanFileMulti(functions: FunctionEntry[]): string {
  const lines: string[] = [];

  lines.push("import JSCore.Syntax");
  lines.push("import JSCore.Values");
  lines.push("import JSCore.Eval");
  lines.push("import JSCore.Trace");
  lines.push("import JSCore.Properties");
  lines.push("import JSCore.Taint");
  lines.push("import JSCore.Tactics");
  lines.push("");
  lines.push("open JSCore");
  lines.push("");

  for (const fn of functions) {
    // Emit the definition
    lines.push(`def ${fn.name}_body : Expr :=`);
    lines.push(emitLean(fn.expr, 1));
    lines.push("");

    // Emit theorems
    for (const thm of fn.theorems) {
      lines.push(thm);
      lines.push("");
    }
  }

  return lines.join("\n");
}
