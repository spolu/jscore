/**
 * Pipeline orchestration — coordinates extraction from TS source to Lean files.
 */

import { Project, SourceFile, SyntaxKind, FunctionDeclaration, Node, TypeLiteralNode } from "ts-morph";
import { extractFunction, JsCoreExpr } from "./ast-to-jscore";
import { emitLean, emitLeanFile } from "./lean-emitter";
import {
  parseAnnotations,
  extractFunctionAnnotations,
  extractEnsuresAnnotations,
  RequiresAnnotation,
  InvariantAnnotation,
  EnsuresAnnotation,
} from "./annotation-parser";
import { generateTheorem } from "./lean-theorem";
import * as fs from "fs";
import * as path from "path";

export interface ExtractionResult {
  functionName: string;
  leanSource: string;
  hasSorry: boolean;
  invariantCount: number;
  requiresCount: number;
}

/**
 * Extract all annotated functions from a TypeScript source file.
 */
export function extractFile(
  filePath: string,
  project: Project,
  outputDir: string
): ExtractionResult[] {
  const sourceFile = project.addSourceFileAtPath(filePath);
  const checker = project.getTypeChecker();
  const results: ExtractionResult[] = [];

  // Collect untainted call targets from declare blocks
  const untaintedCalls = collectDeclareUntaints(sourceFile);

  // Find all function declarations with annotations
  const functions = sourceFile.getFunctions();

  for (const func of functions) {
    const name = func.getName();
    if (!name) continue;

    // Get leading comments for annotations
    const commentRanges = func.getLeadingCommentRanges();
    const comments = commentRanges.map((r) => r.getText());

    const { requires: reqs, invariants: invs } =
      extractFunctionAnnotations(comments);

    // Skip functions with no annotations
    if (reqs.length === 0 && invs.length === 0) continue;

    // Collect @ensures from inline comments in the function body
    const bodyEnsures = collectInlineEnsures(func);
    const ensuresBindings = new Set(bodyEnsures.map((e) => e.binding));

    // Extract the function body
    const expr = extractFunction(func, checker, 1000, ensuresBindings);

    // Check for sorry
    const hasSorry = containsSorry(expr);

    // Get parameter names
    const params = func.getParameters().map((p) => p.getName());
    const runtimeFuel = estimateRuntimeFuel(expr);
    const emitCanonicalRuntimeTheorem = isStraightLine(expr);

    // Generate theorems (with index to disambiguate duplicate tags)
    const tagCounts = new Map<string, number>();
    const theorems = invs.map((inv) => {
      const count = tagCounts.get(inv.tag) ?? 0;
      tagCounts.set(inv.tag, count + 1);
      return generateTheorem(name, inv, reqs, bodyEnsures, params, count, {
        runtimeFuel,
        emitCanonicalRuntimeTheorem,
      }, untaintedCalls);
    });

    // Emit Lean file
    const leanSource = emitLeanFile(name, expr, params, theorems);

    // Write to output
    const pascalName = name[0].toUpperCase() + name.slice(1);
    const outPath = path.join(outputDir, `${pascalName}.lean`);
    fs.mkdirSync(outputDir, { recursive: true });
    fs.writeFileSync(outPath, leanSource);

    results.push({
      functionName: name,
      leanSource,
      hasSorry,
      invariantCount: invs.length,
      requiresCount: reqs.length,
    });
  }

  return results;
}

/**
 * Extract all TypeScript files in a list.
 */
export function extractFiles(
  filePaths: string[],
  outputDir: string,
  tsConfigPath?: string
): ExtractionResult[] {
  const project = new Project({
    tsConfigFilePath: tsConfigPath,
    skipAddingFilesFromTsConfig: true,
  });

  const allResults: ExtractionResult[] = [];

  for (const filePath of filePaths) {
    const results = extractFile(filePath, project, outputDir);
    allResults.push(...results);
  }

  return allResults;
}

function containsSorry(expr: JsCoreExpr): boolean {
  if (expr.tag === "sorry") return true;

  switch (expr.tag) {
    case "letConst":
    case "letMut":
    case "assign":
      return containsSorry(expr.value) || containsSorry(expr.body);
    case "seq":
      return containsSorry(expr.first) || containsSorry(expr.second);
    case "ite":
      return (
        containsSorry(expr.cond) ||
        containsSorry(expr.then) ||
        containsSorry(expr.else)
      );
    case "forOf":
      return containsSorry(expr.arr) || containsSorry(expr.body);
    case "whileLoop":
      return containsSorry(expr.cond) || containsSorry(expr.body);
    case "call":
      return (
        expr.args.some(([, v]) => containsSorry(v)) ||
        containsSorry(expr.body)
      );
    case "tryCatch":
      return containsSorry(expr.body) || containsSorry(expr.handler);
    case "ret":
    case "throw":
      return containsSorry(expr.value);
    case "field":
      return containsSorry(expr.expr);
    case "index":
      return containsSorry(expr.expr) || containsSorry(expr.idx);
    case "push":
      return containsSorry(expr.value);
    case "obj":
      return expr.fields.some(([, v]) => containsSorry(v));
    case "spread":
      return (
        containsSorry(expr.base) ||
        expr.overrides.some(([, v]) => containsSorry(v))
      );
    case "arr":
      return expr.elements.some(containsSorry);
    case "binOp":
      return containsSorry(expr.left) || containsSorry(expr.right);
    case "unOp":
      return containsSorry(expr.operand);
    default:
      return false;
  }
}

function estimateRuntimeFuel(expr: JsCoreExpr): number {
  // Add a small buffer to the structural depth so generated `h_fuel` is robust
  // to tiny evaluation-shape changes in arguments/body wrappers.
  return depthFuel(expr) + 1;
}

function depthFuel(expr: JsCoreExpr): number {
  switch (expr.tag) {
    case "var":
    case "strLit":
    case "numLit":
    case "boolLit":
    case "none":
    case "break":
      return 1;
    case "letConst":
    case "letMut":
    case "assign":
      return 1 + Math.max(depthFuel(expr.value), depthFuel(expr.body));
    case "field":
      return 1 + depthFuel(expr.expr);
    case "obj": {
      const fieldDepth =
        expr.fields.length === 0
          ? 0
          : Math.max(...expr.fields.map(([, value]) => depthFuel(value)));
      return 1 + fieldDepth;
    }
    case "spread": {
      const overrideDepth =
        expr.overrides.length === 0
          ? 0
          : Math.max(...expr.overrides.map(([, value]) => depthFuel(value)));
      return 1 + Math.max(depthFuel(expr.base), overrideDepth);
    }
    case "arr": {
      const elemDepth =
        expr.elements.length === 0
          ? 0
          : Math.max(...expr.elements.map((element) => depthFuel(element)));
      return 1 + elemDepth;
    }
    case "index":
      return 1 + Math.max(depthFuel(expr.expr), depthFuel(expr.idx));
    case "push":
      return 1 + depthFuel(expr.value);
    case "seq":
      return 1 + Math.max(depthFuel(expr.first), depthFuel(expr.second));
    case "ite":
      return 1 + Math.max(depthFuel(expr.cond), depthFuel(expr.then), depthFuel(expr.else));
    case "forOf":
      return 1 + Math.max(depthFuel(expr.arr), depthFuel(expr.body));
    case "whileLoop":
      return 1 + Math.max(depthFuel(expr.cond), depthFuel(expr.body));
    case "ret":
    case "throw":
      return 1 + depthFuel(expr.value);
    case "call": {
      const argDepth =
        expr.args.length === 0
          ? 0
          : Math.max(...expr.args.map(([, value]) => depthFuel(value)));
      return 1 + Math.max(argDepth, depthFuel(expr.body));
    }
    case "tryCatch":
      return 1 + Math.max(depthFuel(expr.body), depthFuel(expr.handler));
    case "binOp":
      return 1 + Math.max(depthFuel(expr.left), depthFuel(expr.right));
    case "unOp":
      return 1 + depthFuel(expr.operand);
    case "sorry":
      return 1;
  }
}

/**
 * Collect @ensures annotations from inline comments within a function body.
 * Scans all descendant nodes for leading comment ranges containing @ensures.
 */
function collectInlineEnsures(func: Node): EnsuresAnnotation[] {
  const ensures: EnsuresAnnotation[] = [];
  func.forEachDescendant((node) => {
    const commentRanges = node.getLeadingCommentRanges();
    for (const cr of commentRanges) {
      const text = cr.getText();
      const found = extractEnsuresAnnotations([text]);
      ensures.push(...found);
    }
  });
  // Deduplicate by binding name (same binding may be found multiple times
  // due to overlapping descendant traversal)
  const seen = new Set<string>();
  return ensures.filter((e) => {
    const key = `${e.binding}.${e.pred}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

/**
 * Collect untainted call targets from declare blocks.
 * Scans `declare const X: { method(...): ...; }` for methods annotated with
 * `@invariant no-taint: ¬ tainted <param> in result` and returns call targets
 * as "varName.methodName".
 */
function collectDeclareUntaints(sourceFile: SourceFile): string[] {
  const untainted: string[] = [];

  for (const stmt of sourceFile.getVariableStatements()) {
    if (!stmt.hasDeclareKeyword()) continue;

    for (const decl of stmt.getDeclarations()) {
      const varName = decl.getName();
      const typeNode = decl.getTypeNode();
      if (!typeNode || typeNode.getKind() !== SyntaxKind.TypeLiteral) continue;

      const typeLiteral = typeNode as TypeLiteralNode;
      for (const member of typeLiteral.getMembers()) {
        const memberName = member.getSymbol()?.getName();
        if (!memberName) continue;

        const commentRanges = member.getLeadingCommentRanges();
        for (const cr of commentRanges) {
          const text = cr.getText();
          // Match: @invariant <tag>: ¬ tainted <param> in result
          if (/¬\s*tainted\s+\w+\s+in\s+result/.test(text)) {
            untainted.push(`${varName}.${memberName}`);
          }
        }
      }
    }
  }

  return untainted;
}

function isStraightLine(expr: JsCoreExpr): boolean {
  switch (expr.tag) {
    case "ite":
    case "forOf":
    case "whileLoop":
    case "tryCatch":
      return false;
    case "letConst":
    case "letMut":
    case "assign":
      return isStraightLine(expr.value) && isStraightLine(expr.body);
    case "seq":
      return isStraightLine(expr.first) && isStraightLine(expr.second);
    case "field":
      return isStraightLine(expr.expr);
    case "obj":
      return expr.fields.every(([, value]) => isStraightLine(value));
    case "spread":
      return isStraightLine(expr.base) && expr.overrides.every(([, value]) => isStraightLine(value));
    case "arr":
      return expr.elements.every((element) => isStraightLine(element));
    case "index":
      return isStraightLine(expr.expr) && isStraightLine(expr.idx);
    case "push":
      return isStraightLine(expr.value);
    case "ret":
    case "throw":
      return isStraightLine(expr.value);
    case "call":
      return expr.args.every(([, value]) => isStraightLine(value)) && isStraightLine(expr.body);
    case "binOp":
      return isStraightLine(expr.left) && isStraightLine(expr.right);
    case "unOp":
      return isStraightLine(expr.operand);
    case "var":
    case "strLit":
    case "numLit":
    case "boolLit":
    case "none":
    case "break":
    case "sorry":
      return true;
  }
}
