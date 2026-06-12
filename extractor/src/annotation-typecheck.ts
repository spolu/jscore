/**
 * Annotation type-checking — validates @requires/@ensures expressions against
 * the TypeScript types they reference. FAIL-CLOSED for detectable problems:
 *
 *   1. Type mismatches: a numeric comparison on a string-typed path, equality
 *      between paths/literals of different primitive kinds, starts_with on a
 *      non-string, ∈-membership against the wrong literal kind. These produce
 *      UNSATISFIABLE Lean hypotheses — every runtime theorem for the function
 *      becomes vacuously "proved".
 *   2. Missing fields: a path that doesn't exist on the parameter's type.
 *   3. Contradictory numeric @requires (e.g. `x > 5` and `x < 3`): the
 *      hypotheses jointly admit no witness.
 *
 * Scope note: only HYPOTHESES (@requires, @ensures) are checked. A mistyped
 * invariant CONCLUSION makes the proof impossible (fail-safe), not vacuous.
 *
 * Best-effort: paths that resolve to `any`/unknown types are skipped — the
 * goal is catching definite bugs, not refusing untypable code.
 */

import { Node, SyntaxKind, Type } from "ts-morph";
import { RequiresAnnotation, EnsuresAnnotation } from "./annotation-parser";
import { AnnotationTranslationError } from "./lean-theorem";

type PathClass = "number" | "string" | "boolean" | "object" | "array" | "unknown";

interface TermInfo {
  kind: "path" | "numLit" | "strLit" | "boolLit" | "other";
  cls: PathClass | null; // resolved class for paths; literal kind otherwise
  text: string;
}

export function checkAnnotationTypes(
  func: Node,
  requires: RequiresAnnotation[],
  ensures: EnsuresAnnotation[],
  functionName: string
): void {
  const paramTypes = collectParamTypes(func);

  // Numeric interval constraints per path, for contradiction detection.
  const intervals = new Map<string, { lo: bigint; hi: bigint }>();

  for (const req of requires) {
    checkRequires(req.prop.trim(), paramTypes, func, functionName, intervals);
  }

  for (const [path, iv] of intervals) {
    if (iv.lo > iv.hi) {
      throw new AnnotationTranslationError(
        functionName,
        "requires",
        path,
        `contradictory numeric @requires constraints on '${path}' — ` +
          `they admit no value (lower bound ${iv.lo} > upper bound ${iv.hi}), ` +
          "so every runtime theorem would be vacuously provable"
      );
    }
  }

  for (const ens of ensures) {
    checkEnsures(ens, paramTypes, func, functionName);
  }
}

// ---------------------------------------------------------------------------

function checkRequires(
  prop: string,
  paramTypes: Map<string, Type>,
  loc: Node,
  functionName: string,
  intervals: Map<string, { lo: bigint; hi: bigint }>
): void {
  const fail = (reason: string): never => {
    throw new AnnotationTranslationError(functionName, "requires", prop, reason);
  };

  const startsWithMatch = prop.match(/^(.+?)\s+starts_with\s+(.+)$/);
  if (startsWithMatch) {
    const left = resolveTerm(startsWithMatch[1], paramTypes, loc, functionName);
    const right = resolveTerm(startsWithMatch[2], paramTypes, loc, functionName);
    for (const side of [left, right]) {
      if (side.kind === "path" && side.cls && side.cls !== "string" && side.cls !== "unknown") {
        fail(`'${side.text}' has type ${side.cls}, but starts_with requires strings`);
      }
      if (side.kind === "numLit" || side.kind === "boolLit") {
        fail(`'${side.text}' is not a string, but starts_with requires strings`);
      }
    }
    return;
  }

  const memMatch = prop.match(/^(.+?)\s*∈\s*\[(.+)\]$/);
  if (memMatch) {
    const left = resolveTerm(memMatch[1], paramTypes, loc, functionName);
    const members = memMatch[2].split(",").map((m) => resolveTerm(m.trim(), paramTypes, loc, functionName));
    const memberKinds = new Set(members.map((m) => m.kind));
    if (left.kind === "path" && left.cls === "string" && memberKinds.has("numLit")) {
      fail(`'${left.text}' is a string but the member list contains numbers — unsatisfiable`);
    }
    if (left.kind === "path" && left.cls === "number" && memberKinds.has("strLit")) {
      fail(`'${left.text}' is a number but the member list contains strings — unsatisfiable`);
    }
    return;
  }

  const cmpMatch = prop.match(/^(.+?)\s*(=|≠|>=|<=|>|<|≥|≤)\s*(.+)$/);
  if (cmpMatch) {
    const [, leftRaw, op, rightRaw] = cmpMatch;
    const left = resolveTerm(leftRaw, paramTypes, loc, functionName);
    const right = resolveTerm(rightRaw, paramTypes, loc, functionName);
    const numericOp = !["=", "≠"].includes(op);

    if (numericOp) {
      // Both sides must be number-classified (the Lean translation demands
      // Val.num on both sides — a string-typed path makes it unsatisfiable).
      for (const side of [left, right]) {
        if (side.kind === "path" && side.cls && side.cls !== "number" && side.cls !== "unknown") {
          fail(
            `'${side.text}' has type ${side.cls}, but '${op}' requires numbers — ` +
              "the generated hypothesis would be unsatisfiable (vacuous theorems)"
          );
        }
        if (side.kind === "strLit" || side.kind === "boolLit") {
          fail(`'${side.text}' is not a number, but '${op}' requires numbers`);
        }
      }
      // Interval bookkeeping for path-vs-literal constraints.
      if (left.kind === "path" && right.kind === "numLit") {
        addBound(intervals, left.text, op, BigInt(right.text));
      } else if (left.kind === "numLit" && right.kind === "path") {
        addBound(intervals, right.text, flipOp(op), BigInt(left.text));
      }
    } else {
      // Equality/disequality: definite kind mismatch is unsatisfiable (=)
      // or trivially true (≠) — both indicate a broken annotation.
      const lk = termKindClass(left);
      const rk = termKindClass(right);
      if (lk && rk && lk !== rk) {
        fail(
          `'${left.text}' (${lk}) and '${right.text}' (${rk}) have different types — ` +
            (op === "=" ? "the hypothesis is unsatisfiable" : "the hypothesis is trivially true")
        );
      }
      if (op === "=" && left.kind === "path" && right.kind === "numLit") {
        addBound(intervals, left.text, "≥", BigInt(right.text));
        addBound(intervals, left.text, "≤", BigInt(right.text));
      }
    }
    return;
  }
}

function checkEnsures(
  ens: EnsuresAnnotation,
  paramTypes: Map<string, Type>,
  loc: Node,
  functionName: string
): void {
  const pred = ens.pred.trim();
  const eqMatch = pred.match(/^(\w+(?:\.\w+)*)\s*(=|≠)\s*(.+)$/);
  if (!eqMatch) return; // unsupported shapes are rejected by the translator

  const [, leftPath, , rightRaw] = eqMatch;
  const bindingType = resolveBindingType(loc, ens.binding);
  if (!bindingType) return; // binding not found / untyped — best-effort skip

  const leftType = resolvePath(bindingType, leftPath.split("."), loc);
  if (leftType === "missing") {
    throw new AnnotationTranslationError(
      functionName,
      "ensures",
      `${ens.binding}.${pred}`,
      `'${ens.binding}.${leftPath}' does not exist on the binding's type — ` +
        "the hypothesis would constrain a field that is never present"
    );
  }
  const lcls = classify(leftType);
  const right = resolveTerm(rightRaw, paramTypes, loc, functionName);
  const rk = termKindClass(right);
  if (lcls !== "unknown" && lcls !== "object" && lcls !== "array" && rk && rk !== lcls) {
    throw new AnnotationTranslationError(
      functionName,
      "ensures",
      `${ens.binding}.${pred}`,
      `'${ens.binding}.${leftPath}' has type ${lcls} but is equated with '${right.text}' (${rk}) — unsatisfiable`
    );
  }
}

// ---------------------------------------------------------------------------

function collectParamTypes(func: Node): Map<string, Type> {
  const map = new Map<string, Type>();
  const params = (func as any).getParameters?.() ?? [];
  for (const p of params) {
    map.set(p.getName(), p.getType());
  }
  return map;
}

/** Resolve the TS type of a dotted path through object properties. */
function resolvePath(start: Type, segs: string[], loc: Node): Type | "missing" {
  let t = start;
  for (const seg of segs) {
    t = stripNullish(t);
    if (classify(t) === "unknown") return t; // any/unknown — stop resolving
    const prop = t.getProperty(seg);
    if (!prop) return "missing";
    t = prop.getTypeAtLocation(loc);
  }
  return t;
}

function stripNullish(t: Type): Type {
  if (!t.isUnion()) return t;
  const parts = t.getUnionTypes().filter((p) => !p.isNull() && !p.isUndefined());
  return parts.length === 1 ? parts[0] : t;
}

function classify(t: Type): PathClass {
  const s = stripNullish(t);
  if (s.isAny() || s.isUnknown()) return "unknown";
  const parts = s.isUnion() ? s.getUnionTypes() : [s];
  if (parts.every((p) => p.isString() || p.isStringLiteral())) return "string";
  if (parts.every((p) => p.isNumber() || p.isNumberLiteral())) return "number";
  if (parts.every((p) => p.isBoolean() || p.isBooleanLiteral())) return "boolean";
  if (s.isArray()) return "array";
  if (s.isObject()) return "object";
  return "unknown";
}

function resolveTerm(raw: string, paramTypes: Map<string, Type>, loc: Node, functionName: string): TermInfo {
  const text = raw.trim();
  if (/^-?\d+$/.test(text)) return { kind: "numLit", cls: "number", text };
  if (text === "true" || text === "false") return { kind: "boolLit", cls: "boolean", text };
  if (
    (text.startsWith('"') && text.endsWith('"')) ||
    (text.startsWith("'") && text.endsWith("'"))
  ) {
    return { kind: "strLit", cls: "string", text };
  }
  if (/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(text)) {
    const [root, ...rest] = text.split(".");
    const rootType = paramTypes.get(root);
    if (!rootType) return { kind: "other", cls: null, text };
    const resolved = resolvePath(rootType, rest, loc);
    if (resolved === "missing") {
      // Treated as a hard error by the caller via cls "missing"? Keep it
      // simple: a missing field on a typed param is always a bug.
      throw new AnnotationTranslationError(
        functionName,
        "requires",
        text,
        `'${text}' does not exist on the parameter's type`
      );
    }
    return { kind: "path", cls: classify(resolved), text };
  }
  return { kind: "other", cls: null, text };
}

function termKindClass(t: TermInfo): PathClass | null {
  if (t.kind === "path") {
    return t.cls && t.cls !== "unknown" && t.cls !== "object" && t.cls !== "array"
      ? t.cls
      : null;
  }
  return t.cls;
}

function flipOp(op: string): string {
  switch (op) {
    case ">": return "<";
    case "<": return ">";
    case ">=": case "≥": return "≤";
    case "<=": case "≤": return "≥";
    default: return op;
  }
}

const INT_MIN = -(2n ** 62n);
const INT_MAX = 2n ** 62n;

function addBound(
  intervals: Map<string, { lo: bigint; hi: bigint }>,
  path: string,
  op: string,
  lit: bigint
): void {
  const iv = intervals.get(path) ?? { lo: INT_MIN, hi: INT_MAX };
  switch (op) {
    case ">": iv.lo = iv.lo > lit + 1n ? iv.lo : lit + 1n; break;
    case "≥": case ">=": iv.lo = iv.lo > lit ? iv.lo : lit; break;
    case "<": iv.hi = iv.hi < lit - 1n ? iv.hi : lit - 1n; break;
    case "≤": case "<=": iv.hi = iv.hi < lit ? iv.hi : lit; break;
  }
  intervals.set(path, iv);
}

/** Find the declared type of a `const <binding> = ...` in the function body. */
function resolveBindingType(func: Node, binding: string): Type | null {
  let found: Type | null = null;
  func.forEachDescendant((node) => {
    if (found) return;
    if (node.getKind() === SyntaxKind.VariableDeclaration) {
      const nameNode = node.getChildren().find((c) => c.getKind() === SyntaxKind.Identifier);
      if (nameNode?.getText() === binding) {
        found = (node as any).getType?.() ?? null;
      }
    }
  });
  return found;
}
