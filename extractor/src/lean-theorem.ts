/**
 * Lean Theorem Generator — Annotations → theorem statements.
 *
 * Three invariant shapes:
 *   1. ¬ tainted X in call P  → notTaintedIn body "X" "P" = true       (native_decide)
 *   2. ¬ ∃ call P             → (callExprsIn body "P").length = 0       (native_decide)
 *   3. ∀ call P (c) => pred   → runtime trace property                  (sorry)
 */

import { RequiresAnnotation, InvariantAnnotation } from "./annotation-parser";

interface SyntacticInvariantTranslation {
  kind: "syntactic";
  conclusion: string;
}

interface RuntimeInvariantTranslation {
  kind: "runtime";
  bindVar: string;
  pattern: string;
  predicate: string;
}

type InvariantTranslation =
  | SyntacticInvariantTranslation
  | RuntimeInvariantTranslation;

export interface TheoremGenerationOptions {
  runtimeFuel: number;
  emitCanonicalRuntimeTheorem: boolean;
}

/**
 * Generate a Lean theorem statement from an invariant annotation.
 */
export function generateTheorem(
  functionName: string,
  invariant: InvariantAnnotation,
  requires: RequiresAnnotation[],
  params: string[],
  tagIndex: number = 0,
  options?: TheoremGenerationOptions
): string {
  const tag = sanitizeTag(invariant.tag);
  const thmName =
    tagIndex > 0 ? `${functionName}_${tag}_${tagIndex}` : `${functionName}_${tag}`;

  const translation = translateInvariantToLean(
    invariant.prop,
    functionName,
    params
  );

  if (translation.kind === "syntactic") {
    // Purely syntactic theorem — no fuel/env/store/params needed
    return [
      `theorem ${thmName}`,
      `    : ${translation.conclusion} := by`,
      `  native_decide`,
    ].join("\n");
  }

  // Runtime theorem — needs fuel, env, store, params, and assumptions that
  // avoid store shadowing/under-fueling artifacts.
  const runtimeFuel = Math.max(1, options?.runtimeFuel ?? 8);
  const requireHyps = requires.map((req, idx) =>
    makeRequireHypothesisLine(req, params, idx)
  );

  const lines: string[] = [];
  lines.push(`theorem ${thmName}`);
  lines.push(`    (fuel : Nat)`);
  for (const param of params) {
    lines.push(`    (${param} : Val)`);
  }
  lines.push(`    (env : Env)`);
  lines.push(`    (store : Store)`);

  // Env binding hypotheses: env "param" = some param
  for (const param of params) {
    lines.push(`    (h_env_${param} : env "${param}" = some ${param})`);
  }
  // No-shadowing assumptions: mutable store does not override parameters.
  for (const param of params) {
    lines.push(`    (h_store_${param} : store "${param}" = none)`);
  }
  for (const hyp of requireHyps) {
    lines.push(hyp);
  }
  lines.push(`    (h_fuel : fuel = ${runtimeFuel})`);

  lines.push(
    `    : ${buildRuntimeConclusion(functionName, translation, "fuel", "env", "store")} := by`
  );
  lines.push(`  sorry`);

  if (!options?.emitCanonicalRuntimeTheorem) {
    return lines.join("\n");
  }

  return [lines.join("\n"), "", buildCanonicalRuntimeTheorem({
    theoremName: thmName,
    functionName,
    runtimeInvariant: translation,
    params,
    requires,
    runtimeFuel,
  })].join("\n");
}

/**
 * Translate an invariant proposition to a Lean conclusion.
 * Returns the conclusion string and whether it needs runtime (eval) reasoning.
 */
function translateInvariantToLean(
  prop: string,
  functionName: string,
  params: string[]
): InvariantTranslation {
  prop = prop.trim();

  // ¬ tainted <binding> in call <pattern> → purely syntactic
  const taintMatch = prop.match(
    /^¬\s*tainted\s+(\w+)\s+in\s+call\s+(\S+)/
  );
  if (taintMatch) {
    const [, source, pattern] = taintMatch;
    return {
      kind: "syntactic",
      conclusion: `notTaintedIn ${functionName}_body "${source}" "${pattern}" = true`,
    };
  }

  // ¬ ∃ call <pattern> → purely syntactic (no matching call sites in AST)
  const noCallMatch = prop.match(/^¬\s*∃\s+call\s+(\S+)/);
  if (noCallMatch) {
    const [, pattern] = noCallMatch;
    return {
      kind: "syntactic",
      conclusion: `(callExprsIn ${functionName}_body "${pattern}").length = 0`,
    };
  }

  // ∀ call <pattern> (c) => <pred> → runtime trace property
  const forallMatch = prop.match(
    /^∀\s+call\s+(\S+)\s+\((\w+)\)\s*=>\s*(.+)$/s
  );
  if (forallMatch) {
    const [, pattern, bindVar, pred] = forallMatch;
    return {
      kind: "runtime",
      bindVar,
      pattern,
      predicate: translateCallPred(pred.trim(), bindVar, params),
    };
  }

  return {
    kind: "runtime",
    bindVar: "c",
    pattern: "*",
    predicate: `True /- TODO invariant: ${sanitizeTodo(prop)} -/`,
  };
}

function translateCallPred(
  pred: string,
  callVar: string,
  params: string[]
): string {
  // c.where.workspaceId = auth.workspaceId
  const eqMatch = pred.match(
    /^(\w+(?:\.\w+)*)\s*(=|≠)\s*(\w+(?:\.\w+)*)$/
  );
  if (eqMatch) {
    const [, left, op, right] = eqMatch;
    const leanOp = op === "=" ? "=" : "≠";
    const leanLeft = left.startsWith(callVar + ".")
      ? `argAtPath ${callVar} "${left.slice(callVar.length + 1)}"`
      : translateAccessAsOption(left, params);
    const leanRight = right.startsWith(callVar + ".")
      ? `argAtPath ${callVar} "${right.slice(callVar.length + 1)}"`
      : translateAccessAsOption(right, params);
    return `${leanLeft} ${leanOp} ${leanRight}`;
  }

  return `True /- TODO: ${pred} -/`;
}

/**
 * Translate a dotted access to an Option Val expression.
 * auth.workspaceId → Val.field' auth "workspaceId"
 * Multi-level paths are translated with `Option.bind` chains.
 */
function translateAccessAsOption(path: string, params: string[]): string {
  const parts = path.split(".");
  let current: string;
  if (params.includes(parts[0])) {
    current = `some ${parts[0]}`;
  } else {
    current = `some (Val.str "${escapeLeanString(parts[0])}")`;
  }

  for (const field of parts.slice(1)) {
    current = `Option.bind (${current}) (fun __v => Val.field' __v "${escapeLeanString(field)}")`;
  }
  return current;
}

function buildRuntimeConclusion(
  functionName: string,
  runtimeInvariant: RuntimeInvariantTranslation,
  fuelExpr: string,
  envExpr: string,
  storeExpr: string
): string {
  return `∀ ${runtimeInvariant.bindVar} ∈ callsTo (eval ${fuelExpr} ${envExpr} ${storeExpr} ${functionName}_body).trace "${runtimeInvariant.pattern}",\n      ${runtimeInvariant.predicate}`;
}

interface CanonicalRuntimeTheoremInput {
  theoremName: string;
  functionName: string;
  runtimeInvariant: RuntimeInvariantTranslation;
  params: string[];
  requires: RequiresAnnotation[];
  runtimeFuel: number;
}

function buildCanonicalRuntimeTheorem(input: CanonicalRuntimeTheoremInput): string {
  const {
    theoremName,
    functionName,
    runtimeInvariant,
    params,
    requires,
    runtimeFuel,
  } = input;
  const canonicalName = `${theoremName}_canonical`;
  const canonicalEnv = buildCanonicalEnvExpr(params);
  const requireHyps = requires.map((_, idx) => `h_req_${idx}`);

  const lines: string[] = [];
  lines.push(`theorem ${canonicalName}`);
  lines.push(`    (fuel : Nat)`);
  for (const param of params) {
    lines.push(`    (${param} : Val)`);
  }
  for (let i = 0; i < requires.length; i++) {
    const req = translateRequireToLean(requires[i].prop, params, i);
    lines.push(`    (h_req_${i} : ${req})`);
  }
  lines.push(`    (h_fuel : fuel = ${runtimeFuel})`);
  lines.push(
    `    : ${buildRuntimeConclusion(functionName, runtimeInvariant, "fuel", canonicalEnv, "emptyStore")} := by`
  );
  lines.push(`  intro c hc`);
  lines.push(`  exact ${theoremName}`);
  lines.push(`    fuel`);
  for (const param of params) {
    lines.push(`    ${param}`);
  }
  lines.push(`    ${canonicalEnv}`);
  lines.push(`    emptyStore`);
  for (const param of params) {
    lines.push(`    (by simp [Env.set, emptyEnv])`);
  }
  for (const _param of params) {
    lines.push(`    (by simp [emptyStore])`);
  }
  for (const reqHyp of requireHyps) {
    lines.push(`    ${reqHyp}`);
  }
  lines.push(`    h_fuel`);
  lines.push(`    c`);
  lines.push(`    hc`);

  return lines.join("\n");
}

function buildCanonicalEnvExpr(params: string[]): string {
  return params.reduce(
    (acc, param) => `(${acc}.set "${param}" ${param})`,
    "emptyEnv"
  );
}

function makeRequireHypothesisLine(
  req: RequiresAnnotation,
  params: string[],
  reqIndex: number
): string {
  const reqProp = translateRequireToLean(req.prop, params, reqIndex);
  return `    (h_req_${reqIndex} : ${reqProp})`;
}

function translateRequireToLean(
  prop: string,
  params: string[],
  reqIndex: number
): string {
  const trimmed = prop.trim();

  const startsWithMatch = trimmed.match(/^(.+?)\s+starts_with\s+(.+)$/);
  if (startsWithMatch) {
    const [, leftRaw, rightRaw] = startsWithMatch;
    const left = parseTermAsOption(leftRaw, params);
    const right = parseTermAsOption(rightRaw, params);
    if (left && right) {
      return `match ${left}, ${right} with | some __lhs, some __rhs => Val.startsWith' __lhs __rhs = true | _, _ => False`;
    }
  }

  const memMatch = trimmed.match(/^(.+?)\s*∈\s*\[(.+)\]$/);
  if (memMatch) {
    const [, leftRaw, membersRaw] = memMatch;
    const left = parseTermAsOption(leftRaw, params);
    const members = splitListItems(membersRaw)
      .map((item) => parseTermAsVal(item, params))
      .filter((item): item is string => item !== null);
    if (left && members.length > 0) {
      return `match ${left} with | some __lhs => Val.mem' __lhs [${members.join(", ")}] = true | none => False`;
    }
  }

  const cmpMatch = trimmed.match(/^(.+?)\s*(=|≠|>=|<=|>|<|≥|≤)\s*(.+)$/);
  if (cmpMatch) {
    const [, leftRaw, opRaw, rightRaw] = cmpMatch;
    const left = parseTermAsOption(leftRaw, params);
    const right = parseTermAsOption(rightRaw, params);
    const op = normalizeIneqOp(opRaw);
    if (left && right) {
      if (op === "=" || op === "≠") {
        return `${left} ${op} ${right}`;
      }

      const leftVar = `__n_lhs_${reqIndex}`;
      const rightVar = `__n_rhs_${reqIndex}`;
      return `∃ ${leftVar} ${rightVar}, ${left} = some (Val.num ${leftVar}) ∧ ${right} = some (Val.num ${rightVar}) ∧ ${leftVar} ${op} ${rightVar}`;
    }
  }

  return `True /- TODO @requires: ${sanitizeTodo(trimmed)} -/`;
}

function normalizeIneqOp(op: string): string {
  switch (op) {
    case ">=":
      return "≥";
    case "<=":
      return "≤";
    default:
      return op;
  }
}

function parseTermAsOption(term: string, params: string[]): string | null {
  const trimmed = term.trim();
  const numMatch = trimmed.match(/^-?\d+$/);
  if (numMatch) {
    return `some (Val.num ${trimmed})`;
  }

  if (trimmed === "true" || trimmed === "false") {
    return `some (Val.bool ${trimmed})`;
  }

  const stringLiteral = parseStringLiteral(trimmed);
  if (stringLiteral !== null) {
    return `some (Val.str "${escapeLeanString(stringLiteral)}")`;
  }

  if (/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(trimmed)) {
    return translateAccessAsOption(trimmed, params);
  }

  return null;
}

function parseTermAsVal(term: string, params: string[]): string | null {
  const trimmed = term.trim();
  const numMatch = trimmed.match(/^-?\d+$/);
  if (numMatch) {
    return `Val.num ${trimmed}`;
  }

  if (trimmed === "true" || trimmed === "false") {
    return `Val.bool ${trimmed}`;
  }

  const stringLiteral = parseStringLiteral(trimmed);
  if (stringLiteral !== null) {
    return `Val.str "${escapeLeanString(stringLiteral)}"`;
  }

  if (params.includes(trimmed)) {
    return trimmed;
  }

  return null;
}

function parseStringLiteral(term: string): string | null {
  if (term.length >= 2 && term.startsWith("\"") && term.endsWith("\"")) {
    return term.slice(1, -1);
  }
  if (term.length >= 2 && term.startsWith("'") && term.endsWith("'")) {
    return term.slice(1, -1);
  }
  return null;
}

function splitListItems(items: string): string[] {
  return items
    .split(",")
    .map((item) => item.trim())
    .filter((item) => item.length > 0);
}

function escapeLeanString(s: string): string {
  return s
    .replace(/\\/g, "\\\\")
    .replace(/"/g, '\\"')
    .replace(/\n/g, "\\n")
    .replace(/\t/g, "\\t");
}

function sanitizeTodo(text: string): string {
  return text.replace(/-\//g, "- /");
}

function sanitizeTag(tag: string): string {
  return tag.replace(/[^a-zA-Z0-9_]/g, "_").replace(/-/g, "_");
}
