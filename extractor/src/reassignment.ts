/**
 * Reassignment analysis — determines which `let`-declared names are ever reassigned.
 * This determines whether a binding becomes `letConst` or `letMut` in JSCore₀.
 */

import { Node, SyntaxKind, FunctionDeclaration, ArrowFunction, MethodDeclaration } from "ts-morph";

/**
 * Walk a function body and build the set of `let`-declared names that are reassigned.
 */
export function findReassignedVars(
  body: Node
): Set<string> {
  const reassigned = new Set<string>();
  walkForReassignments(body, reassigned);
  return reassigned;
}

/**
 * Walk a function body and build the set of names mutated via `.push(...)`.
 * JS allows `const arr = []; arr.push(x)`, but JSCore₀'s `push` writes the
 * updated array into the mutable Store — so a pushed array MUST be bound with
 * `letMut`, regardless of `const`/`let` in the source. Otherwise the binding
 * would live in Env while its mutations live in Store, breaking the
 * Env/Store-disjointness invariant that `env_stable` and the generated
 * `h_store_* = none` hypotheses rely on.
 */
export function findPushedVars(body: Node): Set<string> {
  const pushed = new Set<string>();
  walkForPushes(body, pushed);
  return pushed;
}

function walkForPushes(node: Node, pushed: Set<string>): void {
  if (node.getKind() === SyntaxKind.CallExpression) {
    const callee = node.getChildren()[0];
    if (callee && callee.getKind() === SyntaxKind.PropertyAccessExpression) {
      const parts = callee.getChildren();
      // <expr> . <name> — last child is the property name
      const propName = parts[parts.length - 1];
      const receiver = parts[0];
      if (
        propName?.getText() === "push" &&
        receiver?.getKind() === SyntaxKind.Identifier
      ) {
        pushed.add(receiver.getText());
      }
    }
  }

  // Don't recurse into nested function declarations/arrows
  if (
    node.getKind() === SyntaxKind.FunctionDeclaration ||
    node.getKind() === SyntaxKind.ArrowFunction ||
    node.getKind() === SyntaxKind.FunctionExpression
  ) {
    return;
  }

  for (const child of node.getChildren()) {
    walkForPushes(child, pushed);
  }
}

function walkForReassignments(node: Node, reassigned: Set<string>): void {
  // Binary expression with = operator (assignment)
  if (node.getKind() === SyntaxKind.BinaryExpression) {
    const binary = node;
    const children = binary.getChildren();
    // children[1] is the operator token
    if (children.length >= 3) {
      const opToken = children[1];
      if (opToken.getKind() === SyntaxKind.EqualsToken) {
        const left = children[0];
        if (left.getKind() === SyntaxKind.Identifier) {
          reassigned.add(left.getText());
        }
      }
      // Also handle +=, -=, etc.
      const compoundOps = [
        SyntaxKind.PlusEqualsToken,
        SyntaxKind.MinusEqualsToken,
        SyntaxKind.AsteriskEqualsToken,
        SyntaxKind.SlashEqualsToken,
        SyntaxKind.PercentEqualsToken,
      ];
      if (compoundOps.includes(opToken.getKind())) {
        const left = children[0];
        if (left.getKind() === SyntaxKind.Identifier) {
          reassigned.add(left.getText());
        }
      }
    }
  }

  // Prefix/Postfix ++ and --
  if (
    node.getKind() === SyntaxKind.PrefixUnaryExpression ||
    node.getKind() === SyntaxKind.PostfixUnaryExpression
  ) {
    const children = node.getChildren();
    for (const child of children) {
      if (child.getKind() === SyntaxKind.Identifier) {
        reassigned.add(child.getText());
      }
    }
  }

  // Don't recurse into nested function declarations/arrows
  if (
    node.getKind() === SyntaxKind.FunctionDeclaration ||
    node.getKind() === SyntaxKind.ArrowFunction ||
    node.getKind() === SyntaxKind.FunctionExpression
  ) {
    return;
  }

  for (const child of node.getChildren()) {
    walkForReassignments(child, reassigned);
  }
}

/**
 * Check if a variable declaration uses `let` (not `const`).
 */
export function isLetDeclaration(node: Node): boolean {
  if (node.getKind() === SyntaxKind.VariableDeclarationList) {
    const text = node.getText();
    return text.startsWith("let ");
  }
  return false;
}
