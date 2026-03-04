/**
 * AST to JSCore₀ — transforms TypeScript AST nodes into JsCoreExpr.
 * This is the largest extractor file (~400 LOC).
 */

import { Node, SyntaxKind, TypeChecker, SourceFile, ts } from "ts-morph";
import { findReassignedVars } from "./reassignment";

// JSCore₀ expression types (mirror the Lean inductive)
export type JsCoreExpr =
  | { tag: "var"; name: string }
  | { tag: "strLit"; value: string }
  | { tag: "numLit"; value: number }
  | { tag: "boolLit"; value: boolean }
  | { tag: "none" }
  | { tag: "letConst"; name: string; value: JsCoreExpr; body: JsCoreExpr }
  | { tag: "letMut"; name: string; value: JsCoreExpr; body: JsCoreExpr }
  | { tag: "assign"; name: string; value: JsCoreExpr; body: JsCoreExpr }
  | { tag: "field"; expr: JsCoreExpr; fieldName: string }
  | { tag: "obj"; fields: [string, JsCoreExpr][] }
  | { tag: "spread"; base: JsCoreExpr; overrides: [string, JsCoreExpr][] }
  | { tag: "arr"; elements: JsCoreExpr[] }
  | { tag: "index"; expr: JsCoreExpr; idx: JsCoreExpr }
  | { tag: "push"; arrName: string; value: JsCoreExpr }
  | { tag: "seq"; first: JsCoreExpr; second: JsCoreExpr }
  | { tag: "ite"; cond: JsCoreExpr; then: JsCoreExpr; else: JsCoreExpr }
  | {
      tag: "forOf";
      varName: string;
      arr: JsCoreExpr;
      body: JsCoreExpr;
    }
  | {
      tag: "whileLoop";
      fuel: number;
      cond: JsCoreExpr;
      body: JsCoreExpr;
    }
  | { tag: "break" }
  | { tag: "ret"; value: JsCoreExpr }
  | {
      tag: "call";
      target: string;
      args: [string, JsCoreExpr][];
      resultBinder: string;
      body: JsCoreExpr;
    }
  | { tag: "throw"; value: JsCoreExpr }
  | {
      tag: "tryCatch";
      body: JsCoreExpr;
      errName: string;
      handler: JsCoreExpr;
    }
  | { tag: "binOp"; op: string; left: JsCoreExpr; right: JsCoreExpr }
  | { tag: "unOp"; op: string; operand: JsCoreExpr }
  | { tag: "sorry"; reason: string };

export interface EnsuresInfo {
  binding: string;
  paramName: string; // "__ensures_<binding>" — the env-bound parameter
}

interface ExtractionContext {
  checker: TypeChecker;
  reassigned: Set<string>;
  freshCounter: number;
  defaultFuel: number;
  ensuresBindings: Set<string>; // bindings that have @ensures annotations
}

function freshName(ctx: ExtractionContext, prefix: string = "__fresh"): string {
  return `${prefix}_${ctx.freshCounter++}`;
}

/**
 * Extract a function body into a JsCoreExpr.
 */
export function extractFunction(
  node: Node,
  checker: TypeChecker,
  defaultFuel: number = 1000,
  ensuresBindings: Set<string> = new Set()
): JsCoreExpr {
  const body = getFunctionBody(node);
  if (!body) {
    return { tag: "sorry", reason: "no function body" };
  }

  const reassigned = findReassignedVars(body);
  const ctx: ExtractionContext = {
    checker,
    reassigned,
    freshCounter: 0,
    defaultFuel,
    ensuresBindings,
  };

  return extractBlock(body, ctx);
}

function getFunctionBody(node: Node): Node | null {
  if (node.getKind() === SyntaxKind.FunctionDeclaration) {
    return (node as any).getBody?.() ?? null;
  }
  if (node.getKind() === SyntaxKind.ArrowFunction) {
    return (node as any).getBody?.() ?? null;
  }
  if (node.getKind() === SyntaxKind.MethodDeclaration) {
    return (node as any).getBody?.() ?? null;
  }
  return null;
}

/**
 * Extract a block (list of statements) into a CPS-threaded JsCoreExpr.
 * Process in reverse: body of each statement is the rest of the block.
 */
function extractBlock(block: Node, ctx: ExtractionContext): JsCoreExpr {
  let children = block.getChildren();
  // A Block node's children are: { SyntaxList }
  // The actual statements are inside the SyntaxList
  const syntaxList = children.find(
    (c) => c.getKind() === SyntaxKind.SyntaxList
  );
  if (syntaxList) {
    children = syntaxList.getChildren();
  }
  const statements = children.filter(isStatement);
  if (statements.length === 0) {
    return { tag: "none" };
  }
  return extractStatements(statements, 0, ctx);
}

function extractStatements(
  stmts: Node[],
  idx: number,
  ctx: ExtractionContext
): JsCoreExpr {
  if (idx >= stmts.length) {
    return { tag: "none" };
  }
  const rest = () => extractStatements(stmts, idx + 1, ctx);
  return extractStatement(stmts[idx], rest, ctx);
}

function isStatement(node: Node): boolean {
  const kind = node.getKind();
  return (
    kind === SyntaxKind.VariableStatement ||
    kind === SyntaxKind.ExpressionStatement ||
    kind === SyntaxKind.IfStatement ||
    kind === SyntaxKind.ForOfStatement ||
    kind === SyntaxKind.ForInStatement ||
    kind === SyntaxKind.WhileStatement ||
    kind === SyntaxKind.ReturnStatement ||
    kind === SyntaxKind.ThrowStatement ||
    kind === SyntaxKind.TryStatement ||
    kind === SyntaxKind.BreakStatement ||
    kind === SyntaxKind.Block
  );
}

function extractStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const kind = stmt.getKind();

  switch (kind) {
    case SyntaxKind.VariableStatement:
      return extractVariableStatement(stmt, rest, ctx);

    case SyntaxKind.ExpressionStatement:
      return extractExpressionStatement(stmt, rest, ctx);

    case SyntaxKind.IfStatement:
      return extractIfStatement(stmt, rest, ctx);

    case SyntaxKind.ForOfStatement:
      return extractForOfStatement(stmt, rest, ctx);

    case SyntaxKind.WhileStatement:
      return extractWhileStatement(stmt, rest, ctx);

    case SyntaxKind.ReturnStatement:
      return extractReturnStatement(stmt, ctx);

    case SyntaxKind.ThrowStatement:
      return extractThrowStatement(stmt, ctx);

    case SyntaxKind.TryStatement:
      return extractTryStatement(stmt, rest, ctx);

    case SyntaxKind.BreakStatement:
      return { tag: "break" };

    case SyntaxKind.Block:
      return {
        tag: "seq",
        first: extractBlock(stmt, ctx),
        second: rest(),
      };

    default:
      return {
        tag: "seq",
        first: { tag: "sorry", reason: `unsupported statement: ${SyntaxKind[kind]}` },
        second: rest(),
      };
  }
}

function extractVariableStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const declList = stmt
    .getChildren()
    .find((c) => c.getKind() === SyntaxKind.VariableDeclarationList);
  if (!declList) return rest();

  const decls = flatChildren(declList)
    .filter((c) => c.getKind() === SyntaxKind.VariableDeclaration);

  let body = rest();

  // Process declarations in reverse for CPS threading
  for (let i = decls.length - 1; i >= 0; i--) {
    const decl = decls[i];
    const children = decl.getChildren();
    const nameNode = children.find((c) => c.getKind() === SyntaxKind.Identifier);
    const name = nameNode?.getText() ?? "__unknown";

    // Check for destructuring
    if (children[0]?.getKind() === SyntaxKind.ObjectBindingPattern) {
      body = extractDestructuring(children[0], decl, body, ctx);
      continue;
    }

    const initializer = children.find(
      (c) =>
        c.getKind() !== SyntaxKind.Identifier &&
        c.getKind() !== SyntaxKind.ColonToken &&
        c.getKind() !== SyntaxKind.EqualsToken &&
        !isTypeNode(c)
    );

    const value = initializer
      ? extractExpr(initializer, ctx)
      : { tag: "none" as const };

    // Check if this is an await call
    if (isAwaitCall(initializer)) {
      const callInfo = extractAwaitCall(initializer!, ctx);
      // If this binding has @ensures, split: call binds a void name,
      // then letConst binds the real name from an ensures parameter.
      if (ctx.ensuresBindings.has(name)) {
        const callBinder = freshName(ctx, "__call");
        const ensuresParam = `__ensures_${name}`;
        body = {
          tag: "call",
          target: callInfo.target,
          args: callInfo.args,
          resultBinder: callBinder,
          body: {
            tag: "letConst",
            name,
            value: { tag: "var", name: ensuresParam },
            body,
          },
        };
      } else {
        body = {
          tag: "call",
          target: callInfo.target,
          args: callInfo.args,
          resultBinder: name,
          body,
        };
      }
      continue;
    }

    const isLet = declList.getText().startsWith("let ");
    if (isLet && ctx.reassigned.has(name)) {
      body = { tag: "letMut", name, value, body };
    } else {
      body = { tag: "letConst", name, value, body };
    }
  }

  return body;
}

function extractDestructuring(
  pattern: Node,
  decl: Node,
  body: JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = decl.getChildren();
  const initializer = children.find(
    (c) =>
      c.getKind() !== SyntaxKind.ObjectBindingPattern &&
      c.getKind() !== SyntaxKind.EqualsToken &&
      !isTypeNode(c)
  );
  const source = initializer
    ? extractExpr(initializer, ctx)
    : { tag: "none" as const };

  const tempName = freshName(ctx, "__destr");
  let innerBody = body;

  const elements = pattern
    .getChildren()
    .filter((c) => c.getKind() === SyntaxKind.BindingElement);

  for (let i = elements.length - 1; i >= 0; i--) {
    const elem = elements[i];
    const propName =
      elem.getChildren().find((c) => c.getKind() === SyntaxKind.Identifier)
        ?.getText() ?? "__unknown";
    innerBody = {
      tag: "letConst",
      name: propName,
      value: { tag: "field", expr: { tag: "var", name: tempName }, fieldName: propName },
      body: innerBody,
    };
  }

  return {
    tag: "letConst",
    name: tempName,
    value: source,
    body: innerBody,
  };
}

function extractExpressionStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = stmt.getChildren().filter(
    (c) => c.getKind() !== SyntaxKind.SemicolonToken
  );

  if (children.length === 0) return rest();
  const expr = children[0];

  // Check for assignment: x = value
  if (
    expr.getKind() === SyntaxKind.BinaryExpression
  ) {
    const binChildren = expr.getChildren();
    if (binChildren.length >= 3 && binChildren[1].getKind() === SyntaxKind.EqualsToken) {
      const left = binChildren[0];
      if (left.getKind() === SyntaxKind.Identifier) {
        return {
          tag: "assign",
          name: left.getText(),
          value: extractExpr(binChildren[2], ctx),
          body: rest(),
        };
      }
    }
  }

  // Check for await call as expression statement
  if (isAwaitCall(expr)) {
    const callInfo = extractAwaitCall(expr, ctx);
    const tempName = freshName(ctx, "__void");
    return {
      tag: "call",
      target: callInfo.target,
      args: callInfo.args,
      resultBinder: tempName,
      body: rest(),
    };
  }

  // Check for .push()
  if (
    expr.getKind() === SyntaxKind.CallExpression
  ) {
    const callText = expr.getText();
    const pushMatch = callText.match(/^(\w+)\.push\(/);
    if (pushMatch) {
      const arrName = pushMatch[1];
      const callChildren = expr.getChildren();
      const args = callChildren.find(
        (c) => c.getKind() === SyntaxKind.SyntaxList
      );
      const argExpr = args?.getChildren()[0];
      return {
        tag: "seq",
        first: {
          tag: "push",
          arrName,
          value: argExpr
            ? extractExpr(argExpr, ctx)
            : { tag: "none" },
        },
        second: rest(),
      };
    }
  }

  return {
    tag: "seq",
    first: extractExpr(expr, ctx),
    second: rest(),
  };
}

function extractIfStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = stmt.getChildren();
  // Find condition (in parentheses), then block, optional else
  const condExpr = children.find(
    (c) =>
      c.getKind() !== SyntaxKind.IfKeyword &&
      c.getKind() !== SyntaxKind.OpenParenToken &&
      c.getKind() !== SyntaxKind.CloseParenToken &&
      c.getKind() !== SyntaxKind.ElseKeyword &&
      c.getKind() !== SyntaxKind.Block &&
      c.getKind() !== SyntaxKind.IfStatement
  );
  const blocks = children.filter(
    (c) => c.getKind() === SyntaxKind.Block || c.getKind() === SyntaxKind.IfStatement
  );

  const cond = condExpr
    ? extractExpr(condExpr, ctx)
    : { tag: "boolLit" as const, value: true };

  const thenBranch = blocks[0]
    ? extractBlock(blocks[0], ctx)
    : { tag: "none" as const };

  const elseBranch = blocks[1]
    ? blocks[1].getKind() === SyntaxKind.IfStatement
      ? extractIfStatement(blocks[1], () => ({ tag: "none" as const }), ctx)
      : extractBlock(blocks[1], ctx)
    : { tag: "none" as const };

  return {
    tag: "seq",
    first: { tag: "ite", cond, then: thenBranch, else: elseBranch },
    second: rest(),
  };
}

function extractForOfStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = stmt.getChildren();
  // Find the variable name, iterable expression, and body
  const varDecl = children.find(
    (c) => c.getKind() === SyntaxKind.VariableDeclarationList
  );
  const varName = varDecl
    ? flatChildren(varDecl)
        .find((c) => c.getKind() === SyntaxKind.VariableDeclaration)
        ?.getChildren()
        .find((c) => c.getKind() === SyntaxKind.Identifier)
        ?.getText() ?? "__iter"
    : "__iter";

  // Find iterable (expression after 'of')
  const ofIdx = children.findIndex((c) => c.getKind() === SyntaxKind.OfKeyword);
  const iterableExpr = ofIdx >= 0 ? children[ofIdx + 1] : null;
  const bodyBlock = children.find((c) => c.getKind() === SyntaxKind.Block);

  return {
    tag: "seq",
    first: {
      tag: "forOf",
      varName,
      arr: iterableExpr
        ? extractExpr(iterableExpr, ctx)
        : { tag: "arr", elements: [] },
      body: bodyBlock
        ? extractBlock(bodyBlock, ctx)
        : { tag: "none" },
    },
    second: rest(),
  };
}

function extractWhileStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = stmt.getChildren();
  const condExpr = children.find(
    (c) =>
      c.getKind() !== SyntaxKind.WhileKeyword &&
      c.getKind() !== SyntaxKind.OpenParenToken &&
      c.getKind() !== SyntaxKind.CloseParenToken &&
      c.getKind() !== SyntaxKind.Block
  );
  const bodyBlock = children.find((c) => c.getKind() === SyntaxKind.Block);

  // Check for @fuel annotation in preceding comments
  let fuel = ctx.defaultFuel;
  const leadingComments = stmt.getLeadingCommentRanges();
  for (const comment of leadingComments) {
    const text = comment.getText();
    const fuelMatch = text.match(/@fuel\s+(\d+)/);
    if (fuelMatch) {
      fuel = parseInt(fuelMatch[1], 10);
    }
  }

  return {
    tag: "seq",
    first: {
      tag: "whileLoop",
      fuel,
      cond: condExpr
        ? extractExpr(condExpr, ctx)
        : { tag: "boolLit", value: true },
      body: bodyBlock
        ? extractBlock(bodyBlock, ctx)
        : { tag: "none" },
    },
    second: rest(),
  };
}

function extractReturnStatement(stmt: Node, ctx: ExtractionContext): JsCoreExpr {
  const children = stmt.getChildren();
  const expr = children.find(
    (c) =>
      c.getKind() !== SyntaxKind.ReturnKeyword &&
      c.getKind() !== SyntaxKind.SemicolonToken
  );
  return {
    tag: "ret",
    value: expr ? extractExpr(expr, ctx) : { tag: "none" },
  };
}

function extractThrowStatement(stmt: Node, ctx: ExtractionContext): JsCoreExpr {
  const children = stmt.getChildren();
  const expr = children.find(
    (c) =>
      c.getKind() !== SyntaxKind.ThrowKeyword &&
      c.getKind() !== SyntaxKind.SemicolonToken
  );
  return {
    tag: "throw",
    value: expr ? extractExpr(expr, ctx) : { tag: "strLit", value: "unknown error" },
  };
}

function extractTryStatement(
  stmt: Node,
  rest: () => JsCoreExpr,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = stmt.getChildren();
  const tryBlock = children.find((c) => c.getKind() === SyntaxKind.Block);
  const catchClause = children.find(
    (c) => c.getKind() === SyntaxKind.CatchClause
  );

  const tryBody = tryBlock
    ? extractBlock(tryBlock, ctx)
    : { tag: "none" as const };

  if (!catchClause) {
    return { tag: "seq", first: tryBody, second: rest() };
  }

  const catchChildren = catchClause.getChildren();
  const catchParam = catchChildren
    .find((c) => c.getKind() === SyntaxKind.VariableDeclaration)
    ?.getChildren()
    .find((c) => c.getKind() === SyntaxKind.Identifier)
    ?.getText() ?? "__err";
  const catchBlock = catchChildren.find((c) => c.getKind() === SyntaxKind.Block);

  return {
    tag: "seq",
    first: {
      tag: "tryCatch",
      body: tryBody,
      errName: catchParam,
      handler: catchBlock
        ? extractBlock(catchBlock, ctx)
        : { tag: "none" },
    },
    second: rest(),
  };
}

/**
 * Extract an expression node into JsCoreExpr.
 */
function extractExpr(node: Node, ctx: ExtractionContext): JsCoreExpr {
  const kind = node.getKind();

  switch (kind) {
    case SyntaxKind.Identifier:
      return { tag: "var", name: node.getText() };

    case SyntaxKind.StringLiteral:
    case SyntaxKind.NoSubstitutionTemplateLiteral:
      return {
        tag: "strLit",
        value: node.getText().slice(1, -1), // remove quotes
      };

    case SyntaxKind.NumericLiteral:
      return { tag: "numLit", value: parseInt(node.getText(), 10) };

    case SyntaxKind.TrueKeyword:
      return { tag: "boolLit", value: true };

    case SyntaxKind.FalseKeyword:
      return { tag: "boolLit", value: false };

    case SyntaxKind.NullKeyword:
    case SyntaxKind.UndefinedKeyword:
      return { tag: "none" };

    case SyntaxKind.PropertyAccessExpression: {
      const children = node.getChildren();
      const obj = children[0];
      const prop = children[children.length - 1];
      return {
        tag: "field",
        expr: extractExpr(obj, ctx),
        fieldName: prop.getText(),
      };
    }

    case SyntaxKind.ObjectLiteralExpression: {
      const props = flatChildren(node).filter(
        (c) =>
          c.getKind() === SyntaxKind.PropertyAssignment ||
          c.getKind() === SyntaxKind.ShorthandPropertyAssignment ||
          c.getKind() === SyntaxKind.SpreadAssignment
      );

      // Check for spread
      const spreadProp = props.find(
        (p) => p.getKind() === SyntaxKind.SpreadAssignment
      );
      if (spreadProp) {
        const spreadExpr = spreadProp.getChildren().find(
          (c) => c.getKind() !== SyntaxKind.DotDotDotToken
        );
        const overrides = props
          .filter((p) => p.getKind() !== SyntaxKind.SpreadAssignment)
          .map((p) => extractObjectProp(p, ctx));
        return {
          tag: "spread",
          base: spreadExpr
            ? extractExpr(spreadExpr, ctx)
            : { tag: "none" },
          overrides,
        };
      }

      return {
        tag: "obj",
        fields: props.map((p) => extractObjectProp(p, ctx)),
      };
    }

    case SyntaxKind.ArrayLiteralExpression: {
      const elements = flatChildren(node).filter(
        (c) =>
          c.getKind() !== SyntaxKind.OpenBracketToken &&
          c.getKind() !== SyntaxKind.CloseBracketToken &&
          c.getKind() !== SyntaxKind.CommaToken
      );
      return {
        tag: "arr",
        elements: elements.map((e) => extractExpr(e, ctx)),
      };
    }

    case SyntaxKind.ElementAccessExpression: {
      const children = node.getChildren();
      return {
        tag: "index",
        expr: extractExpr(children[0], ctx),
        idx: children.length > 2
          ? extractExpr(children[2], ctx)
          : { tag: "numLit", value: 0 },
      };
    }

    case SyntaxKind.TemplateExpression: {
      // Template literal: `${a}:${b}` → strConcat
      return extractTemplateLiteral(node, ctx);
    }

    case SyntaxKind.BinaryExpression: {
      const children = node.getChildren();
      if (children.length >= 3) {
        const op = children[1];
        const left = extractExpr(children[0], ctx);
        const right = extractExpr(children[2], ctx);

        // Handle && and ||
        if (op.getKind() === SyntaxKind.AmpersandAmpersandToken) {
          return { tag: "ite", cond: left, then: right, else: { tag: "boolLit", value: false } };
        }
        if (op.getKind() === SyntaxKind.BarBarToken) {
          const temp = freshName(ctx, "__or");
          return {
            tag: "letConst",
            name: temp,
            value: left,
            body: {
              tag: "ite",
              cond: { tag: "var", name: temp },
              then: { tag: "var", name: temp },
              else: right,
            },
          };
        }

        return {
          tag: "binOp",
          op: binaryOpToJsCore(op.getKind()),
          left,
          right,
        };
      }
      break;
    }

    case SyntaxKind.PrefixUnaryExpression: {
      const children = node.getChildren();
      if (children.length >= 2) {
        const opKind = children[0].getKind();
        if (opKind === SyntaxKind.ExclamationToken) {
          return { tag: "unOp", op: "not", operand: extractExpr(children[1], ctx) };
        }
        if (opKind === SyntaxKind.MinusToken) {
          return { tag: "unOp", op: "neg", operand: extractExpr(children[1], ctx) };
        }
      }
      break;
    }

    case SyntaxKind.ConditionalExpression: {
      // Ternary: c ? t : f
      const children = node.getChildren();
      if (children.length >= 5) {
        return {
          tag: "ite",
          cond: extractExpr(children[0], ctx),
          then: extractExpr(children[2], ctx),
          else: extractExpr(children[4], ctx),
        };
      }
      break;
    }

    case SyntaxKind.AwaitExpression: {
      // Standalone await (not in assignment context)
      const children = node.getChildren();
      const inner = children.find(
        (c) => c.getKind() !== SyntaxKind.AwaitKeyword
      );
      if (inner) return extractExpr(inner, ctx);
      break;
    }

    case SyntaxKind.ParenthesizedExpression: {
      const children = node.getChildren();
      const inner = children.find(
        (c) =>
          c.getKind() !== SyntaxKind.OpenParenToken &&
          c.getKind() !== SyntaxKind.CloseParenToken
      );
      if (inner) return extractExpr(inner, ctx);
      break;
    }

    case SyntaxKind.AsExpression: {
      // Type assertion: e as T — extract e, ignore T
      const children = node.getChildren();
      return extractExpr(children[0], ctx);
    }

    case SyntaxKind.NonNullExpression: {
      // e! — strip non-null assertion
      const children = node.getChildren();
      return extractExpr(children[0], ctx);
    }
  }

  return { tag: "sorry", reason: `unsupported expression: ${SyntaxKind[kind]}` };
}

function extractObjectProp(
  node: Node,
  ctx: ExtractionContext
): [string, JsCoreExpr] {
  if (node.getKind() === SyntaxKind.ShorthandPropertyAssignment) {
    const name = node.getChildren()[0]?.getText() ?? "__unknown";
    return [name, { tag: "var", name }];
  }

  const children = node.getChildren();
  const keyNode = children[0];
  const key = keyNode?.getKind() === SyntaxKind.StringLiteral
    ? keyNode.getText().slice(1, -1)
    : keyNode?.getText() ?? "__unknown";

  // Value is after the colon — find the colon and take the next non-comma child
  const colonIdx = children.findIndex((c) => c.getKind() === SyntaxKind.ColonToken);
  const valueNode = colonIdx >= 0
    ? children.slice(colonIdx + 1).find((c) => c.getKind() !== SyntaxKind.CommaToken)
    : undefined;

  return [key, valueNode ? extractExpr(valueNode, ctx) : { tag: "var", name: key }];
}

function extractTemplateLiteral(
  node: Node,
  ctx: ExtractionContext
): JsCoreExpr {
  const children = node.getChildren();
  let result: JsCoreExpr = { tag: "strLit", value: "" };

  for (const child of children) {
    if (child.getKind() === SyntaxKind.TemplateHead) {
      const text = child.getText().slice(1, -2); // remove ` and ${
      if (text) {
        result = { tag: "strLit", value: text };
      }
    } else if (child.getKind() === SyntaxKind.TemplateSpan) {
      const spanChildren = child.getChildren();
      const expr = spanChildren[0];
      const tail = spanChildren.find(
        (c) =>
          c.getKind() === SyntaxKind.TemplateTail ||
          c.getKind() === SyntaxKind.TemplateMiddle
      );

      const exprJsCore = expr ? extractExpr(expr, ctx) : { tag: "none" as const };
      result = {
        tag: "binOp",
        op: "strConcat",
        left: result,
        right: exprJsCore,
      };

      if (tail) {
        const tailText =
          tail.getKind() === SyntaxKind.TemplateTail
            ? tail.getText().slice(1, -1)
            : tail.getText().slice(1, -2);
        if (tailText) {
          result = {
            tag: "binOp",
            op: "strConcat",
            left: result,
            right: { tag: "strLit", value: tailText },
          };
        }
      }
    }
  }

  return result;
}

function isAwaitCall(node: Node | undefined | null): boolean {
  if (!node) return false;
  if (node.getKind() === SyntaxKind.AwaitExpression) return true;
  return node.getChildren().some((c) => c.getKind() === SyntaxKind.AwaitExpression);
}

function extractAwaitCall(
  node: Node,
  ctx: ExtractionContext
): { target: string; args: [string, JsCoreExpr][] } {
  // Unwrap await
  let callExpr = node;
  if (callExpr.getKind() === SyntaxKind.AwaitExpression) {
    callExpr =
      callExpr
        .getChildren()
        .find((c) => c.getKind() !== SyntaxKind.AwaitKeyword) ?? callExpr;
  }

  // Get target (the function being called)
  const children = callExpr.getChildren();
  const targetNode = children[0];
  const target = targetNode?.getText() ?? "__unknown";

  // Get arguments
  const argsList = children.find(
    (c) => c.getKind() === SyntaxKind.SyntaxList
  );
  const args: [string, JsCoreExpr][] = [];

  if (argsList) {
    const argNodes = argsList
      .getChildren()
      .filter((c) => c.getKind() !== SyntaxKind.CommaToken);

    for (let i = 0; i < argNodes.length; i++) {
      const argNode = argNodes[i];
      // If argument is an object literal, use its properties as named args
      if (argNode.getKind() === SyntaxKind.ObjectLiteralExpression) {
        const props = flatChildren(argNode).filter(
          (c) =>
            c.getKind() === SyntaxKind.PropertyAssignment ||
            c.getKind() === SyntaxKind.ShorthandPropertyAssignment
        );
        for (const prop of props) {
          args.push(extractObjectProp(prop, ctx));
        }
      } else {
        args.push([`arg${i}`, extractExpr(argNode, ctx)]);
      }
    }
  }

  return { target, args };
}

function binaryOpToJsCore(kind: SyntaxKind): string {
  switch (kind) {
    case SyntaxKind.EqualsEqualsEqualsToken:
    case SyntaxKind.EqualsEqualsToken:
      return "eq";
    case SyntaxKind.ExclamationEqualsEqualsToken:
    case SyntaxKind.ExclamationEqualsToken:
      return "neq";
    case SyntaxKind.LessThanToken:
      return "lt";
    case SyntaxKind.LessThanEqualsToken:
      return "le";
    case SyntaxKind.GreaterThanToken:
      return "gt";
    case SyntaxKind.GreaterThanEqualsToken:
      return "ge";
    case SyntaxKind.PlusToken:
      return "add";
    case SyntaxKind.MinusToken:
      return "sub";
    case SyntaxKind.AsteriskToken:
      return "mul";
    case SyntaxKind.SlashToken:
      return "div";
    case SyntaxKind.PercentToken:
      return "mod";
    default:
      return "add"; // fallback
  }
}

/**
 * Get all descendants at depth 1 or 2, unwrapping SyntaxList nodes.
 * ts-morph wraps collections in SyntaxList — this flattens them out.
 */
function flatChildren(node: Node): Node[] {
  const result: Node[] = [];
  for (const c of node.getChildren()) {
    if (c.getKind() === SyntaxKind.SyntaxList) {
      result.push(...c.getChildren());
    } else {
      result.push(c);
    }
  }
  return result;
}


function isTypeNode(node: Node): boolean {
  const kind = node.getKind();
  return (
    kind === SyntaxKind.TypeReference ||
    kind === SyntaxKind.TypeLiteral ||
    kind === SyntaxKind.UnionType ||
    kind === SyntaxKind.IntersectionType ||
    kind === SyntaxKind.ArrayType ||
    kind === SyntaxKind.TupleType ||
    kind === SyntaxKind.StringKeyword ||
    kind === SyntaxKind.NumberKeyword ||
    kind === SyntaxKind.BooleanKeyword ||
    kind === SyntaxKind.VoidKeyword ||
    kind === SyntaxKind.AnyKeyword
  );
}
