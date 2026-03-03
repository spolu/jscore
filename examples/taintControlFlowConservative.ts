declare const logger: {
  info(msg: string): Promise<void>;
};

// @invariant baseline-unused-source: ¬ tainted unused in call logger.*
// Expected with current implementation: false
// Reason: source appears in control flow (`if (secret)`), so
// `notTaintedIn` fails conservatively even though both logged literals are static.
async function taintControlFlowConservative(secret: string) {
  if (secret) {
    await logger.info("branch-true");
  } else {
    await logger.info("branch-false");
  }
}
