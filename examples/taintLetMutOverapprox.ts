declare const logger: {
  secretPath(msg: string): Promise<void>;
  public(msg: string): Promise<void>;
};

// @invariant baseline-unused-source: ¬ tainted unused in call logger.*
// Expected with current implementation: false (conservative)
// Reason: source appears in program + mutable assignment over-approximation.
// A path-sensitive control-dependence analysis could accept this for `logger.public`.
async function taintLetMutOverapprox(secret: string, rare: boolean) {
  let msg = "public";
  if (rare) {
    msg = secret;
    await logger.secretPath(msg);
  } else {
    await logger.public(msg);
  }
}
