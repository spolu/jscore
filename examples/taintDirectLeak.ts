declare const logger: {
  info(msg: string): Promise<void>;
};

// @invariant baseline-unused-source: ¬ tainted unused in call logger.*
// Expected: false (direct data flow from secret to logger argument)
async function taintDirectLeak(secret: string) {
  await logger.info(secret);
}
