declare const logger: {
  info(msg: string): Promise<void>;
};

// @invariant no-secret-leak: ¬ tainted secret in call logger.*
// Expected: true (source does not appear in the program)
async function taintSafeLiteral() {
  await logger.info("static log line");
}
