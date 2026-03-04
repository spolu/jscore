declare const logger: {
  info(msg: string): Promise<void>;
};

declare const crypto: {
  // @invariant no-taint: ¬ tainted key in result
  hmac(key: string, data: string): Promise<string>;
};

// @invariant no-secret-in-logs: ¬ tainted secret in call logger.*
async function signAndLog(secret: string, userId: string, action: string) {
  const payload = userId + ":" + action;
  const tokenBlob = secret + ":" + payload;
  const signature = await crypto.hmac(secret, payload);
  const logLine = payload + "|sig:" + signature;
  await logger.info(logLine);
}

declare const unsafeHash: {
  digest(data: string): Promise<string>;
};

// @invariant secret-leaks-to-logs: tainted secret in call logger.*
async function leakyLog(secret: string, userId: string) {
  const tag = await unsafeHash.digest(secret);
  const logLine = userId + ":" + tag;
  await logger.info(logLine);
}
