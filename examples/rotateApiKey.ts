declare const db: {
  apiKey: {
    update(query: {
      where: { id: string };
      data: { key: string };
    }): Promise<void>;
  };
};

declare function generateKey(): Promise<string>;

declare const logger: {
  info(msg: string): Promise<void>;
};

// @invariant no-secret-leak: ¬ tainted apiKey in call logger.*
async function rotateApiKey(apiKey: string, keyId: string) {
  const newKey = await generateKey();

  await db.apiKey.update({
    where: { id: keyId },
    data: { key: apiKey },
  });

  await logger.info("rotated:" + keyId);
}
