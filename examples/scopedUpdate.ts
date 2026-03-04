// Types for the example
interface Auth {
  workspaceId: string;
}

// External API namespaces (dotted calls)
declare const db: {
  project: {
    findUnique(query: { where: { id: string; workspaceId: string } }): Promise<any>;
  };
  item: {
    findUnique(query: { where: { id: string } }): Promise<any>;
    update(query: { where: any; data: any }): Promise<any>;
  };
};

// @requires auth.workspaceId > 0
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
async function lookupProject(auth: Auth, projectId: string) {
  const project = await db.project.findUnique({
    where: { id: projectId, workspaceId: auth.workspaceId },
  });

  return project;
}

// @requires auth.workspaceId > 0
// @requires kind = "workspace"
// @invariant scoped-update: ∀ call db.item.update (c) => c.where.workspaceId = auth.workspaceId
async function scopedUpdate(auth: Auth, kind: string, itemId: string) {
  const item = await db.item.findUnique({
    where: { id: itemId },
  });
  // @ensures item.workspaceId = auth.workspaceId

  if (kind === "workspace") {
    await db.item.update({
      where: { id: item.id, workspaceId: item.workspaceId },
      data: { updatedAt: "now" },
    });
  } else {
    await db.item.update({
      where: { id: item.id },
      data: { updatedAt: "now" },
    });
  }
}
