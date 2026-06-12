// Types for the example
interface Auth {
  workspaceId: string;
  userId: string;
}

// External API namespaces (dotted calls)
declare const db: {
  projects: {
    findMany(query: { where: { workspaceId: string } }): Promise<any[]>;
  };
  tasks: {
    findMany(query: { where: { workspaceId: string } }): Promise<any[]>;
  };
};

// @requires auth.workspaceId starts_with "ws_"
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant read-only: ¬ ∃ call db.*.update
// @invariant read-only: ¬ ∃ call db.*.create
// @invariant read-only: ¬ ∃ call db.*.delete
async function exportWorkspaceData(auth: Auth, format: string) {
  const projects = await db.projects.findMany({
    where: { workspaceId: auth.workspaceId },
  });

  const tasks = await db.tasks.findMany({
    where: { workspaceId: auth.workspaceId },
  });

  return { projects, tasks };
}
