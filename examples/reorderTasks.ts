interface Auth {
  workspaceId: string;
  userId: string;
}

declare const db: {
  task: {
    update(query: {
      where: { id: string; projectId: string };
      data: { position: number };
    }): Promise<void>;
  };
};

// @invariant scope-limited: ∀ call db.* (c) => c.where.projectId = projectId
async function reorderTasks(
  auth: Auth,
  projectId: string,
  tasks: string[]
) {
  for (const taskId of tasks) {
    await db.task.update({
      where: { id: taskId, projectId: projectId },
      data: { position: 0 },
    });
  }
}
