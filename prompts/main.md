# Project

This is a Lean mathematics library with two layers: a general **backbone** and an original-text-matching **surface**, as described in [`README.md`](../README.md). The evolution of the backbone is driven by demands from the surface (statements in original texts) and careful analyses of what can be naturally generalized and reused.

# Collaboration

The user-facing agent is the orchestrator agent, responsible for coordinating sub-agents for each user request. Each sub-agent may launch sub-agents recursively if needed, to which it acts as an orchestrator.

- An orchestrator should always provide sufficient context to its sub-agents, including the following sections:
  - The goal of the task, referencing the relevant prompt files.
  - Supplementary materials, like the original text being formalized or reviewed against.
  - Expected scope of changes. This is a suggestion, not a hard constraint. Let the sub-agent edit in worktrees and resolve conflicts later.
  - Expected working time.
- A sub-agent is always free to finish with either a positive or negative outcome:
  - A positive outcome indicates the completion of the assigned task.
  - A negative outcome indicates the rejection of the assigned task, if it determines the task is ill-specified, impossible, or if its completion would require far more time and effort than anticipated by its creator.
  - Regardless of the task outcome, a sub-agent can also raise suspicions to its creator, and is encouraged to suggest improvements to adjacent code besides its assigned task. If improvements are localized, it can implement them directly.
- An orchestrator should use Git worktrees or otherwise designate a different working directory for each sub-agent, so they do not interfere with each other. After a sub-agent has finished and made changes to its worktree, squash-merge its changes into your branch as a single commit.
- Regardless of role, each agent should base decisions on the overall quality of the project, rather than merely finishing the assigned tasks quickly.

# Prompts

The `prompts/` directory should contain prompts for common workflows. If not, notify the user to take appropriate actions.

- Each formalization request from the user is carried out in two stages.
  - First, TOML plan files in `plans/` should contain complete blueprints for the formalization project.
    - The planning workflow should be guided by [`plan.md`](plan.md).
  - Second, Lean proofs are written against the plans, with further amendments to the plans as needed.
    - The proving workflow should be guided by [`proof.md`](proof.md).
- Each refactoring request from the user should be guided by [`refactor.md`](refactor.md).

# Tools

The environment should have adequate tooling. If not, notify the user to take appropriate actions.

- If Lean LSP or LeanSearch are available via MCP, use them; otherwise, use CLI as a fallback.
- LeanSearch is accessible via CLI at URL `https://leansearch.net/?q=` (followed by query), which provides semantic search across Mathlib that complements local `grep`-like pattern matching; use both to reduce the possibility of duplication.
- Run `lake build` before the first `lake exe tracker` invocation, and rebuild after subsequent Lean changes or merges. The tracker reads compiled `.olean` files without invoking build.
