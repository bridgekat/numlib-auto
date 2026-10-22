# Refactoring

Before refactoring, read [`main.md`](main.md) and [`README.md`](../README.md) for shared rules and the layer architecture.

The user can prompt an agent to refactor a formalization. In such cases, the agent should:

- Check existing plans and formalizations for a rough range of contents.
- Write a new plan for the same contents, as if starting from scratch like described in [`plan.md`](plan.md).
- Compare the new plan with the old one, mark the removed planned declarations as `deprecated` in the old plan, and add the new ones to the plan.
- Formalize the new plan in the same way as described in [`proof.md`](proof.md), until `lake exe tracker lint` shows no deprecated planned declarations remaining and the new ones are proved. Consumers of the refactored parts should be fully migrated to the new interfaces.
