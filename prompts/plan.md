# Writing a plan

To start a formalization project, write a plan specifying its overall shape. Plans are structured TOML files in the `plans/` directory, one for each Lean module, with [format specified by the tracker tool](../tools/tracker/README.md). Always read [`plan-rubrics.md`](plan-rubrics.md) and follow its guidelines during planning.

Plans are typically extracted from textbooks or papers. In such cases, the orchestrator agent should:

- Analyze all book contents, factor out commonalities (similar to finding a minimum spanning tree covering the topics *across all books*).
- Optionally search the web to see if there are more general theorem statements.
- Plan the backbone-surface split, threading general definitions and theorems into a logically coherent spanning tree, putting special forms at the leaves to the surface. The agent is encouraged to form its own opinions on how the material should be organized in the backbone, before adapting the book's content to them.
- Search in Mathlib for existing formalizations to build upon, and vocabulary to reuse.
- Repeat until sufficient understanding is achieved, then write the plan.

Anytime when proposing the plan, the agent can experiment with Lean and Mathlib for prototyping. Type checking Lean files with `sorry` holes to identify if a proposed definition of theorem statement works.

If a single task is too large (e.g. analyzing a whole textbook), break it down into smaller, self-contained tasks and spawn sub-agents to work on them. At a minimum, provide [`main.md`](main.md), [`plan-rubrics.md`](plan-rubrics.md), and the original text.

# Reviewing a plan

The review of a plan may be done at any time after the plan is written. This can be prompted by a user, or initiated by a formalizer agent if it thinks the plan needs improvement during the formalization process. Reviews should be done by a fresh agent or an independent sub-agent given the source material, the plan itself, [`main.md`](main.md), and [`plan-rubrics.md`](plan-rubrics.md), with little context from the author's reasoning.

Treat the review process as a search for better (structures of) proofs. Think hard on plans, as this may save time and effort in the actual formalization process, and reduce the need for later refactoring when new demands arise.
