# Contributing

Before anything, make sure to understand the intended roles of the backbone and surface layers as described in [`README.md`](README.md). The evolution of the backbone is driven by demands from the surface (the textbook statements) and careful analyses of what can be naturally generalized and reused.

Each section below is an instruction ("agent skill") for one specific task.

## Writing a plan

To start a formalization project, write a plan specifying its overall shape.

Plans are structured TOML files in the `plans/` directory, with [format specified by the tracker tool](tools/tracker/README.md). Each TOML file corresponds to one Lean module. They should contain:

- Overall design notes, in module `desc` fields.
- A list of key nodes (Lean definitions and theorem statements) in logical progression order. Each backbone node should be placed carefully within the module and namespace hierarchies. Each surface node should be placed in the module `NumlibSurface/<source>/[Chapter<number>]/[Section<number>]`.
- Brief descriptions of difficult proofs, in node `desc` fields.

Plans may be automatically extracted from textbooks. In such cases, the agent should:

- Analyze all book contents, factor out commonalities (similar to finding a minimum spanning tree covering the topics *across all books*).
- Optionally search the web to see if there are more general theorem statements.
- Plan the backbone-surface split, threading general definitions and theorems into a logically coherent spanning tree, putting special forms at the leaves to the surface. The agent is encouraged to form its own opinions on how the material should be organized in the backbone, before adapting the book's content to them.
- Search in Mathlib for existing formalizations to build upon, and vocabulary to reuse.
- Repeat until sufficient understanding is achieved, then write the plan.

Anytime when proposing the plan, the agent can experiment with Lean and Mathlib for prototyping. Type checking Lean files with `sorry` holes to identify if a proposed definition of theorem statement works.

## Reviewing a plan

The review of a plan may be done at any time after the plan is written. This can be prompted by a user, or initiated by a formalizer agent if it thinks the plan needs improvement during the formalization process. Reviews should be done by a fresh agent or an independent sub-agent that inherits little context, better with "adversarial" goals.

In such cases, the agent should:

- Scrutinize the plan, consider proof approaches, explore possible alternative choices, weigh the costs/benefits and suggest improvements.
- Make sure that the project criteria are met, e.g. backbone and surface should be appropriately delineated.
- Make sure everything is carefully named, so that a future uninformed agent can find things using intuitive candidate names.
- Consider typical future demands, e.g. integrating another textbook on the same topic into this project, or formalizing another research paper in the same area using this project. Adjust the plan to reduce anticipated amount of work needed to accommodate for such demands.

Treat the review process as a search for better (structures of) proofs. Think hard on plans, as this may save time and effort in the actual formalization process, and reduce the need for later refactoring when new demands arise. Make sure `lake exe tracker lint` passes on the plan.

## Formalizing

The user can prompt an agent to formalize a plan. In such cases, the agent should:

- Estimate the amount of work, focus on one part of the plan at a time. `lake exe tracker ready` lists the groups whose dependencies are all proved, which are the best next steps of formalization.
- Write the actual Lean proofs according to the corresponding TOML plans, optionally by spawning parallel sub-agents to work on different files. Start each with the output of `tracker show <group>`, tell them to mark `wrong` on problematic plan items and allow them to write their own items. If any of them proves difficult to complete, identify the cause, report back and stop for a restructure of the plan if necessary.
- Run `lake exe tracker lint` and remove superseded fields in the plan: the Lean files now become the source of truth.
- Verify the formalization by compiling the Lean files and running `lake exe tracker check`.

Keep in mind the backbone-surface split. Everything in the backbone (including doc comments) should be self-contained; to reference material from the books, cite the source explicitly instead of writing a mere number like "Theorem 3.7". Mere numbers may be used in surface only.

## Reviewing a formalization

The review of a formalization may be done at any time after the formalization has begun. This can be prompted by a user, or initiated by a formalizer agent if it thinks the existing formalization needs improvement during the process. Reviews should be done by a fresh agent or an independent sub-agent that inherits little context, better with "adversarial" goals.

In such cases, the agent should make sure that the formalization is idiomatic Lean code and pleasant to read, on top of being semantically correct. Some code style guidance:

- Match Mathlib style in general: use notations, tactics, and doc comments in similar ways. By default, follow the same conventions.
- Minimize duplication: something may have been formalized elsewhere in Mathlib or within this project, or the same logic is repeated in multiple proofs.
- Prefer multiple short lemmas rather than rushing to theorems in long proofs.
- Prefer defining and using bundled, named interfaces for a named concept rather than repeating individual assumptions.
- Identify Mathlib interfaces (e.g. topological spaces, modules, rings) that emerge implicitly from the definitions, and instantiate them eagerly to benefit from Mathlib machinery (e.g. the `ring` tactic and helpful lemmas) and simplify proofs.

Finally, check for semantic alignment:

- At surface level, confirm that the definition or theorem statement matches the textbook definition or statement, with no axiomatic or definitional cheats. This includes correct use of dependent definitions or theorems.
- At backbone level, confirm that the definition or theorem statement agrees with the specification in the plan.

## Refactoring

The user can prompt an agent to refactor a formalization. In such cases, the agent should:

- Check existing plans and formalizations for a rough range of contents.
- Write a new plan for the same contents, as if starting from scratch (see [writing a plan](#writing-a-plan)).
- Compare the new plan with the old one, mark the removed items as `deprecated` in the old plan, and add new items to the plan.
- Formalize the new plan in the same way as [formalizing](#formalizing), until `lake exe tracker lint` shows no deprecated items remaining and the new items are finished. Consumers of the refactored parts should be fully migrated to the new interfaces.

## General instructions for agents

- Always run `lake build` before `lake exe tracker ...`: the tracker reads the compiled `.olean` files, so an unbuilt change is invisible to it.
- If Lean LSP or LeanSearch are available via MCP, use them; otherwise, use CLI as a fallback. LeanSearch is accessible via `curl` at `https://leansearch.net/?q=` (followed by query), which provides semantic search across Mathlib that complements local `grep`-like pattern matching; use both to reduce the possibility of duplication.
- For context-clearing operations (including launching sub-agents and context compaction), make sure to link to README.md in the new context, so that the new session or sub-agent reads this file as well.
- If a single task is too large (e.g. analyzing a whole book), break it down into smaller, self-contained tasks and spawn sub-agents to work on them. Give clear instructions on the expected input and output formats to sub-agents, and designate a different working directory for each (so they do not interfere with each other).
- When spawning sub-agents that can modify Lean code in the repository, ensure that (1) the whole project compiles clean before spawning (2) each sub-agent (including yourself) works on a separate worktree or in a temporary directory, *not* touching the original copy. You should handle the merge after all other agents finish their work and none of them is still running.
- In difficult situations, you may spawn sub-agents to explore solutions, but given them an effort limit and ask them to report what works and what does not. You should selectively consolidate their reports into a central record file, which is passed to new sub-agents to avoid repeating the same mistakes.
