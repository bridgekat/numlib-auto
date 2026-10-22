# Writing a formalization

Formalization is guided by plans, which are subject to repeated amendments during the formalization process. Plans are structured TOML files in the `plans/` directory, one for each Lean module, with [format specified by the tracker tool](../tools/tracker/README.md). Always read [`proof-rubrics.md`](proof-rubrics.md) and follow its guidelines during formalization.

The user can prompt an agent to formalize a plan. In such cases, the orchestrator agent should:

- Use `lake exe tracker ready` to list the modules whose dependencies are all proved, which are the best next steps of formalization.
- Spawn parallel sub-agents to write the actual Lean proofs according to the corresponding TOML plans.
  - Use `tracker show <module>` to show a brief overview of a particular module in the plans.
  - Estimate the amount of work (time, number of lines of Lean code) and try to distribute work evenly among sub-agents.
  - Allow sub-agents to mark `wrong` on problematic planned declarations and amend the plan accordingly.
  - Allow sub-agents to raise suspicions on given tasks, or report negative outcome if any task involves large chunks of unplanned material.
  - If any sub-agent reports a negative outcome, the orchestrator should investigate, restructure the plan, or report back to the user if necessary.
- Before merging a sub-agent's work, have an independent reviewer check its diff. Suggested refactors or improvements that sub-agents report should be addressed when the round of sub-agents finishes.
- Run `lake exe tracker lint` and remove superseded fields in the plan: the Lean files now become the source of truth.
- Verify the formalization by compiling the Lean files and making sure all proofs check with only standard axioms. Then check if there are still `open`, `stated` or `wrong` items via `lake exe tracker status`, and repeat the process for such items.

If a single task is too large, break it down into smaller, self-contained tasks and spawn sub-agents to work on them. At a minimum, provide [`main.md`](main.md), [`proof-rubrics.md`](proof-rubrics.md), and the original text.

Unless explicitly instructed otherwise, the orchestrator itself is allowed to give up on particularly difficult tasks and report issues back to the user. For example, previous experience suggests that 1%-5% numbered items in a textbook may take significantly more time and effort than the rest, some requiring extensive prerequisites out of scope of the book. Such can be skipped as long as they are clearly documented.

# Reviewing a formalization

The review of a formalization may be done at any time after the formalization has begun. This can be prompted by a user, or initiated by a formalizer agent if it thinks the existing formalization needs improvement during the process. Reviews should be done by a fresh agent or an independent sub-agent given the source material, the Lean code itself, [`main.md`](main.md), and [`proof-rubrics.md`](proof-rubrics.md), with little context from the author's reasoning.

The final Lean code should be a polished product.
