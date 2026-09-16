# Notes

Local, gitignored working notes for the formalization project. The orchestrator gives sub-agents
their detailed instructions through files here, sub-agents' lessons are summarized into them, and
the orchestrator prunes them between rounds so that no agent has to read history to work.

Pruned 2026-09-16: the thirteen per-chapter planning reports and Lean prototypes of the
Quarteroni–Sacco–Saleri round (`qss/chNN/`, no longer cited by any plan), the planning brief, the
orchestrator's wave ledger, and the `tdaf-dedup/` scripts of the convex-library merge. The git log
carries what they recorded.

| file | what it is | read it when |
|---|---|---|
| `qss/formalize-brief.md` | the sub-agent brief: reading order, worktree rules, build discipline, standards, finishing steps, report format, and the operational traps that have destroyed files | every sub-agent, first |
| `lessons.md` | what agents learned about Mathlib at this pin, the toolchain, proof routes, and (last section) orchestration | every sub-agent — skim the headings, read what touches the topic |
| `frontier.md` | **the current triage of every open node by the mathematics it needs**, with blocker numbers that plan descriptions cite | deciding what to formalize next |
| `fem-roadmap.md` | the reading list and design decisions for frontier blockers 1 and 2 (Sobolev structure theory, the boundary) | before starting on either |
| `followups.md` | work owed elsewhere: relocations, duplicates, upstreaming candidates, the tracker defect | refactor rounds; agents add to it through their reports |
| `book-errata.md` | every place a book was found wrong, with the counterexample and what the library states instead | any agent touching that section of that book |
| `backbone.md` | the design record of the backbone: conventions (§1), and the planning rounds by which it grew | when a plan `desc` points you to a section; §1 always |
