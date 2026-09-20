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
| `brezis/planning-brief.md`, `brezis/formalize-brief.md`, `brezis/chNN/report.md`, `brezis/orchestrator.md`, `brezis/waves.md`, `brezis/waveN/*-report.md` | the Brezis round (2026-09-17–): the planning brief with decisions D1–D13 and the module skeleton, the formalizing brief, the twelve chapter reports (inventories, name tables, estimates, errata), the orchestrator's reconciliation ledger, the wave ledger with the merge procedure and the per-agent reports; `brezis/checkplans.py` validates the plan tree without the tracker, `brezis/groupdeps.py` computes a group's outside open deps, `brezis/movenodes.py` moves nodes between plan files, `brezis/mkwt-offline.ps1` finishes a worktree when the network is down | before formalizing any Brezis group; `backbone.md` §21 is the summary |
| `ahqss/brief.md`, `ahqss/ledger.md`, `ahqss/*-report.md` | the Atkinson–Han / QSS closing round (2026-09-20–21): the brief (the Brezis brief's rules with the two source texts, the policies on stale `Blocked:` notes, `C¹`/extension-domain restatements and non-proposition displays), the ledger with every agent task, its merge and the closing state listing the 73 open nodes by blocker, and the 26 per-agent reports; `brezis/absorb.py` accepts the wave name `ahqss` | before touching an open AH/QSS node; `backbone.md` §22 is the summary |
