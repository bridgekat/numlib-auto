# Proof quality rubrics

All mathematical, organizational, and style criteria mentioned in [`plan-rubrics.md`](plan-rubrics.md) also apply to finalized Lean declarations. Address plan rubrics issues surfaced during formalization first, e.g. certain hypotheses or structures in the original plans may turn out to be unnecessary, so a fix for generality is now desired.

## Proof structure rubrics

- Prefer multiple short lemmas rather than rushing to theorems in long proofs.
- Prefer defining and using bundled, named interfaces for a named concept rather than repeating individual assumptions.
- Definitions should have lemmas that characterize it (introduction and elimination forms, `mem_` and `_iff` restatements, `@[simp]` normal forms), so that no proof in another file has to unfold it directly using raw definitions (which are considered as implementation details).
- Identify Mathlib interfaces (e.g. topological spaces, modules, rings) that emerge implicitly from the definitions, and instantiate them eagerly to benefit from Mathlib machinery (e.g. the `ring` tactic and helpful lemmas) and simplify proofs.

## Documentation comments rubrics

- Follow [Mathlib documentation style](https://leanprover-community.github.io/contribute/doc.html).
- References added to [`references/references.bib`](../references/references.bib) can be cited using the syntax described in the above link. Each reference you add must be marked `# GENERATED` to be reviewed by the user.
- Each textbook or paper in the surface library should have an index file importing all chapters, whose module-level doc comment provides an overview of the entire work. Discrepancies with the source material due to fixes, or any parts skipped in the formalization due to scope, should be clearly indicated in the doc comment.
- Doc comments for declarations should be clear and self-contained, easy to read for an outsider having no knowledge about the agents' work process.
- Do not include history of work, internal agent discussions or decision-making processes in the doc comments. Only describe the final Lean declarations as-is.

## Semantic alignment checks

- Each declaration that has a corresponding numbered item in the source material should match exactly against those, except documented fixes for incorrect statements in the source material. Successful compilation establishes neither source faithfulness nor the intended mathematical content. Read the formalization for common pitfalls:
  - Compare surface statements with the cited source and backbone statements with their intended mathematical specification. Inspect the definitions they depend on; matching names or prose is not sufficient.
  - Check quantifier order, implication directions, hypotheses, and zero, empty, or other degenerate cases. Reject vacuous statements caused by unintended impossible assumptions or trivial stand-ins for the intended objects.
  - Do not move a theorem's conclusion into an assumption, axiom, or structure field to make its proof succeed. Check that dependent definitions preserve the intended meaning rather than hiding the claim being proved.
