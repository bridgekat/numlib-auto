# numlib-auto

[![Lean Action CI](https://github.com/bridgekat/numlib-auto/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/bridgekat/numlib-auto/actions/workflows/lean_action_ci.yml)

An LLM-generated numerical analysis library, with two layers: a general **backbone** and a textbook-matching **surface**.

[Read the full documentation here.](https://bridgekat.github.io/numlib-auto/docs/Numlib.html)

## The backbone

The backbone aims to be a foundational library similar to Mathlib, despite being LLM-generated: we seek generality of theorem statements, modularity of the structure, and completeness of API coverage.

It contains the *canonical* definitions and *actual* proofs for theorems, with theorem statements in their *natural and general* forms. Proofs are often simpler and more modular in such forms.

The natural level of generality at the backbone is often determined by *which structures are being used* downstream. For example, if a textbook theory utilizes only the vector space and topological structure of $\mathbb R^n$, it may be generalized to Banach spaces, or even topological vector spaces. This is similar to preferring interfaces over concrete implementations in software engineering. When in doubt, multiple levels of generality can be provided, with more concrete interfaces instantiating more general ones.

Examples that may go into the backbone:

- Definition of Krylov subspaces for linear operators.
- Abstract definition of MINRES as iterative argmins of residuals.
- Perturbation functions in Banach spaces.
- Convex conjugates, Fenchel's duality theorem.

## The surface

One surface library is produced for each textbook, which should contain theorem statements faithful to the book: we seek similar structures and organizations as the books (with chapter-to-chapter correspondence), with accurate semantic alignment for each theorem statement. Every numbered item in a book maps to a node in the plans.

The proofs here should mostly be *direct uses and specializations* of results in the backbone. Definitions may be created here for semantic alignment, but it is desirable to accompany those with equivalence proofs to the backbone versions, so that results can derive from the equivalence. Within a surface library the dependencies run forwards in the direction of the chapter numbering, and where an earlier chapter has already restated something, later chapters use that restatement rather than reaching past it to the Mathlib or backbone original.

The level of generality at the surface should simply match the books. Consider the surface as integration tests, specified by product requirements written in the books, that the backbone implementation must pass.

Examples that may go into the surface:

- Specific variations of MINRES implementations, all satisfying the canonical specification in the backbone.
- Lagrangian duality in $\mathbb R^n$.

## Contributing

Both the backbone and the surface libraries are covered by structured plans in [`plans/`](plans/). They are TOML files that can either index into finished Lean code, or represent desired Lean modules/declarations not yet written.

To start new plans for a formalization project or complete open items in existing plans, refer to [`CONTRIBUTING.md`](CONTRIBUTING.md).
