# Open proof obligations

**None.** The library is proved entire, backbone and surface alike: `lake build` reports no
`declaration uses 'sorry'` anywhere.

The single entry this file used to carry was
`Numlib/Surface/SaadSparse/Chapter06/Section10.lean`'s
`exists_aeval_eq_conjTranspose_of_isStarNormal` — a normal `A` satisfies `A^H = q(A)` for some
polynomial `q` — held open for normal-matrix theory the backbone did not have. That theory is now
`Numlib/Eigen/Normal.lean`, and the surface theorem is one line of it.

The entry's facts were right and its conclusion was wrong, which is worth remembering. It said the
proof "needs unitary diagonalization of a normal matrix", and that Mathlib has neither Schur
triangulation nor the normal spectral theorem. Both observations were correct; neither mattered.
For normal `N`, `ker N² = ker N`, so every generalized eigenspace of a normal operator is an
eigenspace; `Module.End.iSup_maxGenEigenspace_eq_top` then makes the eigenspaces span, and that is
diagonalizability with no triangulation theorem and no `Q` ever constructed. Reading the textbook
proof as the *only* proof is what made the item look expensive.

Keep this file as the register of backbone debt. When you do leave a `sorry`, add a section naming
the declaration and stating the *obstruction* — and be careful what you assert, because the next
agent will believe it and plan around it. Of the nine entries this file used to carry, four were
misleading:

* the `Complexify` entry blamed instance-search friction, but the statement was simply **false**: a
  `NormedRing (Matrix n n ℝ)` class argument carries its own `Ring`, unrelated to the canonical one
  the rest of the statement used. No amount of instance surgery could have worked.
* the `Newton` entry asserted the sharp constant would cost three further instance arguments on a
  public statement, and judged that not worth it. It costs none — the real scalar structure is
  introduced inside the proof by `restrictScalars`.
* Kato's lemma was budgeted for a minimal-gap API that Mathlib lacks. It needed none of it.
* the Givens identities were said to need a block decomposition of the rotation product; they did
  not, and the statement flagged as "suspect at `c_m = 0`" was true exactly as written, because
  `c_m = 0` makes its own Galerkin hypothesis contradictory.

So: record what you actually tried and what you observed, and mark anything you did not verify as a
conjecture rather than as a diagnosis.
