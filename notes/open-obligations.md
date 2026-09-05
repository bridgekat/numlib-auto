# Open proof obligations

The backbone is proved entire. One `sorry` remains, on the surface, and it is deferred backbone
material rather than an unfinished proof: `lake build` reports exactly one
`declaration uses 'sorry'`, at the declaration below.

## `Numlib/Surface/SaadSparse/Chapter06/Section10.lean` (1)

`exists_aeval_eq_conjTranspose_of_isStarNormal`: a normal `A` satisfies `A^H = q(A)` for some
polynomial `q`. Writing `A = Q Λ Q^H`, any `q` interpolating `z ↦ conj z` at the eigenvalues
works — but that needs unitary diagonalization of a normal matrix, and Mathlib has `IsStarNormal`
and `Lagrange.interpolate` yet neither Schur triangulation nor the normal spectral theorem. This is
backbone material for a future `Numlib/Eigen/Normal.lean` (`tracker/backbone.md` §4.2, phase 3), and
Saad's Lemma 6.23 and Theorem 6.24 wait on the same item.

The consumer `exists_aeval_eq_conjTranspose`, which lowers the degree below `n` by reducing modulo
the characteristic polynomial, *is* proved; only the existence above is open. Do not repair this by
adding the existence as a hypothesis: it is not part of the final statement, so it would be
permanent damage to the interface in exchange for temporary tidiness.

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
