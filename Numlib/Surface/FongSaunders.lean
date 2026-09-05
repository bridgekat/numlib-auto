import Numlib.Surface.FongSaunders.Section1
import Numlib.Surface.FongSaunders.Section2
import Numlib.Surface.FongSaunders.Section3
import Numlib.Surface.FongSaunders.Section4
import Numlib.Surface.FongSaunders.Section5

/-!
# Fong–Saunders, *CG versus MINRES: an empirical comparison*

The surface library for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical
comparison*, SQU Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R): five modules, one
per section of the paper. Each states the paper's results in the paper's own terms and proves them
from `Numlib`, the general backbone. Little is proved here that is not proved there — the surface
exists to test the backbone against a published account of the subject, and to give a reader of the
paper a Lean name for every result in it.

**All six numbered theorems of the paper are formalized** — Theorems 2.1–2.5 and Theorem 3.1 —
together with the displayed equations (2.2), (3.2)–(3.6) and (4.1), the definitions (2.1) of a
MINRES iterate and (3.1) of an acceptable solution, the two algorithms of Table 2.1, and the
monotonicity profile of Table 5.1. The two indefinite-case results that §4.2 states in prose are
deferred; see "Not formalized" below.

This module imports the five section modules and adds nothing of its own.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_2_3_cr` is
Theorem 2.3 for Algorithm CR and `equation_4_1` is (4.1). Where one numbered result needs several
declarations — its separate clauses, its CG and its MINRES form, or a strict beside a nonstrict
version — a trailing word tells them apart, as in `theorem_2_2_a`, `theorem_3_1_minres` and
`theorem_2_3_strict`. The paper's unnumbered constructions keep descriptive names (`cg`, `cr`,
`krylov`, `lanczosVec`, `nrbe`). Everything is in the flat `FongSaunders` namespace, and `SectionN`
is the module for §N.

## The outline

| § | module | subject |
|---|---|---|
| 1 | `Section1` | The setting, Krylov subspaces and the Lanczos process |
| 2 | `Section2` | Algorithms CG and CR, their minimization properties, Theorems 2.1–2.5 |
| 3 | `Section3` | Normwise relative backward errors, the stopping rule, Theorem 3.1 |
| 4 | `Section4` | The exact relations behind the numerical comparison |
| 5 | `Section5` | Table 5.1, the summary of monotonicity properties |

`Section1` also fixes the vocabulary the other four use and proves the bridges to the backbone;
each later module imports its predecessor together with the backbone modules its own proofs need.

## The setting

The paper works throughout with a real symmetric positive definite system `A x = b` of order `n`,
solved from the zero starting point `x₀ = 0`, taking the 2-norm on vectors and the Frobenius norm
on matrices. In Lean:

* `Vec n` is `EuclideanSpace ℝ (Fin n)`, so `‖·‖` on it is the 2-norm and `⟪x, y⟫_ℝ` is `xᵀ y`;
* `A : Matrix (Fin n) (Fin n) ℝ` carries `hA : A.PosDef`, which over `ℝ` is Mathlib's spelling of
  "symmetric, with `xᵀ A x > 0` for `x ≠ 0`"; `isSymmetricCoercive_of_posDef` is the bridge to the
  backbone's `LinearMap.IsSymmetricCoercive`, through which every backbone theorem applies;
* `A ⬝ x` is `Matrix.toEuclideanLin A x`, the paper's matrix–vector product read on `Vec n`;
* `‖A‖` is the Frobenius norm, from `open scoped Matrix.Norms.Frobenius` in `Section3`.

`x₀ = 0` is an instantiation rather than a hypothesis: the backbone states its Krylov theory for an
arbitrary `x₀`, and every theorem here fixes it to `0`, as the paper does. That is what makes
`𝒦_k(A, b)` — not `𝒦_k(A, r₀)` — the subspace the iterates live in, and it is where the two `k ≥ 1`
restrictions recorded below come from. Because the ambient space is `Vec n`, the backbone's
`[FiniteDimensional …]` instance hypotheses are discharged automatically and its `RCLike.re`
disappears.

## Where formalizing needs care

Three places where the paper does not transcribe literally. Each is recorded on the declarations
concerned; `tracker/fongsaunders.md` carries the full discussion.

* **The backward-error results need `A ≠ 0` and `b ≠ 0`** (§3). The paper measures a perturbation
  by the ratios `‖E‖/‖A‖` and `‖f‖/‖b‖`, which presuppose nonzero denominators. Lean's `t / 0 = 0`
  makes both ratios vanish when they do not, so every perturbation of a zero matrix would be
  feasible at every tolerance and `nrbe_isLeast`, `nrbePert_attains` and
  `isAcceptable_iff_nrbe_le_one` would be vacuously true rather than sharp. The two hypotheses are
  therefore explicit; under `A.PosDef` the first follows from the second by `ne_zero_of_posDef`.

* **Two monotonicity rows start at `k = 1`, because `x₀ = 0`** (§3, §5). The quantities `‖E_k‖/‖A‖`
  of Theorem 3.1 and `‖r_k‖/‖x_k‖` of Table 5.1 divide by `‖x_k‖`, which vanishes at `k = 0`. The
  paper's `E_0` is simply undefined there, whereas in Lean the ratio evaluates to `0`, which is
  *below* every later value: `Antitone` on all of `ℕ` would be false, not merely unstated. So
  `theorem_3_1_minres`, `nrbe_minres_antitoneOn` and `MinresProfile.backwardError` are
  `AntitoneOn … (Set.Ici 1)`. When `β > 0` keeps the denominator positive at `k = 0` the honest
  statement is `Antitone` on all of `ℕ`, and that is what `nrbe_minres_antitone` says.

* **The two blank entries of Table 5.1 need explicit witnesses** (§5). Read faithfully, a blank
  entry asserts the existence of a symmetric positive definite system on which the row fails to be
  monotone. `cg_norm_residual_not_antitone` uses `A = diag(1, 9)`, `b = (3, 1)ᵀ`, where
  `‖r₀‖² = 10` and `‖r₁‖² = 160/9`. `cg_backwardError_not_antitoneOn` uses `A = diag(1, 13, 16)`,
  `b = (1, 5, 1)ᵀ`, where `(‖r₁‖/‖x₁‖)² = 50/9 < 200/33 = (‖r₂‖/‖x₂‖)²`. The second admits no
  `2 × 2` witness: CG on an order-2 system terminates with `r₂ = 0`, so the ratio is `0` from
  `k = 2` on and the row cannot fail on `Set.Ici 1`.

## Not formalized

**Deferred.** §4.2 states Steihaug's theorem — for CG on a symmetric, possibly *indefinite* system
the solution norms `‖x_1‖, …, ‖x_k‖` increase strictly as long as `p_jᵀ A p_j > 0` — and asserts
the same for CR and MINRES under the further condition `r_jᵀ A r_j > 0`. Both rest on strict
monotonicity statements for symmetric indefinite operators that the backbone does not yet provide
(`tracker/backbone.md` §3.11, "Steihaug's generalization", scheduled for phase 2), and the surface
layer may not invent them. The CR analogue would also need restating: the paper's proof of
Theorem 2.2 (d) expands `p_i` in the complete orthogonal basis `{q_0, …, q_{ℓ−1}}` of `A 𝒦_ℓ`,
which needs the recurrence to run to termination without breakdown, not merely through iteration
`k`, so the local hypotheses the paper states do not support the local conclusion it draws.

**Left out.** The empirical half of the paper: the test set and diagonal preconditioning of §4, all
of Figures 4.1–4.8 with their percentages of monotone steps, the "cumulative minimum" heuristic of
§4.1.1, and the MINRES-QLP relationship of §4.2, which is built on Choi–Paige–Saunders and from
which the paper draws no theorem. Table 5.2 and the §5 discussion of LSQR and LSMR state results of
other papers.

## References

* D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU Journal for
  Science **17** (2012) 44–62; also Report SOL 2011-2R, Department of Management Science and
  Engineering, Stanford University, 2011.
-/
