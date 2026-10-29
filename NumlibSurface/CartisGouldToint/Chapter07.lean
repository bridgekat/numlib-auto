import NumlibSurface.CartisGouldToint.Chapter07.Section01
import NumlibSurface.CartisGouldToint.Chapter07.Section02

/-!
# Cartis–Gould–Toint, Chapter 7: Problems with Nonconvex Constraints

Surface of [cartis2022evaluation] Chapter 7: `minimize_{x ∈ 𝒞} f(x)` subject to `c(x) = 0`
(7.1.1), its Lagrangian `ℒ(x, y) = f(x) - ⟨y, c(x)⟩` and scaled approximate first-order
criticality (7.1.4), and the two-phase target-following algorithm TPp-GC (Algorithm 7.2.1). This
module imports the section modules and adds nothing of its own.

* §7.1, `Chapter07.Section01`: the problem (7.1.1), `ω_{ℒ,𝒞,1}`, approximate minimizers (7.1.4);
  Theorem 7.1.1
* §7.2, `Chapter07.Section02`: TPp-GC (Algorithm 7.2.1); Lemmas 7.2.1–7.2.6, Theorem 7.2.7

The target residual and merit function are the backbone `Constrained.targetResidual`,
`Constrained.targetMerit`; Phase 1 is an ARpLE-CC run (§6.3) on `c`, Phase 2 the run predicate
`IsTPpGCPhase2`, an instance of the backbone's target-following outer loop
(`Constrained.IsTargetFollowingRun`), from whose complexity theorem Lemma 7.2.6 and Theorem 7.2.7
are derived (shared with TPqp-GC, Chapter 14). Appendix B's Lemma B.7.1 is in `AppendixB.Chapter07`.

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Algorithm 7.2.1, Phase 2: **gap**, it must apply ARp1-CC (Algorithm 6.2.2), not ARp-CC, since
  the proof of Lemma 7.2.6 uses Lemma 6.2.4 (`IsTPpGCPhase2`).
* Algorithm 7.2.1, Step 2(a): **false** with `‖r(x_{k+1}, t_k)‖ < θε₀`, the algorithm can terminate
  without the guarantee (7.2.17) of Lemma 7.2.1; the test is `≤ θε₀` (`algorithm_7_2_1`,
  `lemma_7_2_1`).
* Lemma 7.2.6, Theorem 7.2.7: **gap**, the block argument omits the restart of `σ` at `σ₀` in every
  inner run, the `i = 0` elements of `𝓘^s_k` (so (7.2.39) can fail), and the "bad" outer
  iterations, whose inner run ends with a successful step to a point passing the third test of
  (7.2.10) and for which the book gives no bound. `theorem_7_2_7` carries their number as a
  parameter (with it bounded independently of `ε`, the order of (7.2.50)); under bounded
  gradients `theorem_7_2_7_of_gradient_le` bounds them by `N_b = O(ε₀⁻¹ε₁⁻¹)`, within the order of
  (7.2.50) (for `ε₀ = ε₁`) iff `p ≤ 2`. The derivative count has an `ε₀^{-1}` term absent from
  (7.2.53); whether (7.2.53) holds is open (`lemma_7_2_6`).
* Lemma 7.2.2, (7.2.24): **false** derivative-evaluation bound, `+ 2` (`lemma_7_2_2`).
* (7.1.1), Theorem 7.1.1: **reading**, `𝒞` need not be bounded, nor `𝒮` closed or inside `𝒞`
  (`theorem_7_1_1`).

## Not formalized

§7.2.3 (penalty, augmented Lagrangian, barrier and SQP methods; no numbered results) and the
heuristic motivation of the scaling `‖(y, 1)‖` after (7.1.5).
-/
