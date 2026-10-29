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

* Phase 2 must apply ARp1-CC (Algorithm 6.2.2), not ARp-CC: the proof of Lemma 7.2.6 uses
  Lemma 6.2.4.
* The Step-2(a) test `‖r(x_{k+1}, t_k)‖ < θε₀` must be `≤ θε₀`; with `<` the algorithm can terminate
  without the guarantee (7.2.17), contradicting Lemma 7.2.1.
* **The counting of Lemma 7.2.6 and Theorem 7.2.7 has a gap.** The block argument omits the
  restart of `σ` at `σ₀` in every inner run, the `i = 0` elements of `𝓘^s_k` (so (7.2.39) can
  fail), and the "bad" outer iterations, whose inner run ends with a successful step to a point
  passing the third test of (7.2.10): no decrease is guaranteed for these and the book gives no
  bound on their number. `theorem_7_2_7` carries the number of bad iterations as a parameter; when
  it is bounded independently of `ε`, the counts have the order
  `O(max(ε₀^{-1}, ε₀^{-1/p} ε₁^{-(p+1)/p}))` of (7.2.50). Under bounded gradients (`f`, `c` of
  class `C¹`, `‖∇f‖ ≤ B_f` near feasibility) `theorem_7_2_7_of_gradient_le` closes the gap, with
  an extra `N_b = O(ε₀⁻¹ε₁⁻¹)` outer iterations, within the order of (7.2.50) (for `ε₀ = ε₁`) iff
  `p ≤ 2`.
  The derivative count acquires an `ε₀^{-1}` term absent from (7.2.53); whether (7.2.53) holds is
  not established.
* Lemma 7.2.2's derivative-evaluation bound (7.2.24) misses `+ 2`.
* The convex set `𝒞` need not be bounded (nor, in Theorem 7.1.1, `𝒮` closed or inside `𝒞`).

## Not formalized

§7.2.3 (penalty, augmented Lagrangian, barrier and SQP methods; no numbered results) and the
heuristic motivation of the scaling `‖(y, 1)‖` after (7.1.5).
-/
