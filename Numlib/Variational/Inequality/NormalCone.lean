import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Optimization.Minimum
import Numlib.Analysis.Convex.Subgradient.Calculus
import Numlib.Analysis.Convex.Subgradient.Defs
import Numlib.Analysis.Convex.Subgradient.Monotone
import Numlib.Variational.Inequality.Basic

/-!
# Variational inequalities in the vocabulary of convex analysis

The dictionary between the elliptic variational inequality of `Numlib/Variational/Inequality/Basic`
and the normal cones, subdifferentials and monotone relations of `Numlib/Analysis/Convex`. The
inequality

  `u ∈ K`,  `⟪f, v - u⟫ ≤ ⟪A u, v - u⟫ + j v - j u`  for every `v ∈ K`

stays the *definition*: its consumers manipulate it as an inequality, `A` is a nonlinear operator
and `j` is real-valued, and a definition through `subgradient` would carry an `EReal` coercion into
every proof of the Hilbert-space theory for no gain. What this module adds are the translations, all
of them `Iff`s about the same point `u`:

* `isVariationalInequalitySolution_zero_iff_sub_mem_normalCone` — the inequality of the first kind
  (`j = 0`) is `f - A u ∈ N_K(u)`, the normal cone taken for the pairing `innerₗ V`;
* `isVariationalInequalitySolution_iff_sub_mem_subgradient` — the inequality of the second kind is
  `f - A u ∈ ∂(j + δ_K)(u)`, with `δ_K` the indicator function `indicatorFn K`;
* `isVariationalInequalitySolution_iff_sub_mem_add_normalCone` — in a Hilbert space, for `j` convex
  and lower semicontinuous, the subdifferential splits, `∂(j + δ_K)(u) = ∂j(u) + N_K(u)`, so the
  inequality of the second kind is `f - A u ∈ ∂j(u) + N_K(u)`. The split is the sum rule
  `IsExactSum.subgradient_add` under the continuity constraint qualification
  `IsExactSum.of_continuousAt`; the continuity of `j` is
  `ConvexOn.continuous_of_lowerSemicontinuous`, and the qualification wants the pairing compatible,
  which `instIsCompatiblePairingInner` supplies by Fréchet–Riesz.

Two neighbouring translations live here as well:

* `IsStronglyMonotoneWith.isMonotoneRel_graph` — a strongly monotone operator with a non-negative
  constant has a monotone graph in the sense of `IsMonotoneRel`, the multivalued notion the theory
  of `∂f` is built on;
* `isMinOn_iff_neg_mem_normalCone`, `isMinOn_iff_neg_toDual_symm_mem_normalCone` — the
  first-order condition of `Numlib/Analysis/Convex/Gateaux` for a minimiser of a convex Gâteaux
  differentiable `f` over a convex `K`, `0 ≤ f' u (v - u)` for all `v ∈ K`, is `-f' u ∈ N_K(u)`,
  against the pairing of `V` with its dual in a normed space and, through the Riesz representative
  of `f' u`, against `innerₗ V` in a Hilbert space. This is the sufficiency half of Rockafellar,
  *Convex Analysis*, Theorem 27.4, in the vocabulary of the variational layer.

The two lemmas `ConvexOn.convexFn_coe` and `ConvexAnalysis.proper_coe_real`, reading a real-valued
convex function as a proper `ConvexFn`, are the glue the split needs; their natural home is beside
`convexOn_iff_convexFn` in `Numlib/Analysis/Convex/Epigraph`.

Sources: Atkinson–Han, *Theoretical Numerical Analysis*, §11.3 for the inequalities; Rockafellar,
*Convex Analysis*, §23 for the sum rule and Theorem 27.4 for the optimality condition.
-/

open ConvexAnalysis
open scoped Pointwise

/-! ### Real-valued functions as `EReal`-valued ones -/

section Coe

variable {V : Type*}

/-- A real-valued function on a nonempty type, read as an `EReal`-valued one, is proper. -/
theorem ConvexAnalysis.proper_coe_real [Nonempty V] (j : V → ℝ) :
    Proper fun v => (j v : EReal) :=
  ⟨⟨Classical.arbitrary V, EReal.coe_lt_top _⟩, fun _ => EReal.coe_ne_bot _⟩

/-- A convex real-valued function, read as an `EReal`-valued one, is convex in the sense of
`ConvexFn`. -/
theorem ConvexOn.convexFn_coe [AddCommGroup V] [Module ℝ V] {j : V → ℝ}
    (hj : ConvexOn ℝ Set.univ j) : ConvexFn fun v => (j v : EReal) := by
  refine (convexFn_iff_le fun _ => EReal.coe_ne_bot _).2 fun x y a b ha hb hab => ?_
  have h := hj.2 (Set.mem_univ x) (Set.mem_univ y) ha.le hb.le hab
  simp only [smul_eq_mul] at h
  exact_mod_cast h

end Coe

/-! ### The variational inequality as a normal-cone and a subgradient condition -/

section Inequality

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {u : V}

/-- **The inequality of the first kind is a normal-cone condition.** With `j = 0`,
`IsVariationalInequalitySolution A 0 f K u` says exactly that `u ∈ K` and `f - A u` is normal to
`K` at `u`: `⟪v - u, f - A u⟫ ≤ 0` for every `v ∈ K`. No hypothesis on `A`, `K` or `V`. -/
theorem isVariationalInequalitySolution_zero_iff_sub_mem_normalCone :
    IsVariationalInequalitySolution A 0 f K u ↔ u ∈ K ∧ f - A u ∈ normalCone (innerₗ V) K u := by
  unfold IsVariationalInequalitySolution
  rw [mem_normalCone]
  refine and_congr_right fun _ => forall₂_congr fun v _ => ?_
  rw [Pi.zero_apply, Pi.zero_apply, sub_zero, add_zero, innerₗ_apply_apply,
    inner_sub_right (v - u) f (A u), sub_nonpos, real_inner_comm (v - u) f,
    real_inner_comm (v - u) (A u)]

/-- **The inequality of the second kind is a subgradient condition.**
`IsVariationalInequalitySolution A j f K u` says exactly that `u ∈ K` and `f - A u` is a
subgradient at `u` of `j + δ_K`, the functional `j` extended by `+∞` off `K`. Off `K` the
subgradient inequality is vacuous, and on `K` it is the variational inequality. No hypothesis on
`A`, `j`, `K` or `V`. -/
theorem isVariationalInequalitySolution_iff_sub_mem_subgradient :
    IsVariationalInequalitySolution A j f K u ↔
      u ∈ K ∧ f - A u ∈ subgradient (innerₗ V) (fun v => (j v : EReal) + indicatorFn K v) u := by
  unfold IsVariationalInequalitySolution
  refine and_congr_right fun hu => ?_
  simp only [mem_subgradient, indicatorFn_of_mem hu, add_zero, innerₗ_apply_apply]
  constructor
  · intro h v
    by_cases hv : v ∈ K
    · rw [indicatorFn_of_mem hv, add_zero, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right,
        real_inner_comm f (v - u), real_inner_comm (A u) (v - u)]
      linarith [h v hv]
    · rw [indicatorFn_of_notMem hv, EReal.coe_add_top]
      exact le_top
  · intro h v hv
    have hv' := h v
    rw [indicatorFn_of_mem hv, add_zero, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right,
      real_inner_comm f (v - u), real_inner_comm (A u) (v - u)] at hv'
    linarith

/-- The constraint qualification behind the split `∂(j + δ_K) = ∂j + N_K`: in a real Hilbert
space a convex lower semicontinuous `j : V → ℝ` is continuous, so it adds exactly with the
indicator of any nonempty convex `K`. -/
theorem ConvexOn.isExactSum_coe_indicatorFn [CompleteSpace V] (hj : ConvexOn ℝ Set.univ j)
    (hlsc : LowerSemicontinuous j) (hK : Convex ℝ K) (hne : K.Nonempty) :
    IsExactSum (innerₗ V) (fun v => (j v : EReal)) (indicatorFn K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine IsExactSum.of_continuousAt (ConvexOn.convexFn_coe hj) (proper_coe_real j)
    (convexFn_indicatorFn.2 hK) (proper_indicatorFn.2 ⟨x₀, hx₀⟩) (x₀ := x₀)
    (mem_dom.2 (EReal.coe_lt_top _)) (by rwa [dom_indicatorFn]) ?_
  exact (continuous_coe_real_ereal.comp (hj.continuous_of_lowerSemicontinuous hlsc)).continuousAt

/-- **The inequality of the second kind, split.** In a real Hilbert space, for `j` convex and
lower semicontinuous and `K` nonempty and convex, `IsVariationalInequalitySolution A j f K u`
says exactly that `u ∈ K` and `f - A u ∈ ∂j(u) + N_K(u)`: some subgradient `y` of `j` at `u`
has `f - A u - y` normal to `K` at `u`. The inclusion `∂j(u) + N_K(u) ⊆ ∂(j + δ_K)(u)` is
unconditional; the reverse one is the sum rule `IsExactSum.subgradient_add` under the continuity
constraint qualification, which is where the hypotheses on `j`, `K` and `V` are spent. -/
theorem isVariationalInequalitySolution_iff_sub_mem_add_normalCone [CompleteSpace V]
    (hj : ConvexOn ℝ Set.univ j) (hlsc : LowerSemicontinuous j) (hK : Convex ℝ K)
    (hne : K.Nonempty) :
    IsVariationalInequalitySolution A j f K u ↔
      u ∈ K ∧ f - A u ∈ subgradient (innerₗ V) (fun v => (j v : EReal)) u +
        normalCone (innerₗ V) K u := by
  rw [isVariationalInequalitySolution_iff_sub_mem_subgradient]
  refine and_congr_right fun hu => ?_
  rw [← subgradient_indicatorFn (B := innerₗ V) hu,
    ← (ConvexOn.isExactSum_coe_indicatorFn hj hlsc hK hne).subgradient_add u]
  rfl

/-- **A strongly monotone operator has a monotone graph.** `IsStronglyMonotoneWith ℝ A c` with
`0 ≤ c` gives `0 ≤ ⟪x - y, A x - A y⟫` for all `x, y`, which is `IsMonotoneRel (innerₗ V)` of the
graph `{p | p.2 = A p.1}` of `A` — the single-valued case of the monotone relations the theory of
the subdifferential is built on. -/
theorem IsStronglyMonotoneWith.isMonotoneRel_graph {c : ℝ} (hA : IsStronglyMonotoneWith ℝ A c)
    (hc : 0 ≤ c) : IsMonotoneRel (innerₗ V) {p : V × V | p.2 = A p.1} := by
  rintro ⟨x, x'⟩ (rfl : x' = A x) ⟨y, y'⟩ (rfl : y' = A y)
  have h := (isStronglyMonotoneWith_real_iff A c).1 hA x y
  dsimp only
  rw [innerₗ_apply_apply, real_inner_comm]
  exact (mul_nonneg hc (sq_nonneg _)).trans h

end Inequality

/-! ### The first-order condition of a constrained convex minimiser -/

section Gateaux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ}
  {f' : V → V →L[ℝ] ℝ} {K : Set V} {u : V}

/-- **The first-order condition as a normal-cone condition** (the sufficiency half of Rockafellar,
*Convex Analysis*, Theorem 27.4, in the setting of `Numlib/Analysis/Convex/Gateaux`). For `f`
convex on a convex `K` with directional derivatives `f'` at the points of `K`, a point `u ∈ K`
minimises `f` over `K` if and only if `-f' u` is normal to `K` at `u`, against the pairing of `V`
with its continuous dual: `f' u (v - u) ≥ 0` for every `v ∈ K`. This is
`isMinOn_iff_forall_lineDeriv_nonneg` with its right-hand side read as a set membership. -/
theorem isMinOn_iff_neg_mem_normalCone (hf : ConvexOn ℝ K f)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) (hu : u ∈ K) :
    IsMinOn f K u ↔ -f' u ∈ normalCone (topDualPairing ℝ V).flip K u := by
  rw [isMinOn_iff_forall_lineDeriv_nonneg hf hG hu, mem_normalCone]
  refine forall₂_congr fun v _ => ?_
  simp only [LinearMap.flip_apply, topDualPairing_apply, neg_apply, neg_nonpos]

end Gateaux

section GateauxHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {K : Set V} {u : V}

/-- **The first-order condition as a normal-cone condition, in a Hilbert space.** With the Riesz
representative `∇f(u) = (toDual ℝ V).symm (f' u)` of the derivative, `u ∈ K` minimises the convex
`f` over the convex `K` if and only if `-∇f(u) ∈ N_K(u)` for the pairing `innerₗ V`. -/
theorem isMinOn_iff_neg_toDual_symm_mem_normalCone (hf : ConvexOn ℝ K f)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) (hu : u ∈ K) :
    IsMinOn f K u ↔ -(InnerProductSpace.toDual ℝ V).symm (f' u) ∈ normalCone (innerₗ V) K u := by
  rw [isMinOn_iff_forall_lineDeriv_nonneg hf hG hu, mem_normalCone]
  refine forall₂_congr fun v _ => ?_
  rw [innerₗ_apply_apply, inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply,
    neg_nonpos]

end GateauxHilbert
