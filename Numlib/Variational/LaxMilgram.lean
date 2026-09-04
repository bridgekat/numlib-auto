import Numlib.Variational.Forms
import Numlib.Nonlinear.FixedPoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Lax–Milgram, Babuška–Nečas, and existence theory for variational problems

* `SesqForm.laxMilgram`: a bounded coercive form on a Hilbert space is uniquely solvable,
  `‖u‖ ≤ ‖ℓ‖ / c` (AH Thm 8.3.4, Kress; Mathlib's `IsCoercive.continuousLinearEquivOfBilin` is
  the real case); proof routes: Riesz + `ContinuousLinearMap.exists_equiv_of_isCoerciveWith`
  (AH proof #2) or the damped fixed-point iteration (AH proof #1, `contractingWith_damped`).
* `SesqForm.isMinOn_energy_iff`: for Hermitian coercive forms, the solution is the unique
  minimizer of the energy (AH Thm 8.3.3, Ex 8.3.5; Saad Prop 5.2 in operator form), on subspaces
  and on closed convex sets (variational inequalities, AH (8.3.3)).
* `SesqForm₂.babuska_necas`: the generalized Lax–Milgram lemma (AH Thm 8.7.1) under the
  inf–sup condition and nondegeneracy, with `‖u‖ ≤ ‖ℓ‖ / α` (8.7.5).
* Existence via a priori estimates (AH Thm 8.2.1–8.2.4): bounded-below operators with closed /
  dense range, including the closed-operator version.
-/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

namespace SesqForm

variable (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)

/-- Lax–Milgram (AH Thm 8.3.4): a bounded coercive form is uniquely solvable. -/
theorem laxMilgram {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) : ∃! u, ∀ v, a u v = ℓ v := by
  sorry

/-- The stability estimate `‖u‖ ≤ ‖ℓ‖ / c`. -/
theorem norm_le_of_forall_apply_eq {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) {u : V}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / c := by
  sorry

/-- Lipschitz dependence on the data (AH (5.1.11) / (8.3.6)). -/
theorem norm_sub_le_of_forall_apply_eq {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c)
    {ℓ₁ ℓ₂ : V →L[𝕜] 𝕜} {u₁ u₂ : V} (h₁ : ∀ v, a u₁ v = ℓ₁ v) (h₂ : ∀ v, a u₂ v = ℓ₂ v) :
    ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / c := by
  sorry

/-- The solution operator `ℓ ↦ u` is a continuous linear equivalence `V' ≃L V` (AH (8.3.5)). -/
theorem exists_solutionEquiv {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) :
    ∃ S : (V →L[𝕜] 𝕜) ≃L[𝕜] V, (∀ ℓ v, a (S ℓ) v = ℓ v) ∧ ‖(S : (V →L[𝕜] 𝕜) →L[𝕜] V)‖ ≤ 1 / c := by
  sorry

/-- AH proof #1: the damped iteration `u ↦ u - θ (A u - f)` is a contraction with factor
`√(1 - 2θc + θ²‖a‖²)` for `0 < θ < 2c / ‖a‖²` (see `contractingWith_damped`,
`ContinuousLinearMap.norm_sub_smul_apply_sq_le`). -/
theorem contractingWith_damped_toOperator {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c)
    (ha0 : 0 < ‖a‖) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * c / ‖a‖ ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * ‖a‖ ^ 2)))
      (fun u => u - (θ : 𝕜) • (toOperator a u - rieszRep ℓ)) := by
  sorry

section Energy

variable {a} (ha : a.IsHermitian)
include ha

/-- AH Thm 8.3.3 (subspace / whole-space case): for a Hermitian coercive form, `u` solves
`a u v = ℓ v` for all `v ∈ K` iff `u ∈ K` minimizes the energy on the subspace `K`. -/
theorem isMinOn_energy_iff {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (K : Submodule 𝕜 V)
    {u : V} (hu : u ∈ K) : IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v := by
  sorry

/-- AH (8.3.3): on a nonempty closed convex set `K` (real scalars), the energy minimizer is
characterized by the variational inequality `re (a u (v - u)) ≥ re (ℓ (v - u))`. -/
theorem isMinOn_energy_iff_forall_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hK : Convex ℝ K) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u) := by
  sorry

/-- Existence and uniqueness of the energy minimizer on a nonempty closed convex set
(AH Thm 8.3.3 via Thm 3.3.12 / Mathlib's `exists_norm_eq_iInf_of_complete_convex`). -/
theorem existsUnique_isMinOn_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hK : Convex ℝ K) (hKc : IsClosed K)
    (hne : K.Nonempty) : ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u := by
  sorry

/-- The energy identity `E(v) - E(u) = ½ ‖v - u‖_a²` at the solution `u` (AH Ex 8.3.5, Saad
Prop 5.2's proof). -/
theorem energy_sub_energy_eq {u : V} (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2 := by
  sorry

end Energy

end SesqForm

namespace SesqForm₂

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜)

/-- Generalized Lax–Milgram / Babuška–Nečas (AH Thm 8.7.1): under the inf–sup condition and
nondegeneracy, `a u v = ℓ v ∀ v` is uniquely solvable. -/
theorem babuska_necas {α : ℝ} (hα : 0 < α) (hinf : a.InfSupWith α) (hnd : a.IsNondegenerate) :
    ∃! u, ∀ v, a u v = ℓ v := by
  sorry

/-- AH (8.7.5): `‖u‖ ≤ ‖ℓ‖ / α`. -/
theorem norm_le_of_infSupWith {α : ℝ} (hα : 0 < α) (hinf : a.InfSupWith α) {u : U}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α := by
  sorry

/-- The inf–sup condition is necessary: if the problem is well posed with `‖u‖ ≤ C ‖ℓ‖` for all
`ℓ`, then `a.InfSupWith (1 / C)` (AH Thm 8.7.1 converse / Nečas). -/
theorem infSupWith_of_forall_exists {C : ℝ} (hC : 0 < C)
    (h : ∀ ℓ : V →L[𝕜] 𝕜, ∃ u, (∀ v, a u v = ℓ v) ∧ ‖u‖ ≤ C * ‖ℓ‖) :
    a.InfSupWith (1 / C) := by
  sorry

end SesqForm₂

section APriori

/-! ### Existence from a priori estimates (AH §8.2) -/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

/-- AH Thm 8.2.1/8.2.4 (bounded case): a bounded-below operator `c ‖v‖ ≤ ‖L v‖` has closed
range; if moreover its range is dense (`(range L)ᗮ = ⊥`) it is bijective. -/
theorem ContinuousLinearMap.isClosed_range_of_le_norm (L : V →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) : IsClosed (LinearMap.range (L : V →ₗ[𝕜] W) : Set W) := by
  sorry

theorem ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot (L : V →L[𝕜] W)
    {c : ℝ} (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    (hdense : (LinearMap.range (L : V →ₗ[𝕜] W))ᗮ = ⊥) : Function.Bijective L := by
  sorry

/-- AH Thm 8.2.4 (closed-operator version): a closed, bounded-below, densely defined operator
`L : V →ₗ.[𝕜] W` has closed range. -/
theorem LinearPMap.isClosed_range_of_isClosed_of_le_norm (L : V →ₗ.[𝕜] W) (hL : L.IsClosed)
    {c : ℝ} (hc : 0 < c) (h : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖) :
    _root_.IsClosed (LinearMap.range L.toFun : Set W) := by
  sorry

/-- AH (8.2.2): the a priori (stability) estimate `‖v‖ ≤ C ‖L v‖` is equivalent to injectivity
with continuous inverse on the range; here the quantitative form `‖L⁻¹ w‖ ≤ C ‖w‖`. -/
theorem ContinuousLinearMap.norm_le_of_le_norm (L : V →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) {v : V} {w : W} (hv : L v = w) : ‖v‖ ≤ ‖w‖ / c := by
  sorry

end APriori
