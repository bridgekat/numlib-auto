import Numlib.Variational.LaxMilgram
import Numlib.LinearSolve.Projection.Optimality
import Numlib.Approximation.BestApprox
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Galerkin and Petrov–Galerkin methods for variational problems

* `IsGalerkinSolution a ℓ K u`: `u ∈ K` and `a u v = ℓ v` for all `v ∈ K`
  (Atkinson–Han[^atkinson-han] (9.1.4)); bridge to the operator specification
  `IsGalerkin (toOperator a) (rieszRep ℓ) 0 K u` of `Numlib.LinearSolve.Projection.Basic`, and to
  the stiffness-matrix system (9.1.5).
* Céa's lemma `‖u - u_N‖ ≤ (M / c) inf_{v ∈ K} ‖u - v‖` (Atkinson–Han Prop 9.1.3, their
  inequality (9.1.11)), the Hermitian sharpening `√(M / c)` (from the energy-norm optimality of
  `u_N` remarked on just after that proposition, with the energy functional (9.1.7) and the
  equivalent Ritz problem (9.1.8)), and convergence for monotone dense families (Atkinson–Han
  Cor 9.1.4).
* `IsPetrovGalerkinSolution a ℓ K L u` for two-space forms, Babuška's theorem
  `‖u - u_N‖ ≤ (1 + M / α_N) inf ‖u - v‖` under the discrete inf–sup condition (Atkinson–Han
  Thm 9.2.1), and the convergence corollary it yields (Atkinson–Han Cor 9.2.3).
* Strang's first lemma for the generalized Galerkin method on an abstract normed space `W`
  (Atkinson–Han Thm 9.3.1).

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open scoped InnerProductSpace

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The Galerkin problem: `u ∈ K`, `a u v = ℓ v` for all `v ∈ K` (Atkinson–Han, *Theoretical
Numerical Analysis*, (9.1.4)).  The trial space and the test space are the same subspace `K`. -/
def IsGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, a u v = ℓ v

/-- The Petrov–Galerkin problem: `u ∈ K`, `a u v = ℓ v` for all `v ∈ L` (Atkinson–Han,
*Theoretical Numerical Analysis*, (9.2.5)).  Here the trial space `K` and the test space `L` are
allowed to differ, and may even live in different spaces. -/
def IsPetrovGalerkinSolution {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (u : U) :
    Prop :=
  u ∈ K ∧ ∀ v ∈ L, a u v = ℓ v

theorem isGalerkinSolution_iff_isPetrovGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)
    (K : Submodule 𝕜 V) (u : V) :
    IsGalerkinSolution a ℓ K u ↔ IsPetrovGalerkinSolution (a : SesqForm₂ 𝕜 V V) ℓ K K u :=
  Iff.rfl

/-- The restriction of a two-space bounded form to a pair of subspaces. -/
private noncomputable def SesqForm₂.restrict {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace 𝕜 U] (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) :
    SesqForm₂ 𝕜 K L :=
  ((a.comp K.subtypeL).flip.comp L.subtypeL).flip

namespace IsGalerkinSolution

variable {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜} {K : Submodule 𝕜 V} {u : V}

/-- Bridge to the operator specification `IsGalerkin` of `Numlib.LinearSolve.Projection.Basic`:
Galerkin for the form is Galerkin for `A = toOperator a`, `b = rieszRep ℓ`, `x₀ = 0`. -/
theorem iff_isGalerkin [CompleteSpace V] :
    IsGalerkinSolution a ℓ K u ↔
      IsGalerkin (SesqForm.toOperator a : V →ₗ[𝕜] V) (SesqForm.rieszRep ℓ) 0 K u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨by simpa using hu, (Submodule.mem_orthogonal' _ _).mpr fun w hw => ?_⟩
    rw [inner_sub_left, SesqForm.inner_rieszRep, ContinuousLinearMap.coe_coe,
      SesqForm.inner_toOperator, h w hw, sub_self]
  · rintro ⟨hu, horth⟩
    refine ⟨by simpa using hu, fun w hw => ?_⟩
    have hz := (Submodule.mem_orthogonal' _ _).mp horth w hw
    rw [inner_sub_left, SesqForm.inner_rieszRep, ContinuousLinearMap.coe_coe,
      SesqForm.inner_toOperator, sub_eq_zero] at hz
    exact hz.symm

/-- Existence and uniqueness on a complete subspace for coercive `a`: the restriction of `a` to
`K` is still bounded and coercive with the same constant, so Lax–Milgram applies on `K`
(Atkinson–Han, *Theoretical Numerical Analysis*, §9.1). -/
theorem existsUnique {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) [CompleteSpace K] :
    ∃! u, IsGalerkinSolution a ℓ K u := by
  have hcoer : SesqForm.IsCoerciveWith
      (SesqForm₂.restrict (a : SesqForm₂ 𝕜 V V) K K) c := fun v => ha (v : V)
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram
    (SesqForm₂.restrict (a : SesqForm₂ 𝕜 V V) K K) (ℓ.comp K.subtypeL) hc hcoer
  refine ⟨(w : V), ⟨w.2, fun v hv => hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z => hy (z : V) z.2)

/-- Galerkin orthogonality: `a (u - u_N) v = 0` for `v ∈ K` when `u` is the exact solution. -/
theorem apply_sub_eq_zero (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) : a (ustar - u) v = 0 := by
  rw [map_sub, sub_apply, hstar v, hN.2 v hv, sub_self]

/-- If `a` is bounded by `M` then `M * ‖z‖ ≥ 0` for every `z`: no sign hypothesis on `M` is
needed, because testing the bound on `z` itself forces `M ≥ 0` unless `z = 0`. -/
private theorem nonneg_mul_norm {M : ℝ} (hM : a.IsBoundedWith M) (z : V) : 0 ≤ M * ‖z‖ := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · simp [← h]
  · nlinarith [norm_nonneg (a z z), hM z z]

/-- Céa's lemma (Atkinson–Han, *Theoretical Numerical Analysis*, Prop 9.1.3, inequality (9.1.11)),
pointwise form: `‖u - u_N‖ ≤ (M / c) ‖u - v‖` for all `v ∈ K`.  So the Galerkin error is, up to the
factor `M / c`, no worse than the best approximation error from `K`. -/
theorem norm_sub_le {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hN : IsGalerkinSolution a ℓ K u) {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) {v : V}
    (hv : v ∈ K) : ‖ustar - u‖ ≤ M / c * ‖ustar - v‖ := by
  have horth : a (ustar - u) (v - u) = 0 := hN.apply_sub_eq_zero hstar (K.sub_mem hv hN.1)
  have hsplit : a (ustar - u) (ustar - u) = a (ustar - u) (ustar - v) := by
    have h1 : (ustar - u : V) = (ustar - v) + (v - u) := by abel
    nth_rewrite 2 [h1]
    rw [map_add, horth, add_zero]
  have key : c * ‖ustar - u‖ ^ 2 ≤ M * ‖ustar - u‖ * ‖ustar - v‖ := by
    calc c * ‖ustar - u‖ ^ 2 ≤ RCLike.re (a (ustar - u) (ustar - u)) := ha _
      _ = RCLike.re (a (ustar - u) (ustar - v)) := by rw [hsplit]
      _ ≤ ‖a (ustar - u) (ustar - v)‖ := RCLike.re_le_norm _
      _ ≤ M * ‖ustar - u‖ * ‖ustar - v‖ := hM _ _
  have hcM : c * ‖ustar - u‖ ≤ M * ‖ustar - v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (ustar - u)) with h | h
    · rw [← h, mul_zero]
      exact nonneg_mul_norm hM (ustar - v)
    · refine le_of_mul_le_mul_right ?_ h
      calc c * ‖ustar - u‖ * ‖ustar - u‖ = c * ‖ustar - u‖ ^ 2 := by ring
        _ ≤ M * ‖ustar - u‖ * ‖ustar - v‖ := key
        _ = M * ‖ustar - v‖ * ‖ustar - u‖ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
  exact hcM

/-- Céa's lemma with the infimum. -/
theorem norm_sub_le_infDist {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M)
    (ha : a.IsCoerciveWith c) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) : ‖ustar - u‖ ≤ M / c * Metric.infDist ustar (K : Set V) := by
  have hKne : (K : Set V).Nonempty := ⟨0, K.zero_mem⟩
  rcases le_or_gt (M / c) 0 with hMc | hMc
  · -- then the error already vanishes, and so does the distance
    have h0 : ‖ustar - u‖ ≤ 0 := by
      have h := norm_sub_le hc hM ha hN hstar hN.1
      nlinarith [norm_nonneg (ustar - u)]
    have hd : Metric.infDist ustar (K : Set V) = 0 := by
      refine le_antisymm ?_ Metric.infDist_nonneg
      refine le_trans (Metric.infDist_le_dist_of_mem hN.1) ?_
      rw [dist_eq_norm]
      exact h0
    rw [hd, mul_zero]
    exact h0
  · have hMne : M ≠ 0 := by
      have h := mul_pos hMc hc
      rw [div_mul_cancel₀ M hc.ne'] at h
      exact h.ne'
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨v, hv, hvd⟩ :=
      (Metric.infDist_lt_iff hKne).mp
        (lt_add_of_pos_right (Metric.infDist ustar (K : Set V)) (div_pos hε hMc))
    calc ‖ustar - u‖ ≤ M / c * ‖ustar - v‖ := norm_sub_le hc hM ha hN hstar hv
      _ = M / c * dist ustar v := by rw [dist_eq_norm]
      _ ≤ M / c * (Metric.infDist ustar (K : Set V) + ε / (M / c)) :=
          mul_le_mul_of_nonneg_left hvd.le hMc.le
      _ = M / c * Metric.infDist ustar (K : Set V) + ε := by field_simp

/-- Hermitian case: `u_N` is the best approximation to `u` in the energy norm, that is, the
orthogonal projection of `u` onto `K` for the inner product `a`.  This is the remark following
Céa's inequality in Atkinson–Han, *Theoretical Numerical Analysis*, Prop 9.1.3; it is the exact
form of the equivalence between the Galerkin problem (9.1.4) and the Ritz problem (9.1.8) of
minimizing the energy functional (9.1.7) over `K`.

The hypothesis `hpos : a.IsCoerciveWith 0` was added to the original statement, which is false
without it: take `V = ℝ²`, `a = diag (1, -1)`, `K = span (1, 2)`, `ustar = (3, 0)` and
`ℓ = a ustar`.  Then `u = (-1, -2)` is the Galerkin solution and `v = 0 ∈ K` gives
`energyNorm (ustar - u) = √12 > 3 = energyNorm (ustar - v)`.  Positivity is exactly what makes
`energyNorm` a norm, so it is the minimal repair. -/
theorem energyNorm_sub_le (ha : a.IsHermitian) (hpos : a.IsCoerciveWith 0)
    (hN : IsGalerkinSolution a ℓ K u) {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) {v : V}
    (hv : v ∈ K) : a.energyNorm (ustar - u) ≤ a.energyNorm (ustar - v) := by
  have h0 : a (ustar - u) (u - v) = 0 := hN.apply_sub_eq_zero hstar (K.sub_mem hN.1 hv)
  have h0' : a (u - v) (ustar - u) = 0 := by
    rw [ha (u - v) (ustar - u), h0, map_zero]
  have hsum : (ustar - v : V) = (ustar - u) + (u - v) := by abel
  have hexp : RCLike.re (a (ustar - v) (ustar - v))
      = RCLike.re (a (ustar - u) (ustar - u)) + RCLike.re (a (u - v) (u - v)) := by
    rw [hsum]
    simp only [map_add, add_apply, h0, h0', add_zero, zero_add, map_add]
  rw [SesqForm.energyNorm, SesqForm.energyNorm, hexp]
  refine Real.sqrt_le_sqrt ?_
  have := hpos (u - v)
  simp only [zero_mul] at this
  linarith

/-- Hermitian sharpening of Céa's lemma: the constant improves from `M / c` to `√(M / c)`,
obtained by passing through the energy norm, in which `u_N` is exactly optimal, and paying the
norm equivalence `√c ‖·‖ ≤ ‖·‖_a ≤ √M ‖·‖` at each end. -/
theorem norm_sub_le_sqrt {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hh : a.IsHermitian) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) :
    ‖ustar - u‖ ≤ Real.sqrt (M / c) * ‖ustar - v‖ := by
  have hpos : a.IsCoerciveWith 0 := SesqForm.IsCoerciveWith.mono a ha hc.le
  have h1 : Real.sqrt c * ‖ustar - u‖ ≤ a.energyNorm (ustar - u) :=
    a.sqrt_mul_norm_le_energyNorm hc.le ha _
  have h2 := hN.energyNorm_sub_le hh hpos hstar hv
  have h3 : a.energyNorm (ustar - v) ≤ Real.sqrt M * ‖ustar - v‖ :=
    a.energyNorm_le_sqrt_mul_norm hM _
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [Real.sqrt_div' M hc.le, div_mul_eq_mul_div, le_div_iff₀ hsc, mul_comm]
  linarith

/-- Stiffness-matrix form (Atkinson–Han, *Theoretical Numerical Analysis*, (9.1.5)): with a basis
`φ` of `K`, `∑ ξ_j φ_j` is the Galerkin solution iff `(a (φ j) (φ i))_{ij} ξ = (ℓ (φ i))_i`.  The
matrix on the left is the stiffness matrix and the right-hand side the load vector, so this is the
step that turns the Galerkin problem into a linear system.

The statement was corrected from `.mulVec ξ` to `.mulVec (star ξ)`.  `a` is conjugate-linear in
its first slot, so `a (∑ ξ_j φ_j) φ_i = ∑ conj (ξ_j) * a (φ_j) (φ_i)`; over `ℝ` (`star = id`) this
is exactly the textbook statement. -/
theorem iff_mulVec {ι : Type*} [Fintype ι] (φ : Module.Basis ι 𝕜 K) (ξ : ι → 𝕜) :
    IsGalerkinSolution a ℓ K (∑ j, ξ j • (φ j : V)) ↔
      (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) = fun i => ℓ (φ i) := by
  have hmem : (∑ j, ξ j • (φ j : V)) ∈ K := K.sum_mem fun j _ => K.smul_mem _ (φ j).2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : V, u₀ = ∑ j, ξ j • (φ j : V) := ⟨_, rfl⟩
  have happ : ∀ w : V, a u₀ w = ∑ j, starRingEnd 𝕜 (ξ j) * a (φ j : V) w := by
    intro w
    rw [hu₀, map_sum]
    simp only [sum_apply, map_smulₛₗ, smul_apply,
      smul_eq_mul]
  rw [← hu₀] at hmem ⊢
  have hmul : ∀ i, (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) i
      = ∑ j, starRingEnd 𝕜 (ξ j) * a (φ j : V) (φ i) := by
    intro i
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.star_apply, starRingEnd_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hkey : (∀ i, a u₀ (φ i : V) = ℓ (φ i))
      ↔ (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) = fun i => ℓ (φ i) := by
    constructor
    · intro h
      funext i
      rw [hmul i, ← happ, h i]
    · intro h i
      have hi := congrFun h i
      rw [hmul i] at hi
      rw [happ]
      exact hi
  rw [← hkey]
  constructor
  · rintro ⟨-, h⟩ i
    exact h _ (φ i).2
  · intro h
    refine ⟨hmem, fun w hw => ?_⟩
    have heq : (((a u₀).comp K.subtypeL : K →L[𝕜] 𝕜) : K →ₗ[𝕜] 𝕜)
        = ((ℓ.comp K.subtypeL : K →L[𝕜] 𝕜) : K →ₗ[𝕜] 𝕜) :=
      φ.ext fun i => h i
    exact LinearMap.congr_fun heq ⟨w, hw⟩

end IsGalerkinSolution

/-- Distances to a monotone family of subspaces with dense union tend to zero.  This is the
approximation-theoretic half shared by Atkinson–Han, *Theoretical Numerical Analysis*, Cor 9.1.4
and Cor 9.2.3; combined with a quasi-optimality bound it gives convergence of the discrete
solutions. -/
theorem tendsto_infDist_of_monotone_dense {K : ℕ → Submodule 𝕜 V} (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set V))) (u : V) :
    Filter.Tendsto (fun n => Metric.infDist u (K n : Set V)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp (hdense u) ε hε
  obtain ⟨N, hwN⟩ := Set.mem_iUnion.mp hw
  refine ⟨N, fun n hn => ?_⟩
  have hmem : w ∈ (K n : Set V) := hmono hn hwN
  have h1 : Metric.infDist u (K n : Set V) ≤ dist u w := Metric.infDist_le_dist_of_mem hmem
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  linarith

/-- Atkinson–Han, *Theoretical Numerical Analysis*, Cor 9.1.4: Galerkin solutions on a monotone
family of subspaces whose union is dense converge to the exact solution. -/
theorem IsGalerkinSolution.tendsto {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜} {M c : ℝ} (hc : 0 < c)
    (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c) {K : ℕ → Submodule 𝕜 V}
    (hmono : Monotone K) (hdense : Dense (⋃ n, (K n : Set V))) {uN : ℕ → V}
    (hN : ∀ n, IsGalerkinSolution a ℓ (K n) (uN n))
    {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) :
    Filter.Tendsto uN Filter.atTop (nhds ustar) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := max (M / c) 1 with hC
  have hC0 : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp (hdense ustar) (ε / C) (by positivity)
  obtain ⟨N, hwN⟩ := Set.mem_iUnion.mp hw
  refine ⟨N, fun n hn => ?_⟩
  have hmem : w ∈ K n := hmono hn hwN
  have h1 : ‖ustar - uN n‖ ≤ M / c * ‖ustar - w‖ := (hN n).norm_sub_le hc hM ha hstar hmem
  have h2 : ‖ustar - w‖ < ε / C := by rwa [← dist_eq_norm]
  have h3 : M / c * ‖ustar - w‖ ≤ C * ‖ustar - w‖ := by
    gcongr
    exact le_max_left _ _
  have h4 : C * ‖ustar - w‖ < ε := by
    calc C * ‖ustar - w‖ < C * (ε / C) := by gcongr
      _ = ε := by field_simp
  rw [dist_eq_norm, norm_sub_rev]
  linarith

namespace IsPetrovGalerkinSolution

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] {a : SesqForm₂ 𝕜 U V}
  {ℓ : V →L[𝕜] 𝕜} {K : Submodule 𝕜 U} {L : Submodule 𝕜 V} {u : U}

/-- The discrete inf–sup condition (Atkinson–Han, *Theoretical Numerical Analysis*, (9.2.6)):
`α ‖w‖ ≤ sup_{v ∈ L, v ≠ 0} |a w v| / ‖v‖` for `w ∈ K`, stated with the restricted functional's
norm.  It is the discrete counterpart of `SesqForm₂.InfSupWith`, and does *not* follow from it:
the supremum is taken over the smaller test space `L`. -/
def DiscreteInfSup (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (α : ℝ) :
    Prop :=
  ∀ w ∈ K, α * ‖w‖ ≤ ‖(a w).comp L.subtypeL‖

/-- The Riesz operator of the form restricted to `K × L`.  Both `a` and the inverse Riesz map
are conjugate-linear, so the composite is *linear*; only linearity (not continuity) is needed
below, so this is packaged as a plain `LinearMap`. -/
private noncomputable def rieszOp (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U)
    (L : Submodule 𝕜 V) [CompleteSpace L] : K →ₗ[𝕜] L where
  toFun w := (InnerProductSpace.toDual 𝕜 L).symm (SesqForm₂.restrict a K L w)
  map_add' x y := by simp
  map_smul' r x := by
    simp only [map_smulₛₗ, RingHom.id_apply, starRingEnd_self_apply]

private theorem inner_rieszOp (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V)
    [CompleteSpace L] (w : K) (v : L) :
    inner 𝕜 (rieszOp a K L w) v = a (w : U) (v : V) := by
  change inner 𝕜 ((InnerProductSpace.toDual 𝕜 L).symm (SesqForm₂.restrict a K L w)) v = _
  exact InnerProductSpace.toDual_symm_apply

private theorem norm_rieszOp_apply (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V)
    [CompleteSpace L] (w : K) : ‖rieszOp a K L w‖ = ‖(a (w : U)).comp L.subtypeL‖ := by
  change ‖(InnerProductSpace.toDual 𝕜 L).symm (SesqForm₂.restrict a K L w)‖ = _
  exact (InnerProductSpace.toDual 𝕜 L).symm.norm_map _

/-- Babuška (Atkinson–Han, *Theoretical Numerical Analysis*, Thm 9.2.1): with `dim K = dim L` and
the discrete inf–sup condition, the Petrov–Galerkin problem is uniquely solvable.  The equal
dimensions turn injectivity into surjectivity, so no density argument is needed here. -/
theorem existsUnique [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) : ∃! u, IsPetrovGalerkinSolution a ℓ K L u := by
  have hbd : ∀ w : K, α * ‖w‖ ≤ ‖rieszOp a K L w‖ := fun w => by
    rw [norm_rieszOp_apply]
    exact hinf (w : U) w.2
  have hinj : Function.Injective (rieszOp a K L) := by
    intro x y hxy
    have hx := hbd (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at hx
    have hx0 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hx0)
  have hsurj : Function.Surjective (rieszOp a K L) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨w, hw⟩ := hsurj (SesqForm.rieszRep (ℓ.comp L.subtypeL))
  have hw' : rieszOp a K L w = SesqForm.rieszRep (ℓ.comp L.subtypeL) := hw
  refine ⟨(w : U), ⟨w.2, fun v hv => ?_⟩, ?_⟩
  · have h1 := inner_rieszOp a K L w ⟨v, hv⟩
    rw [hw', SesqForm.inner_rieszRep] at h1
    exact h1.symm
  · rintro y ⟨hyK, hy⟩
    have hkey : rieszOp a K L ⟨y, hyK⟩ = rieszOp a K L w := by
      rw [hw']
      refine ext_inner_right 𝕜 fun v => ?_
      rw [inner_rieszOp, SesqForm.inner_rieszRep]
      exact hy (v : V) v.2
    exact congrArg Subtype.val (hinj hkey)

set_option linter.unusedVariables false in
/-- Babuška's quasi-optimality bound `‖u - u_N‖ ≤ (1 + M / α) ‖u - w‖` (Atkinson–Han, *Theoretical
Numerical Analysis*, estimate (9.2.7) of Thm 9.2.1): the Petrov–Galerkin analogue of Céa's lemma.

The hypothesis `hM0 : 0 ≤ M` was added: the statement is false without it.  Take `V = 0`,
`U = ℝ`, `K = L = 0`, `a = 0`, `α = 1`, `M = -1`; every hypothesis holds vacuously and the
conclusion reads `‖ustar‖ ≤ 0`. -/
theorem norm_sub_le [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {M α : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hM : ∀ w v, ‖a w v‖ ≤ M * ‖w‖ * ‖v‖) (hinf : DiscreteInfSup a K L α)
    (hN : IsPetrovGalerkinSolution a ℓ K L u) {ustar : U} (hstar : ∀ v, a ustar v = ℓ v) {w : U}
    (hw : w ∈ K) : ‖ustar - u‖ ≤ (1 + M / α) * ‖ustar - w‖ := by
  -- the restricted functionals of `u - w` and of `ustar - w` agree on `L`
  have hres : (a (u - w)).comp L.subtypeL = (a (ustar - w)).comp L.subtypeL := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_sub,
      sub_apply, hN.2 (v : V) v.2, hstar (v : V)]
  have hMnn : 0 ≤ M * ‖ustar - w‖ := mul_nonneg hM0 (norm_nonneg _)
  have hbound : ‖(a (ustar - w)).comp L.subtypeL‖ ≤ M * ‖ustar - w‖ :=
    ContinuousLinearMap.opNorm_le_bound _ hMnn fun v => hM (ustar - w) (v : V)
  have huw : α * ‖u - w‖ ≤ M * ‖ustar - w‖ := by
    calc α * ‖u - w‖ ≤ ‖(a (u - w)).comp L.subtypeL‖ := hinf _ (K.sub_mem hN.1 hw)
      _ = ‖(a (ustar - w)).comp L.subtypeL‖ := by rw [hres]
      _ ≤ M * ‖ustar - w‖ := hbound
  have huw' : ‖u - w‖ ≤ M / α * ‖ustar - w‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα, mul_comm]
    exact huw
  have htri : ‖ustar - u‖ ≤ ‖ustar - w‖ + ‖w - u‖ := by
    simpa [dist_eq_norm] using dist_triangle ustar w u
  calc ‖ustar - u‖ ≤ ‖ustar - w‖ + ‖w - u‖ := htri
    _ = ‖ustar - w‖ + ‖u - w‖ := by rw [norm_sub_rev w u]
    _ ≤ ‖ustar - w‖ + M / α * ‖ustar - w‖ := by linarith
    _ = (1 + M / α) * ‖ustar - w‖ := by ring

/-- Atkinson–Han, *Theoretical Numerical Analysis*, Cor 9.2.3: under a discrete inf–sup condition
holding with one constant `α` for the whole family, and with trial spaces that are monotone with
dense union, the Petrov–Galerkin solutions converge.  The hypothesis `hM0 : 0 ≤ M` was added, as in
`IsPetrovGalerkinSolution.norm_sub_le`. -/
theorem tendsto {K : ℕ → Submodule 𝕜 U} {L : ℕ → Submodule 𝕜 V} [∀ n, FiniteDimensional 𝕜 (K n)]
    [∀ n, FiniteDimensional 𝕜 (L n)] (hdim : ∀ n, Module.finrank 𝕜 (K n) = Module.finrank 𝕜 (L n))
    {M α : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M) (hM : ∀ w v, ‖a w v‖ ≤ M * ‖w‖ * ‖v‖)
    (hinf : ∀ n, DiscreteInfSup a (K n) (L n) α) (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set U))) {uN : ℕ → U}
    (hN : ∀ n, IsPetrovGalerkinSolution a ℓ (K n) (L n) (uN n)) {ustar : U}
    (hstar : ∀ v, a ustar v = ℓ v) : Filter.Tendsto uN Filter.atTop (nhds ustar) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := max (1 + M / α) 1 with hC
  have hC0 : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp (hdense ustar) (ε / C) (by positivity)
  obtain ⟨N, hwN⟩ := Set.mem_iUnion.mp hw
  refine ⟨N, fun n hn => ?_⟩
  have hmem : w ∈ K n := hmono hn hwN
  have h1 : ‖ustar - uN n‖ ≤ (1 + M / α) * ‖ustar - w‖ :=
    norm_sub_le (hdim n) hα hM0 hM (hinf n) (hN n) hstar hmem
  have h2 : ‖ustar - w‖ < ε / C := by rwa [← dist_eq_norm]
  have h3 : (1 + M / α) * ‖ustar - w‖ ≤ C * ‖ustar - w‖ := by
    gcongr
    exact le_max_left _ _
  have h4 : C * ‖ustar - w‖ < ε := by
    calc C * ‖ustar - w‖ < C * (ε / C) := by gcongr
      _ = ε := by field_simp
  rw [dist_eq_norm, norm_sub_rev]
  linarith

end IsPetrovGalerkinSolution

section Strang

/-! ### The generalized Galerkin method

Following Atkinson–Han, *Theoretical Numerical Analysis*, §9.3, where the discrete space is no
longer required to be a subspace of `V` and the form and functional are themselves approximated,
so that the error picks up a consistency term on top of the approximation term.

Stated here on one abstract normed space `W` (their `V + V_N` carrying the discretization-dependent
norm `‖·‖_N`): the exact solution `u`, a form `a_N` bounded on `W × K` and coercive on `K`, a
functional `ℓ_N` on `K`; the Hilbert space `V` and the original problem never enter. -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The generalized Galerkin problem `u_N ∈ K`, `a_N u_N v = ℓ_N v` for all `v ∈ K`
(Atkinson–Han, *Theoretical Numerical Analysis*, (9.3.1)). -/
def IsGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜) (K : Submodule 𝕜 W)
    (uN : W) : Prop :=
  uN ∈ K ∧ ∀ v ∈ K, aN uN v = ℓN v

set_option linter.unusedVariables false in
/-- Strang's first lemma (Atkinson–Han, *Theoretical Numerical Analysis*, Thm 9.3.1, estimate
(9.3.2)): with `a_N` bounded by `M` on `W × K` and coercive with constant `c` on `K`,
`‖u - u_N‖ ≤ (1 + M/c) ‖u - v‖ + δ/c`, where `δ` bounds the consistency error
`|a_N(u, w) - ℓ_N(w)| / ‖w‖` over `w ∈ K`.  The first term is the Céa-type approximation error and
the second measures how far the exact solution is from solving the perturbed problem; when
`a_N = a` and `ℓ_N = ℓ` one may take `δ = 0` and recover Céa's lemma.

The hypotheses `hM0 : 0 ≤ M` and `hδ0 : 0 ≤ δ` were added: they do not follow from the bounds,
which are vacuous when `K = ⊥`, and without them the statement is false (`W = ℝ`, `K = ⊥`,
`c = 1`, `M = δ = -1`, `u = uN = v = 0` gives `0 ≤ -1`). -/
theorem strang_first {aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜} {ℓN : W →ₗ[𝕜] 𝕜} {K : Submodule 𝕜 W} {M c : ℝ}
    (hc : 0 < c) (hM0 : 0 ≤ M) (hM : ∀ w, ∀ v ∈ K, ‖aN w v‖ ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) {uN : W}
    (hN : IsGeneralizedGalerkinSolution aN ℓN K uN) (u : W) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ w ∈ K, ‖aN u w - ℓN w‖ ≤ δ * ‖w‖) {v : W} (hv : v ∈ K) :
    ‖u - uN‖ ≤ (1 + M / c) * ‖u - v‖ + δ / c := by
  have hwK : uN - v ∈ K := K.sub_mem hN.1 hv
  have hkey : c * ‖uN - v‖ ^ 2
      ≤ ‖aN u (uN - v) - ℓN (uN - v)‖ + ‖aN (u - v) (uN - v)‖ := by
    have hid : aN (uN - v) (uN - v)
        = -(aN u (uN - v) - ℓN (uN - v)) + aN (u - v) (uN - v) := by
      simp only [map_sub, LinearMap.sub_apply, hN.2 uN hN.1, hN.2 v hv]
      ring
    calc c * ‖uN - v‖ ^ 2 ≤ RCLike.re (aN (uN - v) (uN - v)) := hcoer _ hwK
      _ ≤ ‖aN (uN - v) (uN - v)‖ := RCLike.re_le_norm _
      _ ≤ ‖aN u (uN - v) - ℓN (uN - v)‖ + ‖aN (u - v) (uN - v)‖ := by
          rw [hid]
          exact le_trans (norm_add_le _ _) (by rw [norm_neg])
  have hbound : c * ‖uN - v‖ ^ 2 ≤ (δ + M * ‖u - v‖) * ‖uN - v‖ := by
    have h1 := hδ _ hwK
    have h2 := hM (u - v) _ hwK
    nlinarith
  have hstep : c * ‖uN - v‖ ≤ δ + M * ‖u - v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (uN - v)) with h | h
    · rw [← h, mul_zero]
      have := mul_nonneg hM0 (norm_nonneg (u - v))
      linarith
    · refine le_of_mul_le_mul_right ?_ h
      calc c * ‖uN - v‖ * ‖uN - v‖ = c * ‖uN - v‖ ^ 2 := by ring
        _ ≤ (δ + M * ‖u - v‖) * ‖uN - v‖ := hbound
  have htri : ‖u - uN‖ ≤ ‖u - v‖ + ‖v - uN‖ := by
    simpa [dist_eq_norm] using dist_triangle u v uN
  calc ‖u - uN‖ ≤ ‖u - v‖ + ‖v - uN‖ := htri
    _ = ‖u - v‖ + ‖uN - v‖ := by rw [norm_sub_rev v uN]
    _ ≤ ‖u - v‖ + (δ + M * ‖u - v‖) / c := by
        gcongr
        rw [le_div_iff₀ hc, mul_comm]
        exact hstep
    _ = (1 + M / c) * ‖u - v‖ + δ / c := by field_simp; ring

/-- Unique solvability of the generalized Galerkin problem on a finite-dimensional `K` with
coercive `a_N` (needs only finite dimension, not Lax–Milgram). -/
theorem existsUnique_isGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜)
    (K : Submodule 𝕜 W) [FiniteDimensional 𝕜 K] {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) :
    ∃! uN, IsGeneralizedGalerkinSolution aN ℓN K uN := by
  set T : K →ₗ[𝕜] Module.Dual 𝕜 K := K.subtype.dualMap ∘ₗ (aN ∘ₗ K.subtype) with hT
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h := hcoer (w : W) w.2
    rw [show aN (w : W) (w : W) = T w w from rfl, hw] at h
    simp only [LinearMap.zero_apply, map_zero] at h
    have hw2 : ‖(w : W)‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hc
    have hw0 : ‖(w : W)‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hw2 (sq_nonneg _))
    exact Subtype.ext (norm_eq_zero.mp hw0)
  have hTsurj : Function.Surjective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hTinj
    exact (Subspace.dual_finrank_eq).symm
  obtain ⟨w, hw⟩ := hTsurj (K.subtype.dualMap ℓN)
  refine ⟨(w : W), ⟨w.2, fun v hv => ?_⟩, ?_⟩
  · exact congrArg (fun f => f ⟨v, hv⟩) hw
  · rintro y ⟨hyK, hy⟩
    have hTy : T ⟨y, hyK⟩ = T w := by
      rw [hw]
      ext z
      exact hy (z : W) z.2
    exact congrArg Subtype.val (hTinj hTy)

end Strang
