import Numlib.Variational.Galerkin
import NumlibSurface.AtkinsonHan.Chapter09.Section01

/-!
# The generalized Galerkin method and Strang's first lemma (§9.3)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

In §9.3 the discrete space `V_N` need no longer be a subspace of `V`, and the form and the
functional are themselves approximated by `a_N` and `ℓ_N`.  The book carries out the analysis on
`V + V_N` equipped with the discretization-dependent norm `‖·‖_N`; since the theorem is stated
for one `N` at a time, that space is here simply an abstract real normed space `W`, which is also
how the backbone states it.  `theorem_9_3_1` is Theorem 9.3.1 (Strang's first lemma) with the error
bound (9.3.2), and `theorem_9_3_1'` re-attaches the book's data (`V` Hilbert, the exact solution
`u ∈ V` of (9.1.1), an injection `ι : V → W`), which the proof never uses.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan

/-- The generalized Galerkin problem (9.3.1): `u_N ∈ V_N`, `a_N(u_N, v) = ℓ_N(v)` for all
`v ∈ V_N`, on a space `W` playing the role of `V + V_N` with the norm `‖·‖_N`. -/
abbrev GeneralizedGalerkinProblem {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ) (VN : Submodule ℝ W) (uN : W) : Prop :=
  IsGeneralizedGalerkinSolution aN ℓN VN uN

namespace Ch09

section Strang

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ} {ℓN : W →ₗ[ℝ] ℝ} {VN : Submodule ℝ W} {M α₀ c₀ : ℝ}

/-- The consistency error of (9.3.2): `sup_{0 ≠ v_N ∈ V_N} |a_N(u, v_N) − ℓ_N(v_N)|/‖v_N‖`. -/
noncomputable def consistencyError (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) (u : W) : ℝ :=
  ⨆ v : {v : VN // v ≠ 0},
    |aN u ((v : VN) : W) - ℓN ((v : VN) : W)| / ‖((v : VN) : W)‖

theorem consistencyError_nonneg (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) (u : W) : 0 ≤ consistencyError aN ℓN VN u :=
  Real.iSup_nonneg fun _ => by positivity

private theorem bddAbove_consistency (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W) :
    BddAbove (Set.range fun v : {v : VN // v ≠ 0} =>
      |aN u ((v : VN) : W) - ℓN ((v : VN) : W)| / ‖((v : VN) : W)‖) := by
  refine ⟨M * ‖u‖ + c₀, Set.forall_mem_range.2 fun v => ?_⟩
  have hv : ((v : VN) : W) ≠ 0 := fun h => v.2 (Subtype.ext h)
  have hvpos : (0 : ℝ) < ‖((v : VN) : W)‖ := norm_pos_iff.mpr hv
  rw [div_le_iff₀ hvpos]
  have h1 := hM u ((v : VN) : W) (v : VN).2
  have h2 := hℓ ((v : VN) : W) (v : VN).2
  calc |aN u ((v : VN) : W) - ℓN ((v : VN) : W)|
      ≤ |aN u ((v : VN) : W)| + |ℓN ((v : VN) : W)| := abs_sub _ _
    _ ≤ M * ‖u‖ * ‖((v : VN) : W)‖ + c₀ * ‖((v : VN) : W)‖ := by gcongr
    _ = (M * ‖u‖ + c₀) * ‖((v : VN) : W)‖ := by ring

/-- The consistency error really does bound the residual of the exact solution on `V_N`. -/
theorem le_consistencyError (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W) {w : W} (hw : w ∈ VN) :
    ‖aN u w - ℓN w‖ ≤ consistencyError aN ℓN VN u * ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  · rw [Real.norm_eq_abs, ← div_le_iff₀ (norm_pos_iff.mpr hw0)]
    exact le_ciSup (bddAbove_consistency hM hℓ u)
      (⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩ : {v : VN // v ≠ 0})

/-- Theorem 9.3.1 (Strang's first lemma): the generalized Galerkin problem (9.3.1) is uniquely
solvable, and its error obeys (9.3.2)

`‖u − u_N‖_N ≤ (1 + M/α₀) inf_{w_N ∈ V_N} ‖u − w_N‖_N + α₀⁻¹ sup_{v_N ∈ V_N}
  |a_N(u,v_N) − ℓ_N(v_N)|/‖v_N‖_N`,

the sum of an approximation term of Céa type and a consistency term. -/
theorem theorem_9_3_1 (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ) (VN : Submodule ℝ W)
    [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M) (hα₀ : 0 < α₀)
    (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ VN, α₀ * ‖v‖ ^ 2 ≤ aN v v) (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W) :
    (∃! uN, GeneralizedGalerkinProblem aN ℓN VN uN) ∧
      ∀ uN, GeneralizedGalerkinProblem aN ℓN VN uN →
        ‖u - uN‖ ≤ (1 + M / α₀) * (⨅ w : VN, ‖u - (w : W)‖)
          + 1 / α₀ * consistencyError aN ℓN VN u := by
  refine ⟨existsUnique_isGeneralizedGalerkinSolution aN ℓN VN hα₀ hcoer, fun uN huN => ?_⟩
  have hC : 0 < 1 + M / α₀ := by
    have : 0 ≤ M / α₀ := div_nonneg hM0 hα₀.le
    linarith
  set δ := consistencyError aN ℓN VN u with hδdef
  have hδ0 : 0 ≤ δ := consistencyError_nonneg aN ℓN VN u
  have hpt : ∀ w : VN, ‖u - uN‖ - δ / α₀ ≤ (1 + M / α₀) * ‖u - (w : W)‖ := by
    intro w
    have := strang_first (𝕜 := ℝ) hα₀ hM0 hM hcoer huN u hδ0
      (fun z hz => le_consistencyError hM hℓ u hz) w.2
    linarith
  have hkey : ∀ w : VN, (‖u - uN‖ - δ / α₀) / (1 + M / α₀) ≤ ‖u - (w : W)‖ := by
    intro w
    rw [div_le_iff₀ hC, mul_comm]
    exact hpt w
  have hle := le_ciInf hkey
  rw [div_le_iff₀ hC] at hle
  have hδα : 1 / α₀ * δ = δ / α₀ := by ring
  rw [hδα]
  linarith [hle]

set_option linter.unusedVariables false in
/-- Theorem 9.3.1 in the book's setting: `V` is the Hilbert space of (9.1.1) with its exact
solution `u`, and `ι` embeds it into the space `W = V + V_N` carrying the norm `‖·‖_N`.  Neither
`V` nor `ι` enters the proof: the estimate is entirely about `W`. -/
theorem theorem_9_3_1' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (a : BilinForm V) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M) (hα₀ : 0 < α₀)
    (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ VN, α₀ * ‖v‖ ^ 2 ≤ aN v v) (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) :
    (∃! uN, GeneralizedGalerkinProblem aN ℓN VN uN) ∧
      ∀ uN, GeneralizedGalerkinProblem aN ℓN VN uN →
        ‖ι u - uN‖ ≤ (1 + M / α₀) * (⨅ w : VN, ‖ι u - (w : W)‖)
          + 1 / α₀ * consistencyError aN ℓN VN (ι u) :=
  theorem_9_3_1 aN ℓN VN hM0 hα₀ hM hcoer hℓ (ι u)

end Strang

/-- Exercise 9.3.1, the conforming case `V_N ⊂ V`, `a_N = a`, `ℓ_N = ℓ`: the consistency term of
(9.3.2) vanishes, and Strang's estimate becomes an inequality of the form (9.1.11),
`‖u − u_N‖ ≤ (1 + M/c₀) ‖u − v‖`. -/
theorem exercise_9_3_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : BilinForm V)
    (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V) {M c₀ : ℝ} (hM0 : 0 ≤ M) (hc₀ : 0 < c₀)
    (hM : a.IsBoundedWith M) (ha : a.IsEllipticWith c₀) {u uN : V} (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ (1 + M / c₀) * ‖u - v‖ := by
  have hres : ∀ w ∈ VN, ‖a u w - (ℓ : V →ₗ[ℝ] ℝ) w‖ ≤ (0 : ℝ) * ‖w‖ := by
    intro w _
    simp [hu w]
  have h := strang_first (𝕜 := ℝ) (aN := a) (ℓN := (ℓ : V →ₗ[ℝ] ℝ)) (K := VN) hc₀ hM0
    (fun w v _ => hM w v) (fun v _ => ha v) huN u le_rfl hres hv
  simpa using h

end Ch09

end AtkinsonHan
