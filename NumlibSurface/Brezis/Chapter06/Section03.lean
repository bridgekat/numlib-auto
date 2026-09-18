import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Operator.Compact.Banach
import NumlibSurface.Brezis.Chapter06.Section01

/-!
# Brezis §6.3: the spectrum of a compact operator

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §6.3, for `T : E →L[ℝ] E` on a real Banach space
`E`. The book's resolvent set `ρ(T) = {λ ∈ ℝ | T - λI bijective}` is Mathlib's `resolventSet ℝ T`
(`λ ∈ ρ(T) ↔ IsUnit (algebraMap ℝ _ λ - T)`, and the units of `E →L[ℝ] E` are the bijective
operators by `ContinuousLinearMap.isUnit_iff_bijective`, which is Corollary 2.7 and needs `E`
complete), `σ(T)` is `spectrum ℝ T` and `EV(T)` is
`{λ | Module.End.HasEigenvalue (T : Module.End ℝ E) λ}`. Proposition 6.7 is Mathlib's
`spectrum.isCompact` / `spectrum.subset_closedBall_norm`; Theorem 6.8 and Lemma 6.2 delegate to
the backbone `Numlib/Analysis/Normed/Operator/Compact/Banach` (and Mathlib's Fredholm
alternative `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` for (b)). The examples of
Remarks 6 and 7 live on `ℓ² = lp (fun _ : ℕ => ℝ) 2`: the right shift is the backbone's
`lp.shiftRightL ℝ` (`Numlib/Analysis/Normed/Lp/Sequence`, shared with §11.4), restated here as
`rightShift`; Mathlib has no multiplication operators on `lp`, so `multiplicationOperator` is
defined here, by content (it belongs in the same backbone module). The unnumbered claim of the
Comments (3) that the null spaces of the powers of `T - λI` stabilize is `ascent_stabilizes`.

## Main results

* `mem_resolventSet_iff_bijective`, `mem_spectrum_iff_not_bijective`,
  `hasEigenvalue_iff_ker_ne_bot`, `exists_equiv_of_mem_resolventSet` — the Definition.
* `remark_6_6`, `rightShift`, `remark_6_6_rightShift`,
  `remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one`, `remark_6_6_rotation` — `EV(T) ⊆ σ(T)`,
  strictly for the right shift on `ℓ²`; both may be empty over `ℝ` (an operator with
  `T² = -I`, the rotation by `π/2` of `ℝ²`).
* `proposition_6_7`, `proposition_6_7_subset` — `σ(T)` is compact and `⊆ [-‖T‖, ‖T‖]`.
* `theorem_6_8_a`, `theorem_6_8_b`, `theorem_6_8_c`, `lemma_6_2` — the spectrum of a compact
  operator: `0 ∈ σ(T)` in infinite dimension, `σ(T) ∖ {0} = EV(T) ∖ {0}`, and `σ(T) ∖ {0}` is
  finite or a sequence tending to `0`, its points being isolated.
* `multiplicationOperator`, `remark_6_7_isCompactOperator`, `remark_6_7_spectrum` — every null
  sequence `(αₙ)` is `σ(T) ∖ {0}` for a compact `T`, the multiplication operator on `ℓ²`.
* `ascent_stabilizes` — the ascent of `T - λI` (Comments on Chapter 6, 3).
-/

open Filter Topology Module.End
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The resolvent set, the spectrum, the eigenvalues -/

/-- **The Definition of §6.3, resolvent set.** For `T ∈ L(E)`, `E` Banach, `λ ∈ ρ(T)` iff
`T - λI` is bijective from `E` onto `E`. -/
theorem mem_resolventSet_iff_bijective [CompleteSpace E] (T : E →L[ℝ] E) (μ : ℝ) :
    μ ∈ resolventSet ℝ T ↔ Function.Bijective (T - μ • (1 : E →L[ℝ] E)) := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff,
    ContinuousLinearMap.isUnit_iff_bijective]

/-- **The Definition of §6.3, spectrum**: `σ(T) = ℝ ∖ ρ(T)`, so `λ ∈ σ(T)` iff `T - λI` is not
bijective. -/
theorem mem_spectrum_iff_not_bijective [CompleteSpace E] (T : E →L[ℝ] E) (μ : ℝ) :
    μ ∈ spectrum ℝ T ↔ ¬ Function.Bijective (T - μ • (1 : E →L[ℝ] E)) := by
  rw [spectrum, Set.mem_compl_iff, mem_resolventSet_iff_bijective]

/-- **The Definition of §6.3, eigenvalues.** A real `λ` is an eigenvalue of `T` if
`N(T - λI) ≠ {0}`; `N(T - λI)` is the corresponding eigenspace (Mathlib's
`Module.End.eigenspace T λ`). -/
theorem hasEigenvalue_iff_ker_ne_bot (T : E →L[ℝ] E) (μ : ℝ) :
    HasEigenvalue (T : Module.End ℝ E) μ ↔ (T - μ • (1 : E →L[ℝ] E)).ker ≠ ⊥ := by
  have h : eigenspace (T : Module.End ℝ E) μ = (T - μ • (1 : E →L[ℝ] E)).ker := by
    ext x
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [hasEigenvalue_iff, h]

/-- "It is useful to keep in mind that if `λ ∈ ρ(T)` then `(T - λI)⁻¹ ∈ L(E)` (see Corollary
2.7)": `T - λI` is a continuous linear equivalence, whose inverse is bounded. -/
theorem exists_equiv_of_mem_resolventSet [CompleteSpace E] (T : E →L[ℝ] E) {μ : ℝ}
    (h : μ ∈ resolventSet ℝ T) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = T - μ • (1 : E →L[ℝ] E) := by
  obtain ⟨hinj, hsurj⟩ := (mem_resolventSet_iff_bijective T μ).1 h
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- **Remark 6, first sentence.** `EV(T) ⊆ σ(T)`. -/
theorem remark_6_6 [CompleteSpace E] {T : E →L[ℝ] E} {μ : ℝ}
    (h : HasEigenvalue (T : Module.End ℝ E) μ) : μ ∈ spectrum ℝ T := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact h.mem_spectrum

/-! ### The right shift on `ℓ²` -/

/-- **The right shift of Remark 6** on `ℓ² = lp (fun _ : ℕ => ℝ) 2`:
`S_r u = (0, u₁, u₂, …)`, i.e. `(S_r u) 0 = 0` and `(S_r u) (n + 1) = uₙ`; a bounded operator
(an isometry). It is the backbone's `lp.shiftRightL ℝ` (`Numlib/Analysis/Normed/Lp/Sequence`). -/
def rightShift : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  lp.shiftRightL ℝ

@[simp]
theorem rightShift_apply_zero (x : lp (fun _ : ℕ => ℝ) 2) : rightShift x 0 = 0 :=
  lp.shiftRightL_apply_zero ℝ x

@[simp]
theorem rightShift_apply_succ (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    rightShift x (n + 1) = x n :=
  lp.shiftRightL_apply_succ ℝ x n

/-- The right shift is an isometry. -/
theorem norm_rightShift_apply (x : lp (fun _ : ℕ => ℝ) 2) : ‖rightShift x‖ = ‖x‖ :=
  lp.norm_shiftRightL_apply ℝ x

/-- **Remark 6, the right shift.** For the right shift `S_r` on `ℓ²`, `0 ∈ σ(S_r)` while
`0 ∉ EV(S_r)`: the inclusion `EV(T) ⊆ σ(T)` can be strict (`N(T - λI) = {0}` and
`R(T - λI) ≠ E`). Equivalently, as Remark 5 says, `S_r` is injective but not surjective. -/
theorem remark_6_6_rightShift :
    (0 : ℝ) ∈ spectrum ℝ rightShift ∧
      ¬ HasEigenvalue (rightShift : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) 0 := by
  have hinj : Function.Injective rightShift := fun x y hxy => by
    ext n
    have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z (n + 1)) hxy
    simpa using this
  constructor
  · rw [mem_spectrum_iff_not_bijective, zero_smul, sub_zero]
    rintro ⟨-, hsurj⟩
    obtain ⟨x, hx⟩ := hsurj (lp.single 2 0 1)
    have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z 0) hx
    simp at this
  · rw [hasEigenvalue_iff_ker_ne_bot, zero_smul, sub_zero, not_not, LinearMap.ker_eq_bot,
      ContinuousLinearMap.coe_coe]
    exact hinj

/-- **Remark 6, "it may happen that `EV(T) = σ(T) = ∅`"** — the fact behind both of the book's
examples: a bounded operator `T` on a real Banach space with `T² = -I` has empty spectrum,
since `(T - λI)(T + λI) = -(I + λ²I)` is invertible for every real `λ`. (Also Exercise 6.16.) -/
theorem remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one [CompleteSpace E] {T : E →L[ℝ] E}
    (hT : T * T = -1) : spectrum ℝ T = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro μ hμ
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] at hμ
  refine hμ ⟨⟨μ • 1 - T, (μ ^ 2 + 1)⁻¹ • (μ • 1 + T), ?_, ?_⟩, rfl⟩
  · have h : (μ • (1 : E →L[ℝ] E) - T) * (μ • 1 + T) = (μ ^ 2 + 1) • 1 := by
      rw [sub_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        mul_smul_comm, one_mul, one_mul, mul_one, hT, smul_smul, add_smul, one_smul, ← sq]
      abel
    change (μ • 1 - T) * ((μ ^ 2 + 1)⁻¹ • (μ • 1 + T)) = 1
    rw [mul_smul_comm, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · have h : (μ • (1 : E →L[ℝ] E) + T) * (μ • 1 - T) = (μ ^ 2 + 1) • 1 := by
      rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        mul_smul_comm, one_mul, one_mul, mul_one, hT, smul_smul, add_smul, one_smul, ← sq]
      abel
    change ((μ ^ 2 + 1)⁻¹ • (μ • 1 + T)) * (μ • 1 - T) = 1
    rw [smul_mul_assoc, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- **Remark 6, the example**: the rotation by `π/2` in `ℝ²`, `R (x₀, x₁) = (-x₁, x₀)`, has
`σ(R) = ∅` and no eigenvalue. (The book's second example, the pairwise swap
`(u₁, u₂, u₃, u₄, …) ↦ (-u₂, u₁, -u₄, u₃, …)` on `ℓ²`, is the same fact
`remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one` for an operator with `T² = -I`.) -/
theorem remark_6_6_rotation :
    ∃ R : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      (∀ x, R x 0 = -x 1 ∧ R x 1 = x 0) ∧ spectrum ℝ R = ∅ ∧
        ∀ μ : ℝ, ¬ HasEigenvalue (R : Module.End ℝ (EuclideanSpace ℝ (Fin 2))) μ := by
  set R : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, -1; 1, 0] with hR
  have hsq : R * R = -1 := by
    rw [hR, ← map_mul, ← map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)), ← map_neg]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hspec := remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one hsq
  refine ⟨R, fun x => ?_, hspec, fun μ hμ => ?_⟩
  · have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
    rw [hR, hx, Matrix.toEuclideanCLM_toLp]
    constructor <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · have := remark_6_6 hμ
    rw [hspec] at this
    exact this

/-! ### Proposition 6.7 and Theorem 6.8 -/

/-- **Proposition 6.7, compactness.** The spectrum `σ(T)` of a bounded operator on a Banach
space is compact (`ρ(T)` is open by the contraction mapping principle, and `σ(T)` bounded). -/
theorem proposition_6_7 [CompleteSpace E] (T : E →L[ℝ] E) : IsCompact (spectrum ℝ T) :=
  spectrum.isCompact T

/-- **Proposition 6.7, the bound.** `σ(T) ⊆ [-‖T‖, +‖T‖]`. -/
theorem proposition_6_7_subset [CompleteSpace E] (T : E →L[ℝ] E) :
    spectrum ℝ T ⊆ Set.Icc (-‖T‖) ‖T‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  · have := spectrum.subset_closedBall_norm (𝕜 := ℝ) T
    rwa [Real.closedBall_eq_Icc, zero_sub, zero_add] at this

/-- **Theorem 6.8 (a).** Let `T ∈ K(E)` with `dim E = ∞`. Then `0 ∈ σ(T)`. -/
theorem theorem_6_8_a [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T)
    (hE : ¬ FiniteDimensional ℝ E) : (0 : ℝ) ∈ spectrum ℝ T :=
  hT.zero_mem_spectrum hE

/-- **Theorem 6.8 (b).** For `T ∈ K(E)`, `σ(T) ∖ {0} = EV(T) ∖ {0}` (the header's `dim E = ∞`
is not needed for this clause): Mathlib's Fredholm alternative. -/
theorem theorem_6_8_b [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    spectrum ℝ T \ {0} = {μ | HasEigenvalue (T : Module.End ℝ E) μ} \ {0} := by
  ext μ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hμ, hne⟩
    exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hne).2 hμ, hne⟩
  · rintro ⟨hμ, hne⟩
    exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hne).1 hμ, hne⟩

/-- **Theorem 6.8 (c).** For `T ∈ K(E)`, one of the following holds: `σ(T) ∖ {0}` is empty or
finite (the book's first two cases together), or `σ(T) ∖ {0}` is a sequence of distinct points
converging to `0`. -/
theorem theorem_6_8_c [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    (spectrum ℝ T \ {0}).Finite ∨
      ∃ f : ℕ → ℝ, Function.Injective f ∧ Set.range f = spectrum ℝ T \ {0} ∧
        Tendsto f atTop (𝓝 0) :=
  hT.finite_or_exists_enumeration_spectrum

/-- **Lemma 6.2.** Let `T ∈ K(E)` and `(λₙ)` a sequence of distinct real numbers with
`λₙ → λ` and `λₙ ∈ σ(T) ∖ {0}` for all `n`. Then `λ = 0`: all the points of `σ(T) ∖ {0}` are
isolated. (The backbone's form is stronger: any such sequence converges, to `0`.) -/
theorem lemma_6_2 [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) {l : ℕ → ℝ}
    (hl : Function.Injective l) (hmem : ∀ n, l n ∈ spectrum ℝ T \ {0}) {μ : ℝ}
    (hlim : Tendsto l atTop (𝓝 μ)) : μ = 0 := by
  have hev : ∀ n, HasEigenvalue (T : Module.End ℝ E) (l n) := fun n => by
    have := hmem n
    rw [theorem_6_8_b hT] at this
    exact this.1
  exact tendsto_nhds_unique hlim (hT.tendsto_zero_of_injective_of_forall_hasEigenvalue hl hev)

/-! ### The multiplication operators on `ℓ²` -/

/-- The pointwise product `(αₙ uₙ)ₙ`. -/
private def mulFun (α x : ℕ → ℝ) : ℕ → ℝ := fun n => α n * x n

private theorem norm_mulFun_le {α : ℕ → ℝ} {C : ℝ} (hα : ∀ n, |α n| ≤ C)
    (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) : ‖mulFun α x n‖ ≤ ‖(C • x) n‖ := by
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mulFun, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hα n).trans (le_abs_self C)) (abs_nonneg _)

private theorem memℓp_mulFun {α : ℕ → ℝ} {C : ℝ} (hα : ∀ n, |α n| ≤ C)
    (x : lp (fun _ : ℕ => ℝ) 2) : Memℓp (mulFun α x) 2 :=
  (lp.memℓp (C • x)).mono' (norm_mulFun_le hα x)

/-- **The multiplication operator of Remark 7** (and of Exercises 6.1, 6.17) on
`ℓ² = lp (fun _ : ℕ => ℝ) 2`, for a bounded sequence `α` (`|αₙ| ≤ C` for all `n`):
`T u = (α₁ u₁, α₂ u₂, …)`, a bounded operator of norm at most `|C|`. -/
def multiplicationOperator (α : ℕ → ℝ) {C : ℝ} (hα : ∀ n, |α n| ≤ C) :
    lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨mulFun α x, memℓp_mulFun hα x⟩
      map_add' := fun x y => by
        ext n
        change α n * (x + y) n = α n * x n + α n * y n
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c x => by
        ext n
        change α n * (c • x) n = c * (α n * x n)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    |C| (fun x => by
      have h := lp.norm_mono two_ne_zero (x := (⟨mulFun α x, memℓp_mulFun hα x⟩ : lp _ 2))
        (y := C • x) (norm_mulFun_le hα x)
      rwa [norm_smul, Real.norm_eq_abs] at h)

/-- The multiplication operator acts by `(T u)ₙ = αₙ uₙ`. -/
@[simp]
theorem multiplicationOperator_apply (α : ℕ → ℝ) {C : ℝ} (hα : ∀ n, |α n| ≤ C)
    (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) : multiplicationOperator α hα x n = α n * x n :=
  rfl

/-- The truncated sequence `(α₀, …, α_{n-1}, 0, 0, …)` is bounded by the bound of `α`. -/
private theorem abs_ite_lt_le {α : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |α n| ≤ C) (n k : ℕ) :
    |if k < n then α k else 0| ≤ C := by
  split_ifs
  · exact hC k
  · simpa using (abs_nonneg _).trans (hC 0)

/-- The truncated multiplication operator `Tₙ u = (α₁ u₁, …, αₙ uₙ, 0, 0, …)` has finite rank:
its range lies in the span of the first `n` unit vectors. -/
private theorem isFiniteRank_multiplicationOperator_truncation {α : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |α n| ≤ C) (n : ℕ) :
    IsFiniteRank (multiplicationOperator (fun k => if k < n then α k else 0)
      (abs_ite_lt_le hC n)) := by
  set G : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) := Submodule.span ℝ (Set.range fun k : Fin n =>
    (lp.single 2 (k : ℕ) (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2)) with hG
  have hspan : FiniteDimensional ℝ G := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  refine Submodule.finiteDimensional_of_le (S₂ := G) fun y hy => ?_
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hy
  have hx : multiplicationOperator (fun k => if k < n then α k else 0) (abs_ite_lt_le hC n) x =
      ∑ k ∈ Finset.range n, (α k * x k) • lp.single 2 k (1 : ℝ) := by
    ext m
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp [Pi.single_apply, Finset.sum_ite_eq, ite_mul]
  rw [ContinuousLinearMap.coe_coe, hx]
  exact Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, Finset.mem_range.1 hk⟩, rfl⟩)

/-- **Remark 7, compactness.** If `αₙ → 0` (so that `α` is bounded, by `C`), the multiplication
operator `T u = (α₁ u₁, α₂ u₂, …)` on `ℓ²` is compact: it is the norm limit of the finite-rank
truncations `Tₙ u = (α₁ u₁, …, αₙ uₙ, 0, 0, …)`, with `‖Tₙ - T‖ ≤ sup_{k ≥ n} |αₖ| → 0`. -/
theorem remark_6_7_isCompactOperator {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0)) {C : ℝ}
    (hC : ∀ n, |α n| ≤ C) : IsCompactOperator (multiplicationOperator α hC) := by
  refine corollary_6_2 (T := fun n =>
    multiplicationOperator (fun k => if k < n then α k else 0) (abs_ite_lt_le hC n))
    (fun n => isFiniteRank_multiplicationOperator_truncation hC n) ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hα (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le fun x => ?_
  have hle : ∀ k, ‖((multiplicationOperator (fun k => if k < n then α k else 0)
      (abs_ite_lt_le hC n) - multiplicationOperator α hC) x) k‖ ≤ ‖((ε / 2) • x) k‖ := by
    intro k
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      multiplicationOperator_apply, multiplicationOperator_apply, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_pos (half_pos hε)]
    split_ifs with hk
    · rw [sub_self, abs_zero]
      positivity
    · have h := hN k (by omega)
      rw [Real.dist_eq, sub_zero] at h
      rw [zero_mul, zero_sub, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg _)
  have h := lp.norm_mono two_ne_zero hle
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε)] at h

/-- The unit vectors `eₙ = lp.single 2 n 1` of `ℓ²` are eigenvectors of the multiplication
operator: `T eₙ = αₙ eₙ`. -/
private theorem multiplicationOperator_single (α : ℕ → ℝ) {C : ℝ} (hC : ∀ n, |α n| ≤ C)
    (n : ℕ) :
    multiplicationOperator α hC (lp.single 2 n (1 : ℝ)) = α n • lp.single 2 n (1 : ℝ) := by
  ext m
  rw [lp.coeFn_smul, Pi.smul_apply, multiplicationOperator_apply, smul_eq_mul, lp.single_apply,
    Pi.single_apply]
  split_ifs with h
  · subst h; ring
  · ring

/-- `ℓ²` is infinite dimensional: the unit vectors form an infinite orthonormal family. -/
private theorem not_finiteDimensional_lp : ¬ FiniteDimensional ℝ (lp (fun _ : ℕ => ℝ) 2) := by
  intro h
  have hon : Orthonormal ℝ fun n : ℕ => lp.single 2 n (1 : ℝ) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs <;> simp
  exact Module.Finite.not_linearIndependent_of_infinite _ hon.linearIndependent

/-- **Remark 7, the spectrum.** For a sequence `(αₙ)` converging to `0`, the multiplication
operator `T` on `ℓ²` has `σ(T) = {αₙ} ∪ {0}`; each `αₙ` is an eigenvalue (with eigenvector
`eₙ`), and `0` is an eigenvalue iff some `αₙ = 0` — so `0` may or may not belong to `EV(T)`
(and, when it does, `N(T)` may be finite or infinite dimensional). -/
theorem remark_6_7_spectrum {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0)) {C : ℝ}
    (hC : ∀ n, |α n| ≤ C) :
    spectrum ℝ (multiplicationOperator α hC) = Set.range α ∪ {0} ∧
      (∀ n, HasEigenvalue
        (multiplicationOperator α hC : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) (α n)) ∧
      (HasEigenvalue (multiplicationOperator α hC : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) 0 ↔
        ∃ n, α n = 0) := by
  have hev : ∀ n, HasEigenvalue
      (multiplicationOperator α hC : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) (α n) := fun n => by
    refine hasEigenvalue_of_hasEigenvector (x := lp.single 2 n (1 : ℝ)) ⟨?_, ?_⟩
    · rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe]
      exact multiplicationOperator_single α hC n
    · intro h
      have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) h
      simp at this
  refine ⟨?_, hev, ?_⟩
  · refine Set.Subset.antisymm ?_ ?_
    · -- `μ ∉ range α ∪ {0}` is in the resolvent set: `T - μ I` has the bounded inverse
      -- given by multiplication with `(αₙ - μ)⁻¹`
      intro μ hμ
      by_contra hnot
      rw [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, not_or, not_exists] at hnot
      obtain ⟨hne, hμ0⟩ := hnot
      -- a uniform lower bound `δ` on `|αₙ - μ|`
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hα (|μ| / 2) (by positivity)
      have hpos : ∀ n, 0 < |α n - μ| := fun n => abs_pos.2 (sub_ne_zero.2 (hne n))
      obtain ⟨n₀, -, hn₀⟩ := (Finset.range (N + 1)).exists_min_image
        (fun n => if n < N then |α n - μ| else |μ| / 2) ⟨N, Finset.mem_range.2 N.lt_succ_self⟩
      have hδpos : 0 < if n₀ < N then |α n₀ - μ| else |μ| / 2 := by
        split_ifs
        · exact hpos n₀
        · positivity
      have hδle : ∀ n, (if n₀ < N then |α n₀ - μ| else |μ| / 2) ≤ |α n - μ| := fun n => by
        by_cases hn : n < N
        · have := hn₀ n (Finset.mem_range.2 (by omega))
          simpa only [hn, ite_true] using this
        · have h1 := hn₀ N (Finset.mem_range.2 N.lt_succ_self)
          simp only [lt_irrefl, ite_false] at h1
          have h2 := hN n (by omega)
          rw [Real.dist_eq, sub_zero] at h2
          have h3 : |μ| - |α n| ≤ |α n - μ| := by
            rw [abs_sub_comm]
            exact abs_sub_abs_le_abs_sub μ (α n)
          linarith
      have hinv : ∀ n, |(α n - μ)⁻¹| ≤ (if n₀ < N then |α n₀ - μ| else |μ| / 2)⁻¹ := fun n => by
        rw [abs_inv]
        exact inv_anti₀ hδpos (hδle n)
      -- the inverse of `T - μ I`
      have hcoord : ∀ x : lp (fun _ : ℕ => ℝ) 2, ∀ n,
          ((multiplicationOperator α hC - μ • 1) x) n = (α n - μ) * x n := fun x n => by
        rw [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
          Pi.smul_apply, multiplicationOperator_apply, smul_eq_mul]
        ring
      have hunit : IsUnit (multiplicationOperator α hC - μ • 1) := by
        refine ⟨⟨multiplicationOperator α hC - μ • 1,
          multiplicationOperator (fun n => (α n - μ)⁻¹) hinv, ?_, ?_⟩, rfl⟩
        · ext x n
          rw [mul_apply_eq_comp, hcoord, multiplicationOperator_apply, one_apply_eq_self]
          field_simp [sub_ne_zero.2 (hne n)]
        · ext x n
          rw [mul_apply_eq_comp, multiplicationOperator_apply, hcoord, one_apply_eq_self]
          field_simp [sub_ne_zero.2 (hne n)]
      rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub] at hμ
      exact hμ hunit.neg
    · rintro μ (⟨n, rfl⟩ | rfl)
      · exact remark_6_6 (hev n)
      · exact theorem_6_8_a (remark_6_7_isCompactOperator hα hC) not_finiteDimensional_lp
  · constructor
    · intro h
      obtain ⟨x, hx, hx0⟩ := h.exists_hasEigenvector
      rw [mem_eigenspace_iff, zero_smul] at hx
      by_contra hcontra
      push Not at hcontra
      refine hx0 ?_
      ext n
      have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) hx
      simp only [ContinuousLinearMap.coe_coe, multiplicationOperator_apply] at this
      change x n = 0
      exact (mul_eq_zero.1 this).resolve_left (hcontra n)
    · rintro ⟨n, hn⟩
      have := hev n
      rwa [hn] at this

/-! ### The ascent of `T - λI` -/

/-- The kernels of the powers of `T - λI` and of `λI - T` agree. -/
private theorem ker_pow_sub_smul_one (T : E →L[ℝ] E) (μ : ℝ) (j : ℕ) :
    ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker = ((μ • (1 : E →L[ℝ] E) - T) ^ j).ker := by
  rw [← neg_sub, neg_pow]
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_one_pow, one_mul]
  · rw [hj.neg_one_pow, neg_one_mul, ContinuousLinearMap.toLinearMap_neg, LinearMap.ker_neg]

/-- **Comments on Chapter 6, 3 (multiplicity of eigenvalues).** Let `T ∈ K(E)` and
`λ ∈ σ(T) ∖ {0}`. The sequence `N((T - λI)^k)`, `k = 1, 2, …`, is strictly increasing up to
some finite `p` — the ascent of `T - λI`, which is `≥ 1` since `λ` is an eigenvalue — and then
stays constant; every `N((T - λI)^k)` is finite dimensional. -/
theorem ascent_stabilizes [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ T \ {0}) :
    ∃ p : ℕ, 1 ≤ p ∧
      (∀ j < p, ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker <
        ((T - μ • (1 : E →L[ℝ] E)) ^ (j + 1)).ker) ∧
      (∀ j, p ≤ j → ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker =
        ((T - μ • (1 : E →L[ℝ] E)) ^ p).ker) ∧
      ∀ j, FiniteDimensional ℝ ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker := by
  have hne : μ ≠ 0 := hμ.2
  obtain ⟨ν, hstrict, hstab, -, -⟩ := hT.exists_riesz_index hne
  simp only [ker_pow_sub_smul_one]
  refine ⟨ν, ?_, hstrict, hstab, fun j => ?_⟩
  swap
  · rw [ker_pow_sub_smul_one]
    exact hT.finiteDimensional_ker_pow hne j
  by_contra hν
  have hev : HasEigenvalue (T : Module.End ℝ E) μ := by
    have := hμ
    rw [theorem_6_8_b hT] at this
    exact this.1
  rw [hasEigenvalue_iff_ker_ne_bot, ← pow_one (T - μ • 1), ker_pow_sub_smul_one,
    hstab 1 (by omega), ← hstab 0 (by omega), pow_zero] at hev
  exact hev (Submodule.eq_bot_iff _ |>.2 fun u hu => by simpa using hu)

end Brezis.Chapter06

end
