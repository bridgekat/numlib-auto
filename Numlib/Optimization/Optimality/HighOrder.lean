import Numlib.Optimization.Optimality.Approximate
import Numlib.Optimization.Optimality.CurveConditions

/-!
# High-order approximate optimality through the Taylor-decrement measure

For derivative data `D` (exact data being `ftaylorSeries ℝ f x`), the Taylor-decrement measure
`taylorMeasure D j δ S = sup_{d ∈ S, ‖d‖ ≤ δ} ΔT_j(d)` is the book's `φ^δ_{f,j}(x)`
([cartis2022evaluation], (12.1.10)) when `S = univ`. This file relates it to the classical
optimality conditions of low order and to local minimizers.

## Main results

* `taylorMeasure_mono`, `taylorMeasure_le_taylorMeasure_succ_add`: monotonicity and the cascade
  estimate behind Theorem 12.1.7 (`taylorMeasure_le_of_taylorMeasure_succ_le`);
* `taylorMeasure_two_eq_zero_of_three`: Lemma B.12.1;
* `taylorMeasure_one_eq_zero_iff`, `neg_le_minCurvature_of_taylorMeasure_two_le`,
  `norm_sq_le_of_taylorMeasure_two_le`, `taylorMeasure_two_eq_zero_iff`,
  `abs_apply_three_le_taylorMeasure`: first-, second- and third-order readings of `φ_1, φ_2, φ_3`
  (Theorems 12.1.3, 12.1.6);
* `taylorMeasure_eq_zero_of_isLocalMin`, `exists_taylorMeasure_le_of_isLocalMin`,
  `tendsto_taylorMeasure_div_pow_of_isLocalMin`: local minimizers (Theorem 12.1.4);
* `isStrictLocalMin_taylorPolynomial_succ_of_growth`,
  `isStrictLocalMin_of_taylorPolynomial_growth`: corrected forms of Theorem 12.1.5.

## Implementation notes

Statements about the measure alone are stated for arbitrary data `D` (exact, inexact, or the jet
of a model). Low-order identifications are proved directly by testing the supremum at well-chosen
displacements (`±d`, `t • d`), avoiding the trust-region multiplier `(H + λI)^+` of the book's
proofs; the bound of Theorem 12.1.6 (ii) becomes explicit: `‖∇f‖² ≤ δ² ε max(‖∇²f‖, ε)`.

Theorem 12.1.5 is false as stated (an isolated minimizer of `T_{f,j}(x, ·)` need not have
uniform growth; see `isStrictLocalMin_taylorPolynomial_succ_of_growth` for a counterexample); the
sufficient conditions here assume growth of order `j`.
-/

open Finset Filter Metric Asymptotics
open scoped Nat Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Optimization

/-- Real-valued form of `ContinuousMultilinearMap.apply_smul_diag`: `A[t d]^n = t^n A[d]^n`. -/
private theorem apply_smul_diag_mul {n : ℕ} (A : E [×n]→L[ℝ] ℝ) (t : ℝ) (d : E) :
    (A fun _ => t • d) = t ^ n * A fun _ => d := by
  rw [ContinuousMultilinearMap.apply_smul_diag, smul_eq_mul]

section Measure

variable (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ} {δ : ℝ} {S : Set E}

omit [NormedSpace ℝ E] in
private theorem zero_mem_inter (hδ : 0 ≤ δ) (h0 : 0 ∈ S) : (0 : E) ∈ closedBall 0 δ ∩ S :=
  ⟨mem_closedBall_self hδ, h0⟩

private theorem le_taylorMeasure_univ {d : E} (hd : ‖d‖ ≤ δ) :
    D.taylorDecrement j d ≤ taylorMeasure D j δ Set.univ :=
  taylorDecrement_le_taylorMeasure D j ⟨by simpa using hd, Set.mem_univ _⟩

/-- Monotonicity of the measure in the radius and in the feasible set
([cartis2022evaluation], (12.1.10)). -/
theorem taylorMeasure_mono {δ' : ℝ} {S' : Set E} (h0 : 0 ∈ S) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ')
    (hSS' : S ⊆ S') : taylorMeasure D j δ S ≤ taylorMeasure D j δ' S' :=
  (decrementMeasure_mono_radius ⟨0, zero_mem_inter hδ h0⟩ (bddAbove_taylorDecrement D j δ' S)
    hδδ').trans (decrementMeasure_mono_set ⟨0, zero_mem_inter (hδ.trans hδδ') h0⟩
      (bddAbove_taylorDecrement D j δ' S') hSS')

/-- **Cascade estimate** (core of [cartis2022evaluation], Theorem 12.1.7):
`φ_j ≤ φ_{j+1} + ‖D_{j+1}‖ δ^{j+1}/(j+1)!`. -/
theorem taylorMeasure_le_taylorMeasure_succ_add (h0 : 0 ∈ S) (hδ : 0 ≤ δ) (j : ℕ) :
    taylorMeasure D j δ S ≤
      taylorMeasure D (j + 1) δ S + ‖D (j + 1)‖ * δ ^ (j + 1) / (j + 1)! := by
  refine decrementMeasure_le ⟨0, zero_mem_inter hδ h0⟩ fun d hd => ?_
  have h1 := taylorDecrement_le_taylorMeasure D (j + 1) hd
  have hd' : ‖d‖ ≤ δ := by simpa using hd.1
  have h2 : (D (j + 1) fun _ => d) ≤ ‖D (j + 1)‖ * δ ^ (j + 1) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (D.norm_apply_diagonal_le (j + 1) d).trans ?_
    gcongr
  rw [D.taylorDecrement_succ] at h1
  have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
  rw [div_eq_mul_inv, mul_comm _ ((j + 1)! : ℝ)⁻¹]
  nlinarith [inv_pos.2 hf]

/-- **Cascading approximate optimality** ([cartis2022evaluation], Theorem 12.1.7, with `j + 1` for
the book's `j`). If `φ_{j+1} ≤ ε δ^{j+1}/(j+1)!` with `0 ≤ ε ≤ ε'`, `δ ≤ 1` and
`2 ‖D_{j+1}‖ δ ≤ (j+1) ε`, then `φ_j ≤ ε' δ^j / j!`. -/
theorem taylorMeasure_le_of_taylorMeasure_succ_le (hj : 1 ≤ j) (h0 : 0 ∈ S) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) {ε ε' : ℝ} (hε : 0 ≤ ε) (hεε' : ε ≤ ε')
    (h : taylorMeasure D (j + 1) δ S ≤ ε * δ ^ (j + 1) / (j + 1)!)
    (hδε : 2 * ‖D (j + 1)‖ * δ ≤ (j + 1) * ε) :
    taylorMeasure D j δ S ≤ ε' * δ ^ j / j ! := by
  have hc := taylorMeasure_le_taylorMeasure_succ_add D h0 hδ0 j
  have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
  have hfs : ((j + 1)! : ℝ) = (j + 1) * j ! := by push_cast [Nat.factorial_succ]; ring
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpow : 0 ≤ δ ^ j := pow_nonneg hδ0 j
  -- `(ε δ + ‖D_{j+1}‖ δ) ≤ (j + 1) ε'`
  have key : ε * δ + ‖D (j + 1)‖ * δ ≤ (j + 1) * ε' := by nlinarith
  calc taylorMeasure D j δ S ≤ ε * δ ^ (j + 1) / (j + 1)! + ‖D (j + 1)‖ * δ ^ (j + 1) / (j + 1)! :=
        by linarith
    _ = δ ^ j * (ε * δ + ‖D (j + 1)‖ * δ) / ((j + 1) * j !) := by rw [hfs]; ring
    _ ≤ δ ^ j * ((j + 1) * ε') / ((j + 1) * j !) := by gcongr
    _ = ε' * δ ^ j / j ! := by field_simp

/-- **Lemma B.12.1** ([cartis2022evaluation]): if `φ_3^δ = 0` then `φ_2^δ = 0`. No symmetry of
the data is needed. -/
theorem taylorMeasure_two_eq_zero_of_three (hδ : 0 ≤ δ) (h : taylorMeasure D 3 δ Set.univ = 0) :
    taylorMeasure D 2 δ Set.univ = 0 := by
  refine le_antisymm (decrementMeasure_le ⟨0, zero_mem_inter hδ (Set.mem_univ _)⟩ fun s hs => ?_)
    (taylorMeasure_nonneg D _ (Set.mem_univ _) hδ)
  have hs' : ‖s‖ ≤ δ := by simpa using hs.1
  have h3 : ∀ t : E, ‖t‖ ≤ δ → D.taylorDecrement 3 t ≤ 0 := fun t ht =>
    h ▸ le_taylorMeasure_univ D ht
  by_contra! hpos
  rw [D.taylorDecrement_two] at hpos
  set a := D 1 fun _ => s
  set b := D 2 fun _ => s
  set c := D 3 fun _ => s
  have hp := h3 s hs'
  have hm := h3 (-s) (by simpa using hs')
  rw [D.taylorDecrement_three] at hp hm
  have h1m : (D 1 fun _ => -s) = -a := by
    rw [show -s = (-1 : ℝ) • s by simp, apply_smul_diag_mul]; ring
  have h2m : (D 2 fun _ => -s) = b := by
    rw [show -s = (-1 : ℝ) • s by simp, apply_smul_diag_mul]; ring
  have h3m : (D 3 fun _ => -s) = -c := by
    rw [show -s = (-1 : ℝ) • s by simp, apply_smul_diag_mul]; ring
  rw [h1m, h2m, h3m] at hm
  -- `ψ₂ := a + b/2 < 0`, `c > 0`, `b ≥ 0`
  have hb : 0 ≤ b := by linarith
  have hc : 0 < c := by linarith
  set ψ := a + b / 2 with hψ
  have hψneg : ψ < 0 := by linarith
  set α := min 1 (-ψ / (2 * (c / 6))) with hα
  have hα0 : 0 < α := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hα1 : α ≤ 1 := min_le_left _ _
  have hαc : α * (c / 6) ≤ -ψ / 2 := by
    have := min_le_right 1 (-ψ / (2 * (c / 6)))
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  have hαs : ‖α • s‖ ≤ δ := by
    rw [norm_smul, Real.norm_of_nonneg hα0.le]
    nlinarith [norm_nonneg s]
  have hq := h3 (α • s) hαs
  rw [D.taylorDecrement_three, apply_smul_diag_mul, apply_smul_diag_mul, apply_smul_diag_mul] at hq
  -- `ψ₃(α s) = α a + α² b/2 + α³ c/6 ≤ α (ψ + α c / 6) ≤ α ψ / 2 < 0`
  have hα2 : α ^ 2 ≤ α := by nlinarith
  have hα3 : α ^ 3 ≤ α ^ 2 := by nlinarith
  have e1 : α ^ 2 * b ≤ α * b := mul_le_mul_of_nonneg_right hα2 hb
  have e2 : α ^ 3 * c ≤ α ^ 2 * c := mul_le_mul_of_nonneg_right hα3 hc.le
  have e3 : α ^ 2 * (c / 6) ≤ α * (-ψ / 2) := by nlinarith
  nlinarith

/-- **First-order reading of `φ_1`** ([cartis2022evaluation], Theorem 12.1.3 (i)): for `δ > 0`,
`φ^δ_1 = 0` iff the first derivative vanishes. -/
theorem taylorMeasure_one_eq_zero_iff (hδ : 0 < δ) :
    taylorMeasure D 1 δ Set.univ = 0 ↔ D 1 = 0 := by
  rw [taylorMeasure_one_eq D hδ.le, mul_eq_zero, norm_eq_zero, or_iff_right hδ.ne']

/-- **Second-order reading of `φ_2`** ([cartis2022evaluation], Theorem 12.1.6 (ii), first part):
if `φ^δ_2 ≤ ε δ²/2` then `λ_min[D_2] ≥ -ε`. -/
theorem neg_le_minCurvature_of_taylorMeasure_two_le {ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (h : taylorMeasure D 2 δ Set.univ ≤ ε * δ ^ 2 / 2) : -ε ≤ minCurvature (D 2) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [minCurvature_of_subsingleton]
    linarith
  rw [le_minCurvature_iff]
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · rw [(D 2).map_coord_zero (m := fun _ => (0 : E)) 0 rfl]
    simp
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  set t := δ / ‖d‖
  have ht : 0 < t := div_pos hδ hdpos
  have hu : ‖t • d‖ ≤ δ := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_cancel₀ _ hdpos.ne']
  have h1 := (le_taylorMeasure_univ D (j := 2) hu).trans h
  have h2 := (le_taylorMeasure_univ D (j := 2) (d := (-t) • d)
    (by rwa [neg_smul, norm_neg])).trans h
  rw [D.taylorDecrement_two, apply_smul_diag_mul, apply_smul_diag_mul] at h1 h2
  have hsum : -(t ^ 2 * D 2 fun _ => d) ≤ ε * δ ^ 2 := by nlinarith
  have htd : t * ‖d‖ = δ := div_mul_cancel₀ _ hdpos.ne'
  have : t ^ 2 * (-ε * ‖d‖ ^ 2) ≤ t ^ 2 * D 2 fun _ => d := by
    have : t ^ 2 * ‖d‖ ^ 2 = δ ^ 2 := by rw [← mul_pow, htd]
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

/-- **First-order reading of `φ_2`**, explicit form of the book's `‖∇f‖ ≤ δ κ √ε₂`
([cartis2022evaluation], Theorem 12.1.6 (ii), second part, (12.1.27)–(12.1.29)): if
`φ^δ_2 ≤ ε δ²/2` then `‖D_1‖² ≤ δ² ε max(‖D_2‖, ε)`. -/
theorem norm_sq_le_of_taylorMeasure_two_le {ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (h : taylorMeasure D 2 δ Set.univ ≤ ε * δ ^ 2 / 2) :
    ‖D 1‖ ^ 2 ≤ δ ^ 2 * ε * max ‖D 2‖ ε := by
  set M := max ‖D 2‖ ε
  have hM2 : ‖D 2‖ ≤ M := le_max_left _ _
  have hMε : ε ≤ M := le_max_right _ _
  -- along `±t v`, `t |D_1 v| ≤ ε δ²/2 + t² M/2`
  have hline : ∀ v : E, ‖v‖ ≤ 1 → ∀ t, 0 ≤ t → t ≤ δ →
      t * |D 1 fun _ => v| ≤ ε * δ ^ 2 / 2 + t ^ 2 * M / 2 := by
    intro v hv t ht0 htδ
    have hn : ‖t • v‖ ≤ δ := by
      rw [norm_smul, Real.norm_of_nonneg ht0]
      nlinarith [norm_nonneg v]
    have h1 := (le_taylorMeasure_univ D (j := 2) hn).trans h
    have h2 := (le_taylorMeasure_univ D (j := 2) (d := (-t) • v)
      (by rwa [neg_smul, norm_neg])).trans h
    rw [D.taylorDecrement_two, apply_smul_diag_mul, apply_smul_diag_mul] at h1 h2
    have hD2 : |D 2 fun _ => v| ≤ M := by
      rw [← Real.norm_eq_abs]
      refine (D.norm_apply_diagonal_le 2 v).trans ?_
      calc ‖D 2‖ * ‖v‖ ^ 2 ≤ ‖D 2‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hv
        _ ≤ M := by rw [mul_one]; exact hM2
    have e : (t ^ 2 * D 2 fun _ => v) ≤ t ^ 2 * M :=
      mul_le_mul_of_nonneg_left (abs_le.1 hD2).2 (sq_nonneg t)
    simp only [pow_one, neg_sq, neg_mul] at h1 h2
    rcases abs_cases (D 1 fun _ => v) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;> linarith
  -- hence `|D_1 v|² ≤ δ² ε M` for `‖v‖ ≤ 1`
  have hunit : ∀ v : E, ‖v‖ ≤ 1 → |D 1 fun _ => v| ^ 2 ≤ δ ^ 2 * ε * M := by
    intro v hv
    set a := |D 1 fun _ => v|
    have ha : 0 ≤ a := abs_nonneg _
    have hM0 : 0 ≤ M := hε.trans hMε
    rcases le_or_gt a (δ * M) with haM | haM
    · rcases hM0.eq_or_lt with hM | hM
      · have : a = 0 := le_antisymm (by rw [← hM, mul_zero] at haM; exact haM) ha
        rw [this, ← hM]
        simp
      · have := hline v hv (a / M) (div_nonneg ha hM.le) ((div_le_iff₀ hM).2 (by linarith))
        have e : a / M * a = a ^ 2 / M := by ring
        have e2 : (a / M) ^ 2 * M / 2 = a ^ 2 / M / 2 := by field_simp
        rw [e, e2] at this
        have : a ^ 2 / M ≤ ε * δ ^ 2 := by linarith
        rw [div_le_iff₀ hM] at this
        linarith
    · exfalso
      have := hline v hv δ hδ.le le_rfl
      nlinarith
  -- operator norm
  set K := Real.sqrt (δ ^ 2 * ε * M)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = δ ^ 2 * ε * M := Real.sq_sqrt (by
    have : 0 ≤ M := hε.trans hMε
    positivity)
  have hbound : ∀ v : E, ‖v‖ ≤ 1 → |D 1 fun _ => v| ≤ K := fun v hv =>
    Real.abs_le_sqrt (by simpa [sq_abs] using hunit v hv)
  have hnorm : ‖D 1‖ ≤ K := by
    refine (D 1).opNorm_le_bound hK0 fun m => ?_
    have hm : m = fun _ => m 0 := funext fun i => by rw [Subsingleton.elim i 0]
    rw [hm]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
    set v := m 0
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv, (D 1).map_coord_zero (m := fun _ => (0 : E)) 0 rfl]
      simp
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖‖v‖⁻¹ • v‖ ≤ 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    have := hbound _ hu
    rw [apply_smul_diag_mul, pow_one, abs_mul, abs_of_pos (inv_pos.2 hvpos)] at this
    rw [Real.norm_eq_abs, mul_comm K]
    rwa [inv_mul_le_iff₀ hvpos] at this
  calc ‖D 1‖ ^ 2 ≤ K ^ 2 := by gcongr
    _ = δ ^ 2 * ε * M := hKsq

/-- **Second-order reading of `φ_2`** ([cartis2022evaluation], Theorem 12.1.3 (ii), (12.1.14)): for
`δ > 0`, `φ^δ_2 = 0` iff `D_1 = 0` and `λ_min[D_2] ≥ 0`. -/
theorem taylorMeasure_two_eq_zero_iff (hδ : 0 < δ) :
    taylorMeasure D 2 δ Set.univ = 0 ↔ D 1 = 0 ∧ 0 ≤ minCurvature (D 2) := by
  constructor
  · intro h
    have h' : taylorMeasure D 2 δ Set.univ ≤ 0 * δ ^ 2 / 2 := by simp [h]
    refine ⟨?_, by simpa using neg_le_minCurvature_of_taylorMeasure_two_le D hδ le_rfl h'⟩
    have := norm_sq_le_of_taylorMeasure_two_le D hδ le_rfl h'
    simp only [mul_zero, zero_mul] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
  · rintro ⟨h1, h2⟩
    refine le_antisymm (decrementMeasure_le ⟨0, zero_mem_inter hδ.le (Set.mem_univ _)⟩
      fun d _ => ?_) (taylorMeasure_nonneg D _ (Set.mem_univ _) hδ.le)
    rw [D.taylorDecrement_two, h1]
    have := (minCurvature_nonneg_iff.1 h2) d
    simp only [zero_apply, neg_zero, zero_sub]
    linarith

/-- **Third-order reading of `φ_3`** ([cartis2022evaluation], Theorem 12.1.3 (iii), (12.1.13),
(12.1.15)): on directions `d` with `‖d‖ ≤ 1`, `D_1[d] = 0` and `D_2[d]^2 = 0` (the subspace
`𝓜(x) = ker D_1 ∩ ker D_2` when `D_2` is positive semidefinite),
`|D_3[d]^3| ≤ φ^δ_3 / (δ³/3!)`. This is the book's bound on the projected tensor
`‖P_𝓜[∇³f(x)]‖`, read on the diagonal. -/
theorem abs_apply_three_le_taylorMeasure (hδ : 0 ≤ δ) {d : E} (hd : ‖d‖ ≤ 1)
    (h1 : (D 1 fun _ => d) = 0) (h2 : (D 2 fun _ => d) = 0) :
    δ ^ 3 / 6 * |D 3 fun _ => d| ≤ taylorMeasure D 3 δ Set.univ := by
  have hn : ‖δ • d‖ ≤ δ := by
    rw [norm_smul, Real.norm_of_nonneg hδ]
    nlinarith [norm_nonneg d]
  have hp := le_taylorMeasure_univ D (j := 3) hn
  have hm := le_taylorMeasure_univ D (j := 3) (δ := δ) (d := (-δ) • d)
    (by rw [neg_smul, norm_neg]; exact hn)
  rw [D.taylorDecrement_three, apply_smul_diag_mul, apply_smul_diag_mul, apply_smul_diag_mul, h1,
    h2] at hp hm
  rcases abs_cases (D 3 fun _ => d) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;> nlinarith

end Measure

/-! ### Local minimizers -/

section LocalMin

variable {f : E → ℝ} {x : E} {j : ℕ}

/-- **The measure at a local minimizer, low orders** ([cartis2022evaluation], Theorem 12.1.4,
(12.1.16)): if `f` is `C^j` at a local minimizer `x`, `j ∈ {1, 2}`, then `φ^δ_j(x) = 0` for every
`δ ≥ 0`. -/
theorem taylorMeasure_eq_zero_of_isLocalMin (hf : ContDiffAt ℝ j f x) (hmin : IsLocalMin f x)
    (hj : j ∈ Icc 1 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ f x) j δ Set.univ = 0 := by
  set D := ftaylorSeries ℝ f x
  have hc : IsCurveCritical D j := IsLocalMin.isCurveCritical hf hmin
  have h1 : D 1 = 0 := hc.apply_one_eq_zero (mem_Icc.1 hj).1
  refine le_antisymm (decrementMeasure_le ⟨0, zero_mem_inter hδ (Set.mem_univ _)⟩
    fun d _ => ?_) (taylorMeasure_nonneg D _ (Set.mem_univ _) hδ)
  rcases (by simp at hj; omega : j = 1 ∨ j = 2) with rfl | rfl
  · simp [D.taylorDecrement_one_apply, h1]
  · have h2 := hc.apply_two_nonneg le_rfl d
    rw [D.taylorDecrement_two, h1]
    simp only [zero_apply, neg_zero, zero_sub]
    linarith

/-- **The measure at a local minimizer, quantitative form** ([cartis2022evaluation],
Theorem 12.1.4): if `f` is `C^j` at a local minimizer `x`, then for every `η > 0` there is
`δ₀ > 0` with `φ^δ_j(x) ≤ η δ^j` for all `δ ∈ [0, δ₀]`. -/
theorem exists_taylorMeasure_le_of_isLocalMin (hf : ContDiffAt ℝ j f x) (hmin : IsLocalMin f x)
    {η : ℝ} (hη : 0 < η) : ∃ δ₀ > 0, ∀ δ, 0 ≤ δ → δ ≤ δ₀ →
      taylorMeasure (ftaylorSeries ℝ f x) j δ Set.univ ≤ η * δ ^ j := by
  obtain ⟨r, hr, hP⟩ := exists_norm_sub_taylorPolynomial_le hf hη
  obtain ⟨r', hr', hloc⟩ := Metric.eventually_nhds_iff_ball.1 hmin
  refine ⟨min r r' / 2, by positivity, fun δ hδ hδ₀ => ?_⟩
  refine decrementMeasure_le ⟨0, zero_mem_inter hδ (Set.mem_univ _)⟩ fun d hd => ?_
  have hd' : ‖d‖ ≤ δ := by simpa using hd.1
  have hdr : ‖d‖ < r := by linarith [min_le_left r r', half_lt_self (lt_min hr hr')]
  have hdr' : ‖d‖ < r' := by linarith [min_le_right r r', half_lt_self (lt_min hr hr')]
  have hfx : f x ≤ f (x + d) := hloc _ (by simpa using hdr')
  have hT := hP d hdr
  have hdec : (ftaylorSeries ℝ f x).taylorDecrement j d = f x - taylorPolynomial f j x d := by
    rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
      taylorPolynomial_zero_right]
  rw [hdec]
  have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hT)
  calc f x - taylorPolynomial f j x d ≤ f (x + d) - taylorPolynomial f j x d := by linarith
    _ ≤ η * ‖d‖ ^ j := this
    _ ≤ η * δ ^ j := by gcongr

/-- **The measure at a local minimizer** ([cartis2022evaluation], Theorem 12.1.4, (12.1.17)): if
`f` is `C^j` at a local minimizer `x`, then `φ^δ_j(x)/δ^j → 0` as `δ → 0⁺`. -/
theorem tendsto_taylorMeasure_div_pow_of_isLocalMin (hf : ContDiffAt ℝ j f x)
    (hmin : IsLocalMin f x) :
    Tendsto (fun δ => taylorMeasure (ftaylorSeries ℝ f x) j δ Set.univ / δ ^ j) (𝓝[>] 0)
      (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ₀, hδ₀, h⟩ := exists_taylorMeasure_le_of_isLocalMin hf hmin (half_pos hη)
  refine ⟨δ₀, hδ₀, fun δ hδ hδd => ?_⟩
  have hδ' : 0 < δ := hδ
  have hd : δ < δ₀ := by simpa [abs_of_pos hδ'] using hδd
  have hpow : 0 < δ ^ j := pow_pos hδ' j
  have h1 := h δ hδ'.le hd.le
  have h0 := taylorMeasure_nonneg (ftaylorSeries ℝ f x) j (Set.mem_univ 0) hδ'.le
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 hpow.le),
    div_lt_iff₀ hpow]
  nlinarith

end LocalMin

/-! ### Sufficient conditions (Theorem 12.1.5, corrected) -/

section Sufficient

/-- Growth of order `j` of the Taylor sum `T_j` survives the next term:
`T_{j+1}(s) - T_{j+1}(0) ≥ (c - L ‖s‖/(j+1)!) ‖s‖^j` when `‖D_{j+1}‖ ≤ L` and
`T_j(s) - T_j(0) ≥ c ‖s‖^j` (proof of [cartis2022evaluation], Theorem 12.1.5). -/
theorem sub_taylorSum_succ_ge_of_growth (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ} {c L r : ℝ}
    (hL : ‖D (j + 1)‖ ≤ L)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ D.taylorSum j s - D.taylorSum j 0)
    {s : E} (hs : ‖s‖ ≤ r) :
    (c - L * ‖s‖ / (j + 1)!) * ‖s‖ ^ j ≤ D.taylorSum (j + 1) s - D.taylorSum (j + 1) 0 := by
  have h1 := hgrowth s hs
  have h0 : (D (j + 1) fun _ => (0 : E)) = 0 := (D (j + 1)).map_coord_zero (0 : Fin (j + 1)) rfl
  have h2 : -(L * ‖s‖ ^ (j + 1)) ≤ D (j + 1) fun _ => s := by
    have h := D.norm_apply_diagonal_le (j + 1) s
    rw [Real.norm_eq_abs] at h
    have hb : ‖D (j + 1)‖ * ‖s‖ ^ (j + 1) ≤ L * ‖s‖ ^ (j + 1) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    linarith [(abs_le.1 h).1]
  rw [D.taylorSum_succ, D.taylorSum_succ, h0, smul_zero, add_zero, smul_eq_mul]
  have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
  have : -(L * ‖s‖ / (j + 1)! * ‖s‖ ^ j) ≤ ((j + 1)! : ℝ)⁻¹ * D (j + 1) fun _ => s := by
    rw [pow_succ] at h2
    rw [div_mul_eq_mul_div, ← neg_div, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hf.le)
  nlinarith

/-- Under the hypotheses of `sub_taylorSum_succ_ge_of_growth`, `T_{j+1}(0) < T_{j+1}(s)` for
`0 < ‖s‖ ≤ r` with `L ‖s‖ < c (j+1)!`. -/
theorem taylorSum_succ_zero_lt_of_growth (D : FormalMultilinearSeries ℝ E ℝ)
    {j : ℕ} {c L r : ℝ} (hL : ‖D (j + 1)‖ ≤ L)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ D.taylorSum j s - D.taylorSum j 0)
    {s : E} (hs0 : s ≠ 0) (hs : ‖s‖ ≤ r) (hsL : L * ‖s‖ < c * (j + 1)!) :
    D.taylorSum (j + 1) 0 < D.taylorSum (j + 1) s := by
  have h := sub_taylorSum_succ_ge_of_growth D hL hgrowth hs
  have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
  have hpos : 0 < c - L * ‖s‖ / (j + 1)! := by
    rw [sub_pos, div_lt_iff₀ hf]
    exact hsL
  have : 0 < (c - L * ‖s‖ / (j + 1)!) * ‖s‖ ^ j :=
    mul_pos hpos (pow_pos (norm_pos_iff.2 hs0) j)
  linarith

/-- **Propagation of growth to the next order** (the consequence stated after Theorem 12.1.5 of
[cartis2022evaluation], in corrected form): if `‖D_{j+1}‖ ≤ L` and
`T_j(s) - T_j(0) ≥ c ‖s‖^j` (`c > 0`) for `‖s‖ ≤ r` (`r > 0`), then `T_{j+1}` grows of the same
order with constant `c/2` on a smaller ball. Iterating gives growth of every `T_ℓ`, `ℓ ≥ j`, when
the higher derivatives are bounded. -/
theorem exists_growth_taylorSum_succ_of_growth (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ}
    {c L r : ℝ} (hc : 0 < c) (hr : 0 < r) (hL : ‖D (j + 1)‖ ≤ L)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ D.taylorSum j s - D.taylorSum j 0) :
    ∃ r' > 0, r' ≤ r ∧ ∀ s : E, ‖s‖ ≤ r' →
      c / 2 * ‖s‖ ^ j ≤ D.taylorSum (j + 1) s - D.taylorSum (j + 1) 0 := by
  have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
  set ρ := c * (j + 1)! / (2 * (|L| + 1))
  have hρ : 0 < ρ := by positivity
  refine ⟨min r ρ, lt_min hr hρ, min_le_left _ _, fun s hs => ?_⟩
  have h := sub_taylorSum_succ_ge_of_growth D hL hgrowth (hs.trans (min_le_left _ _))
  have hsρ : ‖s‖ ≤ ρ := hs.trans (min_le_right _ _)
  have hLs : L * ‖s‖ / (j + 1)! ≤ c / 2 := by
    rw [div_le_iff₀ hf]
    have h1 : (|L| + 1) * ‖s‖ ≤ c * (j + 1)! / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have := hsρ
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    nlinarith [le_abs_self L, norm_nonneg s]
  have hpow : 0 ≤ ‖s‖ ^ j := by positivity
  nlinarith

/-- **Sufficient condition for the Taylor model, corrected form of [cartis2022evaluation],
Theorem 12.1.5 (first conclusion).** If `‖D_{j+1}‖ ≤ L` and `T_j` grows like
`T_j(s) - T_j(0) ≥ c ‖s‖^j` (`c > 0`) for `‖s‖ ≤ r` (`r > 0`), then `s = 0` is a strict local
minimizer of `T_{j+1}`.

The book only assumes that `s = 0` is an isolated minimizer of `T_j`; this does not give the
uniform growth that its proof uses, and the statement is then false. For
`f(x) = (x₂ - x₁²)² + x₂⁶ - x₁⁷` on `ℝ²`, `j = 6`, `x = 0`: `T_{f,6}(0, s) = (s₂ - s₁²)² + s₂⁶` has
the isolated minimizer `s = 0`, but `T_{f,7}(0, ·) = f` and `f(t, t²) = t¹² - t⁷ < 0` for
`t ∈ (0, 1)`, so `0` is neither an isolated minimizer of `T_{f,7}(0, ·)` nor a local minimizer of
`f`. -/
theorem isStrictLocalMin_taylorPolynomial_succ_of_growth (D : FormalMultilinearSeries ℝ E ℝ)
    {j : ℕ} {c L r : ℝ} (hc : 0 < c) (hr : 0 < r) (hL : ‖D (j + 1)‖ ≤ L)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ D.taylorSum j s - D.taylorSum j 0) :
    IsStrictLocalMinOn (D.taylorSum (j + 1)) Set.univ 0 := by
  have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
  have hρ : 0 < c * (j + 1)! / (|L| + 1) := by positivity
  refine isStrictLocalMinOn_iff.2 ⟨min r (c * (j + 1)! / (|L| + 1)), lt_min hr hρ,
    fun s _ hs hs0 => ?_⟩
  rw [dist_zero_right] at hs
  refine taylorSum_succ_zero_lt_of_growth D hL hgrowth hs0 (hs.le.trans (min_le_left _ _)) ?_
  have h1 := hs.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at h1
  nlinarith [le_abs_self L, norm_nonneg s]

/-- Quantitative form of `isStrictLocalMin_of_taylorPolynomial_growth`: if `f` is `C^j` at `x`
and `T_{f,j}(x, s) - f(x) ≥ c ‖s‖^j` (`c > 0`) for `‖s‖ ≤ r` (`r > 0`), then
`f(x + s) ≥ f(x) + (c/2) ‖s‖^j` for all small `s`. -/
theorem exists_add_le_of_taylorPolynomial_growth {f : E → ℝ} {x : E} {j : ℕ}
    (hf : ContDiffAt ℝ j f x) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ taylorPolynomial f j x s - f x) :
    ∃ ρ > 0, ∀ s : E, ‖s‖ < ρ → f x + c / 2 * ‖s‖ ^ j ≤ f (x + s) := by
  obtain ⟨r', hr', hP⟩ := exists_norm_sub_taylorPolynomial_le hf (half_pos hc)
  refine ⟨min r r', lt_min hr hr', fun s hs => ?_⟩
  have h1 := hgrowth s (hs.le.trans (min_le_left _ _))
  have h2 := hP s (hs.trans_le (min_le_right _ _))
  rw [Real.norm_eq_abs] at h2
  have := (abs_le.1 h2).1
  linarith

/-- **Sufficient condition for `f`, corrected form of [cartis2022evaluation], Theorem 12.1.5
(second conclusion).** If `f` is `C^j` at `x` and its Taylor polynomial grows like
`T_{f,j}(x, s) - f(x) ≥ c ‖s‖^j` (`c > 0`) for `‖s‖ ≤ r` (`r > 0`), then `x` is a strict local
minimizer of `f`. For `j = 2` the growth condition is `∇f(x) = 0` with `∇²f(x)` coercive. The
book's hypotheses ("`s = 0` is an isolated minimizer of `T_{f,j}(x, ·)`") are not sufficient
(counterexample in `isStrictLocalMin_taylorPolynomial_succ_of_growth`). -/
theorem isStrictLocalMin_of_taylorPolynomial_growth {f : E → ℝ} {x : E} {j : ℕ}
    (hf : ContDiffAt ℝ j f x) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ taylorPolynomial f j x s - f x) :
    IsStrictLocalMinOn f Set.univ x := by
  obtain ⟨ρ, hρ, h⟩ := exists_add_le_of_taylorPolynomial_growth hf hc hr hgrowth
  refine isStrictLocalMinOn_iff.2 ⟨ρ, hρ, fun z _ hz hzx => ?_⟩
  have hs : z - x ≠ 0 := sub_ne_zero.2 hzx
  have := h (z - x) (by rwa [← dist_eq_norm])
  rw [add_sub_cancel] at this
  have : 0 < c / 2 * ‖z - x‖ ^ j := by
    have := norm_pos_iff.2 hs
    positivity
  linarith

end Sufficient

end Optimization
