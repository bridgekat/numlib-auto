import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Gradient.Basic
import Numlib.Analysis.Calculus.MultivariateTaylor.DerivBound
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Gluing separated quadratic jets

The multidimensional construction behind Theorem 3.1.1 of [cartis2022evaluation] ((3.1.7)):
quadratic jets prescribed at points at mutual distance at least `r` are interpolated by a smooth
function whose derivatives of order `≤ 3` are bounded independently of the number of points. The
interpolant is a sum of translated bump functions times the quadratic Taylor polynomials.

## Main definitions and results

* `Optimization.quadJet f g H`: the jet `(f, g, H)` as a formal multilinear series.
* `Optimization.exists_contDiff_interpolating_separated_taylorData`,
  `Optimization.exists_contDiff_interpolating_separated_jets`: the gluing.
-/

open Set

namespace Optimization

/-! ### Gluing separated quadratic jets -/

section SeparatedJets

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gluing with separation `2r`; see `exists_contDiff_interpolating_separated_taylorData`. -/
private theorem exists_contDiff_interpolating_separated_taylorData_aux [FiniteDimensional ℝ E]
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K : ℕ) (x : ℕ → E) (D : ℕ → FormalMultilinearSeries ℝ E ℝ),
      (∀ i ≤ K, ∀ j ≤ K, i ≠ j → 2 * r ≤ ‖x i - x j‖) →
      (∀ k ≤ K, (D k).IsSymm 2) → (∀ k ≤ K, ∀ i ≤ 2, ‖D k i‖ ≤ κ) →
      ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
        (∀ k ≤ K, ∀ j ≤ 2, iteratedFDeriv ℝ j F (x k) = D k j) ∧
        ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
  let φ : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hφc : ContDiff ℝ ∞ φ := φ.contDiff
  -- a uniform bound on the derivatives of `φ`
  obtain ⟨Cφ, hCφ0, hCφ⟩ : ∃ C, 0 ≤ C ∧ ∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j φ z‖ ≤ C := by
    have : ∀ j : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ j φ z‖ ≤ C := fun j =>
      (hφc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
        (φ.hasCompactSupport.iteratedFDeriv j)
    choose C hC using this
    refine ⟨|C 0| + |C 1| + |C 2| + |C 3|, by positivity, fun j hj z => ?_⟩
    have h0 := le_abs_self (C 0)
    have h1 := le_abs_self (C 1)
    have h2 := le_abs_self (C 2)
    have h3 := le_abs_self (C 3)
    have a0 := abs_nonneg (C 0)
    have a1 := abs_nonneg (C 1)
    have a2 := abs_nonneg (C 2)
    have a3 := abs_nonneg (C 3)
    interval_cases j
    · linarith [hC 0 z]
    · linarith [hC 1 z]
    · linarith [hC 2 z]
    · linarith [hC 3 z]
  have hφ0 : ∀ z : E, r / 2 ≤ ‖z‖ → φ z = 0 := fun z hz => by
    have : z ∉ Function.support φ := by
      rw [φ.support_eq, Metric.mem_ball, dist_zero_right, not_lt]; exact hz
    simpa using this
  have hφD0 : ∀ j z, r / 2 < ‖z‖ → iteratedFDeriv ℝ j φ z = 0 := fun j z hz => by
    have : z ∉ tsupport φ := by
      rw [φ.tsupport_eq, Metric.mem_closedBall, dist_zero_right, not_le]; exact hz
    exact Function.notMem_support.1 fun h => this (support_iteratedFDeriv_subset j h)
  set Q := 3 * κ * (1 + r / 2) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨8 * Cφ * Q, by positivity, fun K x D hsep hsymm hD => ?_⟩
  set term : ℕ → E → ℝ := fun k y => φ (y - x k) * (D k).taylorSum 2 (y - x k) with hterm
  have hterm_c : ∀ k, ContDiff ℝ ∞ (term k) := fun k =>
    (hφc.comp (contDiff_id.sub contDiff_const)).mul
      (((D k).contDiff_taylorSum 2).comp (contDiff_id.sub contDiff_const))
  set F : E → ℝ := fun y => ∑ k ∈ Finset.range (K + 1), term k y with hF
  have hFc : ContDiff ℝ ∞ F := ContDiff.sum fun k _ => hterm_c k
  -- locality
  have hloc : ∀ y, ∀ k ≤ K, (∀ l ≤ K, l ≠ k → r ≤ ‖y - x l‖) → F =ᶠ[nhds y] term k := by
    intro y k hk hl
    filter_upwards [Metric.ball_mem_nhds y (by positivity : 0 < r / 2)] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    refine Finset.sum_eq_single_of_mem k (Finset.mem_range.2 (by omega)) fun l hl' hlk => ?_
    have hlK : l ≤ K := by have := Finset.mem_range.1 hl'; omega
    have : r / 2 ≤ ‖z - x l‖ := by
      have h1 := hl l hlK hlk
      have h2 : ‖y - x l‖ ≤ ‖z - x l‖ + ‖z - y‖ := by
        calc ‖y - x l‖ = ‖(z - x l) - (z - y)‖ := by congr 1; abel
          _ ≤ ‖z - x l‖ + ‖z - y‖ := norm_sub_le _ _
      linarith
    simp only [hterm, hφ0 _ this, zero_mul]
  have hzero : ∀ y, (∀ l ≤ K, r ≤ ‖y - x l‖) → F =ᶠ[nhds y] fun _ => 0 := by
    intro y hl
    filter_upwards [Metric.ball_mem_nhds y (by positivity : 0 < r / 2)] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    refine Finset.sum_eq_zero fun l hl' => ?_
    have hlK : l ≤ K := by have := Finset.mem_range.1 hl'; omega
    have : r / 2 ≤ ‖z - x l‖ := by
      have h1 := hl l hlK
      have h2 : ‖y - x l‖ ≤ ‖z - x l‖ + ‖z - y‖ := by
        calc ‖y - x l‖ = ‖(z - x l) - (z - y)‖ := by congr 1; abel
          _ ≤ ‖z - x l‖ + ‖z - y‖ := norm_sub_le _ _
      linarith
    simp only [hterm, hφ0 _ this, zero_mul]
  -- the dichotomy: at most one node within distance `r`
  have hdich : ∀ y, (∃ k ≤ K, ∀ l ≤ K, l ≠ k → r ≤ ‖y - x l‖) ∨ ∀ l ≤ K, r ≤ ‖y - x l‖ := by
    intro y
    by_cases h : ∃ k ≤ K, ‖y - x k‖ < r
    · obtain ⟨k, hk, hyk⟩ := h
      refine Or.inl ⟨k, hk, fun l hl hlk => ?_⟩
      by_contra hcon
      have := hsep l hl k hk hlk
      have h2 : ‖x l - x k‖ ≤ ‖y - x l‖ + ‖y - x k‖ := by
        calc ‖x l - x k‖ = ‖(y - x k) - (y - x l)‖ := by congr 1; abel
          _ ≤ ‖y - x k‖ + ‖y - x l‖ := norm_sub_le _ _
          _ = ‖y - x l‖ + ‖y - x k‖ := add_comm _ _
      linarith
    · push Not at h
      exact Or.inr h
  -- bound on the derivatives of one term
  have hbound : ∀ k ≤ K, ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j (term k) y‖ ≤ 8 * Cφ * Q := by
    intro k hk j hj y
    have hf1 : ContDiff ℝ ∞ (fun y => φ (y - x k)) :=
      hφc.comp (contDiff_id.sub (contDiff_const (c := x k)))
    have hf2 : ContDiff ℝ ∞ (fun y => (D k).taylorSum 2 (y - x k)) :=
      ((D k).contDiff_taylorSum 2).comp (contDiff_id.sub (contDiff_const (c := x k)))
    have hmul := norm_iteratedFDeriv_mul_le hf1 hf2 y (n := j) (by exact_mod_cast le_top)
    refine hmul.trans ?_
    have hsummand : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => φ (y - x k)) y‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => (D k).taylorSum 2 (y - x k)) y‖ ≤
        (j.choose i : ℝ) * (Cφ * Q) := by
      intro i hi
      have hi3 : i ≤ 3 := by have := Finset.mem_range.1 hi; omega
      rw [iteratedFDeriv_comp_sub, iteratedFDeriv_comp_sub, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rcases le_or_gt ‖y - x k‖ (r / 2) with hy | hy
      · exact mul_le_mul (hCφ i hi3 _)
          ((D k).norm_iteratedFDeriv_taylorSum_two_le hκ (by positivity) (hD k hk) _ hy)
          (norm_nonneg _) hCφ0
      · rw [hφD0 i _ hy, norm_zero, zero_mul]
        positivity
    refine (Finset.sum_le_sum hsummand).trans ?_
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    have : ((2 ^ j : ℕ) : ℝ) ≤ 8 := by
      have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj
      exact_mod_cast this
    nlinarith [mul_nonneg hCφ0 hQ0]
  refine ⟨F, hFc, fun k hk j hj => ?_, fun j hj y => ?_⟩
  · -- interpolation at the nodes
    have h1 : F =ᶠ[nhds (x k)] term k := hloc (x k) k hk fun l hl hlk => by
      have := hsep k hk l hl (Ne.symm hlk)
      linarith
    have h2 : term k =ᶠ[nhds (x k)] fun y => (D k).taylorSum 2 (y - x k) := by
      filter_upwards [Metric.closedBall_mem_nhds (x k) (by positivity : 0 < r / 4)] with z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have : φ (z - x k) = 1 :=
        φ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
      simp only [hterm, this, one_mul]
    rw [((h1.trans h2).iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_comp_sub, sub_self,
      FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero (hsymm k hk) hj]
  · rcases hdich y with ⟨k, hk, hl⟩ | hl
    · rw [((hloc y k hk hl).iteratedFDeriv ℝ j).eq_of_nhds]
      exact hbound k hk j hj y
    · rw [((hzero y hl).iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply,
        norm_zero]
      positivity

/-- **Gluing separated quadratic jets** (Taylor-data form). Let `E` be a finite-dimensional real
inner product space, `r > 0` and `κ ≥ 0`. There is `B ≥ 0` (depending only on `E`, `r` and `κ`)
such that for any points `x_0, …, x_K` with `‖x_i - x_j‖ ≥ r` (`i ≠ j`) and symmetric Taylor data
`D_k` with `‖D_{k,i}‖ ≤ κ` (`i ≤ 2`), there is a smooth `F : E → ℝ` whose derivatives of order
`j ≤ 2` at `x_k` are `D_{k,j}` and whose derivatives of order `j ≤ 3` are bounded by `B`.

The function is `F(y) = ∑_k φ(y - x_k) T_{D_k,2}(y - x_k)` with a fixed bump `φ` equal to `1` on
the ball of radius `r/8` and supported in the ball of radius `r/4`: near every point at most one
term is nonzero. -/
theorem exists_contDiff_interpolating_separated_taylorData [FiniteDimensional ℝ E] {r κ : ℝ}
    (hr : 0 < r) (hκ : 0 ≤ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K : ℕ) (x : ℕ → E) (D : ℕ → FormalMultilinearSeries ℝ E ℝ),
      (∀ i ≤ K, ∀ j ≤ K, i ≠ j → r ≤ ‖x i - x j‖) →
      (∀ k ≤ K, (D k).IsSymm 2) → (∀ k ≤ K, ∀ i ≤ 2, ‖D k i‖ ≤ κ) →
      ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
        (∀ k ≤ K, ∀ j ≤ 2, iteratedFDeriv ℝ j F (x k) = D k j) ∧
        ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
  obtain ⟨B, hB, hmain⟩ :=
    exists_contDiff_interpolating_separated_taylorData_aux (E := E) (by positivity : 0 < r / 2) hκ
  exact ⟨B, hB, fun K x D hsep => hmain K x D fun i hi j hj hij => by
    linarith [hsep i hi j hj hij]⟩

/-- The quadratic jet `(f, g, H)` (value, gradient, Hessian) as Taylor data:
`D_0 = f`, `D_1 = ⟪g, ·⟫`, `D_2 = H`, `D_i = 0` for `i ≥ 3`. -/
noncomputable def quadJet (f : ℝ) (g : E) (H : E [×2]→L[ℝ] ℝ) : FormalMultilinearSeries ℝ E ℝ
  | 0 => ContinuousMultilinearMap.uncurry0 ℝ E f
  | 1 => (continuousMultilinearCurryFin1 ℝ E ℝ).symm (innerSL ℝ g)
  | 2 => H
  | _ + 3 => 0

theorem quadJet_isSymm {f : ℝ} {g : E} {H : E [×2]→L[ℝ] ℝ}
    (hH : ∀ v w, H ![v, w] = H ![w, v]) : (quadJet f g H).IsSymm 2 := by
  intro i hi σ v
  interval_cases i
  · exact congrArg _ (Subsingleton.elim _ _)
  · have : σ = 1 := Subsingleton.elim _ _
    subst this
    rfl
  · refine ContinuousMultilinearMap.apply_comp_perm_of_swap H (fun a b hab w => ?_) σ v
    have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    have hab' : Equiv.swap a b = Equiv.swap 0 1 := by
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · rfl
      · exact Equiv.swap_comm _ _
      · exact absurd rfl hab
    have hs : w ∘ Equiv.swap a b = ![w 1, w 0] := by
      rw [hab']; ext i; fin_cases i <;> simp
    change H (w ∘ Equiv.swap a b) = H w
    rw [hs, hw, hH]
    rfl

theorem norm_quadJet_le {f κ : ℝ} {g : E} {H : E [×2]→L[ℝ] ℝ} (hf : |f| ≤ κ) (hg : ‖g‖ ≤ κ)
    (hH : ‖H‖ ≤ κ) : ∀ i ≤ 2, ‖quadJet f g H i‖ ≤ κ := by
  intro i hi
  interval_cases i
  · simpa [quadJet, ContinuousMultilinearMap.uncurry0_norm] using hf
  · simpa [quadJet, innerSL_apply_norm] using hg
  · exact hH

/-- **Gluing separated quadratic jets** ([cartis2022evaluation], proof of Theorem 3.1.1, (3.1.7),
with a smooth bump in place of the book's piecewise-polynomial one). Let `E` be a
finite-dimensional real inner product space, `r > 0` and `κ ≥ 0`. There is `B ≥ 0` (depending
only on `E`, `r` and `κ`, not on the number of points) such that for any points
`x_0, …, x_K` with `‖x_i - x_j‖ ≥ r` (`i ≠ j`) and jets `(f_k, g_k, H_k)` with `H_k` symmetric
and `|f_k|, ‖g_k‖, ‖H_k‖ ≤ κ`, there is a smooth `F : E → ℝ` with `F(x_k) = f_k`,
`∇F(x_k) = g_k`, `∇²F(x_k) = H_k`, `|F| ≤ B` and `‖∇^j F‖ ≤ B` for `j ≤ 3`. -/
theorem exists_contDiff_interpolating_separated_jets [FiniteDimensional ℝ E] {r κ : ℝ}
    (hr : 0 < r) (hκ : 0 ≤ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K : ℕ) (x : ℕ → E) (f : ℕ → ℝ) (g : ℕ → E) (H : ℕ → E [×2]→L[ℝ] ℝ),
      (∀ i ≤ K, ∀ j ≤ K, i ≠ j → r ≤ ‖x i - x j‖) →
      (∀ k ≤ K, ∀ v w, H k ![v, w] = H k ![w, v]) →
      (∀ k ≤ K, |f k| ≤ κ ∧ ‖g k‖ ≤ κ ∧ ‖H k‖ ≤ κ) →
      ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
        (∀ k ≤ K, F (x k) = f k ∧ gradient F (x k) = g k ∧ iteratedFDeriv ℝ 2 F (x k) = H k) ∧
        ∀ y, |F y| ≤ B ∧ ∀ j ≤ 3, ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
  obtain ⟨B, hB, hmain⟩ := exists_contDiff_interpolating_separated_taylorData (E := E) hr hκ
  refine ⟨B, hB, fun K x f g H hsep hH hbd => ?_⟩
  obtain ⟨F, hF, hjet, hFB⟩ := hmain K x (fun k => quadJet (f k) (g k) (H k)) hsep
    (fun k hk => quadJet_isSymm (hH k hk))
    (fun k hk => norm_quadJet_le (hbd k hk).1 (hbd k hk).2.1 (hbd k hk).2.2)
  refine ⟨F, hF, fun k hk => ⟨?_, ?_, hjet k hk 2 le_rfl⟩, fun y => ⟨?_, fun j hj => hFB j hj y⟩⟩
  · have := congrArg (fun A => A (fun _ => 0)) (hjet k hk 0 (Nat.zero_le _))
    simpa [quadJet, iteratedFDeriv_zero_apply] using this
  · have h1 : fderiv ℝ F (x k) = InnerProductSpace.toDual ℝ E (g k) := by
      ext v
      have := congrArg (fun A => A (fun _ => v)) (hjet k hk 1 (by norm_num))
      simpa [quadJet, iteratedFDeriv_one_apply, InnerProductSpace.toDual_apply_apply] using this
    rw [gradient, h1, LinearIsometryEquiv.symm_apply_apply]
  · have := hFB 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

end SeparatedJets

end Optimization
