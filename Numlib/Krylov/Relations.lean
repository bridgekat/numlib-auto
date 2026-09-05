import Numlib.Krylov.Iterate

/-!
# Relations between Galerkin and minimal-residual iterates

Residual smoothing (Weiss[^weiss]; Saad, *Iterative Methods*[^saad-iterative] Lemma 6.18) and the
Cullum–Greenbaum[^cullum-greenbaum] / Brown[^brown] relations between FOM and GMRES residuals
(Saad Prop 6.12–6.17, (6.65), Cor 6.14; Fong–Saunders[^fong-saunders] (4.1);
Greenbaum[^greenbaum] Lemma 5.4.1), proved at the specification level without any factorization.

Throughout, `r^F_m` denotes the residual `b - A x` of the Galerkin (FOM) iterate over `x₀ + 𝒦_m`
and `r^G_m` that of the minimal-residual (GMRES) iterate over the same affine space.

## References

[^weiss]: Rüdiger Weiss, *Convergence behavior of generalized conjugate gradient methods*,
  PhD thesis, University of Karlsruhe, 1990.
[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^cullum-greenbaum]: Jane Cullum and Anne Greenbaum, *Relations between Galerkin and
  norm-minimizing iterative methods for solving linear systems*, SIAM Journal on Matrix Analysis
  and Applications 17 (1996), 223–247.
[^brown]: Peter N. Brown, *A theoretical comparison of the Arnoldi and GMRES algorithms*, SIAM
  Journal on Scientific and Statistical Computing 12 (1991), 58–78.
[^fong-saunders]: David Chin-Lung Fong and Michael Saunders, *CG versus MINRES: an empirical
  comparison*, SQU Journal for Science 17 (2012), 44–62.
[^greenbaum]: Anne Greenbaum, *Iterative Methods for Solving Linear Systems*, 1997.
-/

open Krylov Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E}

namespace Krylov

/-- Weiss's residual smoothing step: `r' = s + η (r - s)` with the residual-minimizing `η`. -/
noncomputable def smoothingCoeff (s r : E) : 𝕜 := inner 𝕜 (r - s) (-s) / (‖r - s‖ ^ 2 : ℝ)

section Smoothing

variable {s r : E}

/-- For orthogonal `s`, `r` the smoothing coefficient is the real number
`‖s‖² / (‖r‖² + ‖s‖²)`. -/
theorem smoothingCoeff_eq (horth : inner 𝕜 r s = 0) :
    (smoothingCoeff s r : 𝕜) = ((‖s‖ ^ 2 / (‖r‖ ^ 2 + ‖s‖ ^ 2) : ℝ) : 𝕜) := by
  have hnum : inner 𝕜 (r - s) (-s) = ((‖s‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_neg_right, inner_sub_left, horth, inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  have hden : ‖r - s‖ ^ 2 = ‖r‖ ^ 2 + ‖s‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), horth]
    simp
  rw [smoothingCoeff, hnum, hden, ← RCLike.ofReal_div]

/-- The smoothed vector `s + η (r - s)` in barycentric form. -/
theorem smoothing_eq (horth : inner 𝕜 r s = 0) :
    s + (smoothingCoeff s r : 𝕜) • (r - s)
      = ((1 - ‖s‖ ^ 2 / (‖r‖ ^ 2 + ‖s‖ ^ 2) : ℝ) : 𝕜) • s +
        ((‖s‖ ^ 2 / (‖r‖ ^ 2 + ‖s‖ ^ 2) : ℝ) : 𝕜) • r := by
  rw [smoothingCoeff_eq horth]
  push_cast
  module

/-- The squared norm of the smoothed vector. -/
private theorem norm_smoothing_sq (hs : s ≠ 0) (hr : r ≠ 0) (horth : inner 𝕜 r s = 0) :
    ‖s + (smoothingCoeff s r : 𝕜) • (r - s)‖ ^ 2
      = ‖s‖ ^ 2 * ‖r‖ ^ 2 / (‖r‖ ^ 2 + ‖s‖ ^ 2) := by
  have ha : (0 : ℝ) < ‖s‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < ‖r‖ ^ 2 := by positivity
  have hsr : inner 𝕜 s r = (0 : 𝕜) := inner_eq_zero_symm.1 horth
  set t : ℝ := ‖s‖ ^ 2 / (‖r‖ ^ 2 + ‖s‖ ^ 2) with htdef
  have h0 : inner 𝕜 (((1 - t : ℝ) : 𝕜) • s) (((t : ℝ) : 𝕜) • r) = (0 : 𝕜) := by
    rw [inner_smul_left, inner_smul_right, hsr, mul_zero, mul_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (((1 - t : ℝ) : 𝕜) • s) (((t : ℝ) : 𝕜) • r) h0
  rw [← smoothing_eq horth, norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal] at hpy
  have e1 : |1 - t| * ‖s‖ * (|1 - t| * ‖s‖) = (1 - t) ^ 2 * ‖s‖ ^ 2 := by
    rw [show |1 - t| * ‖s‖ * (|1 - t| * ‖s‖) = |1 - t| ^ 2 * ‖s‖ ^ 2 by ring, sq_abs]
  have e2 : |t| * ‖r‖ * (|t| * ‖r‖) = t ^ 2 * ‖r‖ ^ 2 := by
    rw [show |t| * ‖r‖ * (|t| * ‖r‖) = |t| ^ 2 * ‖r‖ ^ 2 by ring, sq_abs]
  rw [e1, e2] at hpy
  rw [pow_two, hpy, htdef]
  field_simp
  ring

/-- Saad, *Iterative Methods*, Lemma 6.18 (Weiss's smoothing lemma): if `r ⟂ s'` where
`s' = s + η (r - s)` is the residual-minimizing combination and `r ⟂ s`, then
`1/‖s'‖² = 1/‖s‖² + 1/‖r‖²`. -/
theorem inv_sq_norm_smoothing {s r : E} (hs : s ≠ 0) (hr : r ≠ 0)
    (horth : inner 𝕜 r s = 0) :
    let s' := s + (smoothingCoeff s r : 𝕜) • (r - s)
    1 / ‖s'‖ ^ 2 = 1 / ‖s‖ ^ 2 + 1 / ‖r‖ ^ 2 := by
  intro s'
  have ha : (0 : ℝ) < ‖s‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < ‖r‖ ^ 2 := by positivity
  have hn : ‖s'‖ ^ 2 = ‖s‖ ^ 2 * ‖r‖ ^ 2 / (‖r‖ ^ 2 + ‖s‖ ^ 2) := norm_smoothing_sq hs hr horth
  rw [hn]
  field_simp

end Smoothing

section Decomposition

variable {m : ℕ} {xG xF : E}

/-- `𝒦_{m+1} = 𝒦_m + 𝕜 A^m v`. -/
theorem subspace_succ_eq_sup (A : E →ₗ[𝕜] E) (v : E) (m : ℕ) :
    subspace A v (m + 1) = subspace A v m ⊔ 𝕜 ∙ ((A ^ m) v) := by
  refine le_antisymm ?_ (sup_le (subspace_mono A v (Nat.le_succ m))
    ((Submodule.span_singleton_le_iff_mem _ _).2 (pow_apply_mem_subspace A v (Nat.lt_succ_self m))))
  rw [subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  dsimp only
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.2) with h | h
  · exact Submodule.mem_sup_left (pow_apply_mem_subspace A v h)
  · rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- The Galerkin residual at step `m + 1` is orthogonal to the minimal-residual residual at
step `m`. -/
private theorem inner_residual_minRes_galerkin (hG : IsMinResIterate A b x₀ m xG)
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) : inner 𝕜 (b - A xG) (b - A xF) = 0 :=
  IsPetrovGalerkin.inner_residual_eq_zero hF (residual_mem_subspace_succ hG.mem)

/-- The residual of the smoothing step. -/
theorem residual_smoothing_step (η : 𝕜) (xG xF : E) :
    b - A (xG + η • (xF - xG)) = (b - A xG) + η • ((b - A xF) - (b - A xG)) := by
  simp only [map_add, map_smul, map_sub]
  module

/-- `A 𝒦_{m+1} = A 𝒦_m ⊔ 𝕜 (r^F_{m+1} - r^G_m)`, the key decomposition behind the
residual-smoothing proof of the Cullum–Greenbaum relation. Only `r^G_m ≠ 0` is needed. -/
private theorem map_subspace_succ_eq_sup_span' (hG : IsMinResIterate A b x₀ m xG)
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hG0 : b - A xG ≠ 0) :
    (subspace A (b - A x₀) (m + 1)).map A =
      (subspace A (b - A x₀) m).map A ⊔ 𝕜 ∙ ((b - A xF) - (b - A xG)) := by
  have hdmem : xG - xF ∈ subspace A (b - A x₀) (m + 1) := by
    have h : xG - xF = (xG - x₀) - (xF - x₀) := by abel
    rw [h]
    exact Submodule.sub_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ m) hG.mem) hF.mem
  rw [subspace_succ_eq_sup] at hdmem
  obtain ⟨u, hu, w, hw, hduw⟩ := Submodule.mem_sup.1 hdmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hrs : (b - A xF) - (b - A xG) = A u + c • A ((A ^ m) (b - A x₀)) := by
    have h : (b - A xF) - (b - A xG) = A (xG - xF) := by rw [map_sub]; abel
    rw [h, ← hduw, map_add, map_smul]
  have hc0 : c ≠ 0 := by
    intro hc
    have h1 : inner 𝕜 ((b - A xF) - (b - A xG)) (b - A xG) = (0 : 𝕜) := by
      rw [hrs, hc, zero_smul, add_zero]
      exact (Submodule.mem_orthogonal _ _).1 hG.residual_mem_orthogonal (A u)
        (Submodule.mem_map_of_mem hu)
    rw [inner_sub_left, inner_eq_zero_symm.1 (inner_residual_minRes_galerkin hG hF), zero_sub,
      neg_eq_zero, inner_self_eq_zero] at h1
    exact hG0 h1
  have hApow : A ((A ^ m) (b - A x₀))
      = c⁻¹ • (((b - A xF) - (b - A xG)) - A u) := by
    rw [hrs]
    rw [show A u + c • A ((A ^ m) (b - A x₀)) - A u = c • A ((A ^ m) (b - A x₀)) by abel,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [subspace_succ_eq_sup, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hApow]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem hu)))
  · rw [Submodule.span_singleton_le_iff_mem, hrs]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hu))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

set_option linter.unusedVariables false in
/-- The step from `A 𝒦_m` to `A 𝒦_{m+1}` is spanned by `r^F_{m+1} - r^G_m` (the Galerkin residual
at `m + 1` minus the minimal-residual residual at `m`), the key step of the residual-smoothing
proof of the Cullum–Greenbaum relation: `A 𝒦_{m+1} = A 𝒦_m ⊔ 𝕜 ∙ (r^F_{m+1} - r^G_m)`. -/
theorem map_subspace_succ_eq_sup_span {m : ℕ} {xG xF : E} (hG : IsMinResIterate A b x₀ m xG)
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hF0 : b - A xF ≠ 0)
    (hinj : Function.Injective A) [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m + 1 ≤ grade A (b - A x₀)) :
    (subspace A (b - A x₀) (m + 1)).map A =
      (subspace A (b - A x₀) m).map A ⊔ 𝕜 ∙ ((b - A xF) - (b - A xG)) := by
  refine map_subspace_succ_eq_sup_span' hG hF fun hG0 => ?_
  have hAx : A xG = b := (sub_eq_zero.1 hG0).symm
  exact absurd (grade_le_of_apply_eq hG.mem hAx) (by omega)

/-- One residual-smoothing step turns the minimal-residual iterate at `m` and the Galerkin
iterate at `m + 1` into the minimal-residual iterate at `m + 1`. -/
private theorem smoothing_isMinResIterate (hG : IsMinResIterate A b x₀ m xG)
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hG0 : b - A xG ≠ 0) :
    IsMinResIterate A b x₀ (m + 1)
      (xG + (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) • (xF - xG)) := by
  have horth : inner 𝕜 (b - A xF) (b - A xG) = 0 :=
    inner_eq_zero_symm.1 (inner_residual_minRes_galerkin hG hF)
  have hne : (b - A xF) - (b - A xG) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, inner_self_eq_zero] at horth
    exact hG0 horth
  refine IsMinRes.iff_isPetrovGalerkin.2 ⟨?_, ?_⟩
  · have h : xG + (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) • (xF - xG) - x₀
        = (xG - x₀) + (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) • ((xF - x₀) - (xG - x₀)) := by
      module
    rw [h]
    exact Submodule.add_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ m) hG.mem)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ hF.mem
        (subspace_mono A (b - A x₀) (Nat.le_succ m) hG.mem)))
  · rw [residual_smoothing_step, map_subspace_succ_eq_sup_span' hG hF hG0]
    have hD : ((‖(b - A xF) - (b - A xG)‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
      simpa using pow_ne_zero 2 (norm_ne_zero_iff.2 hne)
    have h2 : inner 𝕜 ((b - A xF) - (b - A xG))
        ((b - A xG) + (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) •
          ((b - A xF) - (b - A xG))) = 0 := by
      rw [inner_add_right, inner_smul_right, smoothingCoeff, inner_self_eq_norm_sq_to_K,
        ← RCLike.ofReal_pow, div_mul_cancel₀ _ hD, inner_neg_right]
      ring
    refine (Submodule.mem_orthogonal _ _).2 fun z hz => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
    have hus : inner 𝕜 u (b - A xG) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal _ _).1 hG.residual_mem_orthogonal u hu
    have huF : inner 𝕜 u (b - A xF) = (0 : 𝕜) :=
      IsPetrovGalerkin.inner_residual_eq_zero hF (map_subspace_le A (b - A x₀) m hu)
    have hdiff : inner 𝕜 u ((b - A xF) - (b - A xG)) = (0 : 𝕜) := by
      rw [inner_sub_right, hus, huF, sub_zero]
    have h1 : inner 𝕜 u ((b - A xG) + (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) •
        ((b - A xF) - (b - A xG))) = 0 := by
      rw [inner_add_right, inner_smul_right, hus, hdiff, mul_zero, add_zero]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [inner_add_left, h1, inner_smul_left, h2, mul_zero, add_zero]

end Decomposition

section Relations

variable {m : ℕ} {xG xG' xF : E}

/-- Cullum–Greenbaum (Saad, *Iterative Methods*, (6.65)):
`1/‖r_{m+1}^G‖² = 1/‖r_m^G‖² + 1/‖r_{m+1}^F‖²`. -/
theorem inv_sq_norm_residual_minRes {m : ℕ} {xG xG' xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (h0 : b - A xG' ≠ 0) :
    1 / ‖b - A xG'‖ ^ 2 = 1 / ‖b - A xG‖ ^ 2 + 1 / ‖b - A xF‖ ^ 2 := by
  have hG0 : b - A xG ≠ 0 := by
    intro h
    have hle := hG.norm_residual_le hG' (subspace_mono A (b - A x₀) (Nat.le_succ m))
    rw [h, norm_zero] at hle
    exact h0 (norm_le_zero_iff.1 hle)
  have hF0 : b - A xF ≠ 0 := by
    intro h
    have hax := hG'.apply_eq_of_exists hF.mem (sub_eq_zero.1 h).symm
    exact h0 (by rw [hax, sub_self])
  have horth : inner 𝕜 (b - A xF) (b - A xG) = 0 :=
    inner_eq_zero_symm.1 (inner_residual_minRes_galerkin hG hF)
  have heq : b - A xG' = (b - A xG) +
      (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) • ((b - A xF) - (b - A xG)) := by
    rw [← residual_smoothing_step]
    exact hG'.residual_unique (smoothing_isMinResIterate hG hF hG0)
  rw [heq]
  exact inv_sq_norm_smoothing hG0 hF0 horth

/-- `‖r_m^G‖ ≤ ‖r_m^F‖`. -/
theorem norm_residual_minRes_le_galerkin {m : ℕ} {xG xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : IsGalerkinIterate A b x₀ m xF) :
    ‖b - A xG‖ ≤ ‖b - A xF‖ :=
  hG.min xF hF.mem

/-- Saad, *Iterative Methods*, Cor 6.14: `1/‖r_m^G‖² = ∑_{i ≤ m} 1/‖r_i^F‖²` when all Galerkin
iterates exist. -/
theorem inv_sq_norm_residual_minRes_eq_sum {m : ℕ} {xG : E} {xF : ℕ → E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xF i))
    (h0 : b - A xG ≠ 0) :
    1 / ‖b - A xG‖ ^ 2 = ∑ i ∈ Finset.range (m + 1), 1 / ‖b - A (xF i)‖ ^ 2 := by
  suffices H : ∀ k (y : E), IsMinResIterate A b x₀ k y → b - A y ≠ 0 →
      (∀ i ≤ k, IsGalerkinIterate A b x₀ i (xF i)) →
      1 / ‖b - A y‖ ^ 2 = ∑ i ∈ Finset.range (k + 1), 1 / ‖b - A (xF i)‖ ^ 2 from
    H m xG hG h0 hF
  intro k
  induction k with
  | zero =>
    intro y hy _ hF0
    have hy0 : y = x₀ := by
      have h := hy.mem
      rw [subspace_zero] at h
      exact sub_eq_zero.1 (by simpa using h)
    have hF00 : xF 0 = x₀ := by
      have h := (hF0 0 le_rfl).mem
      rw [subspace_zero] at h
      exact sub_eq_zero.1 (by simpa using h)
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [hy0, hF00]
  | succ n ih =>
    intro y hy hy0 hFk
    obtain ⟨z, hz⟩ := exists_isMinResIterate A b x₀ n
    have hz0 : b - A z ≠ 0 := by
      intro h
      have hle := hz.norm_residual_le hy (subspace_mono A (b - A x₀) (Nat.le_succ n))
      rw [h, norm_zero] at hle
      exact hy0 (norm_le_zero_iff.1 hle)
    rw [Finset.sum_range_succ, ← ih z hz hz0 fun i hi => hFk i (hi.trans (Nat.le_succ n))]
    exact inv_sq_norm_residual_minRes hz hy (hFk (n + 1) le_rfl) hy0

/-- If the minimal-residual iterate at step `m` is exact then so is the Galerkin iterate. -/
private theorem galerkin_residual_eq_zero_of_minRes (hG : IsMinResIterate A b x₀ m xG)
    (hG0 : b - A xG = 0) (hF : IsGalerkinIterate A b x₀ m xF) : b - A xF = 0 := by
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hG.mem
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hp0
    simp at hp0
  have hann : aeval A p (b - A x₀) = 0 := by rw [← hres, hG0]
  -- the annihilator makes `𝒦_m` invariant
  have hmem : ∀ k, p.natDegree ≤ k → (A ^ k) (b - A x₀) ∈ subspace A (b - A x₀) k := by
    intro k hk
    induction k with
    | zero =>
      have hd : p.natDegree = 0 := Nat.le_zero.1 hk
      refine (pow_apply_mem_subspace_iff_exists_monic A (b - A x₀) 0).2
        ⟨C p.leadingCoeff⁻¹ * p, ?_, ?_, ?_⟩
      · have hlc : (C p.leadingCoeff⁻¹ * p).leadingCoeff = 1 := by
          rw [leadingCoeff_mul, leadingCoeff_C,
            inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hpne)]
        exact hlc
      · rw [natDegree_mul (by simpa using inv_ne_zero (leadingCoeff_ne_zero.2 hpne)) hpne,
          natDegree_C, zero_add, hd]
      · rw [map_mul, Module.End.mul_apply, hann, map_zero]
    | succ j ihj =>
      rcases Nat.lt_or_ge j p.natDegree with hj | hj
      · have hjd : p.natDegree = j + 1 := by omega
        refine (pow_apply_mem_subspace_iff_exists_monic A (b - A x₀) (j + 1)).2
          ⟨C p.leadingCoeff⁻¹ * p, ?_, ?_, ?_⟩
        · have hlc : (C p.leadingCoeff⁻¹ * p).leadingCoeff = 1 := by
            rw [leadingCoeff_mul, leadingCoeff_C,
              inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hpne)]
          exact hlc
        · rw [natDegree_mul (by simpa using inv_ne_zero (leadingCoeff_ne_zero.2 hpne)) hpne,
            natDegree_C, zero_add, hjd]
        · rw [map_mul, Module.End.mul_apply, hann, map_zero]
      · have hstab : subspace A (b - A x₀) (j + 1) = subspace A (b - A x₀) j :=
          (subspace_succ_eq_iff A (b - A x₀) j).2 (ihj hj)
        have hinvt := mem_invtSubmodule_of_subspace_succ_eq A (b - A x₀) hstab
        rw [hstab, pow_succ']
        exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hinvt _ (ihj hj)
  have hAm : (A ^ m) (b - A x₀) ∈ subspace A (b - A x₀) m :=
    hmem m (natDegree_le_iff_degree_le.2 hp)
  have hinvt := mem_invtSubmodule_of_subspace_succ_eq A (b - A x₀)
    ((subspace_succ_eq_iff A (b - A x₀) m).2 hAm)
  have hAxG : A xG = b := (sub_eq_zero.1 hG0).symm
  have hFmem : b - A xF ∈ subspace A (b - A x₀) m := by
    have h : b - A xF = A (xG - xF) := by rw [map_sub, hAxG]
    rw [h]
    refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hinvt _ ?_
    have h2 : xG - xF = (xG - x₀) - (xF - x₀) := by abel
    rw [h2]
    exact Submodule.sub_mem _ hG.mem hF.mem
  exact inner_self_eq_zero.1
    (IsPetrovGalerkin.inner_residual_eq_zero hF hFmem)

/-- Saad, *Iterative Methods*, Prop 6.15: `min_{i ≤ m} ‖r_i^F‖ ≤ √(m+1) ‖r_m^G‖`. -/
theorem exists_norm_residual_galerkin_le {m : ℕ} {xG : E} {xF : ℕ → E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xF i)) :
    ∃ i ≤ m, ‖b - A (xF i)‖ ≤ Real.sqrt (m + 1) * ‖b - A xG‖ := by
  rcases eq_or_ne (b - A xG) 0 with h0 | h0
  · refine ⟨m, le_rfl, ?_⟩
    rw [galerkin_residual_eq_zero_of_minRes hG h0 (hF m le_rfl), h0]
    simp
  have hpos : 0 < ‖b - A xG‖ := norm_pos_iff.2 h0
  have hsum := inv_sq_norm_residual_minRes_eq_sum hG hF h0
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i ∈ Finset.range (m + 1),
      1 / ‖b - A (xF i)‖ ^ 2 < 1 / (((m : ℝ) + 1) * ‖b - A xG‖ ^ 2) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hcon i hi'
    have hsq : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ Real.sqrt ((m : ℝ) + 1) * ‖b - A xG‖ := by positivity
    have h2 : ((m : ℝ) + 1) * ‖b - A xG‖ ^ 2 < ‖b - A (xF i)‖ ^ 2 := by
      nlinarith [mul_self_lt_mul_self hs0 h1, hsq]
    exact one_div_lt_one_div_of_lt (by positivity) h2
  have hkey : ∑ i ∈ Finset.range (m + 1), 1 / ‖b - A (xF i)‖ ^ 2
      < ∑ _i ∈ Finset.range (m + 1), 1 / (((m : ℝ) + 1) * ‖b - A xG‖ ^ 2) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hlt
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hkey
  rw [← hsum] at hkey
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have heq : ((m : ℝ) + 1) * (1 / (((m : ℝ) + 1) * ‖b - A xG‖ ^ 2)) = 1 / ‖b - A xG‖ ^ 2 := by
    field_simp
  push_cast at hkey
  rw [heq] at hkey
  exact lt_irrefl _ hkey

/-- Iterate relation (Saad, *Iterative Methods*, (6.74)): `x_m^G = s_m² x_{m-1}^G + c_m² x_m^F`
with
`c_m² = ‖r_m^G‖² / ‖r_m^F‖²`. -/
theorem minRes_eq_combination {m : ℕ} {xG xG' xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hinj : Function.Injective A)
    (h0 : b - A xF ≠ 0) :
    xG' = ((1 - ‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2 : ℝ) : 𝕜) • xG +
      ((‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2 : ℝ) : 𝕜) • xF := by
  rcases eq_or_ne (b - A xG) 0 with hG0 | hG0
  · have hG'0 : b - A xG' = 0 := by
      have hle := hG.norm_residual_le hG' (subspace_mono A (b - A x₀) (Nat.le_succ m))
      rw [hG0, norm_zero] at hle
      exact norm_le_zero_iff.1 hle
    have h1 : A xG' = b := (sub_eq_zero.1 hG'0).symm
    have h2 : A xG = b := (sub_eq_zero.1 hG0).symm
    have hxx : xG' = xG := hinj (h1.trans h2.symm)
    rw [hG'0, hxx]
    simp
  have horth : inner 𝕜 (b - A xF) (b - A xG) = 0 :=
    inner_eq_zero_symm.1 (inner_residual_minRes_galerkin hG hF)
  have hsmooth := smoothing_isMinResIterate hG hF hG0
  have hxG' : xG' = xG + (smoothingCoeff (b - A xG) (b - A xF) : 𝕜) • (xF - xG) :=
    hinj (sub_right_injective (hG'.residual_unique hsmooth))
  have hns : ‖b - A xG'‖ ^ 2
      = ‖b - A xG‖ ^ 2 * ‖b - A xF‖ ^ 2 / (‖b - A xF‖ ^ 2 + ‖b - A xG‖ ^ 2) := by
    rw [hxG', residual_smoothing_step]
    exact norm_smoothing_sq hG0 h0 horth
  have hb : (0 : ℝ) < ‖b - A xF‖ ^ 2 := by positivity
  have ha : (0 : ℝ) < ‖b - A xG‖ ^ 2 := by positivity
  have hcoef : ‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2
      = ‖b - A xG‖ ^ 2 / (‖b - A xF‖ ^ 2 + ‖b - A xG‖ ^ 2) := by
    rw [hns]
    field_simp
  rw [hcoef, hxG', smoothingCoeff_eq horth]
  push_cast
  module

/-- Brown (Saad, *Iterative Methods*, Prop 6.17): the minimal-residual iteration stagnates at
step `m + 1` (`‖r_{m+1}^G‖ = ‖r_m^G‖ ≠ 0`) iff no Galerkin iterate exists at step `m + 1`. -/
theorem norm_residual_minRes_eq_iff_not_exists_galerkin [FiniteDimensional 𝕜 E] {m : ℕ}
    {xG xG' : E} (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (h0 : b - A xG' ≠ 0) [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m + 1 ≤ grade A (b - A x₀)) :
    ‖b - A xG'‖ = ‖b - A xG‖ ↔ ¬ ∃ xF, IsGalerkinIterate A b x₀ (m + 1) xF := by
  constructor
  · rintro heq ⟨xF, hF⟩
    have hkey := inv_sq_norm_residual_minRes hG hG' hF h0
    rw [heq] at hkey
    have hzero : 1 / ‖b - A xF‖ ^ 2 = 0 := by linarith
    rw [one_div, inv_eq_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hzero
    exact h0 (by rw [hG'.apply_eq_of_exists hF.mem (sub_eq_zero.1 hzero).symm, sub_self])
  · intro hno
    -- the compression of `A` to `𝒦_{m+1}` is not injective, else the Galerkin iterate exists
    have hTinj : ¬ Function.Injective
        (((subspace A (b - A x₀) (m + 1)).orthogonalProjectionOnto :
            E →ₗ[𝕜] subspace A (b - A x₀) (m + 1)).comp
          (A.comp (subspace A (b - A x₀) (m + 1)).subtype)) := by
      intro hinj
      refine hno ?_
      obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj)
        ((subspace A (b - A x₀) (m + 1)).orthogonalProjectionOnto (b - A x₀))
      have hz' : (subspace A (b - A x₀) (m + 1)).starProjection (A (z : E))
          = (subspace A (b - A x₀) (m + 1)).starProjection (b - A x₀) := by
        rw [Submodule.starProjection_apply, Submodule.starProjection_apply]
        exact congrArg Subtype.val hz
      refine ⟨x₀ + (z : E), by simp, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
      have h1 : inner 𝕜 w (A (z : E)) = inner 𝕜 w (b - A x₀) := by
        rw [← Submodule.inner_starProjection_right hw (A (z : E)), hz',
          Submodule.inner_starProjection_right hw]
      rw [map_add, ← sub_sub, inner_sub_right, h1, sub_self]
    obtain ⟨z, hzmem, hzne⟩ := (Submodule.ne_bot_iff _).1
      (fun h => hTinj (LinearMap.ker_eq_bot.1 h))
    have hstar : (subspace A (b - A x₀) (m + 1)).starProjection (A (z : E)) = 0 := by
      rw [Submodule.starProjection_apply]
      simpa using congrArg Subtype.val (LinearMap.mem_ker.1 hzmem)
    have hAzperp : A (z : E) ∈ (subspace A (b - A x₀) (m + 1))ᗮ := by
      refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
      rw [← Submodule.inner_starProjection_right hw, hstar, inner_zero_right]
    have hrK : b - A xG ∈ subspace A (b - A x₀) (m + 1) := residual_mem_subspace_succ hG.mem
    by_cases hzm : (z : E) ∈ subspace A (b - A x₀) m
    · -- then `A z = 0` with `z ≠ 0` in `𝒦_m`, contradicting `m + 1 ≤ grade`
      exfalso
      have hAz0 : A (z : E) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hAzperp _
          (map_subspace_le A (b - A x₀) m (Submodule.mem_map_of_mem hzm)))
      obtain ⟨q, hqdeg, hq⟩ := (mem_subspace_iff_exists_aeval A (b - A x₀)).1 hzm
      have hqne : q ≠ 0 := by
        intro h
        refine hzne (Subtype.ext ?_)
        rw [← hq, h]
        simp
      have hXq : aeval A (X * q) (b - A x₀) = 0 := by
        rw [map_mul, Module.End.mul_apply, hq, aeval_X, hAz0]
      have hdeg : (X * q).natDegree ≤ m := by
        have hqm : q.natDegree < m := (natDegree_lt_iff_degree_lt hqne).2 hqdeg
        rw [natDegree_mul X_ne_zero hqne, natDegree_X]
        omega
      have hgr := grade_le_of_aeval_eq_zero (mul_ne_zero X_ne_zero hqne) hdeg hXq
      omega
    · -- `𝒦_{m+1} = 𝒦_m ⊔ 𝕜 ∙ z`, so `r_m^G ⟂ A 𝒦_{m+1}` and `x_m^G` is minimal at `m + 1`
      have hsup : subspace A (b - A x₀) (m + 1)
          ≤ subspace A (b - A x₀) m ⊔ 𝕜 ∙ (z : E) := by
        have hzsup : (z : E) ∈ subspace A (b - A x₀) m ⊔ 𝕜 ∙ ((A ^ m) (b - A x₀)) := by
          rw [← subspace_succ_eq_sup]
          exact z.2
        obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hzsup
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul, add_zero] at huw
          exact hzm (huw ▸ hu)
        refine (subspace_succ_eq_sup A (b - A x₀) m).le.trans
          (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
        have hpow : (A ^ m) (b - A x₀) = c⁻¹ • ((z : E) - u) := by
          rw [← huw, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hpow]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_left hu))
      have hzr : inner 𝕜 (A (z : E)) (b - A xG) = (0 : 𝕜) :=
        inner_eq_zero_symm.1 ((Submodule.mem_orthogonal _ _).1 hAzperp _ hrK)
      have horthAK : b - A xG ∈ ((subspace A (b - A x₀) (m + 1)).map A)ᗮ := by
        refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hsup hy)
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
        have hu0 : inner 𝕜 (A u) (b - A xG) = (0 : 𝕜) :=
          (Submodule.mem_orthogonal _ _).1 hG.residual_mem_orthogonal (A u)
            (Submodule.mem_map_of_mem hu)
        rw [map_add, map_smul, inner_add_left, inner_smul_left, hu0, hzr, mul_zero, add_zero]
      have hGK : IsMinResIterate A b x₀ (m + 1) xG :=
        IsMinRes.iff_isPetrovGalerkin.2
          ⟨subspace_mono A (b - A x₀) (Nat.le_succ m) hG.mem, horthAK⟩
      rw [hGK.residual_unique hG']

end Relations

/-- Weiss's minimal-residual smoothing (Saad, *Iterative Methods*, Alg 6.14) of a sequence of
iterates `xO`: `xS 0 = xO 0`, `xS (m+1) = xS m + η_m (xO (m+1) - xS m)` with `η_m` minimizing
the residual on the line. -/
noncomputable def mrs (A : E →ₗ[𝕜] E) (b : E) (xO : ℕ → E) : ℕ → E
  | 0 => xO 0
  | m + 1 => mrs A b xO m +
      (smoothingCoeff (b - A (mrs A b xO m)) (b - A (xO (m + 1))) : 𝕜) • (xO (m + 1) - mrs A b xO m)

/-- An exact iterate in `x₀ + K` is trivially a minimal-residual iterate on `K`. -/
private theorem isMinRes_of_residual_eq_zero {K : Submodule 𝕜 E} {x : E} (hmem : x - x₀ ∈ K)
    (h0 : b - A x = 0) : IsMinRes A b x₀ K x :=
  ⟨hmem, fun y _ => by rw [h0, norm_zero]; exact norm_nonneg _⟩

private theorem smoothingCoeff_zero_left (r : E) : (smoothingCoeff (0 : E) r : 𝕜) = 0 := by
  simp [smoothingCoeff]

set_option linter.unusedVariables false in
/-- Saad, *Iterative Methods*, §6.5.8 (Weiss; Zhou–Walker, *Residual smoothing techniques for
iterative methods*): minimal-residual smoothing of the Galerkin (FOM) iterates produces the
minimal-residual (GMRES) iterates. -/
theorem IsGalerkinIterate.mrs_isMinResIterate {xO : ℕ → E} (hinj : Function.Injective A) (m : ℕ)
    (hO : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xO i)) :
    IsMinResIterate A b x₀ m (mrs A b xO m) := by
  induction m with
  | zero =>
    have hx0 : xO 0 = x₀ := by
      have h := (hO 0 le_rfl).mem
      rw [subspace_zero] at h
      exact sub_eq_zero.1 (by simpa using h)
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mrs, hx0, sub_self]
      exact Submodule.zero_mem _
    · rw [subspace_zero] at hy
      have hyx : y = x₀ := sub_eq_zero.1 (by simpa using hy)
      rw [hyx, mrs, hx0]
  | succ n ih =>
    have hOn : ∀ i ≤ n, IsGalerkinIterate A b x₀ i (xO i) :=
      fun i hi => hO i (hi.trans (Nat.le_succ n))
    rcases eq_or_ne (b - A (mrs A b xO n)) 0 with h0 | h0
    · have hz : mrs A b xO (n + 1) = mrs A b xO n := by
        rw [mrs, h0, smoothingCoeff_zero_left, zero_smul, add_zero]
      rw [hz]
      exact isMinRes_of_residual_eq_zero
        (subspace_mono A (b - A x₀) (Nat.le_succ n) (ih hOn).mem) h0
    · rw [mrs]
      exact smoothing_isMinResIterate (ih hOn) (hO (n + 1) le_rfl) h0

/-- Saad, *Iterative Methods*, (6.79): for pairwise orthogonal residuals `r^O_j` (Galerkin
residuals), the smoothed residual is the weighted average
`r^S_m = (∑_{j ≤ m} r^O_j / ρ_j²) / (∑_{j ≤ m} 1 / ρ_j²)`. -/
theorem smul_combination_eq {S rho : ℝ} (hS : 0 < S) (hr : 0 < rho) (u v : E) :
    ((1 - S⁻¹ / (rho + S⁻¹) : ℝ) : 𝕜) • (((S⁻¹ : ℝ) : 𝕜) • u) +
        ((S⁻¹ / (rho + S⁻¹) : ℝ) : 𝕜) • v
      = (((S + 1 / rho)⁻¹ : ℝ) : 𝕜) • (u + ((1 / rho : ℝ) : 𝕜) • v) := by
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hr0 : rho ≠ 0 := ne_of_gt hr
  have hd : rho + S⁻¹ ≠ 0 := ne_of_gt (by have h := inv_pos.2 hS; linarith)
  have hd2 : S + 1 / rho ≠ 0 := ne_of_gt (by have h := one_div_pos.2 hr; linarith)
  have e1 : (1 - S⁻¹ / (rho + S⁻¹)) * S⁻¹ = (S + 1 / rho)⁻¹ := by
    field_simp
    ring
  have e2 : S⁻¹ / (rho + S⁻¹) = (S + 1 / rho)⁻¹ * (1 / rho) := by
    field_simp
  rw [smul_smul, ← RCLike.ofReal_mul, e1, smul_add, smul_smul, ← RCLike.ofReal_mul, e2]

theorem residual_mrs_eq {xO : ℕ → E} (hinj : Function.Injective A) (m : ℕ)
    (hO : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xO i)) (h0 : ∀ j ≤ m, b - A (xO j) ≠ 0) :
    b - A (mrs A b xO m) =
      (((∑ j ∈ Finset.range (m + 1), 1 / ‖b - A (xO j)‖ ^ 2)⁻¹ : ℝ) : 𝕜) •
        ∑ j ∈ Finset.range (m + 1), ((1 / ‖b - A (xO j)‖ ^ 2 : ℝ) : 𝕜) • (b - A (xO j)) := by
  induction m with
  | zero =>
    have hne : ‖b - A (xO 0)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (h0 0 le_rfl))
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, mrs]
    rw [smul_smul, ← RCLike.ofReal_mul, inv_mul_cancel₀ (one_div_ne_zero hne),
      RCLike.ofReal_one, one_smul]
  | succ n ih =>
    have hOn : ∀ j ≤ n, b - A (xO j) ≠ 0 := fun j hj => h0 j (hj.trans (Nat.le_succ n))
    have hGn : ∀ i ≤ n, IsGalerkinIterate A b x₀ i (xO i) :=
      fun i hi => hO i (hi.trans (Nat.le_succ n))
    have hSpos : (0 : ℝ) < ∑ j ∈ Finset.range (n + 1), 1 / ‖b - A (xO j)‖ ^ 2 :=
      Finset.sum_pos (fun j hj => by
        have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        exact one_div_pos.2 (pow_pos (norm_pos_iff.2 (hOn j hj')) 2)) ⟨0, by simp⟩
    have hrpos : (0 : ℝ) < ‖b - A (xO (n + 1))‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (h0 (n + 1) le_rfl)) 2
    have hmres := IsGalerkinIterate.mrs_isMinResIterate hinj n hGn
    have hSne : b - A (mrs A b xO n) ≠ 0 := fun h =>
      hOn n le_rfl (galerkin_residual_eq_zero_of_minRes hmres h (hO n (Nat.le_succ n)))
    have hsum := inv_sq_norm_residual_minRes_eq_sum hmres (fun i hi => hO i (hi.trans (Nat.le_succ n))) hSne
    have hsn : ‖b - A (mrs A b xO n)‖ ^ 2
        = (∑ j ∈ Finset.range (n + 1), 1 / ‖b - A (xO j)‖ ^ 2)⁻¹ := by
      rw [← hsum, one_div, inv_inv]
    have horth : inner 𝕜 (b - A (xO (n + 1))) (b - A (mrs A b xO n)) = 0 :=
      inner_eq_zero_symm.1 (inner_residual_minRes_galerkin hmres (hO (n + 1) le_rfl))
    rw [Finset.sum_range_succ (fun j => 1 / ‖b - A (xO j)‖ ^ 2) (n + 1),
      Finset.sum_range_succ
        (fun j => ((1 / ‖b - A (xO j)‖ ^ 2 : ℝ) : 𝕜) • (b - A (xO j))) (n + 1),
      mrs, residual_smoothing_step, smoothing_eq horth, hsn, ih hGn hOn]
    exact smul_combination_eq (𝕜 := 𝕜) (E := E) hSpos hrpos _ _

end Krylov
