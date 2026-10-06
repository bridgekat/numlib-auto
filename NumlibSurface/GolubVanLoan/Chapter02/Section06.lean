import Numlib.Conditioning.LinearSystem
import Numlib.Conditioning.LinearSystem.Componentwise
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.GolubVanLoan.Chapter02.Section03
import NumlibSurface.GolubVanLoan.Chapter02.Section04

/-!
# Golub–Van Loan §2.6: the sensitivity of square systems

Surface file for [golub2013matrix] §2.6: the SVD expansion of the solution (2.6.1), the derivative
of the perturbed solution and the first-order bounds (2.6.2), (2.6.4) in rigorous form, the
condition number (2.6.3) and its characterizations (2.6.5)–(2.6.8), `κ ≥ 1`, the examples (2.6.9)
and `Dₙ`, the rigorous normwise bounds Lemma 2.6.1 and Theorem 2.6.2 with (2.6.11), the
componentwise Theorem 2.6.3 with the Skeel condition number, and the Oettli–Prager theorem
(2.6.13).

## Conventions

Norms are the `p`-norms, `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`: `‖x‖_p = ‖WithLp.toLp p x‖`,
`‖A‖_p = Matrix.lpOpNorm p A`. The book's "any vector norm and consistent matrix norm" is the
backbone's operator statement (`Numlib/Conditioning/LinearSystem`, on any normed space), which
this file instantiates at `PiLp p` through `Matrix.lpCLM` and `Matrix.lpEquiv`. The condition
number `κ_p(A) = ‖A‖_p ‖A⁻¹‖_p` is the backbone's real-valued `Matrix.condNumberLp p A`, used under
an explicit `IsUnit A`; the book's convention `κ(A) = ∞` for singular `A` is the surface
definition `kappa`. The first-order bounds (2.6.2) and (2.6.4), printed with `+ O(ε²)`, are stated
in the rigorous form whose factor `1 / (1 - |ε| ‖A⁻¹‖ ‖F‖) = 1 + O(ε)` produces the `O(ε²)` term.
`σ_max(A)` and `σ_min(A)` in (2.6.5) are §2.4's `sigmaMax` and `sigmaMin` (the convention of
`NumlibSurface/GolubVanLoan`). An SVD `A = U Σ Vᵀ` in (2.6.1) is given by its three factors.

## Sources

Backbone `Numlib/Conditioning/LinearSystem` (+ `/Componentwise`: the Skeel number and
Oettli–Prager), `Numlib/Analysis/Matrix/OperatorNorm` (`Matrix.condNumberLp`, `Matrix.lpEquiv`),
`Numlib/LinearAlgebra/Matrix/SVD`. The `2 × 2` example after Theorem 2.6.2 (the bound attained or
not) is a numerical example.

## Readings and errata

Lemma 2.6.1 carries the nonsingularity of `A` through the convention `κ = ∞`; it is an explicit
hypothesis here. Theorem 2.6.3 prints its hypothesis as "`δ κ_∞(A) = r < 1`", a typo for `ε`, and
its second display "`(A + ΔA) y, = b + ΔbΔA ∈ …`" is conversion damage for
`(A + ΔA) y = b + Δb`, `ΔA ∈ ℝ^{n×n}`, `Δb ∈ ℝⁿ`.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace GolubVanLoan.Chapter02

variable {n : ℕ}

/-! ### Glue between matrices and operators on `PiLp p` -/

/-- The operator condition number of the coercion of `Matrix.lpEquiv`. -/
private theorem condNumber_coe_lpEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) :
    NormedRing.condNumber
        (lpEquiv p hA : PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ)) =
      condNumberLp p A := by
  rw [coe_lpEquiv, condNumberLp_eq_condNumber]

/-- A perturbation with `‖ΔA‖_p ≤ ε ‖A‖_p` and `ε κ_p(A) < 1` keeps `A` nonsingular (Theorem 2.3.4,
since `‖A⁻¹ ΔA‖_p ≤ ε κ_p(A)`). -/
private theorem isUnit_add_of_lpOpNorm_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {A ΔA : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {ε : ℝ}
    (hΔA : lpOpNorm p ΔA ≤ ε * lpOpNorm p A) (hr : ε * condNumberLp p A < 1) :
    IsUnit (A + ΔA) := by
  refine (theorem_2_3_4 p hA (lt_of_le_of_lt ?_ hr)).1
  calc lpOpNorm p (A⁻¹ * ΔA) ≤ lpOpNorm p A⁻¹ * lpOpNorm p ΔA := lpOpNorm_mul_le p _ _
    _ ≤ lpOpNorm p A⁻¹ * (ε * lpOpNorm p A) :=
        mul_le_mul_of_nonneg_left hΔA (lpOpNorm_nonneg _ _)
    _ = ε * condNumberLp p A := by rw [condNumberLp]; ring

/-! ### §2.6.1 An SVD analysis -/

/-- **(2.6.1)**: if `A = U Σ Vᵀ` is an SVD of a nonsingular `A`, then
`x = A⁻¹ b = ∑ᵢ (uᵢᵀ b / σᵢ) vᵢ`. -/
theorem equation_2_6_1 {A U V : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hU : U ∈ orthogonalGroup (Fin n) ℝ) (hV : V ∈ orthogonalGroup (Fin n) ℝ) {σ : ℕ → ℝ}
    (h : Uᵀ * A * V = diagonal fun i : Fin n => σ i) (b : Fin n → ℝ) :
    A⁻¹ *ᵥ b = ∑ i : Fin n, ((U.col i ⬝ᵥ b) / σ i) • V.col i := by
  have h' : star U * A * V = rectDiagonal σ := by
    rw [rectDiagonal_eq_diagonal, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, h]
  rw [← pinv_eq_inv hA, pinv_eq_of_svd hU hV h', rectDiagonal_eq_diagonal, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, ← mulVec_mulVec, ← mulVec_mulVec]
  ext k
  simp only [mulVec, dotProduct, diagonal_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    col_apply, transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_inv_mul]
  ring

/-! ### §2.6.2 Condition -/

/-- **§2.6.2**: for nonsingular `A`, the solution `x(ε) = (A + εF)⁻¹ (b + εf)` of the parameterized
system `(A + εF) x(ε) = b + εf` is differentiable at `0` with `ẋ(0) = A⁻¹ (f - F x)`,
`x = A⁻¹ b`. -/
theorem perturbed_solution_hasDerivAt {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (F : Matrix (Fin n) (Fin n) ℝ) (b f : Fin n → ℝ) :
    HasDerivAt (fun ε : ℝ => (A + ε • F)⁻¹ *ᵥ (b + ε • f)) (A⁻¹ *ᵥ (f - F *ᵥ (A⁻¹ *ᵥ b))) 0 := by
  have h := hasDerivAt_perturbed_solution (lpEquiv 2 hA) (lpCLM 2 F) (WithLp.toLp 2 b)
    (WithLp.toLp 2 f)
  rw [coe_lpEquiv, coe_lpEquiv_symm] at h
  have key : ∀ ε : ℝ,
      (Ring.inverse (lpCLM 2 A + ε • lpCLM 2 F)) (WithLp.toLp 2 b + ε • WithLp.toLp 2 f)
      = WithLp.toLp 2 ((A + ε • F)⁻¹ *ᵥ (b + ε • f)) := fun ε => by
    rw [← lpCLM_smul, ← lpCLM_add, ringInverse_lpCLM, lpCLM_apply, ← WithLp.toLp_smul,
      ← WithLp.toLp_add, WithLp.ofLp_toLp]
  simp_rw [key] at h
  exact (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 _).comp_hasDerivAt 0 h

/-- **(2.6.2), rigorous form.** With `x(ε)` as above, `x ≠ 0` and `|ε| ‖A⁻¹‖_p ‖F‖_p < 1`,
`‖x(ε) - x‖_p / ‖x‖_p ≤ |ε| ‖A⁻¹‖_p (‖f‖_p / ‖x‖_p + ‖F‖_p) / (1 - |ε| ‖A⁻¹‖_p ‖F‖_p)`; the book's
`+ O(ε²)` is the factor `1 / (1 - |ε| ‖A⁻¹‖ ‖F‖) = 1 + O(ε)`. -/
theorem equation_2_6_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A F : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    {b f x : Fin n → ℝ} (hx : A *ᵥ x = b) (hx0 : x ≠ 0) {ε : ℝ}
    (hε : |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F < 1) :
    ‖WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f) - x)‖ / ‖WithLp.toLp p x‖ ≤
      |ε| * lpOpNorm p A⁻¹ * (‖WithLp.toLp p f‖ / ‖WithLp.toLp p x‖ + lpOpNorm p F) /
        (1 - |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F) := by
  have hsmall : lpOpNorm p A⁻¹ * lpOpNorm p (ε • F) < 1 := by
    rw [lpOpNorm_smul, Real.norm_eq_abs]; linarith
  have hunit : IsUnit (A + ε • F) := by
    refine (theorem_2_3_4 p hA (lt_of_le_of_lt (lpOpNorm_mul_le p _ _) hsmall)).1
  have h := relative_error_le_norm_inverse (lpEquiv p hA) (lpCLM p (ε • F))
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p (ε • f)) (x := WithLp.toLp p x)
    (y := WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f)))
    (by simp [hx]) (by
      rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp,
        mulVec_nonsing_inv_mulVec hunit, WithLp.toLp_add])
    (by rw [coe_lpEquiv_symm]; exact hsmall) (by simpa using hx0)
  rw [coe_lpEquiv_symm, ← WithLp.toLp_sub] at h
  change _ ≤ lpOpNorm p A⁻¹ / (1 - lpOpNorm p A⁻¹ * lpOpNorm p (ε • F)) *
    (‖WithLp.toLp p (ε • f)‖ / ‖WithLp.toLp p x‖ + lpOpNorm p (ε • F)) at h
  rw [lpOpNorm_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  rw [div_mul_eq_mul_div, mul_div_assoc]
  ring_nf

open Classical in
/-- **(2.6.3), the condition number** `κ(A) = ‖A‖ ‖A⁻¹‖` in the `p`-norm, with the book's
convention `κ(A) = ∞` for singular `A`. -/
noncomputable def kappa (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  if IsUnit A then ENNReal.ofReal (condNumberLp p A) else ⊤

/-- For nonsingular `A`, `kappa` is the backbone's `κ_p(A) = ‖A‖_p ‖A⁻¹‖_p`. -/
theorem kappa_of_isUnit (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) : kappa p A = ENNReal.ofReal (condNumberLp p A) :=
  ite_eq_left hA

/-- For singular `A`, `κ(A) = ∞`. -/
theorem kappa_of_not_isUnit (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ¬ IsUnit A) : kappa p A = ⊤ :=
  ite_eq_right hA

/-- **(2.6.4), rigorous form.** With `x(ε)` as above, `x ≠ 0`, `b ≠ 0` and
`|ε| ‖A⁻¹‖_p ‖F‖_p < 1`,
`‖x(ε) - x‖_p / ‖x‖_p ≤ κ_p(A) / (1 - |ε| ‖A⁻¹‖_p ‖F‖_p) · (ρ_A + ρ_b)` with
the relative errors `ρ_A = |ε| ‖F‖_p / ‖A‖_p` and `ρ_b = |ε| ‖f‖_p / ‖b‖_p`. -/
theorem equation_2_6_4 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A F : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    {b f x : Fin n → ℝ} (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hb : b ≠ 0) {ε : ℝ}
    (hε : |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F < 1) :
    ‖WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f) - x)‖ / ‖WithLp.toLp p x‖ ≤
      condNumberLp p A / (1 - |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F) *
        (|ε| * lpOpNorm p F / lpOpNorm p A + |ε| * ‖WithLp.toLp p f‖ / ‖WithLp.toLp p b‖) := by
  have hsmall : lpOpNorm p A⁻¹ * lpOpNorm p (ε • F) < 1 := by
    rw [lpOpNorm_smul, Real.norm_eq_abs]; linarith
  have hunit : IsUnit (A + ε • F) :=
    (theorem_2_3_4 p hA (lt_of_le_of_lt (lpOpNorm_mul_le p _ _) hsmall)).1
  have h := relative_error_le_condNumber (lpEquiv p hA) (lpCLM p (ε • F))
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p (ε • f)) (x := WithLp.toLp p x)
    (y := WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f)))
    (by simp [hx]) (by
      rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp,
        mulVec_nonsing_inv_mulVec hunit, WithLp.toLp_add])
    (by rw [coe_lpEquiv_symm]; exact hsmall) (by simpa using hx0) (by simpa using hb)
  rw [condNumber_coe_lpEquiv, coe_lpEquiv_symm, ← WithLp.toLp_sub, coe_lpEquiv] at h
  change _ ≤ condNumberLp p A / (1 - lpOpNorm p A⁻¹ * lpOpNorm p (ε • F)) *
    (lpOpNorm p (ε • F) / lpOpNorm p A + ‖WithLp.toLp p (ε • f)‖ / ‖WithLp.toLp p b‖) at h
  rw [lpOpNorm_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  ring_nf

section L2

open scoped Matrix.Norms.L2Operator

/-- **(2.6.5)**: `κ₂(A) = ‖A‖₂ ‖A⁻¹‖₂ = σ_max(A) / σ_min(A)` for nonsingular `A`. -/
theorem equation_2_6_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    condNumberLp 2 A = lpOpNorm 2 A * lpOpNorm 2 A⁻¹ ∧
      condNumberLp 2 A = sigmaMax A / sigmaMin A := by
  refine ⟨rfl, ?_⟩
  rw [sigmaMax_eq_iSup_colSingularValues, sigmaMin_eq_iInf_colSingularValues A le_rfl]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Subsingleton.elim A 0]
    simp [condNumberLp]
  · have h := condNumber_l2_eq_div_colSingularValues A ((isUnit_iff_isUnit_det A).1 hA)
    rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse] at h
    rw [condNumberLp, lpOpNorm_two, lpOpNorm_two]
    exact h

end L2

/-- **(2.6.6), Kahan**: `1 / κ_p(A) = min_{A + ΔA singular} ‖ΔA‖_p / ‖A‖_p` for nonsingular
`A ∈ ℝ^{n×n}`, `n ≥ 1`: `κ_p(A)` measures the relative distance from `A` to the singular
matrices. -/
theorem equation_2_6_6 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hn : 0 < n) :
    IsLeast {r : ℝ | ∃ ΔA : Matrix (Fin n) (Fin n) ℝ, ¬ IsUnit (A + ΔA) ∧
      lpOpNorm p ΔA / lpOpNorm p A = r} (1 / condNumberLp p A) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial (PiLp p fun _ : Fin n => ℝ) := (WithLp.equiv p (Fin n → ℝ)).nontrivial
  have h := (lpEquiv p hA).isLeast_dist_singular
  rw [condNumber_lpEquiv, coe_lpEquiv] at h
  convert h using 1
  ext r
  constructor
  · rintro ⟨ΔA, hs, rfl⟩
    exact ⟨lpCLM p ΔA, by rwa [← lpCLM_add, isUnit_lpCLM_iff], rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨ΔA, rfl⟩ := (lpCLMEquiv (𝕜 := ℝ) (m := Fin n) (n := Fin n) p).surjective t
    rw [lpCLMEquiv_apply, ← lpCLM_add, isUnit_lpCLM_iff] at ht
    exact ⟨ΔA, ht, rfl⟩

/-- **(2.6.7)**: the condition number is a normalized Fréchet derivative of `A ↦ A⁻¹`,
`κ_p(A) = lim_{ε → 0⁺} sup_{‖ΔA‖_p ≤ ε ‖A‖_p} ‖(A + ΔA)⁻¹ - A⁻¹‖_p / (ε ‖A⁻¹‖_p)` for nonsingular
`A`, `n ≥ 1`. -/
theorem equation_2_6_7 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hn : 0 < n) :
    Tendsto (fun ε : ℝ => (⨆ ΔA : {ΔA : Matrix (Fin n) (Fin n) ℝ //
        lpOpNorm p ΔA ≤ ε * lpOpNorm p A}, lpOpNorm p ((A + ΔA.1)⁻¹ - A⁻¹)) /
          (ε * lpOpNorm p A⁻¹)) (𝓝[>] 0) (𝓝 (condNumberLp p A)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial (PiLp p fun _ : Fin n => ℝ) := (WithLp.equiv p (Fin n → ℝ)).nontrivial
  have h := (lpEquiv p hA).tendsto_iSup_norm_inverse_add_sub_div
  rw [condNumber_lpEquiv, coe_lpEquiv, coe_lpEquiv_symm] at h
  refine h.congr fun ε => ?_
  congr 1
  let e : {ΔA : Matrix (Fin n) (Fin n) ℝ // lpOpNorm p ΔA ≤ ε * lpOpNorm p A} ≃
      {T : PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ) //
        ‖T‖ ≤ ε * ‖lpCLM p A‖} :=
    (lpCLMEquiv p).toEquiv.subtypeEquiv fun _ => Iff.rfl
  refine (Equiv.iSup_congr e fun ΔA => ?_).symm
  change ‖Ring.inverse (lpCLM p A + lpCLM p ΔA.1) - lpCLM p A⁻¹‖ = _
  rw [← lpCLM_add, ringInverse_lpCLM, ← lpCLM_sub]
  rfl

/-- **(2.6.8)**: on `ℝ^{n×n}`, `(1/n) κ₂ ≤ κ₁ ≤ n κ₂`, `(1/n) κ_∞ ≤ κ₂ ≤ n κ_∞` and
`(1/n²) κ₁ ≤ κ_∞ ≤ n² κ₁`: any two condition numbers are equivalent. -/
theorem equation_2_6_8 (A : Matrix (Fin n) (Fin n) ℝ) :
    1 / (n : ℝ) * condNumberLp 2 A ≤ condNumberLp 1 A ∧ condNumberLp 1 A ≤ n * condNumberLp 2 A ∧
      1 / (n : ℝ) * condNumberLp ∞ A ≤ condNumberLp 2 A ∧
      condNumberLp 2 A ≤ n * condNumberLp ∞ A ∧
      1 / (n : ℝ) ^ 2 * condNumberLp 1 A ≤ condNumberLp ∞ A ∧
      condNumberLp ∞ A ≤ (n : ℝ) ^ 2 * condNumberLp 1 A := by
  have hnn : ∀ q : ℝ≥0∞, [Fact (1 ≤ q)] → 0 ≤ condNumberLp q A := fun q _ =>
    mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  obtain ⟨h12, h21⟩ := condNumberLp_le_card_rpow_mul_condNumberLp (p := 1) (q := 2)
    (by norm_num) A
  obtain ⟨h2t, ht2⟩ := condNumberLp_le_card_rpow_mul_condNumberLp (p := 2) (q := ∞) le_top A
  obtain ⟨h1t, ht1⟩ := condNumberLp_le_card_rpow_mul_condNumberLp (p := 1) (q := ∞) le_top A
  norm_num at h12 h21 h2t ht2 h1t ht1
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  refine ⟨?_, h12, ?_, h2t, ?_, ht1⟩
  · rw [one_div_mul_eq_div]
    exact div_le_of_le_mul₀ hn0 (hnn 1) (h21.trans_eq (mul_comm _ _))
  · rw [one_div_mul_eq_div]
    exact div_le_of_le_mul₀ hn0 (hnn 2) (ht2.trans_eq (mul_comm _ _))
  · rw [one_div_mul_eq_div]
    exact div_le_of_le_mul₀ (by positivity) (hnn ∞) (h1t.trans_eq (mul_comm _ _))

section L2

open scoped Matrix.Norms.L2Operator

/-- **§2.6.2**: `κ_p(A) ≥ 1` for every `A ∈ ℝ^{n×n}`, `n ≥ 1` (for singular `A`, `κ = ∞`). -/
theorem one_le_kappa (p : ℝ≥0∞) [Fact (1 ≤ p)] (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    1 ≤ kappa p A := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_cases hA : IsUnit A
  · rw [kappa_of_isUnit p hA]
    exact ENNReal.one_le_ofReal.2 (one_le_condNumberLp p hA)
  · rw [kappa_of_not_isUnit p hA]
    exact le_top

/-- **§2.6.2**: orthogonal matrices are perfectly conditioned in the 2-norm,
`κ₂(Q) = ‖Q‖₂ ‖Qᵀ‖₂ = 1` (`n ≥ 1`). -/
theorem kappa_two_eq_one_of_mem_orthogonalGroup (hn : 0 < n) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) : kappa 2 Q = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hQu : IsUnit Q :=
    ⟨⟨Q, star Q, mem_unitaryGroup_iff.1 hQ, mem_unitaryGroup_iff'.1 hQ⟩, rfl⟩
  have h := condNumber_l2_of_mem_unitaryGroup hQ
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse] at h
  rw [kappa_of_isUnit 2 hQu, condNumberLp, lpOpNorm_two, lpOpNorm_two, h, ENNReal.ofReal_one]

end L2

/-! ### §2.6.3 Determinants and nearness to singularity -/

/-- The entries of the matrix `Bₙ` of (2.6.9) on natural indices. -/
private def bEntry (i k : ℕ) : ℝ :=
  if i = k then 1 else if i < k then -1 else 0

/-- The entries of `Bₙ⁻¹` on natural indices: `1` on the diagonal, `2^{j-i-1}` above it. -/
private def cEntry (k j : ℕ) : ℝ :=
  if k = j then 1 else if k < j then 2 ^ (j - k - 1) else 0

private theorem bEntry_of_lt {i k : ℕ} (h : k < i) : bEntry i k = 0 := by
  simp [bEntry, show i ≠ k by omega, show ¬ i < k by omega]

private theorem bEntry_of_gt {i k : ℕ} (h : i < k) : bEntry i k = -1 := by
  simp [bEntry, h.ne, h]

private theorem cEntry_of_gt {k j : ℕ} (h : j < k) : cEntry k j = 0 := by
  simp [cEntry, show k ≠ j by omega, show ¬ k < j by omega]

/-- The columns of `Bₙ⁻¹` double: `c_{k,j+1} = 2 c_{k,j} - δ_{k,j} + δ_{k,j+1}`. -/
private theorem cEntry_succ (k j : ℕ) :
    cEntry k (j + 1) = 2 * cEntry k j - (if k = j then 1 else 0) +
      (if k = j + 1 then 1 else 0) := by
  rcases lt_trichotomy k j with h | rfl | h
  · have e : j + 1 - k - 1 = (j - k - 1) + 1 := by omega
    simp only [cEntry]
    rw [e]
    simp only [show k ≠ j + 1 by omega, show k < j + 1 by omega, h.ne, h, ↓reduceIte, pow_succ]
    ring
  · norm_num [cEntry]
  · rcases (show k = j + 1 ∨ j + 1 < k by omega) with rfl | h'
    · simp [cEntry]
    · rw [cEntry_of_gt h, cEntry_of_gt h']
      simp [show k ≠ j by omega, show k ≠ j + 1 by omega]

/-- One more column: `∑ₖ b_{ik} c_{k,j+1} = 2 ∑ₖ b_{ik} c_{kj} - b_{ij} + b_{i,j+1}`. -/
private theorem sum_bEntry_mul_cEntry_succ {n i j : ℕ} (hj : j + 1 < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k (j + 1) =
      2 * ∑ k ∈ range n, bEntry i k * cEntry k j - bEntry i j + bEntry i (j + 1) := by
  have h : ∀ k, bEntry i k * cEntry k (j + 1) = 2 * (bEntry i k * cEntry k j) -
      (if k = j then bEntry i k else 0) + (if k = j + 1 then bEntry i k else 0) := fun k => by
    rw [cEntry_succ]
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.sum_ite_eq', ite_eq_left (mem_range.2 (by omega)), ite_eq_left (mem_range.2 hj)]

/-- Row `i` of `Bₙ` against column `j < i` of `Bₙ⁻¹`. -/
private theorem sum_bEntry_mul_cEntry_of_lt {n i j : ℕ} (hji : j < i) :
    ∑ k ∈ range n, bEntry i k * cEntry k j = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i ≤ k
  · rw [cEntry_of_gt (by omega), mul_zero]
  · rw [bEntry_of_lt (by omega), zero_mul]

/-- Row `i` of `Bₙ` against column `i` of `Bₙ⁻¹`. -/
private theorem sum_bEntry_mul_cEntry_self {n i : ℕ} (hi : i < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k i = 1 := by
  rw [Finset.sum_eq_single_of_mem i (mem_range.2 hi)]
  · simp [bEntry, cEntry]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [bEntry_of_lt h, zero_mul]
    · rw [cEntry_of_gt h, mul_zero]

/-- Row `i` of `Bₙ` against column `j > i` of `Bₙ⁻¹`, by induction on `j`. -/
private theorem sum_bEntry_mul_cEntry_of_gt {n i : ℕ} (d : ℕ) (hj : i + 1 + d < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k (i + 1 + d) = 0 := by
  induction d with
  | zero =>
    rw [add_zero, sum_bEntry_mul_cEntry_succ (by omega), sum_bEntry_mul_cEntry_self (by omega),
      bEntry_of_gt (by omega : i < i + 1)]
    norm_num [bEntry]
  | succ d ih =>
    rw [show i + 1 + (d + 1) = i + 1 + d + 1 by ring, sum_bEntry_mul_cEntry_succ (by omega),
      ih (by omega), bEntry_of_gt (by omega : i < i + 1 + d),
      bEntry_of_gt (by omega : i < i + 1 + d + 1)]
    ring

/-- `Bₙ Bₙ⁻¹ = I` on natural indices. -/
private theorem sum_bEntry_mul_cEntry {n i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k j = if i = j then 1 else 0 := by
  rcases lt_trichotomy j i with hji | rfl | hij
  · rw [ite_eq_right hji.ne', sum_bEntry_mul_cEntry_of_lt hji]
  · rw [ite_eq_left rfl, sum_bEntry_mul_cEntry_self hi]
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
    rw [ite_eq_right (by omega), sum_bEntry_mul_cEntry_of_gt d hj]

/-- The row sums of `|Bₙ|`: `∑_{k < m} |b_{ik}| = m - i` for `i ≤ m`. -/
private theorem sum_abs_bEntry {i m : ℕ} (hi : i ≤ m) :
    ∑ k ∈ range m, |bEntry i k| = ((m - i : ℕ) : ℝ) := by
  induction m, hi using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, Nat.cast_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [bEntry_of_lt (mem_range.1 hk), abs_zero]
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 - i = (m - i) + 1 by omega, Nat.cast_succ]
    congr 1
    rcases hm.eq_or_lt with rfl | h
    · simp [bEntry]
    · rw [bEntry_of_gt h, abs_neg, abs_one]

/-- The row sums of `|Bₙ⁻¹|`: `∑_{k < m} |c_{ik}| = 2^{m-i-1}` for `i < m`. -/
private theorem sum_abs_cEntry {i m : ℕ} (hi : i < m) :
    ∑ k ∈ range m, |cEntry i k| = 2 ^ (m - i - 1) := by
  induction m, hi using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => ?_]
    · simp [cEntry]
    · rw [cEntry_of_gt (mem_range.1 hk), abs_zero]
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 - i - 1 = (m - i - 1) + 1 by omega, pow_succ]
    have hc : cEntry i m = 2 ^ (m - i - 1) := by
      simp [cEntry, show i ≠ m by omega, show i < m by omega]
    rw [hc, abs_of_pos (by positivity)]
    ring

/-- A finite supremum attained at the first index. -/
private theorem iSup_eq_of_le_zero (hn : 0 < n) {f : Fin n → ℝ} (h : ∀ i, f i ≤ f ⟨0, hn⟩) :
    ⨆ i, f i = f ⟨0, hn⟩ :=
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  le_antisymm (ciSup_le h) (le_ciSup (Set.finite_range f).bddAbove _)

/-- **(2.6.9)**: the unit upper triangular `Bₙ` with `-1` above the diagonal has `det(Bₙ) = 1` but
`κ_∞(Bₙ) = n · 2^{n-1}`: determinant size does not measure conditioning. -/
theorem equation_2_6_9 (hn : 0 < n) :
    (of fun i j : Fin n => if i = j then (1 : ℝ) else if i < j then -1 else 0).det = 1 ∧
      condNumberLp ∞ (of fun i j : Fin n => if i = j then (1 : ℝ) else if i < j then -1 else 0) =
        n * 2 ^ (n - 1) := by
  set B : Matrix (Fin n) (Fin n) ℝ := of fun i j => if i = j then 1 else if i < j then -1 else 0
  set C : Matrix (Fin n) (Fin n) ℝ := of fun i j => cEntry i j
  have hB : ∀ i j : Fin n, B i j = bEntry i j := fun i j => by
    simp only [B, bEntry, of_apply, Fin.ext_iff, Fin.lt_def]
  have hC : ∀ i j : Fin n, C i j = cEntry i j := fun _ _ => rfl
  have hBC : B * C = 1 := by
    ext i j
    rw [mul_apply, one_apply]
    simp_rw [hB, hC]
    rw [Fin.sum_univ_eq_sum_range (fun k => bEntry i k * cEntry k j) n,
      sum_bEntry_mul_cEntry i.isLt j.isLt]
    simp [Fin.ext_iff]
  have hinv : B⁻¹ = C := inv_eq_right_inv hBC
  refine ⟨?_, ?_⟩
  · rw [det_of_isUpperTriangular fun i j (hji : j < i) => ?_]
    · simp [B]
    · simp [B, hji.ne', not_lt.2 hji.le]
  · have hBrow : ∀ i : Fin n, ∑ j, |B i j| = ((n - i : ℕ) : ℝ) := fun i => by
      simp_rw [hB]
      rw [Fin.sum_univ_eq_sum_range (fun k => |bEntry i k|) n, sum_abs_bEntry i.isLt.le]
    have hCrow : ∀ i : Fin n, ∑ j, |C i j| = 2 ^ (n - i - 1) := fun i => by
      simp_rw [hC]
      rw [Fin.sum_univ_eq_sum_range (fun k => |cEntry i k|) n, sum_abs_cEntry i.isLt]
    rw [condNumberLp, equation_2_3_10, equation_2_3_10, hinv]
    simp_rw [hBrow, hCrow]
    rw [iSup_eq_of_le_zero hn fun i => by dsimp only; exact_mod_cast Nat.sub_le n i,
      iSup_eq_of_le_zero hn fun i =>
        pow_le_pow_right₀ one_le_two (by dsimp only; omega)]
    simp

/-- **§2.6.3**: `Dₙ = diag(10⁻¹, …, 10⁻¹)` is perfectly conditioned, `κ_p(Dₙ) = 1`, although
`det(Dₙ) = 10⁻ⁿ`: determinant size does not measure conditioning. -/
theorem condNumberLp_diag_tenth (p : ℝ≥0∞) [Fact (1 ≤ p)] (hn : 0 < n) :
    condNumberLp p (diagonal fun _ : Fin n => (10 : ℝ)⁻¹) = 1 ∧
      (diagonal fun _ : Fin n => (10 : ℝ)⁻¹).det = 10 ^ (-(n : ℤ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨?_, ?_⟩
  · rw [← smul_one_eq_diagonal]
    exact condNumberLp_smul_one p (by norm_num)
  · rw [det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
      _root_.zpow_neg, zpow_natCast]

/-! ### §2.6.4 A rigorous norm bound -/

/-- **Lemma 2.6.1.** Suppose `Ax = b` with `A` nonsingular and `b ≠ 0`, `(A + ΔA) y = b + Δb` with
`‖ΔA‖_p ≤ ε ‖A‖_p` and `‖Δb‖_p ≤ ε ‖b‖_p`. If `ε κ_p(A) = r < 1`, then `A + ΔA` is nonsingular and
`‖y‖_p / ‖x‖_p ≤ (1 + r) / (1 - r)`. -/
theorem lemma_2_6_1 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b Δb x y : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hy : (A + ΔA) *ᵥ y = b + Δb) {ε : ℝ} (hΔA : lpOpNorm p ΔA ≤ ε * lpOpNorm p A)
    (hΔb : ‖WithLp.toLp p Δb‖ ≤ ε * ‖WithLp.toLp p b‖) (hr : ε * condNumberLp p A < 1) :
    IsUnit (A + ΔA) ∧
      ‖WithLp.toLp p y‖ / ‖WithLp.toLp p x‖ ≤
        (1 + ε * condNumberLp p A) / (1 - ε * condNumberLp p A) := by
  refine ⟨isUnit_add_of_lpOpNorm_le p hA hΔA hr, ?_⟩
  have h := norm_add_div_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p ΔA)
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p Δb) (x := WithLp.toLp p x)
    (y := WithLp.toLp p y) (by simp [hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp, hy, WithLp.toLp_add])
    (by rw [coe_lpEquiv]; exact hΔA) hΔb (by rwa [condNumber_coe_lpEquiv]) (by simpa using hb)
  rwa [condNumber_coe_lpEquiv] at h

/-- **(2.6.11)**: if `Ax = b` with `A` nonsingular and `(A + ΔA) y = b + Δb`, then
`y - x = A⁻¹ Δb - A⁻¹ ΔA y`. -/
theorem equation_2_6_11 {A ΔA : Matrix (Fin n) (Fin n) ℝ} {b Δb x y : Fin n → ℝ}
    (hA : IsUnit A) (hx : A *ᵥ x = b) (hy : (A + ΔA) *ᵥ y = b + Δb) :
    y - x = A⁻¹ *ᵥ Δb - A⁻¹ *ᵥ (ΔA *ᵥ y) := by
  rw [sub_eq_inv_mulVec_of_mulVec_eq hA hx hy, mulVec_sub]

/-- **Theorem 2.6.2, (2.6.10).** Under the hypotheses of Lemma 2.6.1,
`‖y - x‖_p / ‖x‖_p ≤ 2ε / (1 - r) · κ_p(A)`. -/
theorem theorem_2_6_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b Δb x y : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hy : (A + ΔA) *ᵥ y = b + Δb) {ε : ℝ} (hΔA : lpOpNorm p ΔA ≤ ε * lpOpNorm p A)
    (hΔb : ‖WithLp.toLp p Δb‖ ≤ ε * ‖WithLp.toLp p b‖) (hr : ε * condNumberLp p A < 1) :
    ‖WithLp.toLp p (y - x)‖ / ‖WithLp.toLp p x‖ ≤
      2 * ε / (1 - ε * condNumberLp p A) * condNumberLp p A := by
  have h := relative_error_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p ΔA)
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p Δb) (x := WithLp.toLp p x)
    (y := WithLp.toLp p y) (by simp [hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp, hy, WithLp.toLp_add])
    (by rw [coe_lpEquiv]; exact hΔA) hΔb (by rwa [condNumber_coe_lpEquiv]) (by simpa using hb)
  rwa [condNumber_coe_lpEquiv, ← WithLp.toLp_sub] at h

/-! ### §2.6.5 More refined bounds -/

/-- **§2.6.5, the Skeel condition number** `‖|A⁻¹| |A|‖_∞` (the backbone's `Matrix.skeelCond A`)
is at most `κ_∞(A)`. -/
theorem skeelCond_eq_and_le_condNumberLp (A : Matrix (Fin n) (Fin n) ℝ) :
    skeelCond A = lpOpNorm ∞ (A⁻¹.abs * A.abs) ∧ skeelCond A ≤ condNumberLp ∞ A :=
  ⟨(lpOpNorm_top _).symm, skeelCond_le_condNumberLp_top A⟩

/-- **Theorem 2.6.3, (2.6.12).** Suppose `Ax = b` with `A` nonsingular and `b ≠ 0`,
`(A + ΔA) y = b + Δb`, `|ΔA| ≤ ε |A|` and `|Δb| ≤ ε |b|`. If `ε κ_∞(A) = r < 1`, then `A + ΔA` is
nonsingular and `‖y - x‖_∞ / ‖x‖_∞ ≤ 2ε / (1 - r) · ‖|A⁻¹| |A|‖_∞`. -/
theorem theorem_2_6_3 {A ΔA : Matrix (Fin n) (Fin n) ℝ} {b Δb x y : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hy : (A + ΔA) *ᵥ y = b + Δb) {ε : ℝ}
    (hΔA : ΔA.abs ≤ₑ ε • A.abs) (hΔb : |Δb| ≤ ε • |b|) (hr : ε * condNumberLp ∞ A < 1) :
    IsUnit (A + ΔA) ∧
      ‖WithLp.toLp ∞ (y - x)‖ / ‖WithLp.toLp ∞ x‖ ≤
        2 * ε / (1 - ε * condNumberLp ∞ A) * lpOpNorm ∞ (A⁻¹.abs * A.abs) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
  have hε0 : 0 ≤ ε := by
    have h := hΔb i
    simp only [Pi.abs_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h hi
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg (abs_pos.2 hi)
    linarith [abs_nonneg (Δb i)]
  have hΔA' : lpOpNorm ∞ ΔA ≤ ε * lpOpNorm ∞ A := by
    rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_mul_of_abs_entrywiseLE hε0 hΔA
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have hsk := skeelCond_le_condNumberLp_top A
  have hsmall : ε * skeelCond A < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsk hε0) hr
  refine ⟨isUnit_add_of_lpOpNorm_le ∞ hA hΔA' hr, ?_⟩
  have hsk0 : 0 ≤ skeelCond A := by
    rw [(skeelCond_eq_and_le_condNumberLp A).1]
    exact lpOpNorm_nonneg _ _
  have h := (norm_sub_le_of_abs_le_abs hA hx hy hε0 hΔA hΔb hsmall hx0).2
  rw [PiLp.norm_toLp, PiLp.norm_toLp, ← (skeelCond_eq_and_le_condNumberLp A).1]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hsk0)
  refine div_le_div_of_nonneg_left (by positivity) (by linarith) ?_
  linarith [mul_le_mul_of_nonneg_left hsk hε0]

/-- **(2.6.13), Oettli–Prager.** For given `A`, `b`, `x̂`, `E`, `f`, a perturbation
`(A + ΔA) x̂ = b + Δb` with `|ΔA| ≤ ω |E|`, `|Δb| ≤ ω |f|` exists exactly when
`|b - A x̂| ≤ ω (|E| |x̂| + |f|)`; the smallest such `ω ≥ 0` is
`ω_min = max_i |A x̂ - b|_i / (|E| |x̂| + |f|)_i` (`Matrix.componentwiseBackwardError`) when every
row with `(|E| |x̂| + |f|)_i = 0` has zero residual, and otherwise no `ω` exists (the book's
`ω_min = ∞`); if `A x̂ = b`, then `ω_min = 0`. -/
theorem equation_2_6_13 (A E : Matrix (Fin n) (Fin n) ℝ) (b f x : Fin n → ℝ) :
    (∀ ω : ℝ, 0 ≤ ω →
      ((∃ (ΔA : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ), (A + ΔA) *ᵥ x = b + Δb ∧
          ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|) ↔
        |b - A *ᵥ x| ≤ ω • (E.abs *ᵥ |x| + |f|))) ∧
    ((∀ i, (E.abs *ᵥ |x| + |f|) i = 0 → (b - A *ᵥ x) i = 0) →
      IsLeast {ω : ℝ | 0 ≤ ω ∧ ∃ (ΔA : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ),
          (A + ΔA) *ᵥ x = b + Δb ∧ ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|}
        (componentwiseBackwardError A E b f x)) ∧
    ((∃ i, (E.abs *ᵥ |x| + |f|) i = 0 ∧ (b - A *ᵥ x) i ≠ 0) →
      ¬ ∃ ω : ℝ, 0 ≤ ω ∧ ∃ (ΔA : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ),
          (A + ΔA) *ᵥ x = b + Δb ∧ ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|) ∧
    (A *ᵥ x = b → componentwiseBackwardError A E b f x = 0) := by
  refine ⟨fun ω hω => exists_perturbation_iff_abs_residual_le A E b f x hω,
    isLeast_componentwiseBackwardError A E b f x, ?_, fun hx => ?_⟩
  · rintro ⟨i, hs, hr⟩ ⟨ω, hω, hex⟩
    have h := (exists_perturbation_iff_abs_residual_le A E b f x hω).1 hex i
    simp only [Pi.abs_apply, Pi.smul_apply, smul_eq_mul, hs, mul_zero] at h
    exact hr (abs_nonpos_iff.1 h)
  · simp [componentwiseBackwardError, hx]

end GolubVanLoan.Chapter02
