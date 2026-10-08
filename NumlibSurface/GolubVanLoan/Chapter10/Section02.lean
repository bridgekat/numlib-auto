import Numlib.Approximation.GaussLobatto
import Numlib.Krylov.Quadrature
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub–Van Loan §10.2: Lanczos, quadrature, and approximation

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.2:
`uᵀ f(A) u` as a Stieltjes integral against the spectral weight (10.2.2)–(10.2.6), the four
Gauss-type rules (10.2.7)–(10.2.10) with their remainders and the two-sided bound for `1/λ²`,
Facts 1–2 on orthogonal polynomials and Jacobi matrices, the Lanczos polynomials (10.2.13), the
Gauss rule computed by Lanczos (Fact 3 with (10.2.11)–(10.2.12)), the Gauss–Radau modification of
§10.2.5 and the framework of §10.2.6.

## Conventions

The chapter's (`GolubVanLoan.Chapter10.Section01`). A Riemann–Stieltjes integral `∫_a^b f dw` is
read as the Lebesgue–Stieltjes integral against `StieltjesFunction.measure` (for the continuous
integrands of the section they agree). A *general* weight `w` on `[a, b]` is a measure `μ` with
`OrthogonalPolynomial.IsWeight μ` (every moment finite, infinite support, so every Gauss rule
exists) carried by `Icc a b` (`μ (Icc a b)ᶜ = 0`); the *spectral* weight (10.2.5) is finitely
supported, and its rules exist only up to the grade of `u`, which is why the Lanczos statements
carry `dim 𝒦(A, u, k) = k`. A quadrature rule is a pair of families `t` (nodes) and `w` (weights)
indexed by `Fin k`, and exactness to degree `d` is `Quadrature.IsExactOnMeasure μ w t d`. The
Lanczos quantities are those of `toEuclideanLin A` from `u`: `T_k = Lanczos.tridiag _ u k`, with
the orthonormal eigenvectors `s_j` and eigenvalues `θ_j` of `Lanczos.tridiag_isHermitian`
(`0`-based: the book's `s_{1j}` is `s_j 0`); the Lanczos polynomials are `Lanczos.poly`, normalized
by `p_0 = 1/‖u‖`, so that `q_{j+1} = p_j(A) u`.

## Not formalized

The Riemann–Stieltjes sums of §10.2.1, the Golub–Welsch weight formula of Fact 3 for a general
weight (the book uses Fact 3 only through §10.2.4), numerical remarks.
-/

open MeasureTheory Polynomial Matrix Krylov Quadrature OrthogonalPolynomial
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

/-! ### Errors from residuals (§10.2, introduction) -/

/-- **The error from the residual** (§10.2, the display before §10.2.1): for a symmetric positive
definite `A`, `x* = A⁻¹ b` and `r = b − A x̂`, `‖x* − x̂‖₂² = rᵀ f(A) r` with `f(λ) = 1/λ²`,
`f(A) = cfc f A` — so the error norm is a quadratic form `uᵀ f(A) u` of the kind §10.2 estimates.
Mathlib's `cfc_inv` and `cfc_pow_id`: `f(A) = (A²)⁻¹ = A⁻¹ A⁻¹`. -/
theorem norm_error_sq_eq_residual {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x : Fin n → ℝ) :
    (A⁻¹ *ᵥ b - x) ⬝ᵥ (A⁻¹ *ᵥ b - x) =
      (b - A *ᵥ x) ⬝ᵥ (cfc (fun t : ℝ => (t ^ 2)⁻¹) A *ᵥ (b - A *ᵥ x)) := by
  have hU : IsUnit A := hA.isUnit
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hU
  have e1 : A⁻¹ *ᵥ b - x = A⁻¹ *ᵥ (b - A *ᵥ x) := by
    rw [mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]
  have h0 : ∀ t ∈ spectrum ℝ A, t ^ 2 ≠ 0 := fun t ht =>
    pow_ne_zero 2 fun h => spectrum.zero_notMem ℝ hU (h ▸ ht)
  have hcfc : cfc (fun t : ℝ => (t ^ 2)⁻¹) A = A⁻¹ * A⁻¹ := by
    have h1 : cfc (fun t : ℝ => (t ^ 2)⁻¹) A = Ring.inverse (cfc (fun t : ℝ => t ^ 2) A) :=
      cfc_inv (fun t : ℝ => t ^ 2) A h0 (ha := hA.1)
    have h2 : cfc (fun t : ℝ => t ^ 2) A = A ^ 2 := cfc_pow_id A 2 (ha := hA.1)
    rw [h1, h2, sq,
      Ring.inverse_mul (Or.inl hU), ← nonsing_inv_eq_ringInverse]
  have hsym : A⁻¹ᵀ = A⁻¹ := by
    rw [transpose_nonsing_inv, ← conjTranspose_eq_transpose_of_trivial, hA.1]
  rw [e1, hcfc, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hsym]
  exact dotProduct_comm _ _

/-! ### Gauss-type rules for a weight (§10.2.2) -/

section Rules

variable {μ : Measure ℝ}

/-- **(10.2.7), the Gauss rule**: for a weight `μ` and `k`, there are distinct nodes `t_1, …, t_k`
and positive weights `w_1, …, w_k` with `∫ p dμ = ∑ w_i p(t_i)` for every polynomial of degree at
most `2k − 1`. Backbone `Quadrature.exists_gauss`. -/
theorem equation_10_2_7 (hw : IsWeight μ) (k : ℕ) :
    ∃ t w : Fin k → ℝ, Function.Injective t ∧ (∀ i, 0 < w i) ∧
      ∀ p : ℝ[X], p.degree < ((2 * k : ℕ) : WithBot ℕ) →
        ∫ x, p.eval x ∂μ = ∑ i, w i * p.eval (t i) := by
  obtain ⟨t, w, ht, hpos, hex⟩ := exists_gauss hw k
  exact ⟨t, w, ht, hpos, fun p hp => (hex p hp).symm⟩

/-- **(10.2.8), the Gauss–Radau(a) rule**: for a weight `μ` carried by `[a, b]` and `k`, there are
distinct nodes `t_0 = a` and `t_1, …, t_k ∈ (a, b]` and positive weights with
`∫ p dμ = w_a p(a) + ∑ w_i p(t_i)` for every polynomial of degree at most `2k`. Backbone
`Quadrature.exists_gaussRadau` (the prescribed node first). -/
theorem equation_10_2_8 (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) (k : ℕ) :
    ∃ t w : Fin (k + 1) → ℝ, Function.Injective t ∧ t 0 = a ∧
      (∀ i, i ≠ 0 → t i ∈ Set.Ioc a b) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w t (2 * k) := by
  obtain ⟨t, w, ht, h0, hmem, hpos, hex, -⟩ := exists_gaussRadau hw hsupp k
  refine ⟨t, w, ht, h0, fun i hi => ⟨lt_of_le_of_ne (hmem i).1 ?_, (hmem i).2⟩, hpos, hex⟩
  intro h
  exact hi (ht (h0.trans h).symm)

/-- **(10.2.9), the Gauss–Radau(b) rule**: the same with the prescribed node `b`: distinct nodes
`t_0 = b` and `t_1, …, t_k ∈ [a, b)`, positive weights, exact to degree `2k`. Backbone
`Quadrature.exists_gaussRadau_right` (the rule of (10.2.8) for the reflected weight, transported
back). -/
theorem equation_10_2_9 (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) (k : ℕ) :
    ∃ t w : Fin (k + 1) → ℝ, Function.Injective t ∧ t 0 = b ∧
      (∀ i, i ≠ 0 → t i ∈ Set.Ico a b) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w t (2 * k) := by
  obtain ⟨t, w, ht, h0, hmem, hpos, hex⟩ := exists_gaussRadau_right hw hsupp k
  refine ⟨t, w, ht, h0, fun i hi => ⟨(hmem i).1, lt_of_le_of_ne (hmem i).2 ?_⟩, hpos, hex⟩
  intro h
  exact hi (ht (h.trans h0.symm))

/-- **(10.2.10), the Gauss–Lobatto rule**: for a weight carried by `[a, b]`, `a < b`, and `k`,
there are distinct nodes `t_0 = a`, `t_{k+1} = b` and `k` interior nodes in `[a, b]`, and positive
weights, with the rule exact to degree `2k + 1`. Backbone `Quadrature.exists_gaussLobatto` on
`[−1, 1]` (with `n = k + 1`) for the image of `μ` under the affine map `[a, b] → [−1, 1]`,
transported back (`Quadrature.isExactOnMeasure_map_affine`). -/
theorem equation_10_2_10 (hw : IsWeight μ) {a b : ℝ} (hab : a < b)
    (hsupp : μ (Set.Icc a b)ᶜ = 0) (k : ℕ) :
    ∃ t w : Fin (k + 2) → ℝ, Function.Injective t ∧ t 0 = a ∧ t (Fin.last (k + 1)) = b ∧
      (∀ i, t i ∈ Set.Icc a b) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w t (2 * k + 1) := by
  have hba : 0 < b - a := sub_pos.2 hab
  set c : ℝ := 2 / (b - a) with hc
  set d : ℝ := -(a + b) / (b - a) with hd
  have hc0 : c ≠ 0 := by positivity
  have hν := hw.map_affine hc0 d
  have hsupp' : (μ.map fun t => c * t + d) (Set.Icc (-1) 1)ᶜ = 0 := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    refine measure_mono_null (fun x hx => ?_) hsupp
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc] at hx ⊢
    intro hxab
    apply hx
    have e : c * x + d = (2 * x - a - b) / (b - a) := by
      rw [hc, hd]; field_simp; ring
    rw [e, le_div_iff₀ hba, div_le_iff₀ hba]
    constructor <;> nlinarith [hxab.1, hxab.2]
  obtain ⟨x, w, hx, h0, hl, hmem, hpos, hex, -⟩ :=
    exists_gaussLobatto hν hsupp' (n := k + 1) (by omega)
  set c' : ℝ := (b - a) / 2
  set d' : ℝ := (a + b) / 2
  have hcomp : ∀ t : ℝ, c' * (c * t + d) + d' = t := fun t => by
    rw [hc, hd]; field_simp; ring
  have hmap : (μ.map fun t => c * t + d).map (fun t => c' * t + d') = μ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    convert Measure.map_id using 2
    funext t
    exact hcomp t
  have hex' := isExactOnMeasure_map_affine hex c' d'
  rw [hmap, show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hex'
  have hc'0 : 0 < c' := by positivity
  refine ⟨(fun t => c' * t + d') ∘ x, w, fun i j hij => hx ?_, ?_, ?_, fun i => ?_, hpos, hex'⟩
  · have := mul_left_cancel₀ hc'0.ne' (add_right_cancel hij)
    exact this
  · simp only [Function.comp_apply, h0]; ring
  · simp only [Function.comp_apply, hl]; ring
  · obtain ⟨h1, h2⟩ := hmem i
    have e : c' * x i + d' = a + (b - a) * ((x i + 1) / 2) := by
      simp only [c', d']; ring
    simp only [Function.comp_apply, Set.mem_Icc, e]
    have hx0 : 0 ≤ (x i + 1) / 2 := by linarith
    have hx1 : (x i + 1) / 2 ≤ 1 := by linarith
    constructor
    · nlinarith [mul_nonneg hba.le hx0]
    · nlinarith [mul_le_of_le_one_right hba.le hx1]

end Rules

/-! ### Remainders (§10.2.2) -/

section Remainders

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- **The remainder of the Gauss rule** (§10.2.2, `R_G`): for a rule with `k ≥ 1` distinct nodes
in `[a, b]`, exact to degree `2k − 1` (the rule of (10.2.7)), and `f` of class `C^{2k}`,
`∫ f dμ − I_G(f) = f^{(2k)}(η)/(2k)! ∫ ∏_i (λ − t_i)² dμ` for some `η ∈ [a, b]` (the book prints
`(2n)!`; the rule has `k` nodes). No positivity of `μ` is used. Backbone
`Quadrature.exists_error_eq_of_hermite` with every node doubled. -/
theorem gauss_remainder (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} (hk : 1 ≤ k) {t w : Fin k → ℝ}
    (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b)
    (hex : IsExactOnMeasure μ w t (2 * k - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, (∫ x, f x ∂μ) - ∑ i, w i * f (t i) =
      iteratedDeriv (2 * k) f η / (2 * k).factorial * ∫ x, ∏ i, (x - t i) ^ 2 ∂μ := by
  have hN : 2 * k - 1 + 1 = 2 * k := by omega
  have hsum : ∑ _i : Fin k, (1 + 1) = 2 * k - 1 + 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hf' : ContDiff ℝ ((2 * k - 1 + 1 : ℕ) : WithTop ℕ∞) f := by rwa [hN]
  obtain ⟨η, hη, he⟩ := exists_error_eq_of_hermite hsupp ht hmem hsum
    (Or.inl fun x _ => by
      simp only [Hermite.nodal, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      exact Finset.prod_nonneg fun i _ => Even.pow_nonneg ⟨1, rfl⟩ _) hex hf'
  refine ⟨η, hη, ?_⟩
  rw [he, hN]
  simp [Hermite.nodal, eval_prod]

/-- The nodal polynomial of a rule whose first node is simple and the others double. -/
private theorem eval_nodal_radau {k : ℕ} (t : Fin (k + 1) → ℝ) (x : ℝ) :
    (Hermite.nodal t (Fin.cases 0 fun _ => 1)).eval x =
      (x - t 0) * ∏ i : Fin k, (x - t i.succ) ^ 2 := by
  simp [Hermite.nodal, eval_prod, Fin.prod_univ_succ]

/-- **The remainders of the Gauss–Radau rules** (§10.2.2, `R_{GR(a)}` and `R_{GR(b)}`): for a rule
with `k + 1` distinct nodes in `[a, b]`, the first of them `a` (resp. `b`), exact to degree `2k`
(the rules of (10.2.8)–(10.2.9)), and `f` of class `C^{2k+1}`,
`∫ f dμ − I_{GR}(f) = f^{(2k+1)}(η)/(2k+1)! ∫ (λ − t_0) ∏_{i ≥ 1} (λ − t_i)² dμ` for some
`η ∈ [a, b]`, `t_0` being `a` (resp. `b`); the nodal polynomial has constant sign on `[a, b]`.
The book has `a < η < b`; the closed interval is what the backbone's mean value argument gives.
Backbone `Quadrature.exists_error_eq_of_hermite` (multiplicity one at the prescribed node, two
elsewhere). -/
theorem gaussRadau_remainder (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} {t w : Fin (k + 1) → ℝ}
    (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b) (h0 : t 0 = a ∨ t 0 = b)
    (hex : IsExactOnMeasure μ w t (2 * k)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, (∫ x, f x ∂μ) - ∑ i, w i * f (t i) =
      iteratedDeriv (2 * k + 1) f η / (2 * k + 1).factorial *
        ∫ x, (x - t 0) * ∏ i : Fin k, (x - t i.succ) ^ 2 ∂μ := by
  have hsum : ∑ i : Fin (k + 1), ((Fin.cases 0 fun _ => 1 : Fin (k + 1) → ℕ) i + 1) =
      2 * k + 1 := by
    rw [Fin.sum_univ_succ]
    simp [mul_comm]
    ring
  have hsign : (∀ x ∈ Set.Icc a b, 0 ≤ (Hermite.nodal t (Fin.cases 0 fun _ => 1)).eval x) ∨
      ∀ x ∈ Set.Icc a b, (Hermite.nodal t (Fin.cases 0 fun _ => 1)).eval x ≤ 0 := by
    have hp : ∀ x, 0 ≤ ∏ i : Fin k, (x - t i.succ) ^ 2 :=
      fun x => Finset.prod_nonneg fun i _ => by positivity
    rcases h0 with h0 | h0
    · refine Or.inl fun x hx => ?_
      rw [eval_nodal_radau, h0]
      exact mul_nonneg (by linarith [hx.1]) (hp x)
    · refine Or.inr fun x hx => ?_
      rw [eval_nodal_radau, h0]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (hp x)
  obtain ⟨η, hη, he⟩ := exists_error_eq_of_hermite hsupp ht hmem hsum hsign hex hf
  refine ⟨η, hη, ?_⟩
  rw [he]
  simp only [eval_nodal_radau]

/-- The nodal polynomial of a rule whose two end nodes are simple and the others double. -/
private theorem eval_nodal_lobatto {k : ℕ} (t : Fin (k + 2) → ℝ) (x : ℝ) :
    (Hermite.nodal t (Fin.cases 0 (Fin.lastCases 0 fun _ => 1))).eval x =
      (x - t 0) * (x - t (Fin.last (k + 1))) * ∏ i : Fin k, (x - t i.castSucc.succ) ^ 2 := by
  simp only [Hermite.nodal, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc,
    zero_add, pow_one]
  rw [Fin.succ_last]
  ring

/-- **The remainder of the Gauss–Lobatto rule** (§10.2.2, `R_{GL}`, printed `R_{GG}` in the list):
for a rule with `k + 2` distinct nodes in `[a, b]`, the first `a` and the last `b`, exact to degree
`2k + 1` (the rule of (10.2.10)), and `f` of class `C^{2k+2}`,
`∫ f dμ − I_{GL}(f) = f^{(2k+2)}(η)/(2k+2)! ∫ (λ − a)(λ − b) ∏ (λ − t_i)² dμ` over the interior
nodes, for some `η ∈ [a, b]` (the book has `a < η < b`; the closed interval is what the
backbone's mean value argument gives). Backbone `Quadrature.exists_error_eq_of_hermite`
(multiplicity one at both ends). -/
theorem gaussLobatto_remainder (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} {t w : Fin (k + 2) → ℝ}
    (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b) (h0 : t 0 = a)
    (hl : t (Fin.last (k + 1)) = b) (hex : IsExactOnMeasure μ w t (2 * k + 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k + 1 + 1 : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, (∫ x, f x ∂μ) - ∑ i, w i * f (t i) =
      iteratedDeriv (2 * k + 2) f η / (2 * k + 2).factorial *
        ∫ x, (x - a) * (x - b) * ∏ i : Fin k, (x - t i.castSucc.succ) ^ 2 ∂μ := by
  have hsum : ∑ i : Fin (k + 2),
      ((Fin.cases 0 (Fin.lastCases 0 fun _ => 1) : Fin (k + 2) → ℕ) i + 1) = 2 * k + 1 + 1 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc]
    simp [mul_comm]
    ring
  have hsign : (∀ x ∈ Set.Icc a b,
        0 ≤ (Hermite.nodal t (Fin.cases 0 (Fin.lastCases 0 fun _ => 1))).eval x) ∨
      ∀ x ∈ Set.Icc a b,
        (Hermite.nodal t (Fin.cases 0 (Fin.lastCases 0 fun _ => 1))).eval x ≤ 0 := by
    refine Or.inr fun x hx => ?_
    rw [eval_nodal_lobatto, h0, hl]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) (by linarith [hx.2]))
      (Finset.prod_nonneg fun i _ => by positivity)
  obtain ⟨η, hη, he⟩ := exists_error_eq_of_hermite hsupp ht hmem hsum hsign hex hf
  refine ⟨η, hη, ?_⟩
  rw [he]
  simp only [eval_nodal_lobatto, h0, hl]

/-- The derivatives of `λ ↦ λ⁻²`: `f^{(j)}(λ) = (−1)^j (j + 1)! λ^{−2−j}`, positive for even `j`
and negative for odd `j` when `λ > 0`. -/
private theorem iteratedDeriv_inv_sq (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => (y ^ 2)⁻¹) x =
      (∏ i ∈ Finset.range j, ((-2 : ℤ) - i : ℝ)) * x ^ ((-2 : ℤ) - j) := by
  have hf : (fun y : ℝ => (y ^ 2)⁻¹) = fun y => y ^ (-2 : ℤ) := by
    funext y
    rw [_root_.zpow_neg, zpow_ofNat]
  rw [hf, iteratedDeriv_eq_iterate, iter_deriv_zpow]

private theorem prod_neg_two_sub (j : ℕ) :
    ∏ i ∈ Finset.range j, ((-2 : ℤ) - i : ℝ) = (-1) ^ j * ∏ i ∈ Finset.range j, (2 + i : ℝ) := by
  rw [show ((-1 : ℝ)) ^ j = ∏ _i ∈ Finset.range j, (-1 : ℝ) by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast
  ring

/-- **The two-sided bound for `f(λ) = 1/λ²`** (§10.2.2): for `0 < a < b` and a finite measure
carried by `[a, b]`, the Gauss rule of (10.2.7) with `k ≥ 1` nodes and the Gauss–Radau(a) rule of
(10.2.8) with `k + 1` nodes bracket the integral: `I_G(f) ≤ ∫ f dμ ≤ I_{GR(a)}(f)`. The derivatives
of `λ⁻²` alternate in sign on `(0, ∞)`: `f^{(2k)} > 0`, `f^{(2k+1)} < 0`. Backbone
`Quadrature.gauss_le_integral_le_gaussRadau` (rules given by their exactness, nodes in `[a, b]`). -/
theorem gauss_le_integral_le_gaussRadau (ha : 0 < a) (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ}
    (hk : 1 ≤ k) {t w : Fin k → ℝ} (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b)
    (hex : IsExactOnMeasure μ w t (2 * k - 1)) {t' w' : Fin (k + 1) → ℝ}
    (ht' : Function.Injective t') (hmem' : ∀ i, t' i ∈ Set.Icc a b) (h0 : t' 0 = a)
    (hex' : IsExactOnMeasure μ w' t' (2 * k)) :
    ∑ i, w i * (t i ^ 2)⁻¹ ≤ ∫ x, (x ^ 2)⁻¹ ∂μ ∧ ∫ x, (x ^ 2)⁻¹ ∂μ ≤ ∑ i, w' i * (t' i ^ 2)⁻¹ := by
  have hsign : ∀ j : ℕ, ∀ x ∈ Set.Icc a b,
      iteratedDeriv j (fun y : ℝ => (y ^ 2)⁻¹) x =
        (-1) ^ j * ((∏ i ∈ Finset.range j, (2 + i : ℝ)) * x ^ ((-2 : ℤ) - j)) := by
    intro j x _
    rw [iteratedDeriv_inv_sq, prod_neg_two_sub, mul_assoc]
  have hpos : ∀ j : ℕ, ∀ x ∈ Set.Icc a b,
      0 < (∏ i ∈ Finset.range j, (2 + i : ℝ)) * x ^ ((-2 : ℤ) - j) := fun j x hx =>
    mul_pos (Finset.prod_pos fun i _ => by positivity) (zpow_pos (ha.trans_le hx.1) _)
  exact Quadrature.gauss_le_integral_le_gaussRadau (f := fun y : ℝ => (y ^ 2)⁻¹) hsupp hk ht hmem
    hex ht' hmem' h0 hex' isOpen_Ioi
    (fun x hx => ha.trans_le hx.1)
    (((contDiff_id.pow 2).contDiffOn).inv fun x hx => pow_ne_zero 2 (ne_of_gt hx))
    (fun x hx => by
      rw [hsign _ x hx, pow_mul, neg_one_sq, one_pow, one_mul]
      exact (hpos _ x hx).le)
    (fun x hx => by
      rw [hsign _ x hx, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
      exact neg_nonpos.2 (hpos _ x hx).le)

end Remainders

/-! ### The Stieltjes weights (§10.2.1) -/

section Weights

open Filter Topology

/-- The Heaviside Stieltjes function with its jump at `c`: `x ↦ 1` for `c ≤ x`, `0` otherwise
(right-continuous). Its measure is the Dirac mass at `c` (`heavisideStieltjes_measure`). -/
noncomputable def heavisideStieltjes (c : ℝ) : StieltjesFunction ℝ where
  toFun x := if c ≤ x then 1 else 0
  mono' x y hxy := by
    dsimp only
    split_ifs with h1 h2 <;> first | exact absurd (h1.trans hxy) h2 | exact le_rfl | norm_num
  right_continuous' x := by
    by_cases hx : c ≤ x
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr (fun y hy => ?_) ?_
      · simp only [ite_eq_left (hx.trans hy)]
      · simp only [ite_eq_left hx]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Iio_mem_nhds (not_le.1 hx))] with y hy
        simp only [ite_eq_right (not_le.2 hy)]
      · simp only [ite_eq_right hx]

/-- The Stieltjes measure of the unit step at `c` is the Dirac mass at `c`. -/
theorem heavisideStieltjes_measure (c : ℝ) :
    (heavisideStieltjes c).measure = Measure.dirac c := by
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  rw [StieltjesFunction.measure_Ioc, Measure.dirac_apply' _ measurableSet_Ioc]
  change ENNReal.ofReal ((if c ≤ b then 1 else 0) - if c ≤ a then 1 else 0) = _
  by_cases h1 : c ≤ a
  · rw [ite_eq_left (h1.trans hab.le), ite_eq_left h1, sub_self, ENNReal.ofReal_zero,
      Set.indicator_of_notMem (fun h => not_lt.2 h1 h.1)]
  · by_cases h2 : c ≤ b
    · rw [ite_eq_left h2, ite_eq_right h1, sub_zero, ENNReal.ofReal_one,
        Set.indicator_of_mem (show c ∈ Set.Ioc a b from ⟨not_le.1 h1, h2⟩)]
      rfl
    · rw [ite_eq_right h2, ite_eq_right h1, sub_self, ENNReal.ofReal_zero,
        Set.indicator_of_notMem (fun h => h2 h.2)]

private theorem measure_finset_sum {ι : Type*} (s : Finset ι) (g : ι → StieltjesFunction ℝ) :
    (∑ i ∈ s, g i).measure = ∑ i ∈ s, (g i).measure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [StieltjesFunction.measure_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, StieltjesFunction.measure_add, ih]

/-- A finite nonnegative combination of Heaviside functions has the corresponding combination of
Dirac masses as its measure. -/
private theorem measure_sum_smul_heaviside {ι : Type*} [Fintype ι] (c : ι → ℝ) (lam : ι → ℝ)
    (d : ℝ) :
    (StieltjesFunction.const ℝ d +
        ∑ i, (c i).toNNReal • heavisideStieltjes (lam i)).measure =
      ∑ i, ENNReal.ofReal (c i) • Measure.dirac (lam i) := by
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_const, zero_add,
    measure_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [StieltjesFunction.measure_smul, heavisideStieltjes_measure]
  rfl

/-- The integral of `f` against `∑ c_i δ_{λ_i}` with `c_i ≥ 0`. -/
private theorem integral_sum_smul_dirac {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (lam : ι → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(∑ i, ENNReal.ofReal (c i) • Measure.dirac (lam i)) = ∑ i, c i * f (lam i) := by
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure (by simp)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc i), smul_eq_mul]

/-- **(10.2.2), the step weight**: for `λ_n < ⋯ < λ_1` (`0`-based, `λ 0` the largest) and
`w_1 ≥ ⋯ ≥ w_{n+1} ≥ 0` (`w : Fin (n + 2) → ℝ`), the right-continuous step function with value
`w_{n+1}` below `λ_n`, `w_μ` on `[λ_μ, λ_{μ−1})` and `w_1` from `λ_1` on:
`w_{n+1} + ∑_μ (w_μ − w_{μ+1}) 𝟙[λ_μ, ∞)`. -/
noncomputable def stepWeight {n : ℕ} (lam : Fin (n + 1) → ℝ) (w : Fin (n + 2) → ℝ) :
    StieltjesFunction ℝ :=
  StieltjesFunction.const ℝ (w (Fin.last (n + 1))) +
    ∑ i, (w i.castSucc - w i.succ).toNNReal • heavisideStieltjes (lam i)

/-- **(10.2.3)**: `∫_a^b f dw = ∑_μ (w_μ − w_{μ+1}) f(λ_μ)` with `a = λ_n`, `b = λ_1`, for every
`f`: the measure of the step weight is `∑_μ (w_μ − w_{μ+1}) δ_{λ_μ}`
(`StieltjesFunction.measure_Ioc` on the jumps), all of whose atoms lie in `[a, b]`. -/
theorem equation_10_2_3 {n : ℕ} {lam : Fin (n + 1) → ℝ} (hlam : StrictAnti lam)
    {w : Fin (n + 2) → ℝ} (hw : Antitone w) (f : ℝ → ℝ) :
    ∫ x in Set.Icc (lam (Fin.last n)) (lam 0), f x ∂(stepWeight lam w).measure =
      ∑ i, (w i.castSucc - w i.succ) * f (lam i) := by
  have hc : ∀ i : Fin (n + 1), 0 ≤ w i.castSucc - w i.succ :=
    fun i => sub_nonneg.2 (hw Fin.castSucc_lt_succ.le)
  rw [stepWeight, measure_sum_smul_heaviside]
  have hmem : ∀ i, lam i ∈ Set.Icc (lam (Fin.last n)) (lam 0) :=
    fun i => ⟨hlam.antitone (Fin.le_last i), hlam.antitone (Fin.zero_le i)⟩
  have hres : (∑ i, ENNReal.ofReal (w i.castSucc - w i.succ) • Measure.dirac (lam i)).restrict
      (Set.Icc (lam (Fin.last n)) (lam 0)) =
      ∑ i, ENNReal.ofReal (w i.castSucc - w i.succ) • Measure.dirac (lam i) := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.smul_apply,
      show {x : ℝ | ¬x ∈ Set.Icc (lam (Fin.last n)) (lam 0)} =
        (Set.Icc (lam (Fin.last n)) (lam 0))ᶜ from rfl,
      Measure.dirac_apply' _ (MeasurableSet.compl measurableSet_Icc),
      Set.indicator_of_notMem (by simpa using hmem i), smul_zero]
  rw [hres, integral_sum_smul_dirac hc]

end Weights

/-! ### Orthogonal polynomials and Jacobi matrices (§10.2.3) -/

section Facts

variable {μ : Measure ℝ}

/-- **Fact 1** (§10.2.3): for a weight `μ` there are polynomials `p_0, p_1, …` with `deg p_k = k`
and `∫ p_i p_j dμ = δ_ij` — the backbone's `OrthogonalPolynomial.orthonormalFamily` — satisfying
`γ_k p_k = (λ − ω_k) p_{k−1} − γ_{k−1} p_{k−2}` (`p_{−1} = 0`; the book writes `w_k` for `ω_k`),
here `γ_k = ‖π_k‖/‖π_{k−1}‖` for the monic `π_k` and `ω_k` the backbone's
`OrthogonalPolynomial.alpha`; and they are unique up to a factor `±1`: a polynomial of degree `k`
orthogonal to every polynomial of lower degree with `∫ q² dμ = 1` is `±p_k`. Backbone
`OrthogonalPolynomial.orthonormalFamily_recurrence` and
`OrthogonalPolynomial.eq_orthonormalFamily_or_eq_neg`. -/
theorem orthonormalPolynomials_threeTerm (hw : IsWeight μ) :
    (∀ k, (orthonormalFamily μ k).degree = k) ∧
    (∀ i j, ∫ x, (orthonormalFamily μ i).eval x * (orthonormalFamily μ j).eval x ∂μ =
      if i = j then 1 else 0) ∧
    C (normOf μ 1 / normOf μ 0) * orthonormalFamily μ 1 =
      (X - C (OrthogonalPolynomial.alpha μ 0)) * orthonormalFamily μ 0 ∧
    (∀ k, C (normOf μ (k + 2) / normOf μ (k + 1)) * orthonormalFamily μ (k + 2) =
      (X - C (OrthogonalPolynomial.alpha μ (k + 1))) * orthonormalFamily μ (k + 1) -
        C (normOf μ (k + 1) / normOf μ k) * orthonormalFamily μ k) ∧
    (∀ (k : ℕ) (q : ℝ[X]), q.degree = k →
      (∀ r : ℝ[X], r.degree < k → ∫ x, q.eval x * r.eval x ∂μ = 0) →
      ∫ x, q.eval x ^ 2 ∂μ = 1 → q = orthonormalFamily μ k ∨ q = -orthonormalFamily μ k) := by
  have hN : ∀ k, normOf μ k ≠ 0 := fun k => (normOf_pos hw k).ne'
  refine ⟨degree_orthonormalFamily hw, fun i j => ?_, ?_, fun k => ?_, fun k q hq horth hq1 => ?_⟩
  · split_ifs with h
    · subst h
      simpa [sq] using integral_orthonormalFamily_sq hw i
    · exact integral_orthonormalFamily_mul hw h
  · apply Polynomial.funext
    intro x
    simp only [orthonormalFamily, family_one, family_zero, eval_mul, eval_C, eval_sub, eval_X,
      eval_one]
    field_simp [hN 0, hN 1]
  · apply Polynomial.funext
    intro x
    have h := congrArg (eval x) (orthonormalFamily_recurrence hw k)
    simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X] at h ⊢
    rw [h]
    simp only [cdA, cdB, cdC, show k + 1 - 1 = k by omega]
    field_simp [hN k, hN (k + 1), hN (k + 2)]
    ring
  · exact eq_orthonormalFamily_or_eq_neg hw hq horth hq1

/-- **Fact 2** (§10.2.3): the zeros of `p_k` are the eigenvalues of the Jacobi matrix `T_k`
(diagonal `ω_i`, off-diagonal `γ_i`), and they are distinct: both root multisets are the image of
one injective family. Backbone `OrthogonalPolynomial.charpoly_jacobiMatrix` (the characteristic
polynomial is the monic `π_k`) and `OrthogonalPolynomial.exists_injective_family_eq_prod` — the
book's appeal to Theorem 8.4.1 is replaced by the orthogonal-polynomial argument. -/
theorem roots_orthonormalPolynomial_eq_eigenvalues (hw : IsWeight μ) (k : ℕ) :
    ∃ x : Fin k → ℝ, Function.Injective x ∧
      (orthonormalFamily μ k).roots = Finset.univ.val.map x ∧
      (jacobiMatrix μ k).charpoly.roots = Finset.univ.val.map x := by
  obtain ⟨x, hx, hprod⟩ := exists_injective_family_eq_prod hw k
  have hroots : (family μ k).roots = Finset.univ.val.map x := by
    rw [hprod, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun i _ => X_sub_C_ne_zero (x i))]
    simp [roots_X_sub_C]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [orthonormalFamily, roots_C_mul _ (inv_ne_zero (normOf_pos hw k).ne'), hroots]
  · rw [charpoly_jacobiMatrix hw, hroots]

end Facts

/-! ### The spectral weight and the Lanczos rules (§10.2.1, §10.2.4–10.2.6) -/

section Lanczos

open Lanczos

variable {n : ℕ}

/-- **(10.2.5), the spectral weight** of a symmetric `A = X Λ Xᵀ` (10.2.4) and a vector `u`:
`w(λ) = ∑_{i : λ_i ≤ λ} [Xᵀu]_i²`, the right-continuous step function whose jumps are the squared
components of `u` along the orthonormal eigenvectors. For distinct eigenvalues it is the step
weight (10.2.2) with the book's `w_μ = [Xᵀu]_μ² + ⋯ + [Xᵀu]_n²`; this formulation needs no
distinctness. Its measure is the backbone's `Krylov.spectralMeasure` (`spectralWeight_measure`). -/
noncomputable def spectralWeight {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) : StieltjesFunction ℝ :=
  StieltjesFunction.const ℝ 0 +
    ∑ i, (‖inner ℝ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace i)
        u‖ ^ 2).toNNReal •
      heavisideStieltjes ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace i)

/-- The measure of the spectral weight is the spectral measure `∑_i [Xᵀu]_i² δ_{λ_i}`. -/
theorem spectralWeight_measure {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) :
    (spectralWeight hA u).measure =
      Krylov.spectralMeasure hA.isSymmetric_toEuclideanLin finrank_euclideanSpace u := by
  rw [spectralWeight, measure_sum_smul_heaviside]
  rfl

/-- **(10.2.6)**: for symmetric `A` and every `f`,
`uᵀ f(A) u = ∑_μ [Xᵀu]_μ² f(λ_μ) = ∫ f dw` with `w` the spectral weight, `f(A) = cfc f A`.
Backbone `Matrix.IsHermitian.inner_cfc_eq_integral_spectralMeasure`. -/
theorem equation_10_2_6 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) (f : ℝ → ℝ) :
    u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) =
        ∑ i, inner ℝ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace i)
            u ^ 2 * f ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace i) ∧
      u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) = ∫ x, f x ∂(spectralWeight hA u).measure := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  have h := hH.inner_cfc_eq_integral_spectralMeasure f u.ofLp
  simp only [star_trivial, WithLp.toLp_ofLp, RCLike.ofReal_real_eq_id, id] at h
  have h2 : u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) = ∫ x, f x ∂(spectralWeight hA u).measure := by
    rw [h, spectralWeight_measure]
  refine ⟨?_, h2⟩
  rw [h2, spectralWeight_measure, Krylov.integral_spectralMeasure]
  simp [Real.norm_eq_abs, sq_abs]

/-- **The Lanczos polynomials** (§10.2.4, (10.2.13)): the Lanczos vectors are polynomials in `A`
applied to `u`, `q_{j+1} = p_j(A) u` with `deg p_j = j` below the grade (`0`-based; the book's
"`q_k = p_k(A) q₁` for some degree-`k` polynomial" is off by one), and
`β_{j+1} p_{j+2}(λ) = (λ − α_{j+1}) p_{j+1}(λ) − β_j p_j(λ)` as long as `β_{j+1} ≠ 0`, with the
first step `β_0 p_1(λ) = (λ − α_0) p_0(λ)` (the book's `β₀q₀ ≡ 0`) when `β_0 ≠ 0` — the book
prints `β²_{k−1}`, which is the recurrence of the *monic* polynomials `det(λ − T_k)`, not of these.
Backbone `Lanczos.poly`, `Lanczos.aeval_poly`, `Lanczos.poly_degree`, `Lanczos.poly_add_two`. -/
theorem equation_10_2_13 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) :
    (∀ j, aeval (toEuclideanLin A) (Lanczos.poly (toEuclideanLin A) u j) u =
      Arnoldi.vec (toEuclideanLin A) u j) ∧
    (∀ j, j < grade (toEuclideanLin A) u → (Lanczos.poly (toEuclideanLin A) u j).degree = j) ∧
    (1 < grade (toEuclideanLin A) u →
      C (Lanczos.beta (toEuclideanLin A) u 0) * Lanczos.poly (toEuclideanLin A) u 1 =
        (X - C (Lanczos.alpha (toEuclideanLin A) u 0)) * Lanczos.poly (toEuclideanLin A) u 0) ∧
    (∀ j, j + 2 < grade (toEuclideanLin A) u →
      C (Lanczos.beta (toEuclideanLin A) u (j + 1)) * Lanczos.poly (toEuclideanLin A) u (j + 2) =
        (X - C (Lanczos.alpha (toEuclideanLin A) u (j + 1))) *
            Lanczos.poly (toEuclideanLin A) u (j + 1) -
          C (Lanczos.beta (toEuclideanLin A) u j) * Lanczos.poly (toEuclideanLin A) u j) := by
  refine ⟨Lanczos.aeval_poly hA.isSymmetric_toEuclideanLin u,
    fun j hj => Lanczos.poly_degree _ u hj, fun hg => ?_, fun j hj => ?_⟩
  · have hβ : Lanczos.beta (toEuclideanLin A) u 0 ≠ 0 := by
      rw [Ne, Lanczos.beta_eq_zero_iff u hA.isSymmetric_toEuclideanLin]
      omega
    rw [Lanczos.poly_one]
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hβ, C_1, one_mul]
  have hβ : Lanczos.beta (toEuclideanLin A) u (j + 1) ≠ 0 := by
    rw [Ne, Lanczos.beta_eq_zero_iff u hA.isSymmetric_toEuclideanLin]
    omega
  rw [Lanczos.poly_add_two]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hβ, C_1, one_mul]

/-- **Orthonormality of the Lanczos polynomials** (§10.2.4, the chain after (10.2.13)):
`∫ p_i p_j dw = q_{i+1}ᵀ q_{j+1} = δ_ij` below the grade, for the spectral weight `w` of `u` — the
Lanczos polynomials, normalized by `p_0 = 1/‖u‖`, are the orthonormal polynomials of `w`. Backbone
`Lanczos.polyInner_poly`, `Krylov.polyInner_eq_integral`. -/
theorem lanczosPolynomials_orthonormal {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {i j : ℕ} (hi : i < grade (toEuclideanLin A) u)
    (hj : j < grade (toEuclideanLin A) u) :
    ∫ x, (Lanczos.poly (toEuclideanLin A) u i).eval x *
        (Lanczos.poly (toEuclideanLin A) u j).eval x ∂(spectralWeight hA u).measure =
      if i = j then 1 else 0 := by
  have h := Krylov.polyInner_eq_integral hA.isSymmetric_toEuclideanLin finrank_euclideanSpace u
    (Lanczos.poly (toEuclideanLin A) u i) (Lanczos.poly (toEuclideanLin A) u j)
  rw [Algebra.algebraMap_self, Polynomial.map_id, Polynomial.map_id,
    Lanczos.polyInner_poly hA.isSymmetric_toEuclideanLin u hi hj] at h
  rw [spectralWeight_measure]
  simpa using h.symm

/-- **Fact 3 with (10.2.11)–(10.2.12), for the spectral weight**: if `1 ≤ k ≤ grade`, `T_k` is the
Lanczos matrix from `u` and `Sᵀ T_k S = diag(θ_1, …, θ_k)`, the Gauss rule of the spectral weight
has nodes `θ_j` and weights `‖u‖² s_{1j}²`: `∫ p dw = ‖u‖² ∑_j s_{1j}² p(θ_j)` for `deg p ≤ 2k − 1`.
The book's weights `s_{1j}²` assume `∫ dw = 1`, i.e. `‖u‖ = 1`. Backbone
`Lanczos.gauss_quadrature`, `Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag`. -/
theorem equation_10_2_12 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk0 : 0 < k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u k) = k) {p : ℝ[X]}
    (hp : p.natDegree < 2 * k) :
    ∫ x, p.eval x ∂(spectralWeight hA u).measure =
      ‖u‖ ^ 2 * ∑ j, ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvectorBasis j
          ⟨0, hk0⟩) ^ 2 * p.eval ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvalues j) := by
  rw [spectralWeight_measure, Lanczos.gauss_quadrature hA.isSymmetric_toEuclideanLin _ u hk0 hk hp,
    Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hA.isSymmetric_toEuclideanLin u
      hk0 hk]

/-- The eigenvalues of `A` in the order of `Matrix.IsHermitian.eigenvalues₀` lie in any interval
containing its spectrum. -/
private theorem eigenvalues_mem_Icc {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {a b : ℝ}
    (hab : spectrum ℝ A ⊆ Set.Icc a b) (i : Fin (Fintype.card (Fin n))) :
    (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace i ∈ Set.Icc a b := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  have h := hab (hH.eigenvalues_mem_spectrum_real ((Fintype.equivOfCardEq (Fintype.card_fin _)) i))
  convert h using 1
  simp [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]

/-- **The Gauss rule via Lanczos** (§10.2.4, Steps 1–3): `σ = ‖u‖² (s_{11}² f(θ_1) + ⋯ + s_{1k}²
f(θ_k))` computed from `k` Lanczos steps is the `k`-point Gauss rule of the spectral weight: exact
on polynomials of degree `≤ 2k − 1` (`equation_10_2_12`), with error `uᵀ f(A) u − σ =
f^{(2k)}(η)/(2k)! ∫ π_k² dw`, `π_k = det(λ I − T_k)`, for `f` of class `C^{2k}` and some `η` in any
interval `[a, b]` containing the spectrum (the book's `[λ_n, λ_1]`). Backbone
`Lanczos.exists_gauss_error_eq`. -/
theorem lanczos_gaussRule {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk0 : 0 < k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u k) = k) {a b : ℝ}
    (hab : spectrum ℝ A ⊆ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) -
        ‖u‖ ^ 2 * ∑ j, ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvectorBasis j
          ⟨0, hk0⟩) ^ 2 * f ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvalues j) =
      iteratedDeriv (2 * k) f η / (2 * k).factorial *
        ∫ x, ((Lanczos.tridiag (toEuclideanLin A) u k).charpoly.eval x) ^ 2
          ∂(spectralWeight hA u).measure := by
  obtain ⟨η, hη, he⟩ := Lanczos.exists_gauss_error_eq hA.isSymmetric_toEuclideanLin
    finrank_euclideanSpace u hk0 hk (eigenvalues_mem_Icc hA hab) hf
  refine ⟨η, hη, ?_⟩
  rw [(equation_10_2_6 hA u f).2, spectralWeight_measure, ← he,
    Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hA.isSymmetric_toEuclideanLin u
      hk0 hk]

/-- The eigenvector `[x; −1]` of the Gauss–Radau matrix: `T̃ [x; −1] = a [x; −1]` with
`x = β_k (T_k − a I)⁻¹ e_k` (`x` empty for `k = 0`). The backbone's
`Lanczos.radauTridiag_hasEigenvalue` builds this vector inside its proof but exports only the
spectral membership; this is its computation, kept local (a candidate for the backbone). -/
private theorem radauTridiag_mulVec_snoc {A : Matrix (Fin n) (Fin n) ℝ}
    (u : EuclideanSpace ℝ (Fin n)) (k : ℕ) {a : ℝ}
    (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det) :
    ∃ x : Fin k → ℝ, Lanczos.radauTridiag (toEuclideanLin A) u k a *ᵥ
        (Fin.snoc x (-1) : Fin (k + 1) → ℝ) = a • (Fin.snoc x (-1) : Fin (k + 1) → ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨Fin.elim0, ?_⟩
    ext i
    fin_cases i
    simp [Lanczos.radauTridiag, Lanczos.radauCorrection, Matrix.mulVec, dotProduct]
  set T := Lanczos.tridiag (toEuclideanLin A) u k
  set R := (T - a • 1)⁻¹
  set β := Lanczos.beta (toEuclideanLin A) u (k - 1)
  have hTRm : T * R = 1 + a • R := by
    have h := Matrix.mul_nonsing_inv _ ha
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
    rw [← h]
    abel
  have hTR : ∀ i j, ∑ l, T i l * R l j = (if i = j then 1 else 0) + a * R i j := by
    intro i j
    have h := congrFun (congrFun hTRm i) j
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul] at h
    exact h
  refine ⟨fun i => β * R i ⟨k - 1, by omega⟩, ?_⟩
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hrow : ∀ j : Fin k,
        Lanczos.radauTridiag (toEuclideanLin A) u k a (Fin.last k) j.castSucc =
        if (j : ℕ) + 1 = k then Lanczos.beta (toEuclideanLin A) u j else 0 := by
      intro j
      rw [Lanczos.radauTridiag_apply_of_ne _ _ _ _ fun h => absurd h.2 (Fin.castSucc_ne_last j),
        Lanczos.tridiag_apply]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hll : Lanczos.radauTridiag (toEuclideanLin A) u k a (Fin.last k) (Fin.last k) =
        a + β ^ 2 * R ⟨k - 1, by omega⟩ ⟨k - 1, by omega⟩ := by
      simp only [Lanczos.radauTridiag, Matrix.of_apply, and_self, ↓reduceIte,
        Lanczos.radauCorrection, hk, ↓reduceDIte]
      rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
      hrow, hll, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
      ring
    · intro j _ hj
      rw [ite_eq_right fun h => hj (Fin.ext (by simp; omega)), zero_mul]
    · simp
  · have hcol :
        Lanczos.radauTridiag (toEuclideanLin A) u k a i.castSucc (Fin.last k) =
        if (i : ℕ) + 1 = k then Lanczos.beta (toEuclideanLin A) u i else 0 := by
      rw [Lanczos.radauTridiag_apply_of_ne _ _ _ _ fun h => absurd h.1 (Fin.castSucc_ne_last i),
        Lanczos.tridiag_apply]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega)]
      by_cases h : (i : ℕ) + 1 = k
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (by omega)]
    have hin : ∀ j : Fin k,
        Lanczos.radauTridiag (toEuclideanLin A) u k a i.castSucc j.castSucc = T i j := fun j => by
      rw [Lanczos.radauTridiag_apply_of_ne _ _ _ _ fun h => absurd h.1 (Fin.castSucc_ne_last i)]
      rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
      hcol, hin, Pi.smul_apply, smul_eq_mul]
    have hs : ∑ j, T i j * (β * R j ⟨k - 1, by omega⟩) =
        β * ((if i = ⟨k - 1, by omega⟩ then 1 else 0) + a * R i ⟨k - 1, by omega⟩) := by
      rw [← hTR, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    by_cases h : (i : ℕ) + 1 = k
    · have hi : i = ⟨k - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [ite_eq_left h, ite_eq_left hi, hi]
      ring
    · have hi : i ≠ ⟨k - 1, by omega⟩ := fun h' => h (by rw [h']; simp; omega)
      rw [ite_eq_right h, ite_eq_right hi]
      ring

/-- **The Gauss–Radau modification** (§10.2.5): with `T̃_{k+1}` equal to `T_{k+1}` except `α̃_{k+1}
= a + β_k² e_kᵀ (T_k − a I)⁻¹ e_k` (the book prints `β_{k+1}²`, and its displayed `T̃_{k+1}` omits
`β_k` above the diagonal), `a` is an eigenvalue of `T̃_{k+1}` whenever `T_k − a I` is nonsingular,
with the eigenvector of the book's derivation: `T̃_{k+1} [x; −1] = a [x; −1]` for some `x ∈ ℝ^k`
(namely `x = β_k (T_k − a I)⁻¹ e_k`). Backbone `Lanczos.radauTridiag_hasEigenvalue`. -/
theorem gaussRadau_tridiag {A : Matrix (Fin n) (Fin n) ℝ} (u : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    {a : ℝ} (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det) :
    a ∈ spectrum ℝ (Lanczos.radauTridiag (toEuclideanLin A) u k a) ∧
      ∃ x : Fin k → ℝ, Lanczos.radauTridiag (toEuclideanLin A) u k a *ᵥ
        (Fin.snoc x (-1) : Fin (k + 1) → ℝ) = a • (Fin.snoc x (-1) : Fin (k + 1) → ℝ) :=
  ⟨Lanczos.radauTridiag_hasEigenvalue (A := toEuclideanLin A) (v := u) (m := k) (a := a) ha,
    radauTridiag_mulVec_snoc u k ha⟩

/-- **The Gauss–Radau rule via Lanczos** (§10.2.5, "Guided by Gauss quadrature theory …"): for
`k + 1 ≤ grade` and `T_k − a I` nonsingular, the rule with the eigenvalues `θ̃_j` of `T̃_{k+1}` as
nodes and `‖u‖²` times the squared first components `s̃_{1j}²` of its eigenvectors as weights has
`a` as a node and integrates every polynomial of degree `≤ 2k` exactly against the spectral weight:
it is the Gauss–Radau(a) rule (10.2.8) of `w`. Backbone `Lanczos.radau_quadrature`. -/
theorem gaussRadau_via_lanczos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u (k + 1)) = k + 1) {a : ℝ}
    (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det) :
    (∃ j, (radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvalues j = a) ∧
      ∀ p : ℝ[X], p.natDegree ≤ 2 * k →
        ∫ x, p.eval x ∂(spectralWeight hA u).measure =
          ‖u‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvectorBasis
              j 0) ^ 2 *
            p.eval ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvalues j) := by
  refine ⟨(Lanczos.radau_quadrature (toEuclideanLin A) u k a hA.isSymmetric_toEuclideanLin
    finrank_euclideanSpace hk ha
    (f := 0) (by simp)).1, fun p hp => ?_⟩
  rw [spectralWeight_measure]
  exact (Lanczos.radau_quadrature (toEuclideanLin A) u k a hA.isSymmetric_toEuclideanLin
    finrank_euclideanSpace hk ha hp).2

/-- **The framework of §10.2.6**: for symmetric `A` with spectrum in `[a, b]` and `f` smooth on an
open set containing `[a, b]` with `f^{(2k)} ≥ 0 ≥ f^{(2k+1)}` there (for instance `f(λ) = 1/λ²`
with `0 < a`), the Lanczos-computed Gauss value `b_k` (`k` nodes) and Gauss–Radau(a) value `B_k`
satisfy `b_k ≤ uᵀ f(A) u ≤ B_k` for every `k ≥ 1` with `k + 1 ≤ grade` and `T_k − a I`
nonsingular; that `B_k − b_k → 0` is not claimed by the book. Backbone
`Lanczos.gauss_le_integral_le_radau` with (10.2.6). -/
theorem lanczos_quadrature_bounds {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk0 : 0 < k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u (k + 1)) = k + 1) {a b : ℝ}
    (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det)
    (hab : spectrum ℝ A ⊆ Set.Icc a b) {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f U)
    (heven : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k) f t)
    (hodd : ∀ t ∈ Set.Icc a b, iteratedDeriv (2 * k + 1) f t ≤ 0) :
    ‖u‖ ^ 2 * ∑ j, ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvectorBasis j
        ⟨0, hk0⟩) ^ 2 * f ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvalues j) ≤
        u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) ∧
      u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) ≤
        ‖u‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvectorBasis
          j 0) ^ 2 * f ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvalues j) := by
  rw [(equation_10_2_6 hA u f).2, spectralWeight_measure]
  exact Lanczos.gauss_le_integral_le_radau hA.isSymmetric_toEuclideanLin finrank_euclideanSpace
    u hk0 hk ha (eigenvalues_mem_Icc hA hab) hU hUsub hf heven hodd

end Lanczos

end GolubVanLoan.Chapter10
