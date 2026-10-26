import NumlibSurface.CartisGouldToint.Chapter10.Section03

/-!
# Cartis–Gould–Toint §11.1: Variable scaling

Surface file for [cartis2022evaluation] §11.1: the modified absolute value (11.1.4), the ideal
scaling `M = V |Λ_δ| Vᵀ` (11.1.2)–(11.1.3) and the change of variables to the diagonal problems
(11.1.5)–(11.1.7), the explicit solutions of the diagonal problems (§11.1.3), and the same
transformation for a symmetric indefinite factorization (§11.1.4, (11.1.15)).

## Main definitions

* `modifiedAbs δ x` — the modified absolute value `|x|_δ` of (11.1.4).
* `partOn d c v` — the part of `v` on the index set `{i | dᵢ = c}`; `plusPart d v`, `minusPart d v`
  — the parts `g₊ᴰ`, `g₋ᴰ` of a vector on `𝒟⁺ = {i | dᵢ = 1}`, `𝒟⁻ = {i | dᵢ = -1}`.

## Main results

* `transform_of_congruence` — a congruence `H = W D Wᵀ`, `M = W Wᵀ` turns (8.1.2)/(8.1.3) into the
  problems for `(W⁻¹g, D)` in the Euclidean norm.
* `idealScaling_transform` — (11.1.5)–(11.1.7).
* `indefiniteFactorization_transform` — §11.1.4.
* `diagonal_trustRegion_solution`, `diagonal_regularization_solution` — §11.1.3.

## Corrections to the source

* (11.1.6): the regularization term is `σ/r ‖sᴰ‖^r` (printed `‖s‖^r`).
* (11.1.7): the cases must read `λᵢ ≥ δ` and `λᵢ ≤ -δ` (printed `>`, `<`) to match (11.1.4) at
  `|λᵢ| = δ`; then `dᵢᵢ = λᵢ/δ ∈ (-1, 1)` in the remaining case.
* §11.1.3, regularization: the secular equation for `g₋ᴰ ≠ 0` is
  `‖g₊ᴰ‖²/(λ+1)² + ‖g₋ᴰ‖²/(λ-1)² = (λ/σ)^{2/(r-2)}` (printed `(λ²/σ²)^{2/(r-2)}`); the hard case
  occurs iff `½‖gᴰ‖ ≤ σ^{-1/(r-2)}` (printed `≥`); and then `∑ αᵢ² = σ^{-2/(r-2)} - ¼‖gᴰ‖²` (printed
  as a product).

## Implementation notes

In the trust-region case with `g₋ᴰ = 0` and `½‖gᴰ‖ = Δ` the hard-case family reduces to (11.1.13),
so the boundary `½‖gᴰ‖ = Δ` belongs to both descriptions; `diagonal_trustRegion_solution` files
it under (11.1.13).
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter11

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter10

variable {n : ℕ}

/-! ### The modified absolute value -/

/-- The **modified absolute value** `|x|_δ` of [cartis2022evaluation] (11.1.4): `|x|` if
`|x| ≥ δ`, and `δ` otherwise. Applied to the eigenvalues of `H` it gives the ideal scaling
`M = V |Λ_δ| Vᵀ` (11.1.2)–(11.1.3). -/
noncomputable def modifiedAbs (δ x : ℝ) : ℝ := if δ ≤ |x| then |x| else δ

theorem modifiedAbs_pos {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 < modifiedAbs δ x := by
  unfold modifiedAbs; split_ifs with h <;> linarith

/-- The diagonal entries (11.1.7): `x/|x|_δ` is `1` if `x ≥ δ`, `-1` if `x ≤ -δ`, and
`x/δ ∈ (-1, 1)` otherwise. -/
theorem div_modifiedAbs {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (δ ≤ x → x / modifiedAbs δ x = 1) ∧ (x ≤ -δ → x / modifiedAbs δ x = -1) ∧
      (-δ < x → x < δ → x / modifiedAbs δ x = x / δ ∧ x / δ ∈ Ioo (-1) 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · rw [modifiedAbs, ite_eq_left (by rw [abs_of_pos (by linarith)]; exact h),
      abs_of_pos (by linarith), div_self (by linarith)]
  · rw [modifiedAbs, ite_eq_left (by rw [abs_of_neg (by linarith)]; linarith),
      abs_of_neg (by linarith), div_neg, div_self (by linarith)]
  · have : ¬ δ ≤ |x| := by rw [not_le, abs_lt]; exact ⟨h1, h2⟩
    rw [modifiedAbs, ite_eq_right this]
    refine ⟨rfl, ?_, ?_⟩
    · rw [lt_div_iff₀ hδ]; linarith
    · rw [div_lt_iff₀ hδ]; linarith

/-! ### Congruence transformations -/

section Transform

variable {H M W D : Matrix (Fin n) (Fin n) ℝ} {g gD : EuclideanSpace ℝ (Fin n)}

/-- **Change of variables by a congruence.** If `H = W D Wᵀ` and `M = W Wᵀ` with `W` invertible,
and `W gᴰ = g`, then with `sᴰ = Wᵀ s`: `m(s) = ⟪gᴰ, sᴰ⟫ + ½ ⟪sᴰ, D sᴰ⟫`, `‖s‖_M = ‖sᴰ‖`, and `s`
solves (8.1.2) (resp. (8.1.3)) iff `sᴰ` solves the trust-region (resp. regularization) problem for
`(gᴰ, D)` in the Euclidean norm. -/
theorem transform_of_congruence (hW : IsUnit W) (hH : H = W * D * Wᵀ) (hM : M = W * Wᵀ)
    (hg : toEuclideanLin W gD = g) :
    (∀ s, model g H s = model gD D (toEuclideanLin Wᵀ s)) ∧
      (∀ s, mNorm M s = ‖toEuclideanLin Wᵀ s‖) ∧
      (∀ Δ s, IsTrustRegionSolution g H M Δ s ↔
        IsTrustRegionSolution gD D 1 Δ (toEuclideanLin Wᵀ s)) ∧
      (∀ σ r s, IsRegularizationSolution g H M σ r s ↔
        IsRegularizationSolution gD D 1 σ r (toEuclideanLin Wᵀ s)) := by
  have hmodel : ∀ s, model g H s = model gD D (toEuclideanLin Wᵀ s) := fun s => by
    rw [model, model, hH, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
      toEuclideanLin_transpose_inner_left, toEuclideanLin_transpose_inner_right, hg]
  have hnorm : ∀ s, mNorm M s = ‖toEuclideanLin Wᵀ s‖ := fun s => by
    rw [mNorm, hM, toEuclideanLin_mul_apply, ← toEuclideanLin_transpose_inner_left,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsurj : Function.Surjective (toEuclideanLin Wᵀ) := fun y =>
    ⟨toEuclideanLin Wᵀ⁻¹ y, toEuclideanLin_mul_nonsing_inv_apply ((isUnit_transpose W).2 hW) y⟩
  refine ⟨hmodel, hnorm, fun Δ s => ?_, fun σ r s => ?_⟩
  · simp only [IsTrustRegionSolution, hnorm, hmodel, mNorm_one]
    refine and_congr_right fun _ => ⟨fun h u hu => ?_, fun h u hu => h _ hu⟩
    obtain ⟨v, rfl⟩ := hsurj u
    exact h v hu
  · have hreg : ∀ s, regModel g H M σ r s = regModel gD D 1 σ r (toEuclideanLin Wᵀ s) :=
      fun s => by rw [Chapter08.regModel, Chapter08.regModel, hmodel, hnorm, mNorm_one]
    simp only [IsRegularizationSolution, hreg]
    refine ⟨fun h u => ?_, fun h u => h _⟩
    obtain ⟨v, rfl⟩ := hsurj u
    exact h v

/-- `√a · √a = a` for a positive vector, as a diagonal identity. -/
private theorem diagonal_sqrt_mul_sqrt {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    diagonal (fun i => √(a i)) * diagonal (fun i => √(a i)) = diagonal a := by
  rw [diagonal_mul_diagonal]
  congr 1; funext i; exact Real.mul_self_sqrt (ha i).le

/-- **Scalings by a symmetric indefinite factorization** ([cartis2022evaluation] §11.1.4,
(11.1.15)). Let `H = F Dᴮ Fᵀ` with `F` invertible and `Dᴮ = diag(β)` (e.g. `F = P L V` from a
Bunch–Kaufman–Parlett factorization `H = P L B Lᵀ Pᵀ`, `B = V Dᴮ Vᵀ`), `δ > 0` and
`M = F |Dᴮ_δ| Fᵀ`. Then `M` is positive definite, and the change of variables
`sᴰ = |Dᴮ_δ|^{1/2} Fᵀ s`, `gᴰ = |Dᴮ_δ|^{-1/2} F⁻¹ g` turns (8.1.2)/(8.1.3) into (11.1.5)/(11.1.6)
with the diagonal `D = diag(βᵢ/|βᵢ|_δ)` of (11.1.7) (`div_modifiedAbs`): `m(s) = m^D(sᴰ)`,
`‖s‖_M = ‖sᴰ‖`, solutions correspond, and `s = F⁻ᵀ |Dᴮ_δ|^{-1/2} sᴰ`. -/
theorem indefiniteFactorization_transform {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsUnit F)
    {β : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ) (hH : H = F * diagonal β * Fᵀ)
    (hM : M = F * diagonal (fun i => modifiedAbs δ (β i)) * Fᵀ) (g : EuclideanSpace ℝ (Fin n)) :
    M.PosDef ∧
    (∀ s, model g H s = model
        (toEuclideanLin (diagonal (fun i => 1 / √(modifiedAbs δ (β i))) * F⁻¹) g)
        (diagonal fun i => β i / modifiedAbs δ (β i))
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (β i))) * Fᵀ) s)) ∧
    (∀ s, mNorm M s = ‖toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (β i))) * Fᵀ) s‖) ∧
    (∀ Δ s, IsTrustRegionSolution g H M Δ s ↔ IsTrustRegionSolution
        (toEuclideanLin (diagonal (fun i => 1 / √(modifiedAbs δ (β i))) * F⁻¹) g)
        (diagonal fun i => β i / modifiedAbs δ (β i)) 1 Δ
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (β i))) * Fᵀ) s)) ∧
    (∀ σ r s, IsRegularizationSolution g H M σ r s ↔ IsRegularizationSolution
        (toEuclideanLin (diagonal (fun i => 1 / √(modifiedAbs δ (β i))) * F⁻¹) g)
        (diagonal fun i => β i / modifiedAbs δ (β i)) 1 σ r
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (β i))) * Fᵀ) s)) ∧
    (∀ s, s = toEuclideanLin (Fᵀ⁻¹ * diagonal (fun i => 1 / √(modifiedAbs δ (β i))))
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (β i))) * Fᵀ) s)) := by
  set a : Fin n → ℝ := fun i => modifiedAbs δ (β i)
  have ha : ∀ i, 0 < a i := fun i => modifiedAbs_pos hδ _
  have hsq : ∀ i, 0 < √(a i) := fun i => Real.sqrt_pos.2 (ha i)
  set W := F * diagonal (fun i => √(a i))
  have hWt : Wᵀ = diagonal (fun i => √(a i)) * Fᵀ := by
    rw [transpose_mul, diagonal_transpose]
  have hdinv : diagonal (fun i => √(a i)) * diagonal (fun i => 1 / √(a i)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_one_div_cancel (hsq i).ne'
  have hdinv' : diagonal (fun i => 1 / √(a i)) * diagonal (fun i => √(a i)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact one_div_mul_cancel (hsq i).ne'
  have hdu : IsUnit (diagonal (fun i => √(a i))) :=
    isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i => isUnit_iff_ne_zero.2 (hsq i).ne')
  have hWu : IsUnit W := hF.mul hdu
  have hFt : IsUnit Fᵀ := (isUnit_transpose F).2 hF
  have hFdet : IsUnit F.det := (isUnit_iff_isUnit_det F).1 hF
  have hFtdet : IsUnit Fᵀ.det := (isUnit_iff_isUnit_det Fᵀ).1 hFt
  have hHW : H = W * diagonal (fun i => β i / a i) * Wᵀ := by
    have hβ : diagonal β = diagonal (fun i => √(a i)) * diagonal (fun i => β i / a i) *
        diagonal (fun i => √(a i)) := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1; funext i
      calc β i = β i / a i * (√(a i) * √(a i)) := by
            rw [Real.mul_self_sqrt (ha i).le, div_mul_cancel₀ _ (ha i).ne']
        _ = _ := by ring
    rw [hH, hβ, hWt]
    simp only [W, Matrix.mul_assoc]
  have hMW : M = W * Wᵀ := by
    rw [hM, ← diagonal_sqrt_mul_sqrt ha, hWt]
    simp only [W, Matrix.mul_assoc]
  have hg : toEuclideanLin W (toEuclideanLin (diagonal (fun i => 1 / √(a i)) * F⁻¹) g) = g := by
    rw [← toEuclideanLin_mul_apply, Matrix.mul_assoc F, ← Matrix.mul_assoc (diagonal _), hdinv,
      Matrix.one_mul, mul_nonsing_inv _ hFdet, toEuclideanLin_one, LinearMap.id_apply]
  obtain ⟨h1, h2, h3, h4⟩ := transform_of_congruence hWu hHW hMW hg
  rw [hWt] at h1 h2 h3 h4
  have hpd : M.PosDef := by
    have hD : (diagonal a).PosDef := posDef_diagonal_iff.2 ha
    have := hD.conjTranspose_mul_mul_same (B := Fᵀ) (mulVec_injective_iff_isUnit.2 hFt)
    rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose, ← hM] at this
  refine ⟨hpd, h1, h2, h3, h4, fun s => ?_⟩
  rw [← toEuclideanLin_mul_apply, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hdinv',
    Matrix.one_mul, nonsing_inv_mul _ hFtdet, toEuclideanLin_one, LinearMap.id_apply]

/-- **The ideal scaling** ([cartis2022evaluation] (11.1.1)–(11.1.7)). Let `H = V Λ Vᵀ` with `V`
orthogonal and `Λ = diag(λ)`, `δ > 0`, and `M = V |Λ_δ| Vᵀ` (11.1.2)–(11.1.4). Then `M` is positive
definite, and with `sᴰ = |Λ_δ|^{1/2} Vᵀ s`, `gᴰ = |Λ_δ|^{-1/2} Vᵀ g` and
`D = |Λ_δ|^{-1/2} Λ |Λ_δ|^{-1/2}= diag(λᵢ/|λᵢ|_δ)`:
(i) `dᵢᵢ = 1` if `λᵢ ≥ δ`, `dᵢᵢ = -1` if `λᵢ ≤ -δ`, and `dᵢᵢ = λᵢ/δ ∈ (-1, 1)` otherwise
((11.1.7), corrected at `|λᵢ| = δ`);
(ii) `m(s) = ⟪gᴰ, sᴰ⟫ + ½ ⟪sᴰ, D sᴰ⟫` and `‖s‖_M = ‖sᴰ‖`;
(iii) `s` solves (8.1.2) (resp. (8.1.3)) iff `sᴰ` solves (11.1.5) (resp. (11.1.6)), and
`s = V |Λ_δ|^{-1/2} sᴰ`. -/
theorem idealScaling_transform {H M V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1)
    {lam : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ) (hH : H = V * diagonal lam * Vᵀ)
    (hM : M = V * diagonal (fun i => modifiedAbs δ (lam i)) * Vᵀ) (g : EuclideanSpace ℝ (Fin n)) :
    M.PosDef ∧
    (∀ i, (δ ≤ lam i → lam i / modifiedAbs δ (lam i) = 1) ∧
      (lam i ≤ -δ → lam i / modifiedAbs δ (lam i) = -1) ∧
      (-δ < lam i → lam i < δ →
        lam i / modifiedAbs δ (lam i) = lam i / δ ∧ lam i / δ ∈ Ioo (-1) 1)) ∧
    (∀ s, model g H s = model
        (toEuclideanLin (diagonal (fun i => 1 / √(modifiedAbs δ (lam i))) * Vᵀ) g)
        (diagonal fun i => lam i / modifiedAbs δ (lam i))
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (lam i))) * Vᵀ) s)) ∧
    (∀ s, mNorm M s = ‖toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (lam i))) * Vᵀ) s‖) ∧
    (∀ Δ s, IsTrustRegionSolution g H M Δ s ↔ IsTrustRegionSolution
        (toEuclideanLin (diagonal (fun i => 1 / √(modifiedAbs δ (lam i))) * Vᵀ) g)
        (diagonal fun i => lam i / modifiedAbs δ (lam i)) 1 Δ
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (lam i))) * Vᵀ) s)) ∧
    (∀ σ r s, IsRegularizationSolution g H M σ r s ↔ IsRegularizationSolution
        (toEuclideanLin (diagonal (fun i => 1 / √(modifiedAbs δ (lam i))) * Vᵀ) g)
        (diagonal fun i => lam i / modifiedAbs δ (lam i)) 1 σ r
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (lam i))) * Vᵀ) s)) ∧
    (∀ s, s = toEuclideanLin (V * diagonal (fun i => 1 / √(modifiedAbs δ (lam i))))
        (toEuclideanLin (diagonal (fun i => √(modifiedAbs δ (lam i))) * Vᵀ) s)) := by
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.1 hV
  have hVu : IsUnit V := (isUnit_iff_isUnit_det V).2 (isUnit_det_of_left_inverse hV)
  have hVinv : V⁻¹ = Vᵀ := inv_eq_left_inv hV
  have hVtinv : Vᵀ⁻¹ = V := inv_eq_left_inv hV'
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := indefiniteFactorization_transform hVu hδ hH hM g
  rw [hVinv] at h1 h3 h4
  rw [hVtinv] at h5
  exact ⟨h0, fun i => div_modifiedAbs hδ (lam i), h1, h2, h3, h4, h5⟩

end Transform


/-! ### The diagonal problems (§11.1.3) -/

section Diagonal

variable {d : Fin n → ℝ}

/-- The part `∑_{i : dᵢ = c} vᵢ eᵢ` of a vector on the index set `{i | dᵢ = c}`. -/
noncomputable def partOn (d : Fin n → ℝ) (c : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => if d i = c then v i else 0

/-- `g₊ᴰ = ∑_{i ∈ 𝒟⁺} gᵢᴰ eᵢ`, `𝒟⁺ = {i | dᵢᵢ = 1}` ([cartis2022evaluation] §11.1.3). -/
noncomputable abbrev plusPart (d : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  partOn d 1 v

/-- `g₋ᴰ = ∑_{i ∈ 𝒟⁻} gᵢᴰ eᵢ`, `𝒟⁻ = {i | dᵢᵢ = -1}` ([cartis2022evaluation] §11.1.3). -/
noncomputable abbrev minusPart (d : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  partOn d (-1) v

@[simp]
theorem partOn_apply (c : ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    partOn d c v i = if d i = c then v i else 0 := rfl

/-- Vectors with disjoint supports are orthogonal. -/
private theorem inner_eq_zero_of_disjoint {v w : EuclideanSpace ℝ (Fin n)}
    (h : ∀ i, v i = 0 ∨ w i = 0) :
    ⟪v, w⟫ = 0 := by
  rw [PiLp.inner_apply]
  exact Finset.sum_eq_zero fun i _ => by rcases h i with h | h <;> simp [h]

/-- Pythagoras for disjoint supports. -/
private theorem norm_add_sq_of_disjoint {v w : EuclideanSpace ℝ (Fin n)}
    (h : ∀ i, v i = 0 ∨ w i = 0) : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_real (inner_eq_zero_of_disjoint h)

/-- The diagonal shifted system `(D + λ I) s = -g`, componentwise. -/
theorem diagonal_shifted_iff (lam : ℝ) (s g : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (diagonal d + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) s = -g ↔
      ∀ i, (d i + lam) * s i = -g i := by
  have : diagonal d + lam • (1 : Matrix (Fin n) (Fin n) ℝ) = diagonal fun i => d i + lam := by
    ext i j; by_cases h : i = j <;> simp [h, one_apply]
  rw [this]
  constructor
  · intro h i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    simpa [toEuclideanLin_apply, mulVec_diagonal] using this
  · intro h
    ext i
    simpa [toEuclideanLin_apply, mulVec_diagonal] using h i

/-- `D + λ I ⪰ 0` iff `dᵢ + λ ≥ 0` for all `i`. -/
theorem diagonal_posSemidef_iff (lam : ℝ) :
    (diagonal d + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ↔ ∀ i, 0 ≤ d i + lam := by
  have : diagonal d + lam • (1 : Matrix (Fin n) (Fin n) ℝ) = diagonal fun i => d i + lam := by
    ext i j; by_cases h : i = j <;> simp [h, one_apply]
  rw [this, posSemidef_diagonal_iff]

/-- The multiplier conditions of Theorem 8.2.7 for the diagonal data `(g, D, I)`. -/
theorem diagonal_kkt_iff {g s : EuclideanSpace ℝ (Fin n)} {Δ lam : ℝ} :
    IsTrustRegionKKT g (diagonal d) 1 Δ s lam ↔
      0 ≤ lam ∧ (∀ i, (d i + lam) * s i = -g i) ∧ (∀ i, 0 ≤ d i + lam) ∧
        lam * (‖s‖ ^ 2 - Δ ^ 2) = 0 := by
  rw [← diagonal_shifted_iff, ← diagonal_posSemidef_iff, ← mNorm_one]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- A positive multiplier forces `‖s‖ = Δ`. -/
private theorem norm_eq_of_compl {s : EuclideanSpace ℝ (Fin n)} {Δ lam : ℝ} (hΔ : 0 < Δ)
    (hlam : 0 < lam) (h : lam * (‖s‖ ^ 2 - Δ ^ 2) = 0) : ‖s‖ = Δ := by
  have : ‖s‖ ^ 2 = Δ ^ 2 := by
    have := (mul_eq_zero.1 h).resolve_left hlam.ne'; linarith
  exact (sq_eq_sq₀ (norm_nonneg _) hΔ.le).1 this

/-- The components on `𝒟⁺` and `𝒟⁻` are disjoint. -/
private theorem plusPart_minusPart_disjoint (v w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    plusPart d v i = 0 ∨ minusPart d w i = 0 := by
  simp only [partOn_apply]
  by_cases h : d i = 1
  · right; rw [ite_eq_right (by rw [h]; norm_num)]
  · left; rw [ite_eq_right h]

/-- `v = v₊ + v₋` when `D = diag(±1)`. -/
theorem plusPart_add_minusPart (hd : ∀ i, d i = 1 ∨ d i = -1) (v : EuclideanSpace ℝ (Fin n)) :
    plusPart d v + minusPart d v = v := by
  ext i
  simp only [PiLp.add_apply, partOn_apply]
  rcases hd i with h | h <;> simp [h, show (1 : ℝ) ≠ -1 by norm_num, show (-1 : ℝ) ≠ 1 by norm_num]

/-- `‖c v‖² = c² ‖v‖²`. -/
private theorem norm_smul_sq (c : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The function `A/(λ+1)² + B/(λ-1)²` (`A ≥ 0`, `B > 0`) is strictly decreasing on `(1, ∞)`. -/
private theorem secular_diag_strictAnti {A B a b : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (ha : 1 < a)
    (hab : a < b) :
    A / (b + 1) ^ 2 + B / (b - 1) ^ 2 < A / (a + 1) ^ 2 + B / (a - 1) ^ 2 := by
  have h1 : A / (b + 1) ^ 2 ≤ A / (a + 1) ^ 2 :=
    div_le_div_of_nonneg_left hA (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have h2 : B / (b - 1) ^ 2 < B / (a - 1) ^ 2 :=
    div_lt_div_of_pos_left hB (by nlinarith)
      (pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero)
  linarith

/-- With `g₋ = 0`, the components of `g` on `𝒟⁻` vanish and `g₊ = g`. -/
private theorem minusPart_eq_zero_iff {g : EuclideanSpace ℝ (Fin n)} :
    minusPart d g = 0 ↔ ∀ i, d i = -1 → g i = 0 := by
  constructor
  · intro h i hi
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    simpa [hi] using this
  · intro h; ext i
    simp only [partOn_apply, PiLp.zero_apply]
    split_ifs with hi
    · exact h i hi
    · rfl

/-- The solution of `(D + λ I) s = -g` for `λ > 1`: `s = -g₊/(λ+1) - g₋/(λ-1)` (11.1.10), with
`‖s‖² = ‖g₊‖²/(λ+1)² + ‖g₋‖²/(λ-1)²`. -/
private theorem diagonal_step (hd : ∀ i, d i = 1 ∨ d i = -1) {g s : EuclideanSpace ℝ (Fin n)}
    {lam : ℝ}
    (hsh : ∀ i, (d i + lam) * s i = -g i) (hl : 1 < lam) :
    s = -(lam + 1)⁻¹ • plusPart d g - (lam - 1)⁻¹ • minusPart d g ∧
      ‖s‖ ^ 2 = ‖plusPart d g‖ ^ 2 / (lam + 1) ^ 2 + ‖minusPart d g‖ ^ 2 / (lam - 1) ^ 2 := by
  have h1ne : (-1 : ℝ) ≠ 1 := by norm_num
  have h1ne' : (1 : ℝ) ≠ -1 := by norm_num
  have hp : lam + 1 ≠ 0 := by linarith
  have hm : lam - 1 ≠ 0 := by linarith
  have hseq : s = -(lam + 1)⁻¹ • plusPart d g - (lam - 1)⁻¹ • minusPart d g := by
    ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, partOn_apply, smul_eq_mul]
    rcases hd i with h | h
    · have := hsh i; rw [h] at this
      simp only [h, ite_true, h1ne', ite_false, mul_zero, sub_zero]
      field_simp; linarith
    · have := hsh i; rw [h] at this
      simp only [h, h1ne, ite_false, ite_true, mul_zero, zero_sub]
      field_simp; linarith
  refine ⟨hseq, ?_⟩
  have hdisj : ∀ i, ((-(lam + 1)⁻¹) • plusPart d g) i = 0 ∨
      (-((lam - 1)⁻¹ • minusPart d g)) i = 0 := fun i => by
    rcases hd i with h | h
    · right; simp [h, h1ne']
    · left; simp [h, h1ne]
  rw [hseq, sub_eq_add_neg, norm_add_sq_of_disjoint hdisj, norm_neg, norm_smul_sq, norm_smul_sq]
  field_simp

/-- If `g₋ ≠ 0`, a multiplier `λ ≥ 1` of `(D + λ I) s = -g` is `> 1`. -/
private theorem one_lt_of_minusPart_ne_zero {g s : EuclideanSpace ℝ (Fin n)} {lam : ℝ}
    (hsh : ∀ i, (d i + lam) * s i = -g i) (hl1 : 1 ≤ lam) (hgm : minusPart d g ≠ 0) :
    1 < lam := by
  obtain ⟨j, hj⟩ : ∃ j, minusPart d g j ≠ 0 := by
    by_contra h
    push Not at h
    exact hgm (by ext j; exact h j)
  have hdj : d j = -1 := by by_contra h; simp [h] at hj
  have hj' : g j ≠ 0 := by simpa [hdj] using hj
  refine lt_of_le_of_ne hl1 fun h => hj' ?_
  have := hsh j; rw [hdj, ← h] at this; linarith

/-- The case `g₋ = 0`: for `λ > 1`, `s = -g/(λ+1)` and `‖s‖ = ‖g‖/(λ+1)`; for `λ = 1`,
`s = -½ g + α` with `α` supported on `𝒟⁻` and `‖s‖² = ¼ ‖g‖² + ‖α‖²`. -/
private theorem diagonal_step_of_minusPart_eq_zero (hd : ∀ i, d i = 1 ∨ d i = -1)
    {g s : EuclideanSpace ℝ (Fin n)} {lam : ℝ} (hsh : ∀ i, (d i + lam) * s i = -g i)
    (hgm : minusPart d g = 0) :
    (1 < lam → s = -(lam + 1)⁻¹ • g ∧ ‖s‖ = ‖g‖ / (lam + 1)) ∧
      (lam = 1 → ∃ α : EuclideanSpace ℝ (Fin n), (∀ i, d i = 1 → α i = 0) ∧
        ‖s‖ ^ 2 = ‖g‖ ^ 2 / 4 + ‖α‖ ^ 2 ∧ s = -(1 / 2 : ℝ) • g + α) := by
  have hg0 := minusPart_eq_zero_iff.1 hgm
  constructor
  · intro hgt
    have hsh' : ∀ i, s i = -(lam + 1)⁻¹ * g i := fun i => by
      have hp : lam + 1 ≠ 0 := by linarith
      rcases hd i with h | h
      · have := hsh i; rw [h] at this; field_simp; linarith
      · have := hsh i; rw [h, hg0 i h] at this
        have hsi : s i = 0 :=
          (mul_eq_zero.1 (by linarith : (-1 + lam) * s i = 0)).resolve_left (by linarith)
        rw [hsi, hg0 i h, mul_zero]
    have hseq : s = -(lam + 1)⁻¹ • g := by
      ext i; simp only [PiLp.smul_apply, smul_eq_mul]; exact hsh' i
    refine ⟨hseq, ?_⟩
    rw [hseq, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos (by linarith),
      inv_mul_eq_div]
  · intro hl
    refine ⟨s + (1 / 2 : ℝ) • g, fun i hi => ?_, ?_, by module⟩
    · have := hsh i; rw [hi, hl] at this
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; linarith
    · have hdisj : ∀ i, ((-(1 / 2 : ℝ)) • g) i = 0 ∨ (s + (1 / 2 : ℝ) • g) i = 0 := by
        intro i
        rcases hd i with h | h
        · right; have := hsh i; rw [h, hl] at this
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; linarith
        · left; simp [hg0 i h]
      have := norm_add_sq_of_disjoint hdisj
      rw [show (-(1 / 2 : ℝ)) • g + (s + (1 / 2 : ℝ) • g) = s by module, norm_smul_sq] at this
      linarith

/-- With `g₋ = 0`, `g₊ = g`. -/
private theorem plusPart_eq_self (hd : ∀ i, d i = 1 ∨ d i = -1) {g : EuclideanSpace ℝ (Fin n)}
    (hgm : minusPart d g = 0) : plusPart d g = g := by
  have := plusPart_add_minusPart hd g
  rwa [hgm, add_zero] at this

/-- `‖-½ g + α‖² = ¼‖g‖² + ‖α‖²` when `g` lives on `𝒟⁺` and `α` on `𝒟⁻`. -/
private theorem norm_hardCase_sq (hd : ∀ i, d i = 1 ∨ d i = -1) {g α : EuclideanSpace ℝ (Fin n)}
    (hgm : minusPart d g = 0) (hα : ∀ i, d i = 1 → α i = 0) :
    ‖-(1 / 2 : ℝ) • g + α‖ ^ 2 = ‖g‖ ^ 2 / 4 + ‖α‖ ^ 2 := by
  have hg0 := minusPart_eq_zero_iff.1 hgm
  have hdisj : ∀ i, ((-(1 / 2 : ℝ)) • g) i = 0 ∨ α i = 0 := fun i => by
    rcases hd i with h | h
    · right; exact hα i h
    · left; simp [hg0 i h]
  rw [norm_add_sq_of_disjoint hdisj, norm_smul_sq]; ring

/-- **The diagonal trust-region problem** ([cartis2022evaluation] §11.1.3, (11.1.8)–(11.1.14)).
Let `D = diag(d)` with `dᵢ = ±1` (`𝒟⁰ = ∅`), `Δ > 0`, and let `sᴰ` solve (11.1.5) with
multiplier `λ*`. Then:
(i) if `𝒟⁻ = ∅`: for `‖gᴰ‖ ≤ Δ`, `λ* = 0` and `sᴰ = -gᴰ`; for `‖gᴰ‖ > Δ`, `λ* = ‖gᴰ‖/Δ - 1`
and `sᴰ = -(Δ/‖gᴰ‖) gᴰ` ((11.1.11)–(11.1.13));
(ii) if `𝒟⁻ ≠ ∅`: `‖sᴰ‖ = Δ` and `λ* ≥ 1`; if `g₋ᴰ ≠ 0`, then `λ* > 1` is the unique root on
`(1, ∞)` of (11.1.14) `‖g₊ᴰ‖²/(λ+1)² + ‖g₋ᴰ‖²/(λ-1)² = Δ²` and (11.1.10) holds; if `g₋ᴰ = 0`
and `½‖gᴰ‖ ≥ Δ`, then (11.1.13) holds with `λ* = ‖gᴰ‖/Δ - 1`; if `g₋ᴰ = 0` and `½‖gᴰ‖ < Δ`
(the hard case), then `λ* = 1` and `sᴰ = -½ g₊ᴰ + ∑_{i ∈ 𝒟⁻} αᵢ eᵢ` with
`∑ αᵢ² = Δ² - ¼‖gᴰ‖²` (every such vector is a solution: `diagonal_trustRegion_hardCase`). -/
theorem diagonal_trustRegion_solution (hd : ∀ i, d i = 1 ∨ d i = -1)
    {g : EuclideanSpace ℝ (Fin n)} {Δ : ℝ} (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)} {lam : ℝ}
    (hs : IsTrustRegionSolution g (diagonal d) 1 Δ s)
    (hlam : IsTrustRegionKKT g (diagonal d) 1 Δ s lam) :
    ((∀ i, d i = 1) →
      (‖g‖ ≤ Δ → lam = 0 ∧ s = -g) ∧
      (Δ < ‖g‖ → lam = ‖g‖ / Δ - 1 ∧ s = -(Δ / ‖g‖) • g)) ∧
    ((∃ i, d i = -1) →
      ‖s‖ = Δ ∧ 1 ≤ lam ∧
      (minusPart d g ≠ 0 → 1 < lam ∧
        ‖plusPart d g‖ ^ 2 / (lam + 1) ^ 2 + ‖minusPart d g‖ ^ 2 / (lam - 1) ^ 2 = Δ ^ 2 ∧
        (∀ μ, 1 < μ →
          ‖plusPart d g‖ ^ 2 / (μ + 1) ^ 2 + ‖minusPart d g‖ ^ 2 / (μ - 1) ^ 2 = Δ ^ 2 →
            μ = lam) ∧
        s = -(lam + 1)⁻¹ • plusPart d g - (lam - 1)⁻¹ • minusPart d g) ∧
      (minusPart d g = 0 → Δ ≤ ‖g‖ / 2 → lam = ‖g‖ / Δ - 1 ∧ s = -(Δ / ‖g‖) • g) ∧
      (minusPart d g = 0 → ‖g‖ / 2 < Δ → lam = 1 ∧
        ∃ α : EuclideanSpace ℝ (Fin n), (∀ i, d i = 1 → α i = 0) ∧
          ‖α‖ ^ 2 = Δ ^ 2 - ‖g‖ ^ 2 / 4 ∧ s = -(1 / 2 : ℝ) • plusPart d g + α)) := by
  obtain ⟨hl0, hsh, hps, hc⟩ := diagonal_kkt_iff.1 hlam
  have hsΔ : ‖s‖ ≤ Δ := by rw [← mNorm_one]; exact hs.1
  constructor
  · intro hall
    have hd' : ∀ i, d i = 1 ∨ d i = -1 := fun i => Or.inl (hall i)
    have hgm : minusPart d g = 0 := minusPart_eq_zero_iff.2 fun i hi => by
      rw [hall i] at hi; norm_num at hi
    have hsh' : ∀ i, (1 + lam) * s i = -g i := fun i => by rw [← hall i]; exact hsh i
    have hseq : s = -(1 + lam)⁻¹ • g := by
      ext i; simp only [PiLp.smul_apply, smul_eq_mul]
      have := hsh' i
      field_simp; linarith
    have hsn : ‖s‖ = ‖g‖ / (1 + lam) := by
      rw [hseq, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos (by linarith),
        inv_mul_eq_div]
    constructor
    · intro hgΔ
      have hlam0 : lam = 0 := by
        by_contra hne
        have hpos : 0 < lam := lt_of_le_of_ne hl0 (Ne.symm hne)
        have := norm_eq_of_compl hΔ hpos hc
        rw [hsn, div_eq_iff (by linarith)] at this
        nlinarith
      refine ⟨hlam0, ?_⟩
      rw [hseq, hlam0]; simp
    · intro hgΔ
      have hpos : 0 < lam := by
        refine lt_of_le_of_ne hl0 fun h => ?_
        rw [← h, add_zero, div_one] at hsn
        linarith
      have hn := norm_eq_of_compl hΔ hpos hc
      rw [hsn, div_eq_iff (by linarith)] at hn
      have hlam : lam = ‖g‖ / Δ - 1 := by
        rw [eq_sub_iff_add_eq, eq_div_iff hΔ.ne']; linarith
      refine ⟨hlam, ?_⟩
      rw [hseq, hlam, show 1 + (‖g‖ / Δ - 1) = ‖g‖ / Δ by ring, inv_div]
  · rintro ⟨i₀, hi₀⟩
    have hl1 : 1 ≤ lam := by have := hps i₀; rw [hi₀] at this; linarith
    have hn := norm_eq_of_compl hΔ (by linarith) hc
    refine ⟨hn, hl1, fun hgm => ?_, fun hgm hgΔ => ?_, fun hgm hgΔ => ?_⟩
    · -- `g₋ ≠ 0`
      have hl1' := one_lt_of_minusPart_ne_zero hsh hl1 hgm
      obtain ⟨hseq, hnorm⟩ := diagonal_step hd hsh hl1'
      have hB : 0 < ‖minusPart d g‖ ^ 2 := by have := norm_pos_iff.2 hgm; positivity
      have hl := hnorm.symm.trans (by rw [hn])
      refine ⟨hl1', hl, fun μ hμ hμr => ?_, hseq⟩
      rcases lt_trichotomy μ lam with h | h | h
      · exact absurd (hμr.trans hl.symm)
          (secular_diag_strictAnti (sq_nonneg _) hB hμ h).ne'
      · exact h
      · exact absurd (hl.trans hμr.symm)
          (secular_diag_strictAnti (sq_nonneg _) hB hl1' h).ne'
    · -- `g₋ = 0`, `½‖g‖ ≥ Δ`
      obtain ⟨hgt, heq⟩ := diagonal_step_of_minusPart_eq_zero hd hsh hgm
      rcases eq_or_lt_of_le hl1 with h | h
      · obtain ⟨α, -, hα, hs'⟩ := heq h.symm
        rw [hn] at hα
        have hα0 : ‖α‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
        have hα0' : α = 0 := by rw [sq_eq_zero_iff, norm_eq_zero] at hα0; exact hα0
        have hg2 : ‖g‖ = 2 * Δ := by nlinarith [sq_nonneg ‖α‖, norm_nonneg g]
        refine ⟨by rw [← h, hg2]; field_simp; norm_num, ?_⟩
        rw [hs', hα0', add_zero, hg2]
        congr 2; field_simp
      · obtain ⟨hseq, hg⟩ := hgt h
        rw [hn, eq_div_iff (by linarith)] at hg
        have hlam : lam = ‖g‖ / Δ - 1 := by
          rw [eq_sub_iff_add_eq, eq_div_iff hΔ.ne']; linarith
        refine ⟨hlam, ?_⟩
        rw [hseq, hlam, show ‖g‖ / Δ - 1 + 1 = ‖g‖ / Δ by ring, inv_div]
    · -- `g₋ = 0`, `½‖g‖ < Δ`: the hard case
      obtain ⟨hgt, heq⟩ := diagonal_step_of_minusPart_eq_zero hd hsh hgm
      have hl : lam = 1 := by
        rcases eq_or_lt_of_le hl1 with h | h
        · exact h.symm
        · have := (hgt h).2
          rw [hn, eq_div_iff (by linarith)] at this
          nlinarith
      obtain ⟨α, hα1, hα, hs'⟩ := heq hl
      rw [hn] at hα
      exact ⟨hl, α, hα1, by linarith, by rw [plusPart_eq_self hd hgm]; exact hs'⟩

/-- **The hard case of the diagonal trust-region problem** ([cartis2022evaluation] §11.1.3): if
`g₋ᴰ = 0`, every `sᴰ = -½ g₊ᴰ + ∑_{i ∈ 𝒟⁻} αᵢ eᵢ` with `∑ αᵢ² = Δ² - ¼‖gᴰ‖²` solves (11.1.5). -/
theorem diagonal_trustRegion_hardCase (hd : ∀ i, d i = 1 ∨ d i = -1)
    {g : EuclideanSpace ℝ (Fin n)} {Δ : ℝ} (hΔ : 0 < Δ) (hgm : minusPart d g = 0)
    {α : EuclideanSpace ℝ (Fin n)} (hα1 : ∀ i, d i = 1 → α i = 0)
    (hα : ‖α‖ ^ 2 = Δ ^ 2 - ‖g‖ ^ 2 / 4) :
    IsTrustRegionSolution g (diagonal d) 1 Δ (-(1 / 2 : ℝ) • plusPart d g + α) := by
  have hg0 := minusPart_eq_zero_iff.1 hgm
  rw [plusPart_eq_self hd hgm]
  have hn : ‖-(1 / 2 : ℝ) • g + α‖ = Δ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) hΔ.le, norm_hardCase_sq hd hgm hα1, hα]; ring
  refine isTrustRegionSolution_of_kkt (isHermitian_diagonal d) PosDef.one hΔ
    (diagonal_kkt_iff.2 ⟨zero_le_one, fun i => ?_, fun i => ?_, by rw [hn]; ring⟩)
    (by rw [mNorm_one, hn])
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases hd i with h | h
    · rw [h, hα1 i h]; ring
    · rw [h, hg0 i h]; ring
  · rcases hd i with h | h <;> rw [h] <;> norm_num

/-- The radius `σ^{-1/(r-2)}` of the hard case of the regularization problem: `t ≥ 0` satisfies
`σ t^{r-2} = 1` iff `t = σ^{-1/(r-2)}`, and `(σ^{-1/(r-2)})² = σ^{-2/(r-2)}`. -/
private theorem hardCase_radius {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    0 < σ ^ (-1 / (r - 2)) ∧ σ * (σ ^ (-1 / (r - 2))) ^ (r - 2) = 1 ∧
      (σ ^ (-1 / (r - 2))) ^ 2 = σ ^ (-2 / (r - 2)) ∧
      ∀ t, 0 ≤ t → (σ * t ^ (r - 2) = 1 ↔ t = σ ^ (-1 / (r - 2))) := by
  have hr2 : r - 2 ≠ 0 := by linarith
  have hc : (σ ^ (-1 / (r - 2))) ^ (r - 2) = σ⁻¹ := by
    rw [← Real.rpow_mul hσ.le, div_mul_cancel₀ _ hr2, Real.rpow_neg_one]
  refine ⟨Real.rpow_pos_of_pos hσ _, by rw [hc, mul_inv_cancel₀ hσ.ne'], ?_, fun t ht => ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]; congr 1; push_cast; ring
  · constructor
    · intro h
      have h' : t ^ (r - 2) = σ⁻¹ := by field_simp; linarith
      rw [← Real.rpow_rpow_inv ht hr2, h', ← Real.rpow_neg_one, ← Real.rpow_mul hσ.le]
      ring_nf
    · rintro rfl; rw [hc, mul_inv_cancel₀ hσ.ne']

/-- If `λ = σ t^{r-2}` with `t ≥ 0`, the regularization target (8.2.9) at `λ` is `t²`. -/
theorem regTarget_of_eq_mul_rpow {σ r t lam : ℝ} (hσ : 0 < σ) (hr : 2 < r) (ht : 0 ≤ t)
    (h : lam = σ * t ^ (r - 2)) : regTarget σ r lam = t ^ 2 := by
  have hl : 0 ≤ lam := by rw [h]; positivity
  rw [regTarget_eq_sq r hσ hl, h, mul_div_cancel_left₀ _ hσ.ne', one_div,
    Real.rpow_rpow_inv ht (by linarith)]

/-- **The diagonal regularization problem** ([cartis2022evaluation] §11.1.3, corrected). Let
`D = diag(d)` with `dᵢ = ±1`, `σ > 0`, `r > 2`, and let `sᴰ` solve (11.1.6), with multiplier
`λ* = σ ‖sᴰ‖^{r-2}`. Then:
(i) if `𝒟⁻ = ∅`: `sᴰ = -gᴰ/(λ*+1)` (11.1.11) with `λ* ≥ 0` the unique nonnegative root of
`λ = σ (‖gᴰ‖/(λ+1))^{r-2}`;
(ii) if `𝒟⁻ ≠ ∅`: `λ* ≥ 1`; if `g₋ᴰ ≠ 0`, then `λ* > 1` is the unique root on `(1, ∞)` of
`‖g₊ᴰ‖²/(λ+1)² + ‖g₋ᴰ‖²/(λ-1)² = (λ/σ)^{2/(r-2)}` and (11.1.10) holds; if `g₋ᴰ = 0`, the hard
case `λ* = 1` occurs iff `½‖gᴰ‖ ≤ σ^{-1/(r-2)}`, and then `sᴰ = -½ g₊ᴰ + ∑_{i ∈ 𝒟⁻} αᵢ eᵢ` with
`∑ αᵢ² = σ^{-2/(r-2)} - ¼‖gᴰ‖²` (every such vector is a solution:
`diagonal_regularization_hardCase`); otherwise (11.1.10) holds with `g₋ᴰ = 0`. -/
theorem diagonal_regularization_solution (hd : ∀ i, d i = 1 ∨ d i = -1)
    {g : EuclideanSpace ℝ (Fin n)} {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g (diagonal d) 1 σ r s)
    {lam : ℝ} (hlam : lam = σ * ‖s‖ ^ (r - 2)) :
    ((∀ i, d i = 1) →
      0 ≤ lam ∧ s = -(lam + 1)⁻¹ • g ∧ lam = σ * (‖g‖ / (lam + 1)) ^ (r - 2) ∧
        ∀ μ, 0 ≤ μ → μ = σ * (‖g‖ / (μ + 1)) ^ (r - 2) → μ = lam) ∧
    ((∃ i, d i = -1) → 1 ≤ lam ∧
      (minusPart d g ≠ 0 → 1 < lam ∧
        ‖plusPart d g‖ ^ 2 / (lam + 1) ^ 2 + ‖minusPart d g‖ ^ 2 / (lam - 1) ^ 2 =
          regTarget σ r lam ∧
        (∀ μ, 1 < μ → ‖plusPart d g‖ ^ 2 / (μ + 1) ^ 2 + ‖minusPart d g‖ ^ 2 / (μ - 1) ^ 2 =
          regTarget σ r μ → μ = lam) ∧
        s = -(lam + 1)⁻¹ • plusPart d g - (lam - 1)⁻¹ • minusPart d g) ∧
      (minusPart d g = 0 → (lam = 1 ↔ ‖g‖ / 2 ≤ σ ^ (-1 / (r - 2)))) ∧
      (minusPart d g = 0 → lam = 1 → ∃ α : EuclideanSpace ℝ (Fin n), (∀ i, d i = 1 → α i = 0) ∧
        ‖α‖ ^ 2 = σ ^ (-2 / (r - 2)) - ‖g‖ ^ 2 / 4 ∧ s = -(1 / 2 : ℝ) • plusPart d g + α) ∧
      (minusPart d g = 0 → lam ≠ 1 → s = -(lam + 1)⁻¹ • plusPart d g)) := by
  obtain ⟨h1, h2, -⟩ := theorem_8_2_8 (isHermitian_diagonal d) PosDef.one hσ hr hs
  rw [mNorm_one, ← hlam] at h1 h2
  have hsh := (diagonal_shifted_iff lam s g).1 h1
  have hps := (diagonal_posSemidef_iff lam).1 h2
  have hl0 : 0 ≤ lam := by rw [hlam]; positivity
  obtain ⟨hc0, hc1, hc2, hceq⟩ := hardCase_radius hσ hr
  have hmono : ∀ a b : ℝ, 0 ≤ a → a < b → σ * a ^ (r - 2) < σ * b ^ (r - 2) := fun a b ha hab =>
    mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha hab (by linarith)) hσ
  constructor
  · intro hall
    have hsh' : ∀ i, (1 + lam) * s i = -g i := fun i => by rw [← hall i]; exact hsh i
    have hseq : s = -(lam + 1)⁻¹ • g := by
      ext i; simp only [PiLp.smul_apply, smul_eq_mul]
      have := hsh' i
      field_simp; linarith
    have hsn : ‖s‖ = ‖g‖ / (lam + 1) := by
      rw [hseq, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos (by linarith),
        inv_mul_eq_div]
    have hfix : lam = σ * (‖g‖ / (lam + 1)) ^ (r - 2) := by rw [← hsn]; exact hlam
    refine ⟨hl0, hseq, hfix, fun μ hμ hμr => ?_⟩
    rcases eq_or_lt_of_le (norm_nonneg g) with hg0 | hgpos
    · have e : ∀ x : ℝ, 0 ≤ x → σ * (‖g‖ / (x + 1)) ^ (r - 2) = 0 := fun x _ => by
        rw [← hg0, zero_div, Real.zero_rpow (by linarith), mul_zero]
      rw [hμr, e μ hμ, hfix, e lam hl0]
    have hanti : ∀ a b, 0 ≤ a → a < b →
        σ * (‖g‖ / (b + 1)) ^ (r - 2) < σ * (‖g‖ / (a + 1)) ^ (r - 2) := fun a b ha hab =>
      hmono _ _ (div_nonneg hgpos.le (by linarith))
        (div_lt_div_of_pos_left hgpos (by linarith) (by linarith))
    rcases lt_trichotomy μ lam with h | h | h
    · have := hanti μ lam hμ h; linarith
    · exact h
    · have := hanti lam μ hl0 h; linarith
  · rintro ⟨i₀, hi₀⟩
    have hl1 : 1 ≤ lam := by have := hps i₀; rw [hi₀] at this; linarith
    have htarget := (regTarget_of_eq_mul_rpow hσ hr (norm_nonneg s) hlam).symm
    have hT : ∀ a b : ℝ, 0 < a → a < b → regTarget σ r a < regTarget σ r b :=
      fun a b ha hab => Real.rpow_lt_rpow (div_pos ha hσ).le (div_lt_div_of_pos_right hab hσ)
        (div_pos two_pos (by linarith))
    refine ⟨hl1, fun hgm => ?_, fun hgm => ?_, fun hgm hl => ?_, fun hgm hl => ?_⟩
    · have hl1' := one_lt_of_minusPart_ne_zero hsh hl1 hgm
      obtain ⟨hseq, hnorm⟩ := diagonal_step hd hsh hl1'
      have hB : 0 < ‖minusPart d g‖ ^ 2 := by have := norm_pos_iff.2 hgm; positivity
      have hl := hnorm.symm.trans htarget
      refine ⟨hl1', hl, fun μ hμ hμr => ?_, hseq⟩
      rcases lt_trichotomy μ lam with h | h | h
      · have h1 := secular_diag_strictAnti (sq_nonneg ‖plusPart d g‖) hB hμ h
        have h2 := hT μ lam (by linarith) h
        linarith
      · exact h
      · have h1 := secular_diag_strictAnti (sq_nonneg ‖plusPart d g‖) hB hl1' h
        have h2 := hT lam μ (by linarith) h
        linarith
    · obtain ⟨hgt, heq⟩ := diagonal_step_of_minusPart_eq_zero hd hsh hgm
      constructor
      · intro hl
        obtain ⟨α, -, hα, -⟩ := heq hl
        have hsc : ‖s‖ = σ ^ (-1 / (r - 2)) := (hceq _ (norm_nonneg _)).1 (by rw [← hlam, hl])
        rw [← hsc]
        nlinarith [sq_nonneg ‖α‖, norm_nonneg s, norm_nonneg g]
      · intro hgc
        by_contra hne
        have hgt' : 1 < lam := lt_of_le_of_ne hl1 (Ne.symm hne)
        have hsn := (hgt hgt').2
        have hlt : ‖s‖ < σ ^ (-1 / (r - 2)) := by
          rcases eq_or_lt_of_le (norm_nonneg g) with hg0 | hg0
          · rw [hsn, ← hg0, zero_div]; exact hc0
          · rw [hsn]
            calc ‖g‖ / (lam + 1) < ‖g‖ / 2 :=
                  div_lt_div_of_pos_left hg0 two_pos (by linarith)
              _ ≤ _ := hgc
        have := hmono _ _ (norm_nonneg _) hlt
        rw [← hlam, hc1] at this
        linarith
    · obtain ⟨-, heq⟩ := diagonal_step_of_minusPart_eq_zero hd hsh hgm
      obtain ⟨α, hα1, hα, hs'⟩ := heq hl
      have hsc : ‖s‖ = σ ^ (-1 / (r - 2)) := (hceq _ (norm_nonneg _)).1 (by rw [← hlam, hl])
      rw [hsc, hc2] at hα
      exact ⟨α, hα1, by linarith, by rw [plusPart_eq_self hd hgm]; exact hs'⟩
    · obtain ⟨hgt, -⟩ := diagonal_step_of_minusPart_eq_zero hd hsh hgm
      rw [plusPart_eq_self hd hgm]
      exact (hgt (lt_of_le_of_ne hl1 (Ne.symm hl))).1

/-- **The hard case of the diagonal regularization problem** ([cartis2022evaluation] §11.1.3,
corrected): if `g₋ᴰ = 0`, every `sᴰ = -½ g₊ᴰ + ∑_{i ∈ 𝒟⁻} αᵢ eᵢ` with
`∑ αᵢ² = σ^{-2/(r-2)} - ¼‖gᴰ‖²` solves (11.1.6). -/
theorem diagonal_regularization_hardCase (hd : ∀ i, d i = 1 ∨ d i = -1)
    {g : EuclideanSpace ℝ (Fin n)} {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hgm : minusPart d g = 0)
    {α : EuclideanSpace ℝ (Fin n)} (hα1 : ∀ i, d i = 1 → α i = 0)
    (hα : ‖α‖ ^ 2 = σ ^ (-2 / (r - 2)) - ‖g‖ ^ 2 / 4) :
    IsRegularizationSolution g (diagonal d) 1 σ r (-(1 / 2 : ℝ) • plusPart d g + α) := by
  have hg0 := minusPart_eq_zero_iff.1 hgm
  obtain ⟨hc0, hc1, hc2, -⟩ := hardCase_radius hσ hr
  rw [plusPart_eq_self hd hgm]
  have hn : ‖-(1 / 2 : ℝ) • g + α‖ = σ ^ (-1 / (r - 2)) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) hc0.le, norm_hardCase_sq hd hgm hα1, hα, hc2]; ring
  have hl : σ * mNorm 1 (-(1 / 2 : ℝ) • g + α) ^ (r - 2) = 1 := by rw [mNorm_one, hn, hc1]
  refine isRegularizationSolution_of_shifted (isHermitian_diagonal d) PosDef.one hσ hr ?_ ?_
  · rw [hl, diagonal_shifted_iff]
    intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases hd i with h | h
    · rw [h, hα1 i h]; ring
    · rw [h, hg0 i h]; ring
  · rw [hl, diagonal_posSemidef_iff]
    intro i; rcases hd i with h | h <;> rw [h] <;> norm_num

end Diagonal

end CartisGouldToint.Chapter11
