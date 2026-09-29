/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LeastSquares.Total`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.Matrix.SingularValues

/-!
# Total least squares

Total least squares ([golub2013matrix] §6.3, after Golub–Van Loan 1980) perturbs both the data
matrix and the right-hand sides: minimize `‖D [E | R] T‖_F` subject to
`ran (B + R) ⊆ ran (A + E)`, with nonsingular diagonal row weights `D` and column weights `T`.
With `C = D [A | B] T`, every feasible perturbation makes `C + D [E | R] T` rank-deficient, and
the smallest singular value of `C` bounds its size from below.

## Main definitions

* `Matrix.tlsWeighted d t E R`: the weighted matrix `D [E | R] T`.
* `Matrix.IsTLSPerturbation d t A B E R`, `Matrix.IsTLSSolution d t A B X`: the TLS problem
  ([golub2013matrix] (6.3.2)–(6.3.3)); `(6.3.2)` is `d = 1`, `t = 1`, one right-hand side.
* `Matrix.tlsObjective`: the orthogonal-regression objective `ψ` of (6.3.6).

## Main results

* `Matrix.isUnit_lowerRightBlock_of_lt` (first part of the proof of [golub2013matrix]
  Theorem 6.3.1): the generic condition `σ_n(C₁) > σ_{n+1}(C)` makes `V₂₂` invertible.
* `Matrix.existsUnique_isTLSPerturbation`, `Matrix.isTLSPerturbation_iff`,
  `Matrix.isTLSSolution_iff_eq` ([golub2013matrix] Theorem 6.3.1): under the generic condition the
  TLS perturbation is unique, `C + D [E₀ | R₀] T` is the rank-`n` truncation of the SVD of `C`, and
  the unique TLS solution is `X_TLS = −T₁ V₁₂ V₂₂⁻¹ T₂⁻¹`.
* `Matrix.isTLSSolution_of_mem_smallest` ([golub2013matrix] §6.3.2): with one right-hand side,
  a unit vector `w = [z; α]` with `‖C w‖ = σ_min(C)` and `α ≠ 0` gives the TLS solution
  `x = −T₁ z / (t_{n+1} α)`, the perturbation being `−C w wᴴ`.
* `Matrix.not_isTLSSolution_of_forall_last_eq_zero`: if every such `w` has `α = 0` there is no
  TLS solution.
* `Matrix.iInf_sq_norm_diagonal_mulVec_sub_hyperplane`, `Matrix.isMinOn_tlsObjective`: the
  geometric reading (6.3.6) — `ψ` sums weighted squared distances to a hyperplane, and the TLS
  solution minimizes it.

## Implementation notes

Only the single right-hand side needs no singular-value theory beyond the least stretch
`σ_min(C) ‖w‖ ≤ ‖C w‖` (`Matrix.iInf_colSingularValues_mul_norm_le`, attained by
`Matrix.exists_norm_eq_iInf_colSingularValues`): a feasible perturbation `ΔC` has a unit null vector
`w'` of `C + ΔC` with nonzero last entry, and `‖ΔC‖_F ≥ ‖ΔC w'‖ = ‖C w'‖ ≥ σ_min`; conversely
`ΔC = −C w wᴴ` is feasible for every unit `w` with nonzero last entry and has `‖ΔC‖_F = ‖C w‖`.
The multiple right-hand side of Theorem 6.3.1 rests on the Frobenius Eckart–Young–Mirsky bound
of `Numlib/Analysis/Matrix/SingularValues`.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The weighted problem -/

section Defs

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

/-- **The weighted matrix** `D [E | R] T` of the total least-squares problem, with the real
diagonal weights `d` on the rows and `t` on the columns `n ⊕ k`. -/
noncomputable def tlsWeighted (d : m → ℝ) (t : n ⊕ k → ℝ) (E : Matrix m n 𝕜)
    (R : Matrix m k 𝕜) : Matrix m (n ⊕ k) 𝕜 :=
  diagonal (fun i => (d i : 𝕜)) * fromCols E R * diagonal (fun j => (t j : 𝕜))

open scoped Matrix.Norms.Frobenius in
/-- **A total-least-squares perturbation** ([golub2013matrix] (6.3.2)–(6.3.3)): the pair
`(E, R)` is feasible, `ran (B + R) ⊆ ran (A + E)`, and no feasible pair has a smaller weighted
Frobenius norm `‖D [E | R] T‖_F`. -/
structure IsTLSPerturbation (d : m → ℝ) (t : n ⊕ k → ℝ) (A : Matrix m n 𝕜) (B : Matrix m k 𝕜)
    (E : Matrix m n 𝕜) (R : Matrix m k 𝕜) : Prop where
  /-- The perturbation is feasible. -/
  range_le : LinearMap.range (B + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin
  /-- No feasible perturbation is smaller. -/
  norm_le : ∀ (E' : Matrix m n 𝕜) (R' : Matrix m k 𝕜),
    LinearMap.range (B + R').mulVecLin ≤ LinearMap.range (A + E').mulVecLin →
      ‖tlsWeighted d t E R‖ ≤ ‖tlsWeighted d t E' R'‖

/-- **A total-least-squares solution** ([golub2013matrix] (6.3.3), "any `X` … that satisfies
`(A + E₀) X = B + R₀` is said to be a TLS solution"). -/
def IsTLSSolution (d : m → ℝ) (t : n ⊕ k → ℝ) (A : Matrix m n 𝕜) (B : Matrix m k 𝕜)
    (X : Matrix n k 𝕜) : Prop :=
  ∃ E R, IsTLSPerturbation d t A B E R ∧ (A + E) * X = B + R

/-- The weighted matrix is additive. -/
theorem tlsWeighted_add (d : m → ℝ) (t : n ⊕ k → ℝ) (A E : Matrix m n 𝕜) (B R : Matrix m k 𝕜) :
    tlsWeighted d t (A + E) (B + R) = tlsWeighted d t A B + tlsWeighted d t E R := by
  have : fromCols (A + E) (B + R) = fromCols A B + fromCols E R := by
    ext i (j | j) <;> simp
  rw [tlsWeighted, this, Matrix.mul_add, Matrix.add_mul]
  rfl

/-- The weighted matrix acts on a vector `v` as `D ([E | R] (T v))`. -/
theorem tlsWeighted_mulVec (d : m → ℝ) (t : n ⊕ k → ℝ) (E : Matrix m n 𝕜) (R : Matrix m k 𝕜)
    (v : n ⊕ k → 𝕜) (i : m) :
    (tlsWeighted d t E R *ᵥ v) i =
      d i * ((E *ᵥ fun j => t (Sum.inl j) * v (Sum.inl j)) i +
        (R *ᵥ fun j => t (Sum.inr j) * v (Sum.inr j)) i) := by
  rw [tlsWeighted, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_diagonal, fromCols_mulVec]
  have e1 : ((diagonal fun j => (t j : 𝕜)) *ᵥ v) ∘ Sum.inl =
      fun j => (t (Sum.inl j) : 𝕜) * v (Sum.inl j) := funext fun j => mulVec_diagonal _ _ _
  have e2 : ((diagonal fun j => (t j : 𝕜)) *ᵥ v) ∘ Sum.inr =
      fun j => (t (Sum.inr j) : 𝕜) * v (Sum.inr j) := funext fun j => mulVec_diagonal _ _ _
  rw [Pi.add_apply, e1, e2]

/-- **Every weighted matrix is `D [E | R] T`** for nonzero weights:
`E`, `R` are the column blocks of `D⁻¹ M T⁻¹`. -/
theorem exists_tlsWeighted_eq {d : m → ℝ} {t : n ⊕ k → ℝ} (hd : ∀ i, d i ≠ 0)
    (ht : ∀ j, t j ≠ 0) (M : Matrix m (n ⊕ k) 𝕜) : ∃ E R, tlsWeighted d t E R = M := by
  have hd' : ∀ i, (d i : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (hd i)
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  set ER : Matrix m (n ⊕ k) 𝕜 :=
    diagonal (fun i => (d i : 𝕜)⁻¹) * M * diagonal (fun j => (t j : 𝕜)⁻¹)
  refine ⟨ER.toCols₁, ER.toCols₂, ?_⟩
  rw [tlsWeighted, fromCols_toCols]
  simp only [ER, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  rw [Matrix.mul_assoc, diagonal_mul_diagonal]
  simp [mul_inv_cancel₀ (hd' _), inv_mul_cancel₀ (ht' _)]

/-- **`D [E | R] T` determines `E` and `R`** for nonzero weights. -/
theorem tlsWeighted_injective {d : m → ℝ} {t : n ⊕ k → ℝ} (hd : ∀ i, d i ≠ 0)
    (ht : ∀ j, t j ≠ 0) {E E' : Matrix m n 𝕜} {R R' : Matrix m k 𝕜}
    (h : tlsWeighted d t E R = tlsWeighted d t E' R') : E = E' ∧ R = R' := by
  have hd' : ∀ i, (d i : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (hd i)
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  refine fromCols_inj ?_
  ext i j
  have := congrFun (congrFun h i) j
  simp only [tlsWeighted, mul_diagonal, diagonal_mul] at this
  exact mul_left_cancel₀ (hd' i) (mul_right_cancel₀ (ht' j) this)

end Defs

/-! ### The weighted distance to a hyperplane -/

section Hyperplane

/-- **The weighted distance to a hyperplane** ([golub2013matrix] §6.3.3, "`δ_i` is the square of
the distance from `[a_i; b_i]` to the nearest point in `P_x` … measured by `‖z‖ = ‖Tz‖₂`"): for
nonzero weights `t`, a normal `ν ≠ 0` and a point `q`,
`⨅_{ν ⬝ w = 0} ‖T (q − w)‖₂² = (ν ⬝ q)² / ∑ (ν_j / t_j)²`, attained at
`w = q − λ T⁻² ν`, `λ = (ν ⬝ q) / ∑ (ν_j / t_j)²`. The lower bound is Cauchy–Schwarz on
`ν ⬝ q = ∑ (ν_j / t_j) (t_j (q_j − w_j))`. With `ν = [x; −1]`, `q = [a_i; b_i]` this is
`δ_i = |a_iᵀ x − b_i|² / (xᵀ T₁⁻² x + t_{n+1}⁻²)`. -/
theorem iInf_sq_norm_diagonal_mulVec_sub_hyperplane {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ι → ℝ} (ht : ∀ j, t j ≠ 0) {ν : ι → ℝ} (hν : ν ≠ 0) (q : ι → ℝ) :
    (⨅ w : {w : ι → ℝ // ν ⬝ᵥ w = 0},
        ‖(WithLp.toLp 2 (diagonal t *ᵥ (q - w.1)) : EuclideanSpace ℝ ι)‖ ^ 2) =
      (ν ⬝ᵥ q) ^ 2 / ∑ j, (ν j / t j) ^ 2 ∧
    ∃ w : ι → ℝ, ν ⬝ᵥ w = 0 ∧
      ‖(WithLp.toLp 2 (diagonal t *ᵥ (q - w)) : EuclideanSpace ℝ ι)‖ ^ 2 =
        (ν ⬝ᵥ q) ^ 2 / ∑ j, (ν j / t j) ^ 2 := by
  have hnorm : ∀ w : ι → ℝ, ‖(WithLp.toLp 2 (diagonal t *ᵥ (q - w)) : EuclideanSpace ℝ ι)‖ ^ 2 =
      ∑ j, (t j * (q j - w j)) ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Real.norm_eq_abs, sq_abs]
      simp [mulVec_diagonal]
  set s := ∑ j, (ν j / t j) ^ 2 with hs
  have hs0 : 0 < s := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hν
    exact lt_of_lt_of_le (by have := div_ne_zero hj (ht j); positivity)
      (Finset.single_le_sum (fun i _ => sq_nonneg (ν i / t i)) (Finset.mem_univ j))
  -- the lower bound
  have hlow : ∀ w : ι → ℝ, ν ⬝ᵥ w = 0 → (ν ⬝ᵥ q) ^ 2 / s ≤ ∑ j, (t j * (q j - w j)) ^ 2 :=
    fun w hw => by
    have e : ν ⬝ᵥ q = ∑ j, ν j / t j * (t j * (q j - w j)) := by
      have : ν ⬝ᵥ q = ν ⬝ᵥ (q - w) := by rw [dotProduct_sub, hw, sub_zero]
      rw [this, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Pi.sub_apply]
        field_simp [ht j]
    rw [div_le_iff₀ hs0, e, mul_comm]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- the minimizer
  set lam := (ν ⬝ᵥ q) / s
  set w₀ : ι → ℝ := fun j => q j - lam * ν j / t j ^ 2
  have hw₀ : ν ⬝ᵥ w₀ = 0 := by
    have : ν ⬝ᵥ w₀ = ν ⬝ᵥ q - lam * s := by
      simp only [w₀, dotProduct, mul_sub, Finset.sum_sub_distrib, hs, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by field_simp [ht j]
    rw [this, div_mul_cancel₀ _ hs0.ne', sub_self]
  have hval : ∑ j, (t j * (q j - w₀ j)) ^ 2 = (ν ⬝ᵥ q) ^ 2 / s := by
    have : ∑ j, (t j * (q j - w₀ j)) ^ 2 = lam ^ 2 * s := by
      rw [hs, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [w₀]
        field_simp [ht j]
        ring
    rw [this, div_pow, sq s]
    field_simp
  refine ⟨le_antisymm ?_ ?_, w₀, hw₀, by rw [hnorm, hval]⟩
  · refine (ciInf_le ⟨0, fun _ ⟨w, hw⟩ => hw ▸ sq_nonneg _⟩ ⟨w₀, hw₀⟩).trans_eq ?_
    rw [hnorm, hval]
  · have : Nonempty {w : ι → ℝ // ν ⬝ᵥ w = 0} := ⟨⟨0, by simp⟩⟩
    exact le_ciInf fun w => by rw [hnorm]; exact hlow w.1 w.2

end Hyperplane

/-! ### One right-hand side -/

section SingleRHS

open scoped Matrix.Norms.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {d : m → ℝ} {t : n ⊕ Unit → ℝ} {A : Matrix m n 𝕜} {b : m → 𝕜}

/-- `(u vᴴ) w = (vᴴ w) u`, entrywise. -/
private theorem vecMulVec_mulVec_apply {ι κ : Type*} [Fintype κ] (u : ι → 𝕜) (v w : κ → 𝕜)
    (i : ι) : (vecMulVec u v *ᵥ w) i = u i * (v ⬝ᵥ w) := by
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

/-- **Every feasible perturbation leaves a null vector with nonzero last entry**: if
`ran (b + r) ⊆ ran (A + E)`, then `C + D [E | r] T` annihilates a unit vector `w` with
`w_last ≠ 0` — namely `T⁻¹ [x; −1]` normalized, for `(A + E) x = b + r` ((6.3.5)). -/
private theorem exists_null_of_range_le (ht : ∀ j, t j ≠ 0)
    {E : Matrix m n 𝕜} {R : Matrix m Unit 𝕜}
    (h : LinearMap.range (replicateCol Unit b + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ∃ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 ∧
      w (Sum.inr ()) ≠ 0 ∧
      (tlsWeighted d t A (replicateCol Unit b) + tlsWeighted d t E R) *ᵥ w = 0 := by
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  obtain ⟨x', hx'⟩ := h ⟨fun _ => 1, rfl⟩
  simp only [mulVecLin_apply] at hx'
  set v : n ⊕ Unit → 𝕜 := Sum.elim (fun j => x' j / (t (Sum.inl j) : 𝕜))
    (fun _ => -1 / (t (Sum.inr ()) : 𝕜)) with hv
  have hv0 : v (Sum.inr ()) ≠ 0 := by
    simp [hv, ht' (Sum.inr ())]
  have hnull : (tlsWeighted d t A (replicateCol Unit b) + tlsWeighted d t E R) *ᵥ v = 0 := by
    rw [← tlsWeighted_add]
    funext i
    rw [tlsWeighted_mulVec]
    have e1 : (fun j => (t (Sum.inl j) : 𝕜) * v (Sum.inl j)) = x' := funext fun j => by
      simp [hv, mul_div_cancel₀ _ (ht' (Sum.inl j))]
    have e2 : (fun j : Unit => (t (Sum.inr j) : 𝕜) * v (Sum.inr j)) = -fun _ => 1 :=
      funext fun j => by simp [hv, mul_div_cancel₀ _ (ht' (Sum.inr ()))]
    rw [e1, e2, hx', mulVec_neg, Pi.neg_apply, add_neg_cancel, mul_zero]
    rfl
  have hvn : ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    apply hv0
    have := congrArg (fun z : EuclideanSpace 𝕜 (n ⊕ Unit) => z (Sum.inr ())) h0
    simpa using this
  refine ⟨(‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) • v, ?_, ?_, ?_⟩
  · rw [WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
      inv_mul_cancel₀ hvn]
  · simp [hv0, hvn]
  · rw [mulVec_smul, hnull, smul_zero]

/-- **The lower bound**: a feasible perturbation `ΔC = D [E | r] T` has a unit vector `w` with
`w_last ≠ 0` and `‖C w‖ ≤ ‖ΔC‖_F` — `C w = −ΔC w` — so `σ_min(C) ≤ ‖ΔC‖_F`. -/
private theorem exists_norm_mulVec_le_of_range_le (ht : ∀ j, t j ≠ 0)
    {E : Matrix m n 𝕜} {R : Matrix m Unit 𝕜}
    (h : LinearMap.range (replicateCol Unit b + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ∃ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 ∧
      w (Sum.inr ()) ≠ 0 ∧
      ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) : EuclideanSpace 𝕜 m)‖ ≤
        ‖tlsWeighted d t E R‖ := by
  obtain ⟨w, hw, hα, hnull⟩ := exists_null_of_range_le (A := A) ht h
  refine ⟨w, hw, hα, ?_⟩
  rw [add_mulVec, add_eq_zero_iff_eq_neg] at hnull
  rw [hnull, WithLp.toLp_neg, norm_neg]
  exact (frobenius_norm_mulVec_le _ w).trans_eq (by rw [hw, mul_one])

/-- The least singular value bounds every feasible perturbation. -/
private theorem iInf_colSingularValues_le_of_range_le (ht : ∀ j, t j ≠ 0)
    {E : Matrix m n 𝕜} {R : Matrix m Unit 𝕜}
    (h : LinearMap.range (replicateCol Unit b + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j ≤ ‖tlsWeighted d t E R‖ := by
  obtain ⟨w, hw, -, hle⟩ := exists_norm_mulVec_le_of_range_le (A := A) ht h
  have := iInf_colSingularValues_mul_norm_le (tlsWeighted d t A (replicateCol Unit b))
    (WithLp.toLp 2 w)
  rw [hw, mul_one, toEuclideanLin_toLp] at this
  exact this.trans hle

/-- **The rank-one perturbation of a unit vector is feasible**: for `‖w‖ = 1` with
`α = w_last ≠ 0`, the pair `(E, r)` with `D [E | r] T = −C w wᴴ` makes `C + D [E | r] T`
annihilate `w`, hence `(A + E) x = b + r` for `x = −T₁ z / (t_{n+1} α)`, `w = [z; α]`. -/
private theorem exists_rankOne_perturbation (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    {w : n ⊕ Unit → 𝕜} (hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1)
    (hα : w (Sum.inr ()) ≠ 0) :
    ∃ (E : Matrix m n 𝕜) (R : Matrix m Unit 𝕜),
      tlsWeighted d t E R = -vecMulVec (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) (star w) ∧
      (A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) * w (Sum.inl j)) /
        ((t (Sum.inr ()) : 𝕜) * w (Sum.inr ()))) = replicateCol Unit b + R := by
  have hd' : ∀ i, (d i : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (hd i)
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  set C := tlsWeighted d t A (replicateCol Unit b)
  set ΔC := -vecMulVec (C *ᵥ w) (star w)
  obtain ⟨E, R, hER⟩ := exists_tlsWeighted_eq hd ht ΔC
  refine ⟨E, R, hER, ?_⟩
  -- `C + ΔC` annihilates `w`
  have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
  have hnull : tlsWeighted d t (A + E) (replicateCol Unit b + R) *ᵥ w = 0 := by
    rw [tlsWeighted_add, hER, add_mulVec]
    funext i
    simp only [ΔC, neg_mulVec, Pi.add_apply, Pi.neg_apply, vecMulVec_mulVec_apply, hww, mul_one,
      Pi.zero_apply]
    exact add_neg_cancel _
  set c : 𝕜 := (t (Sum.inr ()) : 𝕜) * w (Sum.inr ())
  have hc : c ≠ 0 := mul_ne_zero (ht' _) hα
  ext i u
  have hi := congrFun hnull i
  rw [tlsWeighted_mulVec, Pi.zero_apply, mul_eq_zero, or_iff_right (hd' i)] at hi
  have hB : ((replicateCol Unit b + R) *ᵥ fun j => (t (Sum.inr j) : 𝕜) * w (Sum.inr j)) i
      = (replicateCol Unit b + R) i () * c := by
    simp [mulVec, dotProduct, c]
  rw [hB] at hi
  have hA : ((A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) *
      w (Sum.inl j)) / c)) i u = -(((A + E) *ᵥ fun j => (t (Sum.inl j) : 𝕜) *
        w (Sum.inl j)) i) / c := by
    simp only [mul_apply, replicateCol_apply, mulVec, dotProduct, neg_div, Finset.sum_div,
      ← Finset.sum_neg_distrib, mul_div_assoc, mul_neg]
  rw [hA, eq_neg_of_add_eq_zero_left hi, neg_neg, mul_div_cancel_right₀ _ hc]

/-- **The single right-hand side with repeated smallest singular values** ([golub2013matrix]
§6.3.2): with `C = D [A | b] T` and nonzero weights, let `w = [z; α]` be a unit vector with
`‖C w‖ = σ_min(C)` — e.g. the book's last column of `V(:, n+1−p : n+1) Q̃` — and `α ≠ 0`. Then
`x = −T₁ z / (t_{n+1} α)` is a TLS solution, with the perturbation `D [E₀ | r₀] T = −C w wᴴ`:
it is feasible (`(C − C w wᴴ) w = 0`) and has `‖C w wᴴ‖_F = σ_min`, while every feasible
perturbation has a unit null vector `w'` of `C + ΔC` and `‖ΔC‖_F ≥ ‖ΔC w'‖ = ‖C w'‖ ≥ σ_min`. -/
theorem isTLSSolution_of_mem_smallest (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    {w : n ⊕ Unit → 𝕜} (hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace 𝕜 m)‖ = ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j)
    (hα : w (Sum.inr ()) ≠ 0) :
    ∃ E R, IsTLSPerturbation d t A (replicateCol Unit b) E R ∧
      (A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) * w (Sum.inl j)) /
        ((t (Sum.inr ()) : 𝕜) * w (Sum.inr ()))) = replicateCol Unit b + R ∧
      tlsWeighted d t E R = -vecMulVec (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) (star w) := by
  obtain ⟨E, R, hER, hsol⟩ := exists_rankOne_perturbation (A := A) (b := b) hd ht hw hα
  refine ⟨E, R, ⟨?_, fun E' R' h' => ?_⟩, hsol, hER⟩
  · rw [← hsol, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [hER, norm_neg, frobenius_norm_vecMulVec_star, hw, mul_one, hmin]
    exact iInf_colSingularValues_le_of_range_le ht h'

/-- A single-right-hand-side TLS solution, in the book's vector form: `x` with `X = [x]`. -/
theorem isTLSSolution_of_mem_smallest' (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    {w : n ⊕ Unit → 𝕜} (hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace 𝕜 m)‖ = ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j)
    (hα : w (Sum.inr ()) ≠ 0) :
    IsTLSSolution d t A (replicateCol Unit b) (replicateCol Unit fun j =>
      -((t (Sum.inl j) : 𝕜) * w (Sum.inl j)) / ((t (Sum.inr ()) : 𝕜) * w (Sum.inr ()))) :=
  let ⟨E, R, h₁, h₂, _⟩ := isTLSSolution_of_mem_smallest hd ht hw hmin hα
  ⟨E, R, h₁, h₂⟩

/-- **The nongeneric case: no TLS solution** ([golub2013matrix] §6.3.2, "If `α = 0`, then the TLS
problem has no solution"): if every unit `w` with `‖C w‖ = σ_min(C)` has `w_last = 0`, no TLS
perturbation exists, so there is no TLS solution. A TLS perturbation `ΔC` would satisfy
`‖ΔC‖_F ≤ ‖C w‖` for every unit `w` with `w_last ≠ 0` (the rank-one perturbations are feasible),
hence `‖ΔC‖_F ≤ σ_min` by tilting a minimizer `w*` (`w*_last = 0`) towards `e_last`; and its
null vector `w'` has `w'_last ≠ 0` and `σ_min ≤ ‖C w'‖ ≤ ‖ΔC‖_F`, forcing `‖C w'‖ = σ_min`. -/
theorem not_isTLSSolution_of_forall_last_eq_zero (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (h : ∀ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 →
      ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) : EuclideanSpace 𝕜 m)‖ =
        ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j → w (Sum.inr ()) = 0) :
    ¬ ∃ X, IsTLSSolution d t A (replicateCol Unit b) X := by
  rintro ⟨X, E, R, hP, -⟩
  set C := tlsWeighted d t A (replicateCol Unit b)
  set σmin := ⨅ j, C.colSingularValues j
  have hnrm : ∀ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 (C *ᵥ w) : EuclideanSpace 𝕜 m)‖ =
      ‖toEuclideanLin C (WithLp.toLp 2 w)‖ := fun w => by rw [toEuclideanLin_toLp]
  -- the upper bound `‖ΔC‖_F ≤ σ_min`
  have hup : ‖tlsWeighted d t E R‖ ≤ σmin := by
    obtain ⟨x, hx, hCx⟩ := exists_norm_eq_iInf_colSingularValues C
    set w₀ : n ⊕ Unit → 𝕜 := WithLp.ofLp x
    have hw₀ : ‖(WithLp.toLp 2 w₀ : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 := hx
    have hCw₀ : ‖(WithLp.toLp 2 (C *ᵥ w₀) : EuclideanSpace 𝕜 m)‖ = σmin := by
      rw [hnrm]; exact hCx
    have hlast : w₀ (Sum.inr ()) = 0 := h w₀ hw₀ hCw₀
    set e : n ⊕ Unit → 𝕜 := Pi.single (Sum.inr ()) 1
    set c := ‖(WithLp.toLp 2 (C *ᵥ e) : EuclideanSpace 𝕜 m)‖
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε : ℝ := δ / (c + 1) with hε
    have hε0 : 0 < ε := div_pos hδ (by positivity)
    set u : n ⊕ Unit → 𝕜 := w₀ + (ε : 𝕜) • e
    have hu_inl : ∀ j, u (Sum.inl j) = w₀ (Sum.inl j) := fun j => by simp [u, e]
    have hu_inr : u (Sum.inr ()) = (ε : 𝕜) := by
      change w₀ (Sum.inr ()) + (ε : 𝕜) • (Pi.single (Sum.inr ()) (1 : 𝕜) : n ⊕ Unit → 𝕜)
        (Sum.inr ()) = ε
      rw [hlast, zero_add, Pi.single_eq_same, smul_eq_mul, mul_one]
    have hsplit : ∀ z : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ^ 2 =
        ∑ j : n, ‖z (Sum.inl j)‖ ^ 2 + ‖z (Sum.inr ())‖ ^ 2 := fun z => by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      simp
    have hu2 : ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ^ 2 = 1 + ε ^ 2 := by
      have h0 : ‖(WithLp.toLp 2 w₀ : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ^ 2 = 1 := by
        rw [hw₀, one_pow]
      rw [hsplit] at h0 ⊢
      rw [hlast, norm_zero, zero_pow two_ne_zero, add_zero] at h0
      rw [hu_inr, RCLike.norm_ofReal, sq_abs, Finset.sum_congr rfl fun j _ => by rw [hu_inl j],
        h0]
    have hu1 : 1 ≤ ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖ := by
      refine (one_le_sq_iff_one_le_abs _).1 ?_ |>.trans_eq (abs_of_nonneg (norm_nonneg _))
      rw [hu2]; nlinarith
    have hun : ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ≠ 0 := by linarith
    set w := (‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) • u
    have hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 := by
      rw [WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
        inv_mul_cancel₀ hun]
    have hα : w (Sum.inr ()) ≠ 0 := by
      have e1 : w (Sum.inr ()) =
          (‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) * (ε : 𝕜) := by
        rw [← hu_inr]
        rfl
      rw [e1]
      exact mul_ne_zero (inv_ne_zero (RCLike.ofReal_ne_zero.2 hun))
        (RCLike.ofReal_ne_zero.2 hε0.ne')
    obtain ⟨E', R', hE', hsol'⟩ := exists_rankOne_perturbation (A := A) (b := b) hd ht hw hα
    have hfeas : LinearMap.range (replicateCol Unit b + R').mulVecLin ≤
        LinearMap.range (A + E').mulVecLin := by
      rw [← hsol', mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    calc ‖tlsWeighted d t E R‖ ≤ ‖tlsWeighted d t E' R'‖ := hP.norm_le E' R' hfeas
      _ = ‖(WithLp.toLp 2 (C *ᵥ w) : EuclideanSpace 𝕜 m)‖ := by
          rw [hE', norm_neg, frobenius_norm_vecMulVec_star, hw, mul_one]
      _ ≤ ‖(WithLp.toLp 2 (C *ᵥ u) : EuclideanSpace 𝕜 m)‖ := by
          rw [show w = (‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) • u from rfl,
            mulVec_smul, WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
          exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hu1)
      _ ≤ σmin + ε * c := by
          rw [show u = w₀ + (ε : 𝕜) • e from rfl, mulVec_add, mulVec_smul, WithLp.toLp_add,
            WithLp.toLp_smul, ← hCw₀]
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hε0]
      _ ≤ σmin + δ := by
          have hc : 0 ≤ c := norm_nonneg _
          have : ε * c ≤ δ := by
            rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
          linarith
  -- the lower bound, with a null vector whose last entry does not vanish
  obtain ⟨w', hw', hα', hle'⟩ := exists_norm_mulVec_le_of_range_le (A := A) ht hP.range_le
  have hge : σmin ≤ ‖(WithLp.toLp 2 (C *ᵥ w') : EuclideanSpace 𝕜 m)‖ := by
    have := iInf_colSingularValues_mul_norm_le C (WithLp.toLp 2 w')
    rwa [hw', mul_one, ← hnrm] at this
  exact hα' (h w' hw' (le_antisymm (hle'.trans hup) hge))

end SingleRHS

/-! ### The generic condition of Theorem 6.3.1 -/

section Generic

variable {m n k : ℕ}

/-- On a Euclidean space of `Fin (a + b)`, the squared norm splits over the two blocks. -/
private theorem norm_sq_toLp_eq_add {a b : ℕ} (v : Fin (a + b) → 𝕜) :
    ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin (a + b)))‖ ^ 2 =
      ‖(WithLp.toLp 2 fun i => v (Fin.castAdd b i) : EuclideanSpace 𝕜 (Fin a))‖ ^ 2 +
        ‖(WithLp.toLp 2 fun j => v (Fin.natAdd a j) : EuclideanSpace 𝕜 (Fin b))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]

open scoped Matrix.Norms.L2Operator in
/-- **The generic condition makes `V₂₂` invertible** ([golub2013matrix] Theorem 6.3.1, first part
of the proof): let `C = [C₁ | C₂]` (`n` and `k` columns, reindexed to `Fin (n + k)`) have the SVD
`Uᴴ C V = Σ`, and `V₂₂` be the trailing `k × k` block of `V`. If `σ_n(C₁) > σ_{n+1}(C)`
(`0`-based: `C₁.sortedSingularValues (n − 1) > σ n`), then `V₂₂` is invertible. If `V₂₂ x = 0`
with `x ≠ 0`, then `v = V [0; x]` has `v = [V₁₂ x; 0]` and `‖v‖ = ‖x‖`, so
`σ_n(C₁) ‖V₁₂ x‖ ≤ ‖C₁ V₁₂ x‖ = ‖C v‖ = ‖Σ [0; x]‖ ≤ σ_{n+1}(C) ‖x‖ = σ_{n+1}(C) ‖V₁₂ x‖`,
by the least stretch of `C₁` and the ordering of `σ`. -/
theorem isUnit_lowerRightBlock_of_lt {C₁ : Matrix (Fin m) (Fin n) 𝕜}
    {C₂ : Matrix (Fin m) (Fin k) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n + k)) (Fin (n + k)) 𝕜}
    (hC : IsSVD ((fromCols C₁ C₂).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < C₁.sortedSingularValues (n - 1)) :
    IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) := by
  set C := (fromCols C₁ C₂).submatrix id finSumFinEquiv.symm with hCdef
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no leading columns: `σ_n(C₁) = 0`
    subst hn
    have h0 : C₁.sortedSingularValues 0 = 0 :=
      (C₁.sortedSingularValues_eq_zero_iff_rank_le 0).2 (by simpa using C₁.rank_le_card_width)
    rw [Nat.zero_sub, h0] at hσ
    exact absurd hσ (not_lt.2 (hC.nonneg 0))
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← mulVec_injective_iff_isUnit]
  suffices hker : ∀ x, V.submatrix (Fin.natAdd n) (Fin.natAdd n) *ᵥ x = 0 → x = 0 from
    fun x y hxy => sub_eq_zero.1 (hker _ (by rw [mulVec_sub, hxy, sub_self]))
  intro x hx
  by_contra hx0
  have hxpos : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin k))‖ := by
    refine norm_pos_iff.2 fun h => hx0 ?_
    exact congrArg WithLp.ofLp h
  set e : Fin (n + k) → 𝕜 := Fin.append (0 : Fin n → 𝕜) x with he
  set v : Fin (n + k) → 𝕜 := V *ᵥ e with hv
  have hv_right : ∀ j, v (Fin.natAdd n j) = 0 := fun j => by
    have := congrFun hx j
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at this
    simp only [hv, he, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    exact this
  set y : Fin n → 𝕜 := fun i => v (Fin.castAdd k i) with hy
  -- the norms of `x`, `e`, `v` and `y` agree
  have hne : ‖(WithLp.toLp 2 e : EuclideanSpace 𝕜 (Fin (n + k)))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin k))‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_toLp_eq_add]
    have h1 : (fun i => e (Fin.castAdd k i)) = 0 := funext fun i => by simp [he]
    have h2 : (fun j => e (Fin.natAdd n j)) = x := funext fun j => by simp [he]
    rw [h1, h2, show (WithLp.toLp 2 (0 : Fin n → 𝕜) : EuclideanSpace 𝕜 (Fin n)) = 0 from rfl,
      norm_zero, zero_pow two_ne_zero, zero_add]
  have hnv : ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin (n + k)))‖ =
      ‖(WithLp.toLp 2 e : EuclideanSpace 𝕜 (Fin (n + k)))‖ :=
    norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_right e
  have hny : ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin n))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin (n + k)))‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_toLp_eq_add]
    have h3 : (fun j => v (Fin.natAdd n j)) = 0 := funext hv_right
    rw [h3, show (WithLp.toLp 2 (0 : Fin k → 𝕜) : EuclideanSpace 𝕜 (Fin k)) = 0 from rfl,
      norm_zero, zero_pow two_ne_zero, add_zero]
  -- `C v = C₁ y`
  have hCv : C *ᵥ v = C₁ *ᵥ y := by
    funext r
    simp only [hCdef, mulVec, dotProduct, Fin.sum_univ_add, submatrix_apply, id_eq,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl,
      fromCols_apply_inr, hv_right, mul_zero, Finset.sum_const_zero, add_zero, hy]
  -- `C v = U Σ e`
  have hCV : C * V = U * rectDiagonal fun i => ((σ i : ℝ) : 𝕜) := by
    rw [← hC.star_mul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem hC.mem_unitaryGroup_left, Matrix.one_mul]
  -- `Σ e` only sees the entries from `n` on
  set τ : ℕ → 𝕜 := fun i => if n ≤ i then ((σ i : ℝ) : 𝕜) else 0 with hτ
  have hSe : (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin (n + k)) 𝕜) *ᵥ e =
      (rectDiagonal τ : Matrix (Fin m) (Fin (n + k)) 𝕜) *ᵥ e := by
    funext r
    by_cases hr : (r : ℕ) < n + k
    · rw [rectDiagonal_mulVec _ _ _ hr, rectDiagonal_mulVec _ _ _ hr]
      by_cases hrn : n ≤ (r : ℕ)
      · simp [hτ, hrn]
      · have : e ⟨r, hr⟩ = 0 := by
          have := Fin.append_left (0 : Fin n → 𝕜) x ⟨r, by omega⟩
          simpa [he, Fin.castAdd] using this
        rw [this, mul_zero, mul_zero]
    · rw [rectDiagonal_mulVec_of_le _ _ _ (by omega), rectDiagonal_mulVec_of_le _ _ _ (by omega)]
  have hτle : ‖(rectDiagonal τ : Matrix (Fin m) (Fin (n + k)) 𝕜)‖ ≤ σ n := by
    rw [l2_opNorm_rectDiagonal]
    refine Real.iSup_le (fun i => ?_) (hC.nonneg n)
    simp only [hτ]
    split_ifs with hi
    · rw [RCLike.norm_ofReal, abs_of_nonneg (hC.nonneg _)]
      exact hC.antitone hi
    · rw [norm_zero]
      exact hC.nonneg n
  have hupper : ‖(WithLp.toLp 2 (C₁ *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ≤
      σ n * ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin n))‖ := by
    rw [← hCv, hv, mulVec_mulVec, hCV, ← mulVec_mulVec,
      norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_left, hSe, hny, hnv,
      ← toEuclideanLin_toLp]
    exact (norm_toEuclideanLin_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right hτle (norm_nonneg _))
  have hlower := iInf_colSingularValues_mul_norm_le C₁ (WithLp.toLp 2 y)
  rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin, toEuclideanLin_toLp]
    at hlower
  have hypos : 0 < ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin n))‖ := by
    rw [hny, hnv, hne]
    exact hxpos
  have := (mul_le_mul_iff_left₀ hypos).1 (hlower.trans hupper)
  linarith

end Generic

/-! ### Theorem 6.3.1: several right-hand sides -/

section Feasible

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- A range inclusion `ran N ⊆ ran M` is the solvability of `M X = N`. -/
private theorem exists_mul_eq_of_range_le {M : Matrix m n 𝕜} {N : Matrix m k 𝕜}
    (h : LinearMap.range N.mulVecLin ≤ LinearMap.range M.mulVecLin) : ∃ X, M * X = N := by
  classical
  have hc : ∀ j, ∃ x, M *ᵥ x = N *ᵥ Pi.single j 1 := fun j => by
    obtain ⟨x, hx⟩ := h (LinearMap.mem_range_self N.mulVecLin (Pi.single j 1))
    exact ⟨x, hx⟩
  choose x hx using hc
  refine ⟨of fun i j => x j i, ?_⟩
  ext r j
  have := congrFun (hx j) r
  rw [mulVec_single_one, col_apply] at this
  rw [← this]
  rfl

/-- A solvable problem has a weighted matrix of rank at most the number of unknowns:
`[M | M X] = M [1 | X]`. -/
private theorem rank_tlsWeighted_le_of_mul_eq {d : m → ℝ} {t : n ⊕ k → ℝ} {M : Matrix m n 𝕜}
    {N : Matrix m k 𝕜} {X : Matrix n k 𝕜} (h : M * X = N) :
    (tlsWeighted d t M N).rank ≤ Fintype.card n := by
  have hMX : fromCols M N = M * fromCols 1 X := by rw [mul_fromCols, Matrix.mul_one, h]
  rw [tlsWeighted, hMX]
  calc _ ≤ (diagonal (fun i => (d i : 𝕜)) * (M * fromCols 1 X)).rank := rank_mul_le_left _ _
    _ ≤ (M * fromCols 1 X).rank := rank_mul_le_right _ _
    _ ≤ M.rank := rank_mul_le_left _ _
    _ ≤ Fintype.card n := rank_le_card_width M

/-- The matrix `T⁻¹ [X; −1]` of [golub2013matrix] (6.3.5). -/
private noncomputable def tlsNull (t : n ⊕ k → ℝ) (X : Matrix n k 𝕜) : Matrix (n ⊕ k) k 𝕜 :=
  fromRows (diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X)
    (-diagonal fun j => (t (Sum.inr j) : 𝕜)⁻¹)

/-- `D [E | R] T T⁻¹ [X; −1] = D (E X − R)`. -/
private theorem tlsWeighted_mul_tlsNull {d : m → ℝ} {t : n ⊕ k → ℝ} (ht : ∀ j, t j ≠ 0)
    (E : Matrix m n 𝕜) (R : Matrix m k 𝕜) (X : Matrix n k 𝕜) :
    tlsWeighted d t E R * tlsNull t X = diagonal (fun i => (d i : 𝕜)) * (E * X - R) := by
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  have hT : diagonal (fun j => (t j : 𝕜)) * tlsNull t X = fromRows X (-1) := by
    ext (i | i) j
    · simp [tlsNull, mul_inv_cancel_left₀ (ht' _)]
    · by_cases hij : i = j
      · subst hij
        simp [tlsNull, ht' (Sum.inr i)]
      · simp [tlsNull, hij]
  rw [tlsWeighted, Matrix.mul_assoc, hT, Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_neg,
    Matrix.mul_one, ← sub_eq_add_neg]

/-- **[golub2013matrix] (6.3.5)**: `E X = R` iff `D [E | R] T` annihilates `T⁻¹ [X; −1]`. -/
private theorem mul_eq_iff_tlsWeighted_mul_tlsNull_eq_zero {d : m → ℝ} {t : n ⊕ k → ℝ}
    (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0) {E : Matrix m n 𝕜} {R : Matrix m k 𝕜}
    {X : Matrix n k 𝕜} : E * X = R ↔ tlsWeighted d t E R * tlsNull t X = 0 := by
  rw [tlsWeighted_mul_tlsNull ht]
  constructor
  · intro h
    rw [h, sub_self, Matrix.mul_zero]
  · intro h
    rw [← sub_eq_zero]
    ext i j
    have := congrFun (congrFun h i) j
    rw [diagonal_mul, zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (RCLike.ofReal_ne_zero.2 (hd i))

end Feasible

section Theorem631

open scoped Matrix.Norms.Frobenius

variable {m n k : ℕ} {d : Fin m → ℝ} {t : Fin n ⊕ Fin k → ℝ} {A : Matrix (Fin m) (Fin n) 𝕜}
  {B : Matrix (Fin m) (Fin k) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin (n + k)) (Fin (n + k)) 𝕜}

/-- Reindexing the columns of a left factor moves to the rows of the right factor. -/
private theorem submatrix_id_mul_eq {l p q r : Type*} [Fintype p] [Fintype q] (M : Matrix l p 𝕜)
    (e : q ≃ p) (N : Matrix q r 𝕜) : M.submatrix id e * N = M * N.submatrix e.symm id := by
  ext i j
  simp only [mul_apply, submatrix_apply, id_eq]
  exact Fintype.sum_equiv e _ _ fun x => by rw [Equiv.symm_apply_apply]

/-- The consequences of the generic condition `σ_n(C₁) > σ_{n+1}(C)` of [golub2013matrix]
Theorem 6.3.1: `1 ≤ n ≤ m`, the gap `σ_{n+1}(C) < σ_n(C)` (column interlacing,
`Matrix.sortedSingularValues_fromCols_left_le`), and the invertibility of `V₂₂`. -/
private theorem generic_facts
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1)) :
    0 < n ∧ n ≤ m ∧ σ n < σ (n - 1) ∧ IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) := by
  have hlt : n - 1 < min m n := by
    by_contra hle
    rw [(tlsWeighted d t A B).toCols₁.sortedSingularValues_eq_zero_of_min_le
      (by simpa using not_lt.1 hle)] at hσ
    exact absurd hσ (not_lt.2 (hC.nonneg n))
  have hC' : IsSVD ((fromCols (tlsWeighted d t A B).toCols₁
      (tlsWeighted d t A B).toCols₂).submatrix id finSumFinEquiv.symm) U σ V := by
    rwa [fromCols_toCols]
  refine ⟨by omega, by omega, ?_, isUnit_lowerRightBlock_of_lt hC' hσ⟩
  have h1 : σ (n - 1) = (tlsWeighted d t A B).sortedSingularValues (n - 1) := by
    rw [hC.singularValues_eq (by omega) (by omega)]
    exact congrFun (sortedSingularValues_submatrix_equiv (tlsWeighted d t A B) (Equiv.refl _)
      finSumFinEquiv.symm) _
  have h2 := sortedSingularValues_fromCols_left_le (tlsWeighted d t A B).toCols₁
    (tlsWeighted d t A B).toCols₂ (n - 1)
  rw [fromCols_toCols] at h2
  linarith

/-- **The null space of a truncated SVD** ([golub2013matrix] proof of Theorem 6.3.1, "the
nullspace of … is the range of `[V₁₂; V₂₂]`"): if `σ_0, …, σ_{n-1}` are nonzero and `n ≤ m`,
then `C_n Y = 0` iff the columns of `Y` lie in the span of the last `k` columns `V₂` of `V`, i.e.
`Y = V₂ V₂ᴴ Y`. -/
private theorem svdTruncation_mul_eq_zero_iff {M : Matrix (Fin m) (Fin (n + k)) 𝕜}
    (hC : IsSVD M U σ V) (hnm : n ≤ m) (hpos : ∀ i < n, σ i ≠ 0) {p : Type*}
    (Y : Matrix (Fin (n + k)) p 𝕜) :
    svdTruncation U σ V n * Y = 0 ↔
      Y = V.submatrix id (Fin.natAdd n) * ((V.submatrix id (Fin.natAdd n))ᴴ * Y) := by
  have hVV : star V * V = 1 := mem_unitaryGroup_iff'.1 hC.mem_unitaryGroup_right
  have hVV' : V * star V = 1 := mem_unitaryGroup_iff.1 hC.mem_unitaryGroup_right
  have hUU : star U * U = 1 := mem_unitaryGroup_iff'.1 hC.mem_unitaryGroup_left
  have hCV : svdTruncation U σ V n * V =
      U * (rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0) := by
    rw [svdTruncation, Matrix.mul_assoc, hVV, Matrix.mul_one]
  -- `C_n V₂ = 0`
  have hSig : ((rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0 :
      Matrix (Fin m) (Fin (n + k)) 𝕜)).submatrix id (Fin.natAdd n) = 0 := by
    ext i j
    simp only [submatrix_apply, id_eq, rectDiagonal_apply, Fin.val_natAdd, zero_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hCV₂ : svdTruncation U σ V n * V.submatrix id (Fin.natAdd n) = 0 := by
    change (svdTruncation U σ V n * V).submatrix id (Fin.natAdd n) = 0
    rw [hCV]
    change U * ((rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0 :
      Matrix (Fin m) (Fin (n + k)) 𝕜)).submatrix id (Fin.natAdd n) = 0
    rw [hSig, Matrix.mul_zero]
  constructor
  · intro h
    have hZ : (rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0 :
        Matrix (Fin m) (Fin (n + k)) 𝕜) * (star V * Y) = 0 := by
      have := congrArg (star U * ·) h
      rw [svdTruncation] at this
      simpa only [← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_zero] using this
    have hlead : ∀ (i : Fin n) (j : p), (star V * Y) (Fin.castAdd k i) j = 0 := by
      intro i j
      have := congrFun (congrFun hZ ⟨i, lt_of_lt_of_le i.isLt hnm⟩) j
      rw [mul_apply, Finset.sum_eq_single (Fin.castAdd k i) (fun b _ hb => by
          rw [rectDiagonal_apply, ite_eq_right (fun h => hb (Fin.ext h.symm)), zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), rectDiagonal_apply,
        ite_eq_left (show ((⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m) : ℕ) = Fin.castAdd k i
          from rfl), ite_eq_left i.isLt, zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left (RCLike.ofReal_ne_zero.2 (hpos i i.isLt))
    have hY : Y = V * (star V * Y) := by rw [← Matrix.mul_assoc, hVV', Matrix.one_mul]
    conv_lhs => rw [hY]
    ext r j
    rw [mul_apply, mul_apply, Fin.sum_univ_add]
    simp only [hlead, mul_zero, Finset.sum_const_zero, zero_add]
    rfl
  · intro h
    rw [h, ← Matrix.mul_assoc, hCV₂, Matrix.zero_mul]

/-- **Reading off `X`** ([golub2013matrix] proof of Theorem 6.3.1): with `V₂₂` invertible,
`T⁻¹ [X; −1] = V₂ S` for some `S` iff `X = −T₁ V₁₂ V₂₂⁻¹ T₂⁻¹` (and then `S = −V₂₂⁻¹ T₂⁻¹`). -/
private theorem exists_eq_mul_iff (ht : ∀ j, t j ≠ 0)
    (hV : IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n))) (X : Matrix (Fin n) (Fin k) 𝕜) :
    (∃ S, (tlsNull t X).submatrix finSumFinEquiv.symm id = V.submatrix id (Fin.natAdd n) * S) ↔
      X = -(diagonal (fun j => (t (Sum.inl j) : 𝕜)) * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
          (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  have hVd := (isUnit_iff_isUnit_det _).1 hV
  have h11 : diagonal (fun j => (t (Sum.inl j) : 𝕜)) *
      diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun j => mul_inv_cancel₀ (ht' _))
  have h11' : diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) *
      diagonal (fun j => (t (Sum.inl j) : 𝕜)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun j => inv_mul_cancel₀ (ht' _))
  have h22 : (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹ =
      diagonal fun j => (t (Sum.inr j) : 𝕜)⁻¹ := inv_eq_left_inv (by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun j => inv_mul_cancel₀ (ht' _)))
  -- the two block rows
  have hrows : ∀ Y Z : Matrix (Fin (n + k)) (Fin k) 𝕜, Y = Z ↔
      Y.submatrix (Fin.castAdd k) id = Z.submatrix (Fin.castAdd k) id ∧
        Y.submatrix (Fin.natAdd n) id = Z.submatrix (Fin.natAdd n) id := by
    intro Y Z
    refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => ?_⟩
    ext r j
    induction r using Fin.addCases with
    | left i => exact congrFun (congrFun h1 i) j
    | right i => exact congrFun (congrFun h2 i) j
  have hW1 : ((tlsNull t X).submatrix finSumFinEquiv.symm id).submatrix (Fin.castAdd k) id =
      diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X := by
    ext i j
    simp [tlsNull]
  have hW2 : ((tlsNull t X).submatrix finSumFinEquiv.symm id).submatrix (Fin.natAdd n) id =
      -diagonal (fun j => (t (Sum.inr j) : 𝕜)⁻¹) := by
    ext i j
    by_cases hij : i = j <;> simp [tlsNull, hij]
  have hsplit : ∀ S : Matrix (Fin k) (Fin k) 𝕜,
      (tlsNull t X).submatrix finSumFinEquiv.symm id = V.submatrix id (Fin.natAdd n) * S ↔
        diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X =
            V.submatrix (Fin.castAdd k) (Fin.natAdd n) * S ∧
          -diagonal (fun j => (t (Sum.inr j) : 𝕜)⁻¹) =
            V.submatrix (Fin.natAdd n) (Fin.natAdd n) * S := fun S => by
    rw [hrows, hW1, hW2]
    rfl
  rw [exists_congr hsplit]
  constructor
  · rintro ⟨S, h1, h2⟩
    have hS : S = -((V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
        (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
      rw [h22]
      calc S = (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
            (V.submatrix (Fin.natAdd n) (Fin.natAdd n) * S) := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul _ hVd, Matrix.one_mul]
        _ = _ := by rw [← h2, Matrix.mul_neg]
    calc X = diagonal (fun j => (t (Sum.inl j) : 𝕜)) *
          (diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X) := by
          rw [← Matrix.mul_assoc, h11, Matrix.one_mul]
      _ = _ := by rw [h1, hS]; simp only [Matrix.mul_neg, Matrix.mul_assoc]
  · intro hX
    refine ⟨-((V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
        (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹), ?_, ?_⟩
    · rw [hX]
      simp only [Matrix.mul_neg, ← Matrix.mul_assoc, h11', Matrix.one_mul]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.one_mul, h22]

/-- Under the generic condition the first `n` singular values are nonzero. -/
private theorem pos_of_generic
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1)) :
    ∀ i < n, σ i ≠ 0 := fun i hi => by
  obtain ⟨-, -, hgap, -⟩ := generic_facts hC hσ
  exact (lt_of_le_of_lt (hC.nonneg n) (lt_of_lt_of_le hgap (hC.antitone (by omega)))).ne'

/-- **The solutions of the truncated problem** ([golub2013matrix] proof of Theorem 6.3.1): if
`C + D [E | R] T` is the truncation `C_n` of the SVD of `C`, then `(A + E) X = B + R` exactly for
`X = −T₁ V₁₂ V₂₂⁻¹ T₂⁻¹`. -/
private theorem add_mul_eq_iff (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : tlsWeighted d t (A + E) (B + R) =
      (svdTruncation U σ V n).submatrix id finSumFinEquiv) (X : Matrix (Fin n) (Fin k) 𝕜) :
    (A + E) * X = B + R ↔
      X = -(diagonal (fun j => (t (Sum.inl j) : 𝕜)) * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
          (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
  obtain ⟨-, hnm, -, hV⟩ := generic_facts hC hσ
  have h22 : (V.submatrix id (Fin.natAdd n))ᴴ * V.submatrix id (Fin.natAdd n) = 1 := by
    rw [conjTranspose_submatrix, ← star_eq_conjTranspose,
      ← submatrix_mul _ _ _ id _ Function.bijective_id,
      mem_unitaryGroup_iff'.1 hC.mem_unitaryGroup_right,
      submatrix_one _ fun a b hab => Fin.ext (by simpa [Fin.ext_iff] using hab)]
  rw [mul_eq_iff_tlsWeighted_mul_tlsNull_eq_zero hd ht, h, submatrix_id_mul_eq,
    svdTruncation_mul_eq_zero_iff hC hnm (pos_of_generic hC hσ), ← exists_eq_mul_iff ht hV]
  constructor
  · intro hY
    exact ⟨_, hY⟩
  · rintro ⟨S, hS⟩
    conv_rhs => rw [hS, ← Matrix.mul_assoc (V.submatrix id (Fin.natAdd n))ᴴ, h22, Matrix.one_mul]
    exact hS

/-- The squared Frobenius norm of `C − C_n` in the notation of the SVD. -/
private theorem frobenius_norm_sub_svdTruncation_sq
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V) :
    ‖(tlsWeighted d t A B).submatrix id finSumFinEquiv.symm - svdTruncation U σ V n‖ ^ 2 =
      ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 := by
  rw [frobenius_norm_sub_svdTruncation hC,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨-, hi⟩ := Finset.mem_Ico.1 hi
  rw [hC.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
    (lt_of_lt_of_le hi (min_le_right _ _))]

/-- Reindexing the columns does not change the Frobenius norm of a weighted matrix. -/
private theorem frobenius_norm_submatrix_finSumFinEquiv (M : Matrix (Fin m) (Fin n ⊕ Fin k) 𝕜) :
    ‖M.submatrix id finSumFinEquiv.symm‖ = ‖M‖ :=
  frobenius_norm_submatrix_equiv M (Equiv.refl _) finSumFinEquiv.symm

/-- `C − (C + ΔC) = −ΔC`, reindexed. -/
private theorem submatrix_sub_tlsWeighted_add (E : Matrix (Fin m) (Fin n) 𝕜)
    (R : Matrix (Fin m) (Fin k) 𝕜) :
    (tlsWeighted d t A B).submatrix id finSumFinEquiv.symm -
        (tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm =
      (-tlsWeighted d t E R).submatrix id finSumFinEquiv.symm := by
  rw [tlsWeighted_add]
  ext i j
  simp

/-- A solvable perturbed problem has a reindexed weighted matrix of rank at most `n`. -/
private theorem rank_submatrix_tlsWeighted_le {E : Matrix (Fin m) (Fin n) 𝕜}
    {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : LinearMap.range (B + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ((tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm).rank ≤ n := by
  obtain ⟨X, hX⟩ := exists_mul_eq_of_range_le h
  rw [show ((tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm).rank =
    (tlsWeighted d t (A + E) (B + R)).rank from
      rank_submatrix _ (Equiv.refl _) finSumFinEquiv.symm]
  simpa using rank_tlsWeighted_le_of_mul_eq (d := d) (t := t) hX

/-- **A feasible perturbation is at least as large as the truncation residual**
([golub2013matrix] proof of Theorem 6.3.1, by Eckart–Young–Mirsky): if `ran (B + R) ⊆ ran (A + E)`
then `C + D [E | R] T` has rank at most `n`, so `∑_{i ≥ n} σ_i² ≤ ‖D [E | R] T‖_F²`. -/
private theorem sum_sq_le_of_range_le
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : LinearMap.range (B + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 ≤ ‖tlsWeighted d t E R‖ ^ 2 := by
  have hEY := sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le
    (C := (tlsWeighted d t A B).submatrix id finSumFinEquiv.symm)
    (rank_submatrix_tlsWeighted_le (d := d) (t := t) h)
  rw [submatrix_sub_tlsWeighted_add, frobenius_norm_submatrix_finSumFinEquiv, norm_neg] at hEY
  refine le_trans (le_of_eq ?_) hEY
  simp only [Fintype.card_fin]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨-, hi⟩ := Finset.mem_Ico.1 hi
  rw [hC.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
    (lt_of_lt_of_le hi (min_le_right _ _))]

/-- The value of a perturbation that truncates: if `C + D [E | R] T = C_n`, then
`‖D [E | R] T‖_F² = ∑_{i ≥ n} σ_i²`. -/
private theorem frobenius_norm_sq_of_tlsWeighted_add_eq
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : tlsWeighted d t (A + E) (B + R) = (svdTruncation U σ V n).submatrix id finSumFinEquiv) :
    ‖tlsWeighted d t E R‖ ^ 2 = ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 := by
  have hER : tlsWeighted d t E R =
      (svdTruncation U σ V n).submatrix id finSumFinEquiv - tlsWeighted d t A B := by
    rw [← h, tlsWeighted_add, add_sub_cancel_left]
  have : svdTruncation U σ V n - (tlsWeighted d t A B).submatrix id finSumFinEquiv.symm =
      (tlsWeighted d t E R).submatrix id finSumFinEquiv.symm := by
    rw [hER]
    ext i j
    simp
  rw [← frobenius_norm_sub_svdTruncation_sq hC, norm_sub_rev, this,
    frobenius_norm_submatrix_finSumFinEquiv]

/-- **The TLS perturbations of Theorem 6.3.1** ([golub2013matrix] Theorem 6.3.1, (6.3.4)): with
`m × (n + k)` data `C = D [A | B] T` (columns reindexed to `Fin (n + k)`), nonzero weights, an SVD
`Uᴴ C V = Σ` and the generic condition `σ_n(C₁) > σ_{n+1}(C)` (`0`-based:
`C₁.sortedSingularValues (n − 1) > σ n`, `C₁` the first `n` columns of `C`), `(E, R)` is a TLS
perturbation exactly when `C + D [E | R] T` is the rank-`n` truncation `C_n = U Σ_n Vᴴ`, i.e.
`D [E | R] T = −U₂ Σ₂ [V₁₂ᴴ | V₂₂ᴴ]`. Every feasible perturbation makes `C + D [E | R] T` of rank
at most `n` ((6.3.5)), so it is at least `‖C − C_n‖_F` by Eckart–Young–Mirsky; the truncation is
feasible since its null space is the range of `[V₁₂; V₂₂]` with `V₂₂` invertible
(`Matrix.isUnit_lowerRightBlock_of_lt`); and it is the only minimizer because the generic condition
separates `σ_n(C) ≥ σ_n(C₁) > σ_{n+1}(C)` (`Matrix.eq_svdTruncation_of_frobenius_norm_sub_sq_le`).
The book's `m ≥ n + k` is not needed. -/
theorem isTLSPerturbation_iff (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜} :
    IsTLSPerturbation d t A B E R ↔
      tlsWeighted d t (A + E) (B + R) = (svdTruncation U σ V n).submatrix id finSumFinEquiv := by
  obtain ⟨-, -, hgap, -⟩ := generic_facts hC hσ
  -- the truncation is feasible
  have hfeas : ∀ {E' : Matrix (Fin m) (Fin n) 𝕜} {R' : Matrix (Fin m) (Fin k) 𝕜},
      tlsWeighted d t (A + E') (B + R') = (svdTruncation U σ V n).submatrix id finSumFinEquiv →
        LinearMap.range (B + R').mulVecLin ≤ LinearMap.range (A + E').mulVecLin := by
    intro E' R' h
    rw [← (add_mul_eq_iff hd ht hC hσ h _).2 rfl, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  obtain ⟨E₀, R₀, h₀⟩ := exists_tlsWeighted_eq hd ht
    ((svdTruncation U σ V n).submatrix id finSumFinEquiv - tlsWeighted d t A B)
  have h₀' : tlsWeighted d t (A + E₀) (B + R₀) =
      (svdTruncation U σ V n).submatrix id finSumFinEquiv := by
    rw [tlsWeighted_add, h₀, add_sub_cancel]
  constructor
  · intro h
    have hle : ‖(tlsWeighted d t A B).submatrix id finSumFinEquiv.symm -
        (tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm‖ ^ 2 ≤
          ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 := by
      rw [submatrix_sub_tlsWeighted_add, frobenius_norm_submatrix_finSumFinEquiv, norm_neg,
        ← frobenius_norm_sq_of_tlsWeighted_add_eq hC h₀']
      exact pow_le_pow_left₀ (norm_nonneg _) (h.norm_le E₀ R₀ (hfeas h₀')) 2
    have hĈ := eq_svdTruncation_of_frobenius_norm_sub_sq_le hC hgap
      (rank_submatrix_tlsWeighted_le h.range_le) hle
    rw [← hĈ]
    ext i j
    simp
  · intro h
    refine ⟨hfeas h, fun E' R' h' => ?_⟩
    have := sum_sq_le_of_range_le hC h'
    rw [← frobenius_norm_sq_of_tlsWeighted_add_eq hC h] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- **[golub2013matrix] Theorem 6.3.1, the perturbation**: under the hypotheses of
`Matrix.isTLSPerturbation_iff` there is exactly one TLS perturbation `(E₀, R₀)`, the one with
`D [E₀ | R₀] T = −U₂ Σ₂ [V₁₂ᴴ | V₂₂ᴴ]` ((6.3.4)); its size is given by
`Matrix.IsTLSPerturbation.frobenius_norm_sq_eq`. -/
theorem existsUnique_isTLSPerturbation (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1)) :
    ∃! ER : Matrix (Fin m) (Fin n) 𝕜 × Matrix (Fin m) (Fin k) 𝕜,
      IsTLSPerturbation d t A B ER.1 ER.2 := by
  obtain ⟨E₀, R₀, h₀⟩ := exists_tlsWeighted_eq hd ht
    ((svdTruncation U σ V n).submatrix id finSumFinEquiv - tlsWeighted d t A B)
  refine ⟨(E₀, R₀), (isTLSPerturbation_iff hd ht hC hσ).2 (by rw [tlsWeighted_add, h₀,
    add_sub_cancel]), fun ER h => ?_⟩
  have h' := (isTLSPerturbation_iff hd ht hC hσ).1 h
  rw [tlsWeighted_add] at h'
  obtain ⟨h1, h2⟩ := tlsWeighted_injective hd ht ((eq_sub_of_add_eq' h').trans h₀.symm)
  exact Prod.ext h1 h2

/-- **The size of the TLS perturbation** ([golub2013matrix] proof of Theorem 6.3.1):
`‖D [E₀ | R₀] T‖_F² = ∑_{n ≤ i < min(m, n + k)} σ_i²` (`0`-based; the book's
`σ_{n+1}² + ⋯ + σ_{n+k}²` when `m ≥ n + k`). -/
theorem IsTLSPerturbation.frobenius_norm_sq_eq (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : IsTLSPerturbation d t A B E R) :
    ‖tlsWeighted d t E R‖ ^ 2 = ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 :=
  frobenius_norm_sq_of_tlsWeighted_add_eq hC ((isTLSPerturbation_iff hd ht hC hσ).1 h)

/-- **[golub2013matrix] Theorem 6.3.1, the solution**: under the hypotheses of
`Matrix.existsUnique_isTLSPerturbation`, with `T₁ = diag(t₁, …, t_n)`,
`T₂ = diag(t_{n+1}, …, t_{n+k})` and `V₁₂`, `V₂₂` the blocks of the last `k` columns of `V`, the
unique TLS solution is `X_TLS = −T₁ V₁₂ V₂₂⁻¹ T₂⁻¹`. The null space of `C + D [E₀ | R₀] T = C_n` is
the range of `[V₁₂; V₂₂]`, so `T⁻¹ [X; −1] = [V₁₂; V₂₂] S` and `S = −V₂₂⁻¹ T₂⁻¹`. -/
theorem isTLSSolution_iff_eq (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    (X : Matrix (Fin n) (Fin k) 𝕜) :
    IsTLSSolution d t A B X ↔
      X = -(diagonal (fun j => (t (Sum.inl j) : 𝕜)) * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
          (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
  constructor
  · rintro ⟨E, R, h, hX⟩
    exact (add_mul_eq_iff hd ht hC hσ ((isTLSPerturbation_iff hd ht hC hσ).1 h) X).1 hX
  · intro hX
    obtain ⟨⟨E₀, R₀⟩, h₀, -⟩ := existsUnique_isTLSPerturbation hd ht hC hσ
    exact ⟨E₀, R₀, h₀,
      (add_mul_eq_iff hd ht hC hσ ((isTLSPerturbation_iff hd ht hC hσ).1 h₀) X).2 hX⟩

end Theorem631

/-! ### Orthogonal regression -/

section Regression

variable {m n : ℕ}

/-- **The orthogonal-regression objective** ([golub2013matrix] (6.3.6)): for real data
`A : Matrix (Fin m) (Fin n) ℝ`, `b`, row weights `d` and column weights `t`,
`ψ(x) = ∑ᵢ dᵢ² (aᵢᵀ x − bᵢ)² / (xᵀ T₁⁻² x + t_{n+1}⁻²)`, the weighted sum of the squared
distances `δᵢ` of the points `[aᵢ; bᵢ]` to the hyperplane `{[a; b] : b = xᵀ a}`
(`Matrix.iInf_sq_norm_diagonal_mulVec_sub_hyperplane`). -/
noncomputable def tlsObjective (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, d i ^ 2 * (A i ⬝ᵥ x - b i) ^ 2 /
    (∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2)

/-- `ψ` as a Rayleigh quotient: with `C = D [A | b] T` (columns reindexed to `Fin (n + 1)`) and
`w = T⁻¹ [x; −1]`, `ψ(x) = ‖C w‖² / ‖w‖²`. -/
private theorem tlsObjective_eq (d : Fin m → ℝ) {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    tlsObjective d t A b x =
      ‖(WithLp.toLp 2 (((fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
          (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
            finSumFinEquiv.symm) *ᵥ Fin.snoc (fun j => x j / t (Fin.castSucc j))
              (-1 / t (Fin.last n))) : EuclideanSpace ℝ (Fin m))‖ ^ 2 /
        ‖(WithLp.toLp 2 (Fin.snoc (fun j => x j / t (Fin.castSucc j)) (-1 / t (Fin.last n)) :
          Fin (n + 1) → ℝ) : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by
  rw [tlsObjective, ← Finset.sum_div, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_castSucc (fun j => ‖(WithLp.toLp 2 (Fin.snoc _ _ : Fin (n + 1) → ℝ) :
      EuclideanSpace ℝ (Fin (n + 1))) j‖ ^ 2)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    simp only [mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp only [submatrix_apply, id_eq, Fin.snoc_castSucc, Fin.snoc_last]
    have h1 : ∀ j : Fin n, finSumFinEquiv.symm (Fin.castSucc j) = Sum.inl j := fun j =>
      finSumFinEquiv_symm_apply_castAdd j
    have h2 : finSumFinEquiv.symm (Fin.last n) = Sum.inr (0 : Fin 1) :=
      finSumFinEquiv_symm_apply_natAdd 0
    simp only [h1, h2, fromCols_apply_inl, fromCols_apply_inr, replicateCol_apply,
      diagonal_mul, mul_diagonal]
    rw [show ∑ j : Fin n, d i * A i j * t (Fin.castSucc j) * (x j / t (Fin.castSucc j)) =
      d i * ∑ j, A i j * x j from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by field_simp [ht (Fin.castSucc j)]]
    field_simp [ht (Fin.last n)]
    ring
  · simp only [Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs, sq_abs,
      div_pow, neg_div, neg_sq, one_pow]

/-- **The TLS solution minimizes `ψ`** ([golub2013matrix] (6.3.6), "It can be shown that the TLS
solution `x_TLS` minimizes `ψ(x)`", P6.3.5): with one right-hand side, `m > n`, an SVD
`Uᵀ C V = Σ` of `C = D [A | b] T` and the generic condition `σ_n(C₁) > σ_{n+1}(C)`, the vector
`x_TLS = −T₁ v₁₂ / (t_{n+1} v₂₂)` of Theorem 6.3.1 minimizes `ψ`. Indeed
`ψ(x) = ‖C w‖²/‖w‖² ≥ σ_min(C)²` for `w = T⁻¹ [x; −1]`, and `T⁻¹ [x_TLS; −1]` is a multiple of
the last column of `V`, on which `‖C v‖ = σ_{n+1}(C) = σ_min(C)`; `v₂₂ ≠ 0` is
`Matrix.isUnit_lowerRightBlock_of_lt`. -/
theorem isMinOn_tlsObjective (hmn : n < m) (d : Fin m → ℝ) {t : Fin (n + 1) → ℝ}
    (ht : ∀ j, t j ≠ 0) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
      (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
        finSumFinEquiv.symm) U σ V)
    (hsep : σ n < (diagonal d * A * diagonal fun j => t (Fin.castSucc j)).sortedSingularValues
      (n - 1)) :
    IsMinOn (tlsObjective d t A b) Set.univ fun j =>
      -(t (Fin.castSucc j) * V (Fin.castSucc j) (Fin.last n)) /
        (t (Fin.last n) * V (Fin.last n) (Fin.last n)) := by
  set C := (fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
    (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
      finSumFinEquiv.symm with hCdef
  -- `v₂₂ ≠ 0`
  have hV : V (Fin.last n) (Fin.last n) ≠ 0 := by
    have hu := isUnit_lowerRightBlock_of_lt hC hsep
    rw [isUnit_iff_isUnit_det, det_unique, isUnit_iff_ne_zero] at hu
    exact hu
  set x₀ : Fin n → ℝ := fun j => -(t (Fin.castSucc j) * V (Fin.castSucc j) (Fin.last n)) /
    (t (Fin.last n) * V (Fin.last n) (Fin.last n))
  -- `σ_min(C) = σ n`
  have hmin : ⨅ j, C.colSingularValues j = σ n := by
    rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin, Nat.add_sub_cancel,
      hC.singularValues_eq hmn (Nat.lt_succ_self n)]
  -- the vector of `x₀` is a multiple of the last column of `V`
  set s : ℝ := -1 / (t (Fin.last n) * V (Fin.last n) (Fin.last n))
  have hw₀ : (Fin.snoc (fun j => x₀ j / t (Fin.castSucc j)) (-1 / t (Fin.last n)) :
      Fin (n + 1) → ℝ) = s • fun p => V p (Fin.last n) := by
    funext p
    induction p using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, s]
      field_simp [ht (Fin.last n), hV]
    | cast j =>
      simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul, s, x₀]
      field_simp [ht (Fin.castSucc j), ht (Fin.last n), hV]
  -- on the last column of `V`, `‖C v‖ = σ n` and `‖v‖ = 1`
  have hCV : C * V = U * (star U * C * V) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem hC.mem_unitaryGroup_left, Matrix.one_mul]
  rw [hC.star_mul_mul] at hCV
  have hVcol : (fun p => V p (Fin.last n)) = V *ᵥ Pi.single (Fin.last n) 1 := by
    funext p
    simp [mulVec, dotProduct, Pi.single_apply]
  have hnormv : ‖(WithLp.toLp 2 (fun p => V p (Fin.last n)) : EuclideanSpace ℝ (Fin (n + 1)))‖
      = 1 := by
    rw [hVcol, norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_right]
    simp
  have hnormCv : ‖(WithLp.toLp 2 (C *ᵥ fun p => V p (Fin.last n)) : EuclideanSpace ℝ (Fin m))‖
      = σ n := by
    rw [hVcol, mulVec_mulVec, hCV, ← mulVec_mulVec,
      norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_left, EuclideanSpace.norm_eq]
    rw [Finset.sum_eq_single (⟨n, hmn⟩ : Fin m)]
    · rw [PiLp.toLp_apply, rectDiagonal_mulVec _ _ _ (by simp)]
      simp [Pi.single_apply, Fin.ext_iff, Real.sqrt_sq_eq_abs, abs_of_nonneg (hC.nonneg n)]
    · intro r _ hr
      rw [PiLp.toLp_apply]
      have hrn' : (r : ℕ) ≠ n := fun h => hr (Fin.ext h)
      by_cases hrn : (r : ℕ) < n + 1
      · rw [rectDiagonal_mulVec _ _ _ hrn]
        simp [Fin.ext_iff, hrn']
      · rw [rectDiagonal_mulVec_of_le _ _ _ (by omega), norm_zero, zero_pow two_ne_zero]
    · simp
  have hs : s ≠ 0 := div_ne_zero (by norm_num) (mul_ne_zero (ht _) hV)
  have hψ₀ : tlsObjective d t A b x₀ = σ n ^ 2 := by
    rw [tlsObjective_eq d ht, hw₀, mulVec_smul, WithLp.toLp_smul, WithLp.toLp_smul, norm_smul,
      norm_smul, hnormCv, hnormv, mul_one, mul_pow,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hs))]
  intro x _
  rw [Set.mem_ofPred_eq, hψ₀, tlsObjective_eq d ht]
  set w : Fin (n + 1) → ℝ := Fin.snoc (fun j => x j / t (Fin.castSucc j)) (-1 / t (Fin.last n))
  have hw : 0 < ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) h
    simp [w, ht (Fin.last n)] at this
  have hlow := iInf_colSingularValues_mul_norm_le C (WithLp.toLp 2 w)
  rw [hmin, toEuclideanLin_toLp] at hlow
  rw [le_div_iff₀ (pow_pos hw 2), ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (hC.nonneg n) (norm_nonneg _)) hlow 2

end Regression

end Matrix
