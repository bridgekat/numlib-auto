import NumlibSurface.GolubVanLoan.Chapter07.Section05

/-!
# Golub–Van Loan §7.6: invariant subspace computations

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.6: inverse iteration (7.6.1) and its stopping criterion (7.6.2), the unique
invariant subspace of a leading Schur block (§7.6.2), the `2 × 2` swap that reorders a Schur form,
the bounds around the block-diagonalizing Sylvester equation (7.6.6) and the condition of the
block unit triangular `Y_ij` (§7.6.3), and the Jordan block counts from null space dimensions
(§7.6.5).

## Conventions

Real `Matrix (Fin n) (Fin n) ℝ` where the book is real; complex where eigenvalues are complex (the
unique invariant subspace, stated over `ℂ` with a unitary `Q`, the real orthogonal case being an
instance); inverse iteration over any `RCLike` field. The `∞`-norm of a matrix is the scoped
`Matrix.Norms.Operator` norm and the `∞`-norm of a vector the sup norm of `Fin n → ℝ`; the Frobenius
norm is the scoped `Matrix.Norms.Frobenius` norm.

## Algorithms

Algorithm 7.6.1 (reordering the Schur form) calls chapter 5's `givens` and shared rotation helpers,
and Algorithms 7.6.2–7.6.3 (Bartels–Stewart, block diagonalization) chapter 3's back substitution;
none of these is available yet, so the three algorithms are planned in this section's group and not
written here.

## Not formalized

The SVD heuristic for why one step of inverse iteration suffices; the stability claims of §7.6.2
and the relative error of the Sylvester solve after (7.6.6) (stated with `≈`, no derivation);
Bavely and Stewart's algorithm; the `7 × 7` Jordan-structure example; flop counts.
-/

open Matrix Filter Topology

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.6.1 Selected eigenvectors via inverse iteration -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **(7.6.1), inverse iteration**, over any `RCLike` field (the book states it over `ℝ`): solve
`(A - μ I) z^(k) = q^(k-1)`, `q^(k) = z^(k)/‖z^(k)‖₂`, `λ^(k) = q^(k)ᴴ A q^(k)`, returned as the
pair `(q^(k), λ^(k))`; the solve is `z^(k) = (A - μ I)⁻¹ q^(k-1)`. "Inverse iteration is just the
power method applied to `(A - μI)⁻¹`": for a unit `q₀` and nonsingular `A - μ I` the vectors are the
backbone's `Krylov.inverseIterate` (`inverseIteration_fst`). -/
noncomputable def inverseIteration (A : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜)
    (q₀ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n) × 𝕜
  | 0 => (q₀, inner 𝕜 q₀ (toEuclideanLin A q₀))
  | k + 1 =>
    let z := toEuclideanLin (A - μ • 1)⁻¹ (inverseIteration A μ q₀ k).1
    let q := (‖z‖ : 𝕜)⁻¹ • z
    (q, inner 𝕜 q (toEuclideanLin A q))

/-- The eigenvalue estimate of inverse iteration is the Rayleigh quotient of its vector. -/
theorem inverseIteration_snd (A : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜)
    (q₀ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    (inverseIteration A μ q₀ k).2 =
      inner 𝕜 (inverseIteration A μ q₀ k).1 (toEuclideanLin A (inverseIteration A μ q₀ k).1) := by
  cases k <;> rfl

/-- The operator of `A - μ I` is `A - μ` on `EuclideanSpace`, and for nonsingular `A - μ I` its
ring inverse is the operator of the matrix inverse. -/
private theorem ringInverse_toEuclideanLin_sub {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜}
    (hA : IsUnit (A - μ • 1)) :
    IsUnit (toEuclideanLin A - μ • (1 : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)))) ∧
      Ring.inverse (toEuclideanLin A - μ • (1 : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)))) =
        toEuclideanLin (A - μ • 1)⁻¹ := by
  have hT : toEuclideanLin (A - μ • 1) =
      toEuclideanLin A - μ • (1 : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n))) := by
    rw [map_sub, map_smul, toLpLin_one]
    rfl
  have hdet : IsUnit (A - μ • 1).det := (isUnit_iff_isUnit_det _).1 hA
  have h1 : toEuclideanLin (A - μ • 1)⁻¹ * toEuclideanLin (A - μ • 1) = 1 := by
    rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, Matrix.nonsing_inv_mul _ hdet, toLpLin_one]
    rfl
  have h2 : toEuclideanLin (A - μ • 1) * toEuclideanLin (A - μ • 1)⁻¹ = 1 := by
    rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, Matrix.mul_nonsing_inv _ hdet, toLpLin_one]
    rfl
  rw [← hT]
  have hu : IsUnit (toEuclideanLin (A - μ • 1)) := ⟨⟨_, _, h2, h1⟩, rfl⟩
  refine ⟨hu, ?_⟩
  calc Ring.inverse (toEuclideanLin (A - μ • 1))
      = Ring.inverse (toEuclideanLin (A - μ • 1)) *
          (toEuclideanLin (A - μ • 1) * toEuclideanLin (A - μ • 1)⁻¹) := by rw [h2, mul_one]
    _ = toEuclideanLin (A - μ • 1)⁻¹ := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- For a unit starting vector and nonsingular `A - μ I`, the vectors of inverse iteration (7.6.1)
are the backbone's `Krylov.inverseIterate`, the power method on `(A - μ I)⁻¹`. -/
theorem inverseIteration_fst {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜} (hA : IsUnit (A - μ • 1))
    {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    (inverseIteration A μ q₀ k).1 = Krylov.inverseIterate (toEuclideanLin A) μ q₀ k := by
  rw [Krylov.inverseIterate_eq_powerIterate, (ringInverse_toEuclideanLin_sub hA).2]
  refine Krylov.eq_powerIterate_of_recurrence _ q₀
    (y := fun j => (inverseIteration A μ q₀ j).1) ?_ (fun _ => rfl) k
  change q₀ = _
  rw [hq₀, RCLike.ofReal_one, inv_one, one_smul]

/-- **§7.6.1, the analysis of (7.6.1), rigorous.** Let `A - μ I` be nonsingular, `q^(0) = u + w`
with `u ≠ 0` an eigenvector of `A` for `λ_j` and `w` in the sum of the generalized eigenspaces of
the other eigenvalues (the book's `q^(0) = ∑ β_i x_i` with `β_j ≠ 0`), and suppose `μ` is closer to
`λ_j` than to every other eigenvalue. Then `q^(k)` converges to the direction of `x_j` — the
rescaled `((λ_j - μ)/|λ_j - μ|)^k q^(k)` tends to `u/‖u‖` — and `λ^(k) → λ_j`: "if `μ` is much
closer to an eigenvalue `λ_j` than to the other eigenvalues, then `q^(k)` is rich in the direction
of `x_j`". -/
theorem equation_7_6_1 {A : Matrix (Fin n) (Fin n) 𝕜} {μ l : 𝕜} (hA : IsUnit (A - μ • 1))
    {u w q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (hu : toEuclideanLin A u = l • u)
    (hu0 : u ≠ 0)
    (hw : w ∈ ⨆ ν, ⨆ _ : ν ≠ l, Module.End.maxGenEigenspace (toEuclideanLin A) ν)
    (hdom : ∀ ν, ν ≠ l → Module.End.HasEigenvalue (toEuclideanLin A) ν → ‖l - μ‖ < ‖ν - μ‖)
    (hq : q₀ = u + w) :
    Tendsto (fun k => (((l - μ) / (‖l - μ‖ : 𝕜)) ^ k) • (inverseIteration A μ q₀ k).1) atTop
        (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) ∧
      Tendsto (fun k => (inverseIteration A μ q₀ k).2) atTop (𝓝 l) := by
  have hσ := (ringInverse_toEuclideanLin_sub hA).1
  refine ⟨?_, ?_⟩
  · simp_rw [inverseIteration_fst hA hq₀]
    exact Krylov.tendsto_smul_inverseIterate hσ hu hu0 hw hdom hq
  · simp_rw [inverseIteration_snd, inverseIteration_fst hA hq₀]
    exact Krylov.tendsto_inner_inverseIterate (LinearMap.continuous_of_finiteDimensional _) hσ hu
      hu0 hw hdom hq

end RCLike

section LInfty

open scoped Matrix.Norms.Operator

/-- **(7.6.2) and the sentence after it.** With `r = (A - μ I) q` for a unit `q` and
`E = -r qᵀ`, `(A + E) q = μ q`, and `‖E‖_∞ = ‖r‖_∞ ‖q‖₁ ≤ √n ‖r‖_∞`: the stopping test
`‖r‖_∞ ≤ c u ‖A‖_∞` makes `(μ, q)` an exact eigenpair of a matrix within `√n c u ‖A‖_∞` of `A` (the
book leaves the factor `√n` implicit). -/
theorem equation_7_6_2 {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} {q : Fin n → ℝ}
    (hq : ‖WithLp.toLp 2 q‖ = 1) :
    (A + -vecMulVec ((A - μ • 1) *ᵥ q) q) *ᵥ q = μ • q ∧
      ‖-vecMulVec ((A - μ • 1) *ᵥ q) q‖ = ‖(A - μ • 1) *ᵥ q‖ * ∑ i, |q i| ∧
      ‖-vecMulVec ((A - μ • 1) *ᵥ q) q‖ ≤ √n * ‖(A - μ • 1) *ᵥ q‖ := by
  set r := (A - μ • 1) *ᵥ q
  have hqq : q ⬝ᵥ q = 1 := by
    have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 q)
    rw [hq, one_pow] at h
    rw [dotProduct, h]
    simp [sq]
  have hnorm : ‖-vecMulVec r q‖ = ‖r‖ * ∑ i, |q i| := by
    have e : ∀ i, ∑ j, ‖vecMulVec r q i j‖₊ = ‖r i‖₊ * ∑ j, ‖q j‖₊ := fun i => by
      simp only [vecMulVec_apply, nnnorm_mul, Finset.mul_sum]
    have hr : ‖r‖ = ((Finset.univ.sup fun b => ‖r b‖₊ : NNReal) : ℝ) := Pi.norm_def r
    rw [norm_neg, linfty_opNorm_def, hr]
    simp_rw [e]
    rw [← NNReal.finset_sup_mul, NNReal.coe_mul, NNReal.coe_sum]
    simp [Real.norm_eq_abs]
  have hl1 : ∑ i, |q i| ≤ √n := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) fun i => |q i|
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at hcs
    have hsq : ∑ i, q i ^ 2 = 1 := by rw [← hqq]; simp [dotProduct, sq]
    rw [hsq, mul_one] at hcs
    exact Real.le_sqrt_of_sq_le hcs
  refine ⟨?_, hnorm, ?_⟩
  · rw [add_mulVec, neg_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hqq, one_smul]
    simp only [r, sub_mulVec, smul_mulVec, one_mulVec]
    abel
  · rw [hnorm, mul_comm]
    exact mul_le_mul_of_nonneg_right hl1 (norm_nonneg _)

end LInfty

/-! ### §7.6.2 Orthogonal bases for selected invariant subspaces -/

/-- **§7.6.2.** If `Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]` (`Q` unitary — orthogonal in the book's real setting
— `T₁₁` of size `p`) and `λ(T₁₁) ∩ λ(T₂₂) = ∅`, then the first `p` columns of `Q` span the unique
invariant subspace associated with `λ(T₁₁)`: every `A`-invariant subspace of dimension `p` on which
`A` has only eigenvalues from `λ(T₁₁)` equals it (the book's "(See §7.1.4.)"). -/
theorem invariantSubspace_leading_unique {p q : ℕ} {A Q : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin (p + q)) ℂ) {T₁₁ : Matrix (Fin p) (Fin p) ℂ}
    {T₁₂ : Matrix (Fin p) (Fin q) ℂ} {T₂₂ : Matrix (Fin q) (Fin q) ℂ}
    (hT : (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
      fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdisj : spectrum ℂ T₁₁ ∩ spectrum ℂ T₂₂ = ∅) :
    Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) =
        ⨆ μ ∈ spectrum ℂ T₁₁, Module.End.maxGenEigenspace (toLin' A) μ ∧
      ∀ S ∈ Module.End.invtSubmodule (toLin' A), Module.finrank ℂ S = p →
        (∀ μ ∉ spectrum ℂ T₁₁, ∀ x ∈ S, A *ᵥ x = μ • x → x = 0) →
        S = Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) :=
  span_leading_schurVectors_eq hQ hT (Set.disjoint_iff_inter_eq_empty.2 hdisj)

/-- **§7.6.2, the `2 × 2` swap.** For `T_F = [λ₁ t₁₂; 0 λ₂]`, `x = (t₁₂, λ₂ - λ₁)` satisfies
`T_F x = λ₂ x`; if `Q_D = [c s; -s c]` is a rotation with `(Q_Dᵀ x)₂ = 0` (the output of
`givens(t₁₂, λ₂ - λ₁)`), then `Q_Dᵀ T_F Q_D = [λ₂ t₁₂; 0 λ₁]`: the diagonal is swapped, the `(2, 1)`
entry is zero, and — for this sign convention — the `(1, 2)` entry is `t₁₂` itself (the book's
`±t₁₂`). -/
theorem swap_two_by_two {l₁ l₂ t c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hQx : ((!![c, s; -s, c])ᵀ *ᵥ ![t, l₂ - l₁]) 1 = 0) :
    !![l₁, t; 0, l₂] *ᵥ ![t, l₂ - l₁] = l₂ • ![t, l₂ - l₁] ∧
      (!![c, s; -s, c])ᵀ * !![l₁, t; 0, l₂] * !![c, s; -s, c] = !![l₂, t; 0, l₁] := by
  have h : s * t + c * (l₂ - l₁) = 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using hQx
  constructor
  · ext i
    fin_cases i
    · simp only [mulVec, dotProduct, Fin.sum_univ_two]
      simp
      ring
    · simp only [mulVec, dotProduct, Fin.sum_univ_two]
      simp
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [mul_apply, Fin.sum_univ_two]
      linear_combination (-c) * h + l₂ * hcs
    · simp [mul_apply, Fin.sum_univ_two]
      linear_combination (-s) * h + t * hcs
    · simp [mul_apply, Fin.sum_univ_two]
      linear_combination (-s) * h
    · simp [mul_apply, Fin.sum_univ_two]
      linear_combination c * h + l₁ * hcs

/-! ### §7.6.3 Block diagonalization -/

/-- **§7.6.3, the `Y_ij` updates.** Let `T` be block upper triangular for a block index `b`, let
`i < j` be two blocks and `Z` supported in the block position `(i, j)` (the book's `E_i Z_ij E_jᵀ`).
Then `Y_ij = I + Z` has `Y_ij⁻¹ = I - Z`, and `T̄ = Y_ij⁻¹ T Y_ij = T + T Z - Z T`: read blockwise,
`T̄` agrees with `T` except `T̄_ij = T_ii Z_ij - Z_ij T_jj + T_ij`, `T̄_ik = T_ik - Z_ij T_jk`
(`k > j`) and `T̄_kj = T_ki Z_ij + T_kj` (`k < i`). The one cross term `Z T Z` vanishes because
`T_ji = 0`. -/
theorem blockDiagonalization_update {q : ℕ} {b : Fin n → Fin q} {T Z : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.BlockTriangular b) {i j : Fin q} (hij : i < j)
    (hZ : ∀ r c, Z r c ≠ 0 → b r = i ∧ b c = j) :
    (1 + Z)⁻¹ = 1 - Z ∧ (1 + Z)⁻¹ * T * (1 + Z) = T + T * Z - Z * T := by
  have hZZ : Z * Z = 0 := by
    ext r c
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hij.ne ((hZ s c h2).1.symm.trans (hZ r s h1).2)
  have hZTZ : Z * T * Z = 0 := by
    ext r c
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h2 : Z t c = 0
    · rw [h2, mul_zero]
    rw [mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h1 : Z r s = 0
    · rw [h1, zero_mul, zero_mul]
    have hs := (hZ r s h1).2
    have ht := (hZ t c h2).1
    rw [hT (show b t < b s by rw [hs, ht]; exact hij), mul_zero, zero_mul]
  have hinv : (1 + Z)⁻¹ = 1 - Z := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hZZ]
    abel
  refine ⟨hinv, ?_⟩
  rw [hinv]
  calc (1 - Z) * T * (1 + Z) = T + T * Z - Z * T - Z * T * Z := by noncomm_ring
    _ = T + T * Z - Z * T := by rw [hZTZ, sub_zero]

/-- **(7.6.4)–(7.6.5), the column recurrences of the Sylvester equation** `F Z - Z G = C` for an
upper Hessenberg (in particular upper quasi-triangular) `G`, with `z_k`, `c_k` the columns: in
general column `k` of `F Z - Z G` is `F z_k - ∑_i g_ik z_i`; if `g_{k+1,k} = 0` (or `k` is the last
column) it is `(F - g_kk I) z_k - ∑_{i<k} g_ik z_i` — the triangular recurrence (7.6.4); and if
`g_{k+1,k} ≠ 0` and `g_{k+2,k+1} = 0`, columns `k`, `m = k + 1` are
`(F - g_kk I) z_k - g_mk z_m - ∑_{i<k} g_ik z_i` and
`(F - g_mm I) z_m - g_km z_k - ∑_{i<k} g_im z_i`, the rows of the `2p × 2p` system (7.6.5). As a
matrix is its columns, `F Z - Z G = C` exactly when these equal the columns of `C`. -/
theorem equation_7_6_5 {p r : ℕ} (F : Matrix (Fin p) (Fin p) ℝ) {G : Matrix (Fin r) (Fin r) ℝ}
    (hG : G.IsUpperHessenberg) (Z : Matrix (Fin p) (Fin r) ℝ) :
    (∀ k, (F * Z - Z * G).col k = F *ᵥ Z.col k - ∑ i, G i k • Z.col i) ∧
    (∀ k : Fin r, (∀ m : Fin r, (m : ℕ) = k + 1 → G m k = 0) →
      (F * Z - Z * G).col k = (F - G k k • 1) *ᵥ Z.col k - ∑ i ∈ Finset.Iio k, G i k • Z.col i) ∧
    (∀ k m : Fin r, (m : ℕ) = k + 1 → (∀ m' : Fin r, (m' : ℕ) = m + 1 → G m' m = 0) →
      (F * Z - Z * G).col k =
          (F - G k k • 1) *ᵥ Z.col k - G m k • Z.col m - ∑ i ∈ Finset.Iio k, G i k • Z.col i ∧
        (F * Z - Z * G).col m =
          (F - G m m • 1) *ᵥ Z.col m - G k m • Z.col k - ∑ i ∈ Finset.Iio k, G i m • Z.col i) := by
  rw [isUpperHessenberg_iff_fin] at hG
  have h1 : ∀ k, (F * Z - Z * G).col k = F *ᵥ Z.col k - ∑ i, G i k • Z.col i := by
    intro k
    ext r'
    simp only [col_apply, Matrix.sub_apply, mul_apply, Pi.sub_apply, mulVec, dotProduct,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsub : ∀ k : Fin r, (F - G k k • 1) *ᵥ Z.col k = F *ᵥ Z.col k - G k k • Z.col k := by
    intro k
    rw [sub_mulVec, smul_mulVec, one_mulVec]
  refine ⟨h1, fun k hk => ?_, fun k m hm hm' => ⟨?_, ?_⟩⟩
  · rw [h1, hsub, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic k)) fun i _ hi => ?_,
      ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    · abel
    · simp only [Finset.mem_Iic, not_le] at hi
      rcases Nat.lt_or_ge ((k : ℕ) + 1) i with h | h
      · rw [hG i k h, zero_smul]
      · rw [hk i (by rw [Fin.lt_def] at hi; omega), zero_smul]
  · have hkm : k < m := by rw [Fin.lt_def]; omega
    have hsupp : ∀ i ∉ insert m (Finset.Iic k), G i k • Z.col i = 0 := fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_Iic, not_or, not_le] at hi
      rw [hG i k (by
        have h1 := hi.1
        have h2 := Fin.lt_def.1 hi.2
        have : (i : ℕ) ≠ m := fun h => h1 (Fin.ext h)
        omega), zero_smul]
    rw [h1, hsub, ← Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hsupp i hi,
      Finset.sum_insert (by simp [Finset.mem_Iic, not_le.2 hkm]), ← Finset.Iio_insert,
      Finset.sum_insert Finset.notMem_Iio_self]
    abel
  · have hkm : k < m := by rw [Fin.lt_def]; omega
    have hsupp : ∀ i ∉ insert m (Finset.Iic k), G i m • Z.col i = 0 := fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_Iic, not_or, not_le] at hi
      have h1 := hi.1
      have h2 := Fin.lt_def.1 hi.2
      have : (i : ℕ) ≠ m := fun h => h1 (Fin.ext h)
      rcases Nat.lt_or_ge ((m : ℕ) + 1) i with h | h
      · rw [hG i m h, zero_smul]
      · rw [hm' i (by omega), zero_smul]
    rw [h1, hsub, ← Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hsupp i hi,
      Finset.sum_insert (by simp [Finset.mem_Iic, not_le.2 hkm]), ← Finset.Iio_insert,
      Finset.sum_insert Finset.notMem_Iio_self]
    abel

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **The two precise claims around (7.6.6).** `sep(T_ii, T_jj) ≤ min_{λ ∈ λ(T_ii), μ ∈ λ(T_jj)}
|λ - μ|`, and if `Z` solves (7.6.6) `T_ii Z - Z T_jj = -T_ij` then `‖Z‖_F ≤ ‖T_ij‖_F /
sep(T_ii, T_jj)`. -/
theorem equation_7_6_6 {p q : ℕ} (Tii : Matrix (Fin p) (Fin p) ℂ) (Tjj : Matrix (Fin q) (Fin q) ℂ)
    (Tij : Matrix (Fin p) (Fin q) ℂ) :
    (∀ μ ∈ spectrum ℂ Tii, ∀ ν ∈ spectrum ℂ Tjj, sep Tii Tjj ≤ ‖μ - ν‖) ∧
      (0 < sep Tii Tjj → ∀ Z : Matrix (Fin p) (Fin q) ℂ, Tii * Z - Z * Tjj = -Tij →
        ‖Z‖ ≤ ‖Tij‖ / sep Tii Tjj) := by
  refine ⟨fun μ hμ ν hν => sep_le_norm_sub hμ hν, fun hs Z hZ => ?_⟩
  have h := frobenius_norm_le_div_sep hs Z
  rwa [hZ, norm_neg] at h

/-- The Frobenius norm of `[I_a Z; 0 I_b]`: `‖Y‖_F² = a + b + ‖Z‖_F²`. -/
private theorem frobenius_norm_sq_fromBlocks_one {a b : ℕ} (Z : Matrix (Fin a) (Fin b) ℝ) :
    ‖(fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)‖ ^ 2 = a + b + ‖Z‖ ^ 2 := by
  have hone : ∀ m : ℕ, ∑ i : Fin m, ∑ j : Fin m, ‖(1 : Matrix (Fin m) (Fin m) ℝ) i j‖ ^ 2 = m := by
    intro m
    simp [one_apply]
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Finset.sum_add_distrib, hone]
  simp [Matrix.zero_apply]
  ring

/-- **§7.6.3, the condition of `Y_ij`.** For `Y = [I_{n_i} Z; 0 I_{n_j}]`,
`κ_F(Y) = ‖Y‖_F ‖Y⁻¹‖_F = n_i + n_j + ‖Z‖_F²` (`Y⁻¹ = [I -Z; 0 I]`). The book prints
`n_i² + n_j² + ‖Z‖_F²`, but `‖I_k‖_F² = k`, not `k²`. -/
theorem kappaF_blockUnit {a b : ℕ} (Z : Matrix (Fin a) (Fin b) ℝ) :
    ‖(fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)‖ *
        ‖(fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)⁻¹‖ = a + b + ‖Z‖ ^ 2 := by
  have hinv : (fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)⁻¹ =
      fromBlocks 1 (-Z) 0 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  have h1 := frobenius_norm_sq_fromBlocks_one Z
  have h2 := frobenius_norm_sq_fromBlocks_one (-Z)
  rw [norm_neg] at h2
  rw [hinv, ← Real.sqrt_sq (norm_nonneg (fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) _ ℝ)),
    ← Real.sqrt_sq (norm_nonneg (fromBlocks 1 (-Z) 0 1 : Matrix (Fin a ⊕ Fin b) _ ℝ)), h1, h2,
    Real.mul_self_sqrt (by positivity)]

end Frobenius

/-! ### §7.6.4 Eigenvectors and eigenvalue condition from the Schur form -/

/-- **§7.6.4, eigenvectors from the real Schur form.** Let `Qᵀ A Q = [T₁₁ u T₁₃; 0 λ vᵀ; 0 0 T₃₃]`
with blocks of sizes `p`, `1`, `q` (indexed by `(Fin p ⊕ Unit) ⊕ Fin q`) and `Q` orthogonal, and let
`(T₁₁ - λ I) w = -u` and `(T₃₃ - λ I)ᵀ z = -v` (uniquely solvable when `λ ∉ λ(T₁₁) ∪ λ(T₃₃)`, the
book's hypothesis, which the identities below do not need). Then `x = Q [w; 1; 0]` and
`y = Q [0; 1; z]` are right and left eigenvectors of `A` for `λ` (`A x = λ x`, `yᵀ A = λ yᵀ`), with
`yᵀ x = 1`, `xᵀ x = 1 + wᵀ w` and `yᵀ y = 1 + zᵀ z`; hence the condition
`1/s(λ) = ‖x‖₂ ‖y‖₂ / |yᵀ x|` (Section 7.2.2) is `√((1 + wᵀ w)(1 + zᵀ z))`. -/
theorem schur_eigenvectors {p q : ℕ}
    {A Q : Matrix ((Fin p ⊕ Unit) ⊕ Fin q) ((Fin p ⊕ Unit) ⊕ Fin q) ℝ}
    (hQ : Q ∈ orthogonalGroup ((Fin p ⊕ Unit) ⊕ Fin q) ℝ) {T₁₁ : Matrix (Fin p) (Fin p) ℝ}
    {u : Fin p → ℝ} {T₁₃ : Matrix (Fin p) (Fin q) ℝ} {l : ℝ} {v : Fin q → ℝ}
    {T₃₃ : Matrix (Fin q) (Fin q) ℝ}
    (hT : Qᵀ * A * Q = fromBlocks (fromBlocks T₁₁ (replicateCol Unit u) 0 (of fun _ _ => l))
      (fromRows T₁₃ (replicateRow Unit v)) 0 T₃₃)
    {w : Fin p → ℝ} {z : Fin q → ℝ} (hw : (T₁₁ - l • 1) *ᵥ w = -u)
    (hz : (T₃₃ - l • 1)ᵀ *ᵥ z = -v) {x y : (Fin p ⊕ Unit) ⊕ Fin q → ℝ}
    (hx : x = Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0)
    (hy : y = Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) :
    A *ᵥ x = l • x ∧ y ᵥ* A = l • y ∧ y ⬝ᵥ x = 1 ∧ x ⬝ᵥ x = 1 + w ⬝ᵥ w ∧
      y ⬝ᵥ y = 1 + z ⬝ᵥ z ∧ √(x ⬝ᵥ x) * √(y ⬝ᵥ y) / |y ⬝ᵥ x| = √((1 + w ⬝ᵥ w) * (1 + z ⬝ᵥ z)) := by
  subst hx hy
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hQQ' : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hAQ : A * Q = Q * (Qᵀ * A * Q) := by
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQA : Aᵀ * Q = Q * (Qᵀ * A * Q)ᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hdot : ∀ a b : (Fin p ⊕ Unit) ⊕ Fin q → ℝ, (Q *ᵥ a) ⬝ᵥ (Q *ᵥ b) = a ⬝ᵥ b := by
    intro a b
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hQQ', vecMul_one]
  have hw' : T₁₁ *ᵥ w = -u + l • w := by
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hw
    exact sub_eq_iff_eq_add.1 hw
  have hz' : z ᵥ* T₃₃ = -v + l • z := by
    rw [mulVec_transpose, vecMul_sub, vecMul_smul, vecMul_one] at hz
    exact sub_eq_iff_eq_add.1 hz
  have hc1 : replicateCol Unit u *ᵥ (fun _ => (1 : ℝ)) = u := by
    ext i
    simp [mulVec, dotProduct, replicateCol_apply]
  have hc2 : (of fun _ _ => l : Matrix Unit Unit ℝ) *ᵥ (fun _ => (1 : ℝ)) = fun _ => l := by
    ext i
    simp [mulVec, dotProduct]
  have hr1 : (fun _ => (1 : ℝ)) ᵥ* replicateRow Unit v = v := by
    ext i
    simp [vecMul, dotProduct, replicateRow_apply]
  have hr2 : (fun _ => (1 : ℝ)) ᵥ* (of fun _ _ => l : Matrix Unit Unit ℝ) = fun _ => l := by
    ext i
    simp [vecMul, dotProduct]
  have hTx : (Qᵀ * A * Q) *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0 =
      l • Sum.elim (Sum.elim w fun _ => 1) 0 := by
    rw [hT]
    ext ((i | ⟨⟩) | i)
    · simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, add_zero,
        hw', hc1, Sum.elim_inl, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp [fromBlocks_mulVec, hc2]
    · simp [fromBlocks_mulVec]
  have hTy : (Qᵀ * A * Q)ᵀ *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z =
      l • Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z := by
    rw [mulVec_transpose, hT]
    ext ((i | ⟨⟩) | i)
    · simp [vecMul_fromBlocks]
    · simp [vecMul_fromBlocks, hr2]
    · simp only [vecMul_fromBlocks, vecMul_fromRows, Sum.elim_comp_inl, Sum.elim_comp_inr,
        zero_vecMul, zero_add, hz', hr1, Sum.elim_inr, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
  have h1 : A *ᵥ (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) =
      l • (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) := by
    rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, hTx, mulVec_smul]
  have h2 : (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) ᵥ* A =
      l • (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) := by
    rw [← mulVec_transpose, mulVec_mulVec, hQA, ← mulVec_mulVec, hTy, mulVec_smul]
  have h3 : (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) ⬝ᵥ
      (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) = 1 := by
    rw [hdot]
    simp [dotProduct, Fintype.sum_sum_type]
  have h4 : (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) ⬝ᵥ
      (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) = 1 + w ⬝ᵥ w := by
    rw [hdot]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero, Finset.univ_unique, Finset.sum_singleton,
      mul_one]
    ring
  have h5 : (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) ⬝ᵥ
      (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) = 1 + z ⬝ᵥ z := by
    rw [hdot]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Finset.univ_unique, Finset.sum_singleton,
      mul_one]
  have hw0 : 0 ≤ 1 + w ⬝ᵥ w :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rw [h3, h4, h5, abs_one, div_one, Real.sqrt_mul hw0]

/-! ### §7.6.5 Ascertaining Jordan block structures -/

/-- **§7.6.5.** For `C = λ I + N` and `p_i = dim null(N^i)`, `p_{i+1} - p_i` is the number of blocks
of dimension `≥ i + 1` for `λ` in the Jordan form of `C` (any Jordan decomposition `X⁻¹ C X = J`,
laid out along `Fin n` by `σ`); in particular these dimensions are similarity invariants. -/
theorem jordan_block_count {C N X : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hC : C = c • 1 + N)
    {q : ℕ} {e : Fin q → ℕ} {μ : Fin q → ℂ} (σ : ((i : Fin q) × Fin (e i)) ≃ Fin n)
    (hX : IsUnit X) (h : X⁻¹ * C * X = reindex σ σ (jordanForm e μ)) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (N ^ (k + 1)).mulVecLin) -
        Module.finrank ℂ (LinearMap.ker (N ^ k).mulVecLin) =
      (Finset.univ.filter fun i => μ i = c ∧ k + 1 ≤ e i).card := by
  have hs : IsSimilar C (reindex σ σ (jordanForm e μ)) := ⟨X, hX, h.symm⟩
  have hN : N = C - c • 1 := by rw [hC]; abel
  have key : ∀ m, Module.finrank ℂ (LinearMap.ker (N ^ m).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker ((jordanForm e μ - c • 1) ^ m).mulVecLin) := by
    intro m
    have hr : (reindex σ σ (jordanForm e μ) - c • 1) ^ m =
        reindex σ σ ((jordanForm e μ - c • 1) ^ m) := by
      have := map_pow (reindexAlgEquiv ℂ ℂ σ) (jordanForm e μ - c • 1) m
      rw [map_sub, map_smul, map_one] at this
      simpa using this.symm
    rw [hN, ((hs.sub_smul_one c).pow m).finrank_ker_mulVecLin_eq, hr,
      finrank_ker_mulVecLin_reindex]
  rw [key, key]
  exact card_filter_le_jordanBlocks_eq e μ c k

end GolubVanLoan.Chapter07
