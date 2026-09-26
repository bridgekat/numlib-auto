import Numlib.Eigen.InverseEigenvalue
import Numlib.Eigen.Perturbation
import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighQuotientIteration
import NumlibSurface.GolubVanLoan.Chapter08.Section01

/-!
# Golub–Van Loan §8.2: power iterations

Surface file for [golub2013matrix] §8.2: the QR iteration (8.2.1) as an orthogonal similarity
(8.2.2), the power method's computable error bound, inverse iteration, Rayleigh quotient iteration
(8.2.6) with the two-by-two cubic recurrence (8.2.7), and the convergence of the QR iteration to
diagonal form (§8.2.5).

## Conventions

The iterations are displays of the book, not numbered algorithms. The power method (8.2.3) and
orthogonal iteration (8.2.8) are chapter 7's (7.3.3) and (7.3.6); the nodes that use them
(Theorems 8.2.1–8.2.2, (8.2.13), (8.2.15), the orthogonal-iteration form of the QR step) wait for
chapter 7's surface and are planned in this group. Inverse iteration is the backbone's
`Krylov.inverseIterate`, Rayleigh quotient iteration `Krylov.rayleighQuotientIterate`, the QR
iteration `Matrix.qrIterate`.

## Readings

(8.2.7) loses the signs: `x_{k+1} = (c_k³, -s_k³)/√(c_k⁶ + s_k⁶)`, and needs `c_k s_k ≠ 0` (else
`μ_k` is an eigenvalue). In the proof of Theorem 8.2.1 the first sum is garbled and
`|λ_1 - λ_n|` should be `max_i |λ_1 - λ_i|`; in the proof of Theorem 8.2.2, `V_k = Q_αᵀ Q_0` should
be `Q_αᵀ Q_k` and `1/(1 - d_0²)` should be `1/√(1 - d_0²)`.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.2.1 The power method -/

/-- **(8.2.1)–(8.2.2).** For symmetric `A`, an orthogonal `U₀` and any QR steps
`T_{k-1} = U_k R_k`, `T_k = R_k U_k` with orthogonal `U_k`, starting from `T_0 = U₀ᵀ A U₀`:
`T_k = (U₀ U₁ ⋯ U_k)ᵀ A (U₀ U₁ ⋯ U_k)`, and every `T_k` is symmetric. -/
theorem equation_8_2_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {U₀ : Matrix (Fin n) (Fin n) ℝ} {U R T : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ k, U (k + 1) ∈ orthogonalGroup (Fin n) ℝ)
    (hT0 : T 0 = U₀ᵀ * A * U₀) (hQR : ∀ k, T k = U (k + 1) * R (k + 1))
    (hRQ : ∀ k, T (k + 1) = R (k + 1) * U (k + 1)) (k : ℕ) :
    T k = (U₀ * ((List.range k).map fun i => U (i + 1)).prod)ᵀ * A *
        (U₀ * ((List.range k).map fun i => U (i + 1)).prod) ∧ (T k).IsSymm := by
  have key : ∀ k, T k = (U₀ * ((List.range k).map fun i => U (i + 1)).prod)ᵀ * A *
      (U₀ * ((List.range k).map fun i => U (i + 1)).prod) := by
    intro k
    induction k with
    | zero => simpa using hT0
    | succ k ih =>
      have hUU : (U (k + 1))ᵀ * U (k + 1) = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 (hU k)
      have hstep : T (k + 1) = (U (k + 1))ᵀ * T k * U (k + 1) := by
        rw [hRQ, hQR k, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
      rw [hstep, ih, List.range_succ, List.map_append, List.prod_append]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one,
        transpose_mul, Matrix.mul_assoc]
  refine ⟨key k, ?_⟩
  rw [key k]
  simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
    (isHermitian_conjTranspose_mul_mul (U₀ * ((List.range k).map fun i => U (i + 1)).prod)
      (isHermitian_iff_isSymm.2 hA))

/-- **§8.2.1, the computable error bound.** For symmetric `A` and a unit `q` with
`‖A q - (qᵀAq) q‖₂ = δ`, some eigenvalue `λ` of `A` has `|qᵀAq - λ| ≤ δ`, a fortiori the book's
`|qᵀAq - λ| ≤ √2 δ` (the case `r = 1` of Theorem 8.1.13). -/
theorem powerMethod_residual_bound {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {q : Fin n → ℝ} (hq : q ⬝ᵥ q = 1) :
    ∃ l ∈ spectrum ℝ A, |q ⬝ᵥ A *ᵥ q - l| ≤ ‖WithLp.toLp 2 (A *ᵥ q - (q ⬝ᵥ A *ᵥ q) • q)‖ ∧
      |q ⬝ᵥ A *ᵥ q - l| ≤ Real.sqrt 2 * ‖WithLp.toLp 2 (A *ᵥ q - (q ⬝ᵥ A *ᵥ q) • q)‖ := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.2 hA)
  have hq0 : (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro h
    have : q = 0 := by simpa using congrArg WithLp.ofLp h
    rw [this, dotProduct_zero] at hq
    exact zero_ne_one hq
  have hn1 : ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (by rw [← dotProduct_self_eq_norm_sq, hq])
  obtain ⟨μ, hμ, hdist⟩ := hT.exists_hasEigenvalue_dist_le (q ⬝ᵥ A *ᵥ q) hq0
  refine ⟨μ, ?_, ?_⟩
  · rw [← Matrix.spectrum_toLpLin (A := A) 2]
    exact Module.End.HasEigenvalue.mem_spectrum hμ
  · have hres : ‖WithLp.toLp 2 (A *ᵥ q - (q ⬝ᵥ A *ᵥ q) • q)‖ =
        ‖toEuclideanLin A (WithLp.toLp 2 q) - ((q ⬝ᵥ A *ᵥ q : ℝ) : ℝ) • WithLp.toLp 2 q‖ := by
      rw [toEuclideanLin_toLp]; rfl
    rw [hn1, div_one, Real.norm_eq_abs, abs_sub_comm] at hdist
    have h1 : |q ⬝ᵥ A *ᵥ q - μ| ≤ ‖WithLp.toLp 2 (A *ᵥ q - (q ⬝ᵥ A *ᵥ q) • q)‖ := by
      rw [hres]; simpa using hdist
    refine ⟨h1, h1.trans ?_⟩
    have : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ q - (q ⬝ᵥ A *ᵥ q) • q))]

/-! ### §8.2.2 Inverse iteration -/

/-- **§8.2.2, the expansion behind inverse iteration.** For symmetric `A` with an orthonormal
eigenbasis `q_i = Q(:, i)` (`Qᵀ A Q = diag(λ)`), `x = ∑ a_i q_i` and `λ` not an eigenvalue,
`(A - λI)⁻¹ x = ∑ (a_i / (λ_i - λ)) q_i`. Inverse iteration is the power method applied to
`(A - λI)⁻¹` (`Krylov.inverseIterate`). -/
theorem inverseIteration_expansion {A Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) {l : Fin n → ℝ} (hQA : Qᵀ * A * Q = diagonal l)
    {c : ℝ} (hc : ∀ i, l i ≠ c) (a : Fin n → ℝ) :
    (A - c • 1)⁻¹ *ᵥ (Q *ᵥ a) = Q *ᵥ fun i => a i / (l i - c) := by
  have hQA' : star Q * A * Q = diagonal l := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hinv : (diagonal fun i => l i - c)⁻¹ = diagonal fun i => (l i - c)⁻¹ :=
    inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (sub_ne_zero.mpr (hc i))))
  have hQQ : star Q * Q = 1 := (mem_unitaryGroup_iff' (A := Q)).1 hQ
  rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQA' c, inv_mul_mul_star_of_mem_unitaryGroup hQ,
    hinv, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one,
    ← mulVec_mulVec]
  congr 1
  funext i
  rw [mulVec_diagonal, div_eq_mul_inv, mul_comm]

/-! ### §8.2.3 Rayleigh quotient iteration -/

/-- **§8.2.3**: the Rayleigh quotient `r(x) = xᵀAx / xᵀx` minimizes `‖(A - λI)x‖₂` over `λ ∈ ℝ`,
for any `A` and `x ≠ 0`. -/
theorem rayleighQuotient_isMinOn (A : Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ} (hx : x ≠ 0) :
    IsMinOn (fun μ : ℝ => ‖WithLp.toLp 2 ((A - μ • 1) *ᵥ x)‖) Set.univ (rayleighQuotient A x) := by
  have hxx : 0 < x ⬝ᵥ x := by
    rw [dotProduct_self_eq_norm_sq]
    have : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ≠ 0 := fun h =>
      hx (by simpa using congrArg WithLp.ofLp h)
    positivity
  have hsq : ∀ μ : ℝ, ‖WithLp.toLp 2 ((A - μ • 1) *ᵥ x)‖ ^ 2 =
      (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - 2 * μ * (x ⬝ᵥ A *ᵥ x) + μ ^ 2 * (x ⬝ᵥ x) := fun μ => by
    rw [← dotProduct_self_eq_norm_sq, sub_mulVec, smul_mulVec, one_mulVec]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm x (A *ᵥ x)]
    ring
  intro μ _
  simp only [Set.mem_ofPred_eq]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, hsq, hsq,
    rayleighQuotient]
  have key : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - 2 * μ * (x ⬝ᵥ A *ᵥ x) + μ ^ 2 * (x ⬝ᵥ x) -
      ((A *ᵥ x) ⬝ᵥ (A *ᵥ x) - 2 * ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)) * (x ⬝ᵥ A *ᵥ x) +
        ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)) ^ 2 * (x ⬝ᵥ x)) =
      (μ - (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)) ^ 2 * (x ⬝ᵥ x) := by
    field_simp
    ring
  nlinarith [sq_nonneg (μ - (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x))]

/-- **(8.2.6), Rayleigh quotient iteration**: `x_0` given; `μ_k = r(x_k)`,
`(A - μ_k I) z_{k+1} = x_k`, `x_{k+1} = z_{k+1} / ‖z_{k+1}‖₂`. The solve is `Matrix.inv` (a singular
shift gives Lean's junk value `0`; statements carry the hypotheses). -/
noncomputable def rayleighQuotientIteration (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 =>
    let z := (A - rayleighQuotient A (rayleighQuotientIteration A x₀ k) • 1)⁻¹ *ᵥ
      rayleighQuotientIteration A x₀ k
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖⁻¹ • z

/-- `Ring.inverse` of the operator of a matrix is the operator of its inverse. -/
private theorem ringInverse_toEuclideanLin' (M : Matrix (Fin n) (Fin n) ℝ) :
    Ring.inverse (toEuclideanLin M) = toEuclideanLin M⁻¹ := by
  by_cases hM : IsUnit M
  · exact (ringInverse_toEuclideanLin hM).2
  · have h1 : ¬IsUnit (toEuclideanLin M) := fun h => hM (by
      refine (Matrix.mulVec_injective_iff_isUnit).1 fun x y hxy => ?_
      have hinj := ((Module.End.isUnit_iff _).1 h).1
      have := hinj (a₁ := WithLp.toLp 2 x) (a₂ := WithLp.toLp 2 y)
        (by rw [toEuclideanLin_toLp, toEuclideanLin_toLp, hxy])
      simpa using congrArg WithLp.ofLp this)
    rw [Ring.inverse_non_unit _ h1, nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hM,
      map_zero]

/-- **(8.2.6) is the backbone's Rayleigh quotient iteration**: from a unit `x_0`, the book's
iterates are `Krylov.rayleighQuotientIterate (toEuclideanLin A) x_0` (inverse iteration with the
Rayleigh shift `⟪x, A x⟫`, normalized). -/
theorem rayleighQuotientIteration_eq (A : Matrix (Fin n) (Fin n) ℝ) {x₀ : Fin n → ℝ}
    (hx₀ : x₀ ⬝ᵥ x₀ = 1) (k : ℕ) :
    WithLp.toLp 2 (rayleighQuotientIteration A x₀ k) =
      Krylov.rayleighQuotientIterate (toEuclideanLin A) (WithLp.toLp 2 x₀) k := by
  -- the iterates are unit vectors or zero
  have hinv : ∀ k, rayleighQuotientIteration A x₀ k ⬝ᵥ rayleighQuotientIteration A x₀ k = 1 ∨
      rayleighQuotientIteration A x₀ k = 0 := by
    intro k
    cases k with
    | zero => exact Or.inl hx₀
    | succ k =>
      simp only [rayleighQuotientIteration]
      set z := (A - rayleighQuotient A (rayleighQuotientIteration A x₀ k) • 1)⁻¹ *ᵥ
        rayleighQuotientIteration A x₀ k
      by_cases hz : z = 0
      · right; rw [hz, smul_zero]
      · left
        have hzn : ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := by
          rw [norm_ne_zero_iff]; exact fun h => hz (by simpa using congrArg WithLp.ofLp h)
        rw [dotProduct_self_eq_norm_sq, WithLp.toLp_smul, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hzn, one_pow]
  induction k with
  | zero =>
    have hn1 : ‖(WithLp.toLp 2 x₀ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
        (by rw [← dotProduct_self_eq_norm_sq, hx₀])
    simp [rayleighQuotientIteration, hn1]
  | succ k ih =>
    rw [Krylov.rayleighQuotientIterate, ← ih, Krylov.rqiStep]
    simp only [rayleighQuotientIteration]
    set x := rayleighQuotientIteration A x₀ k
    have hshift : rayleighQuotient A x =
        inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
          (toEuclideanLin A (WithLp.toLp 2 x)) := by
      rw [toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial, rayleighQuotient]
      have hk : x ⬝ᵥ x = 1 ∨ x = 0 := hinv k
      rcases hk with h | h
      · rw [h, div_one, dotProduct_comm]
      · rw [h]; simp
    have hop : Ring.inverse (toEuclideanLin A -
        inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (toEuclideanLin A (WithLp.toLp 2 x)) •
          (1 : Module.End ℝ (EuclideanSpace ℝ (Fin n)))) =
        toEuclideanLin (A - rayleighQuotient A x • 1)⁻¹ := by
      rw [← ringInverse_toEuclideanLin', hshift, map_sub, map_smul, toEuclideanLin_one]
      rfl
    rw [hop, toEuclideanLin_toLp, WithLp.toLp_smul]
    rfl

/-- **(8.2.7).** Rayleigh quotient iteration on `A = diag(λ₁, λ₂)`, `λ₁ > λ₂`, from
`x_k = (c_k, s_k)` with `c_k² + s_k² = 1` and `c_k s_k ≠ 0` (the book omits this: otherwise
`μ_k` is an eigenvalue): `μ_k = λ₁c_k² + λ₂s_k²`,
`z_{k+1} = (1/(λ₁ - λ₂)) (c_k/s_k², -s_k/c_k²)` and
`x_{k+1} = (c_k³, -s_k³)/√(c_k⁶ + s_k⁶)` — so `|c_{k+1}| = |c_k|³/√(c_k⁶ + s_k⁶)` and
`|s_{k+1}| = |s_k|³/√(c_k⁶ + s_k⁶)`, the book's display up to the lost sign. -/
theorem equation_8_2_7 {l₁ l₂ : ℝ} (hl : l₂ < l₁) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hc : c ≠ 0) (hs : s ≠ 0) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![l₁, l₂]
    let x : Fin 2 → ℝ := ![c, s]
    let z := (A - rayleighQuotient A x • 1)⁻¹ *ᵥ x
    rayleighQuotient A x = l₁ * c ^ 2 + l₂ * s ^ 2 ∧
      z = (1 / (l₁ - l₂)) • ![c / s ^ 2, -s / c ^ 2] ∧
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖⁻¹ • z =
        (1 / Real.sqrt (c ^ 6 + s ^ 6)) • ![c ^ 3, -s ^ 3] := by
  intro A x z
  have hd : l₁ - l₂ ≠ 0 := sub_ne_zero.2 hl.ne'
  have hμ : rayleighQuotient A x = l₁ * c ^ 2 + l₂ * s ^ 2 := by
    simp only [rayleighQuotient, A, x, mulVec_diagonal, dotProduct, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show c * c + s * s = 1 by nlinarith]
    ring
  have hz : z = (1 / (l₁ - l₂)) • ![c / s ^ 2, -s / c ^ 2] := by
    simp only [z, hμ, A]
    have h1 : l₁ - (l₁ * c ^ 2 + l₂ * s ^ 2) = (l₁ - l₂) * s ^ 2 := by
      have : c ^ 2 = 1 - s ^ 2 := by linarith
      rw [this]; ring
    have h2 : l₂ - (l₁ * c ^ 2 + l₂ * s ^ 2) = -((l₁ - l₂) * c ^ 2) := by
      have : s ^ 2 = 1 - c ^ 2 := by linarith
      rw [this]; ring
    have hdiag : (diagonal ![l₁, l₂] - (l₁ * c ^ 2 + l₂ * s ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        diagonal ![(l₁ - l₂) * s ^ 2, -((l₁ - l₂) * c ^ 2)] := by
      rw [smul_one_eq_diagonal, diagonal_sub]
      congr 1
      funext i
      fin_cases i
      · simpa using h1
      · simpa using h2
    have hne : ∀ i, ![(l₁ - l₂) * s ^ 2, -((l₁ - l₂) * c ^ 2)] i ≠ 0 := by
      intro i; fin_cases i <;> simp [hd, hs, hc]
    have hinv : (diagonal ![(l₁ - l₂) * s ^ 2, -((l₁ - l₂) * c ^ 2)])⁻¹ =
        diagonal fun i => (![(l₁ - l₂) * s ^ 2, -((l₁ - l₂) * c ^ 2)] i)⁻¹ :=
      inv_eq_right_inv (by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hne i)))
    rw [hdiag, hinv]
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
      simp only [x, mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;>
      field_simp
  refine ⟨hμ, hz, ?_⟩
  -- `z` is a positive multiple of `(c³, -s³)`
  have hκ : 0 < 1 / ((l₁ - l₂) * c ^ 2 * s ^ 2) := by
    have := sub_pos.2 hl
    positivity
  have hzw : z = (1 / ((l₁ - l₂) * c ^ 2 * s ^ 2)) • ![c ^ 3, -s ^ 3] := by
    rw [hz]
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      field_simp
  have hw : ‖(WithLp.toLp 2 ![c ^ 3, -s ^ 3] : EuclideanSpace ℝ (Fin 2))‖ =
      Real.sqrt (c ^ 6 + s ^ 6) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    ring
  rw [hzw, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hκ, hw, smul_smul]
  congr 1
  field_simp

/-- **§8.2.3, cubic convergence for `n = 2`.** For `A = diag(λ₁, λ₂)`, `λ₁ > λ₂`, and a unit
`x_0 = (c_0, s_0)` with `c_0 s_0 ≠ 0`, the Rayleigh quotient iterates `x_k = (c_k, s_k)` stay unit
vectors with `c_k s_k ≠ 0`, and `|s_k / c_k| = |s_0 / c_0|^(3^k)`: they converge cubically to
`span{e₁}` if `|c_0| > |s_0|` and to `span{e₂}` if `|c_0| < |s_0|`. -/
theorem equation_8_2_7_cubic {l₁ l₂ : ℝ} (hl : l₂ < l₁) {c₀ s₀ : ℝ}
    (hcs : c₀ ^ 2 + s₀ ^ 2 = 1) (hc : c₀ ≠ 0) (hs : s₀ ≠ 0) (k : ℕ) :
    let x := rayleighQuotientIteration (diagonal ![l₁, l₂]) ![c₀, s₀] k
    x 0 ^ 2 + x 1 ^ 2 = 1 ∧ x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ |x 1 / x 0| = |s₀ / c₀| ^ (3 ^ k) := by
  induction k with
  | zero => simp [rayleighQuotientIteration, hcs, hc, hs]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    set x := rayleighQuotientIteration (diagonal ![l₁, l₂]) ![c₀, s₀] k with hx
    have hxe : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    have hstep := (equation_8_2_7 hl h1 h2 h3).2.2
    have hnext : rayleighQuotientIteration (diagonal ![l₁, l₂]) ![c₀, s₀] (k + 1) =
        (1 / Real.sqrt (x 0 ^ 6 + x 1 ^ 6)) • ![x 0 ^ 3, -x 1 ^ 3] := by
      rw [← hstep]
      simp only [rayleighQuotientIteration]
      rw [← hx, ← hxe]
    have hpos : 0 < x 0 ^ 6 + x 1 ^ 6 := by positivity
    have hsq : Real.sqrt (x 0 ^ 6 + x 1 ^ 6) ^ 2 = x 0 ^ 6 + x 1 ^ 6 := Real.sq_sqrt hpos.le
    have hsne : Real.sqrt (x 0 ^ 6 + x 1 ^ 6) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [hnext, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨?_, by simp [hsne, h2], by simp [hsne, h3], ?_⟩
    · field_simp
      rw [hsq]
    · rw [show 1 / Real.sqrt (x 0 ^ 6 + x 1 ^ 6) * -x 1 ^ 3 /
          (1 / Real.sqrt (x 0 ^ 6 + x 1 ^ 6) * x 0 ^ 3) = -(x 1 / x 0) ^ 3 by
          field_simp]
      rw [abs_neg, abs_pow, h4, ← pow_mul, pow_succ]

/-! ### §8.2.5 The QR iteration and orthogonal iteration -/

/-- **§8.2.5: "the matrices `T_k = Q_kᵀ A Q_k` converge to diagonal form".** For symmetric `A` with
`Qᵀ A Q = diag(λ)` (`Q` orthogonal), eigenvalues of distinct moduli `|λ_1| > ⋯ > |λ_n| > 0`, and
`Qᵀ` with nonsingular leading principal submatrices (the general-position condition (8.2.15) at
`Q_0 = I`), the QR iterates `Matrix.qrIterate A k` converge to `diag(λ)`: every off-diagonal entry
tends to `0` and the `j`-th diagonal entry to `λ_j`. -/
theorem qrIterate_tendsto_diagonal {A Q : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) {l : Fin n → ℝ} (hQA : Qᵀ * A * Q = diagonal l)
    (hsep : ∀ j k : Fin n, j < k → |l k| < |l j|) (hl0 : ∀ j, l j ≠ 0)
    (hgen : ∀ (m : ℕ) (hm : m ≤ n), IsUnit ((Qᵀ).submatrix (Fin.castLE hm) (Fin.castLE hm)).det) :
    (∀ j k : Fin n, j ≠ k →
      Filter.Tendsto (fun ν => qrIterate A ν j k) Filter.atTop (nhds 0)) ∧
      ∀ j, Filter.Tendsto (fun ν => qrIterate A ν j j) Filter.atTop (nhds (l j)) := by
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQQ' : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hdetQ : IsUnit Q.det := by
    have := congrArg det hQQ
    rw [det_mul, det_transpose, det_one] at this
    exact isUnit_iff_ne_zero.2 fun h => by rw [h, zero_mul] at this; exact zero_ne_one this
  have hQunit : IsUnit Q := (isUnit_iff_isUnit_det Q).2 hdetQ
  have hQinv : Q⁻¹ = Qᵀ := inv_eq_left_inv hQQ
  have hAeq : A = Q * diagonal l * Qᵀ := by
    rw [← hQA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul, Matrix.mul_assoc,
      hQQ', Matrix.mul_one]
  have hdetA : IsUnit A.det := by
    rw [hAeq, det_mul, det_mul, det_diagonal, det_transpose]
    refine isUnit_iff_ne_zero.2 ?_
    have hq : Q.det ≠ 0 := hdetQ.ne_zero
    exact mul_ne_zero (mul_ne_zero hq (Finset.prod_ne_zero_iff.2 fun j _ => hl0 j)) hq
  have hconv := tendsto_qrIterate (𝕜 := ℝ) hdetA (x := euclideanCol Q) (l := l)
    (linearIndependent_euclideanCol hdetQ) (span_range_euclideanCol_eq_top hdetQ)
    (toEuclideanLin_euclideanCol_of_conj_eq_diagonal hQunit (by rw [hQinv]; exact hQA)) hl0
    (fun j k hjk => by simpa [Real.norm_eq_abs] using hsep j k hjk)
    ((forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal hdetQ).2 (by rwa [hQinv]))
  refine ⟨fun j k hjk => ?_, hconv.2⟩
  rcases lt_or_gt_of_ne hjk with h | h
  · have hsym : ∀ ν, qrIterate A ν j k = qrIterate A ν k j := fun ν => by
      have := (isHermitian_qrIterate (isHermitian_iff_isSymm.2 hA) ν).apply k j
      simpa using this
    simp only [hsym]
    exact hconv.1 k j h
  · exact hconv.1 j k h

end GolubVanLoan.Chapter08
