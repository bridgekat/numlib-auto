import Numlib.Eigen.KrylovEigen
import Numlib.Eigen.Perturbation
import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.Sturm
import Numlib.Krylov.Decomposition
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter08.Section04

/-!
# Golub–Van Loan §10.1: the symmetric Lanczos process

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.1:
the gradient of the Rayleigh quotient (10.1.1), Algorithm 10.1.1 (Lanczos tridiagonalization) and
Theorem 10.1.1 with (10.1.4) and (10.1.6), Ritz approximations (10.1.7)–(10.1.8) with the residual
bound and Golub's rank-one modification with its bracketing intervals (via chapter 8's
Theorem 8.1.8), the Kaniel–Paige–Saad bounds Theorem 10.1.2,
Corollary 10.1.3 and Theorem 10.1.4, and the power-method comparison (10.1.11).

## Conventions

The symmetric `A ∈ ℝ^{n×n}` is `A : Matrix (Fin n) (Fin n) ℝ` with `hA : A.IsSymm`, acting on
`EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanLin` (symmetric by
`Matrix.IsSymm.isSymmetric_toEuclideanLin`). Indices are `0`-based: the book's `q_{j+1}`, `α_{j+1}`,
`β_{j+1}` are `Arnoldi.vec (toEuclideanLin A) q₁ j`, `Lanczos.alpha _ q₁ j`, `Lanczos.beta _ q₁ j`;
`Q_k` is `Arnoldi.basisMatrix A q₁ k`, `T_k` is `Lanczos.tridiag _ q₁ k`, `r_k` is
`(Arnoldi.w _ q₁ (k − 1)).ofLp` and `e_k` is `Krylov.lastVec 1 k`. The Schur decomposition
(10.1.9) is any `Z ∈ orthogonalGroup` with `Zᵀ * A * Z = diagonal λ` and `Antitone λ`
(`λ_1 ≥ ⋯ ≥ λ_n`, `λ_i` at index `i − 1`), with `z_i = Matrix.euclideanCol Z (i − 1)`; the
theorems hold for every such decomposition, also when eigenvalues repeat and `Z` is not unique
(`schurBasis`, and `eigenvalues_eq_of_schur` identifies `λ` with the sorted eigenvalues). The
Ritz values `θ_1 ≥ ⋯ ≥ θ_k` are `Lanczos.ritzValues (toEuclideanLin A) q₁ k`, the sorted
eigenvalues of `T_k`, and the Ritz pairs of (10.1.7) are stated for every eigenpair of `T_k`, so
for every Schur decomposition `S_kᵀ T_k S_k = Θ_k`.

The monotonicity `M_1 ≤ M_2 ≤ ⋯` of §10.1.1 (the largest Ritz values increase with `k`) is the
backbone's `LinearMap.IsSymmetric.eigenvalues_compression_mono`.

## The algorithm

Algorithm 10.1.1 is a monadic program with a rounding hook `rnd` (conventions 1–14 of
`NumlibSurface/GolubVanLoan`): the `while β_k ≠ 0` loop runs over `List.range fuel` with a `done`
flag (convention 3), the matrix–vector product `A q_k` is chapter 1's row gaxpy
(`GolubVanLoan.Chapter01.algorithm_1_1_3`), the inner products are its Algorithm 1.1.1, the
updates `r_k = (A − α_k I) q_k − β_{k−1} q_{k−1}` are two of its saxpys (Algorithm 1.1.2), the
normalization `q_{k+1} = r_k / β_k` is `vecDiv` (one rounded quotient per entry) and
`β_k = ‖r_k‖₂` is `vecNorm` (the rounded square root of a rounded dot product). Its exact semantics
`algorithm_10_1_1_spec` identifies every computed quantity with the backbone's Gram–Schmidt
definition of the Lanczos process (`Numlib/Krylov/Lanczos`).

## Not formalized

(10.1.2)–(10.1.3) (the motivation through `M_k`, `m_k`), (10.1.5) (the display of the tridiagonal
`T_k`, the backbone's `Lanczos.tridiag`), Figure 10.1.1 and the comparison after (10.1.11)
(numerical), operation counts.
-/

open Matrix Krylov FloatingPoint Polynomial
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

variable {n : ℕ}

/-! ### Vector helpers of the Krylov programs -/

section Helpers

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The entrywise rounded quotient `fl(x / β)` of a vector by a scalar, one `rnd` per entry, in
place: the normalization `q = r / β` of the Lanczos, Arnoldi and Golub–Kahan processes. -/
noncomputable def vecDiv (x : Fin n → ℝ) (β : ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let c ← rnd (y i / β)
    pure (Function.update y i c)) x

/-- The rounded Euclidean norm `fl(√(fl(xᵀx)))` of a vector: chapter 1's dot product followed by
one rounded square root. -/
noncomputable def vecNorm (x : Fin n → ℝ) : M ℝ := do
  let s ← algorithm_1_1_1 rnd x x
  rnd (Real.sqrt s)

end Helpers

/-- Exact semantics of `vecDiv`: `x / β = β⁻¹ • x`. -/
theorem vecDiv_spec (x : Fin n → ℝ) (β : ℝ) : Id.run (vecDiv pure x β) = β⁻¹ • x := by
  funext k
  rw [vecDiv, List.idRun_foldlM_update_apply (fun k b => (pure (b / β) : Id ℝ)) _
    (List.nodup_finRange n), ite_eq_left (List.mem_finRange k)]
  simp [div_eq_inv_mul]

/-- Exact semantics of `vecNorm`: the Euclidean norm. -/
theorem vecNorm_spec (x : Fin n → ℝ) :
    Id.run (vecNorm pure x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [vecNorm, Id.run_bind, algorithm_1_1_1_spec, EuclideanSpace.norm_eq]
  simp [dotProduct, sq]

/-! ### (10.1.1): the gradient of the Rayleigh quotient -/

/-- **(10.1.1).** For a symmetric `A` and `x ≠ 0`, the Rayleigh quotient `r(x) = xᵀAx / xᵀx` has
gradient `∇r(x) = (2/xᵀx)(A x − r(x) x)`; hence (the display after (10.1.3)) `∇r(x)` lies in
`span {x, A x}`. Backbone `ContinuousLinearMap.hasGradientAt_rayleighQuotient`. -/
theorem equation_10_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    let T := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
    HasGradientAt T.rayleighQuotient ((2 / ‖x‖ ^ 2) • (T x - T.rayleighQuotient x • x)) x ∧
      (2 / ‖x‖ ^ 2) • (T x - T.rayleighQuotient x • x) ∈ Submodule.span ℝ {x, T x} := by
  intro T
  refine ⟨ContinuousLinearMap.hasGradientAt_rayleighQuotient
    (by rw [coe_toEuclideanCLM_eq_toEuclideanLin]; exact hA.isSymmetric_toEuclideanLin) hx, ?_⟩
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)

/-! ### Algorithm 10.1.1 -/

/-- The state of Algorithm 10.1.1: the number `k` of Lanczos vectors computed so far, the vectors
(`q j` is the book's `q_{j+1}`), the coefficients (`alpha j`, `beta j` are the book's `α_{j+1}`,
`β_{j+1}`), the current residual `r` (the book's `r_k`) and the `done` flag of the `while` loop
(set once a computed `β_k` is `0`). -/
structure LanczosState (n : ℕ) where
  /-- The book's step counter `k`. -/
  k : ℕ
  /-- The Lanczos vectors, `0`-based. -/
  q : ℕ → Fin n → ℝ
  /-- The diagonal coefficients `α`, `0`-based. -/
  alpha : ℕ → ℝ
  /-- The off-diagonal coefficients `β`, `0`-based. -/
  beta : ℕ → ℝ
  /-- The residual `r_k`. -/
  r : Fin n → ℝ
  /-- Whether the loop has stopped (`β_k = 0`). -/
  done : Bool

section Algorithm

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of the `while` loop of Algorithm 10.1.1 (a no-op once `done`):
```
q_{k+1} = r_k/β_k,  k = k + 1,  α_k = q_kᵀ A q_k,
r_k = (A − α_k I) q_k − β_{k−1} q_{k−1},  β_k = ‖r_k‖₂
```
with `β_0 = 1` and `q_0 = 0` at the first pass. -/
noncomputable def lanczosStep (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosState n) :
    M (LanczosState n) :=
  if s.done then pure s else do
    let bk : ℝ := if s.k = 0 then 1 else s.beta (s.k - 1)
    let qk ← vecDiv rnd s.r bk
    let v ← algorithm_1_1_3 rnd A qk 0
    let a ← algorithm_1_1_1 rnd qk v
    let v ← algorithm_1_1_2 rnd (-a) qk v
    let r ← algorithm_1_1_2 rnd (-bk) (if s.k = 0 then 0 else s.q (s.k - 1)) v
    let b ← vecNorm rnd r
    pure
      { k := s.k + 1
        q := Function.update s.q s.k qk
        alpha := Function.update s.alpha s.k a
        beta := Function.update s.beta s.k b
        r := r
        done := decide (b = 0) }

/-- **Algorithm 10.1.1 (Lanczos Tridiagonalization).** "Given a symmetric `A ∈ ℝ^{n×n}` and a unit
2-norm `q₁ ∈ ℝⁿ`, the following algorithm computes a matrix `Q_k = [q_1 | ⋯ | q_k]` with orthonormal
columns and a tridiagonal `T_k ∈ ℝ^{k×k}` so that `A Q_k = Q_k T_k`":
```
k = 0, β_0 = 1, q_0 = 0, r_0 = q₁
while β_k ≠ 0
  q_{k+1} = r_k/β_k,  k = k + 1,  α_k = q_kᵀ A q_k
  r_k = (A − α_k I) q_k − β_{k−1} q_{k−1},  β_k = ‖r_k‖₂
end
```
The `while` loop is at most `fuel` passes of `lanczosStep` (convention 3). -/
noncomputable def algorithm_10_1_1 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (fuel : ℕ) :
    M (LanczosState n) :=
  (List.range fuel).foldlM (fun s _ => lanczosStep rnd A s)
    { k := 0, q := fun _ => 0, alpha := fun _ => 0, beta := fun _ => 0, r := q₁, done := false }

end Algorithm

/-- The exact run after `t + 1` passes is one more pass. -/
private theorem algorithm_10_1_1_succ (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (t : ℕ) :
    Id.run (algorithm_10_1_1 pure A q₁ (t + 1)) =
      Id.run (lanczosStep pure A (Id.run (algorithm_10_1_1 pure A q₁ t))) := by
  simp only [algorithm_10_1_1, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Exact semantics of Algorithm 10.1.1.** For a symmetric `A` and a unit `q₁`, the exact run
stops after `min fuel m` passes, `m` the grade of `q₁` (the dimension of `𝒦(A, q₁, n)`), and every
computed quantity is the backbone's: `q_{j+1} = Arnoldi.vec`, `α_{j+1} = Lanczos.alpha`,
`β_{j+1} = Lanczos.beta` (so the book's positive choice `β_k = ‖r_k‖₂` is the backbone's) and the
last residual is `r_k = Arnoldi.w _ q₁ (k − 1)`. Induction on the passes with the invariant "the
state is the backbone's at step `k`": `Lanczos.w_succ_eq` is the residual update,
`Arnoldi.vec_succ_eq` the normalization and `Lanczos.beta_eq_zero_iff` the exit test. -/
theorem algorithm_10_1_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_1_1 pure A q₁ fuel)
    let T := toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
    s.k = min fuel (grade T q) ∧
      (∀ j < s.k, s.q j = (Arnoldi.vec T q j).ofLp ∧ s.alpha j = Lanczos.alpha T q j ∧
        s.beta j = Lanczos.beta T q j) ∧
      (0 < s.k → s.r = (Arnoldi.w T q (s.k - 1)).ofLp) := by
  intro s T q
  have hT : T.IsSymmetric := hA.isSymmetric_toEuclideanLin
  have hTx : ∀ x, (T x).ofLp = A *ᵥ x.ofLp := fun x => rfl
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hq
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hg : 0 < grade T q := by
    rw [Nat.pos_iff_ne_zero, Ne, grade_eq_zero_iff]
    push Not
    exact ⟨hq0, inferInstance⟩
  -- the invariant after `t` passes
  let P : ℕ → LanczosState n → Prop := fun t s =>
    s.k = min t (grade T q) ∧ s.done = decide (grade T q ≤ s.k) ∧
      (∀ j < s.k, s.q j = (Arnoldi.vec T q j).ofLp ∧ s.alpha j = Lanczos.alpha T q j ∧
        s.beta j = Lanczos.beta T q j) ∧
      s.r = if s.k = 0 then q₁ else (Arnoldi.w T q (s.k - 1)).ofLp
  have hP : ∀ t, P t (Id.run (algorithm_10_1_1 pure A q₁ t)) := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp [algorithm_10_1_1], ?_, fun j hj => ?_, by simp [algorithm_10_1_1]⟩
      · simp [algorithm_10_1_1, hg.ne']
      · simp [algorithm_10_1_1] at hj
    | succ t ih =>
      rw [algorithm_10_1_1_succ]
      set s := Id.run (algorithm_10_1_1 pure A q₁ t)
      obtain ⟨hk, hdone, hvec, hr⟩ := ih
      cases hsd : s.done with
      | true =>
        have hle : grade T q ≤ s.k := by simpa [hsd] using hdone.symm
        simp only [lanczosStep, hsd, ↓reduceIte, Id.run_pure]
        refine ⟨?_, hdone, hvec, hr⟩
        rw [hk] at hle ⊢
        omega
      | false =>
        have hlt : s.k < grade T q := by
          have : ¬ grade T q ≤ s.k := by simpa [hsd] using hdone.symm
          omega
        have hkt : s.k = t := by rw [hk] at hlt ⊢; omega
        simp only [P, lanczosStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
          vecDiv_spec, algorithm_1_1_3_spec, algorithm_1_1_1_spec, algorithm_1_1_2_spec,
          vecNorm_spec, zero_add]
        -- the new Lanczos vector
        have hqk : (if s.k = 0 then 1 else s.beta (s.k - 1))⁻¹ • s.r =
            (Arnoldi.vec T q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [hr, h0, ↓reduceIte]
            rw [Arnoldi.vec_zero T q hq0, show ‖q‖ = 1 from hq]
            simp [q]
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hr, hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [(hvec j (by omega)).2.2, Arnoldi.vec_succ_eq, Lanczos.beta]
            simp
        rw [hqk]
        -- the diagonal coefficient
        have ha : (Arnoldi.vec T q s.k).ofLp ⬝ᵥ (A *ᵥ (Arnoldi.vec T q s.k).ofLp) =
            Lanczos.alpha T q s.k := by
          rw [Lanczos.alpha, Arnoldi.coeff, RCLike.re_to_real,
            EuclideanSpace.inner_eq_star_dotProduct,
            ofLp_toEuclideanLin, star_trivial, dotProduct_comm]
        rw [ha]
        -- the residual
        have hw : A *ᵥ (Arnoldi.vec T q s.k).ofLp +
              (-Lanczos.alpha T q s.k) • (Arnoldi.vec T q s.k).ofLp +
              (-(if s.k = 0 then 1 else s.beta (s.k - 1))) •
                (if s.k = 0 then 0 else s.q (s.k - 1)) =
            (Arnoldi.w T q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [h0, ↓reduceIte, smul_zero, add_zero]
            rw [Arnoldi.w, zero_add, Finset.sum_range_one, ← Lanczos.coe_alpha q hT 0]
            simp [sub_eq_add_neg, hTx]
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
            rw [(hvec j (by omega)).1, (hvec j (by omega)).2.2, Lanczos.w_succ_eq q hT j]
            simp [sub_eq_add_neg, hTx]
        rw [hw, WithLp.toLp_ofLp, ← Lanczos.beta]
        refine ⟨by omega, ?_, fun j hj => ?_, by simp⟩
        · simp only [Lanczos.beta_eq_zero_iff q hT s.k]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · simp only [Function.update_of_ne hj.ne]
            exact hvec j hj
          · simp
  obtain ⟨hk, -, hvec, hr⟩ := hP fuel
  have hr' : s.r = if s.k = 0 then q₁ else (Arnoldi.w T q (s.k - 1)).ofLp := hr
  refine ⟨hk, hvec, fun hpos => ?_⟩
  simp only [hr', hpos.ne', ↓reduceIte]


/-! ### The Lanczos relation and Theorem 10.1.1 -/

/-- **(10.1.4).** For a symmetric `A` and every `k ≥ 1`, `A Q_k = Q_k T_k + r_k e_kᵀ`, with
`Q_k = Arnoldi.basisMatrix A q₁ k`, `T_k = Lanczos.tridiag _ q₁ k` and
`r_k = Arnoldi.w _ q₁ (k − 1)`
(the orthonormality of `Q_k` needs `k ≤ grade`; the relation does not). Backbone
`Lanczos.mul_basisMatrix`. -/
theorem equation_10_1_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : 1 ≤ k) :
    A * Arnoldi.basisMatrix A q₁ k =
      Arnoldi.basisMatrix A q₁ k * Lanczos.tridiag (toEuclideanLin A) q₁ k +
        vecMulVec (Arnoldi.w (toEuclideanLin A) q₁ (k - 1)).ofLp (Krylov.lastVec (1 : ℝ) k) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := Lanczos.mul_basisMatrix hA.isSymmetric_toEuclideanLin q₁ k
  simpa using h

/-- Over `ℝ`, `Q_kᵀ Q_k = I` below the grade. -/
private theorem transpose_basisMatrix_mul_self {A : Matrix (Fin n) (Fin n) ℝ}
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k ≤ grade (toEuclideanLin A) q₁) :
    (Arnoldi.basisMatrix A q₁ k)ᵀ * Arnoldi.basisMatrix A q₁ k = 1 := by
  have h := Arnoldi.conjTranspose_basisMatrix_mul_self A q₁ hk
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- **(10.1.6)** and its consequences in the proof of Theorem 10.1.1: for `1 ≤ k ≤ m` (the grade),
`Q_kᵀ A Q_k = T_k + Q_kᵀ r_k e_kᵀ`, and in fact `Q_kᵀ A Q_k = T_k` and `Q_kᵀ r_k = 0`, so that
`T_{ij} = q_iᵀ A q_j`. Backbone `Arnoldi.conjTranspose_basisMatrix_mulVec_w`. -/
theorem equation_10_1_6 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ grade (toEuclideanLin A) q₁) :
    let Q := Arnoldi.basisMatrix A q₁ k
    let r := (Arnoldi.w (toEuclideanLin A) q₁ (k - 1)).ofLp
    Qᵀ * A * Q = Lanczos.tridiag (toEuclideanLin A) q₁ k + vecMulVec (Qᵀ *ᵥ r)
        (Krylov.lastVec (1 : ℝ) k) ∧
      Qᵀ * A * Q = Lanczos.tridiag (toEuclideanLin A) q₁ k ∧ Qᵀ *ᵥ r = 0 := by
  intro Q r
  have h1 : Qᵀ * A * Q = Lanczos.tridiag (toEuclideanLin A) q₁ k + vecMulVec (Qᵀ *ᵥ r)
      (Krylov.lastVec (1 : ℝ) k) := by
    rw [Matrix.mul_assoc, equation_10_1_4 hA q₁ hk1, Matrix.mul_add, ← Matrix.mul_assoc,
      transpose_basisMatrix_mul_self q₁ hk, Matrix.one_mul, mul_vecMulVec]
  have h3 : Qᵀ *ᵥ r = 0 := by
    change (Arnoldi.basisMatrix A q₁ k)ᵀ *ᵥ (Arnoldi.w (toEuclideanLin A) q₁ (k - 1)).ofLp = 0
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h := Arnoldi.conjTranspose_basisMatrix_mulVec_w A q₁ k
    rw [conjTranspose_eq_transpose_of_trivial] at h
    simpa using h
  refine ⟨h1, ?_, h3⟩
  rw [h1, h3, zero_vecMulVec, add_zero]

/-- **Theorem 10.1.1.** Let `A` be symmetric and `q₁` a unit vector. With enough fuel (`n` passes),
Algorithm 10.1.1 runs until `k = m = rank K(A, q₁, n)`, and for every `1 ≤ k ≤ m` the computed
`Q_k = [q_1 | ⋯ | q_k]` and `T_k` (the tridiagonal matrix of the computed `α`, `β`, (10.1.5)) are
the backbone's `Arnoldi.basisMatrix` and `Lanczos.tridiag`, and
`A Q_k = Q_k T_k + r_k e_kᵀ` (10.1.4), `Q_kᵀ Q_k = I_k`, `ran(Q_k) = 𝒦(A, q₁, k)`. The book's
induction (orthogonality from the three-term recurrence) is the backbone's Gram–Schmidt
definition read backwards (`algorithm_10_1_1_spec`), and `m` is the rank of the Krylov matrix by
`Krylov.grade_eq_rank_krylovMatrix`. -/
theorem theorem_10_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) {fuel : ℕ} (hfuel : n ≤ fuel) :
    let s := Id.run (algorithm_10_1_1 pure A q₁ fuel)
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
    s.k = (krylovMatrix A q₁ n).rank ∧
      ∀ k, 1 ≤ k → k ≤ s.k →
        Matrix.of (fun i (j : Fin k) => s.q j i) = Arnoldi.basisMatrix A q k ∧
        symmTridiagonalOf s.alpha s.beta k = Lanczos.tridiag (toEuclideanLin A) q k ∧
        A * Arnoldi.basisMatrix A q k =
          Arnoldi.basisMatrix A q k * Lanczos.tridiag (toEuclideanLin A) q k +
            vecMulVec (Arnoldi.w (toEuclideanLin A) q (k - 1)).ofLp (Krylov.lastVec (1 : ℝ) k) ∧
        (Arnoldi.basisMatrix A q k)ᵀ * Arnoldi.basisMatrix A q k = 1 ∧
        LinearMap.range (toEuclideanLin (Arnoldi.basisMatrix A q k)) =
          Krylov.subspace (toEuclideanLin A) q k := by
  intro s q
  obtain ⟨hk, hvec, -⟩ := algorithm_10_1_1_spec hA hq fuel
  have hvec' : ∀ j < s.k, s.q j = (Arnoldi.vec (toEuclideanLin A) q j).ofLp ∧
      s.alpha j = Lanczos.alpha (toEuclideanLin A) q j ∧
      s.beta j = Lanczos.beta (toEuclideanLin A) q j := hvec
  have hgn : grade (toEuclideanLin A) q ≤ n :=
    (grade_le_finrank _ _).trans_eq finrank_euclideanSpace_fin
  have hsk : s.k = grade (toEuclideanLin A) q := by
    rw [show s.k = min fuel (grade (toEuclideanLin A) q) from hk]
    omega
  refine ⟨?_, fun k hk1 hks => ⟨?_, ?_, equation_10_1_4 hA q hk1,
    transpose_basisMatrix_mul_self q (hsk ▸ hks), Arnoldi.range_basisMatrix A q k⟩⟩
  · rw [hsk]
    have h := Krylov.grade_eq_rank_krylovMatrix A q₁
    rw [Fintype.card_fin] at h
    exact h
  · ext i j
    simp [Arnoldi.basisMatrix, (hvec' j (by omega)).1]
  · ext i j
    rw [symmTridiagonalOf, Lanczos.tridiag_apply, of_apply,
      (hvec' i (by omega)).2.1, (hvec' i (by omega)).2.2, (hvec' j (by omega)).2.2]

/-! ### Ritz approximations (§10.1.4) -/

/-- `Q_k y` as a combination of the Lanczos vectors: `Q_k y = ∑ⱼ yⱼ q_{j+1}`. -/
theorem toLp_basisMatrix_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (y : Fin k → ℝ) :
    (WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ k *ᵥ y) : EuclideanSpace ℝ (Fin n)) =
      ∑ j, y j • Arnoldi.vec (toEuclideanLin A) q₁ j := by
  rw [← toEuclideanLin_toLp, toEuclideanLin_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

/-- **Ritz pairs from the Lanczos process** (§10.1.4, the claim after (10.1.7)): if
`S_kᵀ T_k S_k = Θ_k = diag(θ_1, …, θ_k)` is a Schur decomposition of `T_k` and `Y_k = Q_k S_k`,
then every `(θ_i, y_i)` is a Ritz pair of `A` with respect to `𝒦(A, q₁, k)`: `y_i ∈ 𝒦`, `y_i ≠ 0`
and `A y_i − θ_i y_i ⟂ 𝒦` (`k ≤ m`). Stated for each column: any eigenpair `T_k s = θ s`,
`s ≠ 0`, of `T_k`, so for every Schur decomposition. Backbone
`Arnoldi.isRitzPair_of_mulVec_eq_smul` with `Lanczos.hessenbergSq_eq_map_tridiag`. -/
theorem isRitzPair_lanczos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k ≤ grade (toEuclideanLin A) q₁) {θ : ℝ}
    {s : Fin k → ℝ} (hs : s ≠ 0) (hTs : Lanczos.tridiag (toEuclideanLin A) q₁ k *ᵥ s = θ • s) :
    Krylov.IsRitzPair (toEuclideanLin A) (Krylov.subspace (toEuclideanLin A) q₁ k) θ
      (WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ k *ᵥ s)) := by
  rw [toLp_basisMatrix_mulVec]
  refine Arnoldi.isRitzPair_of_mulVec_eq_smul _ q₁ hk hs ?_
  rw [Lanczos.hessenbergSq_eq_map_tridiag q₁ hA.isSymmetric_toEuclideanLin]
  simpa using hTs

/-- The residual of a Lanczos Ritz pair: `A y − θ y = s_{k} r_k`, `s_k` the last entry of the
eigenvector `s` of `T_k` (`k = k' + 1`). -/
private theorem ritz_residual_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) {θ : ℝ} {s : Fin (k + 1) → ℝ}
    (hTs : Lanczos.tridiag (toEuclideanLin A) q₁ (k + 1) *ᵥ s = θ • s) :
    toEuclideanLin A (WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ s)) -
        θ • WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ s) =
      s (Fin.last k) • Arnoldi.w (toEuclideanLin A) q₁ k := by
  have hy : (Arnoldi.hessenbergSq (toEuclideanLin A) q₁ (k + 1)).mulVec s = θ • s := by
    rw [Lanczos.hessenbergSq_eq_map_tridiag q₁ hA.isSymmetric_toEuclideanLin]
    simpa using hTs
  rw [toLp_basisMatrix_mulVec, Arnoldi.apply_sub_smul_sum_eq _ q₁ k _ _ hy,
    Arnoldi.coeff_succ_self, Arnoldi.vec_succ_eq]
  rcases eq_or_ne (Arnoldi.w (toEuclideanLin A) q₁ k) 0 with h0 | h0
  · simp [h0]
  · have hn : ‖Arnoldi.w (toEuclideanLin A) q₁ k‖ ≠ 0 := norm_ne_zero_iff.2 h0
    simp only [RCLike.ofReal_real_eq_id, id, smul_smul]
    congr 1
    field_simp

/-- **(10.1.8).** In the setting of `isRitzPair_lanczos`, for `1 ≤ k` and a unit eigenvector `s`
of `T_k` (a column of `S_k`) with eigenvalue `θ`, and `y = Q_k s`:
`A y − θ y = s_k r_k`, hence `‖A y − θ y‖₂ = |β_k| |s_k|` (`β_k` the book's, the
backbone's `Lanczos.beta _ q₁ (k − 1)`, and `s_k` the last entry of `s`), and `|s_k| ≤ 1`.
Backbone `Arnoldi.apply_sub_smul_sum_eq`. -/
theorem equation_10_1_8 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) {θ : ℝ} {s : Fin k → ℝ}
    (hs : ‖(WithLp.toLp 2 s : EuclideanSpace ℝ (Fin k))‖ = 1)
    (hTs : Lanczos.tridiag (toEuclideanLin A) q₁ k *ᵥ s = θ • s) :
    let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ k *ᵥ s)
    let sk := s ⟨k - 1, by omega⟩
    toEuclideanLin A y - θ • y = sk • Arnoldi.w (toEuclideanLin A) q₁ (k - 1) ∧
      ‖toEuclideanLin A y - θ • y‖ = |Lanczos.beta (toEuclideanLin A) q₁ (k - 1)| * |sk| ∧
      |sk| ≤ 1 := by
  intro y sk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlast : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp)
  have hres := ritz_residual_eq hA q₁ k hTs
  have hsk : sk = s (Fin.last k) := by simp only [sk, hlast]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hsk, Nat.add_sub_cancel]
    exact hres
  · simp only [hsk, Nat.add_sub_cancel]
    rw [hres, norm_smul, Real.norm_eq_abs, Lanczos.beta, abs_of_nonneg (norm_nonneg _),
      mul_comm]
  · rw [← Real.norm_eq_abs, ← hs]
    exact PiLp.norm_apply_le (WithLp.toLp 2 s : EuclideanSpace ℝ (Fin (k + 1))) _

/-- **The Ritz value error bound** (§10.1.4, the display after (10.1.8)): for a unit eigenvector
`s` of `T_k` with eigenvalue `θ`, some eigenvalue `μ` of `A` satisfies `|θ − μ| ≤ |β_k| |s_k|`.
The book derives it from Corollary 8.1.6 with `E = −s_k r_k yᵀ`, which is not symmetric, so that
corollary does not apply as cited; the statement is true by the symmetric residual bound
`LinearMap.IsSymmetric.exists_hasEigenvalue_dist_le` (some eigenvalue lies within `‖A y − θ y‖` of
`θ` for a unit `y`), with `equation_10_1_8`. -/
theorem exists_eigenvalue_dist_le_ritz {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ grade (toEuclideanLin A) q₁) {θ : ℝ} {s : Fin k → ℝ}
    (hs : ‖(WithLp.toLp 2 s : EuclideanSpace ℝ (Fin k))‖ = 1)
    (hTs : Lanczos.tridiag (toEuclideanLin A) q₁ k *ᵥ s = θ • s) :
    ∃ μ : ℝ, Module.End.HasEigenvalue (toEuclideanLin A) μ ∧
      |θ - μ| ≤ |Lanczos.beta (toEuclideanLin A) q₁ (k - 1)| * |s ⟨k - 1, by omega⟩| := by
  obtain ⟨h1, h2, -⟩ := equation_10_1_8 hA q₁ hk1 hs hTs
  set y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ k *ᵥ s) with hy
  have hny : ‖y‖ = 1 := by
    rw [hy, toLp_basisMatrix_mulVec, Krylov.norm_sum_smul_vec_eq _ q₁ _
      (fun j hj => absurd (lt_of_lt_of_le j.isLt hk) (not_lt.2 hj))]
    exact hs
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hny
    exact zero_ne_one hny
  obtain ⟨μ, hμ, hle⟩ := hA.isSymmetric_toEuclideanLin.exists_hasEigenvalue_dist_le θ hy0
  refine ⟨μ, hμ, ?_⟩
  have hle' : |μ - θ| ≤ ‖toEuclideanLin A y - θ • y‖ := by
    simpa only [hny, div_one, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id] using hle
  rw [abs_sub_comm, ← h2]
  exact hle'

/-- **Golub's rank-one modification** (§10.1.4, Golub (1974)): in the setting of (10.1.4), for
`1 ≤ k ≤ m`, scalars `τ, a, b` and `w = a q_k + b r_k`, `E = τ w wᵀ`,
`(A + E) Q_k = Q_k (T_k + τ a² e_k e_kᵀ) + (1 + τ a b) r_k e_kᵀ`. Hence if `1 + τ a b = 0`, every
eigenpair `(θ, y)` of `T̃_k = T_k + τ a² e_k e_kᵀ` gives the eigenpair `(θ, Q_k y)` of `A + E`. The
book takes `τ ∈ {−1, 1}`; the identity holds for every `τ`. Proof: `wᵀ Q_k = a e_kᵀ` (orthonormal
columns and `Q_kᵀ r_k = 0`, (10.1.6)), so `E Q_k = τ a w e_kᵀ`. -/
theorem golub_rankOne_modification {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ grade (toEuclideanLin A) q₁)
    (τ a b : ℝ) :
    let Q := Arnoldi.basisMatrix A q₁ k
    let r := (Arnoldi.w (toEuclideanLin A) q₁ (k - 1)).ofLp
    let e := Krylov.lastVec (1 : ℝ) k
    let w := a • (Q *ᵥ e) + b • r
    let T' := Lanczos.tridiag (toEuclideanLin A) q₁ k + (τ * a ^ 2) • vecMulVec e e
    (A + τ • vecMulVec w w) * Q = Q * T' + (1 + τ * a * b) • vecMulVec r e ∧
      (1 + τ * a * b = 0 → ∀ (θ : ℝ) (y : Fin k → ℝ), y ≠ 0 → T' *ᵥ y = θ • y →
        (A + τ • vecMulVec w w) *ᵥ (Q *ᵥ y) = θ • (Q *ᵥ y) ∧ Q *ᵥ y ≠ 0) := by
  intro Q r e w T'
  have hQ : Qᵀ * Q = 1 := transpose_basisMatrix_mul_self q₁ hk
  have hr : Qᵀ *ᵥ r = 0 := (equation_10_1_6 hA q₁ hk1 hk).2.2
  have hwQ : w ᵥ* Q = a • e := by
    rw [← mulVec_transpose]
    simp only [w, mulVec_add, mulVec_smul, hr, smul_zero, add_zero, mulVec_mulVec, hQ,
      one_mulVec]
  have hEQ : (τ • vecMulVec w w) * Q = (τ * a) • vecMulVec w e := by
    rw [Matrix.smul_mul, vecMulVec_mul, hwQ, vecMulVec_smul, smul_smul]
  have hmain : (A + τ • vecMulVec w w) * Q = Q * T' + (1 + τ * a * b) • vecMulVec r e := by
    rw [Matrix.add_mul, hEQ, equation_10_1_4 hA q₁ hk1]
    simp only [T', Matrix.mul_add, Matrix.mul_smul, mul_vecMulVec, w]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  refine ⟨hmain, fun hab θ y hy0 hy => ⟨?_, ?_⟩⟩
  · rw [mulVec_mulVec, hmain, add_mulVec, ← mulVec_mulVec, hy, hab, zero_smul, zero_mulVec,
      add_zero, mulVec_smul]
  · intro h
    apply hy0
    have := congrArg (Qᵀ *ᵥ ·) h
    simpa only [mulVec_mulVec, hQ, one_mulVec, mulVec_zero] using this

/-- The diagonal of Golub's modified tridiagonal matrix `T_k + c e_k e_kᵀ`: the Lanczos `α_j`, with
`c` added to the last one (`0`-based index `k − 1`). -/
private noncomputable def rankOneDiag (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (c : ℝ) : ℕ → ℝ :=
  fun j => Lanczos.alpha (toEuclideanLin A) q₁ j + if j + 1 = k then c else 0

/-- `T_k + c e_k e_kᵀ` is the symmetric tridiagonal matrix of `rankOneDiag` and the Lanczos `β`. -/
private theorem tridiag_add_eq_symmTridiagonalOf (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (c : ℝ) :
    Lanczos.tridiag (toEuclideanLin A) q₁ k +
        c • vecMulVec (Krylov.lastVec (1 : ℝ) k) (Krylov.lastVec 1 k) =
      symmTridiagonalOf (rankOneDiag A q₁ k c) (Lanczos.beta (toEuclideanLin A) q₁) k := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Krylov.lastVec,
    Lanczos.tridiag_apply, symmTridiagonalOf_apply, rankOneDiag, smul_eq_mul]
  by_cases hij : (i : ℕ) = j
  · rw [ite_eq_left hij, ite_eq_left hij, ← hij]
    by_cases h : (i : ℕ) + 1 = k
    · rw [ite_eq_left h, ite_eq_left h, mul_one, mul_one]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]
  · rw [ite_eq_right hij, ite_eq_right hij]
    have h0 : (if (i : ℕ) + 1 = k then (1 : ℝ) else 0) * (if (j : ℕ) + 1 = k then 1 else 0) =
        0 := by
      by_cases hi : (i : ℕ) + 1 = k
      · rw [ite_eq_right (show ¬(j : ℕ) + 1 = k by omega), mul_zero]
      · rw [ite_eq_right hi, zero_mul]
    rw [h0, mul_zero, add_zero]

/-- Golub's modified tridiagonal matrix `T_k + c e_k e_kᵀ` is symmetric. -/
theorem isSymm_tridiag_add_vecMulVec_lastVec (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (c : ℝ) :
    (Lanczos.tridiag (toEuclideanLin A) q₁ k +
      c • vecMulVec (Krylov.lastVec (1 : ℝ) k) (Krylov.lastVec 1 k)).IsSymm :=
  (Lanczos.tridiag_isSymm _ _ _).add
    ((Matrix.IsSymm.ext fun i j => by simp only [vecMulVec_apply, mul_comm]).smul c)

/-- **Golub's bracketing intervals** (§10.1.4, "Using Theorem 8.1.8, it can be shown that the
interval `[λ_i(T̃_k), λ_{i−1}(T̃_k)]` contains an eigenvalue of `A` for `i = 2 : k`"): with
`T̃_k = T_k + τ a² e_k e_kᵀ` and `1 + τ a b = 0`, for `1 ≤ k ≤ m` and every `0`-based `i ≥ 1`, some
eigenvalue `μ` of `A` satisfies `λ_{i+1}(T̃_k) ≤ μ ≤ λ_i(T̃_k)` (`Chapter08.symmEigenvalue`, sorted
decreasingly). Also the determinant formula `det(T̃_k − λI) = (α_k + τ a² − λ) p_{k−1}(λ) −
β_{k−1}² p_{k−2}(λ)`, `p_i(λ) = det(T_i − λ I_i)` (`k ≥ 2`). Proof: `T̃_k` is unreduced
(`β_j ≠ 0` below the grade), so its eigenvalues are simple (`Sturm.strictAnti_eigenvalues`); each is
an eigenvalue of `A + τ w wᵀ` (`golub_rankOne_modification`), and between two distinct eigenvalues
of `A + τ w wᵀ` lies an eigenvalue of `A = (A + τ w wᵀ) − τ w wᵀ` by the rank-one interlacing of
Theorem 8.1.8. The determinant is (8.4.2) (`Chapter08.equation_8_4_2`) for `T̃_k`. -/
theorem golub_rankOne_bracket {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ grade (toEuclideanLin A) q₁)
    (τ a b : ℝ) :
    let hT := isSymm_tridiag_add_vecMulVec_lastVec A q₁ k (τ * a ^ 2)
    (1 + τ * a * b = 0 → ∀ (i : Fin k) (hi : 1 ≤ (i : ℕ)),
      ∃ μ ∈ spectrum ℝ A, Chapter08.symmEigenvalue hT i ≤ μ ∧
        μ ≤ Chapter08.symmEigenvalue hT ⟨i - 1, by omega⟩) ∧
    (2 ≤ k → ∀ x : ℝ, (Lanczos.tridiag (toEuclideanLin A) q₁ k +
        (τ * a ^ 2) • vecMulVec (Krylov.lastVec (1 : ℝ) k) (Krylov.lastVec 1 k) - x • 1).det =
      (Lanczos.alpha (toEuclideanLin A) q₁ (k - 1) + τ * a ^ 2 - x) *
          (Lanczos.tridiag (toEuclideanLin A) q₁ (k - 1) - x • 1).det -
        Lanczos.beta (toEuclideanLin A) q₁ (k - 2) ^ 2 *
          (Lanczos.tridiag (toEuclideanLin A) q₁ (k - 2) - x • 1).det) := by
  intro hT
  set T' := Lanczos.tridiag (toEuclideanLin A) q₁ k +
    (τ * a ^ 2) • vecMulVec (Krylov.lastVec (1 : ℝ) k) (Krylov.lastVec 1 k) with hT'
  have hT'eq : T' = symmTridiagonalOf (rankOneDiag A q₁ k (τ * a ^ 2))
      (Lanczos.beta (toEuclideanLin A) q₁) k :=
    tridiag_add_eq_symmTridiagonalOf A q₁ k _
  refine ⟨fun hab i hi => ?_, fun hk2 x => ?_⟩
  · have hβ : ∀ j, j + 1 < k → Lanczos.beta (toEuclideanLin A) q₁ j ≠ 0 := by
      intro j hj h
      have h' := (Lanczos.beta_eq_zero_iff q₁ hA.isSymmetric_toEuclideanLin j).1 h
      omega
    have hθ : Chapter08.symmEigenvalue hT =
        Sturm.eigenvalues (rankOneDiag A q₁ k (τ * a ^ 2)) (Lanczos.beta (toEuclideanLin A) q₁)
          k := by
      rw [Chapter08.symmEigenvalue_eq_sortedEigenvalues hT (isHermitian_iff_isSymm.2 hT)]
      exact IsHermitian.sortedEigenvalues_congr hT'eq _ _
    have hanti : StrictAnti (Chapter08.symmEigenvalue hT) :=
      hθ ▸ Sturm.strictAnti_eigenvalues _ _ k hβ
    have hmod := golub_rankOne_modification hA q₁ hk1 hk τ a b
    dsimp only at hmod
    obtain ⟨-, heig⟩ := hmod
    set w := a • (Arnoldi.basisMatrix A q₁ k *ᵥ Krylov.lastVec (1 : ℝ) k) +
      b • (Arnoldi.w (toEuclideanLin A) q₁ (k - 1)).ofLp with hw
    have hB : (A + τ • vecMulVec w w).IsSymm :=
      hA.add ((Matrix.IsSymm.ext fun i j => by simp only [vecMulVec_apply, mul_comm]).smul τ)
    have hμ : ∀ j : Fin k,
        ∃ p, Chapter08.symmEigenvalue hB p = Chapter08.symmEigenvalue hT j := by
      intro j
      obtain ⟨y, hy0, hy⟩ :=
        (mem_spectrum_iff_exists_mulVec_eq_smul _ _).1 (Chapter08.symmEigenvalue_mem_spectrum hT j)
      obtain ⟨h1, h2⟩ := heig hab _ y hy0 hy
      have hmem := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).2 ⟨_, h2, h1⟩
      rw [Chapter08.spectrum_eq_range_symmEigenvalue hB] at hmem
      exact hmem
    obtain ⟨p, hp⟩ := hμ ⟨i - 1, by omega⟩
    obtain ⟨q, hq⟩ := hμ i
    have hlt : Chapter08.symmEigenvalue hT i < Chapter08.symmEigenvalue hT ⟨i - 1, by omega⟩ :=
      hanti (Fin.lt_def.2 (by simp only; omega))
    have hpq : (p : ℕ) < q := by
      by_contra h
      have h' := Chapter08.antitone_symmEigenvalue hB (Fin.le_def.2 (not_lt.1 h))
      rw [hp, hq] at h'
      linarith
    have h8 := Chapter08.theorem_8_1_8 hA w τ hB
    rcases le_total 0 τ with hτ | hτ
    · have hq1 : 1 ≤ (q : ℕ) := by omega
      refine ⟨Chapter08.symmEigenvalue hA ⟨q - 1, by omega⟩,
        Chapter08.symmEigenvalue_mem_spectrum hA _, ?_, ?_⟩
      · rw [← hq]
        exact (h8.1 hτ q).2 hq1
      · rw [← hp]
        exact (h8.1 hτ _).1.trans
          (Chapter08.antitone_symmEigenvalue hB (Fin.le_def.2 (by simp only; omega)))
    · have hp1 : (p : ℕ) + 1 < n := by have := q.isLt; omega
      refine ⟨Chapter08.symmEigenvalue hA ⟨p + 1, hp1⟩,
        Chapter08.symmEigenvalue_mem_spectrum hA _, ?_, ?_⟩
      · rw [← hq]
        exact (Chapter08.antitone_symmEigenvalue hB (Fin.le_def.2 (by simp only; omega))).trans
          (h8.2 hτ _).1
      · rw [← hp]
        exact (h8.2 hτ p).2 hp1
  · obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
    have hsub : ∀ s ≤ r + 1, symmTridiagonalOf (rankOneDiag A q₁ (r + 2) (τ * a ^ 2))
        (Lanczos.beta (toEuclideanLin A) q₁) s = Lanczos.tridiag (toEuclideanLin A) q₁ s := by
      intro s hs
      ext i j
      simp only [symmTridiagonalOf_apply, Lanczos.tridiag_apply, rankOneDiag]
      rw [ite_eq_right (show ¬((i : ℕ) + 1 = r + 2) by omega), add_zero]
    rw [← hT', hT'eq, (Chapter08.equation_8_4_2 _ _).2.2 r x, hsub (r + 1) le_rfl,
      hsub r (by omega), show r + 2 - 1 = r + 1 by omega, show r + 2 - 2 = r by omega]
    simp only [rankOneDiag, ite_true]

/-! ### Schur decompositions (10.1.9) -/

section Schur

variable {A Z : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}

/-- The columns `z_1, …, z_n` of an orthogonal `Z` (`Matrix.euclideanCol`), as an orthonormal basis
of `ℝⁿ`: the eigenvectors of a Schur decomposition `Zᵀ A Z = diag(λ)` (10.1.9). -/
noncomputable def schurBasis (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  OrthonormalBasis.mk (orthonormal_euclideanCol (by
      rw [conjTranspose_eq_transpose_of_trivial]; exact (mem_orthogonalGroup_iff' _ ℝ).1 hZ))
    (span_range_euclideanCol_eq_top
      (isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' _ ℝ).1 hZ))).ge

@[simp]
theorem schurBasis_apply (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    schurBasis hZ i = euclideanCol Z i := by
  simp only [schurBasis, OrthonormalBasis.coe_mk]

/-- The columns of the Schur factor are eigenvectors: `A z_i = λ_i z_i`. -/
theorem toEuclideanLin_euclideanCol_of_schur (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hZA : Zᵀ * A * Z = diagonal lam) (i : Fin n) :
    toEuclideanLin A (euclideanCol Z i) = lam i • euclideanCol Z i := by
  have hZZ : Zᵀ * Z = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hZ
  exact toEuclideanLin_euclideanCol_of_conj_eq_diagonal
    ((isUnit_iff_isUnit_det Z).2 (isUnit_det_of_left_inverse hZZ))
    (by rwa [inv_eq_left_inv hZZ]) i

/-- A matrix with a Schur decomposition `Zᵀ A Z = diag(λ)`, `Z` orthogonal, is symmetric:
`A = Z diag(λ) Zᵀ`. -/
theorem isSymm_of_schur (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hZA : Zᵀ * A * Z = diagonal lam) : A.IsSymm := by
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hA : A = Z * diagonal lam * Zᵀ := by
    calc A = (Z * Zᵀ) * A * (Z * Zᵀ) := by rw [hZZ, Matrix.one_mul, Matrix.mul_one]
      _ = Z * (Zᵀ * A * Z) * Zᵀ := by simp only [Matrix.mul_assoc]
      _ = Z * diagonal lam * Zᵀ := by rw [hZA]
  rw [hA, Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
    Matrix.mul_assoc]

/-- The sorted eigenvalues of `A` are the `λ` of any Schur decomposition with
`λ_1 ≥ ⋯ ≥ λ_n` (`LinearMap.IsSymmetric.eigenvalues_eq_of_apply_eq_ofReal_smul`). -/
theorem eigenvalues_eq_of_schur (hA : A.IsSymm) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hZA : Zᵀ * A * Z = diagonal lam) (hlam : Antitone lam) :
    hA.isSymmetric_toEuclideanLin.eigenvalues finrank_euclideanSpace_fin = lam :=
  hA.isSymmetric_toEuclideanLin.eigenvalues_eq_of_apply_eq_ofReal_smul _ (schurBasis hZ)
    (fun i => by rw [schurBasis_apply]; exact toEuclideanLin_euclideanCol_of_schur hZ hZA i) hlam

/-- The Schur decomposition of `−A`, with the order reversed: `Z' = [z_n ⋯ z_1]` and
`λ' = (−λ_n, …, −λ_1)`, again decreasing when `λ` is. -/
theorem schur_neg (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (hZA : Zᵀ * A * Z = diagonal lam) :
    Z.submatrix id Fin.rev ∈ orthogonalGroup (Fin n) ℝ ∧
      (Z.submatrix id Fin.rev)ᵀ * (-A) * Z.submatrix id Fin.rev =
        diagonal fun i => -lam i.rev := by
  have hZZ : Zᵀ * Z = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hZ
  have key : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (Z.submatrix id Fin.rev)ᵀ * M * Z.submatrix id Fin.rev =
        (Zᵀ * M * Z).submatrix Fin.rev Fin.rev := by
    intro M
    rw [submatrix_mul _ _ _ id _ Function.bijective_id,
      submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id, transpose_submatrix]
  refine ⟨(mem_orthogonalGroup_iff' _ ℝ).2 ?_, ?_⟩
  · have h := key 1
    rw [Matrix.mul_one, Matrix.mul_one, hZZ, submatrix_one _ Fin.rev_injective] at h
    exact h
  · rw [key, Matrix.mul_neg, Matrix.neg_mul, hZA]
    ext i j
    by_cases h : i = j <;> simp [h]

end Schur

/-! ### The Kaniel–Paige–Saad bounds (§10.1.5–10.1.6) -/

/-- The quadratic form of an operator with an orthonormal eigenbasis, minus its largest eigenvalue,
is bounded by the spread: `|xᵀAx − λ_1 ‖x‖²| ≤ (λ_1 − λ_n) ‖x‖²`. -/
private theorem abs_re_inner_sub_top_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {T : E →ₗ[ℝ] E} {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E)
    {lam : Fin N → ℝ} (hb : ∀ i, T (b i) = lam i • b i) (i0 il : Fin N)
    (h0 : ∀ j, lam j ≤ lam i0) (hl : ∀ j, lam il ≤ lam j) (x : E) :
    |RCLike.re (inner ℝ (T x) x) - lam i0 * ‖x‖ ^ 2| ≤ (lam i0 - lam il) * ‖x‖ ^ 2 := by
  have h1 := b.mul_norm_sq_sub_re_inner_eq_sum hb (lam i0) x
  have hx : ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using (b.sum_sq_norm_inner_right x).symm
  have hnn : 0 ≤ lam i0 * ‖x‖ ^ 2 - RCLike.re (inner ℝ (T x) x) := by
    rw [h1]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.2 (h0 i)) (sq_nonneg _)
  have hle : lam i0 * ‖x‖ ^ 2 - RCLike.re (inner ℝ (T x) x) ≤ (lam i0 - lam il) * ‖x‖ ^ 2 := by
    rw [h1, hx, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (by linarith [hl i]) (sq_nonneg _)
  rw [abs_sub_comm, abs_of_nonneg hnn]
  exact hle

/-- The quadratic form minus the smallest eigenvalue is bounded by the spread:
`|xᵀAx − λ_n ‖x‖²| ≤ (λ_1 − λ_n) ‖x‖²` — `abs_re_inner_sub_top_le` for `−A`. -/
private theorem abs_re_inner_sub_bot_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {T : E →ₗ[ℝ] E} {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E)
    {lam : Fin N → ℝ} (hb : ∀ i, T (b i) = lam i • b i) (i0 il : Fin N)
    (h0 : ∀ j, lam j ≤ lam i0) (hl : ∀ j, lam il ≤ lam j) (x : E) :
    |RCLike.re (inner ℝ (T x) x) - lam il * ‖x‖ ^ 2| ≤ (lam i0 - lam il) * ‖x‖ ^ 2 := by
  have h := abs_re_inner_sub_top_le (T := -T) b (lam := fun i => -lam i)
    (fun i => by rw [LinearMap.neg_apply, hb, neg_smul]) il i0
    (fun j => neg_le_neg (hl j)) (fun j => neg_le_neg (h0 j)) x
  have e : RCLike.re (inner ℝ ((-T) x) x) = -RCLike.re (inner ℝ (T x) x) := by
    simp [inner_neg_left]
  rw [e] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The Ritz values of `−A` are those of `A`, negated and in reverse order (below the grade). -/
private theorem ritzValues_neg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {q₁ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ k) = k) (i : Fin k) :
    Lanczos.ritzValues (toEuclideanLin (-A)) q₁ k i =
      -Lanczos.ritzValues (toEuclideanLin A) q₁ k i.rev := by
  set T := toEuclideanLin A with hTdef
  have hT : T.IsSymmetric := hA.isSymmetric_toEuclideanLin
  have hneg : toEuclideanLin (-A) = -T := map_neg _ _
  have hkneg : Module.finrank ℝ (Krylov.subspace (-T) q₁ k) = k := by
    rw [Krylov.subspace_neg]; exact hk
  rw [hneg, Lanczos.ritzValues_eq_eigenvalues_compression q₁ hT.neg hkneg,
    Lanczos.ritzValues_eq_eigenvalues_compression q₁ hT hk,
    hT.neg.eigenvalues_compression_congr (Krylov.subspace_neg T q₁ k) hkneg hk,
    LinearMap.IsSymmetric.eigenvalues_congr _
      (compression.isSymmetric T (Krylov.subspace T q₁ k) hT).neg
      (compression.neg T (Krylov.subspace T q₁ k)) hk,
    (compression.isSymmetric T (Krylov.subspace T q₁ k) hT).eigenvalues_neg hk]

/-- **Theorem 10.1.2 (Kaniel–Paige).** Let `A ∈ ℝ^{n×n}` be symmetric with Schur decomposition
`Zᵀ A Z = diag(λ_1, …, λ_n)` (10.1.9), `λ_1 ≥ ⋯ ≥ λ_n`, `Z = [z_1 ⋯ z_n]` orthogonal (any such
decomposition; `z_i` is `Matrix.euclideanCol Z`), and suppose `k` steps of the Lanczos iteration
have been performed (`dim 𝒦(A, q₁, k) = k`). If `θ_1` is the largest eigenvalue of `T_k`
(`Lanczos.ritzValues`), then `λ_1 ≥ θ_1 ≥ λ_1 − (λ_1 − λ_n) (tan φ_1 / c_{k−1}(1 + 2ρ_1))²`, where
`cos φ_1 = |q₁ᵀ z_1|`, `ρ_1 = (λ_1 − λ_2)/(λ_2 − λ_n)` (10.1.10) and `c_{k−1}` is the Chebyshev
polynomial of degree `k − 1`. The symmetry of `A` follows from the decomposition
(`isSymm_of_schur`). The book's implicit hypothesis is `q₁ᵀ z_1 ≠ 0` (so `tan φ_1` is
finite); **no gap hypothesis**: when `λ_2 = λ_n` or `λ_2 = λ_1`, `ρ_1` is `0` (Lean's `x / 0 = 0`),
`c_{k−1}(1) = 1`, and the claim is the `k`-free bound of the largest Ritz value
(`LinearMap.IsSymmetric.ritz_value_error_le` with the angle to `q₁`). Otherwise `λ_n < λ_2 < λ_1`
and this is the backbone's `Lanczos.kaniel_paige_saad` for the eigenbasis `z` at the first index
(empty deflation product). -/
theorem theorem_10_1_2 {A Z : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (hZA : Zᵀ * A * Z = diagonal lam) (hlam : Antitone lam)
    (hn : 2 ≤ n) {q₁ : EuclideanSpace ℝ (Fin n)} (hq₁ : ‖q₁‖ = 1) {k : ℕ} (hk0 : 1 ≤ k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ k) = k)
    (hc : inner ℝ q₁ (euclideanCol Z ⟨0, by omega⟩) ≠ 0) :
    let θ := Lanczos.ritzValues (toEuclideanLin A) q₁ k
    let φ₁ := (ℝ ∙ q₁).angle (euclideanCol Z ⟨0, by omega⟩)
    let ρ₁ := (lam ⟨0, by omega⟩ - lam ⟨1, by omega⟩) / (lam ⟨1, by omega⟩ - lam ⟨n - 1, by omega⟩)
    Real.cos φ₁ = |inner ℝ q₁ (euclideanCol Z ⟨0, by omega⟩)| ∧
      θ ⟨0, by omega⟩ ≤ lam ⟨0, by omega⟩ ∧
      lam ⟨0, by omega⟩ - (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) *
          (Real.tan φ₁ / (Chebyshev.T ℝ (k - 1 : ℕ)).eval (1 + 2 * ρ₁)) ^ 2 ≤ θ ⟨0, by omega⟩ := by
  intro θ φ₁ ρ₁
  set T := toEuclideanLin A with hTdef
  have hT : T.IsSymmetric := (isSymm_of_schur hZ hZA).isSymmetric_toEuclideanLin
  have hnE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set b := schurBasis hZ with hbdef
  have hbz : ∀ i, b i = euclideanCol Z i := schurBasis_apply hZ
  have hb : ∀ i, T (b i) = lam i • b i := fun i => by
    rw [hbz]; exact toEuclideanLin_euclideanCol_of_schur hZ hZA i
  have hlamE : hT.eigenvalues hnE = lam := hT.eigenvalues_eq_of_apply_eq_ofReal_smul hnE b hb hlam
  have hkn : k ≤ n := hk ▸ (Submodule.finrank_le _).trans_eq hnE
  have hθ : θ = (compression.isSymmetric T (Krylov.subspace T q₁ k) hT).eigenvalues hk :=
    Lanczos.ritzValues_eq_eigenvalues_compression q₁ hT hk
  have hq₁0 : q₁ ≠ 0 := by simp [← norm_pos_iff, hq₁]
  have hcos : Real.cos φ₁ = |inner ℝ q₁ (euclideanCol Z ⟨0, by omega⟩)| := by
    rw [Submodule.cos_angle, Submodule.cosAngle_span_singleton hq₁0, hq₁, ← hbz, b.norm_eq_one,
      mul_one, div_one, Real.norm_eq_abs]
  have htan : Real.tan φ₁ = (ℝ ∙ q₁).tanAngle (b ⟨0, by omega⟩) := by
    rw [hbz]
    exact Submodule.tan_angle _ (by rw [← hbz]; exact b.orthonormal.ne_zero _)
  have hup : θ ⟨0, by omega⟩ ≤ lam ⟨0, by omega⟩ := by
    have h := hT.eigenvalues_compression_le (Krylov.subspace T q₁ k) hnE hk hkn ⟨0, by omega⟩
    rw [hlamE] at h
    rw [hθ]
    exact h
  refine ⟨hcos, hup, ?_⟩
  by_cases hnd : lam ⟨1, by omega⟩ < lam ⟨0, by omega⟩ ∧ lam ⟨n - 1, by omega⟩ < lam ⟨1, by omega⟩
  · have hkps := Lanczos.kaniel_paige_saad b hb hlam hT hk ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl rfl
      (fun j => Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
      (fun j => Fin.le_iff_val_le_val.mpr (by simp; omega))
      (by rw [hbz, real_inner_comm]; exact hc) hnd.1 hnd.2
      (fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _))
      (k := k - 1) (by simp; omega)
    have hmin : IsMin (⟨0, by omega⟩ : Fin k) := fun j _ =>
      Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
    simp only [Finset.Iio_eq_empty.mpr hmin, Finset.prod_empty, one_mul, Set.mem_Icc] at hkps
    rw [hθ]
    simp only [ρ₁]
    rw [htan]
    linarith [hkps.2]
  · -- the degenerate case: `ρ_1 = 0` and `c_{k-1}(1) = 1`
    have hρ : ρ₁ = 0 := by
      rcases not_and_or.1 hnd with h | h
      · have h10 : lam ⟨1, by omega⟩ = lam ⟨0, by omega⟩ :=
          le_antisymm (hlam (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))) (not_lt.1 h)
        simp only [ρ₁, h10, sub_self, zero_div]
      · have h1l : lam ⟨n - 1, by omega⟩ = lam ⟨1, by omega⟩ :=
          le_antisymm (hlam (Fin.le_iff_val_le_val.mpr (by simp; omega))) (not_lt.1 h)
        simp only [ρ₁, h1l, sub_self, div_zero]
    rw [hρ, mul_zero, add_zero, Chebyshev.T_eval_one, div_one, htan]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e0 : (⟨0, by omega⟩ : Fin (n' + 1)) = 0 := Fin.ext (by simp)
    have el : (⟨n' + 1 - 1, by omega⟩ : Fin (n' + 1)) = Fin.last n' := Fin.ext (by simp)
    have ek : (⟨0, by omega⟩ : Fin (k' + 1)) = 0 := Fin.ext (by simp)
    rw [e0, el, ek]
    have hqK : q₁ ∈ Krylov.subspace T q₁ (k' + 1) := Krylov.self_mem_subspace T q₁ (by omega)
    have hle : (ℝ ∙ q₁) ≤ Krylov.subspace T q₁ (k' + 1) :=
      (Submodule.span_singleton_le_iff_mem _ _).2 hqK
    have hP1 : (ℝ ∙ q₁).starProjection (b 0) ≠ 0 :=
      Submodule.starProjection_span_singleton_ne_zero (by rw [hbz, ← e0, real_inner_comm]; exact hc)
    have hPK : (Krylov.subspace T q₁ (k' + 1)).starProjection (b 0) ≠ 0 := by
      intro h
      refine hP1 (norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _)))
      exact (Submodule.norm_starProjection_le_of_le hle _).trans (by rw [h, norm_zero])
    have hC := abs_re_inner_sub_top_le b hb 0 (Fin.last n')
      (fun j => hlam (Fin.zero_le j)) (fun j => hlam (Fin.le_last j))
    rw [← hlamE] at hC
    have hb0 : T (b 0) = hT.eigenvalues hnE 0 • b 0 := by rw [hlamE]; exact hb 0
    have h := hT.ritz_value_error_le hnE hk hC hb0 hPK
    rw [hlamE] at h
    have htanle := Submodule.tanAngle_le_of_le hle hP1
    have htan0 := (Krylov.subspace T q₁ (k' + 1)).tanAngle_nonneg (b 0)
    have hspread : 0 ≤ lam 0 - lam (Fin.last n') := by linarith [hlam (Fin.zero_le (Fin.last n'))]
    have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htan0 htanle 2) hspread
    have h2 : lam 0 - θ 0 ≤ (lam 0 - lam (Fin.last n')) *
        (Krylov.subspace T q₁ (k' + 1)).tanAngle (b 0) ^ 2 := by
      rw [hθ]
      exact h.2
    linarith [h2, hsq]

/-- **Corollary 10.1.3.** In the setting of Theorem 10.1.2, with `θ_k` the smallest eigenvalue of
`T_k`, `ρ_n = (λ_{n−1} − λ_n)/(λ_1 − λ_{n−1})` and `cos φ_n = |q₁ᵀ z_n|` (the book omits the
absolute value): `λ_n ≤ θ_k ≤ λ_n + (λ_1 − λ_n) (tan φ_n / c_{k−1}(1 + 2ρ_n))²`. As in the book,
"apply Theorem 10.1.2 with `A` replaced by `−A`": the Schur decomposition of `−A` with the order
reversed (`schur_neg`), whose first eigenvector is `z_n`, and the Ritz values of `−A`, which are
those of `A` negated and reversed (`Krylov.subspace_neg`, `LinearMap.IsSymmetric.eigenvalues_neg`).
No gap hypothesis is needed. -/
theorem corollary_10_1_3 {A Z : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (hZA : Zᵀ * A * Z = diagonal lam) (hlam : Antitone lam)
    (hn : 2 ≤ n) {q₁ : EuclideanSpace ℝ (Fin n)} (hq₁ : ‖q₁‖ = 1) {k : ℕ} (hk0 : 1 ≤ k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ k) = k)
    (hc : inner ℝ q₁ (euclideanCol Z ⟨n - 1, by omega⟩) ≠ 0) :
    let θ := Lanczos.ritzValues (toEuclideanLin A) q₁ k
    let φₙ := (ℝ ∙ q₁).angle (euclideanCol Z ⟨n - 1, by omega⟩)
    let ρₙ := (lam ⟨n - 2, by omega⟩ - lam ⟨n - 1, by omega⟩) /
      (lam ⟨0, by omega⟩ - lam ⟨n - 2, by omega⟩)
    Real.cos φₙ = |inner ℝ q₁ (euclideanCol Z ⟨n - 1, by omega⟩)| ∧
      lam ⟨n - 1, by omega⟩ ≤ θ ⟨k - 1, by omega⟩ ∧
      θ ⟨k - 1, by omega⟩ ≤ lam ⟨n - 1, by omega⟩ + (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) *
          (Real.tan φₙ / (Chebyshev.T ℝ (k - 1 : ℕ)).eval (1 + 2 * ρₙ)) ^ 2 := by
  intro θ φₙ ρₙ
  obtain ⟨hZ', hZA'⟩ := schur_neg hZ hZA
  have hlam' : Antitone fun i : Fin n => -lam i.rev :=
    fun i j hij => neg_le_neg (hlam (Fin.rev_le_rev.2 hij))
  have hk' : Module.finrank ℝ (Krylov.subspace (toEuclideanLin (-A)) q₁ k) = k := by
    rw [show toEuclideanLin (-A) = -toEuclideanLin A from map_neg _ _, Krylov.subspace_neg]
    exact hk
  have r0 : (⟨0, by omega⟩ : Fin n).rev = ⟨n - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
  have r1 : (⟨1, by omega⟩ : Fin n).rev = ⟨n - 2, by omega⟩ :=
    Fin.ext (by rw [Fin.val_rev])
  have rl : (⟨n - 1, by omega⟩ : Fin n).rev = ⟨0, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_rev]; omega)
  have hcol : euclideanCol (Z.submatrix id Fin.rev) ⟨0, by omega⟩ =
      euclideanCol Z ⟨n - 1, by omega⟩ := by
    change euclideanCol Z (Fin.rev ⟨0, by omega⟩) = _
    rw [r0]
  have hθ' : Lanczos.ritzValues (toEuclideanLin (-A)) q₁ k ⟨0, by omega⟩ =
      -θ ⟨k - 1, by omega⟩ := by
    rw [ritzValues_neg (isSymm_of_schur hZ hZA) hk]
    congr 2
  have h := theorem_10_1_2 hZ' hZA' hlam' hn hq₁ hk0 hk' (by rw [hcol]; exact hc)
  dsimp only at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [hcol] at h1 h3
  rw [hθ', r0] at h2
  rw [hθ', r0, r1, rl] at h3
  have harg : (-lam ⟨n - 1, by omega⟩ - -lam ⟨n - 2, by omega⟩) /
      (-lam ⟨n - 2, by omega⟩ - -lam ⟨0, by omega⟩) = ρₙ := by
    simp only [ρₙ]
    congr 1 <;> ring
  rw [harg] at h3
  refine ⟨h1, by linarith, ?_⟩
  simp only [φₙ]
  linarith

/-- **Theorem 10.1.4 (Kaniel–Paige–Saad).** In the setting of Theorem 10.1.2 (any Schur
decomposition `Zᵀ A Z = diag(λ)`, `λ_1 ≥ ⋯ ≥ λ_n`), for `1 ≤ i ≤ k` (`i` is `0`-based here) with
`θ_i = λ_i(T_k)`: `λ_i ≥ θ_i ≥ λ_i − (λ_1 − λ_n) (κ_i tan φ_i / c_{k−i}(1 + 2ρ_i))²`, where
`ρ_i = (λ_i − λ_{i+1})/(λ_{i+1} − λ_n)`, `κ_i = ∏_{j<i} (θ_j − λ_n)/(θ_j − λ_i)` and
`cos φ_i = |q₁ᵀ z_i|`. The hypotheses make the quantities meaningful: `λ_n < λ_{i+1} < λ_i`,
`θ_j > λ_i` for `j < i` (so `κ_i` is defined) and `q₁ᵀ z_i ≠ 0`. Backbone
`Lanczos.kaniel_paige_saad` for the eigenbasis `z`, whose `κ_i` is built from the Ritz values
exactly as here, with `Lanczos.ritzValues_eq_eigenvalues_compression`. -/
theorem theorem_10_1_4 {A Z : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (hZA : Zᵀ * A * Z = diagonal lam) (hlam : Antitone lam)
    {q₁ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ k) = k) (i : Fin k)
    (hin : (i : ℕ) + 1 < n) (hgap : lam ⟨i + 1, hin⟩ < lam ⟨i, by omega⟩)
    (hspread : lam ⟨n - 1, by omega⟩ < lam ⟨i + 1, hin⟩)
    (hθ : ∀ j : Fin k, j < i → lam ⟨i, by omega⟩ < Lanczos.ritzValues (toEuclideanLin A) q₁ k j)
    (hc : inner ℝ q₁ (euclideanCol Z ⟨i, by omega⟩) ≠ 0) :
    let θ := Lanczos.ritzValues (toEuclideanLin A) q₁ k
    let φ := (ℝ ∙ q₁).angle (euclideanCol Z ⟨i, by omega⟩)
    let ρ := (lam ⟨i, by omega⟩ - lam ⟨i + 1, hin⟩) / (lam ⟨i + 1, hin⟩ - lam ⟨n - 1, by omega⟩)
    let κ := ∏ j ∈ Finset.Iio i, (θ j - lam ⟨n - 1, by omega⟩) / (θ j - lam ⟨i, by omega⟩)
    θ i ≤ lam ⟨i, by omega⟩ ∧
      lam ⟨i, by omega⟩ - (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) *
          (κ * Real.tan φ / (Chebyshev.T ℝ (k - 1 - i : ℕ)).eval (1 + 2 * ρ)) ^ 2 ≤ θ i := by
  intro θ φ ρ κ
  set T := toEuclideanLin A with hTdef
  have hT : T.IsSymmetric := (isSymm_of_schur hZ hZA).isSymmetric_toEuclideanLin
  set b := schurBasis hZ with hbdef
  have hbz : ∀ i, b i = euclideanCol Z i := schurBasis_apply hZ
  have hb : ∀ i, T (b i) = lam i • b i := fun i => by
    rw [hbz]; exact toEuclideanLin_euclideanCol_of_schur hZ hZA i
  have hθc : θ = (compression.isSymmetric T (Krylov.subspace T q₁ k) hT).eigenvalues hk :=
    Lanczos.ritzValues_eq_eigenvalues_compression q₁ hT hk
  have htan : Real.tan φ = (ℝ ∙ q₁).tanAngle (b ⟨i, by omega⟩) := by
    rw [hbz]
    exact Submodule.tan_angle _ (by rw [← hbz]; exact b.orthonormal.ne_zero _)
  have hkps :=
    Lanczos.kaniel_paige_saad b hb hlam hT hk i ⟨i, by omega⟩ ⟨i + 1, hin⟩ ⟨0, by omega⟩
    ⟨n - 1, by omega⟩ rfl rfl (fun j => Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    (fun j => Fin.le_iff_val_le_val.mpr (by simp; omega))
    (by rw [hbz, real_inner_comm]; exact hc) hgap hspread
    (fun j hj => by rw [← hθc]; exact hθ j hj) (k := k - 1 - i) (by omega)
  simp only [Set.mem_Icc] at hkps
  simp only [ρ, κ, hθc]
  rw [htan]
  constructor <;> linarith [hkps.1, hkps.2]

/-- **(10.1.11), the power-method comparison.** For a Schur decomposition `Zᵀ A Z = diag(λ)` with
`λ_1 ≥ ⋯ ≥ λ_n ≥ 0`, `q₁ᵀ z_1 ≠ 0`, `v = A^{k−1} q₁` and `γ_1 = vᵀAv / vᵀv` (the Rayleigh quotient
of `v`): `λ_1 ≥ γ_1 ≥ λ_1 − (λ_1 − λ_n) tan²φ_1 (λ_2/λ_1)^{2(k−1)}`. "Set `p(x) = x^{k−1}` in the
proof of Theorem 10.1.2": `γ_1` is the Rayleigh quotient of the projection of `z_1` on `span {v}`
(`LinearMap.IsSymmetric.abs_sub_rayleighQuotient_starProjection_le`), and the angle between `z_1`
and `span {v}` has tangent at most `tan φ_1 (λ_2/λ_1)^{k−1}` by the eigen-expansion of
`A^{k−1} q₁` (`OrthonormalBasis.norm_aeval_apply_le_of_forall_repr`); `λ_n ≥ 0` gives
`|λ_i| ≤ λ_2` for `i ≥ 2`. When `λ_1 = 0` every eigenvalue vanishes and both sides are `0`. -/
theorem equation_10_1_11 {A Z : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin n) ℝ) (hZA : Zᵀ * A * Z = diagonal lam) (hlam : Antitone lam)
    (hn : 2 ≤ n) {q₁ : EuclideanSpace ℝ (Fin n)} (k : ℕ) (hnonneg : 0 ≤ lam ⟨n - 1, by omega⟩)
    (hc : inner ℝ q₁ (euclideanCol Z ⟨0, by omega⟩) ≠ 0) :
    let v := (toEuclideanLin A ^ (k - 1)) q₁
    let γ₁ := (toEuclideanLin A).rayleighQuotient v
    let φ₁ := (ℝ ∙ q₁).angle (euclideanCol Z ⟨0, by omega⟩)
    γ₁ ≤ lam ⟨0, by omega⟩ ∧
      lam ⟨0, by omega⟩ - (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) * Real.tan φ₁ ^ 2 *
          (lam ⟨1, by omega⟩ / lam ⟨0, by omega⟩) ^ (2 * (k - 1)) ≤ γ₁ := by
  intro v γ₁ φ₁
  set T := toEuclideanLin A with hTd
  have hT : T.IsSymmetric := (isSymm_of_schur hZ hZA).isSymmetric_toEuclideanLin
  set b := schurBasis hZ with hbdef
  have hbz : ∀ i, b i = euclideanCol Z i := schurBasis_apply hZ
  have hb : ∀ i, T (b i) = lam i • b i := fun i => by
    rw [hbz]; exact toEuclideanLin_euclideanCol_of_schur hZ hZA i
  set j := k - 1 with hj
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set il : Fin n := ⟨n - 1, by omega⟩ with hil
  have hlo : ∀ i, lam il ≤ lam i := fun i => hlam (Fin.le_def.2 (by simp [hil]; omega))
  have hhi : ∀ i, lam i ≤ lam i0 := fun i => hlam (Fin.le_def.2 (by simp [hi0]))
  have hφ : φ₁ = (ℝ ∙ q₁).angle (b i0) := by rw [hbz]
  -- the Rayleigh quotient lies in `[0, λ_1]`
  have hγ : 0 ≤ γ₁ ∧ γ₁ ≤ lam i0 := by
    rcases eq_or_ne v 0 with hv | hv
    · simp only [γ₁, hv, LinearMap.rayleighQuotient_apply_zero]
      exact ⟨le_rfl, hnonneg.trans (hhi il)⟩
    · have hnE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
      have hlamE : hT.eigenvalues hnE = lam :=
        hT.eigenvalues_eq_of_apply_eq_ofReal_smul hnE b hb hlam
      exact ⟨hnonneg.trans (hT.le_rayleighQuotient_of_forall hnE (by rw [hlamE]; exact hlo) hv),
        hT.rayleighQuotient_le_of_forall hnE (by rw [hlamE]; exact hhi) hv⟩
  refine ⟨hγ.2, ?_⟩
  rcases (hnonneg.trans (hhi il)).eq_or_lt with h0 | hpos
  · -- `λ_1 = 0`: all eigenvalues vanish
    have hl0 : lam il = 0 := le_antisymm (h0 ▸ hhi il) hnonneg
    rw [← h0, hl0]
    simpa using hγ.1
  have hz : ‖b i0‖ = 1 := b.norm_eq_one i0
  have hTz : T (b i0) = (lam i0 : ℝ) • b i0 := hb i0
  have hpowz' : ∀ m : ℕ, (T ^ m) (b i0) = lam i0 ^ m • b i0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hTz, smul_smul, pow_succ]
  have hpowz : (T ^ j) (b i0) = lam i0 ^ j • b i0 := hpowz' j
  have hinner : inner ℝ (b i0) v = lam i0 ^ j * inner ℝ (b i0) q₁ := by
    change inner ℝ (b i0) ((T ^ j) q₁) = _
    rw [← (hT.pow j) (b i0) q₁, hpowz, real_inner_smul_left]
  have hc' : inner ℝ (b i0) q₁ ≠ 0 := by rw [hbz, real_inner_comm]; exact hc
  have hlj : lam i0 ^ j ≠ 0 := pow_ne_zero _ hpos.ne'
  have hinner0 : inner ℝ (b i0) v ≠ 0 := by rw [hinner]; exact mul_ne_zero hlj hc'
  have hv0 : v ≠ 0 := fun h => hinner0 (by rw [h, inner_zero_right])
  -- the Rayleigh quotient of the projection of `z_1` on `span {v}`
  have hPv : (ℝ ∙ v).starProjection (b i0) ≠ 0 :=
    Submodule.starProjection_span_singleton_ne_zero hinner0
  have hC := abs_re_inner_sub_top_le b hb i0 il hhi hlo
  have h1 := hT.abs_sub_rayleighQuotient_starProjection_le (ℝ ∙ v) hC hTz hPv
  have hr : T.rayleighQuotient ((ℝ ∙ v).starProjection (b i0)) = γ₁ := by
    rw [Submodule.starProjection_singleton, LinearMap.rayleighQuotient_smul]
    rw [real_inner_comm]
    exact div_ne_zero hinner0 (by positivity)
  rw [hr] at h1
  -- the angle between `z_1` and `span {v}`
  set w := q₁ - inner ℝ (b i0) q₁ • b i0 with hw
  have hvw : v - inner ℝ (b i0) v • b i0 = (T ^ j) w := by
    rw [hw, map_sub, map_smul, hpowz, hinner, smul_smul, mul_comm]
  have hrepr0 : b.repr w i0 = 0 := by
    rw [OrthonormalBasis.repr_apply_apply, hw, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hz]
    ring
  have hnorm : ‖(T ^ j) w‖ ≤ lam i1 ^ j * ‖w‖ := by
    have h := b.norm_aeval_apply_le_of_forall_repr (A := T) (μ := fun i => lam i) hb
      (Polynomial.X ^ j) (pow_nonneg (hnonneg.trans (hlo i1)) j) (x := w) (fun i hi => by
        have hi0' : i ≠ i0 := fun h => hi (by rw [h, hrepr0])
        have h1i : i1 ≤ i := Fin.le_def.2 (by
          have : (i : ℕ) ≠ 0 := fun h => hi0' (Fin.ext (by simp [hi0, h]))
          simp only [hi1]; omega)
        have hlo' : 0 ≤ lam i := hnonneg.trans (hlo i)
        rw [Polynomial.eval_pow, Polynomial.eval_X, norm_pow, Real.norm_eq_abs, abs_of_nonneg hlo']
        exact pow_le_pow_left₀ hlo' (hlam h1i) j)
    rwa [Polynomial.aeval_X_pow] at h
  have htanv : (ℝ ∙ v).tanAngle (b i0) ≤ (lam i1 / lam i0) ^ j * (ℝ ∙ q₁).tanAngle (b i0) := by
    rw [Submodule.tanAngle_span_singleton hz v, Submodule.tanAngle_span_singleton hz q₁, hvw,
      hinner, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hpos, div_pow, ← hw]
    have hq0 : 0 < ‖(inner ℝ (b i0) q₁ : ℝ)‖ := norm_pos_iff.2 hc'
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖(T ^ j) w‖ * (lam i0 ^ j * ‖(inner ℝ (b i0) q₁ : ℝ)‖)
        ≤ lam i1 ^ j * ‖w‖ * (lam i0 ^ j * ‖(inner ℝ (b i0) q₁ : ℝ)‖) :=
          mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = lam i1 ^ j * ‖w‖ * (lam i0 ^ j * ‖(inner ℝ (b i0) q₁ : ℝ)‖) := rfl
  have htan : Real.tan φ₁ = (ℝ ∙ q₁).tanAngle (b i0) := by
    rw [hφ]
    exact Submodule.tan_angle _ (b.orthonormal.ne_zero _)
  have htan0 := (ℝ ∙ v).tanAngle_nonneg (b i0)
  have hspread : 0 ≤ lam i0 - lam il := by linarith [hhi il]
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htan0 htanv 2) hspread
  have hfin : lam i0 - γ₁ ≤ (lam i0 - lam il) * ((lam i1 / lam i0) ^ j *
      (ℝ ∙ q₁).tanAngle (b i0)) ^ 2 := by
    have := (abs_le.1 h1).2
    linarith
  rw [htan, show 2 * j = j * 2 by ring, pow_mul]
  nlinarith [hfin]

end GolubVanLoan.Chapter10
