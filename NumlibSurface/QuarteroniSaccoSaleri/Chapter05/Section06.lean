import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Numlib.Eigen.Deflation
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section05

/-!
# Quarteroni–Sacco–Saleri §5.6: the QR method for matrices in Hessenberg form

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.6, over the backbone `Numlib/LinearAlgebra/Matrix/QR` (Householder
reflectors, the tail reflector, the Householder reduction to Hessenberg form and the Givens QR
factorization of a Hessenberg matrix), `Numlib/LinearAlgebra/Matrix/PlaneRotation` (plane rotations
and the Givens pair), `Numlib/Eigen/Deflation` (Householder deflation) and
`Numlib/Eigen/QRAlgorithm` (the Hessenberg invariance of a QR step).

## Conventions

Vectors are `Fin n → ℝ` and `‖x‖₂` is the Euclidean norm `‖(WithLp.toLp 2 x : EuclideanSpace ℝ
(Fin n))‖`. The Householder matrix (5.38) is written as the book writes it, `equation_5_38 v = I −
2 v vᵀ / ‖v‖₂²`, and `equation_5_38_eq_householder` identifies it with the backbone's reflector of
the unit axis `v / ‖v‖₂`; the book's sign choice `±` in (5.39) and (5.42) is the backbone's
`+ sign(x_m)` (`Matrix.householderAxis`, `Matrix.phase` being the sign with `sign 0 = 1`), which
avoids cancellation. The Givens matrix (5.43) is `equation_5_43 i k θ`, whose entry `(i, k)` is
`sin θ`; in the backbone's convention (`Matrix.planeRotation i k c s`, entry `(i, k)` equal to `−s`)
it is `planeRotation i k (cos θ) (−sin θ)`, so the pair `(c, s)` of (5.44) and (5.51) is the
backbone's `(c, −s)` and `Matrix.givensPair` carries the opposite sign of `s`. Indices count from
`0`: the book's `P_(k)`, which keeps the first `k` components and works from the `(k+1)`-st on, has
its pivot at the index `k`.

The Householder method of §5.6.2 is written as the book's recursion (5.45), `hessenbergIter`, and
`hessenbergIter_eq` identifies it with the backbone's `Matrix.hessenbergIter`; the Givens QR
factorization of §5.6.3 is stated for the backbone's `Matrix.hessenbergGivensQR`, whose factors are
exhibited as the products of the book's rotations `G_j = G(j, j+1, θ_j)`.

## Contents

* `equation_5_38`, `equation_5_38_eq_householder`, `equation_5_38_isSymm`,
  `equation_5_38_mul_self`, `equation_5_38_mem_orthogonalGroup` — the Householder matrix.
* `equation_5_40`, `equation_5_41` — the reflector that annihilates a vector below one entry, and
  the one that acts on a tail of coordinates only, (5.39)–(5.42).
* `equation_5_43`, `equation_5_43_apply`, `equation_5_43_mem_orthogonalGroup`, `equation_5_44`,
  `equation_5_51` — Givens rotations and the annihilation of one coordinate.
* `remark_5_3` — Householder deflation.
* `hessenbergStep`, `hessenbergIter`, `hessenbergReduce`, `hessenbergQ` and their `_eq` lemmas,
  `equation_5_45`, `hessenbergReduce_isUpperHessenberg`, `exists_orthogonal_conj_isUpperHessenberg`,
  `remark_5_4` — the Householder reduction to Hessenberg form.
* `equation_5_47` — the Givens QR factorization of a Hessenberg matrix, (5.47)–(5.48).
* `isUpperHessenberg_qrIterate` — §5.6.4: Hessenberg form is preserved by the QR iteration.
* `equation_5_49` — applying a reflector is a rank-one update, (5.49)–(5.50).

## Readings and errata

Remark 5.3 prints "`H x₁ = α x₁`" for the reflector `H`; it should read `H x₁ = α e₁`, which is
what `v = x₁ ± ‖x₁‖₂ e₁` and (5.40) give and what the block form of `H A H` requires. The rounding
error estimate (5.46) and the unnumbered one after Program 30 are floating-point statements
without a model here (`equation_5_46`, not formalized). Examples 5.5–5.9 are numerical, operation
counts are prose, and Programs 29–35 are not nodes.
-/

open Finset Matrix Polynomial

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ}

/-! ### (5.38): Householder reflection matrices -/

/-- **(5.38), the Householder reflection matrix** of the Householder vector `v ∈ ℝⁿ`:
`P = I − 2 v vᵀ / ‖v‖₂²`, the reflection across the hyperplane `span{v}ᗮ`; the identity when
`v = 0`, where the book's formula is undefined. -/
noncomputable def equation_5_38 (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 - (2 / ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2) • vecMulVec v v

/-- The book's `‖v‖₂²` is the inner square `v ⬝ᵥ v`. -/
theorem norm_toLp_sq_eq_dotProduct (v : Fin N → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

/-- The Householder matrix of the zero vector is the identity. -/
@[simp]
theorem equation_5_38_zero : equation_5_38 (0 : Fin N → ℝ) = 1 := by
  simp [equation_5_38]

/-- **The book's Householder matrix is the backbone's reflector** of the normalized axis: for
`v ≠ 0`, `equation_5_38 v = Matrix.householder (v / ‖v‖₂)`. -/
theorem equation_5_38_eq_householder {v : Fin N → ℝ} (hv : v ≠ 0) :
    equation_5_38 v =
      householder ((‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖)⁻¹ • v) := by
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by simpa using hv)
  rw [equation_5_38, householder, star_trivial, smul_vecMulVec, vecMulVec_smul, smul_smul,
    smul_smul]
  congr 2
  field_simp

/-- A Householder matrix is symmetric. -/
theorem equation_5_38_isSymm (v : Fin N → ℝ) : (equation_5_38 v).IsSymm := by
  rw [IsSymm, equation_5_38, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

/-- The axis `v / ‖v‖₂` of a nonzero `v` is a unit vector, in the form the backbone's reflector
lemmas take. -/
theorem star_dotProduct_normalize_self {v : Fin N → ℝ} (hv : v ≠ 0) :
    star ((‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖)⁻¹ • v) ⬝ᵥ
      (‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖)⁻¹ • v = 1 := by
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by simpa using hv)
  rw [star_trivial, smul_dotProduct, dotProduct_smul, ← norm_toLp_sq_eq_dotProduct, smul_eq_mul,
    smul_eq_mul]
  field_simp

/-- A Householder matrix is an involution, `P P = I`: the backbone's
`Matrix.householder_mul_self`. -/
theorem equation_5_38_mul_self {v : Fin N → ℝ} (hv : v ≠ 0) :
    equation_5_38 v * equation_5_38 v = 1 := by
  rw [equation_5_38_eq_householder hv]
  exact householder_mul_self (star_dotProduct_normalize_self hv)

/-- A Householder matrix is orthogonal: the backbone's `Matrix.householder_mem_unitaryGroup`. -/
theorem equation_5_38_mem_orthogonalGroup {v : Fin N → ℝ} (hv : v ≠ 0) :
    equation_5_38 v ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  rw [equation_5_38_eq_householder hv]
  exact householder_mem_unitaryGroup (star_dotProduct_normalize_self hv)

/-! ### (5.39)–(5.42): reflectors that annihilate coordinates -/

-- TODO(backbone): `Matrix.householderAxis_ne_zero` is private in `Numlib/LinearAlgebra/Matrix/QR`;
-- this is the same statement, recovered from the unit length of `Matrix.householderVec`.
/-- The axis `x + sign(x_m) ‖x‖₂ e_m` of (5.39) is nonzero when `x` is. -/
theorem householderAxis_ne_zero {x : Fin N → ℝ} (hx : x ≠ 0) (m : Fin N) :
    householderAxis x m ≠ 0 := by
  intro h
  have h1 := star_dotProduct_householderVec_self hx m
  have h0 : householderVec x m = 0 := by
    change (‖(WithLp.toLp 2 (householderAxis x m) : EuclideanSpace ℝ (Fin N))‖)⁻¹ •
      householderAxis x m = 0
    rw [h, smul_zero]
  rw [h0, star_zero, zero_dotProduct] at h1
  exact zero_ne_one h1

/-- **The book's reflector of the axis (5.39) is the backbone's**: for every `x` and `m`,
`equation_5_38 (householderAxis x m) = householder (householderVec x m)`, the backbone's unit
vector `householderVec x m` being the normalized axis (or `0` when `x = 0`, both sides then being
the identity). -/
theorem equation_5_38_householderAxis (x : Fin N → ℝ) (m : Fin N) :
    equation_5_38 (householderAxis x m) = householder (householderVec x m) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : householderAxis (0 : Fin N → ℝ) m = 0 := by
      simp [householderAxis]
    rw [h, householderVec_zero, householder_zero, equation_5_38_zero]
  · exact equation_5_38_eq_householder (householderAxis_ne_zero hx m)

/-- **(5.39)–(5.40).** Let `x ∈ ℝⁿ`, `x ≠ 0`, and let `v = x ± ‖x‖₂ e_m` be the Householder
vector (5.39), the sign being `sign(x_m)` (`Matrix.householderAxis x m`, with `sign 0 = 1`). Then
the Householder matrix `P` of `v` sets to zero all the components of `x` except the `m`-th one:
`P x = [0, …, 0, ∓‖x‖₂, 0, …, 0]ᵀ`, the surviving entry being `−sign(x_m) ‖x‖₂`, of modulus `‖x‖₂`.
Backbone `Matrix.householder_mulVec_eq_smul_single`. -/
theorem equation_5_40 {x : Fin N → ℝ} (hx : x ≠ 0) (m : Fin N) :
    let v := householderAxis x m
    v = x + (phase (x m) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖) •
        (Pi.single m 1 : Fin N → ℝ) ∧
      equation_5_38 v *ᵥ x =
        (-(phase (x m) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖)) •
          (Pi.single m 1 : Fin N → ℝ) ∧
      |-(phase (x m) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖)| =
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [equation_5_38_householderAxis]
    exact householder_mulVec_eq_smul_single hx m
  · rw [abs_neg, abs_mul, ← Real.norm_eq_abs, norm_phase, one_mul, abs_norm]

/-- **(5.41)–(5.42).** For `x ∈ ℝⁿ` and `k < n`, let `x^{(n−k)}` be the vector of the last `n − k`
components of `x` (embedded in `ℝⁿ` by zeros: `t r = x r` for `r ≥ k`, `t r = 0` for `r < k`) and
let `w^{(k)} = x^{(n−k)} ± ‖x^{(n−k)}‖₂ e₁^{(n−k)}` be the Householder vector (5.42), the sign being
`sign(x_k)` (`Matrix.householderAxis t k`). The Householder matrix `P_(k)` of `w^{(k)}` has the
block form `diag(I_k, R_{n−k})` of (5.41) — its axis vanishes on the first `k` coordinates — and
the transformed vector `y = P_(k) x` reads `y_j = x_j` for `j < k`, `y_j = 0` for `j > k`, and
`y_k = ±‖x^{(n−k)}‖₂`, precisely `y_k = −sign(x_k) ‖x^{(n−k)}‖₂`. Backbone
`Matrix.householder_tail_mulVec` and `Matrix.householderTail_apply_of_lt`. -/
theorem equation_5_41 (x : Fin N → ℝ) {k : ℕ} (hk : k < N) :
    let t : Fin N → ℝ := fun r => if k ≤ (r : ℕ) then x r else 0
    let w := householderAxis t ⟨k, hk⟩
    (∀ i : Fin N, (i : ℕ) < k → w i = 0) ∧
      (∀ i : Fin N, (i : ℕ) < k → (equation_5_38 w *ᵥ x) i = x i) ∧
      (∀ i : Fin N, k < (i : ℕ) → (equation_5_38 w *ᵥ x) i = 0) ∧
      (equation_5_38 w *ᵥ x) ⟨k, hk⟩ =
        -(phase (x ⟨k, hk⟩) * ‖(WithLp.toLp 2 t : EuclideanSpace ℝ (Fin N))‖) ∧
      |(equation_5_38 w *ᵥ x) ⟨k, hk⟩| = ‖(WithLp.toLp 2 t : EuclideanSpace ℝ (Fin N))‖ := by
  intro t w
  have hP : equation_5_38 w = householder (householderTail x k) := by
    rw [householderTail_of_lt x hk]
    exact equation_5_38_householderAxis t ⟨k, hk⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · have hik : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; exact lt_irrefl _ hi
    change householderAxis t ⟨k, hk⟩ i = 0
    rw [householderAxis_apply_of_ne _ hik]
    exact ite_eq_right (not_le.2 hi)
  · rw [hP]
    exact householder_householderTail_mulVec_apply_of_lt x hi
  · rw [hP]
    exact householder_householderTail_mulVec_apply_of_gt x hi
  · rw [hP]
    exact householder_householderTail_mulVec_apply_self x hk
  · rw [hP, ← Real.norm_eq_abs]
    exact norm_householder_householderTail_mulVec_apply_self x hk

/-! ### (5.43)–(5.44): Givens rotation matrices -/

/-- **(5.43), the Givens rotation matrix** `G(i, k, θ) = I_n − Y`, the identity except for the
entries `g_ii = g_kk = cos θ`, `g_ik = sin θ` and `g_ki = −sin θ`. In the backbone's convention
(`Matrix.planeRotation i k c s` has `−s` in position `(i, k)`) it is
`planeRotation i k (cos θ) (−sin θ)`. -/
noncomputable def equation_5_43 (i k : Fin N) (θ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  planeRotation i k (Real.cos θ) (-Real.sin θ)

/-- The entries of the Givens matrix (5.43), for `i ≠ k`: `cos θ` at `(i, i)` and `(k, k)`,
`sin θ` at `(i, k)`, `−sin θ` at `(k, i)`, and the identity elsewhere. -/
theorem equation_5_43_apply {i k : Fin N} (hik : i ≠ k) (θ : ℝ) (p q : Fin N) :
    equation_5_43 i k θ p q =
      if p = i ∧ q = i then Real.cos θ
      else if p = k ∧ q = k then Real.cos θ
      else if p = i ∧ q = k then Real.sin θ
      else if p = k ∧ q = i then -Real.sin θ
      else if p = q then 1 else 0 := by
  rw [equation_5_43, planeRotation_apply hik]
  by_cases hpi : p = i <;> by_cases hpk : p = k <;> by_cases hqi : q = i <;>
    by_cases hqk : q = k <;> simp_all [hik.symm]

/-- The Givens matrix is orthogonal: `Matrix.planeRotation_mem_orthogonalGroup` with
`cos² θ + sin² θ = 1`. -/
theorem equation_5_43_mem_orthogonalGroup {i k : Fin N} (hik : i ≠ k) (θ : ℝ) :
    equation_5_43 i k θ ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  planeRotation_mem_orthogonalGroup hik (by rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ)

/-- **(5.44).** For `x ∈ ℝⁿ`, the product `y = G(i, k, θ)ᵀ x` rotates `x` counterclockwise by `θ`
in the coordinate plane `(x_i, x_k)`: with `c = cos θ`, `s = sin θ`, `y_j = x_j` for `j ≠ i, k`,
`y_i = c x_i − s x_k` and `y_k = s x_i + c x_k`. Backbone
`Matrix.transpose_planeRotation_mulVec_apply`. -/
theorem equation_5_44 {i k : Fin N} (hik : i ≠ k) (θ : ℝ) (x : Fin N → ℝ) :
    let y := (equation_5_43 i k θ)ᵀ *ᵥ x
    (∀ j, j ≠ i → j ≠ k → y j = x j) ∧
      y i = Real.cos θ * x i - Real.sin θ * x k ∧
      y k = Real.sin θ * x i + Real.cos θ * x k := by
  refine ⟨fun j hji hjk => ?_, ?_, ?_⟩
  · rw [equation_5_43, transpose_planeRotation_mulVec_apply hik, ite_eq_right hji, ite_eq_right hjk]
  · rw [equation_5_43, transpose_planeRotation_mulVec_apply hik, ite_eq_left rfl]
    ring
  · rw [equation_5_43, transpose_planeRotation_mulVec_apply hik, ite_eq_right hik.symm,
      ite_eq_left rfl]
    ring

-- TODO(backbone): a point of the unit circle is `(cos θ, sin θ)`; natural home
-- `Mathlib/Analysis/SpecialFunctions/Complex/Arg`, beside `Complex.norm_eq_one_iff`.
/-- A pair `(c, s)` with `c² + s² = 1` is `(cos θ, sin θ)` for some angle `θ`. -/
theorem exists_cos_eq_sin_eq {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hz : ‖(⟨c, s⟩ : ℂ)‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_mk, ← h]
    ring
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).1 hz
  refine ⟨θ, ?_, ?_⟩
  · have := congrArg Complex.re hθ
    rwa [Complex.exp_ofReal_mul_I_re] at this
  · have := congrArg Complex.im hθ
    rwa [Complex.exp_ofReal_mul_I_im] at this

/-- **(5.44), the annihilating choice, and (5.51).** Let `α_ik = √(x_i² + x_k²) > 0`. If `θ` is
chosen with `c = cos θ = x_i/α_ik` and `s = sin θ = −x_k/α_ik` (that is, `θ = arctan(−x_k/x_i)`) —
such a `θ` exists — then `y = G(i, k, θ)ᵀ x` has `y_k = 0`, `y_i = α_ik` and `y_j = x_j` for
`j ≠ i, k`: this is the system (5.51), `[c −s; s c] [x_i; x_k] = [r; 0]`. The pair `(c, −s)` is
the backbone's `Matrix.givensPair (x i) (x k)`, and the annihilation is
`Matrix.transpose_planeRotation_givensPair_mulVec`. -/
theorem equation_5_51 {i k : Fin N} (hik : i ≠ k) (x : Fin N → ℝ) (hx : ¬ (x i = 0 ∧ x k = 0)) :
    let α := √(x i ^ 2 + x k ^ 2)
    ∃ θ : ℝ, Real.cos θ = x i / α ∧ Real.sin θ = -(x k / α) ∧
      ((equation_5_43 i k θ)ᵀ *ᵥ x) k = 0 ∧ ((equation_5_43 i k θ)ᵀ *ᵥ x) i = α ∧
      ∀ j, j ≠ i → j ≠ k → ((equation_5_43 i k θ)ᵀ *ᵥ x) j = x j := by
  intro α
  have hpair : givensPair (x i) (x k) = (x i / α, x k / α) := givensPair_of_not _ _ hx
  have hsq : (x i / α) ^ 2 + (-(x k / α)) ^ 2 = 1 := by
    have h := givensPair_sq_add_sq (x i) (x k)
    rw [hpair] at h
    rw [neg_sq]
    exact h
  obtain ⟨θ, hc, hs⟩ := exists_cos_eq_sin_eq hsq
  have hG : equation_5_43 i k θ =
      planeRotation i k (givensPair (x i) (x k)).1 (givensPair (x i) (x k)).2 := by
    rw [equation_5_43, hc, hs, neg_neg, hpair]
  obtain ⟨h1, h2, h3⟩ := transpose_planeRotation_givensPair_mulVec hik x
  exact ⟨θ, hc, hs, by rw [hG]; exact h1, by rw [hG]; exact h2, fun j hji hjk => by
    rw [hG]; exact h3 j hji hjk⟩

/-! ### Remark 5.3: Householder deflation -/

/-- **Remark 5.3 (Householder deflation for power iterations).** Let `A ∈ ℝ^{n×n}` and suppose the
eigenpair `(λ₁, x₁)`, `A x₁ = λ₁ x₁`, `x₁ ≠ 0`, has been computed. Let `H` be the Householder
matrix (5.38) of `v = x₁ ± ‖x₁‖₂ e₁`, so that `H x₁ = α e₁` for some `α ∈ ℝ` (the book prints
`H x₁ = α x₁`). Then `A₁ = H A H` has the block form `[λ₁ bᵀ; 0 A₂]`: its first column is `λ₁ e₁`,
and the eigenvalues of the trailing block `A₂ ∈ ℝ^{(n−1)×(n−1)}` are those of `A` except for `λ₁`,
with multiplicities: `A.charpoly = (X − λ₁) A₂.charpoly`. Backbone
`Matrix.householder_conj_eigenvector_apply` and `Matrix.charpoly_householder_conj_eigenvector`. -/
theorem remark_5_3 {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {x₁ : Fin (N + 1) → ℝ} {lam₁ : ℝ}
    (hx : A *ᵥ x₁ = lam₁ • x₁) (hx0 : x₁ ≠ 0) :
    let H := equation_5_38 (householderAxis x₁ 0)
    let A₁ := H * A * H
    (∃ α : ℝ, H *ᵥ x₁ = α • (Pi.single 0 1 : Fin (N + 1) → ℝ)) ∧
      (A₁ 0 0 = lam₁ ∧ ∀ i, i ≠ 0 → A₁ i 0 = 0) ∧
      A.charpoly = (X - C lam₁) * (A₁.submatrix Fin.succ Fin.succ).charpoly := by
  intro H A₁
  have hH : H = householder (householderVec x₁ 0) := equation_5_38_householderAxis x₁ 0
  refine ⟨⟨_, by rw [hH]; exact householder_mulVec_eq_smul_single hx0 0⟩, ⟨?_, fun i hi => ?_⟩, ?_⟩
  · have h := householder_conj_eigenvector_apply A hx hx0 0 0
    rwa [ite_eq_left rfl, ← hH] at h
  · have h := householder_conj_eigenvector_apply A hx hx0 0 i
    rwa [ite_eq_right hi, ← hH] at h
  · have h := charpoly_householder_conj_eigenvector A hx hx0
    rwa [← hH] at h

/-! ### §5.6.2: the Householder reduction to Hessenberg form -/

/-- The Householder matrix `P_(k)` of the `k`-th step of the Householder method (5.45): the matrix
(5.41) built, as in `equation_5_41`, from the `k`-th column of the current matrix `A` with pivot
`k + 1`, so that it sets to zero the entries in positions `k + 2, …, n` of that column (the book
counts from `1`; here the column is `k` and the pivot `k + 1`, both from `0`). It is the identity
when there is nothing to annihilate, `k + 1 ≥ n`. -/
noncomputable def householderStepMatrix (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  if h : k + 1 < N then
    equation_5_38 (householderAxis
      (fun i : Fin N => if k + 1 ≤ (i : ℕ) then A i ⟨k, by omega⟩ else 0) ⟨k + 1, h⟩)
  else 1

/-- **(5.45), one step of the Householder method**: `A^{(k)} = P_(k)ᵀ A^{(k−1)} P_(k)`. -/
noncomputable def hessenbergStep (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (householderStepMatrix A k)ᵀ * A * householderStepMatrix A k

/-- **The Householder method, §5.6.2**: the sequence `A^{(0)} = A`,
`A^{(k)} = P_(k)ᵀ A^{(k−1)} P_(k)` of matrices orthogonally similar to `A`, (5.45). -/
noncomputable def hessenbergIter (A : Matrix (Fin N) (Fin N) ℝ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => A
  | k + 1 => hessenbergStep (hessenbergIter A k) k

/-- The accumulated orthogonal matrix `Q_(k) = P_(1) ⋯ P_(k)` of (5.45). -/
noncomputable def hessenbergQIter (A : Matrix (Fin N) (Fin N) ℝ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 1
  | k + 1 => hessenbergQIter A k * householderStepMatrix (hessenbergIter A k) k

/-- **The Hessenberg form `H = A^{(n−2)}`** produced by the `n − 2` steps of the Householder
method (§5.6.2, Program 29). -/
noncomputable def hessenbergReduce (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  hessenbergIter A (N - 2)

/-- **The orthogonal matrix `Q = P_(1) ⋯ P_(n−2)`** of the Householder method, with `H = Qᵀ A Q`
(§5.6.2, Program 29). -/
noncomputable def hessenbergQ (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  hessenbergQIter A (N - 2)

/-- **The book's `P_(k)` is the backbone's step reflector**:
`householderStepMatrix A k = Matrix.hessenbergReflector A k`. -/
theorem householderStepMatrix_eq (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    householderStepMatrix A k = hessenbergReflector A k := by
  unfold householderStepMatrix
  by_cases h : k + 1 < N
  · rw [dite_eq_left h, hessenbergReflector_of_lt A (by omega),
      householderTail_of_lt _ (show k + 1 < N from h), equation_5_38_householderAxis]
  · rw [dite_eq_right h]
    by_cases hk : k < N
    · rw [hessenbergReflector_of_lt A hk, householderTail_of_le _ (by omega), householder_zero]
    · rw [hessenbergReflector_of_le A (not_lt.1 hk)]

/-- The book's step `P_(k)ᵀ A P_(k)` is the backbone's `Matrix.hessenbergStep`, the reflector being
symmetric. -/
theorem hessenbergStep_eq (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    hessenbergStep A k = Matrix.hessenbergStep A k := by
  rw [hessenbergStep, Matrix.hessenbergStep, householderStepMatrix_eq,
    ← conjTranspose_eq_transpose_of_trivial, (isHermitian_hessenbergReflector A k).eq]

/-- **The book's recursion (5.45) is the backbone's**: `hessenbergIter A k =
Matrix.hessenbergIter A k` and `hessenbergQIter A k = Matrix.hessenbergQIter A k`. -/
theorem hessenbergIter_eq (A : Matrix (Fin N) (Fin N) ℝ) :
    ∀ k, hessenbergIter A k = Matrix.hessenbergIter A k ∧
      hessenbergQIter A k = Matrix.hessenbergQIter A k
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := hessenbergIter_eq A k
    rw [hessenbergIter, hessenbergQIter, h1, h2, hessenbergStep_eq, householderStepMatrix_eq,
      Matrix.hessenbergIter_succ, Matrix.hessenbergQIter_succ]
    exact ⟨rfl, rfl⟩

/-- The book's `H` and `Q` are the backbone's `Matrix.hessenbergReduce` and
`Matrix.hessenbergQ`. -/
theorem hessenbergReduce_eq (A : Matrix (Fin N) (Fin N) ℝ) :
    hessenbergReduce A = Matrix.hessenbergReduce A ∧ hessenbergQ A = Matrix.hessenbergQ A :=
  hessenbergIter_eq A (N - 2)

/-- **(5.45).** The matrices `A^{(k)}` generated by the Householder method are orthogonally similar
to `A`: `A^{(k)} = P_(k)ᵀ A^{(k−1)} P_(k) = (P_(k) ⋯ P_(1))ᵀ A (P_(k) ⋯ P_(1)) = Q_(k)ᵀ A Q_(k)`
with `Q_(k) = P_(1) ⋯ P_(k)` orthogonal, for every `k`; in particular `H = Qᵀ A Q` for the
Hessenberg form `H = A^{(n−2)}` and the orthogonal `Q = P_(1) ⋯ P_(n−2)` (the output of
Program 29).
Backbone `Matrix.hessenbergIter_eq_conj`, `Matrix.hessenbergQIter_mem_unitaryGroup`,
`Matrix.hessenbergReduce_eq_conj` and `Matrix.hessenbergQ_mem_orthogonalGroup`. -/
theorem equation_5_45 (A : Matrix (Fin N) (Fin N) ℝ) :
    (∀ k, hessenbergQIter A k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      hessenbergIter A k = (hessenbergQIter A k)ᵀ * A * hessenbergQIter A k) ∧
      hessenbergQ A ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      hessenbergReduce A = (hessenbergQ A)ᵀ * A * hessenbergQ A := by
  have key : ∀ k, hessenbergQIter A k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      hessenbergIter A k = (hessenbergQIter A k)ᵀ * A * hessenbergQIter A k := fun k => by
    rw [(hessenbergIter_eq A k).1, (hessenbergIter_eq A k).2,
      ← conjTranspose_eq_transpose_of_trivial]
    exact ⟨hessenbergQIter_mem_unitaryGroup A k, hessenbergIter_eq_conj A k⟩
  exact ⟨key, (key (N - 2)).1, (key (N - 2)).2⟩

/-- **After `n − 2` steps of the Householder reduction we obtain a matrix `H = A^{(n−2)}` in upper
Hessenberg form** (§5.6.2): `Matrix.isUpperHessenberg_hessenbergReduce`. -/
theorem hessenbergReduce_isUpperHessenberg (A : Matrix (Fin N) (Fin N) ℝ) :
    (hessenbergReduce A).IsUpperHessenberg := by
  rw [(hessenbergReduce_eq A).1]
  exact isUpperHessenberg_hessenbergReduce A

/-- **Every `A ∈ ℝ^{n×n}` can be transformed by an orthogonal similarity into upper Hessenberg
form** (§5.6.2, the opening sentence): `Matrix.exists_unitary_conj_isUpperHessenberg`, or
`equation_5_45` with `hessenbergReduce_isUpperHessenberg`. -/
theorem exists_orthogonal_conj_isUpperHessenberg (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, (Qᵀ * A * Q).IsUpperHessenberg :=
  ⟨hessenbergQ A, (equation_5_45 A).2.1,
    (equation_5_45 A).2.2 ▸ hessenbergReduce_isUpperHessenberg A⟩

/-- **Remark 5.4 (the symmetric case).** If `A` is symmetric, the transformation (5.45) maintains
the property: `(A^{(k)})ᵀ = (Q_(k)ᵀ A Q_(k))ᵀ = A^{(k)}` for all `k`, so `H = A^{(n−2)}` is
symmetric and, being upper Hessenberg, tridiagonal. Backbone `Matrix.isSymm_hessenbergReduce` and
`Matrix.IsUpperHessenberg.isTridiagonal_of_isSymm`. -/
theorem remark_5_4 {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) :
    (∀ k, (hessenbergIter A k).IsSymm) ∧ (hessenbergReduce A).IsSymm ∧
      (hessenbergReduce A).IsTridiagonal := by
  have hsymm : ∀ k, (hessenbergIter A k).IsSymm := fun k => by
    rw [((equation_5_45 A).1 k).2, IsSymm, transpose_mul, transpose_mul, transpose_transpose,
      hA.eq, Matrix.mul_assoc]
  exact ⟨hsymm, hsymm (N - 2),
    (hessenbergReduce_isUpperHessenberg A).isTridiagonal_of_isSymm (hsymm (N - 2))⟩

/-! ### §5.6.3: the Givens QR factorization of a Hessenberg matrix -/

/-- **(5.47)–(5.48), the QR factorization of a matrix in Hessenberg form by Givens rotations.**
For `H ∈ ℝ^{n×n}` upper Hessenberg there are angles `θ_j`, `j = 1, …, n − 1`, such that with the
Givens rotations `G_j = G(j, j+1, θ_j)` of (5.43), each chosen according to (5.44) so as to
annihilate the entry `(j+1, j)` of `G_{j−1}ᵀ ⋯ G_1ᵀ H`, the matrix `R = G_{n−1}ᵀ ⋯ G_1ᵀ H` is upper
triangular, (5.47), and `H = Q R` with `Q = G_1 ⋯ G_{n−1}` orthogonal and itself upper Hessenberg,
(5.48). The pair `(Q, R)` is the backbone's `Matrix.hessenbergGivensQR H` (Program 31), the fold
of the `n − 1` rotations of the Givens pairs; `Matrix.hessenbergGivensQR_spec` gives the
factorization and `Matrix.exists_cos_eq_sin_eq` the angles. -/
theorem equation_5_47 {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg) :
    ∃ θ : ℕ → ℝ,
      let G : ℕ → Matrix (Fin N) (Fin N) ℝ := fun j =>
        if h : j + 1 < N then equation_5_43 ⟨j, by omega⟩ ⟨j + 1, h⟩ (θ j) else 1
      let Q := ((List.range (N - 1)).map G).prod
      let R := (((List.range (N - 1)).map G).map transpose).reverse.prod * H
      (hessenbergGivensQR H).1 = Q ∧ (hessenbergGivensQR H).2 = R ∧
        Q ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧ R.IsUpperTriangular ∧ H = Q * R ∧
        Q.IsUpperHessenberg := by
  -- the angles of the rotations along the fold
  have hθ : ∀ j : ℕ, ∃ θ : ℝ, ∀ h : j + 1 < N,
      equation_5_43 ⟨j, by omega⟩ ⟨j + 1, h⟩ θ =
        hessenbergGivensRotation (hessenbergGivensIter H j).2 j h := by
    intro j
    by_cases h : j + 1 < N
    · set R := (hessenbergGivensIter H j).2
      set a := R ⟨j, by omega⟩ ⟨j, by omega⟩
      set b := R ⟨j + 1, h⟩ ⟨j, by omega⟩
      have hsq : (givensPair a b).1 ^ 2 + (-(givensPair a b).2) ^ 2 = 1 := by
        rw [neg_sq]; exact givensPair_sq_add_sq a b
      obtain ⟨θ, hc, hs⟩ := exists_cos_eq_sin_eq hsq
      refine ⟨θ, fun h' => ?_⟩
      rw [equation_5_43, hc, hs, neg_neg]
      rfl
    · exact ⟨0, fun h' => absurd h' h⟩
  choose θ hθ using hθ
  refine ⟨θ, ?_⟩
  intro G Q R
  -- the accumulated factor after `j` steps is the product of the first `j` rotations
  have hiter : ∀ j, (hessenbergGivensIter H j).1 = ((List.range j).map G).prod := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ← ih]
      change (hessenbergGivensStep (hessenbergGivensIter H j) j).1 = _
      unfold hessenbergGivensStep
      by_cases h : j + 1 < N
      · rw [dite_eq_left h]
        change _ * hessenbergGivensRotation _ j h = _ * G j
        rw [show G j = equation_5_43 ⟨j, by omega⟩ ⟨j + 1, h⟩ (θ j) from dite_eq_left h, hθ j h]
      · rw [dite_eq_right h, show G j = 1 from dite_eq_right h, Matrix.mul_one]
  obtain ⟨hQ, hR, hQR, hQH⟩ := hessenbergGivensQR_spec hH
  have hQeq : (hessenbergGivensQR H).1 = Q := hiter (N - 1)
  have hQt : Qᵀ * Q = 1 := by
    rw [← hQeq]
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (mem_orthogonalGroup_iff' (Fin N) ℝ).1 hQ
  have hReq : (hessenbergGivensQR H).2 = R := by
    rw [hQeq] at hQR
    calc (hessenbergGivensQR H).2 = Qᵀ * Q * (hessenbergGivensQR H).2 := by
          rw [hQt, Matrix.one_mul]
      _ = Qᵀ * H := by rw [Matrix.mul_assoc, ← hQR]
      _ = R := by rw [transpose_list_prod]
  rw [hQeq] at hQ hQR hQH
  rw [hReq] at hR hQR
  exact ⟨hQeq, hReq, hQ, hR, hQR, hQH⟩

/-! ### §5.6.4: the QR iteration on a Hessenberg matrix -/

/-- **§5.6.4: the QR iteration preserves upper Hessenberg form.** If `T⁽⁰⁾ = H⁽⁰⁾` is nonsingular
and upper Hessenberg then every iterate `T⁽ᵏ⁾ = qrIterate H⁽⁰⁾ k` of (5.32) is upper Hessenberg,
and so is the orthogonal factor `Q⁽ᵏ⁺¹⁾ = qrQ (T⁽ᵏ⁾)` of each step (§5.6.3): `T⁽ᵏ⁺¹⁾ = R Q` is upper
triangular times upper Hessenberg. Backbone `Matrix.isUpperHessenberg_qrIterate` and
`Matrix.isUpperHessenberg_qrQ`. -/
theorem isUpperHessenberg_qrIterate {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperHessenberg)
    (hdet : IsUnit A.det) (k : ℕ) :
    (qrIterate A k).IsUpperHessenberg ∧ (qrQ (qrIterate A k)).IsUpperHessenberg := by
  rw [qrIterate_eq]
  exact ⟨Matrix.isUpperHessenberg_qrIterate hdet hA k,
    isUpperHessenberg_qrQ (isUnit_det_qrIterate hdet k)
      (Matrix.isUpperHessenberg_qrIterate hdet hA k)⟩

/-! ### §5.6.5: applying a reflector -/

/-- **(5.49)–(5.50).** If `P = I − β v vᵀ` is the Householder matrix (5.38) of `v ∈ ℝᵐ`, with
`β = 2/‖v‖₂²`, and `M ∈ ℝ^{m×m}`, then `P M = M − β v wᵀ` with `w = Mᵀ v`, (5.49), and
`M P = M − β w vᵀ` with `w = M v`, (5.50): applying a reflector is a matrix–vector product and a
rank-one update, and `P` is never formed. Backbone `Matrix.householder_mul_eq_sub_vecMulVec` and
`Matrix.mul_householder_eq_sub_vecMulVec` are the same identities for the normalized axis; here
they are read off (5.38) directly. -/
theorem equation_5_49 (v : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    let β := 2 / ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2
    equation_5_38 v * M = M - β • vecMulVec v (Mᵀ *ᵥ v) ∧
      M * equation_5_38 v = M - β • vecMulVec (M *ᵥ v) v := by
  intro β
  constructor
  · rw [equation_5_38, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul,
      mulVec_transpose]
  · rw [equation_5_38, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec]

end QuarteroniSaccoSaleri.Chapter05
