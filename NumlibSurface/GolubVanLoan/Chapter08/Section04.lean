import Numlib.Eigen.DivideConquer
import Numlib.Eigen.InverseEigenvalue
import Numlib.Eigen.Sturm
import Numlib.Nonlinear.Bisection
import NumlibSurface.GolubVanLoan.Chapter08.Section01

/-!
# Golub–Van Loan §8.4: more methods for tridiagonal problems

Surface file for [golub2013matrix] §8.4: the characteristic-polynomial recurrence (8.4.2) and
bisection, the Sturm sequence property (Theorem 8.4.1) and the bisection for `λ_k(T)` (8.4.3), the
`L D Lᵀ` inertia count, the eigensystem of a diagonal-plus-rank-one matrix (Lemma 8.4.2, Theorems
8.4.3–8.4.4), the tearing and merging of divide and conquer ((8.4.5)–(8.4.6), §8.4.4), and the
inverse tridiagonal eigenproblem ((8.4.7)–(8.4.12), §8.4.6).

## Conventions

The tridiagonal matrix (8.4.1) is the backbone's `Matrix.symmTridiagonalOf α β n` with `ℕ`-indexed
data: the book's `α_r` is `α (r - 1)` and `β_r` is `β (r - 1)`. Its Sturm sequence, the sign
convention at a zero, the sign-change count `a(λ)` and Givens' bisection are the backbone's
`Sturm.seq`, `Sturm.sign`, `Sturm.signChanges`, `Sturm.bisectionIterate`. `λ_k` is
`symmEigenvalue` of §8.1.

## Readings

(1) Theorem 8.4.1: with the book's own convention (a vanishing `p_r(λ)` takes the sign opposite to
`p_{r-1}(λ)`), `a(λ)` counts the eigenvalues `≤ λ`, not `< λ`; they differ exactly when `λ` is an
eigenvalue. (2) The bisection (8.4.3) tests `a(x) ≥ n - k`; the correct test is
`a(x) ≥ n - k + 1`. (3) The first bisection loop of §8.4.1 need not terminate in exact arithmetic
when the bracketed zero is `0`; the node states one step. (4) (8.4.12)'s denominator runs over
`j ≠ k` up to `n`. (5) (8.4.6)–(8.4.7) print `a_m` for `α_m` and a stray `λ'_{n-1}`.
(6) Theorem 8.4.4's `μ_r ≥ μ_{r+1}` across the deflation boundary is false (`d = (2, 1)`,
`z = (0, 1)`); the node orders the two parts separately.

## Not formalized

§8.4.5 (the parallel divide-and-conquer tree, Figure 8.4.1), the Lagrange-multiplier motivation
of §8.4.6, operation counts.
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter08

/-! ### §8.4.1 Eigenvalues by bisection -/

/-- `p_r(x) = det(T_r - x I)` is the value at `x` of the backbone's Sturm polynomial. -/
private theorem eval_seq_eq_det (α β : ℕ → ℝ) (r : ℕ) (x : ℝ) :
    (Sturm.seq α β r).eval x = (symmTridiagonalOf α β r - x • 1).det := by
  rw [Sturm.seq_eq_det, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [RingHom.mapMatrix_apply, h]

/-- **(8.4.2).** For the tridiagonal `T` of (8.4.1) and `p_r(x) = det(T_r - x I)`, `T_r` its leading
`r × r` principal submatrix: `T_r` is the tridiagonal matrix of the first `r` entries,
`p_1(x) = α_1 - x` and `p_r(x) = (α_r - x) p_{r-1}(x) - β_{r-1}² p_{r-2}(x)` (0-based data). -/
theorem equation_8_4_2 (α β : ℕ → ℝ) :
    (∀ r n (h : r ≤ n), (symmTridiagonalOf α β n).submatrix (Fin.castLE h) (Fin.castLE h) =
      symmTridiagonalOf α β r) ∧
    (∀ x : ℝ, (symmTridiagonalOf α β 1 - x • 1).det = α 0 - x) ∧
    ∀ (r : ℕ) (x : ℝ), (symmTridiagonalOf α β (r + 2) - x • 1).det =
      (α (r + 1) - x) * (symmTridiagonalOf α β (r + 1) - x • 1).det -
        β r ^ 2 * (symmTridiagonalOf α β r - x • 1).det := by
  refine ⟨fun r n h => ?_, fun x => ?_, fun r x => ?_⟩
  · ext i j
    simp [symmTridiagonalOf_apply]
  · rw [← eval_seq_eq_det, Sturm.seq_one]
    simp
  · rw [← eval_seq_eq_det, ← eval_seq_eq_det, ← eval_seq_eq_det, Sturm.seq_add_two]
    simp

/-- **§8.4.1, one step of the bisection loop on `p_n`.** If `y < z` and `p_n(y) p_n(z) < 0`, the
step `x = (y + z)/2`; `z = x` if `p_n(x) p_n(y) < 0`, else `y = x` gives `y' < z'` with
`z' - y' = (z - y)/2`, keeps a zero of `p_n` (an eigenvalue of `T`) in `[y', z']`, and keeps
`p_n(y') p_n(z') < 0` unless `p_n(x) = 0`. -/
theorem bisection_bracket (α β : ℕ → ℝ) (n : ℕ) {y z : ℝ} (hyz : y < z)
    (h : (symmTridiagonalOf α β n - y • 1).det * (symmTridiagonalOf α β n - z • 1).det < 0) :
    let p := fun t : ℝ => (symmTridiagonalOf α β n - t • 1).det
    let x := (y + z) / 2
    let yz' := if p x * p y < 0 then (y, x) else (x, z)
    yz'.1 < yz'.2 ∧ yz'.2 - yz'.1 = (z - y) / 2 ∧
      (∃ μ ∈ Set.Icc yz'.1 yz'.2, μ ∈ spectrum ℝ (symmTridiagonalOf α β n)) ∧
      (p x ≠ 0 → p yz'.1 * p yz'.2 < 0) := by
  intro p x yz'
  have h' : p y * p z < 0 := h
  have hp : Continuous p := by
    have : p = fun t => (Sturm.seq α β n).eval t :=
      funext fun t => (eval_seq_eq_det α β n t).symm
    rw [this]
    exact Polynomial.continuous _
  have hmem : ∀ μ, p μ = 0 → μ ∈ spectrum ℝ (symmTridiagonalOf α β n) := fun μ hμ => by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, Matrix.eval_charpoly]
    have : (scalar (Fin n) μ - symmTridiagonalOf α β n) =
        -(symmTridiagonalOf α β n - μ • 1) := by
      rw [neg_sub, smul_one_eq_diagonal]; rfl
    have hμ' : (symmTridiagonalOf α β n - μ • 1).det = 0 := hμ
    rw [this, det_neg, hμ', mul_zero]
  have hyx : y < x := by simp only [x]; linarith
  have hxz : x < z := by simp only [x]; linarith
  have hroot : ∀ a b, a ≤ b → p a * p b ≤ 0 → ∃ μ ∈ Set.Icc a b, μ ∈ spectrum ℝ _ :=
    fun a b hab hab' => by
      obtain ⟨μ, hμ, h0⟩ := exists_eq_zero_Icc_of_mul_nonpos hab hp.continuousOn hab'
      exact ⟨μ, hμ, hmem μ h0⟩
  by_cases hc : p x * p y < 0
  · simp only [yz', hc, ite_true]
    refine ⟨hyx, by simp only [x]; ring, hroot y x hyx.le (by linarith [mul_comm (p x) (p y)]),
      fun _ => by linarith [mul_comm (p x) (p y)]⟩
  · simp only [yz', hc, ite_false]
    have hy : p y ≠ 0 := fun h0 => by rw [h0, zero_mul] at h'; exact lt_irrefl _ h'
    have key : p x * p z * p y ^ 2 = (p x * p y) * (p y * p z) := by ring
    have hxz' : p x * p z ≤ 0 := by
      have h1 : 0 ≤ p x * p y := le_of_not_gt hc
      have h2 : (p x * p y) * (p y * p z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h'.le
      have hy2 : 0 < p y ^ 2 := by positivity
      nlinarith
    refine ⟨hxz, by simp only [x]; ring, hroot x z hxz.le hxz', fun hx0 => ?_⟩
    rcases hxz'.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rcases mul_eq_zero.1 heq with h0 | h0
      · exact hx0 h0
      · rw [h0, mul_zero] at h'; exact lt_irrefl _ h'

/-! ### §8.4.2 Sturm sequence methods -/

/-- **Theorem 8.4.1 (Sturm sequence property), interlacing.** If `β_i ≠ 0` for all `i`, the
eigenvalues of `T_{r-1}` strictly separate those of `T_r`:
`λ_r(T_r) < λ_{r-1}(T_{r-1}) < λ_{r-1}(T_r) < ⋯ < λ_1(T_{r-1}) < λ_1(T_r)` (0-based: here `T_r` is
`symmTridiagonalOf α β r` and `T_{r+1}` the next one). -/
theorem theorem_8_4_1 (α β : ℕ → ℝ) (r : ℕ) (hβ : ∀ j, j + 1 < r + 1 → β j ≠ 0) (k : Fin r) :
    symmEigenvalue (isSymm_symmTridiagonalOf α β (r + 1)) k.succ <
        symmEigenvalue (isSymm_symmTridiagonalOf α β r) k ∧
      symmEigenvalue (isSymm_symmTridiagonalOf α β r) k <
        symmEigenvalue (isSymm_symmTridiagonalOf α β (r + 1)) k.castSucc :=
  ⟨Sturm.eigenvalues_succ_lt α β r hβ k, Sturm.eigenvalues_lt_castSucc α β r hβ k⟩

/-- **Theorem 8.4.1, the count**, corrected: if `β_i ≠ 0` for all `i`, the number `a(λ)` of sign
changes in `p_0(λ), …, p_n(λ)` (with the book's sign at a zero) is the number of eigenvalues of
`T` that are `≤ λ`; hence, when `λ` is not an eigenvalue, the number that are `< λ` (the printed
statement, which holds exactly off the spectrum). -/
theorem theorem_8_4_1_b (α β : ℕ → ℝ) (n : ℕ) (hβ : ∀ j, j + 1 < n → β j ≠ 0) (μ : ℝ) :
    Sturm.signChanges α β n μ = (Finset.univ.filter fun k =>
        symmEigenvalue (isSymm_symmTridiagonalOf α β n) k ≤ μ).card ∧
      (μ ∉ spectrum ℝ (symmTridiagonalOf α β n) → Sturm.signChanges α β n μ =
        (Finset.univ.filter fun k =>
          symmEigenvalue (isSymm_symmTridiagonalOf α β n) k < μ).card) := by
  have h := Sturm.signChanges_eq_count α β n hβ μ
  refine ⟨h, fun hμ => ?_⟩
  rw [h, Sturm.count]
  congr 1
  refine Finset.filter_congr fun k _ => ⟨fun hk => lt_of_le_of_ne hk fun he => hμ ?_, le_of_lt⟩
  rw [← he]
  exact symmEigenvalue_mem_spectrum _ k

/-- **§8.4.2, the Gershgorin bracket**: every eigenvalue of the tridiagonal `T` lies in `[y, z]`,
`y = min_i (α_i - |β_i| - |β_{i-1}|)`, `z = max_i (α_i + |β_i| + |β_{i-1}|)` (`β_0 = β_n = 0`; the
radius is `Sturm.gershgorinRadius`). -/
theorem gershgorin_bracket (α β : ℕ → ℝ) (n : ℕ) :
    spectrum ℝ (symmTridiagonalOf α β n) ⊆
      Set.Icc (⨅ i : Fin n, (α i - Sturm.gershgorinRadius β n i))
        (⨆ i : Fin n, (α i + Sturm.gershgorinRadius β n i)) :=
  Sturm.spectrum_subset_Icc α β n

/-- **(8.4.3), bisection for `λ_k(T)`**, with the test corrected to `a(x) ≥ n - k + 1`: for
unreduced `T` (`β_i ≠ 0`), `1 ≤ k ≤ n` and a bracket `[y, z]` with `a(y) ≤ n - k < a(z)` (which a
Gershgorin bracket `y < min_i(α_i - r_i)`, `z ≥ max_i(α_i + r_i)` satisfies), the iterates of the
loop `x = (y + z)/2; if a(x) ≥ n - k + 1 then z = x else y = x` halve in length and always contain
`λ_k(T)` in `(y, z]`. -/
theorem equation_8_4_3 (α β : ℕ → ℝ) {n k : ℕ} (hβ : ∀ j, j + 1 < n → β j ≠ 0) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    (∀ {y z : ℝ}, y < ⨅ i : Fin n, (α i - Sturm.gershgorinRadius β n i) →
      (⨆ i : Fin n, (α i + Sturm.gershgorinRadius β n i)) ≤ z →
      Sturm.signChanges α β n y ≤ n - k ∧ n - k < Sturm.signChanges α β n z) ∧
    ∀ {yz : ℝ × ℝ}, Sturm.signChanges α β n yz.1 ≤ n - k ∧
        n - k < Sturm.signChanges α β n yz.2 → ∀ r : ℕ,
      (Sturm.bisectionIterate α β n k yz r).2 - (Sturm.bisectionIterate α β n k yz r).1 =
          (yz.2 - yz.1) / 2 ^ r ∧
        symmEigenvalue (isSymm_symmTridiagonalOf α β n) ⟨k - 1, by omega⟩ ∈
          Set.Ioc (Sturm.bisectionIterate α β n k yz r).1 (Sturm.bisectionIterate α β n k yz r).2 :=
  ⟨fun hy hz => by
    rw [Sturm.signChanges_eq_count α β n hβ, Sturm.signChanges_eq_count α β n hβ,
      Sturm.count_eq_zero_of_lt α β hy, Sturm.count_eq_of_le α β hz]
    omega,
  fun h r => ⟨Sturm.bisectionIterate_length α β n k _ r,
    Sturm.eigenvalues_mem_bisectionIterate α β hβ hk hkn h r⟩⟩

/-- **§8.4.2, last paragraph**: for symmetric `A` and an `L D Lᵀ` factorization
`A - μ I = L D Lᵀ` (`L` unit lower triangular), the number of negative `d_i` is the number of
eigenvalues `λ_i(A) < μ`. -/
theorem ldlt_inertia_count {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {μ : ℝ}
    {L : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ} (h : IsLDM (A - μ • 1) L (diagonal d) L) :
    (Finset.univ.filter fun k => symmEigenvalue hA k < μ).card =
      (Finset.univ.filter fun i => d i < 0).card := by
  rw [card_filter_symmEigenvalue hA (· < μ)]
  exact (isHermitian_iff_isSymm.2 hA).card_eigenvalues_lt_eq_card_neg_of_isLDM h

/-! ### §8.4.3 Eigensystems of diagonal plus rank-1 matrices -/

section RankOne

variable {n : ℕ}

/-- **(8.4.4)**: `(D + ρ z zᵀ) v = λ v` iff `(D - λ I) v + ρ (zᵀ v) z = 0`. -/
theorem equation_8_4_4 (d : Fin n → ℝ) (ρ : ℝ) (z v : Fin n → ℝ) (t : ℝ) :
    (diagonal d + ρ • vecMulVec z z) *ᵥ v = t • v ↔
      (diagonal d - t • 1) *ᵥ v + (ρ * (z ⬝ᵥ v)) • z = 0 := by
  have h := Matrix.diagonal_add_rankOne_mulVec_eq_iff (𝕜 := ℝ) (d := d) (ρ := ρ) (z := z)
    (v := v) (t := t)
  simp only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] at h
  rw [h, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_mulVec, smul_mulVec,
    one_mulVec, Pi.sub_apply, mulVec_diagonal, Pi.zero_apply]
  constructor <;> intro h' <;> linarith

/-- **Lemma 8.4.2.** For `D = diag(d)` with distinct `d_i`, `ρ ≠ 0`, `z` with no zero component,
and `(D + ρ z zᵀ) v = λ v` with `v ≠ 0`: `zᵀ v ≠ 0` and `D - λ I` is nonsingular. -/
theorem lemma_8_4_2 {d : Fin n → ℝ} (hd : Function.Injective d) {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Fin n → ℝ} (hz : ∀ i, z i ≠ 0) {v : Fin n → ℝ} (hv : v ≠ 0) {t : ℝ}
    (h : (diagonal d + ρ • vecMulVec z z) *ᵥ v = t • v) :
    z ⬝ᵥ v ≠ 0 ∧ IsUnit (diagonal d - t • 1) := by
  have h' := isUnit_diagonal_sub_of_hasEigenvector_add_rankOne (𝕜 := ℝ) hd hρ hz hv
    (by simpa using h)
  refine ⟨by simpa using h'.1, ?_⟩
  rw [smul_one_eq_diagonal, diagonal_sub, isUnit_iff_isUnit_det, det_diagonal,
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => sub_ne_zero.2 (by simpa using h'.2 i)

/-- **§8.4.3, the secular function** `f(λ) = 1 + ρ zᵀ(D - λI)⁻¹z = 1 + ρ ∑ z_i² / (d_i - λ)`. -/
noncomputable def secularFunction (d : Fin n → ℝ) (ρ : ℝ) (z : Fin n → ℝ) (t : ℝ) : ℝ :=
  Matrix.secularFunction d ρ z t

/-- The secular function is `1 + ρ ∑ z_i² / (d_i - λ)`; off `{d_i}` it is
`1 + ρ zᵀ (D - λ I)⁻¹ z`, with derivative `f'(λ) = ρ ∑ z_i² / (d_i - λ)²`. -/
theorem secularFunction_eq (d : Fin n → ℝ) (ρ : ℝ) (z : Fin n → ℝ) (t : ℝ) :
    secularFunction d ρ z t = 1 + ρ * ∑ i, z i ^ 2 / (d i - t) ∧
      (t ∉ Set.range d → secularFunction d ρ z t = 1 + ρ * (z ⬝ᵥ (diagonal d - t • 1)⁻¹ *ᵥ z) ∧
        HasDerivAt (secularFunction d ρ z) (ρ * ∑ i, z i ^ 2 / (d i - t) ^ 2) t) := by
  refine ⟨by simp [secularFunction, Matrix.secularFunction, Real.norm_eq_abs, sq_abs],
    fun ht => ⟨?_, ?_⟩⟩
  · rw [secularFunction, Matrix.secularFunction_eq_inner_resolvent d ρ z ht]
    have : diagonal d - t • 1 = diagonal fun i => d i - t := by
      rw [smul_one_eq_diagonal, diagonal_sub]
    rw [this]
    simp
  · have := Matrix.hasDerivAt_secularFunction d ρ z ht
    change HasDerivAt (Matrix.secularFunction d ρ z) _ t
    simpa [Real.norm_eq_abs, sq_abs] using this

/-- **Theorem 8.4.3 (a), (c).** For distinct `d_i`, `ρ ≠ 0`, `z` with no zero component and an
orthogonal `V` with `Vᵀ (D + ρ z zᵀ) V = diag(λ)`: (a) the `λ_i` are the zeros of `f` — each
`λ_i ∉ {d_j}` with `f(λ_i) = 0`, and every zero of `f` off `{d_j}` is some `λ_i`; (c) each
`V(:, i)` is a multiple of `(D - λ_i I)⁻¹ z`. -/
theorem theorem_8_4_3 {d : Fin n → ℝ} (hd : Function.Injective d) {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Fin n → ℝ} (hz : ∀ i, z i ≠ 0) {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {l : Fin n → ℝ}
    (hVl : Vᵀ * (diagonal d + ρ • vecMulVec z z) * V = diagonal l) :
    (∀ i, l i ∉ Set.range d ∧ secularFunction d ρ z (l i) = 0) ∧
      (∀ t, t ∉ Set.range d → secularFunction d ρ z t = 0 → ∃ i, l i = t) ∧
      ∀ i, ∃ c : ℝ, V.col i = c • fun j => z j / (d j - l i) := by
  set M := diagonal d + ρ • vecMulVec z z
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hV
  have hVV' : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hV
  have hMV : M * V = V * diagonal l := by
    rw [← hVl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hcol : ∀ i, M *ᵥ V.col i = l i • V.col i := fun i => by
    rw [← col_mul_eq_mulVec_col, hMV]
    ext j
    simp [col_apply, mul_diagonal, mul_comm]
  have hcol0 : ∀ i, V.col i ≠ 0 := fun i h0 => by
    have := congrFun (congrFun hVV' i) i
    simp only [Matrix.mul_apply, transpose_apply, one_apply_eq] at this
    have h' : ∀ j, V j i = 0 := fun j => congrFun h0 j
    simp [h'] at this
  have hiff := fun t => hasEigenvalue_iff_secularFunction_eq_zero (𝕜 := ℝ) hd hρ hz t
  simp only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] at hiff
  refine ⟨fun i => ?_, fun t ht hf => ?_, fun i => ?_⟩
  · refine (hiff (l i)).1
      (Module.End.hasEigenvalue_of_hasEigenvector (x := V.col i) ⟨?_, hcol0 i⟩)
    rw [Module.End.mem_genEigenspace_one, toLin'_apply]
    exact hcol i
  · obtain ⟨v, hv⟩ := ((hiff t).2 ⟨ht, hf⟩).exists_hasEigenvector
    have hMv : M *ᵥ v = t • v := by
      have := hv.apply_eq_smul
      rwa [toLin'_apply] at this
    set w := Vᵀ *ᵥ v
    have hw : diagonal l *ᵥ w = t • w := by
      rw [← hVl]
      simp only [w, mulVec_mulVec, Matrix.mul_assoc, hVV, Matrix.mul_one]
      rw [← mulVec_mulVec, hMv, mulVec_smul]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra! h0
      have : v = V *ᵥ w := by rw [mulVec_mulVec, hVV, one_mulVec]
      exact hv.2 (by rw [this, show w = 0 from funext h0, mulVec_zero])
    refine ⟨i, ?_⟩
    have := congrFun hw i
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  · obtain ⟨c, -, hc⟩ := hasEigenvector_diagonal_add_rankOne_resolvent (𝕜 := ℝ) hd hρ hz
      (hcol0 i) (by simpa using hcol i)
    exact ⟨c, by simpa using hc⟩

/-- **Theorem 8.4.3 (b), strict interlacing.** For strictly decreasing `d`, `ρ ≠ 0` and `z` with
no zero component, the eigenvalues `λ_1 ≥ ⋯ ≥ λ_n` of `D + ρ z zᵀ` satisfy
`λ_1 > d_1 > λ_2 > ⋯ > λ_n > d_n` if `ρ > 0` and `d_1 > λ_1 > d_2 > ⋯ > d_n > λ_n` if `ρ < 0`. -/
theorem theorem_8_4_3_b {d : Fin n → ℝ} (hd : StrictAnti d) {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Fin n → ℝ} (hz : ∀ i, z i ≠ 0) (hM : (diagonal d + ρ • vecMulVec z z).IsSymm) :
    (0 < ρ → (∀ i, d i < symmEigenvalue hM i) ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 → symmEigenvalue hM j < d i) ∧
      (ρ < 0 → (∀ i, symmEigenvalue hM i < d i) ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 → d j < symmEigenvalue hM i) := by
  have heq : ((diagonal fun i => (RCLike.ofReal (d i) : ℝ)) + (RCLike.ofReal ρ : ℝ) •
      vecMulVec z (star z)) = diagonal d + ρ • vecMulVec z z := by simp
  have hM' : ((diagonal fun i => (RCLike.ofReal (d i) : ℝ)) + (RCLike.ofReal ρ : ℝ) •
      vecMulVec z (star z)).IsHermitian := by
    rw [heq]; exact isHermitian_iff_isSymm.2 hM
  have h := eigenvalues₀_diagonal_add_rankOne_strictInterlace (𝕜 := ℝ) hd hρ hz hM'
  rw [IsHermitian.sortedEigenvalues_congr heq hM' (isHermitian_iff_isSymm.2 hM)] at h
  exact h

/-- **Theorem 8.4.4 (deflation).** For `D = diag(d)` and `z` there is an orthogonal `V₁` with
`V₁ᵀ D V₁ = diag(μ)` and `w = V₁ᵀ z` such that `w_i ≠ 0` exactly for `i < r`, with
`μ_1 > ⋯ > μ_r` and `μ_{r+1} ≥ ⋯ ≥ μ_n` (0-based; the book's `μ_r ≥ μ_{r+1}` across the boundary
is dropped: it is false in general, see the module doc). -/
theorem theorem_8_4_4 (d z : Fin n → ℝ) :
    ∃ V₁ ∈ orthogonalGroup (Fin n) ℝ, ∃ μ : Fin n → ℝ, ∃ r ≤ n,
      V₁ᵀ * diagonal d * V₁ = diagonal μ ∧
      (∀ i j : Fin n, i < j → (j : ℕ) < r → μ j < μ i) ∧
      (∀ i j : Fin n, r ≤ (i : ℕ) → i ≤ j → μ j ≤ μ i) ∧
      ∀ i, (V₁ᵀ *ᵥ z) i ≠ 0 ↔ (i : ℕ) < r :=
  exists_orthogonal_deflation d z

end RankOne

/-! ### §8.4.4 A divide-and-conquer framework -/

/-- **(8.4.5)–(8.4.6), tearing.** For the tridiagonal `T` of (8.4.1) of order `2m` (here
`(m + 1) + (m + 1)`), `θ` (the book takes `θ ∈ {-1, 1}`; the identity needs no condition on it)
and `ρ` with `ρ θ = β_m` (0-based `β m`), and
`v = (e_m, θ e_1)`: `T = diag(T₁, T₂) + ρ v vᵀ`, where `T₁`, `T₂` are the tridiagonal halves with
`α̃_m = α_m - ρ` and `α̃_{m+1} = α_{m+1} - ρ θ²`. -/
theorem equation_8_4_6 (α β : ℕ → ℝ) (m : ℕ) {θ ρ : ℝ} (hρ : ρ * θ = β m) :
    (symmTridiagonalOf α β (m + 1 + (m + 1))).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (symmTridiagonalOf (Function.update α m (α m - ρ)) β (m + 1)) 0 0
        (symmTridiagonalOf (Function.update (fun i => α (m + 1 + i)) 0 (α (m + 1) - ρ * θ ^ 2))
          (fun i => β (m + 1 + i)) (m + 1)) +
      ρ • vecMulVec (Sum.elim (Pi.single (Fin.last m) 1) (θ • Pi.single 0 1))
        (Sum.elim (Pi.single (Fin.last m) 1) (θ • Pi.single 0 1)) := by
  ext (i | i) (j | j) <;>
    simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.add_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.smul_apply, vecMulVec_apply,
      Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, symmTridiagonalOf_apply,
      Fin.val_castAdd, Fin.val_natAdd, Pi.single_apply, Fin.ext_iff, Fin.val_last, Fin.val_zero,
      Function.update_apply] <;>
    split_ifs <;> (try ring_nf) <;>
    first
    | omega
    | rfl
    | (congr 1 <;> omega)
    | (rw [hρ]; congr 1)

/-- **§8.4.4, the merge.** For `Q₁ᵀ T₁ Q₁ = diag(d₁)` and `Q₂ᵀ T₂ Q₂ = diag(d₂)` (`Q₁`, `Q₂`
orthogonal) and any `v`, `U = diag(Q₁, Q₂)` is orthogonal and
`Uᵀ (diag(T₁, T₂) + ρ v vᵀ) U = diag(d₁, d₂) + ρ z zᵀ` with `z = Uᵀ v`; for the tearing vector
`v = (e_m, θ e_1)`, `z = (Q₁ᵀ e_m, θ Q₂ᵀ e_1)`. Hence an orthogonal `V` with
`Vᵀ (D + ρ z zᵀ) V = diag(λ)` gives the Schur decomposition (8.4.5), with `Q = U V`. -/
theorem divideConquer_merge {m : ℕ} {T₁ Q₁ T₂ Q₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hQ₁ : Q₁ ∈ orthogonalGroup _ ℝ) (hQ₂ : Q₂ ∈ orthogonalGroup _ ℝ) {d₁ d₂ : Fin (m + 1) → ℝ}
    (h₁ : Q₁ᵀ * T₁ * Q₁ = diagonal d₁) (h₂ : Q₂ᵀ * T₂ * Q₂ = diagonal d₂) (ρ θ : ℝ) :
    let v := Sum.elim (Pi.single (Fin.last m) 1) (θ • Pi.single 0 1)
    let U := fromBlocks Q₁ 0 0 Q₂
    U ∈ orthogonalGroup _ ℝ ∧
      Uᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * U =
        diagonal (Sum.elim d₁ d₂) + ρ • vecMulVec (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) ∧
      Uᵀ *ᵥ v = Sum.elim (fun j => Q₁ (Fin.last m) j) (fun j => θ * Q₂ 0 j) ∧
      ∀ V ∈ orthogonalGroup _ ℝ, ∀ l : Fin (m + 1) ⊕ Fin (m + 1) → ℝ,
        Vᵀ * (diagonal (Sum.elim d₁ d₂) + ρ • vecMulVec (Uᵀ *ᵥ v) (Uᵀ *ᵥ v)) * V = diagonal l →
          U * V ∈ orthogonalGroup _ ℝ ∧
            (U * V)ᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * (U * V) = diagonal l := by
  intro v U
  obtain ⟨hU, hconj⟩ := conj_fromBlocks_add_rankOne_eq hQ₁ hQ₂ h₁ h₂ ρ v
  refine ⟨hU, hconj, ?_, fun V hV l hVl => ⟨Submonoid.mul_mem _ hU hV, ?_⟩⟩
  · ext (j | j)
    · simp [U, v, mulVec, dotProduct, Pi.single_apply]
    · simp [U, v, mulVec, dotProduct, Pi.single_apply]
      ring
  · have e : (U * V)ᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * (U * V) =
        Vᵀ * (Uᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * U) * V := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e]
    exact (congrArg (fun X => Vᵀ * X * V) hconj).trans hVl

/-! ### §8.4.6 An inverse tridiagonal eigenvalue problem -/

/-- **(8.4.10)–(8.4.11).** For symmetric `T = Qᵀ Λ Q` (`Q` orthogonal, `Λ = diag(λ)`),
`d = Q(:, 1)` and `λ` not an eigenvalue: `e₁ᵀ (T - λI)⁻¹ e₁ = ∑ d_i² / (λ_i - λ)`, and by Cramer
`e₁ᵀ (T - λI)⁻¹ e₁ = det(T(2:n, 2:n) - λI) / det(T - λI)` — so the zeros of the sum are the
eigenvalues of `T(2:n, 2:n)` that are not eigenvalues of `T`. -/
theorem equation_8_4_10 {N : ℕ} {T Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup _ ℝ) {l : Fin (N + 1) → ℝ} (hT : T = Qᵀ * diagonal l * Q) {c : ℝ}
    (hc : ∀ i, l i ≠ c) :
    (T - c • 1)⁻¹ 0 0 = ∑ i, Q i 0 ^ 2 / (l i - c) ∧
      (T - c • 1)⁻¹ 0 0 = (T.submatrix Fin.succ Fin.succ - c • 1).det / (T - c • 1).det := by
  refine ⟨?_, inv_sub_apply_zero_zero_eq_det_div T c⟩
  have hQt : Qᵀ ∈ unitaryGroup (Fin (N + 1)) ℝ := by
    have := Unitary.star_mem hQ
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hQA : star Qᵀ * T * Qᵀ = diagonal l := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_transpose, hT]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [inv_sub_smul_one_apply_eq_sum hQt hQA hc 0 0]
  simp [sq]

/-- `det(M - c I) = ∏ (μ_j - c)` when the characteristic polynomial of `M` is `∏ (X - μ_j)`. -/
private theorem det_sub_smul_one_of_charpoly {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    {μ : Fin N → ℝ} (h : M.charpoly = ∏ j, (X - C (μ j))) (c : ℝ) :
    (M - c • 1).det = ∏ j, (μ j - c) := by
  have e := congrArg (Polynomial.eval c) h
  rw [eval_charpoly, eval_prod] at e
  simp only [eval_sub, eval_X, eval_C] at e
  have hneg : M - c • 1 = -(scalar (Fin N) c - M) := by
    rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
  rw [hneg, det_neg, e, Fintype.card_fin,
    show ∏ j, (μ j - c) = ∏ j, -(c - μ j) from by simp only [neg_sub], Finset.prod_neg,
    Finset.card_univ, Fintype.card_fin]

/-- **(8.4.12)**, with the denominator's range corrected to `j ≠ k`, `j = 1:n`. If (8.4.7)
`λ_1 > λ̃_1 > λ_2 > ⋯ > λ̃_{n-1} > λ_n` holds and `T = Qᵀ Λ Q` (`Q` orthogonal) has
`T(2:n, 2:n)` with eigenvalues `λ̃`, then `d = Q(:, 1)` satisfies
`d_k² = ∏_{j=1}^{n-1} (λ̃_j - λ_k) / ∏_{j ≠ k} (λ_j - λ_k)`, and these quotients are positive and
sum to `1`. -/
theorem equation_8_4_12 {N : ℕ} {T Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup _ ℝ) {l : Fin (N + 1) → ℝ} (hT : T = Qᵀ * diagonal l * Q)
    {μ : Fin N → ℝ} (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j)
    (hsub : (T.submatrix Fin.succ Fin.succ).charpoly = ∏ j, (X - C (μ j))) :
    (∀ k, Q k 0 ^ 2 = (∏ j, (μ j - l k)) / ∏ j ∈ Finset.univ.erase k, (l j - l k)) ∧
      (∀ k, 0 < (∏ j, (μ j - l k)) / ∏ j ∈ Finset.univ.erase k, (l j - l k)) ∧
      ∑ k, (∏ j, (μ j - l k)) / ∏ j ∈ Finset.univ.erase k, (l j - l k) = 1 := by
  obtain ⟨hpos, hsum⟩ := prod_sub_div_prod_sub_pos_of_strictInterlace h₁ h₂
  refine ⟨fun k => ?_, hpos, hsum⟩
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.mpr fun j => (h₂ j).trans (h₁ j)
  have hQt : Qᵀ ∈ unitaryGroup (Fin (N + 1)) ℝ := by
    have := Unitary.star_mem hQ
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hTs : T.IsHermitian := by
    rw [hT, IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp [transpose_mul, Matrix.mul_assoc]
  have hQA : star Qᵀ * T * Qᵀ = diagonal l := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_transpose, hT]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have h := hTs.norm_sq_eigenvector_mul_prod_eq hQt hQA k
  -- the eigenvalues of the trailing block are the `μ j`
  have hprod : ∏ j, ((hTs.submatrix Fin.succ).eigenvalues j - l k) = ∏ j, (μ j - l k) := by
    have e1 := (hTs.submatrix Fin.succ).det_sub_smul_one_eq_prod (l k)
    rw [det_sub_smul_one_of_charpoly hsub] at e1
    simpa using e1.symm
  have hne : ∏ j ∈ Finset.univ.erase k, (l j - l k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j hj =>
      sub_ne_zero.2 (hl.injective.ne (Finset.ne_of_mem_erase hj))
  rw [eq_div_iff hne, ← hprod, ← h]
  simp [Real.norm_eq_abs, sq_abs]

/-- **§8.4.6, the inverse problem** (Golub 1973): for strictly interlacing
`λ_1 > λ̃_1 > λ_2 > ⋯ > λ̃_{n-1} > λ_n` there is a symmetric tridiagonal `T` with
`λ(T) = {λ_1, …, λ_n}` (8.4.8) and `λ(T(2:n, 2:n)) = {λ̃_1, …, λ̃_{n-1}}` (8.4.9), with
multiplicity. -/
theorem inverseTridiagonal_exists {N : ℕ} {l : Fin (N + 1) → ℝ} {μ : Fin N → ℝ}
    (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    ∃ T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, T.IsSymm ∧ T.IsTridiagonal ∧
      T.charpoly = ∏ i, (X - C (l i)) ∧
        (T.submatrix Fin.succ Fin.succ).charpoly = ∏ j, (X - C (μ j)) :=
  exists_isTridiagonal_eigenvalues_eq_of_strictInterlace h₁ h₂

end GolubVanLoan.Chapter08
