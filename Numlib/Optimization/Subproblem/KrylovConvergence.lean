import Numlib.Eigen.KrylovEigen
import Numlib.LinearAlgebra.Matrix.InverseDecay
import Numlib.Optimization.Subproblem.Krylov

/-!
# Convergence of the Krylov subproblem solutions

Let `H` be a symmetric operator on a finite-dimensional real inner product space, `g ≠ 0`, and let
`sₖ` solve the regularization or trust-region subproblem restricted to the Krylov subspace
`𝒦_k = 𝒦_k(H, g)` (`Numlib.Optimization.Subproblem.Krylov`), with multiplier `λₖ`. This file proves
the convergence bounds of [cartis2022evaluation] §10.2.4 and §10.3 (Gould–Simoncini): the gradient
(resp. residual) `g + H sₖ + λₖ sₖ` decays like `q(κₖ)^{k-1}`, where
`κₖ = (θₖ + λₖ)/(θ₁ + λₖ)` is the condition number of the positive definite `T_k + λₖ` and
`q(κ) = (√κ - 1)/(√κ + 1)`, and the resulting iteration counts for the stopping tests.

The proof follows the book: in Lanczos coordinates the residual is `β_{k-1} |ȳ_{k-1}|` with
`ȳ = -‖g‖ (T_k + λₖ)⁻¹ e₀` ((B.10.1)–(B.10.2)); the `(k-1, 0)` entry of the inverse of a positive
definite tridiagonal matrix decays geometrically (Lemma B.10.1,
`Matrix.abs_inv_apply_le_of_hasBandwidth_of_mem_Icc`); `‖g‖ ≤ (θₖ + λₖ) ‖sₖ‖` ((B.10.3)); and
`β_{k-1} ≤ ‖H‖` ((B.10.4)).

## Main definitions

* `Subproblem.krylovCond hH g k μ`: the condition number `κₖ(μ) = (θₖ + μ)/(θ₁ + μ)` of the
  compression of `H + μ` to `𝒦_k`, `θ₁ ≤ θₖ` the extreme Ritz values ((10.2.8)).
* `Subproblem.convFactor κ = (√κ - 1)/(√κ + 1)`.

`Subproblem.krylovCond_eq_ritzValues` identifies `θ₁`, `θₖ` with the extreme eigenvalues of the
Lanczos tridiagonal `T_k` (`Lanczos.ritzValues`).

## Main statements

* `Subproblem.krylov_residual_le`: the residual bound `2 ‖H‖ κₖ ‖sₖ‖ q(κₖ)^{k-1}` for any point of
  `𝒦_k` satisfying the restricted first-order condition with a shift `μ > -θ₁`.
* `Subproblem.krylov_gradient_bound_regularization`: Theorem 10.2.2.
* `Subproblem.krylov_residual_bound_trustRegion`: Theorem 10.3.2.
* `Subproblem.krylov_iteration_bound_regularization`: Corollary 10.2.3.
* `Subproblem.krylov_iteration_bound_trustRegion`: Corollary 10.3.3.
* Supporting facts: `Subproblem.posDef_tridiag_add` and `Subproblem.eigenvalues_tridiag_add_mem`
  (the shifted Lanczos tridiagonal is positive definite with spectrum in `[θ₁ + μ, θₖ + μ]`),
  `Subproblem.beta_le_opNorm`, `Subproblem.rightmost_compressionL_le` (`θₖ ≤ λmax`),
  `Subproblem.residual_eq_zero_of_grade_le` (exactness at the grade).

## Implementation notes

`‖H‖` is the operator norm of `E`. For matrix data with a scaling `M`, `E` carries the
`M`-inner product (`Numlib.Optimization.Subproblem.Matrix`), and `‖H‖` is the largest `|λ|` of the
pencil `(H, M)`, i.e. `‖M^{-1/2} H M^{-1/2}‖₂`. The book's (B.10.4) claims
`‖M^{-T/2} H M^{-1/2}‖ = ‖M⁻¹ H‖` "by similarity", which is false in general (similarity preserves
eigenvalues, not Euclidean norms); only `≤` holds, which is all the bounds need, so the results are
stated with the (smaller) operator norm.

Corrections to the iteration counts: the book's `⌈log A / log((√κ* + 1)/(√κ* - 1))⌉ + 1` may be
nonpositive or undefined. Here the ceiling is `⌈·⌉₊` (when `log A < 0` the bound is `k ≤ 1`), and
the case `κ* = 1` (where `log((√κ* + 1)/(√κ* - 1))` is undefined) is stated separately: then
`q* = 0` and the test holds at some `k ≤ min 2 grade`. The constant `κ*` may be any upper bound
of the `κₖ`, `1 ≤ k ≤ grade`; the book's choice is their maximum (10.2.10).
-/

open Set Matrix Krylov
open scoped RealInnerProductSpace

namespace Subproblem

/-! ### The convergence factor -/

/-- The convergence factor `q(κ) = (√κ - 1)/(√κ + 1)` of a condition number `κ`
([cartis2022evaluation] (10.2.9)). -/
noncomputable def convFactor (κ : ℝ) : ℝ := (√κ - 1) / (√κ + 1)

theorem convFactor_def (κ : ℝ) : convFactor κ = (√κ - 1) / (√κ + 1) := rfl

/-- `q(κ) ≥ 0` for `κ ≥ 1`. -/
theorem convFactor_nonneg {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ convFactor κ := by
  have : 1 ≤ √κ := Real.one_le_sqrt.2 hκ
  unfold convFactor; positivity

/-- `q(κ) < 1`. -/
theorem convFactor_lt_one (κ : ℝ) : convFactor κ < 1 := by
  have : 0 ≤ √κ := Real.sqrt_nonneg κ
  rw [convFactor, div_lt_one (by positivity)]; linarith

/-- `q(κ) > 0` for `κ > 1`. -/
theorem convFactor_pos {κ : ℝ} (hκ : 1 < κ) : 0 < convFactor κ := by
  have : 1 < √κ := Real.lt_sqrt_of_sq_lt (by simpa using hκ)
  unfold convFactor
  exact div_pos (by linarith) (by linarith)

/-- `q(1) = 0`: a perfectly conditioned system converges in one step. -/
@[simp]
theorem convFactor_one : convFactor 1 = 0 := by simp [convFactor]

/-- For `κ ≥ 1`, `q(κ) = 0` exactly when `κ = 1`. -/
theorem convFactor_eq_zero_iff {κ : ℝ} (hκ : 1 ≤ κ) : convFactor κ = 0 ↔ κ = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ convFactor_one⟩
  rcases hκ.eq_or_lt with h1 | h1
  · exact h1.symm
  · exact absurd h (convFactor_pos h1).ne'

/-- The convergence factor increases with the condition number. -/
theorem convFactor_le_convFactor {κ κ' : ℝ} (h : κ ≤ κ') :
    convFactor κ ≤ convFactor κ' := by
  have h1 : 0 ≤ √κ := Real.sqrt_nonneg κ
  have h2 : √κ ≤ √κ' := Real.sqrt_le_sqrt h
  rw [convFactor, convFactor, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Iteration count for a geometric bound.** If `0 < q < 1` and `A ∈ ℝ`, then
`A q^N ≤ 1` for `N = ⌈log A / log (1/q)⌉₊`. -/
theorem mul_pow_le_one_of_ceil {A q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    A * q ^ ⌈Real.log A / Real.log (1 / q)⌉₊ ≤ 1 := by
  set N := ⌈Real.log A / Real.log (1 / q)⌉₊
  rcases le_or_gt A 0 with hA | hA
  · exact (mul_nonpos_of_nonpos_of_nonneg hA (by positivity)).trans zero_le_one
  have hlq : 0 < Real.log (1 / q) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hq0 |>.2 hq1)
  have hN : Real.log A ≤ N * Real.log (1 / q) := by
    rw [← div_le_iff₀ hlq]; exact Nat.le_ceil _
  have hqN : 0 < q ^ N := pow_pos hq0 N
  rw [← Real.log_pow, _root_.one_div_pow] at hN
  have := (Real.log_le_log_iff hA (by positivity)).1 hN
  rw [le_div_iff₀ hqN] at this
  linarith

/-- **From a geometric test to an iteration count.** Let `G ≥ 1`, `0 ≤ q < 1`, and let `P` hold at
every `k ∈ [1, G]` with `A q^{k-1} ≤ 1`, and at `k = G`. Then `P k` holds at some
`k ∈ [1, min (⌈log A / log (1/q)⌉₊ + 1) G]` when `q > 0`, and at some `k ∈ [1, min 2 G]` when
`q = 0`. -/
theorem exists_le_min_of_geometric {P : ℕ → Prop} {G : ℕ} (hG : 1 ≤ G) {A q : ℝ}
    (hP : ∀ k, 1 ≤ k → k ≤ G → A * q ^ (k - 1) ≤ 1 → P k) (hPG : P G) :
    (0 < q → q < 1 →
      ∃ k, 1 ≤ k ∧ k ≤ min (⌈Real.log A / Real.log (1 / q)⌉₊ + 1) G ∧ P k) ∧
    (q = 0 → ∃ k, 1 ≤ k ∧ k ≤ min 2 G ∧ P k) := by
  constructor
  · intro hq0 hq1
    set N := ⌈Real.log A / Real.log (1 / q)⌉₊
    rcases le_total G (N + 1) with hle | hle
    · exact ⟨G, hG, le_min hle le_rfl, hPG⟩
    · refine ⟨N + 1, by omega, le_min le_rfl hle, hP _ (by omega) hle ?_⟩
      rw [Nat.add_sub_cancel]
      exact mul_pow_le_one_of_ceil hq0 hq1
  · rintro rfl
    rcases le_total G 2 with hle | hle
    · exact ⟨G, hG, le_min hle le_rfl, hPG⟩
    · exact ⟨2, by omega, le_min le_rfl hle, hP 2 (by omega) hle (by simp)⟩

/-! ### The shifted Lanczos tridiagonal -/

section Tridiagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E} {g : E}

/-- `𝒦ₕ[k]` is the Krylov subspace `𝒦_k(H, g)` of the operator `H` and the gradient `g`. -/
local notation "𝒦ₕ[" k "]" => 𝒦[(H : E →ₗ[ℝ] E), g] k

/-- The Lanczos vectors `q j = Arnoldi.vec H g j`. -/
local notation "𝐪" => Arnoldi.vec (H : E →ₗ[ℝ] E) g

/-- The Lanczos tridiagonal matrices `T_m = Lanczos.tridiag H g m`. -/
local notation "𝐓" => Lanczos.tridiag (H : E →ₗ[ℝ] E) g

/-- The Lanczos off-diagonal coefficients `β j = Lanczos.beta H g j`. -/
local notation "𝛃" => Lanczos.beta (H : E →ₗ[ℝ] E) g

/-- The **condition number** `κₖ(μ) = (θₖ + μ)/(θ₁ + μ)` of the shifted compression of `H` to the
Krylov subspace `𝒦_k(H, g)`, `θ₁ ≤ θₖ` its extreme eigenvalues (the extreme Ritz values). At the
multiplier `μ = λₖ` and for `k ≤ grade(H, g)` this is the book's `κₖ = κ(T_k + λₖ I)` (10.2.8),
by `krylovCond_eq_ritzValues`. -/
noncomputable def krylovCond (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (g : E) (k : ℕ) (μ : ℝ) : ℝ :=
  (rightmost (isSymmetric_compressionL (K := 𝒦[(H : E →ₗ[ℝ] E), g] k) hH) + μ) /
    (leftmost (isSymmetric_compressionL (K := 𝒦[(H : E →ₗ[ℝ] E), g] k) hH) + μ)

omit [FiniteDimensional ℝ E] in
/-- Changing the dimension witness only reindexes the eigenvalues. -/
private theorem range_eigenvalues_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {T : F →ₗ[ℝ] F} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ F = n) : range (hT.eigenvalues hn) = range (hT.eigenvalues rfl) := by
  subst hn; rfl

/-- **The extreme Ritz values are the extreme eigenvalues of the Lanczos tridiagonal**: for
`k ≤ grade(H, g)`, the least and greatest eigenvalues `θ₁`, `θₖ` of the compression of `H` to
`𝒦_k` are the least and greatest eigenvalues of `T_k = Lanczos.tridiag H g k`
(`Lanczos.ritzValues`, the sorted eigenvalues of `T_k`). So `krylovCond hH g k λₖ` is the book's
`κ(T_k + λₖ I) = (θ_{k,k} + λₖ)/(θ_{1,k} + λₖ)` (10.2.8). -/
theorem leftmost_rightmost_compressionL_eq_ritzValues (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ}
    (hk : k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) :
    leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) =
        ⨅ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i ∧
      rightmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) =
        ⨆ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i := by
  have hm : Module.finrank ℝ 𝒦ₕ[k] = k := by
    rw [Krylov.finrank_subspace, min_eq_left hk]
  have hr := Lanczos.ritzValues_eq_eigenvalues_compression g hH hm
  have hrange : range (Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k) =
      range ((isSymmetric_compressionL (K := 𝒦ₕ[k]) hH).eigenvalues rfl) := by
    rw [hr]; exact range_eigenvalues_eq _ hm
  refine ⟨?_, ?_⟩
  · change sInf (range _) = sInf (range _); rw [hrange]
  · change sSup (range _) = sSup (range _); rw [hrange]

/-- `krylovCond` in terms of the Ritz values (the eigenvalues of `T_k`), for `k ≤ grade(H, g)`:
`κₖ(μ) = (λmax(T_k) + μ)/(λmin(T_k) + μ)`, the book's (10.2.8). -/
theorem krylovCond_eq_ritzValues (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ}
    (hk : k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) (μ : ℝ) :
    krylovCond hH g k μ = ((⨆ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i) + μ) /
      ((⨅ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i) + μ) := by
  obtain ⟨h1, h2⟩ := leftmost_rightmost_compressionL_eq_ritzValues hH hk
  rw [krylovCond, h1, h2]

/-- A positive definite shift has condition number at least `1`. -/
theorem one_le_krylovCond (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ} {μ : ℝ}
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < μ) :
    1 ≤ krylovCond hH g k μ := by
  rw [krylovCond, one_le_div (by linarith)]
  linarith [leftmost_le_rightmost (hH := isSymmetric_compressionL (K := 𝒦ₕ[k]) hH)]

/-- The quadratic form of the shifted compression on a subspace is that of `H`. -/
theorem inner_compressionL_add_smul_apply (K : Submodule ℝ E) (μ : ℝ) (v : K) :
    ⟪(compressionL H K + μ • (1 : K →L[ℝ] K)) v, v⟫ = ⟪(v : E), H v + μ • (v : E)⟫ := by
  simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self, inner_add_left,
    inner_smul_left, inner_compressionL_left, inner_add_right, inner_smul_right, conj_trivial]
  rw [Submodule.coe_inner, real_inner_comm (H v)]

/-- **The quadratic form of the shifted Lanczos tridiagonal is enclosed by the extreme Ritz
values**: for `g ≠ 0`, `m + 1 ≤ grade(H, g)`, `T = T_{m+1}` and `θ₁ ≤ θ_{m+1}` the extreme
eigenvalues of the compression of `H` to `𝒦_{m+1}`,
`(θ₁ + μ) ‖x‖² ≤ x ⬝ (T + μ) x ≤ (θ_{m+1} + μ) ‖x‖²`. -/
theorem dotProduct_tridiag_add_mem (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) (μ : ℝ) (x : Fin (m + 1) → ℝ) :
    (leftmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ) * (x ⬝ᵥ x) ≤
        x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ x) ∧
      x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ x) ≤
        (rightmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ) * (x ⬝ᵥ x) := by
  obtain ⟨-, hiso, hquad, -⟩ := krylov_lanczos_coordinates hH hg hm x x μ
  have hv : ∑ i, x i • 𝐪 i ∈ 𝒦ₕ[m + 1] :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ i.2)
  set v : 𝒦ₕ[m + 1] := ⟨_, hv⟩
  have hq : x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ x) =
      ⟪(compressionL H 𝒦ₕ[m + 1] + μ • (1 : 𝒦ₕ[m + 1] →L[ℝ] 𝒦ₕ[m + 1])) v, v⟫ := by
    rw [inner_compressionL_add_smul_apply, ← hquad]
  have hn : x ⬝ᵥ x = ‖v‖ ^ 2 := by
    rw [← hiso, ← real_inner_self_eq_norm_sq]; rfl
  rw [hq, hn]
  constructor
  · rw [add_comm (leftmost _)]; exact add_leftmost_mul_norm_sq_le μ v
  · rw [add_comm (rightmost _)]; exact inner_add_smul_le_add_rightmost μ v

/-- **The shifted Lanczos tridiagonal is positive definite** when the shift is to the right of the
least Ritz value: `T_{m+1} + μ ≻ 0` for `μ > -θ₁`. -/
theorem posDef_tridiag_add (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) {μ : ℝ}
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) < μ) :
    (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.2
      ((Lanczos.tridiag_isSymm _ _ _).add (Matrix.isSymm_one.smul μ))
  · have hxx : 0 < x ⬝ᵥ x := by
      rcases Function.ne_iff.1 hx with ⟨i, hi⟩
      exact lt_of_lt_of_le (mul_self_pos.2 hi)
        (Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
          (Finset.mem_univ i))
    have := (dotProduct_tridiag_add_mem hH hg hm μ x).1
    simp only [star_trivial]
    nlinarith

/-- The eigenvalues of the shifted Lanczos tridiagonal lie between the shifted extreme Ritz
values. -/
theorem eigenvalues_tridiag_add_mem (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) {μ : ℝ}
    (hG : (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)).PosDef)
    (i : Fin (m + 1)) :
    hG.1.eigenvalues i ∈ Icc (leftmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ)
      (rightmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ) := by
  set v := hG.1.eigenvectorBasis i
  have hvv : ⇑v ⬝ᵥ ⇑v = 1 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct v v
    rw [real_inner_self_eq_norm_sq, hG.1.eigenvectorBasis.norm_eq_one, one_pow] at h
    simpa using h.symm
  have he := hG.1.eigenvalues_eq i
  simp only [star_trivial, RCLike.re_to_real] at he
  obtain ⟨h1, h2⟩ := dotProduct_tridiag_add_mem hH hg hm μ ⇑v
  rw [hvv, mul_one] at h1 h2
  exact ⟨he ▸ h1, he ▸ h2⟩

omit [FiniteDimensional ℝ E] in
/-- The shifted Lanczos tridiagonal is tridiagonal. -/
theorem tridiag_add_isTridiagonal (m : ℕ) (μ : ℝ) :
    (𝐓 m + μ • (1 : Matrix (Fin m) (Fin m) ℝ)).IsTridiagonal := by
  intro i j hij
  have hne : i ≠ j := by
    rintro rfl
    rcases hij with ⟨k, h1, h2⟩ | ⟨k, h1, h2⟩ <;> exact absurd (h1.trans h2) (lt_irrefl _)
  rw [Matrix.add_apply, Lanczos.tridiag_isTridiagonal _ _ _ i j hij, Matrix.smul_apply,
    Matrix.one_apply_ne hne, smul_zero, add_zero]

omit [FiniteDimensional ℝ E] in
/-- The next Lanczos coefficient is bounded by the operator norm: `β_m ≤ ‖H‖` (the correct form
of the book's (B.10.4), `γ_{k+1} ≤ ‖M⁻¹ H‖`). -/
theorem beta_le_opNorm (m : ℕ) : 𝛃 m ≤ ‖H‖ := by
  rw [Lanczos.beta, Arnoldi.w_eq_sub_starProjection, ← Submodule.starProjection_orthogonal_val]
  refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
  rw [ContinuousLinearMap.coe_coe]
  refine (H.le_opNorm _).trans ?_
  rcases eq_or_ne (𝐪 m) 0 with h | h
  · rw [h, norm_zero, mul_zero]; exact norm_nonneg _
  · rw [Arnoldi.norm_vec_eq_one_of_ne_zero _ _ h, mul_one]

end Tridiagonal

/-! ### The residual bound -/

section Residual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E} {g : E}

/-- `𝒦ₕ[k]` is the Krylov subspace `𝒦_k(H, g)` of the operator `H` and the gradient `g`. -/
local notation "𝒦ₕ[" k "]" => 𝒦[(H : E →ₗ[ℝ] E), g] k

/-- The Lanczos vectors `q j = Arnoldi.vec H g j`. -/
local notation "𝐪" => Arnoldi.vec (H : E →ₗ[ℝ] E) g

/-- The Lanczos tridiagonal matrices `T_m = Lanczos.tridiag H g m`. -/
local notation "𝐓" => Lanczos.tridiag (H : E →ₗ[ℝ] E) g

/-- The Lanczos off-diagonal coefficients `β j = Lanczos.beta H g j`. -/
local notation "𝛃" => Lanczos.beta (H : E →ₗ[ℝ] E) g

/-- **Exactness at the grade.** Once `𝒦_k` is the whole Krylov space (`grade(H, g) ≤ k`), it is
`H`-invariant, so a point `s ∈ 𝒦_k` whose residual `g + H s + μ s` is orthogonal to `𝒦_k` has
zero residual. -/
theorem residual_eq_zero_of_grade_le {k : ℕ} (hk : 1 ≤ k)
    (hgr : Krylov.grade (H : E →ₗ[ℝ] E) g ≤ k) {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[k])
    (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0) : g + H s + μ • s = 0 := by
  have hinv : 𝒦ₕ[k] ∈ Module.End.invtSubmodule (H : E →ₗ[ℝ] E) := by
    rw [Krylov.subspace_eq_of_grade_le _ _ hgr]
    exact Krylov.subspace_grade_mem_invtSubmodule _ _
  have hHs : H s ∈ 𝒦ₕ[k] :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hinv s hs
  have hr : g + H s + μ • s ∈ 𝒦ₕ[k] :=
    Submodule.add_mem _ (Submodule.add_mem _ (mem_krylov H g hk) hHs) (Submodule.smul_mem _ _ hs)
  exact inner_self_eq_zero.1 (hgal _ hr)

/-- **The restricted first-order condition in Lanczos coordinates** ((10.2.2), (B.10.1)). Let
`g ≠ 0`, `m + 1 ≤ grade(H, g)`, `s ∈ 𝒦_{m+1}` with `g + H s + μ s ⟂ 𝒦_{m+1}`, and let
`ȳⱼ = ⟪qⱼ, s⟫` be its Lanczos coordinates. Then `(T_{m+1} + μ) ȳ = -‖g‖ e₀` and
`‖g + H s + μ s‖ = β_m |ȳ_m|`. -/
theorem lanczos_galerkin (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[m + 1])
    (hgal : ∀ v ∈ 𝒦ₕ[m + 1], ⟪g + H s + μ • s, v⟫ = 0) :
    (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ (fun j => ⟪𝐪 j, s⟫) =
        -(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ) ∧
      ‖g + H s + μ • s‖ = 𝛃 m * |⟪𝐪 m, s⟫| := by
  set y : Fin (m + 1) → ℝ := fun j => ⟪𝐪 j, s⟫
  have hsy : ∑ j, y j • 𝐪 j = s := (eq_sum_inner_vec hs).symm
  obtain ⟨hrel, -, -, hnorm⟩ := krylov_lanczos_coordinates hH hg hm y y μ
  rw [hsy] at hrel hnorm
  have hsys : (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y =
      -(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ) := by
    rw [eq_neg_iff_add_eq_zero]
    funext i
    have h0 := hgal _ (Arnoldi.vec_mem_subspace_of_lt _ _ i.2)
    rw [hrel, real_inner_comm, inner_add_right, inner_vec_sum hm, real_inner_smul_right,
      Arnoldi.inner_vec_eq_zero _ _ (by have := i.2; omega), mul_zero, add_zero] at h0
    exact h0
  refine ⟨hsys, ?_⟩
  rw [hnorm hsys]
  simp [y]

/-- **The size of a restricted solution** (proofs of [cartis2022evaluation] Theorem 10.2.2 and
Corollary 10.2.3): if `s ∈ 𝒦_k` satisfies `g + H s + μ s ⟂ 𝒦_k` with `μ ≥ -θ₁`, then
`‖g‖ ≤ (θₖ + μ) ‖s‖`, `θₖ` the greatest Ritz value. -/
theorem norm_le_of_galerkin_krylov (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ} (hk : 1 ≤ k)
    {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[k]) (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0)
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) ≤ μ) :
    ‖g‖ ≤ (rightmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) + μ) * ‖s‖ := by
  have hsh := (compressionL_shifted_iff hs).2 hgal
  have h := norm_add_smul_apply_le (hH := isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) hμ ⟨s, hs⟩
  rw [hsh, norm_neg, orthogonalProjectionOnto_krylov hk] at h
  simp only [add_comm μ] at h
  exact h

/-- **The residual bound** (core of [cartis2022evaluation] Theorems 10.2.2 and 10.3.2; Gould and
Simoncini). Let `g ≠ 0`, `k ≥ 1`, `s ∈ 𝒦_k` with `g + H s + μ s ⟂ 𝒦_k`, and let the shift
`μ` be to the right of the least Ritz value `θ₁` of `𝒦_k`, so that `κ = κₖ(μ)` is the condition
number of the positive definite `T_k + μ`. Then
`‖g + H s + μ s‖ ≤ 2 ‖H‖ κ ‖s‖ q(κ)^{k-1}`, `q(κ) = (√κ - 1)/(√κ + 1)`.

Proof: in Lanczos coordinates the residual is `β_{k-1} |ȳ_{k-1}|` with
`ȳ = -‖g‖ (T_k + μ)⁻¹ e₀`; the `(k-1, 0)` entry of the inverse of the positive definite tridiagonal
`T_k + μ` is at most `2 q^{k-1} / (θ₁ + μ)` (`Matrix.abs_inv_apply_le_of_hasBandwidth_of_mem_Icc`,
Lemma B.10.1), `‖g‖ = ‖(P H| + μ) s‖ ≤ (θₖ + μ) ‖s‖`, and `β_{k-1} ≤ ‖H‖`. Beyond the grade
the residual vanishes. -/
theorem krylov_residual_le (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[k]) (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0)
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < μ) :
    ‖g + H s + μ • s‖ ≤
      2 * ‖H‖ * krylovCond hH g k μ * ‖s‖ * convFactor (krylovCond hH g k μ) ^ (k - 1) := by
  have hκ := one_le_krylovCond (g := g) hH hμ
  rcases le_or_gt (Krylov.grade (H : E →ₗ[ℝ] E) g) k with hgr | hgr
  · rw [residual_eq_zero_of_grade_le hk hgr hs hgal, norm_zero]
    have := convFactor_nonneg hκ
    positivity
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g := hgr.le
  set hC := isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH
  set a := leftmost hC + μ
  set b := rightmost hC + μ
  have ha : 0 < a := by simp only [a]; linarith
  have hab : a ≤ b := by simp only [a, b]; linarith [leftmost_le_rightmost (hH := hC)]
  have hcond : krylovCond hH g (m + 1) μ = b / a := rfl
  obtain ⟨hsys, hres⟩ := lanczos_galerkin hH hg hm hs hgal
  set y : Fin (m + 1) → ℝ := fun j => ⟪𝐪 j, s⟫
  set G := 𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  have hG : G.PosDef := posDef_tridiag_add hH hg hm hμ
  -- the last Lanczos coordinate through the inverse
  have hy : y = G⁻¹ *ᵥ (-(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ)) := by
    rw [← hsys, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det G).1 hG.isUnit), Matrix.one_mulVec]
  have hylast : |⟪𝐪 m, s⟫| = ‖g‖ * |G⁻¹ (Fin.last m) 0| := by
    have h := congrFun hy (Fin.last m)
    simp only [y, Fin.val_last] at h
    rw [h, Matrix.mulVec_neg]
    simp [abs_mul]
  -- the decay of the inverse
  obtain ⟨hl, hu⟩ := isTridiagonal_iff_hasBandwidth_one.1
    (tridiag_add_isTridiagonal (H := H) (g := g) (m + 1) μ)
  have hdecay := abs_inv_apply_le_of_hasBandwidth_of_mem_Icc hG hl hu ha
    (eigenvalues_tridiag_add_mem hH hg hm hG) (Fin.last m) 0
  simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, sub_zero, Int.natAbs_natCast,
    Nat.cast_one, div_one, Nat.ceil_natCast] at hdecay
  have hgs : ‖g‖ ≤ b * ‖s‖ := norm_le_of_galerkin_krylov hH (by omega) hs hgal hμ.le
  have hβ := beta_le_opNorm (H := H) (g := g) m
  have hq := convFactor_nonneg (one_le_krylovCond (g := g) hH hμ)
  rw [hcond] at hq ⊢
  rw [hres, hylast, Nat.add_sub_cancel]
  have hβ0 := Lanczos.beta_nonneg (H : E →ₗ[ℝ] E) g m
  calc 𝛃 m * (‖g‖ * |G⁻¹ (Fin.last m) 0|)
      ≤ ‖H‖ * ((b * ‖s‖) * (2 / a * convFactor (b / a) ^ m)) := by
        refine mul_le_mul hβ (mul_le_mul hgs hdecay (abs_nonneg _)
          (mul_nonneg (by linarith) (norm_nonneg _))) (by positivity) (norm_nonneg _)
    _ = 2 * ‖H‖ * (b / a) * ‖s‖ * convFactor (b / a) ^ m := by
        field_simp

/-- **Interlacing at the top**: the greatest Ritz value on a nonzero subspace is at most the
greatest eigenvalue `λmax` of `H` ([cartis2022evaluation], proof of Corollary 10.2.3). -/
theorem rightmost_compressionL_le (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (K : Submodule ℝ E)
    [Nontrivial K] : rightmost (isSymmetric_compressionL (K := K) hH) ≤ rightmost hH :=
  rightmost_le_of_forall fun v => by
    rw [inner_compressionL_right]
    exact inner_le_rightmost_mul_norm_sq (hH := hH) (v : E)

/-- **Theorem 10.2.2** (bound on the gradient at the Krylov subspace minimizer;
[cartis2022evaluation] Theorem 10.2.2, Gould–Simoncini). Let `H` be symmetric, `g ≠ 0`, `σ > 0`,
`r > 2`, `k ≥ 1`, and let `sₖ` minimize the regularized model over `𝒦_k(H, g)`, with multiplier
`λₖ = σ ‖sₖ‖^{r-2}` ((10.2.3)) and `κₖ = κₖ(λₖ)` ((10.2.8)). Then the gradient of the regularized
model satisfies
`‖g + H sₖ + λₖ sₖ‖ ≤ 2 ‖H‖ κₖ (λₖ/σ)^{1/(r-2)} ((√κₖ - 1)/(√κₖ + 1))^{k-1}` ((10.2.9)).
Here `‖H‖` is the operator norm of `E` (for scaled data, the largest `|λ|` of the pencil
`(H, M)`, which is at most the book's `‖M⁻¹ H‖`). -/
theorem krylov_gradient_bound_regularization (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {k : ℕ} (hk : 1 ≤ k) {s : E} (hs : s ∈ 𝒦ₕ[k])
    (hmin : IsMinOn (regModel g H σ r) (𝒦ₕ[k] : Set E) s) :
    ‖g + H s + (σ * ‖s‖ ^ (r - 2)) • s‖ ≤
      2 * ‖H‖ * krylovCond hH g k (σ * ‖s‖ ^ (r - 2)) *
        (σ * ‖s‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) *
        convFactor (krylovCond hH g k (σ * ‖s‖ ^ (r - 2))) ^ (k - 1) := by
  have hn : (σ * ‖s‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) = ‖s‖ := by
    rw [mul_div_cancel_left₀ _ hσ.ne', one_div,
      Real.rpow_rpow_inv (norm_nonneg _) (by linarith : r - 2 ≠ 0)]
  rw [hn]
  exact krylov_residual_le hH hg hk hs (galerkin_of_isMinOn_regModel_subspace hH hσ hr hs hmin).1
    (neg_leftmost_lt_of_isMinOn_regModel_krylov hH hg hσ hr hk hs hmin).1

/-- **Theorem 10.3.2** (bound on the residual at the Krylov subspace trust-region minimizer;
[cartis2022evaluation] Theorem 10.3.2). Let `H` be symmetric, `g ≠ 0`, `k ≥ 1`, and let `sₖ ∈ 𝒦_k`
be feasible (`‖sₖ‖ ≤ Δ`) with trust-region multiplier `λₖ` for the subproblem restricted to `𝒦_k`
(the compressed data), and `κₖ = κₖ(λₖ)`. Then the residual (10.3.1) satisfies
`‖g + H sₖ + λₖ sₖ‖ ≤ 2 ‖H‖ κₖ Δ ((√κₖ - 1)/(√κₖ + 1))^{k-1}`. -/
theorem krylov_residual_bound_trustRegion (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {Δ μ : ℝ} {k : ℕ} (hk : 1 ≤ k) {s : E} (hs : s ∈ 𝒦ₕ[k]) (hsΔ : ‖s‖ ≤ Δ)
    (h : IsTrustRegionMultiplier ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) Δ
      ⟨s, hs⟩ μ) :
    ‖g + H s + μ • s‖ ≤
      2 * ‖H‖ * krylovCond hH g k μ * Δ * convFactor (krylovCond hH g k μ) ^ (k - 1) := by
  have hμ := (neg_leftmost_lt_of_isTrustRegionMultiplier_krylov hH hg hk hs h).1
  refine (krylov_residual_le hH hg hk hs (h.galerkin_of_compressionL hs) hμ).trans ?_
  have hκ := one_le_krylovCond (g := g) hH hμ
  have hq := convFactor_nonneg hκ
  gcongr

/-- **Corollary 10.2.3** (iteration bound for the Krylov approximation, regularization;
[cartis2022evaluation] Corollary 10.2.3, corrected). Let `H` be symmetric, `g ≠ 0`, `σ > 0`,
`r > 2`, `θ > 0` (the constant `θ₁` of the stopping rule (9.3.14b)), and for `1 ≤ k ≤ grade(H, g)`
let `sₖ` minimize the regularized model over `𝒦_k(H, g)`, with multiplier `λₖ = σ ‖sₖ‖^{r-2}`.
Let `s*` be a global minimizer with `λ* = σ ‖s*‖^{r-2}`, `λmax` the greatest eigenvalue of `H`,
`κ*` an upper bound of the `κₖ(λₖ)` (the book takes their maximum (10.2.10)), `q* = q(κ*)` and
`A = (4 ‖H‖ κ* / θ) (λ*/σ)^{1/(r-2)} ((λmax + λ*)/‖g‖)²`. Then the stopping rule (9.3.14b),
`‖g + H sₖ + λₖ sₖ‖ ≤ ½ θ ‖sₖ‖²`, holds
(i) at every `k ∈ [1, grade]` with `A q*^{k-1} ≤ 1`, and (ii) at `k = grade`; hence
(iii) if `κ* > 1`, at some `k ≤ min (⌈log A / log (1/q*)⌉₊ + 1) grade`, and
(iv) if `κ* = 1`, at some `k ≤ min 2 grade`.
The book's ceiling is corrected to `⌈·⌉₊` (`log A` may be negative), and the case `κ* = 1`, where
the book's `log((√κ* + 1)/(√κ* - 1))` is undefined, is separated. -/
theorem krylov_iteration_bound_regularization (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {σ r θ : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hθ : 0 < θ) {s : ℕ → E}
    (hs : ∀ k, s k ∈ 𝒦ₕ[k])
    (hmin : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      IsMinOn (regModel g H σ r) (𝒦ₕ[k] : Set E) (s k))
    {sstar : E} (hstar : IsMinOn (regModel g H σ r) univ sstar) {κs : ℝ}
    (hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      krylovCond hH g k (σ * ‖s k‖ ^ (r - 2)) ≤ κs) :
    (∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      4 * ‖H‖ * κs / θ * (σ * ‖sstar‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) *
          ((rightmost hH + σ * ‖sstar‖ ^ (r - 2)) / ‖g‖) ^ 2 * convFactor κs ^ (k - 1) ≤ 1 →
        ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2) ∧
    ‖g + H (s (Krylov.grade (H : E →ₗ[ℝ] E) g)) +
        (σ * ‖s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ^ (r - 2)) • s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ≤
      1 / 2 * θ * ‖s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ^ 2 ∧
    (1 < κs → ∃ k, 1 ≤ k ∧
      k ≤ min (⌈Real.log (4 * ‖H‖ * κs / θ * (σ * ‖sstar‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) *
          ((rightmost hH + σ * ‖sstar‖ ^ (r - 2)) / ‖g‖) ^ 2) /
          Real.log (1 / convFactor κs)⌉₊ + 1) (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧
      ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2) ∧
    (κs = 1 → ∃ k, 1 ≤ k ∧ k ≤ min 2 (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧
      ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2) := by
  set G := Krylov.grade (H : E →ₗ[ℝ] E) g
  set lstar := σ * ‖sstar‖ ^ (r - 2)
  set A := 4 * ‖H‖ * κs / θ * (lstar / σ) ^ (1 / (r - 2)) * ((rightmost hH + lstar) / ‖g‖) ^ 2
  have hG : 1 ≤ G := Krylov.grade_pos_of_ne_zero _ _ hg
  have hgn : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hsn : (lstar / σ) ^ (1 / (r - 2)) = ‖sstar‖ := by
    rw [mul_div_cancel_left₀ _ hσ.ne', one_div,
      Real.rpow_rpow_inv (norm_nonneg _) (by linarith : r - 2 ≠ 0)]
  -- the geometric test
  have hP : ∀ k, 1 ≤ k → k ≤ G → A * convFactor κs ^ (k - 1) ≤ 1 →
      ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2 := by
    intro k hk hkG hA
    have hgal := (galerkin_of_isMinOn_regModel_subspace hH hσ hr (hs k) (hmin k hk hkG)).1
    have hμ := (neg_leftmost_lt_of_isMinOn_regModel_krylov hH hg hσ hr hk (hs k)
      (hmin k hk hkG)).1
    have hκ := one_le_krylovCond (g := g) hH hμ
    have hκk := hκs k hk hkG
    obtain ⟨hlam, hnorm⟩ := regMultiplier_le_of_inner_eq_zero hH hσ hr (hs k) hgal hstar
    -- the upper bound on the gradient
    have hup : ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤
        2 * ‖H‖ * κs * ‖sstar‖ * convFactor κs ^ (k - 1) := by
      refine (krylov_residual_le hH hg hk (hs k) hgal hμ).trans ?_
      have hq0 := convFactor_nonneg hκ
      have hq := convFactor_le_convFactor hκk
      have hκs0 : 0 ≤ κs := by linarith
      gcongr
    -- the lower bound on the step
    have : Nontrivial 𝒦ₕ[k] :=
      ⟨⟨⟨g, mem_krylov H g hk⟩, 0, fun h => hg (congrArg Subtype.val h)⟩⟩
    have hθk := rightmost_compressionL_le hH 𝒦ₕ[k]
    have hgs := norm_le_of_galerkin_krylov hH hk (hs k) hgal hμ.le
    have hlow : ‖g‖ ≤ (rightmost hH + lstar) * ‖s k‖ :=
      hgs.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have hD : 0 < rightmost hH + lstar := by
      by_contra hD
      push Not at hD
      have := mul_nonpos_of_nonpos_of_nonneg hD (norm_nonneg (s k))
      linarith
    have hsk : ‖g‖ / (rightmost hH + lstar) ≤ ‖s k‖ := by rwa [div_le_iff₀' hD]
    have hR : 2 * ‖H‖ * κs * ‖sstar‖ * convFactor κs ^ (k - 1) =
        1 / 2 * θ * (‖g‖ / (rightmost hH + lstar)) ^ 2 * (A * convFactor κs ^ (k - 1)) := by
      simp only [A, hsn]
      field_simp
      ring
    calc _ ≤ 2 * ‖H‖ * κs * ‖sstar‖ * convFactor κs ^ (k - 1) := hup
      _ = 1 / 2 * θ * (‖g‖ / (rightmost hH + lstar)) ^ 2 * (A * convFactor κs ^ (k - 1)) := hR
      _ ≤ 1 / 2 * θ * (‖g‖ / (rightmost hH + lstar)) ^ 2 * 1 := by gcongr
      _ ≤ 1 / 2 * θ * ‖s k‖ ^ 2 := by
        rw [mul_one]; gcongr
  -- exactness at the grade
  have hPG : ‖g + H (s G) + (σ * ‖s G‖ ^ (r - 2)) • s G‖ ≤ 1 / 2 * θ * ‖s G‖ ^ 2 := by
    rw [residual_eq_zero_of_grade_le hG le_rfl (hs G)
      (galerkin_of_isMinOn_regModel_subspace hH hσ hr (hs G) (hmin G hG le_rfl)).1, norm_zero]
    positivity
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP hPG
  refine ⟨hP, hPG, fun hκ => h1 (convFactor_pos hκ) (convFactor_lt_one κs), fun hκ => h2 ?_⟩
  rw [hκ, convFactor_one]

/-- **Corollary 10.3.3** (iteration bound for the Krylov approximation, trust region;
[cartis2022evaluation] Corollary 10.3.3, corrected). Let `H` be symmetric, `g ≠ 0`, `ε > 0`, and
for `1 ≤ k ≤ grade(H, g)` let `sₖ ∈ 𝒦_k` be feasible with trust-region multiplier `λₖ` for the
subproblem restricted to `𝒦_k`. Let `κ*` bound the `κₖ(λₖ)` and `q* = q(κ*)`. Then the residual
test (10.3.2), `‖g + H sₖ + λₖ sₖ‖ ≤ ε`, holds (i) at every `k ∈ [1, grade]` with
`2 ‖H‖ κ* Δ q*^{k-1} ≤ ε`, and (ii) at `k = grade`; hence (iii) if `κ* > 1`, at some
`k ≤ min (⌈log (2 ‖H‖ κ* Δ / ε) / log (1/q*)⌉₊ + 1) grade`, and (iv) if `κ* = 1`, at some
`k ≤ min 2 grade`. -/
theorem krylov_iteration_bound_trustRegion (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {Δ ε : ℝ} (hε : 0 < ε) {s : ℕ → E} {μ : ℕ → ℝ} (hs : ∀ k, s k ∈ 𝒦ₕ[k])
    (hmul : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g → ‖s k‖ ≤ Δ ∧
      IsTrustRegionMultiplier ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) Δ
        ⟨s k, hs k⟩ (μ k))
    {κs : ℝ} (hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      krylovCond hH g k (μ k) ≤ κs) :
    (∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      2 * ‖H‖ * κs * Δ * convFactor κs ^ (k - 1) ≤ ε → ‖g + H (s k) + μ k • s k‖ ≤ ε) ∧
    ‖g + H (s (Krylov.grade (H : E →ₗ[ℝ] E) g)) +
        μ (Krylov.grade (H : E →ₗ[ℝ] E) g) • s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ≤ ε ∧
    (1 < κs → ∃ k, 1 ≤ k ∧
      k ≤ min (⌈Real.log (2 * ‖H‖ * κs * Δ / ε) / Real.log (1 / convFactor κs)⌉₊ + 1)
        (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧ ‖g + H (s k) + μ k • s k‖ ≤ ε) ∧
    (κs = 1 → ∃ k, 1 ≤ k ∧ k ≤ min 2 (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧
      ‖g + H (s k) + μ k • s k‖ ≤ ε) := by
  set G := Krylov.grade (H : E →ₗ[ℝ] E) g
  have hG : 1 ≤ G := Krylov.grade_pos_of_ne_zero _ _ hg
  have hP : ∀ k, 1 ≤ k → k ≤ G → 2 * ‖H‖ * κs * Δ * convFactor κs ^ (k - 1) ≤ ε →
      ‖g + H (s k) + μ k • s k‖ ≤ ε := by
    intro k hk hkG hA
    obtain ⟨hsΔ, hm⟩ := hmul k hk hkG
    have hμ := (neg_leftmost_lt_of_isTrustRegionMultiplier_krylov hH hg hk (hs k) hm).1
    have hκ := one_le_krylovCond (g := g) hH hμ
    have hq0 := convFactor_nonneg hκ
    have hq := convFactor_le_convFactor (hκs k hk hkG)
    have hΔ : 0 ≤ Δ := (norm_nonneg _).trans hsΔ
    refine ((krylov_residual_bound_trustRegion hH hg hk (hs k) hsΔ hm).trans ?_).trans hA
    have hκs0 : 0 ≤ κs := by linarith [hκs k hk hkG]
    gcongr
    exact hκs k hk hkG
  have hPG : ‖g + H (s G) + μ G • s G‖ ≤ ε := by
    rw [residual_eq_zero_of_grade_le hG le_rfl (hs G)
      ((hmul G hG le_rfl).2.galerkin_of_compressionL (hs G)), norm_zero]
    exact hε.le
  have hP' : ∀ k, 1 ≤ k → k ≤ G → 2 * ‖H‖ * κs * Δ / ε * convFactor κs ^ (k - 1) ≤ 1 →
      ‖g + H (s k) + μ k • s k‖ ≤ ε := fun k hk hkG hA => hP k hk hkG (by
    rw [div_mul_eq_mul_div, div_le_one hε] at hA; exact hA)
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP' hPG
  refine ⟨hP, hPG, fun hκ => h1 (convFactor_pos hκ) (convFactor_lt_one κs), fun hκ => h2 ?_⟩
  rw [hκ, convFactor_one]

end Residual

end Subproblem
