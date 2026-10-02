/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace` beside the least-squares material.
-/
import Mathlib.Analysis.Convex.Extrema
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Constrained least squares

Least squares with a quadratic inequality constraint (LSQI, `min ‖Ax − b‖` subject to
`‖Bx − d‖ ≤ α`) and with linear equality constraints (LSE, `min ‖Ax − b‖` subject to `Bx = d`)
([golub2013matrix] §6.2).

## Main definitions

* `Matrix.IsLSQISolution A b B d α x` and `Matrix.IsLSESolution A b B d x`: the two problems, as
  specifications in the style of `Matrix.IsLeastSquaresSolution`; LSE is LSQI with `α = 0`
  (`Matrix.isLSQISolution_zero_iff`).
* `Matrix.augmentedLSE A B`: the symmetric indefinite matrix `[0 Aᴴ Bᴴ; A I 0; B 0 0]` of
  [golub2013matrix] (6.2.10).
* `Matrix.penaltyLSE A B b d λ`: the method of weighting, the solution
  `(AᴴA + λBᴴB)⁻¹(Aᴴb + λBᴴd)` of the stacked problem (6.2.13).

## Main results

* The sphere problem (6.2.1): a feasible least-squares solution solves it
  (`Matrix.isLSQISolution_of_isLeastSquaresSolution`); otherwise every solution lies on the sphere
  (`Matrix.IsLSQISolution.norm_eq_of_lt`), the ridge solution of norm `α` solves it
  (`Matrix.isLSQISolution_tikhonov`), and the secular equation `‖x(λ)‖ = α` has exactly one
  positive root (`Matrix.existsUnique_norm_toEuclideanLin_tikhonov_eq`). No Lagrange multiplier
  appears: `‖Ay − b‖² + λ‖y‖² ≥ ‖Ax(λ) − b‖² + λα²` does the work.
* LSE: through the QR factorization of `Bᴴ` (`Matrix.isLSESolution_of_isQR`, the derivation of
  Algorithm 6.2.2), existence and uniqueness (`Matrix.existsUnique_isLSESolution`), the augmented
  system (`Matrix.isLSESolution_of_augmented`, `Matrix.isUnit_augmentedLSE`), the GSVD
  (`Matrix.isLSQISolution_iff_of_isGSVD`, `Matrix.isLSESolution_sum_of_isGSVD`) and the method
  of weighting (`Matrix.penaltyLSE_sub_eq_sum_of_isGSVD`, `Matrix.tendsto_penaltyLSE`).

## Implementation notes

Vectors live in `EuclideanSpace` and matrices act through `Matrix.toEuclideanLin`, as in
`Numlib/LinearAlgebra/Matrix/LeastSquares`. The GSVD statements are in the block order of
Theorem 6.1.1 (`Matrix.IsGSVD`); the book's (6.2.12) and (6.2.14) are printed in the third
edition's order, and (6.2.14) has `λ²` for `λ`.

## References

* [golub2013matrix] §6.2.
-/

open Filter Topology

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Defs

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- **Least squares with a quadratic inequality constraint** ([golub2013matrix] (6.2.1),
(6.2.5)): `x` is feasible, `‖Bx − d‖ ≤ α`, and at least as good as every feasible point. The sphere
problem (6.2.1) is `B = 1`, `d = 0`. -/
structure IsLSQISolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) (B : Matrix p n 𝕜)
    (d : EuclideanSpace 𝕜 p) (α : ℝ) (x : EuclideanSpace 𝕜 n) : Prop where
  /-- The solution is feasible. -/
  feasible : ‖toEuclideanLin B x - d‖ ≤ α
  /-- The solution is optimal among feasible points. -/
  le : ∀ y, ‖toEuclideanLin B y - d‖ ≤ α → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

/-- **Least squares with linear equality constraints** ([golub2013matrix] (6.2.9)): `Bx = d` and
`x` is at least as good as every `y` with `By = d`. -/
structure IsLSESolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) (B : Matrix p n 𝕜)
    (d : EuclideanSpace 𝕜 p) (x : EuclideanSpace 𝕜 n) : Prop where
  /-- The solution is feasible. -/
  feasible : toEuclideanLin B x = d
  /-- The solution is optimal among feasible points. -/
  le : ∀ y, toEuclideanLin B y = d → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {B : Matrix p n 𝕜} {d : EuclideanSpace 𝕜 p}
  {x : EuclideanSpace 𝕜 n}

/-- **LSE is LSQI with `α = 0`** ([golub2013matrix] §6.2.3). -/
theorem isLSQISolution_zero_iff : IsLSQISolution A b B d 0 x ↔ IsLSESolution A b B d x := by
  constructor
  · rintro ⟨hf, hle⟩
    exact ⟨sub_eq_zero.1 (norm_le_zero_iff.1 hf),
      fun y hy => hle y (by rw [hy, sub_self, norm_zero])⟩
  · rintro ⟨hf, hle⟩
    exact ⟨by rw [hf, sub_self, norm_zero],
      fun y hy => hle y (sub_eq_zero.1 (norm_le_zero_iff.1 hy))⟩

/-- **A feasible least-squares solution solves LSQI** ([golub2013matrix] §6.2.1, "if … `x_LS`
satisfies `‖x_LS‖₂ ≤ α`, then it obviously solves (6.2.1)"). -/
theorem isLSQISolution_of_isLeastSquaresSolution (h : IsLeastSquaresSolution A b x) {α : ℝ}
    (hx : ‖toEuclideanLin B x - d‖ ≤ α) : IsLSQISolution A b B d α x :=
  ⟨hx, fun y _ => h y⟩

omit [Fintype p] in
/-- **Non-uniqueness** ([golub2013matrix] §6.2.3, "if `null(A) ∩ null(B) ≠ {0}` … the LSE solution
is not unique"): adding a common null vector of `A` and `B` to an LSE solution gives another. -/
theorem IsLSESolution.add_of_mem (h : IsLSESolution A b B d x) {z : EuclideanSpace 𝕜 n}
    (hz : z ∈ LinearMap.ker (toEuclideanLin A) ⊓ LinearMap.ker (toEuclideanLin B)) :
    IsLSESolution A b B d (x + z) := by
  obtain ⟨hA, hB⟩ := Submodule.mem_inf.1 hz
  rw [LinearMap.mem_ker] at hA hB
  refine ⟨by rw [map_add, hB, add_zero, h.feasible], fun y hy => ?_⟩
  rw [map_add, hA, add_zero]
  exact h.le y hy

omit [Fintype p] in
/-- **Uniqueness of the LSE solution**: two LSE solutions differ by a common null vector of `A`
and `B` (by the parallelogram law, the midpoint would otherwise do better), so they agree when
`ker A ⊓ ker B = ⊥`. -/
theorem IsLSESolution.eq_of_ker_inf_ker_eq_bot {x x' : EuclideanSpace 𝕜 n}
    (hsol : IsLSESolution A b B d x) (hx' : IsLSESolution A b B d x')
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) : x' = x := by
  -- uniqueness through the parallelogram law
  have hv : ‖toEuclideanLin A x - b‖ = ‖toEuclideanLin A x' - b‖ :=
    le_antisymm (hsol.le x' hx'.feasible) (hx'.le x hsol.feasible)
  have hmid : toEuclideanLin B ((2⁻¹ : 𝕜) • (x + x')) = d := by
    rw [map_smul, map_add, hsol.feasible, hx'.feasible, ← two_smul 𝕜 d, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  have hle := hsol.le _ hmid
  have hmid' : toEuclideanLin A ((2⁻¹ : 𝕜) • (x + x')) - b
      = (2⁻¹ : 𝕜) • ((toEuclideanLin A x - b) + (toEuclideanLin A x' - b)) := by
    rw [map_smul, map_add]
    module
  rw [hmid', norm_smul, norm_inv, RCLike.norm_ofNat] at hle
  have hpar := parallelogram_law_with_norm 𝕜 (toEuclideanLin A x - b) (toEuclideanLin A x' - b)
  have h2 : 2 * ‖toEuclideanLin A x - b‖
      ≤ ‖(toEuclideanLin A x - b) + (toEuclideanLin A x' - b)‖ := by linarith
  have hsq := mul_self_le_mul_self (by positivity) h2
  have hz : ‖(toEuclideanLin A x - b) - (toEuclideanLin A x' - b)‖ = 0 := by
    have h0 : ‖(toEuclideanLin A x - b) - (toEuclideanLin A x' - b)‖ *
        ‖(toEuclideanLin A x - b) - (toEuclideanLin A x' - b)‖ = 0 := by
      refine le_antisymm ?_ (mul_self_nonneg _)
      rw [← hv] at hpar
      nlinarith
    exact mul_self_eq_zero.1 h0
  have hA0 : toEuclideanLin A (x - x') = 0 := by
    rw [norm_eq_zero, sub_sub_sub_cancel_right] at hz
    rw [map_sub, hz]
  have hB0 : toEuclideanLin B (x - x') = 0 := by
    rw [map_sub, hsol.feasible, hx'.feasible, sub_self]
  have hmem : WithLp.ofLp (x - x') ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, mulVecLin_apply, ← ofLp_toEuclideanLin, hA0, WithLp.ofLp_zero]
    · rw [LinearMap.mem_ker, mulVecLin_apply, ← ofLp_toEuclideanLin, hB0, WithLp.ofLp_zero]
  rw [hAB, Submodule.mem_bot] at hmem
  have : x - x' = 0 := by simpa using congrArg (WithLp.toLp 2) hmem
  exact (sub_eq_zero.1 this).symm

end Defs

/-! ### Least squares over a sphere -/

section Sphere

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m]
  {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- The sphere problem's constraint `‖1 x − 0‖ ≤ α` is `‖x‖ ≤ α`. -/
private theorem norm_one_sub_zero (y : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (1 : Matrix n n 𝕜) y - 0‖ = ‖y‖ := by
  rw [toEuclideanLin_one_apply, sub_zero]

omit [DecidableEq m] in
/-- A local minimizer of `‖Ay − b‖` in the interior of the ball is a global one: the objective is
convex (`IsMinOn.of_isLocalMin_of_convex_univ`). -/
private theorem isLeastSquaresSolution_of_forall_norm_le {α : ℝ} (hx : ‖x‖ < α)
    (h : ∀ y : EuclideanSpace 𝕜 n, ‖y‖ ≤ α → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖) :
    IsLeastSquaresSolution A b x := by
  have hconv : ConvexOn ℝ Set.univ fun y : EuclideanSpace 𝕜 n => ‖toEuclideanLin A y - b‖ := by
    refine ⟨convex_univ, fun y _ z _ s t hs ht hst => ?_⟩
    have e : toEuclideanLin A (s • y + t • z) - b
        = s • (toEuclideanLin A y - b) + t • (toEuclideanLin A z - b) := by
      rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_sub, smul_sub]
      nth_rw 1 [← one_smul ℝ b, ← hst, add_smul]
      abel
    refine (e ▸ norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht, smul_eq_mul,
      smul_eq_mul]
  have hloc : IsLocalMin (fun y : EuclideanSpace 𝕜 n => ‖toEuclideanLin A y - b‖) x :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x (sub_pos.2 hx)) fun y hy => h y (by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith [norm_sub_norm_le y x])
  exact IsMinOn.of_isLocalMin_of_convex_univ hloc hconv

/-- **The LSQI solution lies on the sphere** ([golub2013matrix] (6.2.3), "it follows that the
solution to (6.2.1) is on the boundary of the constraint sphere"): if `α < ‖A⁺ b‖` then every
solution of the sphere problem has `‖x‖ = α`. Otherwise it would minimize the convex objective
near `x`, hence globally, and a least-squares solution has norm at least `‖A⁺ b‖`. -/
theorem IsLSQISolution.norm_eq_of_lt {α : ℝ} (hα : α < ‖toEuclideanLin A.pinv b‖)
    (h : IsLSQISolution A b (1 : Matrix n n 𝕜) 0 α x) : ‖x‖ = α := by
  have hxα : ‖x‖ ≤ α := by simpa [norm_one_sub_zero] using h.feasible
  refine le_antisymm hxα (not_lt.1 fun hlt => ?_)
  have hls := isLeastSquaresSolution_of_forall_norm_le hlt fun y hy =>
    h.le y (by rw [norm_one_sub_zero]; exact hy)
  have := A.norm_pinv_le_of_normalEquations b (isLeastSquaresSolution_iff_normalEquations.1 hls)
  linarith

/-- **A ridge solution of norm `α` solves the sphere problem** ([golub2013matrix] §6.2.1, "It
follows that `x(λ₊)` solves (6.2.1)"): for feasible `y`,
`‖Ay − b‖² ≥ ‖Ax − b‖² + λ(α² − ‖y‖²) ≥ ‖Ax − b‖²`
(`Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn`) —
the sufficiency half of the Lagrange conditions, without the multiplier theorem. -/
theorem isLSQISolution_tikhonov {μ : ℝ} (hμ : 0 < μ) {α : ℝ}
    (hn : ‖toEuclideanLin (A.tikhonov μ) b‖ = α) :
    IsLSQISolution A b (1 : Matrix n n 𝕜) 0 α (toEuclideanLin (A.tikhonov μ) b) := by
  refine ⟨by rw [norm_one_sub_zero, hn], fun y hy => ?_⟩
  rw [norm_one_sub_zero] at hy
  have hmin := isMinOn_univ_iff.1 ((A.eq_toEuclideanLin_tikhonov_iff_isMinOn hμ b _).1 rfl) y
  rw [hn] at hmin
  have hy2 : ‖y‖ ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  nlinarith

/-- **The secular equation has a unique positive root** ([golub2013matrix] §6.2.1: "`f(0) > 0` …
`f'(λ) < 0` for `λ ≥ 0` … `f` has a unique positive root `λ₊`"): for `0 < α < ‖A⁺ b‖` there is
exactly one `λ > 0` with `‖x(λ)‖ = α`. The norm decreases strictly and continuously from `‖A⁺ b‖`
at `0⁺` to `0` at `∞` (`existsUnique_pos_eq_of_strictAntiOn_Ioi`). -/
theorem existsUnique_norm_toEuclideanLin_tikhonov_eq {α : ℝ} (hα0 : 0 < α)
    (hα : α < ‖toEuclideanLin A.pinv b‖) :
    ∃! μ : ℝ, 0 < μ ∧ ‖toEuclideanLin (A.tikhonov μ) b‖ = α := by
  have h0 : Tendsto (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖) (𝓝[>] 0)
      (𝓝 ‖toEuclideanLin A.pinv b‖) := by
    have hc : Continuous fun M : Matrix n m 𝕜 => ‖toEuclideanLin M b‖ := by
      have : Continuous fun M : Matrix n m 𝕜 => toEuclideanLin M b :=
        (LinearMap.continuous_of_finiteDimensional
          (LinearMap.applyₗ (R := 𝕜) b ∘ₗ (toEuclideanLin (m := n) (n := m)).toLinearMap))
      exact continuous_norm.comp this
    exact (hc.tendsto _).comp A.tendsto_tikhonov_pinv
  have hAb : toEuclideanLin Aᴴ b ≠ 0 := by
    intro h
    have : toEuclideanLin A.pinv b = 0 := by
      rw [pinv_def, toEuclideanLin_mul_apply, h, map_zero]
    rw [this, norm_zero] at hα
    linarith
  exact existsUnique_pos_eq_of_strictAntiOn_Ioi (A.strictAntiOn_norm_toEuclideanLin_tikhonov hAb)
    (continuousOn_norm_toEuclideanLin_tikhonov A b) h0
    (A.tendsto_norm_toEuclideanLin_tikhonov_atTop b) hα0 hα

@[deprecated (since := "2026-09-30")]
alias existsUnique_norm_tikhonov_mulVec_eq := existsUnique_norm_toEuclideanLin_tikhonov_eq

end Sphere

/-! ### Least squares with equality constraints -/

section LSE

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq m]
  [DecidableEq p] {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {B : Matrix p n 𝕜}
  {d : EuclideanSpace 𝕜 p}

omit [Fintype p] [DecidableEq m] [DecidableEq p] in
/-- **Existence and uniqueness of the LSE solution** ([golub2013matrix] §6.2.3–6.2.5): if the
constraint `Bx = d` is consistent, an LSE solution exists, and if moreover
`ker A ⊓ ker B = ⊥` it is unique. Existence: with `B x₀ = d` and `N = 1 − B⁺B` (whose range is
`ker B`), the feasible points are `x₀ + N z`, so a least-squares solution `z₀` of
`(A N) z ≈ b − A x₀` gives the solution `x₀ + N z₀`. Uniqueness: for two solutions the
parallelogram law makes `A (x − x')` vanish. -/
theorem existsUnique_isLSESolution [Finite p]
    (hd : d ∈ LinearMap.range (toEuclideanLin B)) :
    (∃ x, IsLSESolution A b B d x) ∧
      (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ →
        ∃! x, IsLSESolution A b B d x) := by
  classical
  have := Fintype.ofFinite p
  obtain ⟨x₀, hx₀⟩ := hd
  set N : Matrix n n 𝕜 := 1 - B.pinv * B with hN
  have hBN : B * N = 0 := by rw [hN, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    mul_pinv_mul_self, sub_self]
  have hNv : ∀ v : EuclideanSpace 𝕜 n, toEuclideanLin B v = 0 → toEuclideanLin N v = v := by
    intro v hv
    rw [hN, toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply, hv,
      map_zero, sub_zero]
  set c : EuclideanSpace 𝕜 m := b - toEuclideanLin A x₀ with hc
  set z₀ := toEuclideanLin (A * N).pinv c
  have hz₀ := (A * N).isLeastSquaresSolution_pinv c
  set x := x₀ + toEuclideanLin N z₀ with hx
  have hres : ∀ z,
      toEuclideanLin A (x₀ + toEuclideanLin N z) - b = toEuclideanLin (A * N) z - c := by
    intro z
    rw [hc, map_add, toEuclideanLin_mul_apply]
    abel
  have hsol : IsLSESolution A b B d x := by
    refine ⟨by rw [hx, map_add, hx₀, ← toEuclideanLin_mul_apply, hBN, toEuclideanLin_zero_apply,
      add_zero], fun y hy => ?_⟩
    have hy' : y = x₀ + toEuclideanLin N (y - x₀) := by
      rw [hNv _ (by rw [map_sub, hy, hx₀, sub_self]), add_sub_cancel]
    rw [hx, hres, hy', hres]
    exact hz₀ _
  exact ⟨⟨x, hsol⟩, fun hAB => ⟨x, hsol, fun x' hx' => hsol.eq_of_ker_inf_ker_eq_bot hx' hAB⟩⟩

/-- **The augmented matrix of the LSE problem** ([golub2013matrix] (6.2.10)): the symmetric
indefinite matrix `[0 Aᴴ Bᴴ; A I 0; B 0 0]` on `n ⊕ (m ⊕ p)`. -/
def augmentedLSE (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) : Matrix (n ⊕ (m ⊕ p)) (n ⊕ (m ⊕ p)) 𝕜 :=
  fromBlocks 0 (fromCols Aᴴ Bᴴ) (fromRows A B) (fromBlocks 1 0 0 0)

omit [DecidableEq n] [DecidableEq p] in
/-- The three block rows of the augmented system: `Aᴴr + Bᴴλ`, `Ax + r`, `Bx`. -/
theorem augmentedLSE_mulVec (x : n → 𝕜) (r : m → 𝕜) (l : p → 𝕜) :
    augmentedLSE A B *ᵥ Sum.elim x (Sum.elim r l)
      = Sum.elim (Aᴴ *ᵥ r + Bᴴ *ᵥ l) (Sum.elim (A *ᵥ x + r) (B *ᵥ x)) := by
  rw [augmentedLSE, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, fromCols_mulVec,
    fromRows_mulVec, fromBlocks_mulVec, one_mulVec, zero_mulVec, add_zero]
  ext (_ | _ | _) <;> simp

omit [DecidableEq m] [DecidableEq p] in
/-- `⟪r, A w⟫ = 0` when `Aᴴ r = −Bᴴ l` and `B w = 0`. -/
private theorem inner_mulVec_eq_zero {r : m → 𝕜} {l : p → 𝕜} {w : n → 𝕜}
    (h : Aᴴ *ᵥ r + Bᴴ *ᵥ l = 0) (hw : B *ᵥ w = 0) :
    inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m) (toEuclideanLin A (WithLp.toLp 2 w)) = 0 := by
  classical
  rw [← toEuclideanLin_conjTranspose_inner_left, toEuclideanLin_toLp,
    eq_neg_of_add_eq_zero_left h, WithLp.toLp_neg, inner_neg_left, ← toEuclideanLin_toLp,
    toEuclideanLin_conjTranspose_inner_left, toEuclideanLin_toLp, hw, WithLp.toLp_zero,
    inner_zero_right, neg_zero]

omit [DecidableEq p] in
/-- **The augmented system solves LSE** ([golub2013matrix] §6.2.4, (6.2.10)): if
`[0 Aᴴ Bᴴ; A I 0; B 0 0] [x; r; λ] = [0; b; d]` then `x` solves LSE. For feasible `y`,
`Ay − b = A(y − x) − r` and `⟪r, A(y − x)⟫ = −⟪λ, B(y − x)⟫ = 0`, so
`‖Ay − b‖² = ‖r‖² + ‖A(y − x)‖²`. -/
theorem isLSESolution_of_augmented {x : n → 𝕜} {r : m → 𝕜} {l : p → 𝕜} {b' : m → 𝕜}
    {d' : p → 𝕜}
    (h : augmentedLSE A B *ᵥ Sum.elim x (Sum.elim r l) = Sum.elim (0 : n → 𝕜) (Sum.elim b' d')) :
    IsLSESolution A (WithLp.toLp 2 b') B (WithLp.toLp 2 d') (WithLp.toLp 2 x) := by
  rw [augmentedLSE_mulVec] at h
  have h1 : Aᴴ *ᵥ r + Bᴴ *ᵥ l = 0 := funext fun i => congrFun h (Sum.inl i)
  have h2 : A *ᵥ x + r = b' := funext fun i => congrFun h (Sum.inr (Sum.inl i))
  have h3 : B *ᵥ x = d' := funext fun i => congrFun h (Sum.inr (Sum.inr i))
  refine ⟨by rw [toEuclideanLin_toLp, h3], fun y hy => ?_⟩
  set w : n → 𝕜 := WithLp.ofLp y - x with hw
  have hBw : B *ᵥ w = 0 := by
    have := congrArg WithLp.ofLp hy
    rw [ofLp_toEuclideanLin] at this
    rw [hw, mulVec_sub, this, h3, sub_self]
  have hr : toEuclideanLin A (WithLp.toLp 2 x) - WithLp.toLp 2 b' = -WithLp.toLp 2 r := by
    rw [← h2, toEuclideanLin_toLp, WithLp.toLp_add]
    abel
  have hy' : toEuclideanLin A y - WithLp.toLp 2 b'
      = toEuclideanLin A (WithLp.toLp 2 w) + (-WithLp.toLp 2 r) := by
    rw [← hr, hw, WithLp.toLp_sub, WithLp.toLp_ofLp, map_sub]
    abel
  have hinner := inner_mulVec_eq_zero h1 hBw
  rw [hr, hy']
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_add_sq (𝕜 := 𝕜), inner_neg_right, ← inner_conj_symm, hinner]
  simp only [map_zero, neg_zero, mul_zero, add_zero]
  nlinarith [sq_nonneg ‖toEuclideanLin A (WithLp.toLp 2 w)‖]

/-- **The augmented system is nonsingular for full-rank data** ([golub2013matrix] §6.2.4, "This
system is nonsingular if both `A` and `B` have full rank"): if `A` has independent columns and
`B` independent rows. Kernel argument: `Aᴴr + Bᴴλ = 0`, `Ax + r = 0`, `Bx = 0` give
`‖r‖² = −⟪r, Ax⟫ = 0`, so `r = 0`, `x = 0` and then `Bᴴλ = 0`, `λ = 0`. -/
theorem isUnit_augmentedLSE (hA : LinearIndependent 𝕜 Aᵀ) (hB : LinearIndependent 𝕜 B) :
    IsUnit (augmentedLSE A B) := by
  have hAi : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
  have hBi : Function.Injective B.vecMul := vecMul_injective_iff.2 hB
  refine mulVec_injective_iff_isUnit.1 fun u v huv => ?_
  rw [← sub_eq_zero]
  rw [← sub_eq_zero, ← mulVec_sub] at huv
  set w := u - v
  have hw : w = Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr ∘ Sum.inl)
      (w ∘ Sum.inr ∘ Sum.inr)) := by
    ext (_ | _ | _) <;> rfl
  rw [hw, augmentedLSE_mulVec] at huv
  set x := w ∘ Sum.inl
  set r := w ∘ Sum.inr ∘ Sum.inl
  set l := w ∘ Sum.inr ∘ Sum.inr
  have h1 : Aᴴ *ᵥ r + Bᴴ *ᵥ l = 0 := funext fun i => congrFun huv (Sum.inl i)
  have h2 : A *ᵥ x + r = 0 := funext fun i => congrFun huv (Sum.inr (Sum.inl i))
  have h3 : B *ᵥ x = 0 := funext fun i => congrFun huv (Sum.inr (Sum.inr i))
  have hinner := inner_mulVec_eq_zero h1 h3
  have hr0 : r = 0 := by
    have hrA : r = -(A *ᵥ x) := eq_neg_of_add_eq_zero_right h2
    have : inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m) (WithLp.toLp 2 r) = 0 := by
      calc inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m) (WithLp.toLp 2 r)
          = inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m)
              (-toEuclideanLin A (WithLp.toLp 2 x)) := by
            rw [toEuclideanLin_toLp, ← WithLp.toLp_neg, ← hrA]
        _ = 0 := by rw [inner_neg_right, hinner, neg_zero]
    rw [inner_self_eq_zero, WithLp.toLp_eq_zero] at this
    exact this
  have hx0 : x = 0 := hAi (by rw [mulVec_zero]; rwa [hr0, add_zero] at h2)
  have hl0 : l = 0 := by
    rw [hr0, mulVec_zero, zero_add] at h1
    have hs : star l ᵥ* B = (0 : p → 𝕜) ᵥ* B := by
      rw [zero_vecMul]
      have := congrArg star h1
      rwa [star_mulVec, conjTranspose_conjTranspose, star_zero] at this
    exact star_eq_zero.1 (hBi hs)
  rw [hw, hx0, hr0, hl0]
  ext (_ | _ | _) <;> rfl

end LSE

/-! ### LSE through the QR factorization of `Bᴴ` -/

section QR

variable {m : Type*} [Fintype m] [DecidableEq m] {p n : ℕ}

omit [DecidableEq m] in
/-- **LSE through the QR factorization of `Bᴴ`** ([golub2013matrix] §6.2.3, the derivation of
Algorithm 6.2.2): let `B` have independent rows, `Bᴴ = Q R` a QR factorization, `Q = [Q₁ Q₂]` split
`p | n − p` and `R₁` the leading `p × p` block of `R`. Put `y = (R₁ᴴ)⁻¹ d` and let `z` be any
least-squares solution of `(A Q₂) z ≈ b − A Q₁ y`. Then `Q₁ y + Q₂ z` solves LSE. Since
`B Q = Rᴴ = [R₁ᴴ 0]`, the feasible points are exactly the `Q₁ y + Q₂ z'`, where the objective is
`‖A Q₂ z' − (b − A Q₁ y)‖`. -/
theorem isLSESolution_of_isQR {A : Matrix m (Fin n) 𝕜} {b : EuclideanSpace 𝕜 m}
    {B : Matrix (Fin p) (Fin n) 𝕜} {d : EuclideanSpace 𝕜 (Fin p)} (hpn : p ≤ n)
    (hB : LinearIndependent 𝕜 B) {Q : Matrix (Fin n) (Fin n) 𝕜} {R : Matrix (Fin n) (Fin p) 𝕜}
    (h : IsQR Bᴴ Q R) {z : EuclideanSpace 𝕜 (Fin (n - p))}
    (hz : IsLeastSquaresSolution (A * Q.lastColumns (Nat.sub_le n p))
      (b - toEuclideanLin (A * Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᴴ)⁻¹ d)) z) :
    IsLSESolution A b B d
      (toEuclideanLin (Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᴴ)⁻¹ d)
        + toEuclideanLin (Q.lastColumns (Nat.sub_le n p)) z) := by
  classical
  set Q₁ := Q.firstColumns hpn with hQ₁
  set Q₂ := Q.lastColumns (Nat.sub_le n p) with hQ₂
  set R₁ := R.firstRows hpn with hR₁
  set y := toEuclideanLin (R₁ᴴ)⁻¹ d with hy
  set c := b - toEuclideanLin (A * Q₁) y with hc
  have hQQ : Qᴴ * Q = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup
  have hBQ : B * Q = Rᴴ := by
    have hB' : B = Rᴴ * Qᴴ := by rw [← conjTranspose_mul, h.mul_eq, conjTranspose_conjTranspose]
    rw [hB', Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hBQ₁ : B * Q₁ = R₁ᴴ := by
    ext i j
    have := congrFun (congrFun hBQ i) (Fin.castLE hpn j)
    simp only [mul_apply, conjTranspose_apply] at this
    simp only [hQ₁, hR₁, mul_apply, firstColumns_apply, conjTranspose_apply, firstRows_apply]
    exact this
  have hBQ₂ : B * Q₂ = 0 := by
    ext i j
    have := congrFun (congrFun hBQ i) ⟨n - (n - p) + j, by omega⟩
    simp only [mul_apply, conjTranspose_apply] at this
    simp only [hQ₂, mul_apply, lastColumns_apply, zero_apply]
    rw [this, h.apply_eq_zero _ i (by simp only; omega), star_zero]
  have hsplit : Q₁ * Q₁ᴴ + Q₂ * Q₂ᴴ = 1 :=
    firstColumns_mul_conjTranspose_add_lastColumns_mul_conjTranspose h.mem_unitaryGroup hpn
      (Nat.sub_le n p) (by omega)
  have hR₁u : IsUnit (R₁ᴴ).det := by
    have hBc : LinearIndependent 𝕜 (Bᴴ)ᵀ := by
      refine mulVec_injective_iff.1 fun v w hvw => ?_
      have hBi : Function.Injective B.vecMul := vecMul_injective_iff.2 hB
      have := congrArg star hvw
      simp only [star_mulVec, conjTranspose_conjTranspose] at this
      exact star_injective (hBi this)
    rw [det_conjTranspose]
    exact ((isUnit_iff_isUnit_det _).1 (h.isUnit_firstRows_of_linearIndependent hpn hBc)).star
  have hy' : toEuclideanLin R₁ᴴ y = d := by
    rw [hy, ← toEuclideanLin_mul_apply, mul_nonsing_inv _ hR₁u, toEuclideanLin_one_apply]
  -- the residual at `Q₁ y + Q₂ z'`
  have hres : ∀ z', toEuclideanLin A (toEuclideanLin Q₁ y + toEuclideanLin Q₂ z') - b
      = toEuclideanLin (A * Q₂) z' - c := by
    intro z'
    rw [hc, map_add, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    abel
  refine ⟨?_, fun y' hy'' => ?_⟩
  · rw [map_add, ← toEuclideanLin_mul_apply B Q₁, ← toEuclideanLin_mul_apply B Q₂, hBQ₁, hBQ₂,
      toEuclideanLin_zero_apply, add_zero, hy']
  · -- every feasible point is `Q₁ y + Q₂ w₂`
    have hdec : y' = toEuclideanLin Q₁ (toEuclideanLin Q₁ᴴ y')
        + toEuclideanLin Q₂ (toEuclideanLin Q₂ᴴ y') := by
      rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← LinearMap.add_apply,
        ← map_add, hsplit, toEuclideanLin_one_apply]
    have hw₁ : toEuclideanLin Q₁ᴴ y' = y := by
      have hBy : toEuclideanLin B y' = toEuclideanLin R₁ᴴ (toEuclideanLin Q₁ᴴ y') := by
        conv_lhs => rw [hdec]
        rw [map_add, ← toEuclideanLin_mul_apply B Q₁, ← toEuclideanLin_mul_apply B Q₂, hBQ₁,
          hBQ₂, toEuclideanLin_zero_apply, add_zero]
      rw [hy'', ← hy'] at hBy
      have := congrArg (toEuclideanLin (R₁ᴴ)⁻¹) hBy
      rw [← toEuclideanLin_mul_apply (R₁ᴴ)⁻¹ R₁ᴴ, ← toEuclideanLin_mul_apply (R₁ᴴ)⁻¹ R₁ᴴ,
        nonsing_inv_mul _ hR₁u, toEuclideanLin_one_apply, toEuclideanLin_one_apply] at this
      exact this.symm
    rw [hres, hdec, hw₁, hres]
    exact hz _

end QR

/-! ### Constrained least squares in GSVD coordinates -/

section GSVD

/-- A unitary change of coordinates on the left and an invertible one on the right: the residual
of `Uᴴ M X` at `y` against `Uᴴ c` has the norm of the residual of `M` at `X y` against `c`. -/
private theorem norm_unitary_mul_mul_sub {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (M : Matrix m n 𝕜)
    (X : Matrix n n 𝕜) (c : EuclideanSpace 𝕜 m) (y : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (star U * M * X) y - toEuclideanLin (star U) c‖
      = ‖toEuclideanLin M (toEuclideanLin X y) - c‖ := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, ← map_sub,
    norm_toEuclideanLin_apply_of_mem_unitaryGroup (Unitary.star_mem hU)]

/-- LSQI is invariant under unitary changes of the residual coordinates and an invertible change of
the variable: `y` solves the transformed problem iff `X y` solves the original one. -/
theorem isLSQISolution_unitary_mul_mul_iff {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq q] {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m}
    {B : Matrix q n 𝕜} {d : EuclideanSpace 𝕜 q} {α : ℝ} {U₁ : Matrix m m 𝕜}
    {U₂ : Matrix q q 𝕜} {X : Matrix n n 𝕜} (hU₁ : U₁ ∈ unitaryGroup m 𝕜)
    (hU₂ : U₂ ∈ unitaryGroup q 𝕜) (hX : IsUnit X) (y : EuclideanSpace 𝕜 n) :
    IsLSQISolution (star U₁ * A * X) (toEuclideanLin (star U₁) b) (star U₂ * B * X)
        (toEuclideanLin (star U₂) d) α y ↔ IsLSQISolution A b B d α (toEuclideanLin X y) := by
  have hXX : ∀ v, toEuclideanLin X (toEuclideanLin X⁻¹ v) = v := fun v => by
    rw [← toEuclideanLin_mul_apply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det X).1 hX),
      toEuclideanLin_one_apply]
  constructor
  · rintro ⟨hf, hle⟩
    refine ⟨by rwa [norm_unitary_mul_mul_sub hU₂] at hf, fun v hv => ?_⟩
    have := hle (toEuclideanLin X⁻¹ v) (by rwa [norm_unitary_mul_mul_sub hU₂, hXX])
    rwa [norm_unitary_mul_mul_sub hU₁, norm_unitary_mul_mul_sub hU₁, hXX] at this
  · rintro ⟨hf, hle⟩
    refine ⟨by rwa [norm_unitary_mul_mul_sub hU₂], fun v hv => ?_⟩
    rw [norm_unitary_mul_mul_sub hU₁, norm_unitary_mul_mul_sub hU₁]
    exact hle _ (by rwa [norm_unitary_mul_mul_sub hU₂] at hv)

variable {m₁ m₂ n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin m₂) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α' β' : ℕ → ℝ}

/-- **LSQI in GSVD coordinates** ([golub2013matrix] (6.2.6), and (6.2.11) at `α = 0`): with a
GSVD `U₁ᴴ A X = D_A`, `U₂ᴴ B X = D_B`, `x` solves `min ‖Ax − b‖, ‖Bx − d‖ ≤ α` iff `X⁻¹ x` solves
`min ‖D_A y − b̃‖, ‖D_B y − d̃‖ ≤ α` with `b̃ = U₁ᴴ b`, `d̃ = U₂ᴴ d`. -/
theorem isLSQISolution_iff_of_isGSVD (h : IsGSVD A B U₁ U₂ X α' β') {b : EuclideanSpace 𝕜 (Fin m₁)}
    {d : EuclideanSpace 𝕜 (Fin m₂)} {α : ℝ} {x : EuclideanSpace 𝕜 (Fin n)} :
    IsLSQISolution A b B d α x ↔
      IsLSQISolution (star U₁ * A * X) (toEuclideanLin (star U₁) b) (star U₂ * B * X)
        (toEuclideanLin (star U₂) d) α (toEuclideanLin X⁻¹ x) := by
  rw [isLSQISolution_unitary_mul_mul_iff h.mem_unitaryGroup_left₁ h.mem_unitaryGroup_left₂
      h.isUnit,
    ← toEuclideanLin_mul_apply,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det X).1 h.isUnit), toEuclideanLin_one_apply]

end GSVD

section GSVDLSE

/-- The coefficients of the LSE solution in GSVD coordinates ([golub2013matrix] (6.2.12), in
Theorem 6.1.1's block order): `b̃_i` on the first `n − p` columns (pure `A`, `α_i = 1`), and
`d̃_{i − (n − p)} / β_i` on the last `p`. -/
noncomputable def lseGSVDCoeff {m₁ p n : ℕ} (hnm : n ≤ m₁) (bt : Fin m₁ → 𝕜) (dt : Fin p → 𝕜)
    (β : ℕ → ℝ) (i : Fin n) : 𝕜 :=
  if h : (i : ℕ) < n - p then bt ⟨i, lt_of_lt_of_le i.isLt hnm⟩
  else dt ⟨(i : ℕ) - (n - p), by have := i.isLt; omega⟩ / (β i : 𝕜)

variable {m₁ p n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin p) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin p) (Fin p) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α β : ℕ → ℝ}

/-- `∑ yᵢ xᵢ = X y` over the columns `xᵢ` of `X` (`Matrix.mulVec_eq_sum`). -/
private theorem sum_smul_col_eq_mulVec {n : ℕ} (X : Matrix (Fin n) (Fin n) 𝕜) (y : Fin n → 𝕜) :
    ∑ i, y i • X.col i = X *ᵥ y := by
  simp only [mulVec_eq_sum, op_smul_eq_smul]
  rfl

/-- **LSE through the GSVD** ([golub2013matrix] (6.2.12), restated in Theorem 6.1.1's block
order): if `B` has full row rank, `ker A ⊓ ker B = ⊥` and `U₁ᴴ A X = D_A`, `U₂ᴴ B X = D_B` is a
GSVD, then `x = ∑_{i < n−p} b̃_i x_i + ∑_{n−p ≤ i < n} (d̃_{i−(n−p)} / β_i) x_i` solves LSE, with
`b̃ = U₁ᴴ b`, `d̃ = U₂ᴴ d`, `x_i` the columns of `X` (`Matrix.lseGSVDCoeff`); it is the unique
solution (`Matrix.IsLSESolution.eq_of_ker_inf_ker_eq_bot`). The book's
`∑_{i ≤ m₂} (d̃_i/β_i) x_i + ∑_{i > m₂} (b̃_i/α_i) x_i` is the third edition's block order; here
the pure-`A` columns have `α_i = 1`. In GSVD coordinates the constraint fixes the coordinates on
the mixed columns and the objective is minimized by `y_i = b̃_i` on the pure ones. -/
theorem isLSESolution_sum_of_isGSVD (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁)
    (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace 𝕜 (Fin m₁)) (d : EuclideanSpace 𝕜 (Fin p)) :
    IsLSESolution A b B d (WithLp.toLp 2 (∑ i : Fin n,
      lseGSVDCoeff hnm (toEuclideanLin (star U₁) b) (toEuclideanLin (star U₂) d) β i •
        X.col i)) := by
  classical
  obtain ⟨hrn, hpn, hβ⟩ := h.rank_eq_and_ne_zero hB hAB
  set bt := toEuclideanLin (star U₁) b with hbt
  set dt := toEuclideanLin (star U₂) d with hdt
  set y : Fin n → 𝕜 := lseGSVDCoeff hnm bt dt β with hy
  rw [sum_smul_col_eq_mulVec, ← toEuclideanLin_toLp, ← isLSQISolution_zero_iff,
    ← isLSQISolution_unitary_mul_mul_iff h.mem_unitaryGroup_left₁ h.mem_unitaryGroup_left₂
      h.isUnit, isLSQISolution_zero_iff, h.star_mul_mul₁, h.star_mul_mul₂, hrn]
  have hpure : ∀ i : Fin n, (i : ℕ) < n - p → α i = 1 := fun i hi =>
    (h.eq_one_and_eq_zero_of_lt i (by rw [hrn]; exact hi)).1
  -- the constraint in coordinates
  have hfeas : ∀ y' : Fin n → 𝕜,
      toEuclideanLin (shiftedRectDiagonal (n - p) fun i => ((β i : ℝ) : 𝕜)) (WithLp.toLp 2 y')
        = dt ↔ ∀ j : Fin n, n - p ≤ (j : ℕ) → y' j = y j := by
    intro y'
    constructor
    · intro hc j hj
      have hjl := j.isLt
      obtain ⟨k, hkdef⟩ : ∃ k : Fin p, (k : ℕ) = j - (n - p) := ⟨⟨j - (n - p), by omega⟩, rfl⟩
      have hk : (k : ℕ) + (n - p) < n := by omega
      have hkj : (⟨(k : ℕ) + (n - p), hk⟩ : Fin n) = j := Fin.ext (by simp only; omega)
      have hkj' : (k : ℕ) + (n - p) = j := by omega
      have := congrArg (fun v : EuclideanSpace 𝕜 (Fin p) => WithLp.ofLp v k) hc
      simp only [ofLp_toEuclideanLin,] at this
      rw [shiftedRectDiagonal_mulVec _ _ _ _ hk, hkj, hkj'] at this
      have hnlt : ¬ (j : ℕ) < n - p := by omega
      simp only [hy, lseGSVDCoeff, hnlt, ↓reduceDIte]
      rw [eq_div_iff (RCLike.ofReal_ne_zero.2 (hβ j hj)), mul_comm, this]
      exact congrArg (fun i => WithLp.ofLp dt i) (Fin.ext (by simp only; omega))
    · intro hc
      ext k
      have hk : (k : ℕ) + (n - p) < n := by have := k.isLt; omega
      simp only [ofLp_toEuclideanLin]
      rw [shiftedRectDiagonal_mulVec _ _ _ _ hk, hc _ (Nat.le_add_left _ _)]
      have hnlt : ¬ ((k : ℕ) + (n - p) < n - p) := by omega
      simp only [hy, lseGSVDCoeff, hnlt, ↓reduceDIte]
      rw [mul_div_cancel₀ _
        (RCLike.ofReal_ne_zero.2 (hβ ⟨(k : ℕ) + (n - p), hk⟩ (Nat.le_add_left _ _)))]
      exact congrArg (fun i => WithLp.ofLp dt i) (Fin.ext (by simp only; omega))
  refine ⟨(hfeas y).2 fun _ _ => rfl, fun y' hy' => ?_⟩
  have hy'' := (hfeas (WithLp.ofLp y')).1 (by rwa [WithLp.toLp_ofLp])
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [PiLp.sub_apply, ofLp_toEuclideanLin]
  by_cases hin : (i : ℕ) < n
  · rw [rectDiagonal_mulVec _ _ _ hin, rectDiagonal_mulVec _ _ _ hin]
    by_cases hip : (i : ℕ) < n - p
    · have : y ⟨i, hin⟩ = (star U₁ *ᵥ WithLp.ofLp b) i := by
        simp only [hy, lseGSVDCoeff, hip, ↓reduceDIte]
        rfl
      rw [hpure ⟨i, hin⟩ hip, RCLike.ofReal_one, one_mul, one_mul, this, sub_self, norm_zero]
      exact le_trans (zero_pow two_ne_zero).le (sq_nonneg _)
    · rw [hy'' ⟨i, hin⟩ (by simp only; omega)]
  · rw [rectDiagonal_mulVec_of_le _ _ _ (not_lt.1 hin),
      rectDiagonal_mulVec_of_le _ _ _ (not_lt.1 hin)]

/-- **The method of weighting** ([golub2013matrix] §6.2.6): the solution
`(AᴴA + λBᴴB)⁻¹(Aᴴb + λBᴴd)` of the stacked least-squares problem (6.2.13),
`min ‖Ax − b‖² + λ‖Bx − d‖²` (`Matrix.isLeastSquaresSolution_fromRows_iff`). -/
noncomputable def penaltyLSE {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] [DecidableEq n]
    [DecidableEq m] [DecidableEq q] (A : Matrix m n 𝕜) (B : Matrix q n 𝕜)
    (b : EuclideanSpace 𝕜 m) (d : EuclideanSpace 𝕜 q) (μ : ℝ) : EuclideanSpace 𝕜 n :=
  toEuclideanLin (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B))⁻¹
    (toEuclideanLin Aᴴ b + (μ : 𝕜) • toEuclideanLin Bᴴ d)

/-- The coefficients of the error of the method of weighting in GSVD coordinates
([golub2013matrix] (6.2.14), corrected): `0` on the first `n − p` columns and
`α_i (β_i b̃_i − α_i d̃_{i−(n−p)}) / (β_i (α_i² + λ β_i²))` on the last `p`. -/
noncomputable def penaltyGSVDCoeff {m₁ p n : ℕ} (hnm : n ≤ m₁) (bt : Fin m₁ → 𝕜) (dt : Fin p → 𝕜)
    (α β : ℕ → ℝ) (μ : ℝ) (i : Fin n) : 𝕜 :=
  if h : (i : ℕ) < n - p then 0
  else (α i : 𝕜) * ((β i : 𝕜) * bt ⟨i, lt_of_lt_of_le i.isLt hnm⟩
      - (α i : 𝕜) * dt ⟨(i : ℕ) - (n - p), by have := i.isLt; omega⟩)
    / ((β i : 𝕜) * ((α i : 𝕜) ^ 2 + (μ : 𝕜) * (β i : 𝕜) ^ 2))

/-- **The error of the method of weighting** ([golub2013matrix] (6.2.14), corrected): in the
setting of `Matrix.isLSESolution_sum_of_isGSVD`, for `0 < λ`,
`x(λ) − x = ∑_{n−p ≤ i < n} α_i (β_i b̃_i − α_i d̃_{i−(n−p)}) / (β_i (α_i² + λ β_i²)) x_i`
(`Matrix.penaltyGSVDCoeff`). The book prints `λ²` for `λ`, `u_iᵀb`, `v_iᵀd` for `b̃_i`, `d̃_i`,
and sums to `p` in the third edition's block order. In GSVD coordinates
`y_i(λ) = (α_i b̃_i + λ β_i d̃_{i−(n−p)}) / (α_i² + λβ_i²)` on the mixed columns and `b̃_i` on the
pure ones (`Matrix.IsGSVD.inv_gram_add_smul_gram_eq`). -/
theorem penaltyLSE_sub_eq_sum_of_isGSVD (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁)
    (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace 𝕜 (Fin m₁)) (d : EuclideanSpace 𝕜 (Fin p)) {μ : ℝ} (hμ : 0 < μ) :
    penaltyLSE A B b d μ - WithLp.toLp 2 (∑ i : Fin n,
        lseGSVDCoeff hnm (toEuclideanLin (star U₁) b) (toEuclideanLin (star U₂) d) β i • X.col i)
      = WithLp.toLp 2 (∑ i : Fin n, penaltyGSVDCoeff hnm (toEuclideanLin (star U₁) b)
          (toEuclideanLin (star U₂) d) α β μ i • X.col i) := by
  classical
  obtain ⟨hrn, hpn, hβ⟩ := h.rank_eq_and_ne_zero hB hAB
  set bt := toEuclideanLin (star U₁) b with hbt
  set dt := toEuclideanLin (star U₂) d with hdt
  have hpure : ∀ i : Fin n, (i : ℕ) < n - p → α i = 1 ∧ β i = 0 := fun i hi =>
    h.eq_one_and_eq_zero_of_lt i (by rw [hrn]; exact hi)
  have hd0 : ∀ i : Fin n, α i ^ 2 + μ * β i ^ 2 ≠ 0 := fun i =>
    h.sq_add_smul_sq_ne_zero hμ (by rw [hrn]; exact i.isLt)
  have hXB := h.conjTranspose_mul_conjTranspose_right
  rw [hrn] at hXB
  rw [penaltyLSE, h.inv_gram_add_smul_gram_eq hnm μ hd0, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, map_add, map_smul, ← toEuclideanLin_mul_apply Xᴴ,
    h.conjTranspose_mul_conjTranspose_left,
    ← toEuclideanLin_mul_apply Xᴴ, hXB, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    sum_smul_col_eq_mulVec, sum_smul_col_eq_mulVec, toEuclideanLin_apply, ← WithLp.toLp_sub,
    ← mulVec_sub]
  congr 2
  funext i
  simp only [Pi.sub_apply, WithLp.ofLp_add, WithLp.ofLp_smul, ofLp_toEuclideanLin,
    mulVec_diagonal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    rectDiagonal_mulVec _ _ _ (lt_of_lt_of_le i.isLt hnm),
    conjTranspose_shiftedRectDiagonal_mulVec, lseGSVDCoeff, penaltyGSVDCoeff, ← hbt, ← hdt]
  by_cases hi : (i : ℕ) < n - p
  · obtain ⟨hα1, hβ0⟩ := hpure i hi
    have hn : ¬ (n - p ≤ (i : ℕ) ∧ (i : ℕ) - (n - p) < p) := fun hh => by omega
    simp [hi, hα1, hβ0]
  · have hn : n - p ≤ (i : ℕ) ∧ (i : ℕ) - (n - p) < p := ⟨by omega, by have := i.isLt; omega⟩
    simp only [hn, hi, and_self, ↓reduceDIte, ↓reduceDIte]
    have hb : ((β i : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (hβ i (by omega))
    have hd : ((α i : ℝ) : 𝕜) ^ 2 + (μ : 𝕜) * ((β i : ℝ) : 𝕜) ^ 2 ≠ 0 := by
      have := RCLike.ofReal_ne_zero (K := 𝕜).2 (hd0 i)
      push_cast at this
      exact this
    push_cast
    simp only [RCLike.star_def, RCLike.conj_ofReal]
    field_simp
    ring

/-- **The method of weighting converges** ([golub2013matrix] §6.2.6, "`x(λ) → x` as `λ → ∞`"):
if `n ≤ m₁`, `B` has full row rank, `ker A ⊓ ker B = ⊥` and `x` solves LSE, then
`penaltyLSE A B b d λ → x`. From a GSVD (`Matrix.exists_isGSVD`), `x` is the solution of
`Matrix.isLSESolution_sum_of_isGSVD`, and the coefficients of
`Matrix.penaltyLSE_sub_eq_sum_of_isGSVD` are `O(1/λ)`. -/
theorem tendsto_penaltyLSE (hnm : n ≤ m₁) (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {b : EuclideanSpace 𝕜 (Fin m₁)} {d : EuclideanSpace 𝕜 (Fin p)} {x : EuclideanSpace 𝕜 (Fin n)}
    (hx : IsLSESolution A b B d x) : Tendsto (penaltyLSE A B b d) atTop (𝓝 x) := by
  classical
  obtain ⟨U₁, U₂, X, α, β, h⟩ := exists_isGSVD hnm A B
  obtain ⟨hrn, hpn, hβ⟩ := h.rank_eq_and_ne_zero hB hAB
  have hx' := (isLSESolution_sum_of_isGSVD h hnm hB hAB b d).eq_of_ker_inf_ker_eq_bot hx hAB
  set bt := toEuclideanLin (star U₁) b
  set dt := toEuclideanLin (star U₂) d
  have hc : ∀ i : Fin n, Tendsto (fun μ : ℝ => penaltyGSVDCoeff hnm bt dt α β μ i) atTop (𝓝 0) := by
    intro i
    by_cases hi : (i : ℕ) < n - p
    · simp only [penaltyGSVDCoeff, hi, ↓reduceDIte]
      exact tendsto_const_nhds
    · simp only [penaltyGSVDCoeff, hi, ↓reduceDIte]
      have hb : 0 < β i := lt_of_le_of_ne (h.nonneg i).2 (hβ i (by omega)).symm
      have hr : Tendsto (fun μ : ℝ => ((β i * (α i ^ 2 + μ * β i ^ 2))⁻¹ : ℝ)) atTop (𝓝 0) := by
        refine Tendsto.inv_tendsto_atTop (Tendsto.const_mul_atTop (by positivity) ?_)
        exact tendsto_atTop_add_const_left _ _
          (Tendsto.atTop_mul_const (by positivity) tendsto_id)
      have hr' := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 0).comp hr
      rw [RCLike.ofReal_zero] at hr'
      have := hr'.const_mul ((α i : 𝕜) * ((β i : 𝕜) * bt ⟨i, lt_of_lt_of_le i.isLt hnm⟩
        - (α i : 𝕜) * dt ⟨i - (n - p), by have := i.isLt; omega⟩))
      rw [mul_zero] at this
      refine this.congr fun μ => ?_
      simp only [Function.comp_apply]
      push_cast
      rw [div_eq_mul_inv]
  have hsum : Tendsto (fun μ : ℝ => WithLp.toLp 2 (∑ i : Fin n,
      penaltyGSVDCoeff hnm bt dt α β μ i • X.col i) : ℝ → EuclideanSpace 𝕜 (Fin n)) atTop
        (𝓝 0) := by
    have : Tendsto (fun μ : ℝ => ∑ i : Fin n, penaltyGSVDCoeff hnm bt dt α β μ i • X.col i)
        atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ =>
        (hc i).smul_const (X.col i)
      simpa using this
    have hc' := ((PiLp.continuous_toLp 2 _).tendsto 0).comp this
    rw [WithLp.toLp_zero] at hc'
    exact hc'
  have := hsum.const_add x
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with μ hμ
  rw [← penaltyLSE_sub_eq_sum_of_isGSVD h hnm hB hAB b d hμ, ← hx']
  abel

end GSVDLSE

end Matrix
