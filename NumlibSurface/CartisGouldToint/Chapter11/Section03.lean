/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter08.Section03
import NumlibSurface.CartisGouldToint.Chapter11.Section01

/-!
# Cartis, Gould and Toint, Section 11.3: Least-squares models

This module formalizes §11.3 of [cartis2022evaluation]: subproblems whose model comes from a linear
least-squares problem. For $J \in \mathbb{R}^{m \times n}$ and a residual $r \in \mathbb{R}^m$, the
model (11.3.1)
$$\tfrac12 \|r + J s\|^2 = \tfrac12 \langle r, r \rangle + \langle J^T r, s \rangle + \tfrac12
  \langle s, J^T J s \rangle$$
is the quadratic model of Chapter 8 with the data $g = J^T r$ and $H = J^T J$, up to a constant.
Since $J^T J$ is positive semidefinite, $\lambda_{\mathrm{s}} = 0$, and since $J^T r$ lies in the
range of $J^T J$, the hard case cannot occur: a positive multiplier makes $J^T J + \lambda M$
positive definite and is the unique root of the secular equation. The shifted system
$(J^T J + \lambda M) s = -J^T r$ is equivalent to the augmented system (11.3.3). The proofs use the
subproblem theory of Chapter 8.

## Main results

* (11.3.1)–(11.3.2), `CartisGouldToint.Chapter11.leastSquares_structure`: the identity (11.3.1),
  $\lambda_{\mathrm{s}} = 0$, and the absence of the hard case for the trust-region and the
  regularization subproblems, as listed in §11.3.
* (11.3.3), `CartisGouldToint.Chapter11.augmentedSystem_iff`: the shifted system is equivalent to
  the augmented system.

## Implementation notes

* The source uses $r$ both for the residual vector and for the order of the regularization. Here the
  residual is $r$ and the order of the regularization is $p$.

## Not formalized

* The remarks on Krylov and LSQR methods in §11.3.
-/

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter11

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter10

variable {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

/-- For every $J \in \mathbb{R}^{m \times n}$, the matrix $J^T J$ is positive semidefinite. -/
theorem transpose_mul_self_posSemidef (J : Matrix (Fin m) (Fin n) ℝ) : (Jᵀ * J).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self J

/-- For $J \in \mathbb{R}^{m \times n}$ and $r \in \mathbb{R}^m$, the vector $J^T r$ lies in the
range of $J^T J$: if $J x_0$ is the orthogonal projection of $r$ onto the range of $J$, then
$J^T (r - J x_0) = 0$. -/
private theorem exists_transpose_mul_self_eq (J : Matrix (Fin m) (Fin n) ℝ)
    (r : EuclideanSpace ℝ (Fin m)) :
    ∃ x, toEuclideanLin (Jᵀ * J) x = toEuclideanLin Jᵀ r := by
  set K := LinearMap.range (toEuclideanLin J)
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (K.starProjection_apply_mem r)
  refine ⟨x, ?_⟩
  have horth : r - K.starProjection r ∈ Kᗮ := K.sub_starProjection_mem_orthogonal r
  rw [toEuclideanLin_mul_apply, hx, ← sub_eq_zero, ← map_sub]
  rw [← inner_self_eq_zero (𝕜 := ℝ), ← toEuclideanLin_transpose_inner_right]
  rw [← neg_sub, map_neg, inner_neg_left, neg_eq_zero]
  exact (Submodule.mem_orthogonal' _ _).1 horth _ (LinearMap.mem_range_self _ _)

/-- **Section 11.3** of [cartis2022evaluation], least-squares models. Let
$J \in \mathbb{R}^{m \times n}$, $r \in \mathbb{R}^m$ and let $M \in \mathbb{R}^{n \times n}$ be
positive definite. Take $g = J^T r$ and $H = J^T J$, and let $m(s) = \langle g, s \rangle +
\frac12 \langle s, H s \rangle$ be the model (8.1.1).

1. For every $s$, $\frac12 \|r + J s\|^2 = \frac12 \langle r, r \rangle + m(s)$ (11.3.1).
2. For every $\lambda \ge 0$, $J^T J + \lambda M$ is positive semidefinite.
3. The leftmost eigenvalue of the pencil $(J^T J, M)$ satisfies $\lambda_1 \ge 0$, and
   $\lambda_{\mathrm{s}} = \max(0, -\lambda_1) = 0$.
4. $J^T r$ lies in the range of $J^T J$. So $(J^T J) s = -J^T r$ is solvable, and an interior
   trust-region solution with $\lambda_* = 0$ is possible.
5. Let $\Delta > 0$, and let $\lambda$ be a Lagrange multiplier of a step $s$ for the
   trust-region subproblem (8.1.2), in the sense of Theorem 8.2.7. Then either $\lambda = 0$, or
   $\lambda > 0$, $J^T J + \lambda M$ is positive definite, $s = s(\lambda)$, and $\lambda$ is
   the unique root on $(0, \infty)$ of $\pi(\lambda) = \Delta^2$.
6. Let $\sigma > 0$, $p > 2$ and $J^T r \neq 0$, and let $s$ be a global minimizer of the
   regularization subproblem (8.1.3) of order $p$. Then the multiplier
   $\lambda_* = \sigma \|s\|_M^{p-2}$ is positive, $J^T J + \lambda_* M$ is positive definite,
   $s = s(\lambda_*)$, and $\lambda_*$ is the unique root on $(0, \infty)$ of the secular
   equation $\pi(\lambda) = (\lambda/\sigma)^{2/(p-2)}$.

Here $s(\lambda) = -(H + \lambda M)^{-1} g$ is `CartisGouldToint.Chapter08.stepOf`,
$\pi(\lambda) = \|s(\lambda)\|_M^2$ is `CartisGouldToint.Chapter08.secularFn`, and $\lambda_1$
and $\lambda_{\mathrm{s}}$ are `CartisGouldToint.Chapter08.leftmostPencil` and
`CartisGouldToint.Chapter08.lambdaS`. Part 5 is the absence of the hard case for the
trust-region subproblem, and part 6 for the regularization subproblem. -/
theorem leastSquares_structure (J : Matrix (Fin m) (Fin n) ℝ) (r : EuclideanSpace ℝ (Fin m))
    (hM : M.PosDef) :
    (∀ s, 1 / 2 * ‖r + toEuclideanLin J s‖ ^ 2 =
      1 / 2 * ⟪r, r⟫ + model (toEuclideanLin Jᵀ r) (Jᵀ * J) s) ∧
    (∀ lam : ℝ, 0 ≤ lam → (Jᵀ * J + lam • M).PosSemidef) ∧
    (0 ≤ leftmostPencil (transpose_mul_self_posSemidef J).isHermitian hM ∧
      lambdaS (transpose_mul_self_posSemidef J).isHermitian hM = 0) ∧
    (∃ x, toEuclideanLin (Jᵀ * J) x = toEuclideanLin Jᵀ r) ∧
    (∀ {Δ lam : ℝ} {s : EuclideanSpace ℝ (Fin n)}, 0 < Δ →
      IsTrustRegionKKT (toEuclideanLin Jᵀ r) (Jᵀ * J) M Δ s lam →
      lam = 0 ∨ (0 < lam ∧ (Jᵀ * J + lam • M).PosDef ∧
        s = stepOf (toEuclideanLin Jᵀ r) (Jᵀ * J) M lam ∧
        secularFn (toEuclideanLin Jᵀ r) (Jᵀ * J) M lam = Δ ^ 2 ∧
        ∀ μ, 0 < μ → secularFn (toEuclideanLin Jᵀ r) (Jᵀ * J) M μ = Δ ^ 2 → μ = lam)) ∧
    (∀ {σ p : ℝ} {s : EuclideanSpace ℝ (Fin n)}, 0 < σ → 2 < p → toEuclideanLin Jᵀ r ≠ 0 →
      IsRegularizationSolution (toEuclideanLin Jᵀ r) (Jᵀ * J) M σ p s →
      0 < σ * mNorm M s ^ (p - 2) ∧ (Jᵀ * J + (σ * mNorm M s ^ (p - 2)) • M).PosDef ∧
        s = stepOf (toEuclideanLin Jᵀ r) (Jᵀ * J) M (σ * mNorm M s ^ (p - 2)) ∧
        secularFn (toEuclideanLin Jᵀ r) (Jᵀ * J) M (σ * mNorm M s ^ (p - 2)) =
          regTarget σ p (σ * mNorm M s ^ (p - 2)) ∧
        ∀ μ, 0 < μ → secularFn (toEuclideanLin Jᵀ r) (Jᵀ * J) M μ = regTarget σ p μ →
          μ = σ * mNorm M s ^ (p - 2)) := by
  have hJ := transpose_mul_self_posSemidef J
  have hH := hJ.isHermitian
  set g := toEuclideanLin Jᵀ r
  have hpsd : ∀ lam : ℝ, 0 ≤ lam → (Jᵀ * J + lam • M).PosSemidef := fun lam hl =>
    hJ.add (hM.posSemidef.smul hl)
  have hpd : ∀ lam : ℝ, 0 < lam → (Jᵀ * J + lam • M).PosDef := fun lam hl =>
    Matrix.PosDef.posSemidef_add hJ (hM.smul hl)
  -- the step is `s(λ)` when `H + λ M` is positive definite
  have hstep : ∀ {lam : ℝ} {s : EuclideanSpace ℝ (Fin n)}, (Jᵀ * J + lam • M).PosDef →
      toEuclideanLin (Jᵀ * J + lam • M) s = -g → s = stepOf g (Jᵀ * J) M lam := by
    intro lam s hP h
    rw [stepOf_def, ← h, toEuclideanLin_nonsing_inv_mul_apply hP.isUnit]
  have hl₁ : 0 ≤ leftmostPencil hH hM := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · have : IsEmpty (Fin (Fintype.card (Fin n))) := by rw [Fintype.card_fin]; exact hn
      rw [leftmostPencil, Real.iInf_of_isEmpty]
    · rw [leftmostPencil_eq]
      have := ((posDef_add_smul_iff_scaled (hM := hM) hH 0).1).1 (by simpa using hJ)
      linarith
  have hS : lambdaS hH hM = 0 := by rw [lambdaS_def]; exact max_eq_left (by linarith)
  -- the secular function is strictly decreasing on `(0, ∞)` when `g ≠ 0`
  have hA : g ≠ 0 → ∀ a b : ℝ, 0 < a → a < b →
      secularFn g (Jᵀ * J) M b < secularFn g (Jᵀ * J) M a := fun hg a b ha hab => by
    have hanti := ((corollary_8_2_4 hH hM hg 1).1 one_pos).1
    rw [hS] at hanti
    have := hanti (mem_Ioi.2 ha) (mem_Ioi.2 (ha.trans hab)) hab
    simpa only [Real.rpow_one] using this
  refine ⟨fun s => ?_, hpsd, ⟨hl₁, by rw [lambdaS_def]; exact max_eq_left (by linarith)⟩,
    exists_transpose_mul_self_eq J r, fun {Δ lam s} hΔ hk => ?_,
    fun {σ p s} hσ hp hg hs => ?_⟩
  · rw [model_def, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      toEuclideanLin_mul_apply, toEuclideanLin_transpose_inner_left,
      toEuclideanLin_transpose_inner_right, real_inner_comm (toEuclideanLin J s) r]
    ring
  · rcases eq_or_lt_of_le hk.nonneg with h | h
    · exact Or.inl h.symm
    · have hsec : secularFn g (Jᵀ * J) M lam = Δ ^ 2 := by
        rw [← mNorm_stepOf_sq hM, ← hstep (hpd lam h) hk.shifted]
        have := (mul_eq_zero.1 hk.complementarity).resolve_left h.ne'
        linarith
      have hg : g ≠ 0 := by
        intro hg0
        have : secularFn g (Jᵀ * J) M lam = 0 := by
          rw [secularFn_def, stepOf_def, hg0, neg_zero, map_zero, inner_zero_left]
        nlinarith
      refine Or.inr ⟨h, hpd lam h, hstep (hpd lam h) hk.shifted, hsec, fun μ hμ hμr => ?_⟩
      rcases lt_trichotomy μ lam with h' | h' | h'
      · have := hA hg μ lam hμ h'; linarith
      · exact h'
      · have := hA hg lam μ h h'; linarith
  · obtain ⟨h1, -, -⟩ := theorem_8_2_8 hH hM hσ hp hs
    set lam := σ * mNorm M s ^ (p - 2) with hlamdef
    have hs0 : s ≠ 0 := by
      rintro rfl; apply hg; rw [map_zero, eq_comm, neg_eq_zero] at h1; exact h1
    have hlpos : 0 < lam := by
      have : 0 < mNorm M s := by
        rw [mNorm_eq_norm_toScaled hM]
        exact norm_pos_iff.2 fun h => hs0 ((toScaled hM).map_eq_zero_iff.1 h)
      exact mul_pos hσ (Real.rpow_pos_of_pos this _)
    have hseq := hstep (hpd lam hlpos) h1
    have hsec : secularFn g (Jᵀ * J) M lam = regTarget σ p lam := by
      rw [← mNorm_stepOf_sq hM, ← hseq]
      exact (regTarget_of_eq_mul_rpow hσ hp (mNorm_nonneg _ _) hlamdef).symm
    refine ⟨hlpos, hpd lam hlpos, hseq, hsec, fun μ hμ hμr => ?_⟩
    have hT : ∀ a b : ℝ, 0 < a → a < b → regTarget σ p a < regTarget σ p b :=
      fun a b ha hab => Real.rpow_lt_rpow (div_pos ha hσ).le (div_lt_div_of_pos_right hab hσ)
        (div_pos two_pos (by linarith))
    rcases lt_trichotomy μ lam with h | h | h
    · have := hA hg μ lam hμ h; have := hT μ lam hμ h; linarith
    · exact h
    · have := hA hg lam μ hlpos h; have := hT lam μ hlpos h; linarith

/-- **Equation (11.3.3)** of [cartis2022evaluation], the augmented system. Let
$J \in \mathbb{R}^{m \times n}$, $r \in \mathbb{R}^m$, $M \in \mathbb{R}^{n \times n}$,
$\lambda \in \mathbb{R}$ and $s \in \mathbb{R}^n$. Then $(J^T J + \lambda M) s = -J^T r$ if and
only if there is $z \in \mathbb{R}^m$ with
$$\begin{bmatrix} \lambda M & J^T \\ J & -I \end{bmatrix} \begin{bmatrix} s \\ z \end{bmatrix} =
  -\begin{bmatrix} 0 \\ r \end{bmatrix}.$$
The vector $z$ is then $z = J s + r$.

The block matrix is `Matrix.fromBlocks`, indexed by `Fin n ⊕ Fin m`. -/
theorem augmentedSystem_iff (J : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (s : Fin n → ℝ) :
    (Jᵀ * J + lam • M) *ᵥ s = -(Jᵀ *ᵥ r) ↔
      ∃ z : Fin m → ℝ,
        fromBlocks (lam • M) Jᵀ J (-1) *ᵥ Sum.elim s z = -Sum.elim (0 : Fin n → ℝ) r := by
  have e : ∀ z, (lam • M) *ᵥ s + Jᵀ *ᵥ z =
      (Jᵀ * J + lam • M) *ᵥ s + Jᵀ *ᵥ r + Jᵀ *ᵥ (z - (J *ᵥ s + r)) := fun z => by
    rw [add_mulVec, mulVec_sub, mulVec_add, ← mulVec_mulVec]; abel
  simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, neg_mulVec, one_mulVec]
  constructor
  · intro h
    refine ⟨J *ᵥ s + r, ?_⟩
    rw [e, h, sub_self, mulVec_zero, neg_add_cancel, add_zero,
      show J *ᵥ s + -(J *ᵥ s + r) = -r by abel]
    ext (i | i) <;> simp
  · rintro ⟨z, hz⟩
    have hl : (lam • M) *ᵥ s + Jᵀ *ᵥ z = 0 :=
      funext fun i => by simpa using congrFun hz (Sum.inl i)
    have hr : J *ᵥ s + -z = -r := funext fun i => by simpa using congrFun hz (Sum.inr i)
    have hz' : z - (J *ᵥ s + r) = 0 := funext fun i => by
      have := congrFun hr i
      simp only [Pi.add_apply, Pi.neg_apply] at this
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
      linarith
    rw [e, hz', mulVec_zero, add_zero] at hl
    exact eq_neg_of_add_eq_zero_left hl

end CartisGouldToint.Chapter11
