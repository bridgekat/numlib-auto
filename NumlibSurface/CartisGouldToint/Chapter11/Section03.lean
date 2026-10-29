import NumlibSurface.CartisGouldToint.Chapter08.Section03
import NumlibSurface.CartisGouldToint.Chapter11.Section01

/-!
# Cartis–Gould–Toint §11.3: Least-squares models

Surface file for [cartis2022evaluation] §11.3: the least-squares model
`m(s) = ½ ‖r + J s‖²` (11.3.1), i.e. the data `g = Jᵀ r`, `H = Jᵀ J`, for which `λₛ = 0` and the
hard case cannot occur, and the augmented system (11.3.3). The remarks on Krylov and LSQR
methods are not formalized.

## Main results

* `leastSquares_structure` — (11.3.1)–(11.3.2) and the consequences listed in §11.3.
* `augmentedSystem_iff` — (11.3.3).

## Implementation notes

The book uses `r` both for the residual vector and for the regularization order; here the
residual is `r` and the regularization order is `p`.
-/

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter11

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter10

variable {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

/-- `Jᵀ J` is positive semidefinite. -/
theorem transpose_mul_self_posSemidef (J : Matrix (Fin m) (Fin n) ℝ) : (Jᵀ * J).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self J

/-- `Jᵀ r` lies in the range of `Jᵀ J`: with `J x₀` the orthogonal projection of `r` onto the
range of `J`, `Jᵀ (r - J x₀) = 0`. -/
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

/-- **Least-squares models** ([cartis2022evaluation] §11.3). Let `J ∈ ℝ^{m×n}`, `r ∈ ℝᵐ`, `M`
positive definite, `g = Jᵀ r`, `H = Jᵀ J`. Then:
(i) `½ ‖r + J s‖² = ½ ⟪r, r⟫ + ⟪Jᵀ r, s⟫ + ½ ⟪s, Jᵀ J s⟫` (11.3.1);
(ii) `Jᵀ J + λ M` is positive semidefinite for `λ ≥ 0`, so `λ₁ ≥ 0` and `λₛ = 0`;
(iii) `Jᵀ r` lies in the range of `Jᵀ J` (so `(Jᵀ J) s = -Jᵀ r` is solvable and an interior
trust-region solution with `λ* = 0` is possible), and the hard case cannot occur: a multiplier
`λ*` of the trust-region subproblem is either `0` or positive, and then `Jᵀ J + λ* M` is positive
definite, `s* = s(λ*)` and `λ*` is the unique root on `(0, ∞)` of `π(λ) = Δ²`; and if
`Jᵀ r ≠ 0`, the regularization
multiplier `λ* = σ ‖s*‖_M^{p-2}` is positive, `Jᵀ J + λ* M` is positive definite, `s* = s(λ*)`, and
`λ*` is the unique root on `(0, ∞)` of the secular equation `π(λ) = (λ/σ)^{2/(p-2)}`. -/
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

/-- **The augmented system** ([cartis2022evaluation] (11.3.3)): `(Jᵀ J + λ M) s = -Jᵀ r` iff there
is `z` (namely `z = J s + r`) with `[[λ M, Jᵀ], [J, -I]] [s; z] = -[0; r]`. -/
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
