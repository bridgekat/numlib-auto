import Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section01

/-!
# Golub–Van Loan §6.2: constrained least squares

Surface file for [golub2013matrix] §6.2: least squares over a sphere ((6.2.1)–(6.2.4) and
Algorithm 6.2.1), over an ellipsoid through the GSVD ((6.2.5)–(6.2.8)), with linear equality
constraints (the LSE problem (6.2.9)) through the QR factorization of `Bᵀ` (the derivation of
Algorithm 6.2.2), the augmented system (6.2.10), the GSVD ((6.2.11)–(6.2.12)) and weighting
((6.2.13)–(6.2.14)).

## Conventions

Real matrices, 0-based, vectors of least-squares statements in `EuclideanSpace ℝ (Fin n)` acting
through `Matrix.toEuclideanLin`; the book's parameter `λ` is written `μ`. The LSQI problem
`min ‖Ax − b‖₂` subject to `‖Bx − d‖₂ ≤ α` is the backbone's `Matrix.IsLSQISolution A b B d α`, the
sphere problem (6.2.1) its instance `IsSphereLSQISolution A b α` at `B = I`, `d = 0`; the LSE
problem is `Matrix.IsLSESolution A b B d`. An SVD is a factorization `Matrix.IsSVD A U σ V`; its
sums run over
`i < min(m, n)`, the terms with `σ_i = 0` (those past the rank) vanishing. A GSVD is
`Matrix.IsGSVD A B U₁ U₂ X α β` in Theorem 6.1.1's block order.

Algorithm 6.2.1 follows the algorithm conventions of `NumlibSurface/GolubVanLoan`: every arithmetic
result passes through the rounding hook `rnd`; "Compute the SVD" and "Find `λ₊ > 0` such that …"
are monadic parameters `svd` and `root` (the book's SVD algorithm is Chapter 8's, and no root finder
is named), and the specification assumes their specifications. The gaxpy `b̃ = Uᵀb` is chapter 1's
Algorithm 1.1.3 and each `x ← x + c v_i` its saxpy Algorithm 1.1.2.

## Not formalized

(6.2.2) (recalls the SVD), (6.2.5) and (6.2.9) (define the problems: the backbone predicates), the
Lagrange-multiplier arguments of §6.2.1, §6.2.2 and §6.2.4 ("can be used … if it exists"), "there
may not be a solution if `rank(B) < m₂`", the numerical precautions of Powell–Reid, the flop counts.

## Errata

* (6.2.6) cites "(6.2.23)" for (6.1.23).
* (6.2.7), (6.2.8), (6.2.12) and (6.2.14) are printed in the third edition's GSVD block order,
  inconsistent with Theorem 6.1.1; the second sum of (6.2.8) (over `d̃_i`, `i = m₂+1 … n₁`) is
  meaningless, and (6.2.14) prints `λ²` for `λ`, `u_iᵀb`, `v_iᵀd` for `b̃_i`, `d̃_i`, and the range
  `1 : p`. They are stated here in Theorem 6.1.1's order, corrected.
* §6.2.1: "`f(0) > 0`" reads `f(0⁺) = ‖x_LS‖² − α²` (`x(λ)` is `x_LS` only in the limit).
* §6.2.3: "if `null(A) ∩ null(B) ≠ {0}` and `d ∈ ran(B)` LSE solution is not unique" is garbled in
  print (`isLSESolution_not_unique`).

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/LeastSquares/{Constrained,Regularized}`,
`Numlib/LinearAlgebra/Matrix/GSVD`; chapter 1's Algorithms 1.1.2–1.1.3; §6.1 of this chapter.
-/

open Matrix Finset Filter Topology

namespace GolubVanLoan.Chapter06

variable {m n : ℕ}

/-! ### §6.2.1 Least squares minimization over a sphere -/

/-- **§6.2.1, the LSQI problem (6.2.1).** "Given `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, and a positive
`α ∈ ℝ`, we consider the problem `min_{‖x‖₂ ≤ α} ‖Ax − b‖₂`": the sphere case `B = I`, `d = 0` of
the backbone's `Matrix.IsLSQISolution`. -/
def IsSphereLSQISolution (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  Matrix.IsLSQISolution A b (1 : Matrix (Fin n) (Fin n) ℝ) 0 α x

/-- **§6.2.1.** "If the unconstrained minimum norm solution `x_LS` satisfies `‖x_LS‖₂ ≤ α`, then it
obviously solves (6.2.1)." -/
theorem isLSQISolution_pinv (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) {α : ℝ}
    (h : ‖toEuclideanLin A.pinv b‖ ≤ α) : IsSphereLSQISolution A b α (toEuclideanLin A.pinv b) := by
  unfold IsSphereLSQISolution
  exact isLSQISolution_of_isLeastSquaresSolution (isLeastSquaresSolution_pinv A b)
    (by rw [toEuclideanLin_one_apply, sub_zero]; exact h)

/-- `⟨u, b⟩ = uᵀb` on real Euclidean space. -/
private theorem inner_toLp_eq_dotProduct (u : Fin m → ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (WithLp.toLp 2 u) b = u ⬝ᵥ WithLp.ofLp b := by
  change inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 (WithLp.ofLp b)) = _
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/-- **(6.2.3).** With an SVD `A = UΣVᵀ` of rank `r`, "`x_LS = ∑_{i=1}^r (u_iᵀb/σ_i) v_i`" and
"`‖x_LS‖₂² = ∑_{i=1}^r (u_iᵀb/σ_i)²`" (the terms with `σ_i = 0` vanish). -/
theorem equation_6_2_3 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (b : EuclideanSpace ℝ (Fin m)) :
    toEuclideanLin A.pinv b = ∑ i : Fin (min m n),
      (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b / σ i) •
        (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace ℝ (Fin n)) ∧
    ‖toEuclideanLin A.pinv b‖ ^ 2 = ∑ i : Fin (min m n),
      (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b / σ i) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [toEuclideanLin_pinv_eq_sum_of_isSVD h b]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, inner_toLp_eq_dotProduct, RCLike.ofReal_real_eq_id, id_eq, inv_mul_eq_div]
  · rw [norm_sq_toEuclideanLin_pinv_eq_sum_of_isSVD h b]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_toLp_eq_dotProduct, div_pow, div_pow, Real.norm_eq_abs, sq_abs]

/-- **§6.2.1.** "Otherwise, `‖x_LS‖₂² = ∑ (u_iᵀb/σ_i)² > α²`, and it follows that the solution to
(6.2.1) is on the boundary of the constraint sphere": if `α² < ‖x_LS‖₂²`, every
solution has `‖x‖₂ = α`. -/
theorem IsSphereLSQISolution.norm_eq {A : Matrix (Fin m) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m)}
    {α : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hLS : α ^ 2 < ‖toEuclideanLin A.pinv b‖ ^ 2) (h : IsSphereLSQISolution A b α x) : ‖x‖ = α :=
  Matrix.IsLSQISolution.norm_eq_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hLS)
    (show Matrix.IsLSQISolution A b (1 : Matrix (Fin n) (Fin n) ℝ) 0 α x from h)

/-- `(σ|a|/c)² = (σa/c)²` and `(λ|a|/c)² = (λa/c)²`. -/
private theorem sq_mul_abs_div (s a c : ℝ) : (s * |a| / c) ^ 2 = (s * a / c) ^ 2 := by
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]

/-- **§6.2.1, the secular equation.** "Using the SVD (6.2.2), this leads to the problem of finding a
zero of the function `f(λ) = ‖x(λ)‖₂² − α² = ∑_k (σ_k u_kᵀb/(σ_k² + λ))² − α²`. … Since
`f′(λ) < 0` for `λ ≥ 0`, it follows that `f` has a unique positive root `λ₊`": for `α > 0` with
`‖x_LS‖₂ > α`, `f` is strictly decreasing on `λ > 0` and has exactly one positive root. The book's
"`f(0) > 0`" reads `f(0⁺) = ‖x_LS‖₂² − α²` (`x(λ)` is `x_LS` only in the limit). -/
theorem secular_existsUnique {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {b : EuclideanSpace ℝ (Fin m)}
    {α : ℝ} (hα0 : 0 < α) (hα : α < ‖toEuclideanLin A.pinv b‖) :
    (∀ μ, 0 < μ → ‖toEuclideanLin (A.tikhonov μ) b‖ ^ 2 - α ^ 2 = ∑ i : Fin (min m n),
      (σ i * (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b) / (σ i ^ 2 + μ)) ^ 2 -
        α ^ 2) ∧
    StrictAntiOn (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖ ^ 2 - α ^ 2) (Set.Ioi 0) ∧
    ∃! μ, 0 < μ ∧ ‖toEuclideanLin (A.tikhonov μ) b‖ ^ 2 - α ^ 2 = 0 := by
  refine ⟨fun μ hμ => ?_, ?_, ?_⟩
  · rw [norm_sq_toEuclideanLin_tikhonov_eq_sum_of_isSVD h hμ b]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [inner_toLp_eq_dotProduct, Real.norm_eq_abs, sq_mul_abs_div]
  · -- `Aᵀb ≠ 0`: otherwise every `x(λ)` vanishes and so does their limit `x_LS`
    have hb : toEuclideanLin Aᴴ b ≠ 0 := by
      intro hb
      have h0 : ∀ μ, toEuclideanLin (A.tikhonov μ) b = 0 := fun μ => by
        rw [tikhonov_def, toEuclideanLin_mul_apply, hb, map_zero]
      have hlim := tendsto_ridge_leastSquares A b
      simp only [h0] at hlim
      have := tendsto_nhds_unique hlim tendsto_const_nhds
      rw [this, norm_zero] at hα
      linarith
    intro μ hμ ν hν hμν
    have := strictAntiOn_norm_toEuclideanLin_tikhonov A hb hμ hν hμν
    simp only at this ⊢
    have h0 := norm_nonneg (toEuclideanLin (A.tikhonov ν) b)
    nlinarith
  · obtain ⟨μ, ⟨hμ, hμα⟩, huniq⟩ := existsUnique_norm_toEuclideanLin_tikhonov_eq hα0 hα
    refine ⟨μ, ⟨hμ, by rw [hμα, sub_self]⟩, fun ν ⟨hν, hνα⟩ => huniq ν ⟨hν, ?_⟩⟩
    have h2 : ‖toEuclideanLin (A.tikhonov ν) b‖ ^ 2 = α ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) hα0.le two_ne_zero).1 h2

/-- **(6.2.4).** "It can be shown that `ρ(λ) = ‖Ax(λ) − b‖₂² = ‖Ax_LS − b‖₂² +
∑_{i=1}^r (λu_iᵀb/(σ_i² + λ))²`", for any SVD of `A` and `λ > 0`; the sum runs over the `i` with
`σ_i ≠ 0`. -/
theorem equation_6_2_4 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov μ) b) - b‖ ^ 2 =
      ‖toEuclideanLin A (toEuclideanLin A.pinv b) - b‖ ^ 2 +
        ∑ i ∈ univ.filter (fun i : Fin (min m n) => σ i ≠ 0),
          (μ * (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b) / (σ i ^ 2 + μ)) ^ 2 := by
  rw [norm_sq_toEuclideanLin_tikhonov_sub_eq_sum_of_isSVD h hμ b]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [inner_toLp_eq_dotProduct, Real.norm_eq_abs, sq_mul_abs_div]

/-- **§6.2.1.** "It follows that `x(λ₊)` solves (6.2.1)": if `λ > 0` and `‖x(λ)‖₂ = α`, then `x(λ)`
solves the LSQI problem. -/
theorem isSphereLSQISolution_tikhonov {A : Matrix (Fin m) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m)}
    {μ : ℝ} (hμ : 0 < μ) {α : ℝ} (hn : ‖toEuclideanLin (A.tikhonov μ) b‖ = α) :
    IsSphereLSQISolution A b α (toEuclideanLin (A.tikhonov μ) b) := by
  unfold IsSphereLSQISolution
  exact Matrix.isLSQISolution_tikhonov hμ hn

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.2.1.** "Given `A ∈ ℝ^{m×n}` with `m ≥ n`, `b ∈ ℝ^m`, and `α > 0`, the following
algorithm computes a vector `x ∈ ℝⁿ` such that `‖Ax − b‖₂` is minimum subject to the constraint
that `‖x‖₂ ≤ α`":
```
Compute the SVD A = UΣVᵀ, save V = [v₁ | ⋯ | v_n], form b̃ = Uᵀb, and determine r = rank(A).
if ∑_{i=1}^r (b̃_i/σ_i)² > α²
    Find λ₊ > 0 such that ∑_{i=1}^r (σ_i b̃_i/(σ_i² + λ₊))² = α².
    x = ∑_{i=1}^r (σ_i b̃_i/(σ_i² + λ₊)) v_i
else
    x = ∑_{i=1}^r (b̃_i/σ_i) v_i
end
```
"Compute the SVD" is the parameter `svd`, returning `(U, σ, V)`; "Find `λ₊`" is the parameter
`root`, given the secular function of the computed data. The indices `i = 1 : r` are those
`i < min(m, n)` with `σ_i ≠ 0` (the singular values are sorted, so these are the first `r`). -/
noncomputable def algorithm_6_2_1
    (svd : Matrix (Fin m) (Fin n) ℝ →
      M (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (root : (ℝ → ℝ) → M ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (α : ℝ) :
    M (Fin n → ℝ) := do
  let USV ← svd A
  let U := USV.1
  let σ := USV.2.1
  let V := USV.2.2
  let bt ← Chapter01.algorithm_1_1_3 rnd Uᵀ b 0
  let I := (List.finRange (min m n)).filter fun i : Fin (min m n) => σ i ≠ 0
  let s ← I.foldlM (fun s (i : Fin (min m n)) => do
    let q ← rnd (bt (Fin.castLE (min_le_left m n) i) / σ i)
    let q2 ← rnd (q * q)
    rnd (s + q2)) 0
  let α2 ← rnd (α * α)
  if α2 < s then
    let lam ← root fun t =>
      (I.map fun i : Fin (min m n) =>
        (σ i * bt (Fin.castLE (min_le_left m n) i) / (σ i ^ 2 + t)) ^ 2).sum - α ^ 2
    I.foldlM (fun x (i : Fin (min m n)) => do
      let num ← rnd (σ i * bt (Fin.castLE (min_le_left m n) i))
      let s2 ← rnd (σ i * σ i)
      let den ← rnd (s2 + lam)
      let c ← rnd (num / den)
      Chapter01.algorithm_1_1_2 rnd c (fun j => V j (Fin.castLE (min_le_right m n) i)) x) 0
  else
    I.foldlM (fun x (i : Fin (min m n)) => do
      let c ← rnd (bt (Fin.castLE (min_le_left m n) i) / σ i)
      Chapter01.algorithm_1_1_2 rnd c (fun j => V j (Fin.castLE (min_le_right m n) i)) x) 0

end Programs

/-- A sum over the filtered indices of `Fin k`, when the dropped terms vanish, is the full sum. -/
private theorem sum_map_filter_finRange' {k : ℕ} {β : Type*} [AddCommMonoid β] (p : Fin k → Prop)
    [DecidablePred p] (g : Fin k → β) (hg : ∀ i, ¬ p i → g i = 0) :
    (((List.finRange k).filter fun i => decide (p i)).map g).sum = ∑ i, g i := by
  rw [List.sum_map_filter_finRange, Finset.sum_filter_of_ne fun i _ h => not_not.1 (mt (hg i) h)]

/-- **Algorithm 6.2.1 is correct in exact arithmetic**: for `α > 0`, an `svd` subroutine returning
SVDs and a `root` subroutine returning the positive root of a function that has exactly one, the
output solves the LSQI problem (6.2.1). The first branch is `x(λ₊)` (`equation_6_1_14`,
`secular_existsUnique`, `isSphereLSQISolution_tikhonov`), the second `x_LS` (`equation_6_2_3`,
`isLSQISolution_pinv`). -/
theorem algorithm_6_2_1_spec
    (svd : Matrix (Fin m) (Fin n) ℝ →
      Id (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (hsvd : ∀ A', IsSVD A' (Id.run (svd A')).1 (Id.run (svd A')).2.1 (Id.run (svd A')).2.2)
    (root : (ℝ → ℝ) → Id ℝ)
    (hroot : ∀ f : ℝ → ℝ, (∃! t, 0 < t ∧ f t = 0) →
      0 < Id.run (root f) ∧ f (Id.run (root f)) = 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {α : ℝ} (hα : 0 < α) :
    IsSphereLSQISolution A (WithLp.toLp 2 b) α
      (WithLp.toLp 2 (Id.run (algorithm_6_2_1 pure svd root A b α))) := by
  have hs := hsvd A
  have h112 : ∀ (c : ℝ) (v x : Fin n → ℝ),
      Chapter01.algorithm_1_1_2 (M := Id) pure c v x = pure (x + c • v) := fun c v x => by
    rw [← Chapter01.algorithm_1_1_2_spec]
    rfl
  have h113 : ∀ C : Matrix (Fin m) (Fin m) ℝ,
      Chapter01.algorithm_1_1_3 (M := Id) pure C b 0 = pure (C *ᵥ b) := fun C => by
    rw [← zero_add (C *ᵥ b), ← Chapter01.algorithm_1_1_3_spec]
    rfl
  simp only [algorithm_6_2_1, Id.run_bind, h113, h112, List.idRun_foldlM, Id.run_pure]
  set U := (Id.run (svd A)).1 with hU
  set σ := (Id.run (svd A)).2.1 with hσ
  set V := (Id.run (svd A)).2.2 with hV
  set I := (List.finRange (min m n)).filter (fun i : Fin (min m n) => decide (σ i ≠ 0)) with hI
  have hLS := equation_6_2_3 hs (WithLp.toLp 2 b)
  -- the sums over `I = {i : σ_i ≠ 0}` are the full sums, the dropped terms vanishing
  have hsum : ∀ {β : Type} [AddCommMonoid β] (g : Fin (min m n) → β),
      (∀ i : Fin (min m n), σ i = 0 → g i = 0) →
        ∀ a, I.foldl (fun s i => s + g i) a = a + ∑ i, g i :=
    fun g hg a => by
      rw [List.foldl_add_eq_add_sum_map, hI,
        sum_map_filter_finRange' _ g fun i hi => hg i (not_not.1 hi)]
  have hlist : ∀ g : Fin (min m n) → ℝ, (∀ i : Fin (min m n), σ i = 0 → g i = 0) →
      (I.map g).sum = ∑ i, g i := fun g hg => by
    rw [hI, sum_map_filter_finRange' _ g fun i hi => hg i (not_not.1 hi)]
  rw [hsum _ (fun i hi => by simp [hi]), zero_add]
  have hs2 : ∑ i : Fin (min m n), (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) / σ i *
      ((Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) / σ i) =
      ‖toEuclideanLin A.pinv (WithLp.toLp 2 b)‖ ^ 2 := by
    rw [hLS.2]
    refine sum_congr rfl fun i _ => ?_
    rw [sq]
    rfl
  rw [hs2]
  split_ifs with hc
  · simp only [Id.run_bind, List.idRun_foldlM, Id.run_pure]
    have hαLS : α < ‖toEuclideanLin A.pinv (WithLp.toLp 2 b)‖ :=
      lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by rwa [sq])
    obtain ⟨hf1, -, hf3⟩ := secular_existsUnique hs hα hαLS
    suffices key : ∀ F : ℝ → ℝ, (∀ t, 0 < t →
        F t = ‖toEuclideanLin (A.tikhonov t) (WithLp.toLp 2 b)‖ ^ 2 - α ^ 2) →
        IsSphereLSQISolution A (WithLp.toLp 2 b) α (WithLp.toLp 2 (List.foldl
          (fun x (i : Fin (min m n)) =>
          x + (σ i * (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) /
            (σ i * σ i + Id.run (root F))) • fun j => V j (Fin.castLE (min_le_right m n) i))
          0 I)) by
      refine key _ fun t ht => ?_
      rw [hf1 t ht, hlist _ (fun i hi => by simp [hi])]
      rfl
    intro F hF
    have hex : ∃! t, 0 < t ∧ F t = 0 := by
      obtain ⟨t, ⟨ht, hft⟩, hu⟩ := hf3
      refine ⟨t, ⟨ht, by rw [hF t ht, hft]⟩, fun t' ⟨ht', hft'⟩ => hu t' ⟨ht', ?_⟩⟩
      rw [← hF t' ht', hft']
    obtain ⟨hlam, hflam⟩ := hroot F hex
    rw [hsum _ (fun i hi => by simp [hi]), zero_add, WithLp.toLp_sum]
    have hx : ∑ i : Fin (min m n), WithLp.toLp 2
        ((σ i * (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) / (σ i * σ i + Id.run (root F))) •
          fun j => V j (Fin.castLE (min_le_right m n) i)) =
        toEuclideanLin (A.tikhonov (Id.run (root F))) (WithLp.toLp 2 b) := by
      rw [equation_6_1_14 hs hlam]
      refine sum_congr rfl fun i _ => ?_
      rw [WithLp.toLp_smul, inner_toLp_eq_dotProduct, WithLp.ofLp_toLp, sq]
      rfl
    rw [hx]
    refine isSphereLSQISolution_tikhonov hlam ?_
    have h2 := hF _ hlam
    rw [hflam] at h2
    exact (pow_left_inj₀ (norm_nonneg _) hα.le two_ne_zero).1 (by linarith)
  · simp only [Id.run_bind, List.idRun_foldlM, Id.run_pure]
    rw [hsum _ (fun i hi => by simp [hi]), zero_add, WithLp.toLp_sum]
    have hx : ∑ i : Fin (min m n), WithLp.toLp 2 (((Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) /
        σ i) • fun j => V j (Fin.castLE (min_le_right m n) i)) =
        toEuclideanLin A.pinv (WithLp.toLp 2 b) := by
      rw [hLS.1]
      refine sum_congr rfl fun i _ => ?_
      rw [WithLp.toLp_smul]
      rfl
    rw [hx]
    refine isLSQISolution_pinv A _ ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hα.le two_ne_zero).1 ?_
    rw [sq α]
    exact not_lt.1 hc

/-! ### §6.2.2 More general quadratic constraints -/

/-- **(6.2.6).** "If the GSVD of `A` and `B` is given by (6.1.22) and (6.2.23) [(6.1.23)], then
(6.2.5) is equivalent to `minimize ‖D_Ay − b̃‖₂ subject to ‖D_By − d̃‖₂ ≤ α` where `b̃ = U₁ᵀb`,
`d̃ = U₂ᵀd`, `y = X⁻¹x`." -/
theorem equation_6_2_6 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ} {B : Matrix (Fin m₂) (Fin n) ℝ}
    {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ} {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} {α' β' : ℕ → ℝ} (h : IsGSVD A B U₁ U₂ X α' β')
    {b : EuclideanSpace ℝ (Fin m₁)} {d : EuclideanSpace ℝ (Fin m₂)} {α : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    Matrix.IsLSQISolution A b B d α x ↔
      Matrix.IsLSQISolution (rectDiagonal α') (toEuclideanLin U₁ᵀ b)
        (shiftedRectDiagonal ((fromRows A B).rank - m₂) β') (toEuclideanLin U₂ᵀ d) α
        (toEuclideanLin X⁻¹ x) := by
  have e₁ := h.star_mul_mul₁
  have e₂ := h.star_mul_mul₂
  simp only [RCLike.ofReal_real_eq_id, id_eq] at e₁ e₂
  rw [isLSQISolution_iff_of_isGSVD h, e₁, e₂, star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial]

/-- **(6.2.7)**, in Theorem 6.1.1's block order: "`‖D_Ay − b̃‖₂² = ∑_{i=1}^{n₁} (α_iy_i − b̃_i)² +
∑_{i=n₁+1}^{m₁} b̃_i²`" for `D_A = rectDiagonal α ∈ ℝ^{m₁×n₁}`, `m₁ ≥ n₁` (the rows `i < n₁` carry
`α_i y_i − b̃_i`, the others `b̃_i`). -/
theorem equation_6_2_7 {m₁ : ℕ} (α : ℕ → ℝ) (y : Fin n → ℝ) (bt : Fin m₁ → ℝ) :
    ‖WithLp.toLp 2 ((rectDiagonal α : Matrix (Fin m₁) (Fin n) ℝ) *ᵥ y - bt)‖ ^ 2 =
      ∑ i : Fin m₁, if h : (i : ℕ) < n then (α i * y ⟨i, h⟩ - bt i) ^ 2 else bt i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp, Pi.sub_apply]
  split_ifs with hi
  · rw [rectDiagonal_mulVec α y i hi]
  · rw [rectDiagonal_mulVec_of_le α y i (not_lt.1 hi), zero_sub, neg_sq]

/-- `(shiftedRectDiagonal p β *ᵥ y)_i = β_{i+p} y_{i+p}`, or `0` past the last column. -/
private theorem shiftedRectDiagonal_mulVec {m₂ : ℕ} (p : ℕ) (β : ℕ → ℝ) (y : Fin n → ℝ)
    (i : Fin m₂) :
    ((shiftedRectDiagonal p β : Matrix (Fin m₂) (Fin n) ℝ) *ᵥ y) i =
      if h : (i : ℕ) + p < n then β ((i : ℕ) + p) * y ⟨i + p, h⟩ else 0 := by
  rw [mulVec, dotProduct]
  split_ifs with h
  · rw [sum_eq_single ⟨i + p, h⟩]
    · rw [shiftedRectDiagonal_apply, ite_eq_left rfl]
    · intro j _ hj
      rw [shiftedRectDiagonal_apply, ite_eq_right (fun hj' => hj (Fin.ext hj')), zero_mul]
    · exact fun h' => absurd (mem_univ _) h'
  · refine sum_eq_zero fun j _ => ?_
    rw [shiftedRectDiagonal_apply,
      ite_eq_right (fun (hj : (j : ℕ) = i + p) => h (hj ▸ j.isLt)), zero_mul]

/-- **(6.2.8)**, in Theorem 6.1.1's block order: `‖D_By − d̃‖₂² = ∑_i (β_{i+p}y_{i+p} − d̃_i)² +
∑_{i + p ≥ n₁} d̃_i²` for `D_B = shiftedRectDiagonal p β` (row `i` of `D_B` carries `β_{i+p}` in
column `i + p`). The book's form, "`∑_{i=1}^{m₂} (β_iy_i − d̃_i)² + ∑_{i=m₂+1}^{n₁} d̃_i² ≤ α²`",
is the third edition's block order, and its second sum (of `d̃_i` for `i > m₂`) is meaningless. -/
theorem equation_6_2_8 {m₂ : ℕ} (p : ℕ) (β : ℕ → ℝ) (y : Fin n → ℝ) (dt : Fin m₂ → ℝ) :
    ‖WithLp.toLp 2 ((shiftedRectDiagonal p β : Matrix (Fin m₂) (Fin n) ℝ) *ᵥ y - dt)‖ ^ 2 =
      ∑ i : Fin m₂, if h : (i : ℕ) + p < n then (β ((i : ℕ) + p) * y ⟨i + p, h⟩ - dt i) ^ 2
        else dt i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp, Pi.sub_apply, shiftedRectDiagonal_mulVec]
  split_ifs
  · rfl
  · rw [zero_sub, neg_sq]

/-! ### §6.2.3 Least squares with equality constraints -/

/-- **§6.2.3.** "By setting `α = 0` in (6.2.5) we see that the LSE problem is a special case of the
LSQI problem." -/
theorem isLSQISolution_zero_iff {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m₁)}
    {d : EuclideanSpace ℝ (Fin m₂)} {x : EuclideanSpace ℝ (Fin n)} :
    Matrix.IsLSQISolution A b B d 0 x ↔ IsLSESolution A b B d x :=
  Matrix.isLSQISolution_zero_iff

/-- **§6.2.3, the derivation of Algorithm 6.2.2.** "Let `QᵀBᵀ = [R; 0]` be the QR factorization of
`Bᵀ` and set `AQ = [A₁ A₂]`, `Qᵀx = [y; z]`. … Thus, `y` is determined from the constraint equation
`Rᵀy = d` and the vector `z` is obtained by solving the unconstrained LS problem
`min ‖A₂z − (b − A₁y)‖₂`. Combining the above, we see that the following vector solves the LSE
problem: `x = Q[y; z]`", for `B` of full row rank `m₂ ≤ n₁`; when moreover `A` has full column rank
the LSE solution is unique. Here `Q₁ = Q(:, 1:m₂)`, `Q₂ = Q(:, m₂+1:n₁)`, `R₁ = R(1:m₂, 1:m₂)`,
`y = R₁⁻ᵀd`. -/
theorem isLSESolution_qr {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {b : EuclideanSpace ℝ (Fin m₁)} {B : Matrix (Fin m₂) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m₂)} (hpn : m₂ ≤ n) (hB : LinearIndependent ℝ B)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin n) (Fin m₂) ℝ} (hQR : IsQR Bᵀ Q R)
    {z : EuclideanSpace ℝ (Fin (n - m₂))}
    (hz : IsLeastSquaresSolution
      (A * Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂))
      (b - toEuclideanLin (A * Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᵀ)⁻¹ d)) z) :
    IsLSESolution A b B d
        (toEuclideanLin (Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᵀ)⁻¹ d) +
          toEuclideanLin (Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂))
            z) ∧
      (LinearIndependent ℝ Aᵀ → ∃! x, IsLSESolution A b B d x) := by
  have hQR' : IsQR Bᴴ Q R := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hL : Q.lastColumns (Nat.sub_le n m₂) =
      Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂) :=
    lastColumns_eq_submatrix Q _ fun j => by simp; omega
  have hsol := isLSESolution_of_isQR hpn hB hQR' (by
    rw [hL]; rwa [conjTranspose_eq_transpose_of_trivial])
  rw [conjTranspose_eq_transpose_of_trivial, hL] at hsol
  refine ⟨hsol, fun hA => ⟨_, hsol, fun x' hx' => hsol.eq_of_ker_inf_ker_eq_bot hx' ?_⟩⟩
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.2 (mulVec_injective_of_linearIndependent_transpose hA)
  rw [hker, bot_inf_eq]

/-- **§6.2.3.** "If `null(A) ∩ null(B) ≠ {0}` and `d ∈ ran(B)` [the] LSE solution is not unique"
(the printed sentence is garbled): if `d ∈ ran(B)` an LSE solution exists, and adding any vector of
`null(A) ∩ null(B)` to a solution gives another. -/
theorem isLSESolution_not_unique {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {b : EuclideanSpace ℝ (Fin m₁)} {B : Matrix (Fin m₂) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m₂)} (hd : d ∈ LinearMap.range (toEuclideanLin B)) :
    (∃ x, IsLSESolution A b B d x) ∧
      ∀ x, IsLSESolution A b B d x →
        ∀ z ∈ LinearMap.ker (toEuclideanLin A) ⊓ LinearMap.ker (toEuclideanLin B),
          IsLSESolution A b B d (x + z) :=
  ⟨(existsUnique_isLSESolution hd).1, fun _ hx _ hz => hx.add_of_mem hz⟩

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.2.2.** "Suppose `A ∈ ℝ^{m₁×n₁}`, `B ∈ ℝ^{m₂×n₁}`, `b ∈ ℝ^{m₁}`, and `d ∈ ℝ^{m₂}`.
If `rank(A) = n₁` and `rank(B) = m₂ < n₁`, then the following algorithm minimizes `‖Ax − b‖₂`
subject to the constraint `Bx = d`":
```
Compute the QR factorization Bᵀ = QR.
Solve R(1:m₂, 1:m₂)ᵀ · y = d for y.
A = AQ
Find z so ‖A(:, m₂+1:n₁) z − (b − A(:, 1:m₂) · y)‖₂ is minimized.
x = Q(:, 1:m₂) · y + Q(:, m₂+1:n₁) · z
```
"Compute the QR factorization" is chapter 5's Householder QR (Algorithm 5.2.1) with the explicit
factor by forward accumulation of the reflectors it returned; the triangular solve is chapter 3's
forward substitution (Algorithm 3.1.1) on `R(1:m₂, 1:m₂)ᵀ`; `AQ` is chapter 1's Algorithm 1.1.5; the
residual `b − A(:, 1:m₂)y` and the two products forming `x` are gaxpys (Algorithm 1.1.3, the
negation being exact); "Find `z`" names no method and is the parameter `ls`. Here `m₁ = m`,
`n₁ = n`, `m₂ = p`, and `hpn : p ≤ n`. -/
noncomputable def algorithm_6_2_2 {m₂ : ℕ} (hpn : m₂ ≤ n)
    (ls : Matrix (Fin m) (Fin (n - m₂)) ℝ → (Fin m → ℝ) → M (Fin (n - m₂) → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m₂) (Fin n) ℝ) (b : Fin m → ℝ)
    (d : Fin m₂ → ℝ) : M (Fin n → ℝ) := do
  let Aβ ← Chapter05.algorithm_5_2_1 rnd Bᵀ
  let Q ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors Aβ.1 Aβ.2)
  let R := Chapter05.upperPart Aβ.1
  let y ← Chapter03.algorithm_3_1_1 rnd (R.firstRows hpn)ᵀ d
  let AQ ← Chapter01.algorithm_1_1_5 rnd A Q 0
  let c ← Chapter01.algorithm_1_1_3 rnd (-AQ.firstColumns hpn) y b
  let z ← ls (AQ.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂)) c
  let x₁ ← Chapter01.algorithm_1_1_3 rnd (Q.firstColumns hpn) y 0
  Chapter01.algorithm_1_1_3 rnd (Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘
    Fin.natAdd m₂)) z x₁

end Programs

/-- **Algorithm 6.2.2 is correct in exact arithmetic**: if `rank(A) = n₁`, `rank(B) = m₂ ≤ n₁` and
`ls` returns least-squares solutions, the output is the (unique) solution of the LSE problem. The
Householder QR of `Bᵀ` with the returned `β` is a QR factorization unconditionally
(`Chapter05.algorithm_5_2_1_spec`, `Chapter05.forwardAccumulation_spec`), `R(1:m₂, 1:m₂)` has a
nonzero diagonal because `Bᵀ` has full column rank, and the rest is `isLSESolution_qr`. -/
theorem algorithm_6_2_2_spec {m₂ : ℕ} (hpn : m₂ ≤ n)
    (ls : Matrix (Fin m) (Fin (n - m₂)) ℝ → (Fin m → ℝ) → Id (Fin (n - m₂) → ℝ))
    (hls : ∀ C c, IsLeastSquaresSolution C (WithLp.toLp 2 c) (WithLp.toLp 2 (Id.run (ls C c))))
    {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin m₂) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (hB : LinearIndependent ℝ B) (b : Fin m → ℝ) (d : Fin m₂ → ℝ) :
    IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d)
        (WithLp.toLp 2 (Id.run (algorithm_6_2_2 pure hpn ls A B b d))) ∧
      ∀ x, IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d) x →
        x = WithLp.toLp 2 (Id.run (algorithm_6_2_2 pure hpn ls A B b d)) := by
  have h113 : ∀ {r s : ℕ} (C : Matrix (Fin r) (Fin s) ℝ) (v : Fin s → ℝ) (w : Fin r → ℝ),
      Chapter01.algorithm_1_1_3 (M := Id) pure C v w = pure (w + C *ᵥ v) := fun C v w => by
    rw [← Chapter01.algorithm_1_1_3_spec]
    rfl
  have h115 : ∀ {r s t : ℕ} (C : Matrix (Fin r) (Fin s) ℝ) (D : Matrix (Fin s) (Fin t) ℝ),
      Chapter01.algorithm_1_1_5 (M := Id) pure C D 0 = pure (C * D) := fun C D => by
    rw [← zero_add (C * D), ← Chapter01.algorithm_1_1_5_spec]
    rfl
  have hfa : ∀ data : List ((Fin n → ℝ) × ℝ),
      Chapter05.forwardAccumulation (M := Id) pure data =
        pure (Chapter05.householderProduct data) := fun data => by
    rw [← Chapter05.forwardAccumulation_spec]
    rfl
  obtain ⟨hqr, -⟩ := Chapter05.algorithm_5_2_1_spec hpn Bᵀ
  set Aβ := Id.run (Chapter05.algorithm_5_2_1 pure Bᵀ) with hAβ
  set Q := Chapter05.factoredQ Aβ.2 Aβ.1 with hQ
  set R := Chapter05.upperPart Aβ.1 with hR
  set e : Fin (n - m₂) → Fin n := Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂ with he
  have hBT : LinearIndependent ℝ (Bᵀ)ᵀ := by rwa [transpose_transpose]
  -- the triangular solve
  set R₁ := R.firstRows hpn with hR₁
  have hL : R₁ᵀ.IsLowerTriangular := (hqr.isUpperTriangular_firstRows hpn).transpose
  have hdiag : ∀ i, R₁ᵀ i i ≠ 0 := fun i =>
    hqr.firstRows_diag_ne_zero_of_linearIndependent hpn hBT i
  set y := Id.run (Chapter03.algorithm_3_1_1 pure R₁ᵀ d) with hy
  have hRy : R₁ᵀ *ᵥ y = d := Chapter03.algorithm_3_1_1_spec hL hdiag d
  have hR₁u : IsUnit R₁ᵀ :=
    (isUnit_transpose _).2 (hqr.isUnit_firstRows_of_linearIndependent hpn hBT)
  have hy' : y = R₁ᵀ⁻¹ *ᵥ d := by
    rw [← hRy, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hR₁u), one_mulVec]
  have hAQ₁ : (A * Q).firstColumns hpn = A * Q.firstColumns hpn := by
    ext i j
    simp [firstColumns, mul_apply]
  have hAQ₂ : (A * Q).submatrix id e = A * Q.submatrix id e := by
    ext i j
    simp [mul_apply]
  set z := Id.run (ls (A * Q.submatrix id e) (b + -(A * Q.firstColumns hpn) *ᵥ y)) with hz
  have hzLS := hls (A * Q.submatrix id e) (b + -(A * Q.firstColumns hpn) *ᵥ y)
  have hout : Id.run (algorithm_6_2_2 pure hpn ls A B b d) =
      0 + Q.firstColumns hpn *ᵥ y + Q.submatrix id e *ᵥ z := by
    simp only [algorithm_6_2_2, Id.run_bind, hfa, h115, h113, Id.run_pure]
    rw [← hAβ, ← Chapter05.factoredQ, ← hQ, ← hR, ← hR₁, ← hy, hAQ₁, hAQ₂, ← hz]
  have hsol := (isLSESolution_qr (b := WithLp.toLp 2 b) (d := WithLp.toLp 2 d) hpn hB
    (Q := Q) (R := R) (by rwa [← conjTranspose_eq_transpose_of_trivial]) (z := WithLp.toLp 2 z)
    (by
      convert hzLS using 2
      rw [hy']
      change b - (A * Q.firstColumns hpn) *ᵥ (R₁ᵀ⁻¹ *ᵥ d) =
        b + -(A * Q.firstColumns hpn) *ᵥ (R₁ᵀ⁻¹ *ᵥ d)
      rw [neg_mulVec, sub_eq_add_neg]))
  have hx : WithLp.toLp 2 (Id.run (algorithm_6_2_2 pure hpn ls A B b d)) =
      toEuclideanLin (Q.firstColumns hpn) (toEuclideanLin (R₁ᵀ)⁻¹ (WithLp.toLp 2 d)) +
        toEuclideanLin (Q.submatrix id e) (WithLp.toLp 2 z) := by
    rw [hout, zero_add, hy']
    rfl
  rw [hx]
  refine ⟨hsol.1, fun x hx' => ?_⟩
  obtain ⟨x₀, -, hu⟩ := hsol.2 hA
  rw [hu x hx', hu _ hsol.1]

/-! ### §6.2.4 LSE solution using the augmented system -/

/-- **(6.2.10).** "Combining this with the equations `r = b − Ax` and `Bx = d` we obtain the
symmetric indefinite linear system `[0 Aᵀ Bᵀ; A I 0; B 0 0][x; r; λ] = [0; b; d]`": a solution
of the augmented system gives an LSE solution `x`. -/
theorem equation_6_2_10 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {x : Fin n → ℝ} {r b : Fin m₁ → ℝ} {l d : Fin m₂ → ℝ}
    (h : augmentedLSE A B *ᵥ Sum.elim x (Sum.elim r l) =
      Sum.elim (0 : Fin n → ℝ) (Sum.elim b d)) :
    IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d) (WithLp.toLp 2 x) :=
  isLSESolution_of_augmented h

/-- **§6.2.4.** "This system is nonsingular if both `A` and `B` have full rank" (`A` of full column
rank, `B` of full row rank). -/
theorem equation_6_2_10_isUnit {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) (hB : LinearIndependent ℝ B) :
    IsUnit (augmentedLSE A B) :=
  isUnit_augmentedLSE hA hB

/-! ### §6.2.5 LSE solution using the GSVD -/

/-- **(6.2.11).** "Using the GSVD given by (6.1.22) and (6.1.23), we see that the LSE problem
transforms to `min_{D_By = d̃} ‖D_Ay − b̃‖₂` where `b̃ = U₁ᵀb`, `d̃ = U₂ᵀd`, and `y = X⁻¹x`." -/
theorem equation_6_2_11 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) {b : EuclideanSpace ℝ (Fin m₁)} {d : EuclideanSpace ℝ (Fin m₂)}
    {x : EuclideanSpace ℝ (Fin n)} :
    IsLSESolution A b B d x ↔
      IsLSESolution (rectDiagonal α) (toEuclideanLin U₁ᵀ b)
        (shiftedRectDiagonal ((fromRows A B).rank - m₂) β) (toEuclideanLin U₂ᵀ d)
        (toEuclideanLin X⁻¹ x) := by
  rw [← Matrix.isLSQISolution_zero_iff, ← Matrix.isLSQISolution_zero_iff]
  exact equation_6_2_6 h

/-- **(6.2.12)**, in Theorem 6.1.1's block order. "It follows that if `null(A) ∩ null(B) = {0}` and
`X = [x₁ | ⋯ | x_n]`, then `x = ∑ (d̃_i/β_i) x_i + ∑ (b̃_i/α_i) x_i` solves the LSE problem", for
`B` of full row rank `m₂` and `m₁ ≥ n₁`: then `r = n₁`, `p = n₁ − m₂`, the first `n₁ − m₂` pairs are
`(α_i, β_i) = (1, 0)` and `x = ∑_{i < n₁−m₂} b̃_i x_i + ∑_{i ≥ n₁−m₂} (d̃_{i−(n₁−m₂)}/β_i) x_i`. The
book's form is the third edition's block order. -/
theorem equation_6_2_12 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (hB : LinearIndependent ℝ B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace ℝ (Fin m₁)) (d : EuclideanSpace ℝ (Fin m₂)) :
    IsLSESolution A b B d (WithLp.toLp 2 (∑ i : Fin n,
      (if hi : (i : ℕ) < n - m₂ then (U₁ᵀ *ᵥ WithLp.ofLp b) ⟨i, lt_of_lt_of_le i.isLt hnm⟩
        else (U₂ᵀ *ᵥ WithLp.ofLp d) ⟨(i : ℕ) - (n - m₂), by have := i.isLt; omega⟩ / β i) •
        X.col i)) := by
  have e := isLSESolution_sum_of_isGSVD h hnm hB hAB b d
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at e
  exact e

/-! ### §6.2.6 LSE solution using weights -/

/-- **(6.2.13).** "`‖[A; √λB]x − [b; √λd]‖₂² = ‖Ax − b‖₂² + λ‖Bx − d‖₂²`", so for `λ ≥ 0` the
least-squares solutions of the stacked problem are the minimizers of the penalized objective; for
`λ > 0` and `null(A) ∩ null(B) = {0}`, `AᵀA + λBᵀB` is positive definite and the minimizer is the
solution `x(λ)` of `(AᵀA + λBᵀB)x = Aᵀb + λBᵀd` (`Matrix.penaltyLSE`). -/
theorem equation_6_2_13 {m₁ m₂ : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (B : Matrix (Fin m₂) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m₁)) (d : EuclideanSpace ℝ (Fin m₂)) {μ : ℝ} (hμ : 0 ≤ μ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (fromRows A (Real.sqrt μ • B)) x -
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) (Real.sqrt μ • WithLp.ofLp d))‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x - d‖ ^ 2) ∧
    (IsLeastSquaresSolution (fromRows A (Real.sqrt μ • B))
        (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) (Real.sqrt μ • WithLp.ofLp d))) x ↔
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x - d‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y - d‖ ^ 2) ∧
    (0 < μ → LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ →
      (Aᵀ * A + μ • (Bᵀ * B)).PosDef) := by
  refine ⟨?_, ?_, fun hμ' hAB => ?_⟩
  · rw [norm_fromRows_sub_sq, WithLp.toLp_ofLp]
    have e : toEuclideanLin (Real.sqrt μ • B) x - WithLp.toLp 2 (Real.sqrt μ • WithLp.ofLp d) =
        Real.sqrt μ • (toEuclideanLin B x - d) := by
      rw [toEuclideanLin_smul_apply, WithLp.toLp_smul, WithLp.toLp_ofLp, smul_sub]
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hμ]
  · have h := isLeastSquaresSolution_fromRows_iff A B (WithLp.ofLp b) (WithLp.ofLp d) hμ x
    simp only [WithLp.toLp_ofLp, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h
  · have h := (posDef_gram_add_smul_gram_iff A B hμ').2 hAB
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h

/-- **(6.2.14)**, corrected, in Theorem 6.1.1's block order. "It follows that `x(λ) − x =
∑_{i=1}^p (α_i/β_i)((β_iu_iᵀb − α_iv_iᵀd)/(α_i² + λ²β_i²)) x_i`": in the setting of
`equation_6_2_12`, for `λ > 0`, with `x` the LSE solution,
`x(λ) − x = ∑_{i ≥ n₁−m₂} (α_i(β_ib̃_i − α_id̃_{i−(n₁−m₂)})/(β_i(α_i² + λβ_i²))) x_i`. The book
prints `λ²` for `λ`, `u_iᵀb`, `v_iᵀd` for `b̃_i`, `d̃_i`, and the range `1 : p`. -/
theorem equation_6_2_14 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (hB : LinearIndependent ℝ B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace ℝ (Fin m₁)) (d : EuclideanSpace ℝ (Fin m₂)) {μ : ℝ} (hμ : 0 < μ) :
    penaltyLSE A B b d μ - WithLp.toLp 2 (∑ i : Fin n,
      (if hi : (i : ℕ) < n - m₂ then (U₁ᵀ *ᵥ WithLp.ofLp b) ⟨i, lt_of_lt_of_le i.isLt hnm⟩
        else (U₂ᵀ *ᵥ WithLp.ofLp d) ⟨(i : ℕ) - (n - m₂), by have := i.isLt; omega⟩ / β i) •
        X.col i) =
      WithLp.toLp 2 (∑ i : Fin n,
        (if hi : (i : ℕ) < n - m₂ then 0
          else α i * (β i * (U₁ᵀ *ᵥ WithLp.ofLp b) ⟨i, lt_of_lt_of_le i.isLt hnm⟩ -
              α i * (U₂ᵀ *ᵥ WithLp.ofLp d) ⟨(i : ℕ) - (n - m₂), by have := i.isLt; omega⟩) /
            (β i * (α i ^ 2 + μ * β i ^ 2))) • X.col i) := by
  have e := penaltyLSE_sub_eq_sum_of_isGSVD h hnm hB hAB b d hμ
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at e
  exact e

/-- **§6.2.6.** "This shows that `x(λ) → x` as `λ → ∞`", for `B` of full row rank, `m₁ ≥ n₁`,
`null(A) ∩ null(B) = {0}` and `x` the LSE solution. -/
theorem tendsto_penaltyLSE_solution {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} (hnm : n ≤ m₁) (hB : LinearIndependent ℝ B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {b : EuclideanSpace ℝ (Fin m₁)} {d : EuclideanSpace ℝ (Fin m₂)} {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsLSESolution A b B d x) : Tendsto (penaltyLSE A B b d) atTop (𝓝 x) :=
  Matrix.tendsto_penaltyLSE hnm hB hAB hx

end GolubVanLoan.Chapter06
