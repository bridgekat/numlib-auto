import Numlib.Krylov.Preconditioned
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.Preconditioner.ApproximateInverse
import Numlib.Preconditioner.ILU
import Numlib.Preconditioner.Polynomial
import Numlib.Projection.Additive
import Numlib.Stationary.SPD
import Numlib.Stationary.Sweep
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter11.Section01
import NumlibSurface.GolubVanLoan.Chapter11.Section02
import NumlibSurface.GolubVanLoan.Chapter11.Section04

/-!
# Golub–Van Loan §11.5: preconditioning

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition,
§11.5, *Preconditioning*: the transformed system (§11.5.1), the preconditioned CG method
(Algorithm 11.5.1, (11.5.1)–(11.5.2)), the SSOR preconditioner (§11.5.3), sparse approximate
inverses (§11.5.5), polynomial preconditioners ((11.5.3) and the truncated Neumann loop of
§11.5.6), PCG as an accelerated splitting ((11.5.4)–(11.5.5)), incomplete Cholesky
((11.5.6)–(11.5.9), Lemma 11.5.1, Theorem 11.5.2, the recursive `incChol`, the Lin–Moré
factorization), incomplete block preconditioners ((11.5.10)), the saddle-point factorizations of
§11.5.10, and the domain-decomposition and Schwarz preconditioners of §11.5.11.

## Design

Matrices are real, `Matrix (Fin n) (Fin n) ℝ`, 0-based. A splitting `A = M₁ − N₁` is a
`Stationary.Splitting A`, its iteration matrix `G = M₁⁻¹N₁` is `s.iterationOperator`, and `ρ(G)` is
`Matrix.complexSpectralRadius`. The preconditioned Krylov theory is the backbone's
`Numlib/Krylov/Preconditioned` (`Krylov.PCG.iterate`: PCG is CG for `M⁻¹A` in the `M`-inner
product); incomplete factorizations are `Numlib/Preconditioner/ILU` (`Matrix.IsIC`), Stieltjes
matrices `Numlib/LinearAlgebra/Matrix/MMatrix` (`Matrix.IsStieltjes`), sparse approximate inverses
`Numlib/Preconditioner/ApproximateInverse`, and the Neumann polynomials
`Numlib/Preconditioner/Polynomial`.

Algorithms follow the conventions of `NumlibSurface/GolubVanLoan`: generic in a monad `M` with a
rounding hook `rnd`; a solve with the preconditioner is a routine argument `solveM` whose exact
semantics is the inverse. The book analyses no rounding error in this section; only exact
specifications are stated.

The book's incomplete Cholesky condition (11.5.7) asks `HHᵀ` to agree with `A` on the nonzeros of
`A`, while the backbone's `Matrix.IsIC P A H` (which the recursive `incChol` produces) asks
agreement off the dropped pattern `P`; the book's conditions follow from the backbone's when `P`
avoids the nonzeros of `A` (`isIncompleteCholesky_of_isIC`).

## Main results

* `algorithm_11_5_1`, `algorithm_11_5_1_spec`, `equation_11_5_1`, `equation_11_5_2` — PCG is the
  backbone's `Krylov.PCG.iterate`, derived from CG on `C⁻¹AC⁻¹`.
* `ssorPreconditioner_posDef`, `spai_column_decouple`, `spai_reduced_ls`.
* `neumann_inv_eq_tsum`, `neumannLoop_spec` (the loop needs `m + 1` steps), `equation_11_5_3`.
* `equation_11_5_4`, `concusGolubOLearyPCG`, `equation_11_5_5` — the Concus–Golub–O'Leary form of
  PCG is PCG, through the three-term form of CG.
* `IsIncompleteCholesky`, `equation_11_5_9`, `lemma_11_5_1`, `theorem_11_5_2`, `incChol_spec`,
  `poissonMatrix_isStieltjes`, `linMoreIC_nnz_le_add` (the printed bound needs `+ n`).
* `blockTridiagonal_cholesky`, `equation_11_5_10`, `blockIC_forwardSolve`.
* `saddlePoint_factorization`, `saddlePoint_splitting`.
* `equation_11_5_11_blockLU` (the printed block `LU` is wrong in the interface block,
  `equation_11_5_11_counterexample`), `ddPreconditioner_rank_le`, `schwarz_update_affine`.

## Not formalized here

§11.5.4 (Toeplitz and circulant preconditioners: T. Chan's and Strang's choices are definitions
with no claim), the drop-tolerance and `ILU(ℓ)` variants, the HSS saddle-point preconditioner
(its effectiveness is cited), the cost inequality and Criteria 1–2 of §11.5.1, the heuristic
choices of `Λ_k` in §11.5.9, and the Problems. Algorithm 11.5.2
(preconditioned GMRES) is written with the loop of Algorithm 11.4.2 (`gmresCore`) and `M`-solves.
-/

open Matrix Finset

namespace GolubVanLoan.Chapter11

/-! ### §11.5.1: the transformed system -/

/-- §11.5.1: with `M = M₁ M₂` nonsingular, `Ã = M₁⁻¹ A M₂⁻¹` and `b̃ = M₁⁻¹ b`, "solve the tilde
problem … and then determine `x` by solving `M₂ x = x̃`": `Ã x̃ = b̃` exactly when `x = M₂⁻¹ x̃`
solves `A x = b`. -/
theorem preconditioned_system_iff {n : ℕ} {A M₁ M₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : IsUnit M₁)
    (b xt : Fin n → ℝ) :
    (M₁⁻¹ * A * M₂⁻¹) *ᵥ xt = M₁⁻¹ *ᵥ b ↔ A *ᵥ (M₂⁻¹ *ᵥ xt) = b := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congrArg (M₁ *ᵥ ·) h
  simpa only [mulVec_nonsing_inv_mulVec h₁] using this

/-! ### §11.5.2: the preconditioned conjugate gradient method -/

/-- The state of Algorithm 11.5.1 after `k` passes: the iterate `x_k`, the residual `r_k`, the
preconditioned residual `z_k`, the last direction `p_k`, the last `r_{k−1}ᵀz_{k−1}`, and whether
the `while` test has failed. -/
structure PCGState (n : ℕ) where
  /-- The iteration count `k`. -/
  k : ℕ
  /-- The iterate `x_k`. -/
  x : Fin n → ℝ
  /-- The residual `r_k`. -/
  r : Fin n → ℝ
  /-- The preconditioned residual `z_k`, `M z_k = r_k`. -/
  z : Fin n → ℝ
  /-- The last search direction `p_k`. -/
  p : Fin n → ℝ
  /-- The last computed `r_{k−1}ᵀ z_{k−1}`. -/
  rz : ℝ
  /-- Whether the `while` test `‖r_k‖₂ > 0` has failed. -/
  done : Bool

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of the `while` loop of Algorithm 11.5.1 (the test `‖r_k‖₂ > 0` is `r_kᵀr_k ≠ 0` on
the computed dot product). -/
noncomputable def pcgStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (s : PCGState n) : M (PCGState n) := do
  if s.done then return s
  let ρ ← Chapter01.algorithm_1_1_1 rnd s.r s.r
  if ρ = 0 then return { s with done := true }
  let rz ← Chapter01.algorithm_1_1_1 rnd s.r s.z
  let p ← if s.k = 0 then pure s.z else do
    let τ ← rnd (rz / s.rz)
    Chapter01.algorithm_1_1_2 rnd τ s.p s.z
  let Ap ← Chapter01.algorithm_1_1_3 rnd A p 0
  let pAp ← Chapter01.algorithm_1_1_1 rnd p Ap
  let μ ← rnd (rz / pAp)
  let x ← Chapter01.algorithm_1_1_2 rnd μ p s.x
  let r ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
  let z ← solveM r
  return { k := s.k + 1, x := x, r := r, z := z, p := p, rz := rz, done := false }

/-- **Algorithm 11.5.1 (Preconditioned Conjugate Gradients).** "If `A` and `M` are symmetric
positive definite, `b ∈ ℝⁿ`, and `Ax₀ ≈ b`, then this algorithm computes `x_*` so that
`Ax_* = b`":
```
k = 0, r₀ = b − Ax₀, Solve Mz₀ = r₀
while ‖r_k‖₂ > 0
    k = k + 1
    if k = 1, p_k = z₀
    else τ = (r_{k−1}ᵀz_{k−1})/(r_{k−2}ᵀz_{k−2}), p_k = z_{k−1} + τp_{k−1}
    μ = (r_{k−1}ᵀz_{k−1})/(p_kᵀAp_k)
    x_k = x_{k−1} + μp_k
    r_k = r_{k−1} − μAp_k
    Solve Mz_k = r_k
end
```
The book prints `x_k = x_{k−1} − μp_k`, which contradicts `r_k = r_{k−1} − μAp_k` for
`r = b − Ax`; the program uses `+`. The solves with `M` are the routine `solveM`, the `while` loop
runs at most `fuel` passes. -/
noncomputable def algorithm_11_5_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (b x₀ : Fin n → ℝ) (fuel : ℕ) : M (PCGState n) := do
  let r₀ ← Chapter01.algorithm_1_1_3 rnd (-A) x₀ b
  let z₀ ← solveM r₀
  (List.range fuel).foldlM (fun s _ => pcgStep rnd A solveM s)
    { k := 0, x := x₀, r := r₀, z := z₀, p := z₀, rz := 1, done := false }

end Programs

section PCGSpec

variable {n : ℕ}

/-- A positive definite `A` is coercive relative to any `M`: `c ⟪Mx, x⟫ ≤ ⟪Ax, x⟫`. -/
private theorem exists_relCoercive {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (Mp : Matrix (Fin n) (Fin n) ℝ) : ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      c * RCLike.re (inner ℝ (toEuclideanLin Mp x) x) ≤
        RCLike.re (inner ℝ (toEuclideanLin A x) x) := by
  obtain ⟨cA, hcA, hA'⟩ := (Matrix.PosDef.isSymmetricCoercive_toEuclideanLin hA).isCoercive
  set L := ‖LinearMap.toContinuousLinearMap (toEuclideanLin Mp)‖ with hLdef
  have hL : 0 ≤ L := norm_nonneg _
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨cA / (L + 1), div_pos hcA hL1, fun x => ?_⟩
  have h1 : RCLike.re (inner ℝ (toEuclideanLin Mp x) x) ≤ L * ‖x‖ ^ 2 := by
    rw [RCLike.re_to_real]
    calc inner ℝ (toEuclideanLin Mp x) x ≤ ‖toEuclideanLin Mp x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (L * ‖x‖) * ‖x‖ := by
          gcongr
          exact (LinearMap.toContinuousLinearMap (toEuclideanLin Mp)).le_opNorm x
      _ = L * ‖x‖ ^ 2 := by ring
  have h2 := hA' x
  have hx2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  calc cA / (L + 1) * RCLike.re (inner ℝ (toEuclideanLin Mp x) x)
      ≤ cA / (L + 1) * (L * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (div_pos hcA hL1).le
    _ ≤ cA * ‖x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hL1]
        nlinarith [mul_nonneg hcA.le hx2]
    _ ≤ _ := h2

/-- An exact pass that finds the test failed is the identity. -/
private theorem pcgStep_done (A Mi : Matrix (Fin n) (Fin n) ℝ) (s : PCGState n)
    (h : s.done = true) : Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) s) = s := by
  simp [pcgStep, h]

/-- An exact pass that meets `r_k = 0` stops. -/
private theorem pcgStep_stop (A Mi : Matrix (Fin n) (Fin n) ℝ) (s : PCGState n)
    (h : s.done = false) (hρ : s.r ⬝ᵥ s.r = 0) :
    Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) s) = { s with done := true } := by
  simp [pcgStep, h, Chapter01.algorithm_1_1_1_spec, hρ]

/-- An exact pass of Algorithm 11.5.1 with `r_k ≠ 0`. -/
private theorem pcgStep_go (A Mi : Matrix (Fin n) (Fin n) ℝ) (s : PCGState n)
    (h : s.done = false) (hρ : s.r ⬝ᵥ s.r ≠ 0) :
    Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) s) =
      { k := s.k + 1,
        x := s.x + ((s.r ⬝ᵥ s.z) / ((if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p) ⬝ᵥ
          A *ᵥ (if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p))) •
          (if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p),
        r := s.r + (-((s.r ⬝ᵥ s.z) / ((if s.k = 0 then s.z else
          s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p) ⬝ᵥ A *ᵥ (if s.k = 0 then s.z else
          s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p)))) •
          A *ᵥ (if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p),
        z := Mi *ᵥ (s.r + (-((s.r ⬝ᵥ s.z) / ((if s.k = 0 then s.z else
          s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p) ⬝ᵥ A *ᵥ (if s.k = 0 then s.z else
          s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p)))) •
          A *ᵥ (if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p)),
        p := if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p,
        rz := s.r ⬝ᵥ s.z,
        done := false } := by
  by_cases hk : s.k = 0 <;>
    simp [pcgStep, h, hk, Chapter01.algorithm_1_1_1_spec, Chapter01.algorithm_1_1_2_spec,
      Chapter01.algorithm_1_1_3_spec, hρ]

/-- The backbone's PCG iterates for the Euclidean operators of `A` and `Mi = M⁻¹`. -/
private noncomputable abbrev pcgIter (A Mi : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (k : ℕ) : Krylov.PCG.State (EuclideanSpace ℝ (Fin n)) :=
  Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mi) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k

/-- One backbone PCG step in coordinates. -/
private theorem pcgIter_succ (A Mi : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ)
    (r p r' : Fin n → ℝ) (α : ℝ) (hr : r = (pcgIter A Mi b x₀ k).r.ofLp)
    (hp : p = (pcgIter A Mi b x₀ k).p.ofLp) (hα : α = (Mi *ᵥ r ⬝ᵥ r) / (p ⬝ᵥ A *ᵥ p))
    (hr' : r' = r - α • A *ᵥ p) :
    (pcgIter A Mi b x₀ (k + 1)).x.ofLp = (pcgIter A Mi b x₀ k).x.ofLp + α • p ∧
      (pcgIter A Mi b x₀ (k + 1)).r.ofLp = r' ∧
      (pcgIter A Mi b x₀ (k + 1)).p.ofLp =
        Mi *ᵥ r' + ((Mi *ᵥ r' ⬝ᵥ r') / (Mi *ᵥ r ⬝ᵥ r)) • p := by
  have hS : pcgIter A Mi b x₀ (k + 1) =
      Krylov.PCG.step (toEuclideanLin A) (toEuclideanLin Mi) (pcgIter A Mi b x₀ k) :=
    Krylov.PCG.iterate_succ _ _ _ _ k
  have hA : Krylov.PCG.alpha (toEuclideanLin A) (toEuclideanLin Mi) (pcgIter A Mi b x₀ k) = α := by
    rw [hα, hr, hp]
    rfl
  have hR : (Krylov.PCG.step (toEuclideanLin A) (toEuclideanLin Mi)
      (pcgIter A Mi b x₀ k)).r.ofLp = r' := by
    rw [Krylov.PCG.step_r, hA, hr', hr, hp]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hS, Krylov.PCG.step_x, hA, hp]
    rfl
  · rw [hS, hR]
  · rw [hS, Krylov.PCG.step_p, Krylov.PCG.beta, WithLp.ofLp_add, WithLp.ofLp_smul]
    have e1 : ∀ u : EuclideanSpace ℝ (Fin n), inner ℝ u (toEuclideanLin Mi u) =
        Mi *ᵥ u.ofLp ⬝ᵥ u.ofLp := fun u => rfl
    rw [e1, e1, hR, ← hr, ← hp, toEuclideanLin_apply, WithLp.ofLp_toLp, hR]

/-- The book's state after `k` exact passes, read off the backbone iterates. -/
private def PCGGood (A Mi : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ)
    (s : PCGState n) : Prop :=
  s.k = k ∧ s.x = (pcgIter A Mi b x₀ k).x.ofLp ∧ s.r = (pcgIter A Mi b x₀ k).r.ofLp ∧
    s.z = Mi *ᵥ s.r ∧
    (k = 0 → s.p = s.z) ∧
    (∀ j, k = j + 1 → s.p = (pcgIter A Mi b x₀ j).p.ofLp ∧
      s.rz = Mi *ᵥ (pcgIter A Mi b x₀ j).r.ofLp ⬝ᵥ (pcgIter A Mi b x₀ j).r.ofLp)

/-- A pass of Algorithm 11.5.1 with `r_k ≠ 0` advances the book's state by one backbone step. -/
private theorem pcgGood_step (A Mi : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ)
    (s : PCGState n) (hs : PCGGood A Mi b x₀ k s) (h : s.done = false)
    (hρ : s.r ⬝ᵥ s.r ≠ 0) :
    PCGGood A Mi b x₀ (k + 1) (Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) s)) := by
  obtain ⟨hk, hx, hr, hz, hp0, hps⟩ := hs
  rw [pcgStep_go A Mi s h hρ]
  -- the direction of this pass is the backbone direction `p_k`
  have hp : (if s.k = 0 then s.z else s.z + ((s.r ⬝ᵥ s.z) / s.rz) • s.p) =
      (pcgIter A Mi b x₀ k).p.ofLp := by
    rcases k with _ | j
    · rw [ite_eq_left hk, hz, hr]
      rfl
    · rw [ite_eq_right (by omega)]
      obtain ⟨hpj, hrzj⟩ := hps j rfl
      obtain ⟨-, hrs, hpsucc⟩ := pcgIter_succ A Mi b x₀ j _ _ _ _ rfl rfl rfl rfl
      rw [hpsucc, ← hrs, ← hr, hz, hpj, hrzj, dotProduct_comm s.r]
  have hrz : s.r ⬝ᵥ s.z =
      Mi *ᵥ (pcgIter A Mi b x₀ k).r.ofLp ⬝ᵥ (pcgIter A Mi b x₀ k).r.ofLp := by
    rw [hz, hr, dotProduct_comm]
  obtain ⟨hxs, hrs, -⟩ := pcgIter_succ A Mi b x₀ k _ _ _ _ rfl rfl rfl rfl
  refine ⟨by simp [hk], ?_, ?_, rfl, fun h0 => absurd h0 (Nat.succ_ne_zero k),
    fun j hj => ?_⟩
  · dsimp only
    rw [hp, hrz, hx, hxs]
  · dsimp only
    rw [hp, hrz, hr, hrs, neg_smul, sub_eq_add_neg]
  · obtain rfl : k = j := by omega
    exact ⟨hp, hrz⟩

/-- The loop invariant of the exact run of Algorithm 11.5.1 after `f` passes. -/
private def PCGLoop (A Mi : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (f : ℕ)
    (t : PCGState n) : Prop :=
  PCGGood A Mi b x₀ t.k t ∧ t.k ≤ f ∧ (t.done = false → t.k = f) ∧
    (t.done = true → t.r ⬝ᵥ t.r = 0)

/-- The loop invariant of the exact run. -/
private theorem algorithm_11_5_1_loop (A Mi : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    PCGLoop A Mi b x₀ fuel
      (Id.run (algorithm_11_5_1 pure A (fun v => pure (Mi *ᵥ v)) b x₀ fuel)) := by
  have hrun : ∀ f, Id.run (algorithm_11_5_1 pure A (fun v => pure (Mi *ᵥ v)) b x₀ f) =
      (List.range f).foldl (fun s _ => Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) s))
        { k := 0, x := x₀, r := b - A *ᵥ x₀, z := Mi *ᵥ (b - A *ᵥ x₀), p := Mi *ᵥ (b - A *ᵥ x₀),
          rz := 1, done := false } := by
    intro f
    simp only [algorithm_11_5_1, Id.run_bind, Chapter01.algorithm_1_1_3_spec, Id.run_pure,
      List.idRun_foldlM, neg_mulVec, ← sub_eq_add_neg]
  rw [hrun]
  induction fuel with
  | zero =>
    refine ⟨⟨rfl, ?_, ?_, rfl, fun _ => rfl, fun j hj => absurd hj.symm (Nat.succ_ne_zero j)⟩,
      le_rfl, fun _ => rfl, fun h => by simp at h⟩
    · rfl
    · change b - A *ᵥ x₀ = _
      rfl
  | succ f ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set t := (List.range f).foldl (fun s _ => Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) s))
        { k := 0, x := x₀, r := b - A *ᵥ x₀, z := Mi *ᵥ (b - A *ᵥ x₀), p := Mi *ᵥ (b - A *ᵥ x₀),
          rz := 1, done := false }
    obtain ⟨hg, hle, hnd, hd⟩ := ih
    change PCGLoop A Mi b x₀ (f + 1) (Id.run (pcgStep pure A (fun v => pure (Mi *ᵥ v)) t))
    cases htd : t.done with
    | true =>
      rw [pcgStep_done A Mi t htd]
      exact ⟨hg, by omega, fun h => by simp [htd] at h, hd⟩
    | false =>
      have hk := hnd htd
      by_cases hρ : t.r ⬝ᵥ t.r = 0
      · rw [pcgStep_stop A Mi t htd hρ]
        exact ⟨hg, by dsimp only; omega, fun h => by simp at h, fun _ => hρ⟩
      · have hstep := pcgGood_step A Mi b x₀ t.k t hg htd hρ
        rw [pcgStep_go A Mi t htd hρ] at hstep ⊢
        exact ⟨hstep, by dsimp only; omega, fun _ => by dsimp only; omega,
          fun h => by simp at h⟩

/-- **Algorithm 11.5.1 computes the PCG iterates.** For symmetric positive definite `A` and `M`
and the exact solve `solveM = M⁻¹`, the exact run of at most `fuel` passes stops after `k ≤ fuel`
passes (`k = fuel` unless the test failed) in the state `x_k`, `r_k` of the backbone's
preconditioned CG iteration `Krylov.PCG.iterate` for `A` and `M` (PCG is CG for `M⁻¹A` in the
`M`-inner product); so `x_k` is the Galerkin iterate of `Ax = b` over
`x₀ + 𝒦(M⁻¹A, M⁻¹r₀, k)` — it minimizes `‖x − x_*‖_A` there — and when the loop stops by its test
`A x_k = b`: the book's "computes `x_*` so that `Ax_* = b`". -/
theorem algorithm_11_5_1_spec {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hM : Mp.PosDef) (b x₀ : Fin n → ℝ) (fuel : ℕ) :
    let s := Id.run (algorithm_11_5_1 pure A (fun v => pure (Mp⁻¹ *ᵥ v)) b x₀ fuel)
    let S := Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mp⁻¹) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) s.k
    s.k ≤ fuel ∧ (s.done = false → s.k = fuel) ∧
      WithLp.toLp 2 s.x = S.x ∧ WithLp.toLp 2 s.r = S.r ∧
      IsGalerkin (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (Krylov.subspace (toEuclideanLin Mp⁻¹ ∘ₗ toEuclideanLin A)
          (toEuclideanLin Mp⁻¹ (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))) s.k)
        (WithLp.toLp 2 s.x) ∧
      (s.done = true → A *ᵥ s.x = b) := by
  intro s S
  obtain ⟨⟨-, hx, hr, -⟩, hle, hnd, hd⟩ := algorithm_11_5_1_loop A Mp⁻¹ b x₀ fuel
  have hx' : WithLp.toLp 2 s.x = S.x := by rw [hx]
  have hr' : WithLp.toLp 2 s.r = S.r := by rw [hr]
  have hPre := hM.isPreconditioner_toEuclideanLin
  obtain ⟨c, hc, hcoer⟩ := exists_relCoercive hA Mp
  refine ⟨hle, hnd, hx', hr', ?_, fun hdone => ?_⟩
  · rw [hx']
    exact Krylov.PCG.isGalerkinIterate hPre
      (Matrix.PosDef.isSymmetricCoercive_toEuclideanLin hA).isSymmetric hc hcoer s.k
  · have h0 : s.r = 0 := by
      have := hd hdone
      rwa [dotProduct_self_eq_zero] at this
    have hres := Krylov.PCG.residual_eq (toEuclideanLin A) (toEuclideanLin Mp⁻¹)
      (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hPre s.k
    rw [← hr', ← hx', h0, toEuclideanLin_toLp] at hres
    have := congrArg WithLp.ofLp hres
    simp only [WithLp.ofLp_sub] at this
    exact (sub_eq_zero.1 this.symm).symm

/-- **(11.5.2).** "The residuals and search directions satisfy `r_jᵀM⁻¹r_i = 0`,
`p_jᵀ(C⁻¹AC⁻¹)p_i = 0` for all `i ≠ j`": for symmetric positive definite `A` and `M`, the PCG
residuals are `M⁻¹`-orthogonal and the directions `A`-conjugate. (The printed second relation holds
for the transformed directions `p̃ = Cp`; for the `p` of Algorithm 11.5.1 it is `p_jᵀAp_i = 0`.) By
`algorithm_11_5_1_spec` these are the residuals and directions of Algorithm 11.5.1. -/
theorem equation_11_5_2 {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hM : Mp.PosDef)
    (b x₀ : Fin n → ℝ) {i j : ℕ} (hij : i ≠ j) :
    let S := Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mp⁻¹) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀)
    (S j).r.ofLp ⬝ᵥ Mp⁻¹ *ᵥ (S i).r.ofLp = 0 ∧ (S j).p.ofLp ⬝ᵥ A *ᵥ (S i).p.ofLp = 0 := by
  intro S
  have hPre := hM.isPreconditioner_toEuclideanLin
  obtain ⟨c, hc, hcoer⟩ := exists_relCoercive hA Mp
  have hsym := (Matrix.PosDef.isSymmetricCoercive_toEuclideanLin hA).isSymmetric
  have h1 := Krylov.PCG.inner_inv_residual_eq_zero (b := WithLp.toLp 2 b)
    (x₀ := WithLp.toLp 2 x₀) hPre hsym hc hcoer hij
  have h2 := Krylov.PCG.inner_apply_direction_eq_zero (b := WithLp.toLp 2 b)
    (x₀ := WithLp.toLp 2 x₀) hPre hsym hc hcoer hij
  simp only [toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    at h1 h2
  exact ⟨h1, h2⟩

end PCGSpec

/-- The transport of CG on `C⁻¹ T C⁻¹` to PCG with `M⁻¹ = C⁻¹C⁻¹`, for abstract operators. -/
private theorem cg_tilde_eq_pcg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T Tt Cm Ci Mi : E →ₗ[ℝ] E) (hCiC : ∀ z, Ci (Cm z) = z) (hCCi : ∀ z, Cm (Ci z) = z)
    (hMi : ∀ z, Mi z = Ci (Ci z)) (hTt : ∀ z, Tt z = Ci (T (Ci z)))
    (hsym : ∀ u v, inner ℝ (Ci u) v = inner ℝ u (Ci v)) (b x₀ : E) (k : ℕ) :
    (CG.iterate Tt (Ci b) (Cm x₀) k).x = Cm (Krylov.PCG.iterate T Mi b x₀ k).x ∧
      (CG.iterate Tt (Ci b) (Cm x₀) k).r = Ci (Krylov.PCG.iterate T Mi b x₀ k).r ∧
      (CG.iterate Tt (Ci b) (Cm x₀) k).p = Cm (Krylov.PCG.iterate T Mi b x₀ k).p := by
  have e1 : ∀ u, inner ℝ (Ci u) (Ci u) = inner ℝ u (Mi u) := fun u => by rw [hsym, hMi]
  have e2 : ∀ u, inner ℝ (Tt (Cm u)) (Cm u) = inner ℝ (T u) u := fun u => by
    rw [hTt, hCiC, hsym, hCiC]
  induction k with
  | zero =>
    have hr0 : Ci b - Tt (Cm x₀) = Ci (b - T x₀) := by rw [hTt, hCiC, map_sub]
    refine ⟨rfl, hr0, ?_⟩
    change Ci b - Tt (Cm x₀) = Cm (Mi (b - T x₀))
    rw [hr0, hMi, hCCi]
  | succ k ih =>
    rw [CG.iterate_succ, Krylov.PCG.iterate_succ]
    obtain ⟨hx, hr, hp⟩ := ih
    have hα : CG.alpha Tt (CG.iterate Tt (Ci b) (Cm x₀) k) =
        Krylov.PCG.alpha T Mi (Krylov.PCG.iterate T Mi b x₀ k) := by
      rw [CG.alpha, Krylov.PCG.alpha, hr, hp, e1, e2]
    have hr' : (CG.step Tt (CG.iterate Tt (Ci b) (Cm x₀) k)).r =
        Ci (Krylov.PCG.step T Mi (Krylov.PCG.iterate T Mi b x₀ k)).r := by
      rw [CG.step_r, Krylov.PCG.step_r, hα, hr, hp, hTt, hCiC, map_sub, map_smul]
    have hβ : CG.beta Tt (CG.iterate Tt (Ci b) (Cm x₀) k) =
        Krylov.PCG.beta T Mi (Krylov.PCG.iterate T Mi b x₀ k) := by
      rw [CG.beta, Krylov.PCG.beta, hr', hr, e1, e1]
    refine ⟨?_, hr', ?_⟩
    · rw [CG.step_x, Krylov.PCG.step_x, hα, hx, hp, map_add, map_smul]
    · rw [CG.step_p, Krylov.PCG.step_p, hβ, hr', hp, map_add, map_smul, hMi, hCCi]

/-- **(11.5.1) and the derivation of PCG.** For `M = C²` with `C` symmetric and nonsingular (the
book's symmetric positive definite square root `C = M^{1/2}` is one such `C`), CG applied to the
"tilde" system `Ã x̃ = b̃`, `Ã = C⁻¹AC⁻¹`, `b̃ = C⁻¹b`, from `x̃₀ = C x₀`, and transported back by
`x = C⁻¹x̃`, `r = C r̃`, `p = C⁻¹p̃`, is the preconditioned CG iteration `Krylov.PCG.iterate` for
`A` with the preconditioner `M`: "in the end its action is felt only through the preconditioner
`M = C²`". The printed (11.5.1) mixes the gradient and residual sign conventions and writes
`p̃₊ = r̃_c + τp̃_c` for `r̃₊ + τp̃_c`; the statement is the consistent recurrence. -/
theorem equation_11_5_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {Mp C : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.IsSymm) (hCu : IsUnit C) (hCM : C * C = Mp) (b x₀ : Fin n → ℝ) (k : ℕ) :
    let St := CG.iterate (toEuclideanLin (C⁻¹ * A * C⁻¹)) (WithLp.toLp 2 (C⁻¹ *ᵥ b))
      (WithLp.toLp 2 (C *ᵥ x₀)) k
    let S := Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mp⁻¹) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    toEuclideanLin C⁻¹ St.x = S.x ∧ toEuclideanLin C St.r = S.r ∧
      toEuclideanLin C⁻¹ St.p = S.p := by
  intro St S
  have hCiC : ∀ z, toEuclideanLin C⁻¹ (toEuclideanLin C z) = z :=
    toEuclideanLin_nonsing_inv_mul_apply hCu
  have hCCi : ∀ z, toEuclideanLin C (toEuclideanLin C⁻¹ z) = z :=
    toEuclideanLin_mul_nonsing_inv_apply hCu
  have key := cg_tilde_eq_pcg (toEuclideanLin A) (toEuclideanLin (C⁻¹ * A * C⁻¹))
    (toEuclideanLin C) (toEuclideanLin C⁻¹) (toEuclideanLin Mp⁻¹) hCiC hCCi
    (fun z => by rw [← toEuclideanLin_mul_apply, ← Matrix.mul_inv_rev, hCM])
    (fun z => by rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply])
    (IsSymm.isSymmetric_toEuclideanLin hC.inv) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k
  rw [toEuclideanLin_toLp, toEuclideanLin_toLp] at key
  obtain ⟨hx, hr, hp⟩ := key
  exact ⟨by rw [hx, hCiC], by rw [hr, hCCi], by rw [hp, hCiC]⟩

/-! ### §11.5.3: the SSOR preconditioner -/

/-- §11.5.3: for symmetric `A = D − L − Lᵀ` with positive diagonal `D` (here `L = −(strictly lower
part of A)`, the sign convention of this subsection) and any real `ω`, the SSOR preconditioner
`M = (D − ωL) D⁻¹ (D − ωL)ᵀ` "is also symmetric positive definite and so it can be used with PCG".
For `0 < ω < 2` it is `ω(2 − ω)` times the `M` of the SSOR splitting of §11.2.7. -/
theorem ssorPreconditioner_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hd : ∀ i, 0 < A i i) (ω : ℝ) :
    ((diagPart A - ω • -strictLower A) * (diagPart A)⁻¹ *
        (diagPart A - ω • -strictLower A)ᵀ).PosDef ∧
      ∀ (h : IsUnit (diagPart A)) (hω0 : 0 < ω) (hω2 : ω < 2),
        (diagPart A - ω • -strictLower A) * (diagPart A)⁻¹ * (diagPart A - ω • -strictLower A)ᵀ =
          (ω * (2 - ω)) • (ssorSplitting A h hω0.ne' hω2.ne).m := by
  have hD : IsUnit (diagPart A) := by
    rw [diagPart, isUnit_diagonal, Pi.isUnit_iff]
    exact fun i => (hd i).ne'.isUnit
  have hX : IsUnit (diagPart A + ω • strictLower A) :=
    isUnit_diagPart_add_smul_strictLower hD ω
  have hDi : (diagPart A)⁻¹.PosDef := by
    refine PosDef.inv ?_
    rw [diagPart, posDef_diagonal_iff]
    exact hd
  simp only [smul_neg, sub_neg_eq_add]
  refine ⟨?_, fun h hω0 hω2 => ?_⟩
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact hDi.mul_mul_conjTranspose_same ((vecMul_injective_iff_isUnit).mpr hX)
  · change _ = (ω * (2 - ω)) • ((ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) *
      (diagPart A)⁻¹ * (diagPart A + ω • strictUpper A)))
    rw [smul_smul, mul_inv_cancel₀ (mul_pos hω0 (by linarith)).ne', one_smul,
      diagPart_add_smul_strictLower_transpose hA]

/-! ### §11.5.5: sparse approximate inverses -/

open scoped Matrix.Norms.Frobenius in
/-- §11.5.5: `‖AT − I‖_F² = ∑_k ‖A T(:,k) − e_k‖₂²`, so minimizing `‖AT − I‖_F` over the matrices
`T` with zero pattern prescribed by `Z` (the book's `sp(T) = Z`, read as "`T` vanishes where `Z`
does") decouples into `n` independent column problems: `T` is a minimizer exactly when each column
`T(:,k)` minimizes `‖Aτ − e_k‖₂` over the `τ` vanishing where `Z(:,k)` does. -/
theorem spai_column_decouple {n : ℕ} (A Z T : Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i k, Z i k = 0 → T i k = 0) :
    ‖A * T - 1‖ ^ 2 = ∑ k, ‖WithLp.toLp 2 ((A *ᵥ fun i => T i k) - Pi.single k 1)‖ ^ 2 ∧
      (IsMinOn (fun T' : Matrix (Fin n) (Fin n) ℝ => ‖A * T' - 1‖)
          {T' | ∀ i k, Z i k = 0 → T' i k = 0} T ↔
        ∀ k, IsMinOn (fun τ : Fin n → ℝ => ‖WithLp.toLp 2 (A *ᵥ τ - Pi.single k 1)‖)
          {τ | ∀ i, Z i k = 0 → τ i = 0} fun i => T i k) := by
  have hsum := fun T' : Matrix (Fin n) (Fin n) ℝ =>
    Preconditioner.frobenius_sq_mul_sub_one_eq_sum A T'
  refine ⟨hsum T, fun h k τ hτ => ?_, fun h T' hT' => ?_⟩
  · -- replace column `k` of `T` by `τ`
    set T' : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => if j = k then τ i else T i j
    have hT'm : T' ∈ {T' : Matrix (Fin n) (Fin n) ℝ | ∀ i k, Z i k = 0 → T' i k = 0} := by
      intro i j hz
      by_cases hj : j = k
      · subst hj; simpa [T'] using hτ i hz
      · simpa [T', hj] using hT i j hz
    have hle := h hT'm
    simp only [Set.mem_ofPred_eq] at hle
    have hsq : ‖A * T - 1‖ ^ 2 ≤ ‖A * T' - 1‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [hsum, hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsq
    have hrest : ∑ j ∈ univ.erase k, ‖WithLp.toLp 2 ((A *ᵥ fun i => T' i j) - Pi.single j 1)‖ ^ 2
        = ∑ j ∈ univ.erase k, ‖WithLp.toLp 2 ((A *ᵥ fun i => T i j) - Pi.single j 1)‖ ^ 2 :=
      Finset.sum_congr rfl fun j hj => by
        have hjk : j ≠ k := Finset.ne_of_mem_erase hj
        simp [T', hjk]
    have hcol : (fun i => T' i k) = τ := funext fun i => by simp [T']
    rw [hrest, hcol] at hsq
    change ‖WithLp.toLp 2 (A *ᵥ (fun i => T i k) - Pi.single k 1)‖ ≤
      ‖WithLp.toLp 2 (A *ᵥ τ - Pi.single k 1)‖
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  · simp only [Set.mem_ofPred_eq]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsum, hsum]
    refine Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    exact h k (show (fun i => T' i k) ∈ {τ : Fin n → ℝ | ∀ i, Z i k = 0 → τ i = 0} from
      fun i hz => hT' i k hz)

/-- §11.5.5, the reduced least-squares problem: let `cols` (`J`) be the allowed support of
`T(:,k)` and `rows` (`I`) a set of rows containing the nonzero rows of `A(:, cols)`. Then `τ`
solves `min ‖A(rows, cols) τ − e_k(rows)‖₂` exactly when `T(:,k)`, equal to `τ` on `cols` and zero
elsewhere, minimizes `‖Aτ' − e_k‖₂` over the `τ'` supported on `cols`. The book's "`T(rows, k) = τ`"
should read `T(cols, k) = τ`. -/
theorem spai_reduced_ls {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I J : Finset (Fin n)}
    (hI : ∀ i j, j ∈ J → A i j ≠ 0 → i ∈ I) (k : Fin n) {τ : J → ℝ} :
    IsMinOn (fun σ : J → ℝ => ‖WithLp.toLp 2 ((A.submatrix (Subtype.val : I → Fin n)
        (Subtype.val : J → Fin n)) *ᵥ σ - fun i : I => (Pi.single k 1 : Fin n → ℝ) i)‖) Set.univ τ ↔
      IsMinOn (fun x => ‖WithLp.toLp 2 (A *ᵥ x - Pi.single k 1)‖) {x | ∀ j ∉ J, x j = 0}
        fun j => if h : j ∈ J then τ ⟨j, h⟩ else 0 :=
  Preconditioner.isMinOn_submatrix_iff hI

/-! ### §11.5.6: polynomial preconditioners -/

/-- §11.5.6: for a splitting `A = M₁ − N₁` with `ρ(G) < 1`, `G = M₁⁻¹N₁`,
`A⁻¹ = (∑_{k=0}^∞ G^k) M₁⁻¹`. -/
theorem neumann_inv_eq_tsum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (h : s.iterationOperator.complexSpectralRadius < 1) :
    HasSum (fun k => s.iterationOperator ^ k * s.m⁻¹) A⁻¹ := by
  have hs := (hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one h).mul_right s.m⁻¹
  convert hs using 1
  rw [s.one_sub_iterationOperator, ← nonsing_inv_eq_ringInverse, Matrix.mul_inv_rev,
    nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 s.isUnit), Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 s.isUnit), Matrix.mul_one]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The truncated-Neumann loop** of §11.5.6:
```
z_c = 0
for k = 1:m
    M₁ z₊ = N₁ z_c + r
    z_c = z₊
end
z = z_c
```
The product `N₁ z_c + r` is a gaxpy (Algorithm 1.1.3); the solve with `M₁` is a routine argument
`solveM₁`. -/
def neumannLoop {n : ℕ} (solveM₁ : (Fin n → ℝ) → M (Fin n → ℝ)) (N₁ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (m : ℕ) : M (Fin n → ℝ) :=
  (List.range m).foldlM (fun z _ => do
    let w ← Chapter01.algorithm_1_1_3 rnd N₁ z r
    solveM₁ w) 0

end Programs

/-- **The truncated-Neumann loop computes the polynomial preconditioner.** With `solveM₁ = M₁⁻¹`,
`m` exact steps return `z = (I + G + ⋯ + G^{m−1}) M₁⁻¹ r`; so the preconditioner
`M⁻¹ = (∑_{k=0}^{m} G^k) M₁⁻¹` of the text needs `m + 1` steps: the printed "`m` steps" is off by
one. -/
theorem neumannLoop_spec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (r : Fin n → ℝ) (m : ℕ) :
    Id.run (neumannLoop pure (fun v => pure (s.m⁻¹ *ᵥ v)) s.n r m) =
      (∑ j ∈ range m, s.iterationOperator ^ j) *ᵥ (s.m⁻¹ *ᵥ r) := by
  simp only [neumannLoop, List.idRun_foldlM, Id.run_bind, Chapter01.algorithm_1_1_3_spec,
    Id.run_pure]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ', pow_zero, add_mulVec, one_mulVec]
    rw [add_comm r]
    change Stationary.Splitting.mulVecStep s r
      ((∑ j ∈ range m, s.iterationOperator ^ j) *ᵥ (s.m⁻¹ *ᵥ r)) = _
    rw [Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add, mulVec_mulVec,
      Finset.mul_sum]
    congr 3
    exact funext fun j => (pow_succ' s.iterationOperator j).symm

/-- **(11.5.3) and the paragraph after it.** For `M⁻¹ = p(M₁⁻¹A) M₁⁻¹` the preconditioned matrix is
`M⁻¹A = p(B) B` with `B = M₁⁻¹A`; with `M₁ = I`, `I − p(A)A = q(A)` for `q(z) = 1 − z p(z)`, which
has `q(0) = 1` and degree `deg p + 1`; and the truncated Neumann choice `p = ∑_{j≤m} (1 − z)^j`
(after `M₁`) gives `M⁻¹A = I − G^{m+1}`, `G = I − M₁⁻¹A`. -/
theorem equation_11_5_3 {n : ℕ} (A M₁ : Matrix (Fin n) (Fin n) ℝ) (p : Polynomial ℝ) (m : ℕ) :
    Polynomial.aeval (M₁⁻¹ * A) p * M₁⁻¹ * A = Polynomial.aeval (M₁⁻¹ * A) p * (M₁⁻¹ * A) ∧
      (1 - Polynomial.aeval A p * A = Polynomial.aeval A (1 - Polynomial.X * p) ∧
        (1 - Polynomial.X * p).eval 0 = 1 ∧
        (p ≠ 0 → (1 - Polynomial.X * p).natDegree = p.natDegree + 1)) ∧
      Preconditioner.neumannPolyOf (1 - M₁⁻¹ * A) m * M₁⁻¹ * A = 1 - (1 - M₁⁻¹ * A) ^ (m + 1) := by
  refine ⟨Matrix.mul_assoc _ _ _, ⟨?_, by simp, fun hp => ?_⟩, ?_⟩
  · simp [map_sub, Polynomial.aeval_X, (Commute.all _ _).eq]
  · have h1 : (Polynomial.X * p).natDegree = p.natDegree + 1 := by
      rw [mul_comm, Polynomial.natDegree_mul_X hp]
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by rw [h1]; simp), h1]
  · rw [Matrix.mul_assoc, Preconditioner.neumannPoly_mul_eq]

/-! ### §11.5.7: PCG as an accelerated splitting -/

/-- **(11.5.4)** at `ω_k = γ_k = 1`: the step `x_k = x_{k−2} + ω_k(γ_{k−1} z_{k−1} + x_{k−1} −
x_{k−2})` with `M z_{k−1} = b − A x_{k−1}` is `M x_k = N x_{k−1} + b` (`A = M − N`), the step of the
splitting. -/
theorem equation_11_5_4 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (b x₁ x₂ z : Fin n → ℝ) (hz : s.m *ᵥ z = b - A *ᵥ x₁) :
    x₂ + (1 : ℝ) • ((1 : ℝ) • z + x₁ - x₂) = s.mulVecStep b x₁ := by
  rw [Stationary.Splitting.mulVecStep_eq_add_inv_mulVec,
    nonsing_inv_mulVec_eq s.isUnit hz, one_smul, one_smul]
  abel

/-! ### §11.5.7: the Concus–Golub–O'Leary form of PCG -/

/-- The state of the Concus–Golub–O'Leary loop after `k` passes: `x_{k−1}`, `x_k`, `r_k`, and the
last `γ_{k−1}`, `z_{k−1}ᵀMz_{k−1}` and `ω_k`. -/
structure CGOState (n : ℕ) where
  /-- The iteration count `k`. -/
  k : ℕ
  /-- The previous iterate `x_{k−1}` (the book's `x_{−1} = 0` at `k = 0`). -/
  xPrev : Fin n → ℝ
  /-- The iterate `x_k`. -/
  x : Fin n → ℝ
  /-- The residual `r_k = b − Ax_k`. -/
  r : Fin n → ℝ
  /-- The last `γ_{k−1}`. -/
  gam : ℝ
  /-- The last `z_{k−1}ᵀMz_{k−1}`. -/
  zMz : ℝ
  /-- The last `ω_k`. -/
  om : ℝ
  /-- Whether the test `r_k ≠ 0` has failed. -/
  done : Bool

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of the Concus–Golub–O'Leary loop (§11.5.7). -/
noncomputable def cgoStep {n : ℕ} (A Mp : Matrix (Fin n) (Fin n) ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (b : Fin n → ℝ) (s : CGOState n) :
    M (CGOState n) := do
  if s.done then return s
  if s.r = 0 then return { s with done := true }
  let z ← solveM s.r
  let Mz ← Chapter01.algorithm_1_1_3 rnd Mp z 0
  let zMz ← Chapter01.algorithm_1_1_1 rnd z Mz
  let Az ← Chapter01.algorithm_1_1_3 rnd A z 0
  let zAz ← Chapter01.algorithm_1_1_1 rnd z Az
  let γ ← rnd (zMz / zAz)
  let om ← if s.k = 0 then pure 1 else do
    let t₁ ← rnd (γ / s.gam)
    let t₂ ← rnd (zMz / s.zMz)
    let t₃ ← rnd (t₁ * t₂)
    let t₄ ← rnd (t₃ / s.om)
    let t₅ ← rnd (1 - t₄)
    rnd (1 / t₅)
  let u ← Chapter01.vecSub rnd s.x s.xPrev
  let w ← Chapter01.algorithm_1_1_2 rnd γ z u
  let x ← Chapter01.algorithm_1_1_2 rnd om w s.xPrev
  let r ← Chapter01.algorithm_1_1_3 rnd (-A) x b
  return ⟨s.k + 1, s.x, x, r, γ, zMz, om, false⟩

/-- **The Concus–Golub–O'Leary form of PCG** (§11.5.7; the display is untagged in the source and
is taken to be the lost (11.5.5)):
```
x_{−1} = 0, k = 0, r₀ = b − Ax₀
while r_k ≠ 0
    k = k + 1
    Solve M z_{k−1} = r_{k−1}
    γ_{k−1} = z_{k−1}ᵀMz_{k−1} / z_{k−1}ᵀAz_{k−1}
    if k = 1, ω₁ = 1
    else ω_k = (1 − (γ_{k−1}/γ_{k−2}) (z_{k−1}ᵀMz_{k−1} / z_{k−2}ᵀMz_{k−2}) / ω_{k−1})⁻¹
    x_k = x_{k−2} + ω_k(γ_{k−1} z_{k−1} + x_{k−1} − x_{k−2})
    r_k = b − Ax_k
end
```
The test `r_k ≠ 0` compares the computed vector with zero exactly; the solves with `M` are the
routine `solveM`, and the `while` loop runs at most `fuel` passes. -/
noncomputable def concusGolubOLearyPCG {n : ℕ} (A Mp : Matrix (Fin n) (Fin n) ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (b x₀ : Fin n → ℝ) (fuel : ℕ) : M (CGOState n) := do
  let r₀ ← Chapter01.algorithm_1_1_3 rnd (-A) x₀ b
  (List.range fuel).foldlM (fun s _ => cgoStep rnd A Mp solveM b s)
    { k := 0, xPrev := 0, x := x₀, r := r₀, gam := 1, zMz := 1, om := 1, done := false }

end Programs

section CGOSpec

variable {n : ℕ}

/-- An exact pass after the test failed is the identity. -/
private theorem cgoStep_done (A Mp Mi : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (s : CGOState n) (h : s.done = true) :
    Id.run (cgoStep pure A Mp (fun v => pure (Mi *ᵥ v)) b s) = s := by
  simp [cgoStep, h]

/-- An exact pass meeting `r_k = 0` stops. -/
private theorem cgoStep_stop (A Mp Mi : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (s : CGOState n) (h : s.done = false) (hr : s.r = 0) :
    Id.run (cgoStep pure A Mp (fun v => pure (Mi *ᵥ v)) b s) = { s with done := true } := by
  simp [cgoStep, h, hr]

/-- An exact pass with `r_k ≠ 0`. -/
private theorem cgoStep_go (A Mp Mi : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (s : CGOState n) (h : s.done = false) (hr : s.r ≠ 0) :
    Id.run (cgoStep pure A Mp (fun v => pure (Mi *ᵥ v)) b s) =
      let z := Mi *ᵥ s.r
      let γ := (z ⬝ᵥ Mp *ᵥ z) / (z ⬝ᵥ A *ᵥ z)
      let om := if s.k = 0 then 1 else 1 / (1 - γ / s.gam * ((z ⬝ᵥ Mp *ᵥ z) / s.zMz) / s.om)
      let x := s.xPrev + om • (s.x - s.xPrev + γ • z)
      { k := s.k + 1, xPrev := s.x, x := x, r := b + (-A) *ᵥ x, gam := γ,
        zMz := z ⬝ᵥ Mp *ᵥ z, om := om, done := false } := by
  by_cases hk : s.k = 0 <;>
    simp [cgoStep, h, hr, hk, Chapter01.algorithm_1_1_1_spec, Chapter01.algorithm_1_1_2_spec,
      Chapter01.algorithm_1_1_3_spec, Chapter01.vecSub_spec]

/-- The preconditioned PCG residuals `z_j = M⁻¹ r_j`. -/
private noncomputable def cgoZ (A Mp : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ) :
    Fin n → ℝ :=
  Mp⁻¹ *ᵥ (pcgIter A Mp⁻¹ b x₀ j).r.ofLp

/-- The scalars `γ_j = z_jᵀMz_j / z_jᵀAz_j`. -/
private noncomputable def cgoGam (A Mp : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ) :
    ℝ :=
  (cgoZ A Mp b x₀ j ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ j) / (cgoZ A Mp b x₀ j ⬝ᵥ A *ᵥ cgoZ A Mp b x₀ j)

/-- The scalars `ω_{j+1}`: `CG.rho` of `M⁻¹A` in the `M`-inner product. -/
private noncomputable def cgoRho (A Mp : Matrix (Fin n) (Fin n) ℝ) (hM : Mp.PosDef)
    (b x₀ : Fin n → ℝ) : ℕ → ℝ :=
  CG.rho (hM.isPreconditioner_toEuclideanLin.energyEnd
      (toEuclideanLin Mp⁻¹ ∘ₗ toEuclideanLin A))
    (hM.isPreconditioner_toEuclideanLin.toEnergy (toEuclideanLin Mp⁻¹ (WithLp.toLp 2 b)))
    (hM.isPreconditioner_toEuclideanLin.toEnergy (WithLp.toLp 2 x₀))

/-- The facts about PCG in the `M`-inner product that the Concus–Golub–O'Leary recurrence uses:
the three-term recurrence of the iterates and the recurrence of `ω`. -/
private theorem cgo_threeTerm {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hM : Mp.PosDef)
    (b x₀ : Fin n → ℝ) (m : ℕ) (hr : ∀ j ≤ m, (pcgIter A Mp⁻¹ b x₀ j).r ≠ 0) :
    (pcgIter A Mp⁻¹ b x₀ (m + 1)).x.ofLp =
      cgoRho A Mp hM b x₀ m • ((pcgIter A Mp⁻¹ b x₀ m).x.ofLp +
        cgoGam A Mp b x₀ m • cgoZ A Mp b x₀ m) +
        (1 - cgoRho A Mp hM b x₀ m) • (pcgIter A Mp⁻¹ b x₀ (m - 1)).x.ofLp ∧
      cgoRho A Mp hM b x₀ 0 = 1 ∧
      ∀ j, cgoRho A Mp hM b x₀ (j + 1) = (1 - cgoGam A Mp b x₀ (j + 1) / cgoGam A Mp b x₀ j *
        ((cgoZ A Mp b x₀ (j + 1) ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ (j + 1)) /
          (cgoZ A Mp b x₀ j ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ j)) / cgoRho A Mp hM b x₀ j)⁻¹ := by
  have hPre := hM.isPreconditioner_toEuclideanLin
  obtain ⟨c, hc, hcoer⟩ := exists_relCoercive hA Mp
  have hK := hPre.isSymmetricCoercive_energyEnd (toEuclideanLin A)
    (Matrix.PosDef.isSymmetricCoercive_toEuclideanLin hA).isSymmetric hc hcoer
  have hcg := fun j => Krylov.PCG.iterate_eq_CG_iterate_withEnergy (toEuclideanLin A)
    (toEuclideanLin Mp⁻¹) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hPre j
  -- the CG residual in the `M`-inner product is the preconditioned residual
  have hZ : ∀ j, hPre.toEnergy (WithLp.toLp 2 (cgoZ A Mp b x₀ j)) =
      (CG.iterate (hPre.energyEnd (toEuclideanLin Mp⁻¹ ∘ₗ toEuclideanLin A))
        (hPre.toEnergy (toEuclideanLin Mp⁻¹ (WithLp.toLp 2 b)))
        (hPre.toEnergy (WithLp.toLp 2 x₀)) j).r := fun j => (hcg j).2.1
  have hγ : ∀ j, CG.gamma (hPre.energyEnd (toEuclideanLin Mp⁻¹ ∘ₗ toEuclideanLin A))
      (hPre.toEnergy (toEuclideanLin Mp⁻¹ (WithLp.toLp 2 b))) (hPre.toEnergy (WithLp.toLp 2 x₀)) j
        = cgoGam A Mp b x₀ j := by
    intro j
    rw [CG.gamma, ← hZ, hPre.energyEnd_apply, LinearMap.comp_apply, WithEnergy.inner_equiv,
      WithEnergy.inner_equiv, energyInner, energyInner, hPre.apply_inv]
    simp only [toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial]
    rfl
  have hnorm : ∀ j, ‖(CG.iterate (hPre.energyEnd (toEuclideanLin Mp⁻¹ ∘ₗ toEuclideanLin A))
      (hPre.toEnergy (toEuclideanLin Mp⁻¹ (WithLp.toLp 2 b)))
      (hPre.toEnergy (WithLp.toLp 2 x₀)) j).r‖ ^ 2 =
        cgoZ A Mp b x₀ j ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ j := by
    intro j
    rw [← hZ, hPre.norm_toEnergy_sq, RCLike.re_to_real, toEuclideanLin_toLp,
      EuclideanSpace.inner_toLp_toLp, star_trivial]
  have hrK : ∀ j ≤ m, (CG.iterate (hPre.energyEnd (toEuclideanLin Mp⁻¹ ∘ₗ toEuclideanLin A))
      (hPre.toEnergy (toEuclideanLin Mp⁻¹ (WithLp.toLp 2 b)))
      (hPre.toEnergy (WithLp.toLp 2 x₀)) j).r ≠ 0 := by
    intro j hj h0
    apply hr j hj
    have h1 := (hcg j).2.1
    rw [h0, LinearEquiv.map_eq_zero_iff] at h1
    have := hPre.apply_inv (pcgIter A Mp⁻¹ b x₀ j).r
    rw [h1, map_zero] at this
    exact this.symm
  refine ⟨?_, by rw [cgoRho, CG.rho], fun j => ?_⟩
  · have h3 := CG.iterate_succ_eq_three_term _ _ hK m hrK
    simp only [← (hcg (m + 1)).1, ← (hcg m).1, ← (hcg (m - 1)).1, ← hZ, hγ] at h3
    have h4 := congrArg (fun u => (hPre.toEnergy.symm u).ofLp) h3
    simp only [map_add, map_smul, LinearEquiv.symm_apply_apply, WithLp.ofLp_add,
      WithLp.ofLp_smul] at h4
    exact h4
  · rw [cgoRho, CG.rho, hγ, hγ, hnorm, hnorm]
    rfl

/-- The book's state after `k` exact passes of the Concus–Golub–O'Leary loop, read off the PCG
iterates. -/
private def CGOGood (A Mp : Matrix (Fin n) (Fin n) ℝ) (hM : Mp.PosDef) (b x₀ : Fin n → ℝ)
    (k : ℕ) (s : CGOState n) : Prop :=
  s.k = k ∧ s.x = (pcgIter A Mp⁻¹ b x₀ k).x.ofLp ∧ s.r = (pcgIter A Mp⁻¹ b x₀ k).r.ofLp ∧
    (∀ j < k, (pcgIter A Mp⁻¹ b x₀ j).r ≠ 0) ∧ (k = 0 → s.xPrev = 0) ∧
    ∀ j, k = j + 1 → s.xPrev = (pcgIter A Mp⁻¹ b x₀ j).x.ofLp ∧
      s.gam = cgoGam A Mp b x₀ j ∧ s.zMz = cgoZ A Mp b x₀ j ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ j ∧
      s.om = cgoRho A Mp hM b x₀ j

/-- A pass of the loop with `r_k ≠ 0` advances the state by one PCG step. -/
private theorem cgoGood_step {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hM : Mp.PosDef)
    (b x₀ : Fin n → ℝ) (k : ℕ) (s : CGOState n) (hs : CGOGood A Mp hM b x₀ k s)
    (h : s.done = false) (hr : s.r ≠ 0) :
    CGOGood A Mp hM b x₀ (k + 1)
      (Id.run (cgoStep pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b s)) := by
  obtain ⟨hk, hx, hrr, hnz, hp0, hps⟩ := hs
  have hRk : (pcgIter A Mp⁻¹ b x₀ k).r ≠ 0 := fun h0 => hr (by rw [hrr, h0]; rfl)
  have hnz' : ∀ j ≤ k, (pcgIter A Mp⁻¹ b x₀ j).r ≠ 0 := fun j hj => by
    rcases hj.lt_or_eq with hj | rfl
    · exact hnz j hj
    · exact hRk
  obtain ⟨h3, hρ0, hρs⟩ := cgo_threeTerm hA hM b x₀ k hnz'
  have hres : (pcgIter A Mp⁻¹ b x₀ (k + 1)).r =
      WithLp.toLp 2 b - toEuclideanLin A (pcgIter A Mp⁻¹ b x₀ (k + 1)).x :=
    Krylov.PCG.residual_eq (toEuclideanLin A) (toEuclideanLin Mp⁻¹) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) hM.isPreconditioner_toEuclideanLin (k + 1)
  have hz : Mp⁻¹ *ᵥ s.r = cgoZ A Mp b x₀ k := by rw [hrr]; rfl
  rw [cgoStep_go A Mp Mp⁻¹ b s h hr]
  simp only [hz]
  have hγk : (cgoZ A Mp b x₀ k ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ k) / (cgoZ A Mp b x₀ k ⬝ᵥ A *ᵥ
      cgoZ A Mp b x₀ k) = cgoGam A Mp b x₀ k := rfl
  rw [hγk]
  -- the new `ω` is `ω_{k+1}`
  have hω : (if s.k = 0 then 1 else 1 / (1 - cgoGam A Mp b x₀ k / s.gam *
      ((cgoZ A Mp b x₀ k ⬝ᵥ Mp *ᵥ cgoZ A Mp b x₀ k) / s.zMz) / s.om)) =
      cgoRho A Mp hM b x₀ k := by
    rcases k with _ | j
    · rw [ite_eq_left hk, hρ0]
    · obtain ⟨-, hγp, hzp, hop⟩ := hps j rfl
      rw [ite_eq_right (by omega), hγp, hzp, hop, hρs j, one_div]
  rw [hω]
  -- the new iterate is the PCG iterate
  have hxnew : s.xPrev + cgoRho A Mp hM b x₀ k • (s.x - s.xPrev +
      cgoGam A Mp b x₀ k • cgoZ A Mp b x₀ k) = (pcgIter A Mp⁻¹ b x₀ (k + 1)).x.ofLp := by
    rw [h3, hx]
    rcases k with _ | j
    · rw [hp0 rfl, hρ0]
      simp
    · obtain ⟨hxp, -⟩ := hps j rfl
      rw [hxp, Nat.add_sub_cancel]
      module
  refine ⟨by simp [hk], hxnew, ?_, fun j hj => ?_, fun h0 => absurd h0 (Nat.succ_ne_zero k),
    fun j hj => ?_⟩
  · dsimp only
    rw [hxnew, hres]
    simp [toEuclideanLin_apply, neg_mulVec, ← sub_eq_add_neg]
  · rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | rfl
    · exact hnz j hj
    · exact hRk
  · obtain rfl : k = j := by omega
    exact ⟨hx, rfl, rfl, rfl⟩

/-- The loop invariant of the exact run of the Concus–Golub–O'Leary loop after `f` passes. -/
private def CGOLoop (A Mp : Matrix (Fin n) (Fin n) ℝ) (hM : Mp.PosDef) (b x₀ : Fin n → ℝ)
    (f : ℕ) (t : CGOState n) : Prop :=
  CGOGood A Mp hM b x₀ t.k t ∧ t.k ≤ f ∧ (t.done = false → t.k = f) ∧ (t.done = true → t.r = 0)

/-- The loop invariant of the exact run. -/
private theorem concusGolubOLearyPCG_loop {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hM : Mp.PosDef) (b x₀ : Fin n → ℝ) (fuel : ℕ) :
    CGOLoop A Mp hM b x₀ fuel
      (Id.run (concusGolubOLearyPCG pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b x₀ fuel)) := by
  have hrun : ∀ f, Id.run (concusGolubOLearyPCG pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b x₀ f) =
      (List.range f).foldl
        (fun s _ => Id.run (cgoStep pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b s))
        { k := 0, xPrev := 0, x := x₀, r := b - A *ᵥ x₀, gam := 1, zMz := 1, om := 1,
          done := false } := by
    intro f
    simp only [concusGolubOLearyPCG, Id.run_bind, Chapter01.algorithm_1_1_3_spec,
      List.idRun_foldlM, neg_mulVec, ← sub_eq_add_neg]
  rw [hrun]
  induction fuel with
  | zero =>
    refine ⟨⟨rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl,
      fun j hj => absurd hj.symm (Nat.succ_ne_zero j)⟩, le_rfl, fun _ => rfl,
      fun h => by simp at h⟩
  | succ f ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set t := (List.range f).foldl
      (fun s _ => Id.run (cgoStep pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b s))
      { k := 0, xPrev := 0, x := x₀, r := b - A *ᵥ x₀, gam := 1, zMz := 1, om := 1, done := false }
    obtain ⟨hg, hle, hnd, hd⟩ := ih
    change CGOLoop A Mp hM b x₀ (f + 1)
      (Id.run (cgoStep pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b t))
    cases htd : t.done with
    | true =>
      rw [cgoStep_done A Mp Mp⁻¹ b t htd]
      exact ⟨hg, by omega, fun h => by simp [htd] at h, hd⟩
    | false =>
      have hk := hnd htd
      by_cases hr : t.r = 0
      · rw [cgoStep_stop A Mp Mp⁻¹ b t htd hr]
        exact ⟨hg, by dsimp only; omega, fun h => by simp at h, fun _ => hr⟩
      · have hstep := cgoGood_step hA hM b x₀ t.k t hg htd hr
        rw [cgoStep_go A Mp Mp⁻¹ b t htd hr] at hstep ⊢
        exact ⟨hstep, by dsimp only; omega, fun _ => by dsimp only; omega,
          fun h => by simp at h⟩

/-- **The Concus–Golub–O'Leary loop computes the PCG iterates** (the exact semantics of the
display taken as (11.5.5)): for symmetric positive definite `A` and `M` and the exact solve
`solveM = M⁻¹`, the run of at most `fuel` passes stops after `k ≤ fuel` passes (`k = fuel` unless
`r_k = 0`) at the PCG iterate `x_k` of `Krylov.PCG.iterate`, and on exit by the test `A x_k = b`.
So "any iterative method based on the splitting `A = M − N` can be accelerated by the conjugate
gradient algorithm as long as `M` is symmetric positive definite". The coefficients are the
three-term form of CG (`CG.iterate_succ_eq_three_term`) for `M⁻¹A` in the `M`-inner product:
`γ_k` is `CG.gamma` and `ω_{k+1}` is `CG.rho`. -/
theorem equation_11_5_5 {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hM : Mp.PosDef)
    (b x₀ : Fin n → ℝ) (fuel : ℕ) :
    let s := Id.run (concusGolubOLearyPCG pure A Mp (fun v => pure (Mp⁻¹ *ᵥ v)) b x₀ fuel)
    s.k ≤ fuel ∧ (s.done = false → s.k = fuel) ∧
      WithLp.toLp 2 s.x = (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mp⁻¹)
        (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).x ∧
      (s.done = true → A *ᵥ s.x = b) := by
  intro s
  obtain ⟨⟨-, hx, hr, -⟩, hle, hnd, hd⟩ := concusGolubOLearyPCG_loop hA hM b x₀ fuel
  have hx' : WithLp.toLp 2 s.x = (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mp⁻¹)
      (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).x := by rw [hx]
  have hr' : WithLp.toLp 2 s.r = (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin Mp⁻¹)
      (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).r := by rw [hr]
  refine ⟨hle, hnd, hx', fun hdone => ?_⟩
  have hres := Krylov.PCG.residual_eq (toEuclideanLin A) (toEuclideanLin Mp⁻¹) (WithLp.toLp 2 b)
    (WithLp.toLp 2 x₀) hM.isPreconditioner_toEuclideanLin s.k
  rw [← hr', ← hx', hd hdone, toEuclideanLin_toLp] at hres
  have := congrArg WithLp.ofLp hres
  simp only [WithLp.ofLp_sub] at this
  exact (sub_eq_zero.1 this.symm).symm

end CGOSpec

/-! ### §11.5.8: incomplete Cholesky -/

/-- **The incomplete Cholesky factor** of (11.5.6)–(11.5.8): for a set `P` of subdiagonal index
pairs, `H` is lower triangular, `R = HHᵀ − A` vanishes wherever `A` does not ((11.5.6)–(11.5.7):
"`a_ij ≠ 0 ⇒ r_ij = 0`"), and `H` vanishes on `P` ((11.5.8)). -/
structure IsIncompleteCholesky {n : ℕ} (P : Set (Fin n × Fin n))
    (A H : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- `H` is lower triangular. -/
  lower : ∀ i j, i < j → H i j = 0
  /-- (11.5.7): `[HHᵀ]_ij = a_ij` for every nonzero `a_ij`. -/
  agree : ∀ i j, A i j ≠ 0 → (H * Hᵀ - A) i j = 0
  /-- (11.5.8): `(i, j) ∈ P ⇒ h_ij = 0`. -/
  zero : ∀ i j, (i, j) ∈ P → H i j = 0

/-- The backbone's incomplete Cholesky factor gives the book's when the pattern avoids the
nonzeros of `A`: for symmetric `A` and a set `P` of positions where `A` vanishes, a
`Matrix.IsIC (P ∪ Pᵀ) A H` factor satisfies (11.5.6)–(11.5.8). (The converse fails: (11.5.7) does
not constrain `HHᵀ` at the zeros of `A` outside `P`.) -/
theorem isIncompleteCholesky_of_isIC {n : ℕ} {P : Set (Fin n × Fin n)}
    {A H : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hP : ∀ i j, (i, j) ∈ P → A i j = 0)
    (h : IsIC (P ∪ {x | x.swap ∈ P}) A H) : IsIncompleteCholesky P A H where
  lower := h.l_eq_zero_of_lt
  agree := fun i j hij => by
    rw [Matrix.sub_apply, h.agree i j ?_, sub_self]
    rintro (hm | hm)
    · exact hij (hP i j hm)
    · exact hij (by rw [hA.apply j i]; exact hP j i hm)
  zero := fun i j hij => h.l_eq_zero_of_mem i j (Or.inl hij)

/-- **(11.5.9) and the sentence after it.** For `A = [α vᵀ; v B]` with `α > 0`, `w = v/√α` and
`A₁ = B − wwᵀ`: `A = [√α 0; w I] [1 0; 0 A₁] [√α wᵀ; 0 I]`; and if `G₁` is the Cholesky factor of
`A₁` then `G = [√α 0; w G₁]` is the Cholesky factor of `A`. In the second clause `A` is a matrix
on `Fin (n+1)` with pivot `0`, trailing block `B = A(2:n, 2:n)`, and the factors are written
upper, `H = Gᵀ` (`Matrix.IsCholesky A₁ H₁`). -/
theorem equation_11_5_9 {n : ℕ} {α : ℝ} (hα : 0 < α) (v : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    fromBlocks (of fun _ _ => α) (of fun (_ : Fin 1) j => v j) (of fun i (_ : Fin 1) => v i) B =
        fromBlocks (of fun _ _ => √α) 0 (of fun i (_ : Fin 1) => v i / √α) 1 *
          fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
            (B - vecMulVec (fun i => v i / √α) fun i => v i / √α) *
          fromBlocks (of fun _ _ => √α) (of fun (_ : Fin 1) j => v j / √α) 0 1 := by
  have e : B - vecMulVec (fun i => v i / √α) (fun i => v i / √α) = B - α⁻¹ • vecMulVec v v := by
    ext i j
    simp only [Matrix.sub_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, div_mul_div_comm,
      Real.mul_self_sqrt hα.le]
    ring
  rw [e]
  exact (equation_11_1_3 hα v B).1

/-- The Cholesky clause of (11.5.9): with `A` on `Fin (n+1)` symmetric, `α = a₁₁ > 0`,
`w = A(2:n, 1)/√α`, if `H₁` is the (upper) Cholesky factor of `A₁ = A(2:n,2:n) − wwᵀ` then the
bordered `H = [√α wᵀ; 0 H₁]` is the Cholesky factor of `A` (the book's `G = Hᵀ = [√α 0; w G₁]`). -/
theorem equation_11_5_9_cholesky {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsSymm) (hα : 0 < A 0 0) {H₁ : Matrix (Fin n) (Fin n) ℝ}
    (h₁ : (Matrix.of fun i j : Fin n =>
      A i.succ j.succ - A i.succ 0 / √(A 0 0) * (A j.succ 0 / √(A 0 0))).IsCholesky H₁) :
    A.IsCholesky (Matrix.of fun i j : Fin (n + 1) =>
      Fin.cases (Fin.cases (√(A 0 0)) (fun j' => A j'.succ 0 / √(A 0 0)) j)
        (fun i' => Fin.cases 0 (fun j' => H₁ i' j') j) i) := by
  have hs : √(A 0 0) * √(A 0 0) = A 0 0 := Real.mul_self_sqrt hα.le
  have hs0 : √(A 0 0) ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · induction i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp
      | succ j => simpa using h₁.isUpperTriangular (Fin.succ_lt_succ_iff.1 hij)
  · induction i using Fin.cases with
    | zero => simpa using Real.sqrt_pos.2 hα
    | succ i => simpa using h₁.diag_pos i
  · have hH := h₁.conjTranspose_mul_self
    rw [conjTranspose_eq_transpose_of_trivial] at hH
    ext i j
    rw [conjTranspose_eq_transpose_of_trivial, mul_apply, Fin.sum_univ_succ]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [hs]
      | succ j =>
        simp only [transpose_apply, of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul,
          Finset.sum_const_zero, add_zero]
        rw [hA.apply j.succ 0]
        field_simp
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [transpose_apply, of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero,
          Finset.sum_const_zero, add_zero]
        field_simp
      | succ j =>
        have := congrFun (congrFun hH i) j
        simp only [mul_apply, transpose_apply, of_apply] at this
        simp only [transpose_apply, of_apply, Fin.cases_succ, Fin.cases_zero, this]
        ring

/-- **Lemma 11.5.1.** "If `A ∈ ℝ^{n×n}` is a Stieltjes matrix, then `A⁻¹ ≥ 0`." A Stieltjes matrix
(symmetric positive definite with nonpositive off-diagonal entries, §11.5.8) is an M-matrix, whose
inverse is entrywise nonnegative. -/
theorem lemma_11_5_1 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsStieltjes) :
    A⁻¹.EntrywiseNonneg :=
  hA.inv_entrywiseNonneg

/-- **Theorem 11.5.2.** "If `A = [α vᵀ; v B]` is a Stieltjes matrix and `ṽ` is obtained from `v` by
setting any subset of its components to zero, then `B̃ = B − ṽṽᵀ/α` is a Stieltjes matrix." Here
`A` is on `Fin (n+1)` with pivot `0`, `v = A(2:n, 1)`, and `ṽ` keeps the components in `S`. -/
theorem theorem_11_5_2 {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsStieltjes)
    (S : Finset (Fin n)) :
    (Matrix.of fun i j : Fin n => A i.succ j.succ -
      (if i ∈ S then A i.succ 0 else 0) * (if j ∈ S then A j.succ 0 else 0) /
        A 0 0).IsStieltjes := by
  classical
  set S' : Set {i : Fin (n + 1) // i ≠ 0} := {x | ∃ i ∈ S, x.1 = i.succ} with hS'
  have h := (hA.isStieltjes_sub_drop 0 S').submatrix
    (e := fun i : Fin n => (⟨i.succ, Fin.succ_ne_zero i⟩ : {i : Fin (n + 1) // i ≠ 0}))
    (fun a b e => Fin.succ_injective _ (congrArg Subtype.val e))
  have hmem : ∀ i : Fin n, (⟨i.succ, Fin.succ_ne_zero i⟩ : {i : Fin (n + 1) // i ≠ 0}) ∈ S' ↔
      i ∈ S := fun i => ⟨fun ⟨i', hi', he⟩ => Fin.succ_injective _ he ▸ hi', fun hi => ⟨i, hi, rfl⟩⟩
  convert h using 1
  ext i j
  simp only [of_apply, submatrix_apply, hmem, hA.isSymm.apply 0 j.succ]

/-- §11.5.8, "the model problem matrices in §4.8.3 are Stieltjes matrices": `T_m = tridiag(−1, 2,
−1)` and the Poisson matrix `I ⊗ T_{n₂} + T_{n₁} ⊗ I` of (11.2.10) are Stieltjes. -/
theorem poissonMatrix_isStieltjes (m n₁ n₂ : ℕ) :
    (modelT m).IsStieltjes ∧ (poissonMatrix n₁ n₂).IsStieltjes := by
  have hT : ∀ m (i j : Fin m), i ≠ j → modelT m i j ≤ 0 := by
    intro m i j hij
    simp only [modelT, symmTridiagonalToeplitz_apply, hij, ite_false]
    split_ifs <;> norm_num
  refine ⟨⟨posDef_symmTridiagonalToeplitz_neg_one_two m, hT m⟩,
    ⟨poissonMatrix_posDef n₁ n₂, ?_⟩⟩
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ hij
  simp only [poissonMatrix, kroneckerSum_apply]
  by_cases h₂ : i₂ = j₂
  · have h₁ : i₁ ≠ j₁ := fun h => hij (by rw [h, h₂])
    simp [h₂, h₁, hT _ _ _ h₁]
  · by_cases h₁ : i₁ = j₁
    · simp [h₂, h₁, hT _ _ _ h₂]
    · simp [h₂, h₁]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The recursive incomplete Cholesky `incChol(A, Z, n)`** of §11.5.8:
```
function H = incChol(A, Z, n)
if n = 1
    H = √A
else
    α = A(1,1), v = A(2:n,1), B = A(2:n,2:n)
    w = (v/√α) .* Z(2:n,1)
    A₁ = (B − wwᵀ) .* Z(2:n,2:n), H₁ = incChol(A₁, Z(2:n,2:n), n−1)
    H = [√α 0; w H₁]
end
```
The masking `.* Z` by the `0–1` matrix `Z` is exact (an entry is kept or set to zero), and the
entries it sets to zero are not computed; every `√`, `/`, product and difference is rounded. The
matrix size is `n + 1` (the book's `n`), the trailing block `A(2:n, 2:n)` is
`A.submatrix Fin.succ Fin.succ`, and `[√α 0; w H₁]` is assembled by `Fin.cases`. -/
noncomputable def incChol : {n : ℕ} → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ → M (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  | 0, A, _ => do
    let h ← rnd (√(A 0 0))
    pure (Matrix.of fun _ _ => h)
  | n + 1, A, Z => do
    let d ← rnd (√(A 0 0))
    let w ← (List.finRange (n + 1)).foldlM (fun (w : Fin (n + 1) → ℝ) i => do
      let q ← if Z i.succ 0 = 0 then pure 0 else rnd (A i.succ 0 / d)
      pure (Function.update w i q)) 0
    let A₁ ← (List.finRange (n + 1)).foldlM (fun (A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i =>
      (List.finRange (n + 1)).foldlM (fun (A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) j => do
        let t ← if Z i.succ j.succ = 0 then pure 0 else do
          let p ← rnd (w i * w j)
          rnd (A i.succ j.succ - p)
        pure (A₁.updateRow i (Function.update (A₁ i) j t))) A₁) 0
    let H₁ ← incChol A₁ (Z.submatrix Fin.succ Fin.succ)
    pure (Matrix.of fun i j => Fin.cases (Fin.cases d (fun _ => 0) j)
      (fun i' => Fin.cases (w i') (fun j' => H₁ i' j') j) i)

end Programs

/-- A loop writing entry `i` of a vector at step `i` of `finRange` computes the whole vector. -/
private theorem foldl_finRange_update {m : ℕ} {β : Type} (g : Fin m → β) (w₀ : Fin m → β) :
    (List.finRange m).foldl (fun w i => Function.update w i (g i)) w₀ = g :=
  (List.foldl_update_eq_ite g _ w₀).trans (funext fun i => ite_eq_left (List.mem_finRange i))

/-- A double loop writing entry `(i, j)` of a matrix computes the whole matrix. -/
private theorem foldl_finRange_updateRow {m : ℕ} (g : Fin m → Fin m → ℝ)
    (A₀ : Matrix (Fin m) (Fin m) ℝ) :
    (List.finRange m).foldl (fun (A : Matrix (Fin m) (Fin m) ℝ) i =>
      (List.finRange m).foldl (fun (A : Matrix (Fin m) (Fin m) ℝ) j =>
        A.updateRow i (Function.update (A i) j (g i j))) A) A₀ = Matrix.of g := by
  have hrow : ∀ (i : Fin m) (A : Matrix (Fin m) (Fin m) ℝ),
      (List.finRange m).foldl (fun (A : Matrix (Fin m) (Fin m) ℝ) j =>
        A.updateRow i (Function.update (A i) j (g i j))) A = A.updateRow i (g i) := by
    intro i A
    have key : ∀ (L : List (Fin m)) (A : Matrix (Fin m) (Fin m) ℝ),
        L.foldl (fun (A : Matrix (Fin m) (Fin m) ℝ) j =>
          A.updateRow i (Function.update (A i) j (g i j))) A =
          A.updateRow i (L.foldl (fun w j => Function.update w j (g i j)) (A i)) := by
      intro L
      induction L with
      | nil => intro A; simp
      | cons a L ih =>
        intro A
        rw [List.foldl_cons, List.foldl_cons, ih]
        simp [updateRow_idem]
    rw [key, foldl_finRange_update]
  simp only [hrow]
  exact foldl_finRange_update (β := Fin m → ℝ) g A₀

/-- A branch between two writes of one entry is one write of a branch. -/
private theorem ite_update {m : ℕ} {β : Type} (w : Fin m → β) (i : Fin m) (c : Prop)
    [Decidable c] (a b : β) :
    (if c then Function.update w i a else Function.update w i b) =
      Function.update w i (if c then a else b) := by
  split_ifs <;> rfl

/-- A branch between two writes of one matrix entry is one write of a branch. -/
private theorem ite_updateRow {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) (c : Prop)
    [Decidable c] (a b : ℝ) :
    (if c then A.updateRow i (Function.update (A i) j a)
      else A.updateRow i (Function.update (A i) j b)) =
      A.updateRow i (Function.update (A i) j (if c then a else b)) := by
  split_ifs <;> rfl

/-- `Id.run` of a two-way branch between pure values. -/
private theorem idRun_ite_pure {α : Type} (c : Prop) [Decidable c] (a b : α) :
    Id.run (if c then pure a else pure b : Id α) = if c then a else b := by
  split_ifs <;> rfl

/-- The exact run of `incChol` on a `1 × 1` matrix. -/
private theorem incChol_zero (A Z : Matrix (Fin 1) (Fin 1) ℝ) :
    Id.run (incChol pure A Z) = Matrix.of fun _ _ => √(A 0 0) := rfl

/-- The exact run of `incChol` in closed form: one bordering step. -/
private theorem incChol_succ {n : ℕ} (A Z : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Id.run (incChol pure A Z) =
      let w : Fin (n + 1) → ℝ := fun i => if Z i.succ 0 = 0 then 0 else A i.succ 0 / √(A 0 0)
      let A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
        if Z i.succ j.succ = 0 then 0 else A i.succ j.succ - w i * w j
      let H₁ := Id.run (incChol pure A₁ (Z.submatrix Fin.succ Fin.succ))
      Matrix.of fun i j => Fin.cases (Fin.cases (√(A 0 0)) (fun _ => 0) j)
        (fun i' => Fin.cases (w i') (fun j' => H₁ i' j') j) i := by
  simp only [incChol, Id.run_bind, Id.run_pure, pure_bind, List.idRun_foldlM, idRun_ite_pure,
    ite_update, ite_updateRow, foldl_finRange_update, foldl_finRange_updateRow]

/-- **`incChol` computes an incomplete Cholesky factor of a Stieltjes matrix** (§11.5.8, "if the
algorithm runs to completion, then Equations (11.5.6), (11.5.7), and (11.5.8) are satisfied … this
turns out to be the case if `A` is a Stieltjes matrix"; [the book's P11.5.4]). For a Stieltjes
`A` and a symmetric pattern matrix `Z` with nonzero diagonal, every pivot `α` met by the exact run
is positive (each `A₁` is again Stieltjes: Theorem 11.5.2 for the dropped entries of `w`, then the
entrywise comparison theorem for the dropped entries of `B − wwᵀ`, a step the book's argument
omits), and `H` satisfies the backbone's `Matrix.IsIC P A H` with positive diagonal, where `P` is
the zero pattern of `Z`. If `P` avoids the nonzeros of `A`, `H` is an incomplete Cholesky factor
in the sense of (11.5.6)–(11.5.8); with `Z` all ones, `H` is the Cholesky factor
(`A = HHᵀ`). -/
theorem incChol_spec : ∀ {n : ℕ} {A Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
    A.IsStieltjes → Z.IsSymm → (∀ i, Z i i ≠ 0) →
    IsIC {x | Z x.1 x.2 = 0} A (Id.run (incChol pure A Z)) ∧
      ∀ i, 0 < Id.run (incChol pure A Z) i i
  | 0, A, Z, hA, _, hZd => by
    rw [incChol_zero]
    have ha : 0 < A 0 0 := hA.posDef.diag_pos
    have hs : ∀ i : Fin (0 + 1), i = 0 := fun i => Fin.fin_one_eq_zero i
    refine ⟨⟨fun i j hij => ?_, fun i j hij => ?_, fun i j _ => ?_⟩, fun i => ?_⟩
    · rw [hs i, hs j] at hij
      exact absurd hij (lt_irrefl _)
    · rw [hs i, hs j] at hij
      exact absurd hij (hZd 0)
    · rw [hs i, hs j]
      simp [mul_apply, Real.mul_self_sqrt ha.le]
    · simpa using Real.sqrt_pos.2 ha
  | n + 1, A, Z, hA, hZs, hZd => by
    classical
    set w : Fin (n + 1) → ℝ := fun i => if Z i.succ 0 = 0 then 0 else A i.succ 0 / √(A 0 0)
      with hw
    set A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
      if Z i.succ j.succ = 0 then 0 else A i.succ j.succ - w i * w j with hA₁def
    set H₁ := Id.run (incChol pure A₁ (Z.submatrix Fin.succ Fin.succ)) with hH₁
    have hrun : Id.run (incChol pure A Z) = Matrix.of fun i j =>
        Fin.cases (Fin.cases (√(A 0 0)) (fun _ => 0) j)
          (fun i' => Fin.cases (w i') (fun j' => H₁ i' j') j) i := incChol_succ A Z
    rw [hrun]
    have hα : 0 < A 0 0 := hA.posDef.diag_pos
    have hd : 0 < √(A 0 0) := Real.sqrt_pos.2 hα
    have hdd : √(A 0 0) * √(A 0 0) = A 0 0 := Real.mul_self_sqrt hα.le
    have hAs : A.IsSymm := hA.isSymm
    -- the new trailing matrix is Stieltjes
    have hB := theorem_11_5_2 hA (Finset.univ.filter fun i => Z i.succ 0 ≠ 0)
    have hww : ∀ i j, w i * w j = (if i ∈ Finset.univ.filter fun i => Z i.succ 0 ≠ 0 then
        A i.succ 0 else 0) * (if j ∈ Finset.univ.filter fun i => Z i.succ 0 ≠ 0 then
        A j.succ 0 else 0) / A 0 0 := by
      intro i j
      simp only [hw, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : Z i.succ 0 = 0 <;> by_cases hj : Z j.succ 0 = 0 <;>
        simp [hi, hj, div_mul_div_comm, hdd]
    have hA₁ : A₁.IsStieltjes := by
      refine hB.of_entrywiseLE (entrywiseLE_iff.2 fun i j => ?_) ?_ ?_
      · simp only [hA₁def, of_apply, ← hww]
        split_ifs with hz
        · have hij : i ≠ j := fun e => hZd _ (by rw [e] at hz; exact hz)
          have := hB.offDiag_nonpos i j hij
          simp only [of_apply, ← hww] at this
          exact this
        · exact le_rfl
      · refine IsSymm.ext fun i j => ?_
        simp only [hA₁def, of_apply, hZs.apply i.succ j.succ, hAs.apply i.succ j.succ,
          mul_comm (w j)]
      · intro i j hij
        simp only [hA₁def, of_apply]
        split_ifs
        · exact le_rfl
        · have := hB.offDiag_nonpos i j hij
          simp only [of_apply, ← hww] at this
          exact this
    have hZ₁s : (Z.submatrix Fin.succ Fin.succ).IsSymm := by
      refine IsSymm.ext fun i j => ?_
      simp [hZs.apply i.succ j.succ]
    obtain ⟨hIC, hpos⟩ := incChol_spec hA₁ hZ₁s fun i => hZd i.succ
    refine ⟨⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_⟩, fun i => ?_⟩
    · -- lower triangular
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j => simp
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ j => simpa using hIC.l_eq_zero_of_lt i j (Fin.succ_lt_succ_iff.1 hij)
    · -- zero on the pattern
      simp only [Set.mem_ofPred_eq] at hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (hZd 0)
        | succ j => simp
      | succ i =>
        induction j using Fin.cases with
        | zero => simp [hw, hij]
        | succ j => simpa using hIC.l_eq_zero_of_mem i j hij
    · -- agreement off the pattern
      simp only [Set.mem_ofPred_eq] at hij
      rw [mul_apply, Fin.sum_univ_succ]
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp [hdd]
        | succ j =>
          have hz : Z j.succ 0 ≠ 0 := by rwa [← hZs.apply j.succ 0]
          simp [hw, hz, hAs.apply j.succ 0]
          field_simp
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp [hw, hij]
          field_simp
        | succ j =>
          have hag : ∑ k, H₁ i k * H₁ j k = A₁ i j := hIC.agree i j hij
          simp only [transpose_apply, of_apply, Fin.cases_succ, Fin.cases_zero, hag, hA₁def, hij,
            ite_false]
          ring
    · induction i using Fin.cases with
      | zero => simpa using hd
      | succ i => simpa using hpos i

/-- The consequences of `incChol_spec` the book states: with `Z` all ones `incChol` is the
Cholesky factorization (`A = HHᵀ`), and when the dropped pattern avoids the nonzeros of `A` the
result satisfies (11.5.6)–(11.5.8) for the set `P` of subdiagonal pairs where `Z` vanishes. -/
theorem incChol_isIncompleteCholesky {n : ℕ} {A Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsStieltjes) (hZs : Z.IsSymm) (hZd : ∀ i, Z i i ≠ 0) :
    ((∀ i j, Z i j ≠ 0) → A.IsCholesky (Id.run (incChol pure A Z))ᵀ) ∧
      ((∀ i j, Z i j = 0 → A i j = 0) →
        IsIncompleteCholesky {x | x.2 < x.1 ∧ Z x.1 x.2 = 0} A (Id.run (incChol pure A Z))) := by
  obtain ⟨hIC, hpos⟩ := incChol_spec hA hZs hZd
  refine ⟨fun hZ => ⟨fun i j hij => hIC.l_eq_zero_of_lt j i hij, hpos, ?_⟩, fun hP => ?_⟩
  · rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
    ext i j
    exact hIC.agree i j (hZ i j)
  · refine isIncompleteCholesky_of_isIC hA.isSymm (fun i j h => hP i j h.2) ?_
    convert hIC using 1
    ext ⟨i, j⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, Prod.swap]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h
      · rwa [← hZs.apply i j]
    · intro h
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact Or.inr ⟨hij, by rwa [hZs.apply i j]⟩
      · exact absurd h (hZd i)
      · exact Or.inl ⟨hij, h⟩

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The Lin–Moré incomplete Cholesky factorization** of §11.5.8:
```
for j = 1:n
    v(j:n) = A(j:n, j) − H(j:n, 1:j−1) H(j, 1:j−1)ᵀ
    H(j,j) = √v(j)
    N_j = number of nonzeros in A(j:n, j)
    Set to zero each component of v(j+1:n) that is not one of the N_j + p largest
        entries in |v(j:n)|
    H(j+1:n, j) = v(j+1:n)/H(j,j)
end
```
The entries kept are the first `N_j + p` indices of `j:n` sorted by decreasing `|v_i|` (a stable
sort, so ties go to the smaller index; the selection compares computed values, exactly), and the
dropped entries of column `j` are set to zero without computing them. The count `N_j` is exact. -/
noncomputable def linMoreIC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (H : Matrix (Fin n) (Fin n) ℝ) j => do
    let v ← ((List.finRange n).filter fun i => decide (j ≤ i)).foldlM
      (fun (v : Fin n → ℝ) i => do
        let s ← ((List.finRange n).filter fun k => decide (k < j)).foldlM (fun s k => do
          let t ← rnd (H i k * H j k)
          rnd (s - t)) (A i j)
        pure (Function.update v i s)) 0
    let d ← rnd (√(v j))
    let keep := (((List.finRange n).filter fun i => decide (j ≤ i)).mergeSort
      fun a b => decide (|v b| ≤ |v a|)).take ((univ.filter fun i => j ≤ i ∧ A i j ≠ 0).card + p)
    ((List.finRange n).filter fun i => decide (j < i)).foldlM
      (fun (H : Matrix (Fin n) (Fin n) ℝ) i => do
        let h ← if i ∈ keep then rnd (v i / d) else pure 0
        pure (H.updateRow i (Function.update (H i) j h)))
      (H.updateRow j (Function.update (H j) j d))) 0

end Programs

/-- **The nonzero count of the Lin–Moré factor, corrected.** Every run of `linMoreIC`, whatever the
rounding, has at most `N_j + p` nonzeros strictly below the diagonal in column `j`, so
`nnz(H) ≤ pn + N₁ + ⋯ + N_n + n`. The printed bound `pn + N₁ + ⋯ + N_n` fails when the diagonal
`v(j)` is not among the `N_j + p` largest entries of `|v(j:n)|` (then `N_j + p` subdiagonal entries
are kept besides `H(j,j)`): for `A = [1 .9 .9; .9 1 0; .9 0 10]` and `p = 0`, column 2 keeps
`v(3) = −.81` (`|v(3)| > v(2) = .19`) besides `H(2,2)`, and `nnz(H) = 6 > N₁ + N₂ + N₃ = 5`. -/
theorem linMoreIC_nnz_le_add {n : ℕ} (fp : FloatingPoint.RoundingModel ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    ∀ H ∈ (linMoreIC fp.round A p).run,
      (univ.filter fun x : Fin n × Fin n => H x.1 x.2 ≠ 0).card ≤
        p * n + ∑ j, (univ.filter fun i => j ≤ i ∧ A i j ≠ 0).card + n := by
  intro H hH
  set N : Fin n → ℕ := fun j => (univ.filter fun i => j ≤ i ∧ A i j ≠ 0).card with hN
  have hI := SetM.forall_mem_run_foldlM_finRange
    (I := fun k (H : Matrix (Fin n) (Fin n) ℝ) =>
      (∀ i (j : Fin n), k ≤ (j : ℕ) → H i j = 0) ∧
        ∀ j : Fin n, (j : ℕ) < k → (univ.filter fun i => H i j ≠ 0).card ≤ N j + p + 1)
    ⟨fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_ H hH
  · -- sum the column counts
    obtain ⟨-, hcol⟩ := hI
    have hcard : (univ.filter fun x : Fin n × Fin n => H x.1 x.2 ≠ 0).card =
        ∑ j, (univ.filter fun i => H i j ≠ 0).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    rw [hcard]
    calc ∑ j, (univ.filter fun i => H i j ≠ 0).card ≤ ∑ j, (N j + p + 1) :=
          Finset.sum_le_sum fun j _ => hcol j j.2
      _ = p * n + ∑ j, N j + n := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          ring
  · -- one column
    rintro j H₀ ⟨hzero, hcnt⟩ H' hH'
    simp only [SetM.mem_run_bind] at hH'
    obtain ⟨v, -, d, -, hH'⟩ := hH'
    set keep := (((List.finRange n).filter fun i => decide (j ≤ i)).mergeSort
      fun a b => decide (|v b| ≤ |v a|)).take ((univ.filter fun i => j ≤ i ∧ A i j ≠ 0).card + p)
      with hkeep
    set H₁ := H₀.updateRow j (Function.update (H₀ j) j d) with hH₁
    -- the inner loop only writes column `j`, and only at kept rows
    have hinner := SetM.forall_mem_run_foldlM
      (l := (List.finRange n).filter fun i => decide (j < i))
      (I := fun _ (G : Matrix (Fin n) (Fin n) ℝ) =>
        (∀ i (j' : Fin n), j' ≠ j → G i j' = H₀ i j') ∧ ∀ i, G i j ≠ 0 → i = j ∨ i ∈ keep)
      ⟨fun i j' hj' => by
          by_cases hi : i = j
          · subst hi; simp [hH₁, updateRow_apply, Function.update_of_ne hj']
          · simp [hH₁, updateRow_apply, hi],
        fun i hi => by
          by_cases hij : i = j
          · exact Or.inl hij
          · simp [hH₁, updateRow_apply, hij, hzero i j le_rfl] at hi⟩
      (fun _ i _ _ G ⟨hG₁, hG₂⟩ G' hG' => by
        have key : ∃ h, (i ∉ keep → h = 0) ∧ G' = G.updateRow i (Function.update (G i) j h) := by
          split_ifs at hG' with hk
          · obtain ⟨h, -, hG'⟩ := SetM.mem_run_bind.1 hG'
            exact ⟨h, fun h' => absurd hk h', SetM.mem_run_pure.1 hG'⟩
          · obtain ⟨h, hh, hG'⟩ := SetM.mem_run_bind.1 hG'
            exact ⟨h, fun _ => SetM.mem_run_pure.1 hh, SetM.mem_run_pure.1 hG'⟩
        obtain ⟨h, hh0, rfl⟩ := key
        refine ⟨fun i' j' hj' => ?_, fun i' hi' => ?_⟩
        · by_cases hi : i' = i
          · subst hi; simp [updateRow_apply, Function.update_of_ne hj', hG₁ _ _ hj']
          · simp [updateRow_apply, hi, hG₁ _ _ hj']
        · by_cases hi : i' = i
          · subst hi
            simp only [updateRow_apply, ite_true, Function.update_self] at hi'
            by_cases hk : i' ∈ keep
            · exact Or.inr hk
            · exact absurd (hh0 hk) hi'
          · simp only [updateRow_apply, hi, ite_false] at hi'
            exact hG₂ i' hi')
      H' hH'
    obtain ⟨hsame, hnz⟩ := hinner
    refine ⟨fun i j' hj' => ?_, fun j' hj' => ?_⟩
    · rw [hsame i j' (fun e => by rw [e] at hj'; omega)]
      exact hzero i j' (by omega)
    · by_cases hjj : j' = j
      · subst hjj
        calc (univ.filter fun i => H' i j' ≠ 0).card ≤ (insert j' keep.toFinset).card :=
              Finset.card_le_card fun i hi => by
                rcases hnz i (Finset.mem_filter.1 hi).2 with h | h
                · simp [h]
                · simp [h]
          _ ≤ keep.toFinset.card + 1 := Finset.card_insert_le _ _
          _ ≤ keep.length + 1 := Nat.add_le_add_right (List.toFinset_card_le _) 1
          _ ≤ N j' + p + 1 := Nat.add_le_add_right (List.length_take_le _ _) 1
      · have hlt : (j' : ℕ) < j := by
          have : (j' : ℕ) ≠ j := fun e => hjj (Fin.ext e)
          omega
        have h' : ∀ i, H' i j' = H₀ i j' := fun i => hsame i j' hjj
        simpa [h'] using hcnt j' hlt

/-! ### §11.5.9: incomplete block preconditioners -/

section Block

variable {p q : ℕ}

/-- The block tridiagonal matrix `[A₁ E₁ᵀ; E₁ A₂ E₂ᵀ; ⋱]` of §11.5.9 on `Fin p × Fin q` (block row
and column indices first): diagonal blocks `Ad k`, subdiagonal blocks `E k` in block row `k + 1`,
superdiagonal blocks `(E k)ᵀ`. -/
def blockTridiag (Ad E : Fin p → Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin p × Fin q) (Fin p × Fin q) ℝ :=
  Matrix.of fun x y => if y.1 = x.1 then Ad x.1 x.2 y.2
    else if (y.1 : ℕ) + 1 = x.1 then E y.1 x.2 y.2
    else if (x.1 : ℕ) + 1 = y.1 then E x.1 y.2 x.2 else 0

/-- The block lower bidiagonal matrix `[G₁ 0; F₁ G₂ 0; ⋱]` of §11.5.9: diagonal blocks `Gd k`,
subdiagonal blocks `F k` in block row `k + 1`. -/
def blockLowerBidiag (Gd F : Fin p → Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin p × Fin q) (Fin p × Fin q) ℝ :=
  Matrix.of fun x y => if y.1 = x.1 then Gd x.1 x.2 y.2
    else if (y.1 : ℕ) + 1 = x.1 then F y.1 x.2 y.2 else 0

/-- A row of a block lower bidiagonal matrix against a vector: the diagonal block and the one
subdiagonal block. -/
private theorem sum_blockLowerBidiag (Gd F : Fin p → Matrix (Fin q) (Fin q) ℝ) (k : Fin p)
    (i : Fin q) (f : Fin p × Fin q → ℝ) :
    ∑ y, blockLowerBidiag Gd F (k, i) y * f y =
      ∑ t, Gd k i t * f (k, t) +
        ∑ m : Fin p, if (m : ℕ) + 1 = k then ∑ t, F m i t * f (m, t) else 0 := by
  rw [Fintype.sum_prod_type]
  have hm : ∀ m, ∑ t, blockLowerBidiag Gd F (k, i) (m, t) * f (m, t) =
      (if m = k then ∑ t, Gd k i t * f (k, t) else 0) +
        (if (m : ℕ) + 1 = k then ∑ t, F m i t * f (m, t) else 0) := by
    intro m
    by_cases h1 : m = k
    · subst h1
      simp [blockLowerBidiag]
    · by_cases h2 : (m : ℕ) + 1 = k
      · simp [blockLowerBidiag, h1, h2]
      · simp [blockLowerBidiag, h1, h2]
  rw [Finset.sum_congr rfl fun m _ => hm m, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- `(F Fᵀ) = E (G Gᵀ)⁻¹ Eᵀ` for `F = E G⁻ᵀ`. -/
private theorem mul_transpose_eq {E G : Matrix (Fin q) (Fin q) ℝ} :
    E * (G⁻¹)ᵀ * (E * (G⁻¹)ᵀ)ᵀ = E * (G * Gᵀ)⁻¹ * Eᵀ := by
  rw [Matrix.mul_inv_rev, ← transpose_nonsing_inv, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- **§11.5.9, block Cholesky of a block tridiagonal matrix.** With `G₁G₁ᵀ = A₁` and, for each
`k`, `F_k = E_kG_k⁻ᵀ` and `G_{k+1}G_{k+1}ᵀ = A_{k+1} − E_k(G_kG_kᵀ)⁻¹E_kᵀ` (nonsingular `G_k`),
the block tridiagonal `A = [A₁ E₁ᵀ; E₁ A₂ E₂ᵀ; ⋱]` factors as `A = GGᵀ` with the block lower
bidiagonal `G = [G₁ 0; F₁ G₂ 0; ⋱]`. -/
theorem blockTridiagonal_cholesky (Ad E Gd : Fin p → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ k, IsUnit (Gd k)) (h0 : ∀ k : Fin p, (k : ℕ) = 0 → Gd k * (Gd k)ᵀ = Ad k)
    (hS : ∀ k l : Fin p, (k : ℕ) + 1 = l →
      Gd l * (Gd l)ᵀ = Ad l - E k * (Gd k * (Gd k)ᵀ)⁻¹ * (E k)ᵀ) :
    blockTridiag Ad E = blockLowerBidiag Gd (fun k => E k * ((Gd k)⁻¹)ᵀ) *
      (blockLowerBidiag Gd (fun k => E k * ((Gd k)⁻¹)ᵀ))ᵀ := by
  set F : Fin p → Matrix (Fin q) (Fin q) ℝ := fun k => E k * ((Gd k)⁻¹)ᵀ with hF
  have hFG : ∀ m, F m * (Gd m)ᵀ = E m := fun m => by
    rw [hF, Matrix.mul_assoc, ← transpose_mul,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hG m)), transpose_one, Matrix.mul_one]
  ext ⟨k, i⟩ ⟨l, j⟩
  rw [mul_apply]
  simp only [transpose_apply]
  rw [sum_blockLowerBidiag]
  -- the entries of `G` in block row `l`
  have hGl : ∀ m t, blockLowerBidiag Gd F (l, j) (m, t) = if m = l then Gd l j t
      else if (m : ℕ) + 1 = l then F m j t else 0 := fun m t => rfl
  simp only [hGl]
  by_cases hkl : k = l
  · subst hkl
    have hsum : ∑ m : Fin p, (if (m : ℕ) + 1 = k then ∑ t, F m i t *
        (if m = k then Gd k j t else if (m : ℕ) + 1 = k then F m j t else 0) else 0) =
        ∑ m : Fin p, if (m : ℕ) + 1 = k then (F m * (F m)ᵀ) i j else 0 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : (m : ℕ) + 1 = k
      · have hmk : m ≠ k := fun e => by rw [e] at hm; omega
        simp [hm, hmk, mul_apply]
      · simp [hm]
    simp only [ite_true, hsum]
    have hdiag : ∑ t, Gd k i t * Gd k j t = (Gd k * (Gd k)ᵀ) i j := by simp [mul_apply]
    rw [hdiag]
    by_cases h0k : (k : ℕ) = 0
    · rw [Finset.sum_eq_zero fun m _ => by rw [ite_eq_right (by omega)], add_zero, h0 k h0k]
      simp [blockTridiag]
    · obtain ⟨m, hm⟩ : ∃ m : Fin p, (m : ℕ) + 1 = k := ⟨⟨k - 1, by omega⟩, by simp; omega⟩
      rw [Finset.sum_eq_single m (fun m' _ hm' => by
          rw [ite_eq_right (fun h => hm' (Fin.ext (by omega)))]) (by simp), ite_eq_left hm,
        hS m k hm, mul_transpose_eq]
      simp [blockTridiag]
  · by_cases hlk : (l : ℕ) + 1 = k
    · -- the subdiagonal block `E_l`
      have hkl' : ¬ (k : ℕ) + 1 = l := by omega
      rw [Finset.sum_eq_single l (fun m _ hm => by
          rw [ite_eq_right_iff.2 fun h => by
            simp [show m ≠ l from hm, show ¬ (m : ℕ) + 1 = l by omega]]) (by simp),
        ite_eq_left hlk]
      simp only [ite_true, hkl, ite_false, show ¬ (k : ℕ) + 1 = l from hkl']
      rw [show ∑ t, F l i t * Gd l j t = (F l * (Gd l)ᵀ) i j by simp [mul_apply], hFG]
      simp [blockTridiag, Ne.symm hkl, hlk]
    · have hkl₀ : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
      by_cases hkl' : (k : ℕ) + 1 = l
      · -- the superdiagonal block `E_kᵀ`
        have h2 : (∑ m : Fin p, if (m : ℕ) + 1 = k then ∑ t, F m i t *
            (if m = l then Gd l j t else if (m : ℕ) + 1 = l then F m j t else 0) else 0) = 0 := by
          refine Finset.sum_eq_zero fun m _ => ?_
          by_cases hm : (m : ℕ) + 1 = k
          · have h1 : m ≠ l := by rintro rfl; omega
            simp [hm, h1, hkl₀]
          · simp [hm]
        rw [h2, add_zero]
        simp only [hkl, ite_false, hkl', ite_true]
        rw [show ∑ t, Gd k i t * F k j t = (F k * (Gd k)ᵀ) j i by
          simp [mul_apply, mul_comm], hFG]
        simp [blockTridiag, Ne.symm hkl, hlk, hkl']
      · -- blocks two or more apart vanish
        have h2 : (∑ m : Fin p, if (m : ℕ) + 1 = k then ∑ t, F m i t *
            (if m = l then Gd l j t else if (m : ℕ) + 1 = l then F m j t else 0) else 0) = 0 := by
          refine Finset.sum_eq_zero fun m _ => ?_
          by_cases hm : (m : ℕ) + 1 = k
          · have h1 : m ≠ l := by rintro rfl; omega
            simp [hm, h1, hkl₀]
          · simp [hm]
        rw [h2, add_zero]
        simp only [hkl, hkl', ite_false, mul_zero, Finset.sum_const_zero]
        simp [blockTridiag, Ne.symm hkl, hlk, hkl']
/-- **(11.5.10)**, "with this strategy each `G̃_k` is lower bidiagonal": if `A_{k+1}` is
tridiagonal, `E_k` diagonal and `Λ_k` symmetric tridiagonal, then `A_{k+1} − E_kΛ_kE_kᵀ` is
tridiagonal, and the Cholesky factor of a positive definite tridiagonal matrix is bidiagonal: with
`G̃ = Hᵀ`
(`Matrix.IsCholesky T H`), `h_ij = 0` unless `j = i` or `j = i + 1`. (Tridiagonal matrices have no
Cholesky fill.) -/
theorem equation_11_5_10 {Ak Λ : Matrix (Fin q) (Fin q) ℝ} (e : Fin q → ℝ)
    (hA : ∀ i j : Fin q, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → Ak i j = 0)
    (hΛ : ∀ i j : Fin q, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → Λ i j = 0) :
    (∀ i j : Fin q, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i →
      (Ak - diagonal e * Λ * (diagonal e)ᵀ) i j = 0) ∧
    ∀ {T H : Matrix (Fin q) (Fin q) ℝ}, T.IsCholesky H →
      (∀ i j : Fin q, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → T i j = 0) →
      ∀ i j : Fin q, j ≠ i → (j : ℕ) ≠ i + 1 → H i j = 0 := by
  refine ⟨fun i j hij => ?_, fun {T H} hTH hT i j hji hji' => ?_⟩
  · simp [diagonal_transpose, Matrix.sub_apply, diagonal_mul, mul_diagonal, hA i j hij, hΛ i j hij]
  · rcases lt_or_gt_of_ne hji with hlt | hgt
    · exact hTH.isUpperTriangular hlt
    · -- no fill below the subdiagonal
      have hnf : ¬ T.IsCholeskyFill j i := by
        intro hf
        have key : ∀ a b, T.IsCholeskyFill a b → (a : ℕ) = b + 1 := by
          intro a b h
          induction h with
          | of_ne_zero hba hne =>
            by_contra hc
            exact hne (hT _ _ (Or.inr (by rw [Fin.lt_def] at hba; omega)))
          | trans hkj hji _ _ ih₁ ih₂ =>
            rw [Fin.lt_def] at hkj hji
            omega
        have := key j i hf
        omega
      exact hTH.apply_eq_zero_of_not_isCholeskyFill hgt hnf

/-- §11.5.9, the display after (11.5.10): the block lower bidiagonal system
`[G̃₁ 0; F̃₁ G̃₂ 0; ⋱] w = r` with `F̃_k = E_kG̃_k⁻ᵀ` is solved by `G̃₁w₁ = r₁`,
`G̃_{k+1}w_{k+1} = r_{k+1} − E_kG̃_k⁻ᵀw_k` — "the `F̃_k` … do not have to actually be formed". -/
theorem blockIC_forwardSolve (Gd E : Fin p → Matrix (Fin q) (Fin q) ℝ)
    (w r : Fin p × Fin q → ℝ) :
    blockLowerBidiag Gd (fun k => E k * ((Gd k)⁻¹)ᵀ) *ᵥ w = r ↔
      (∀ k : Fin p, (k : ℕ) = 0 → Gd k *ᵥ (fun t => w (k, t)) = fun i => r (k, i)) ∧
      ∀ k l : Fin p, (k : ℕ) + 1 = l →
        Gd l *ᵥ (fun t => w (l, t)) =
          (fun i => r (l, i)) - E k *ᵥ (((Gd k)⁻¹)ᵀ *ᵥ fun t => w (k, t)) := by
  have hrow : ∀ (k : Fin p) (i : Fin q), (blockLowerBidiag Gd (fun k => E k * ((Gd k)⁻¹)ᵀ) *ᵥ w)
      (k, i) = (Gd k *ᵥ fun t => w (k, t)) i + ∑ m : Fin p, if (m : ℕ) + 1 = k then
        (E m *ᵥ (((Gd m)⁻¹)ᵀ *ᵥ fun t => w (m, t))) i else 0 := by
    intro k i
    rw [mulVec, dotProduct, sum_blockLowerBidiag]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs
    · rw [mulVec_mulVec]
      rfl
    · rfl
  constructor
  · intro h
    refine ⟨fun k hk => funext fun i => ?_, fun k l hkl => funext fun i => ?_⟩
    · have := hrow k i
      rw [h, Finset.sum_eq_zero fun m _ => ite_eq_right (by omega), add_zero] at this
      exact this.symm
    · have := hrow l i
      rw [h, Finset.sum_eq_single k (fun m _ hm => ite_eq_right (fun h' => hm (Fin.ext
        (by omega)))) (by simp), ite_eq_left hkl] at this
      rw [Pi.sub_apply, this]
      ring
  · rintro ⟨h0, hs⟩
    ext ⟨k, i⟩
    rw [hrow]
    by_cases hk : (k : ℕ) = 0
    · rw [Finset.sum_eq_zero fun m _ => ite_eq_right (by omega), add_zero, h0 k hk]
    · obtain ⟨m, hm⟩ : ∃ m : Fin p, (m : ℕ) + 1 = k := ⟨⟨k - 1, by omega⟩, by simp; omega⟩
      rw [Finset.sum_eq_single m (fun m' _ hm' => ite_eq_right (fun h' => hm' (Fin.ext
        (by omega)))) (by simp), ite_eq_left hm, hs m k hm, Pi.sub_apply]
      ring

end Block

/-! ### §11.5.10: saddle-point systems -/

/-- §11.5.10: "if `A` is nonsingular and `C = 0`, then
`[A B₁; B₂ᵀ 0] = [I 0; B₂ᵀA⁻¹ I] [A 0; 0 S] [I A⁻¹B₁; 0 I]`, `S = −B₂ᵀA⁻¹B₁`." (The book first
writes the system as `[A B₁ᵀ; B₂ −C]` and then transposes the off-diagonal blocks.) -/
theorem saddlePoint_factorization {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (B₁ B₂ : Matrix (Fin n) (Fin m) ℝ) :
    fromBlocks A B₁ B₂ᵀ 0 = fromBlocks 1 0 (B₂ᵀ * A⁻¹) 1 * fromBlocks A 0 0 (-(B₂ᵀ * A⁻¹ * B₁)) *
      fromBlocks 1 (A⁻¹ * B₁) 0 1 := by
  have hA' := (isUnit_iff_isUnit_det A).1 hA
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_assoc, nonsing_inv_mul _ hA', mul_nonsing_inv_cancel_left _ _ hA']
  congr 1
  abel

/-- §11.5.10: with `H₁ = (A + Aᵀ)/2`, `H₂ = (A − Aᵀ)/2`,
`[A B; −Bᵀ C] = [H₁ 0; 0 C] + [H₂ B; −Bᵀ 0] = K₁ + K₂`, a splitting into a symmetric `K₁` — positive
definite when `C` is and `xᵀAx > 0` for `x ≠ 0` — and a skew-symmetric `K₂`. -/
theorem saddlePoint_splitting {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    fromBlocks A B (-Bᵀ) C = fromBlocks ((1 / 2 : ℝ) • (A + Aᵀ)) 0 0 C +
        fromBlocks ((1 / 2 : ℝ) • (A - Aᵀ)) B (-Bᵀ) 0 ∧
      (C.IsSymm → (fromBlocks ((1 / 2 : ℝ) • (A + Aᵀ)) 0 0 C).IsSymm) ∧
      (fromBlocks ((1 / 2 : ℝ) • (A - Aᵀ)) B (-Bᵀ) 0)ᵀ =
        -fromBlocks ((1 / 2 : ℝ) • (A - Aᵀ)) B (-Bᵀ) 0 ∧
      ((∀ x, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) → C.PosDef →
        (fromBlocks ((1 / 2 : ℝ) • (A + Aᵀ)) 0 0 C).PosDef) := by
  have hq : ∀ x : Fin n → ℝ, x ⬝ᵥ ((1 / 2 : ℝ) • (A + Aᵀ)) *ᵥ x = x ⬝ᵥ A *ᵥ x := by
    intro x
    rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dotProduct_mulVec x Aᵀ x,
      vecMul_transpose, dotProduct_comm (A *ᵥ x) x, smul_eq_mul]
    ring
  refine ⟨?_, fun hC => ?_, ?_, fun hApos hC => ?_⟩
  · rw [fromBlocks_add]
    congr 1
    · rw [smul_add, smul_sub]; module
    all_goals simp
  · rw [IsSymm, fromBlocks_transpose, hC.eq]
    simp only [transpose_zero, transpose_smul, transpose_add, transpose_transpose, add_comm Aᵀ A]
  · rw [fromBlocks_transpose, fromBlocks_neg, transpose_smul, transpose_sub, transpose_transpose,
      transpose_neg, transpose_transpose, transpose_zero, neg_zero, ← smul_neg, neg_sub, neg_neg]
  · rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · have hCt : Cᵀ = C := by
        simpa [conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose, hCt]
      simp only [transpose_zero, transpose_smul, transpose_add, transpose_transpose,
        add_comm Aᵀ A]
    · have hsplit : star x ⬝ᵥ (fromBlocks ((1 / 2 : ℝ) • (A + Aᵀ)) 0 0 C *ᵥ x) =
          (fun i => x (Sum.inl i)) ⬝ᵥ A *ᵥ (fun i => x (Sum.inl i)) +
            star (fun i => x (Sum.inr i)) ⬝ᵥ C *ᵥ (fun i => x (Sum.inr i)) := by
        rw [← hq]
        simp [dotProduct, fromBlocks_mulVec, Fintype.sum_sum_type, star_trivial, Function.comp_def]
      rw [hsplit]
      by_cases hl : (fun i => x (Sum.inl i)) = 0
      · have hr : (fun i => x (Sum.inr i)) ≠ 0 := by
          intro hr
          apply hx
          ext (i | i)
          · exact congrFun hl i
          · exact congrFun hr i
        rw [hl]
        simpa using (posDef_iff_dotProduct_mulVec.1 hC).2 hr
      · have h1 := hApos _ hl
        have h2 : 0 ≤ star (fun i => x (Sum.inr i)) ⬝ᵥ C *ᵥ (fun i => x (Sum.inr i)) :=
          hC.posSemidef.dotProduct_mulVec_nonneg _
        linarith

/-! ### §11.5.11: domain decomposition -/

/-- §11.5.11: "for either the multiplicative or additive approach, it is possible to relate
`u^(new)` to `u^(old)` via an expression of the form `u^(new) = u^(old) + M⁻¹(f − Au^(old))`". For a
nonsingular `A`, subdomain solves given by projection pairs `(K_i, L_i)` (the exact subdomain solves
of the book are `K_i = L_i`, `A`-orthogonal projections for symmetric positive definite `A`), a
multiplicative sweep over the subdomains in the order `l` and an additive sweep with weights `ω`
are both of this form, with a fixed linear `M⁻¹` (independent of `f` and `u^(old)`):
`M⁻¹ = A⁻¹(I − R)` for the residual propagation operator `R` of the sweep. -/
theorem schwarz_update_affine {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {ι : Type*}
    [Fintype ι] (K L : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ i, Projection.IsNondegeneratePair (toEuclideanLin A) (K i) (L i)) :
    (∀ l : List ι, ∃ B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n), ∀ f u,
      Projection.multiplicativeStep (toEuclideanLin A) f K L h l u =
        u + B (f - toEuclideanLin A u)) ∧
    (∀ ω : ι → ℝ, ∃ B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n), ∀ f u,
      Projection.additiveStep (toEuclideanLin A) f K L h ω u =
        u + B (f - toEuclideanLin A u)) := by
  have hinv : ∀ z, toEuclideanLin A⁻¹ (toEuclideanLin A z) = z :=
    toEuclideanLin_nonsing_inv_mul_apply hA
  -- a step whose residual is `R` of the old residual is `u + A⁻¹(I − R)(f − Au)`
  have key : ∀ (R : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (f u v),
      f - toEuclideanLin A v = R (f - toEuclideanLin A u) →
        v = u + (toEuclideanLin A⁻¹ ∘ₗ (1 - R)) (f - toEuclideanLin A u) := by
    intro R f u v hv
    have hAv : toEuclideanLin A v = f - R (f - toEuclideanLin A u) := by
      rw [← hv]; abel
    rw [← hinv v, hAv]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub, hinv]
    abel
  refine ⟨fun l => ⟨_, fun f u => key _ f u _ (Projection.residual_multiplicativeStep h l u)⟩,
    fun ω => ⟨_, fun f u => key _ f u _ (Projection.residual_additiveStep h ω u)⟩⟩

section DomainDecomposition

variable {a b c d e : ℕ}

/-- The interior block `diag(A₁, A₂, A₃)` of (11.5.11), on `Fin a ⊕ (Fin b ⊕ Fin c)`. -/
abbrev ddInterior (A₁ : Matrix (Fin a) (Fin a) ℝ) (A₂ : Matrix (Fin b) (Fin b) ℝ)
    (A₃ : Matrix (Fin c) (Fin c) ℝ) :
    Matrix (Fin a ⊕ (Fin b ⊕ Fin c)) (Fin a ⊕ (Fin b ⊕ Fin c)) ℝ :=
  fromBlocks A₁ 0 0 (fromBlocks A₂ 0 0 A₃)

/-- The interior-to-interface coupling `[B C; D 0; 0 E]` of (11.5.11). -/
abbrev ddCoupling (B : Matrix (Fin a) (Fin d) ℝ) (C : Matrix (Fin a) (Fin e) ℝ)
    (D : Matrix (Fin b) (Fin d) ℝ) (E : Matrix (Fin c) (Fin e) ℝ) :
    Matrix (Fin a ⊕ (Fin b ⊕ Fin c)) (Fin d ⊕ Fin e) ℝ :=
  fromBlocks B C (fromRows D 0) (fromRows 0 E)

/-- The interface-to-interior coupling `[F H 0; G 0 K]` of (11.5.11). -/
abbrev ddCoupling' (F : Matrix (Fin d) (Fin a) ℝ) (H : Matrix (Fin d) (Fin b) ℝ)
    (G : Matrix (Fin e) (Fin a) ℝ) (K : Matrix (Fin e) (Fin c) ℝ) :
    Matrix (Fin d ⊕ Fin e) (Fin a ⊕ (Fin b ⊕ Fin c)) ℝ :=
  fromBlocks F (fromCols H 0) G (fromCols 0 K)

/-- The multipliers `[FA₁⁻¹ HA₂⁻¹ 0; GA₁⁻¹ 0 KA₃⁻¹]` below the diagonal of the book's `L`. -/
noncomputable abbrev ddMultipliers (A₁ : Matrix (Fin a) (Fin a) ℝ)
    (A₂ : Matrix (Fin b) (Fin b) ℝ) (A₃ : Matrix (Fin c) (Fin c) ℝ) (F : Matrix (Fin d) (Fin a) ℝ)
    (H : Matrix (Fin d) (Fin b) ℝ) (G : Matrix (Fin e) (Fin a) ℝ) (K : Matrix (Fin e) (Fin c) ℝ) :
    Matrix (Fin d ⊕ Fin e) (Fin a ⊕ (Fin b ⊕ Fin c)) ℝ :=
  fromBlocks (F * A₁⁻¹) (fromCols (H * A₂⁻¹) 0) (G * A₁⁻¹) (fromCols 0 (K * A₃⁻¹))

/-- **(11.5.11) and the factorization after it, corrected.** For the nonoverlapping decomposition
of the L-shaped domain, with interior blocks `A₁, A₂, A₃` nonsingular,
`A = [A₁ 0 0 B C; 0 A₂ 0 D 0; 0 0 A₃ 0 E; F H 0 Q₄ 0; G 0 K 0 Q₅]` factors as `A = L U` with `L`
unit block lower triangular (`FA₁⁻¹, HA₂⁻¹, GA₁⁻¹, KA₃⁻¹` below the diagonal, as printed) and `U`
block upper triangular with the Schur complement `S = Q − [F H 0; G 0 K] diag(A₁, A₂, A₃)⁻¹ [B C;
D 0; 0 E]` in its interface block. The diagonal blocks of `S` are the book's
`S₄ = Q₄ − FA₁⁻¹B − HA₂⁻¹D` and `S₅ = Q₅ − GA₁⁻¹C − KA₃⁻¹E`, but its off-diagonal blocks are
`−FA₁⁻¹C` and `−GA₁⁻¹B`, not `0` as printed: both interfaces touch `Ω₁`
(`equation_11_5_11_counterexample`). -/
theorem equation_11_5_11_blockLU {A₁ : Matrix (Fin a) (Fin a) ℝ} {A₂ : Matrix (Fin b) (Fin b) ℝ}
    {A₃ : Matrix (Fin c) (Fin c) ℝ} (h₁ : IsUnit A₁) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (B : Matrix (Fin a) (Fin d) ℝ) (C : Matrix (Fin a) (Fin e) ℝ) (D : Matrix (Fin b) (Fin d) ℝ)
    (E : Matrix (Fin c) (Fin e) ℝ) (F : Matrix (Fin d) (Fin a) ℝ) (H : Matrix (Fin d) (Fin b) ℝ)
    (G : Matrix (Fin e) (Fin a) ℝ) (K : Matrix (Fin e) (Fin c) ℝ) (Q₄ : Matrix (Fin d) (Fin d) ℝ)
    (Q₅ : Matrix (Fin e) (Fin e) ℝ) :
    fromBlocks (ddInterior A₁ A₂ A₃) (ddCoupling B C D E) (ddCoupling' F H G K)
        (fromBlocks Q₄ 0 0 Q₅) =
      fromBlocks 1 0 (ddMultipliers A₁ A₂ A₃ F H G K) 1 *
        fromBlocks (ddInterior A₁ A₂ A₃) (ddCoupling B C D E) 0
          (fromBlocks (Q₄ - F * A₁⁻¹ * B - H * A₂⁻¹ * D) (-(F * A₁⁻¹ * C))
            (-(G * A₁⁻¹ * B)) (Q₅ - G * A₁⁻¹ * C - K * A₃⁻¹ * E)) := by
  have h₁' := (isUnit_iff_isUnit_det _).1 h₁
  have h₂' := (isUnit_iff_isUnit_det _).1 h₂
  have h₃' := (isUnit_iff_isUnit_det _).1 h₃
  simp only [ddInterior, ddCoupling, ddCoupling', ddMultipliers, fromBlocks_multiply,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows, fromBlocks_add, Matrix.one_mul,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc,
    nonsing_inv_mul _ h₁', nonsing_inv_mul _ h₂', nonsing_inv_mul _ h₃', Matrix.mul_one]
  congr 2 <;> abel

/-- The printed factorization of §11.5.11 (with `S₄`, `S₅` on the diagonal of `U` and zero
off-diagonal interface blocks) is **false**: with every block `1 × 1` and equal to `1`, the
`(4, 5)` block of `LU` is `FA₁⁻¹C = 1`, while that of `A` is `0`. -/
theorem equation_11_5_11_counterexample :
    let o : Matrix (Fin 1) (Fin 1) ℝ := 1
    fromBlocks (ddInterior o o o) (ddCoupling o o o o) (ddCoupling' o o o o) (fromBlocks o 0 0 o) ≠
      fromBlocks 1 0 (ddMultipliers o o o o o o o) 1 *
        fromBlocks (ddInterior o o o) (ddCoupling o o o o) 0
          (fromBlocks (o - o * o⁻¹ * o - o * o⁻¹ * o) 0 0 (o - o * o⁻¹ * o - o * o⁻¹ * o)) := by
  intro o h
  have := congrFun (congrFun h (Sum.inr (Sum.inl 0))) (Sum.inr (Sum.inr 0))
  simp [o, fromBlocks_multiply, fromCols_mul_fromRows] at this

/-- §11.5.11, "a consequence of (b) is that `A − M` has low rank": for the block ILU preconditioner
`M = L U_M`, where `U_M` is `U` with approximations `St₄ ≈ S₄`, `St₅ ≈ S₅` in place of the interface
Schur complement, `A − M = L (U − U_M)` has rank at most the number `d + e` of interface
unknowns. -/
theorem ddPreconditioner_rank_le {A₁ : Matrix (Fin a) (Fin a) ℝ} {A₂ : Matrix (Fin b) (Fin b) ℝ}
    {A₃ : Matrix (Fin c) (Fin c) ℝ} (h₁ : IsUnit A₁) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (B : Matrix (Fin a) (Fin d) ℝ) (C : Matrix (Fin a) (Fin e) ℝ) (D : Matrix (Fin b) (Fin d) ℝ)
    (E : Matrix (Fin c) (Fin e) ℝ) (F : Matrix (Fin d) (Fin a) ℝ) (H : Matrix (Fin d) (Fin b) ℝ)
    (G : Matrix (Fin e) (Fin a) ℝ) (K : Matrix (Fin e) (Fin c) ℝ) (Q₄ : Matrix (Fin d) (Fin d) ℝ)
    (Q₅ : Matrix (Fin e) (Fin e) ℝ) (St₄ : Matrix (Fin d) (Fin d) ℝ)
    (St₅ : Matrix (Fin e) (Fin e) ℝ) :
    (fromBlocks (ddInterior A₁ A₂ A₃) (ddCoupling B C D E) (ddCoupling' F H G K)
        (fromBlocks Q₄ 0 0 Q₅) -
      fromBlocks 1 0 (ddMultipliers A₁ A₂ A₃ F H G K) 1 *
        fromBlocks (ddInterior A₁ A₂ A₃) (ddCoupling B C D E) 0 (fromBlocks St₄ 0 0 St₅)).rank ≤
      d + e := by
  rw [equation_11_5_11_blockLU h₁ h₂ h₃, ← Matrix.mul_sub]
  refine (rank_mul_le_right _ _).trans ?_
  have hsub : ∀ (P : Matrix (Fin a ⊕ (Fin b ⊕ Fin c)) (Fin a ⊕ (Fin b ⊕ Fin c)) ℝ)
      (Q : Matrix (Fin a ⊕ (Fin b ⊕ Fin c)) (Fin d ⊕ Fin e) ℝ)
      (X₁ X₂ : Matrix (Fin d ⊕ Fin e) (Fin d ⊕ Fin e) ℝ),
      fromBlocks P Q 0 X₁ - fromBlocks P Q 0 X₂ =
        fromRows (0 : Matrix (Fin a ⊕ (Fin b ⊕ Fin c)) (Fin d ⊕ Fin e) ℝ) 1 *
          fromCols (0 : Matrix (Fin d ⊕ Fin e) (Fin a ⊕ (Fin b ⊕ Fin c)) ℝ) (X₁ - X₂) := by
    intro P Q X₁ X₂
    rw [fromRows_mul_fromCols]
    ext (i | i) (j | j) <;> simp
  rw [hsub]
  refine (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans ?_)
  simp

end DomainDecomposition

/-! ### §11.5.2: preconditioned GMRES -/

section PreconditionedGMRES

open Krylov

variable {n m : ℕ}

/-- **Algorithm 11.5.2 (Preconditioned `m`-step GMRES).** "If `A ∈ ℝ^{n×n}` and `M ∈ ℝ^{n×n}`
are nonsingular, `b ∈ ℝⁿ`, `Ax₀ ≈ b`, and `m` is a positive iteration limit, then this algorithm
computes `x̃ ∈ ℝⁿ` where either `x̃` solves `Ax = b` or minimizes `‖M⁻¹(Ax − b)‖₂` over the affine
space `x₀ + 𝒦(M⁻¹A, M⁻¹r₀, m)` where `r₀ = b − Ax₀`": Algorithm 11.4.2 with `r₀` replaced by
`z₀`, `M z₀ = r₀`, and `Aq_k` by `z_k`, `M z_k = Aq_k`; the same rotations and back substitution
(`gmresCore`). The solves with `M` are the routine `solveM`. -/
noncomputable def algorithm_11_5_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (b x₀ : Fin n → ℝ)
    (m : ℕ) : M (GMRESState n m × (Fin n → ℝ)) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let z₀ ← solveM r₀
  gmresCore rnd (fun q => do
    let w ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0
    solveM w) x₀ z₀ m

/-- **Exact semantics of Algorithm 11.5.2** (`A`, `M` nonsingular, `solveM = M⁻¹`): the run is
GMRES on the preconditioned system `(M⁻¹A) x = M⁻¹b` — it makes `k = min(m, grade)` Arnoldi steps
on `z₀ = M⁻¹r₀`, `x̃` minimizes `‖M⁻¹(b − Ax)‖₂` over `x₀ + 𝒦(M⁻¹A, z₀, k)`
(`Krylov.IsMinResidualIterate`), `|ρ_k| = ‖M⁻¹(b − Ax̃)‖₂` (the book's closing remark, up to the
sign of `ρ_k`, which depends on the rotations), and if the loop stopped on `β_k = 0` then
`Ax̃ = b`. From `gmresCore_spec` with `B = M⁻¹A`. -/
theorem algorithm_11_5_2_spec {A Mp : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hM : IsUnit Mp) (b x₀ : Fin n → ℝ) (m : ℕ) :
    let out := Id.run (algorithm_11_5_2 pure A (fun r => pure (Mp⁻¹ *ᵥ r)) b x₀ m)
    let T := toEuclideanLin (Mp⁻¹ * A)
    let z₀ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Mp⁻¹ *ᵥ (b - A *ᵥ x₀))
    out.1.arnoldi.k = min m (grade T z₀) ∧
      IsMinResidualIterate T (WithLp.toLp 2 (Mp⁻¹ *ᵥ b)) (WithLp.toLp 2 x₀) out.1.arnoldi.k
        (WithLp.toLp 2 out.2) ∧
      (∀ i : Fin (m + 1), (i : ℕ) = out.1.arnoldi.k →
        |out.1.g i| = ‖(WithLp.toLp 2 (Mp⁻¹ *ᵥ (b - A *ᵥ out.2)) : EuclideanSpace ℝ (Fin n))‖) ∧
      (out.1.arnoldi.done = true → A *ᵥ out.2 = b) := by
  have hB : IsUnit (Mp⁻¹ * A) := ((Matrix.isUnit_nonsing_inv_iff).2 hM).mul hA
  have hrun : Id.run (algorithm_11_5_2 pure A (fun r => pure (Mp⁻¹ *ᵥ r)) b x₀ m) =
      Id.run (gmresCore pure (fun q => pure ((Mp⁻¹ * A) *ᵥ q)) x₀
        (Mp⁻¹ *ᵥ (b - A *ᵥ x₀)) m) := by
    have hop' : ∀ q, Id.run (do
        let w ← GolubVanLoan.Chapter01.algorithm_1_1_3 pure A q 0
        (pure (Mp⁻¹ *ᵥ w) : Id (Fin n → ℝ))) = (Mp⁻¹ * A) *ᵥ q := fun q => by
      simp only [Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, Id.run_pure]
      rw [zero_add, mulVec_mulVec]
    have hop : (fun q => (do
        let w ← GolubVanLoan.Chapter01.algorithm_1_1_3 pure A q 0
        (pure (Mp⁻¹ *ᵥ w) : Id (Fin n → ℝ)))) = fun q => pure ((Mp⁻¹ * A) *ᵥ q) :=
      funext fun q => hop' q
    simp only [algorithm_11_5_2, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
      mulVec_neg, ← sub_eq_add_neg]
    exact congrArg (fun f => Id.run (gmresCore pure f x₀ (Mp⁻¹ *ᵥ (b - A *ᵥ x₀)) m)) hop
  have hz : Mp⁻¹ *ᵥ (b - A *ᵥ x₀) = Mp⁻¹ *ᵥ b - (Mp⁻¹ * A) *ᵥ x₀ := by
    rw [mulVec_sub, mulVec_mulVec]
  obtain ⟨hk, -, hmin, hg, hdone⟩ := gmresCore_spec (op := fun q => pure ((Mp⁻¹ * A) *ᵥ q)) hB
    (fun q => rfl) (Mp⁻¹ *ᵥ b) x₀ (Mp⁻¹ *ᵥ (b - A *ᵥ x₀)) hz m
  have hres : ∀ x : Fin n → ℝ, (WithLp.toLp 2 (Mp⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) -
      toEuclideanLin (Mp⁻¹ * A) (WithLp.toLp 2 x) = WithLp.toLp 2 (Mp⁻¹ *ᵥ (b - A *ᵥ x)) :=
    fun x => by rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, mulVec_sub, mulVec_mulVec]
  dsimp only
  rw [hrun]
  refine ⟨hk, hmin, fun i hi => by rw [hg i hi, hres], fun hd => ?_⟩
  have hMA : ∀ x : Fin n → ℝ, Mp *ᵥ ((Mp⁻¹ * A) *ᵥ x) = A *ᵥ x := fun x => by
    rw [← mulVec_mulVec, mulVec_nonsing_inv_mulVec hM]
  have h := congrArg (Mp *ᵥ ·) (hdone hd)
  simp only [hMA, mulVec_nonsing_inv_mulVec hM] at h
  exact h

end PreconditionedGMRES

end GolubVanLoan.Chapter11
