import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.PSeries
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.Superlinear
import Numlib.Krylov.Subspace
import Numlib.LinearSolve.Projection.Optimality

/-!
# Atkinson–Han §5.6: the conjugate gradient method for operator equations

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.6: the conjugate gradient method for
`A u = f` in a Hilbert space, its linear and Chebyshev convergence rates, and Winther's
superlinear rate for a second-kind equation.

Throughout, `V` is a real Hilbert space and `A : V →L[ℝ] V` is bounded, self-adjoint and positive
definite in the sense of (5.6.3), `√m ‖v‖ ≤ ‖v‖_A ≤ √M ‖v‖` with `m, M > 0`.

## Book-specific definitions

* `innerA`, `normA` — the `A`-inner product and `A`-norm of §5.6, identified with the backbone's
  `energyInner` and `energyNorm` (`Numlib/Analysis/InnerProductSpace/Energy.lean`) by
  `innerA_eq` and `normA_eq`.
* `CGState`, `cgStep`, `cg` — the conjugate gradient iteration (5.6.2) as the book writes it,
  with the explicit residual `r_{k+1} = f - A u_{k+1}`; `cg_eq_CG_iterate` identifies it with the
  backbone's `CG.iterate` (`Numlib/Krylov/CG.lean`), whose residual obeys the recurrence
  `r_{k+1} = r_k - α_k A s_k` instead.

## Main results

* `isSymmetricBoundedBy_of_bound` — (5.6.3) is the backbone's `LinearMap.IsSymmetricBoundedBy`
  (`Numlib/Analysis/InnerProductSpace/Coercive.lean`), the hypothesis every Chebyshev-type
  estimate takes.
* `existsUnique_solution` — the setting of §5.6: `A u = f` is uniquely solvable and
  `‖A⁻¹‖ ≤ 1/m`.
* `theorem_5_6_1` — Theorem 5.6.1: the iterates converge, at the linear rate (5.6.4)
  (`equation_5_6_4`).
* `equation_5_6_5` — the sharper Chebyshev bound (5.6.5), which the book quotes from Patterson,
  *Iterative Methods for the Solution of a Linear Operator Equation in Hilbert Space — A Survey*,
  and `equation_5_6_6` (Exercise 5.6.1) that its rate is the better of the two.
* `normA_error_min` — the closing remark of §5.6: `u_k` minimizes the `A`-norm of the error over
  `u₀ + 𝒦_k`.
* `theorem_5_6_2` — Theorem 5.6.2, the superlinear convergence the book takes from Winther,
  *Some superlinear convergence results for the conjugate gradient method*, for `A = I - K`, with
  the setting (5.6.7)–(5.6.9) as `isSymmetricBoundedBy_of_one_sub` and the linear rate (5.6.10)
  as `equation_5_6_10`.
* `equation_5_6_8`, `equation_5_6_9` — (5.6.8) and (5.6.9) in the eigenbasis: `A = I - K` is
  positive definite exactly when `δ > 0`, and then `‖A‖ = Δ`, `‖A⁻¹‖ = 1/δ`, with `Δ` and `δ` the
  supremum and infimum of the `1 - λ_j`. `norm_le_of_isSymmetricBoundedBy` is the
  quadratic-form-to-operator-norm step behind `‖A‖ ≤ Δ`.
* `tau`, `theorem_5_6_3_a`, `theorem_5_6_3_b` — Theorem 5.6.3, the two decay rates for the
  Cesàro average `τ_ℓ = (1/ℓ) ∑_{j < ℓ} |λ_j|/(1 - λ_j)` that drives the superlinear estimate:
  `ℓ^{-1/2}` for a Hilbert-Schmidt kernel and `ℓ^{-1}` for a `Cᵖ` symmetric one.
  `wintherRate_eq_tau` identifies `τ_k` inside the backbone's rate.

## Conventions

`cg_energyNorm_error_step_le` is the one statement here that is not a book statement: it is the
per-step Kantorovich contraction in the backbone's own vocabulary, shared with §9.4, and belongs
in `Numlib/Krylov/Convergence/CG.lean`.

In Theorem 5.6.2 the eigen-decomposition of `K` is taken as *data* rather than produced from
compactness: what Mathlib lacks is not the spectral theorem for compact self-adjoint operators,
which it has, but the decreasing enumeration of the eigenvalues of a compact operator as an
`ℕ`-sequence. The constant is the backbone's `Krylov.wintherRate`, which is sharper than the
book's `(Δ/δ)^{3/(2k)}` prefactor and has the same limit `0`.

## Not formalized here

The step *from compactness of `K` to the eigen-decomposition*: (5.6.7)–(5.6.9) are stated with a
`HilbertBasis ℕ ℝ V` of eigenvectors as data, not derived from `K` being compact and self-adjoint.
Mathlib has the spectral theorem for compact self-adjoint operators, but no decreasing enumeration
of the eigenvalues of one as an `ℕ`-sequence, which is what (5.6.8) asks for; the same gap is
recorded on `Numlib/Krylov/Convergence/Superlinear`.

The two quantitative inputs of Theorem 5.6.3 are hypotheses rather than conclusions, for the same
kind of reason: `∑_j λ_j² = ‖K‖²_HS` is Theorem 2.8.15 of the book and Mathlib has no
Hilbert-Schmidt norm for kernel operators on `C(Icc a b × Icc a b, ℝ)`; and the eigenvalue decay
`|λ_j| ≤ M j^{-(p+1/2)}` for a `Cᵖ` symmetric kernel is what the book itself quotes from Fenyő and
Stolle, eigenvalue asymptotics of a kind Mathlib does not have.
-/

open Filter Topology

namespace AtkinsonHan.Chapter05

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Energy

/-- §5.6: the `A`-inner product `(v, u)_A = (A v, u)`. -/
noncomputable def innerA (A : V →L[ℝ] V) (v u : V) : ℝ := inner ℝ (A v) u

/-- §5.6: the `A`-norm `‖v‖_A = √((v, v)_A)`. -/
noncomputable def normA (A : V →L[ℝ] V) (v : V) : ℝ := Real.sqrt (innerA A v v)

/-- The book's `A`-inner product is the backbone's energy inner product. -/
theorem innerA_eq (A : V →L[ℝ] V) (v u : V) :
    innerA A v u = energyInner (A : V →ₗ[ℝ] V) v u := rfl

/-- The book's `A`-norm is the backbone's energy norm. -/
theorem normA_eq (A : V →L[ℝ] V) (v : V) : normA A v = energyNorm (A : V →ₗ[ℝ] V) v := rfl

/-- The `A`-norm is nonnegative, being a square root. -/
theorem normA_nonneg (A : V →L[ℝ] V) (v : V) : 0 ≤ normA A v := Real.sqrt_nonneg _

end Energy

section PositiveDefinite

variable [CompleteSpace V]

/-- **(5.6.3)** identified with the backbone's quadratic-form bounds
`LinearMap.IsSymmetricBoundedBy` — the hypothesis of every Chebyshev-type convergence estimate. -/
theorem isSymmetricBoundedBy_of_bound {A : V →L[ℝ] V} (hA : IsSelfAdjoint A) {m M : ℝ}
    (hm : 0 < m) (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖) :
    (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy m M := by
  have hsym : (A : V →ₗ[ℝ] V).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hinner : ∀ x : V, 0 ≤ inner ℝ (A x) x := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    by_contra hneg
    push Not at hneg
    have hzero : normA A x = 0 := Real.sqrt_eq_zero_of_nonpos hneg.le
    have h1 := (hbound x).1
    rw [hzero] at h1
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    nlinarith
  have hsq : ∀ x : V, normA A x ^ 2 = inner ℝ (A x) x := fun x => Real.sq_sqrt (hinner x)
  refine ⟨hsym, fun x => ?_, fun x => ?_⟩
  · have h1 := (hbound x).1
    have h2 : (Real.sqrt m * ‖x‖) ^ 2 ≤ normA A x ^ 2 := by
      have hnn : 0 ≤ Real.sqrt m * ‖x‖ := by positivity
      nlinarith [normA_nonneg A x]
    rw [mul_pow, Real.sq_sqrt hm.le, hsq] at h2
    simpa [RCLike.re_to_real] using h2
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hlow := (hbound x).1
    have h1 := (hbound x).2
    have hMpos : 0 < Real.sqrt M := by nlinarith
    have hM : 0 ≤ M := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at hMpos
      exact lt_irrefl 0 hMpos
    have h2 : normA A x ^ 2 ≤ (Real.sqrt M * ‖x‖) ^ 2 := by
      nlinarith [normA_nonneg A x]
    rw [hsq, mul_pow, Real.sq_sqrt hM] at h2
    simpa [RCLike.re_to_real] using h2

/-- The setting of §5.6: `A u = f` is uniquely solvable and `‖A⁻¹‖ ≤ 1/m`.  The book derives this
from Theorem 5.1.4; here it is the backbone's
`ContinuousLinearMap.exists_equiv_of_isCoerciveWith`
(`Numlib/Analysis/InnerProductSpace/Coercive.lean`). -/
theorem existsUnique_solution {A : V →L[ℝ] V} (hA : IsSelfAdjoint A) {m M : ℝ} (hm : 0 < m)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖) :
    (∀ f : V, ∃! u, A u = f) ∧
      ∃ e : V ≃L[ℝ] V, (e : V →L[ℝ] V) = A ∧ ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 / m := by
  have hA' := isSymmetricBoundedBy_of_bound hA hm hbound
  obtain ⟨e, he, hnorm⟩ :=
    ContinuousLinearMap.exists_equiv_of_isCoerciveWith hm hA'.isCoerciveWith
  refine ⟨fun f => ⟨e.symm f, ?_, fun u hu => ?_⟩, ⟨e, he, hnorm⟩⟩
  · rw [← he]
    exact e.apply_symm_apply f
  · rw [← hu, ← he]
    exact (e.symm_apply_apply u).symm

end PositiveDefinite

section Iteration

/-- The state `(u_k, r_k, s_k)` of the conjugate gradient iteration (5.6.2). -/
@[ext]
structure CGState (V : Type*) where
  /-- The iterate `u_k`. -/
  u : V
  /-- The residual `r_k = f - A u_k`. -/
  r : V
  /-- The search direction `s_k`. -/
  s : V

/-- **(5.6.2)**: one step of the conjugate gradient method, `α_k = ‖r_k‖²/(A s_k, s_k)`,
`u_{k+1} = u_k + α_k s_k`, `r_{k+1} = f - A u_{k+1}`, `β_k = ‖r_{k+1}‖²/‖r_k‖²`,
`s_{k+1} = r_{k+1} + β_k s_k`.  Lean's `x / 0 = 0` makes the recurrences total: after breakdown
(`r_k = 0`) both `α_k` and `β_k` are `0` and the iterate is frozen, the same convention as the
backbone. -/
noncomputable def cgStep (A : V →L[ℝ] V) (f : V) (st : CGState V) : CGState V :=
  let α := ‖st.r‖ ^ 2 / inner ℝ (A st.s) st.s
  let u' := st.u + α • st.s
  let r' := f - A u'
  let β := ‖r'‖ ^ 2 / ‖st.r‖ ^ 2
  ⟨u', r', r' + β • st.s⟩

/-- The `k`-th conjugate gradient state, started from `r₀ = s₀ = f - A u₀`. -/
noncomputable def cg (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) : CGState V :=
  (cgStep A f)^[k] ⟨u₀, f - A u₀, f - A u₀⟩

/-- The conjugate gradient iteration starts at `u₀` with `r₀ = s₀ = f - A u₀`. -/
theorem cg_zero (A : V →L[ℝ] V) (f u₀ : V) :
    cg A f u₀ 0 = ⟨u₀, f - A u₀, f - A u₀⟩ := rfl

/-- Each conjugate gradient state is one `cgStep` past the previous one. -/
theorem cg_succ (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    cg A f u₀ (k + 1) = cgStep A f (cg A f u₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The book's state read off from the backbone's CG state. -/
def ofCGState (s : CG.State V) : CGState V := ⟨s.x, s.r, s.p⟩

/-- One step of the book's iteration agrees with one step of the backbone's, provided the
incoming state carries the residual `r = f - A x`. -/
private theorem cgStep_ofCGState (A : V →L[ℝ] V) (f : V) {s : CG.State V}
    (hres : s.r = f - A s.x) :
    cgStep A f (ofCGState s) = ofCGState (CG.step (A : V →ₗ[ℝ] V) s) := by
  have hcoe : (A : V →ₗ[ℝ] V) s.p = A s.p := rfl
  have hα : ‖s.r‖ ^ 2 / inner ℝ (A s.p) s.p = CG.alpha (A : V →ₗ[ℝ] V) s := by
    rw [CG.alpha, real_inner_self_eq_norm_sq, hcoe]
  have hu : (cgStep A f (ofCGState s)).u = (ofCGState (CG.step (A : V →ₗ[ℝ] V) s)).u := by
    change s.x + (‖s.r‖ ^ 2 / inner ℝ (A s.p) s.p) • s.p = (CG.step (A : V →ₗ[ℝ] V) s).x
    rw [CG.step_x, hα]
  have hr : (cgStep A f (ofCGState s)).r = (ofCGState (CG.step (A : V →ₗ[ℝ] V) s)).r := by
    change f - A (s.x + (‖s.r‖ ^ 2 / inner ℝ (A s.p) s.p) • s.p)
      = (CG.step (A : V →ₗ[ℝ] V) s).r
    rw [CG.step_r, hα, hres, map_add, map_smul, hcoe]
    abel
  refine CGState.ext hu hr ?_
  change (cgStep A f (ofCGState s)).r
      + (‖(cgStep A f (ofCGState s)).r‖ ^ 2 / ‖s.r‖ ^ 2) • s.p = (CG.step (A : V →ₗ[ℝ] V) s).p
  rw [hr]
  change (CG.step (A : V →ₗ[ℝ] V) s).r
      + (‖(CG.step (A : V →ₗ[ℝ] V) s).r‖ ^ 2 / ‖s.r‖ ^ 2) • s.p = (CG.step (A : V →ₗ[ℝ] V) s).p
  rw [CG.step_p, CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- **Equivalence with the backbone**: the book's iteration (5.6.2) is the backbone's
`CG.iterate` (`Numlib/Krylov/CG.lean`), whose residual recurrence is `r_{k+1} = r_k - α_k A s_k`
rather than the book's explicit `r_{k+1} = f - A u_{k+1}`. -/
theorem cg_eq_CG_iterate (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    cg A f u₀ k = ofCGState (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cg_succ, ih, CG.iterate_succ,
      cgStep_ofCGState A f (CG.residual_eq (A : V →ₗ[ℝ] V) f u₀ k)]

/-- The book's iterate `u_k` is the backbone's `x`. -/
theorem cg_u (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).u = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).x := by
  rw [cg_eq_CG_iterate]
  rfl

/-- The book's residual `r_k` is the backbone's `r`. -/
theorem cg_r (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).r = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).r := by
  rw [cg_eq_CG_iterate]
  rfl

/-- The book's search direction `s_k` is the backbone's `p`. -/
theorem cg_s (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).s = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).p := by
  rw [cg_eq_CG_iterate]
  rfl

end Iteration

section KantorovichStep

/-- One conjugate gradient step is at least as good as one steepest-descent step, so the energy
norm of the error contracts by the Kantorovich factor `(lmax - lmin) / (lmax + lmin)`.

Stated in the backbone's vocabulary because both §5.6 (`equation_5_6_4`) and §9.4
(`AtkinsonHan.Chapter09.cg_energy_rate`) specialize it.  It is a two-line assembly of
`IsGalerkin.energyNorm_le` (the conjugate gradient iterate is optimal in the energy norm over
`x₀ + 𝒦_{k+1}`) and the Kantorovich bound for one steepest-descent step, which the backbone
assembles as `Krylov.IsGalerkinIterate.energyNorm_error_succ_le`. -/
theorem cg_energyNorm_error_step_le {A : V →ₗ[ℝ] V} {b x₀ xstar : V} {lmin lmax : ℝ}
    (hl : 0 < lmin) (hA : A.IsSymmetricBoundedBy lmin lmax) (hstar : A xstar = b) (k : ℕ) :
    energyNorm A (xstar - (CG.iterate A b x₀ (k + 1)).x)
      ≤ (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - (CG.iterate A b x₀ k).x) :=
  have hAc := hA.isSymmetricCoercive hl
  Krylov.IsGalerkinIterate.energyNorm_error_succ_le hl hA (CG.isGalerkinIterate b x₀ hAc k)
    (CG.isGalerkinIterate b x₀ hAc (k + 1)) hstar

end KantorovichStep

section Convergence

variable [CompleteSpace V] {A : V →L[ℝ] V} {m M : ℝ} {f u₀ ustar : V}

set_option linter.unusedSectionVars false in
/-- **(5.6.6)** (Exercise 5.6.1): the Chebyshev rate of (5.6.5) is at least as good as the
steepest-descent rate of (5.6.4). -/
theorem equation_5_6_6 (hm : 0 < m) (hmM : m ≤ M) :
    (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) ≤ (M - m) / (M + m) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ m = s ^ 2 :=
    ⟨Real.sqrt m, Real.sqrt_pos.2 hm, (Real.sq_sqrt hm.le).symm⟩
  obtain ⟨t, ht0, rfl⟩ : ∃ t : ℝ, 0 < t ∧ M = t ^ 2 :=
    ⟨Real.sqrt M, Real.sqrt_pos.2 hM, (Real.sq_sqrt hM.le).symm⟩
  rw [Real.sqrt_sq hs0.le, Real.sqrt_sq ht0.le,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hst : s ≤ t := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hst) (mul_pos hs0 ht0).le]

/-- The closing remark of §5.6: the conjugate gradient iterate minimizes the `A`-norm of the error
over the affine Krylov space `u₀ + 𝒦_k(A, r₀)`.  This is the backbone's
`IsGalerkin.energyNorm_le` together with `CG.isGalerkinIterate`. -/
theorem normA_error_min (hA : IsSelfAdjoint A) (hm : 0 < m)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) (k : ℕ) {y : V}
    (hy : y - u₀ ∈ Krylov.subspace (A : V →ₗ[ℝ] V) (f - A u₀) k) :
    normA A (ustar - (cg A f u₀ k).u) ≤ normA A (ustar - y) := by
  have hA' := isSymmetricBoundedBy_of_bound hA hm hbound
  have hAc := hA'.isSymmetricCoercive hm
  rw [cg_u, normA_eq, normA_eq]
  exact (CG.isGalerkinIterate f u₀ hAc k).energyNorm_le hAc hstar hy

/-- **(5.6.4)**: one conjugate gradient step contracts the `A`-norm of the error by the factor
`(M - m)/(M + m)`.  This is `cg_energyNorm_error_step_le` read through the identification
`cg_u` of the book's iteration with the backbone's. -/
theorem equation_5_6_4 (hA : IsSelfAdjoint A) (hm : 0 < m)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) (k : ℕ) :
    normA A (ustar - (cg A f u₀ (k + 1)).u)
      ≤ (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u) := by
  rw [cg_u, cg_u, normA_eq, normA_eq]
  exact cg_energyNorm_error_step_le hm (isSymmetricBoundedBy_of_bound hA hm hbound) hstar k

/-- **Theorem 5.6.1.** The conjugate gradient iterates converge to the solution of `A u = f`, at
the linear rate (5.6.4). -/
theorem theorem_5_6_1 (hA : IsSelfAdjoint A) (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) :
    Tendsto (fun k => (cg A f u₀ k).u) atTop (𝓝 ustar) ∧
      ∀ k, normA A (ustar - (cg A f u₀ (k + 1)).u)
        ≤ (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u) := by
  refine ⟨?_, fun k => equation_5_6_4 hA hm hbound hstar k⟩
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ (M - m) / (M + m) ≤ ρ := by
    refine ⟨max ((M - m) / (M + m)) 0, le_max_right _ _, max_lt ?_ one_pos, le_max_left _ _⟩
    rw [div_lt_one (by linarith)]
    linarith
  have hgeom : ∀ k, normA A (ustar - (cg A f u₀ k).u) ≤ ρ ^ k * normA A (ustar - u₀) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, one_mul]
      exact le_of_eq rfl
    | succ k ih =>
      have h1 := equation_5_6_4 (u₀ := u₀) hA hm hbound hstar k
      have h2 : (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u)
          ≤ ρ * normA A (ustar - (cg A f u₀ k).u) :=
        mul_le_mul_of_nonneg_right hρle (normA_nonneg _ _)
      calc normA A (ustar - (cg A f u₀ (k + 1)).u)
          ≤ ρ * normA A (ustar - (cg A f u₀ k).u) := h1.trans h2
        _ ≤ ρ * (ρ ^ k * normA A (ustar - u₀)) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * normA A (ustar - u₀) := by ring
  have hmpos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hbnd : ∀ k, ‖(cg A f u₀ k).u - ustar‖ ≤ ρ ^ k * normA A (ustar - u₀) / Real.sqrt m := by
    intro k
    rw [le_div_iff₀ hmpos, ← norm_neg, neg_sub]
    calc ‖ustar - (cg A f u₀ k).u‖ * Real.sqrt m
        = Real.sqrt m * ‖ustar - (cg A f u₀ k).u‖ := mul_comm _ _
      _ ≤ normA A (ustar - (cg A f u₀ k).u) := (hbound _).1
      _ ≤ ρ ^ k * normA A (ustar - u₀) := hgeom k
  have hlim : Tendsto (fun k : ℕ => ρ ^ k * normA A (ustar - u₀) / Real.sqrt m) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const
      (normA A (ustar - u₀) / Real.sqrt m)
    simpa [mul_div_assoc] using h
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun k => norm_nonneg _) hbnd hlim)

/-- **(5.6.5)**: the Chebyshev bound
`‖u* - u_k‖_A ≤ 2 ((√M - √m)/(√M + √m))ᵏ ‖u* - u₀‖_A`, which the book quotes from Patterson
rather than proving.  This is the backbone's
`Krylov.IsGalerkinIterate.energyNorm_error_le` (`Numlib/Krylov/Convergence/CG.lean`), whose rate
is written with the condition number `κ = M/m`. -/
theorem equation_5_6_5 (hA : IsSelfAdjoint A) (hm : 0 < m) (hmM : m ≤ M)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) (k : ℕ) :
    normA A (ustar - (cg A f u₀ k).u)
      ≤ 2 * ((Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m)) ^ k *
        normA A (ustar - u₀) := by
  have hA' := isSymmetricBoundedBy_of_bound hA hm hbound
  have hAc := hA'.isSymmetricCoercive hm
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have ht : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hid : (Real.sqrt (M / m) - 1) / (Real.sqrt (M / m) + 1)
      = (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) := by
    have hd1 : Real.sqrt M / Real.sqrt m + 1 ≠ 0 := by positivity
    have hd2 : Real.sqrt M + Real.sqrt m ≠ 0 := by positivity
    rw [Real.sqrt_div hM.le m, div_eq_div_iff hd1 hd2]
    field_simp
  have hmain := (CG.isGalerkinIterate f u₀ hAc k).energyNorm_error_le hm hmM hA' hstar
  rw [cg_u, normA_eq, normA_eq, ← hid]
  exact hmain

end Convergence

section Superlinear

variable [CompleteSpace V] {A K : V →L[ℝ] V} {lam : ℕ → ℝ} {δ Δ : ℝ} {f u₀ ustar : V}

/-- **(5.6.7)–(5.6.9)**: the setting of Theorem 5.6.2.  `A = I − K` with `K` self-adjoint and
diagonal in a Hilbert basis `φ` with eigenvalues `λ`, and `0 < δ ≤ 1 − λ_j ≤ Δ` for every `j`.
Then `A` satisfies (5.6.3) with `m = δ` and `M = Δ`, which is the backbone's
`LinearMap.IsSymmetricBoundedBy δ Δ`; the derivation is Parseval in the eigenbasis
(`Krylov.isSymmetricBoundedBy_of_eq_one_sub`). -/
theorem isSymmetricBoundedBy_of_one_sub (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V))
    (hK : IsSelfAdjoint K) (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ) :
    (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy δ Δ :=
  Krylov.isSymmetricBoundedBy_of_eq_one_sub hAK
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK) φ
    (fun j => by simpa using hlam j) hlow hupp

omit [CompleteSpace V] in
/-- The eigenrelation `A φ_j = (1 − λ_j) φ_j` behind (5.6.8) and (5.6.9). -/
theorem apply_eigenvector (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (j : ℕ) : A (φ j) = (1 - lam j) • φ j := by
  have h' : (A : V →ₗ[ℝ] V) (φ j) = ((1 : V →ₗ[ℝ] V) - (K : V →ₗ[ℝ] V)) (φ j) := by rw [hAK]
  have h : A (φ j) = φ j - K (φ j) := by simpa using h'
  rw [h, hlam j, sub_smul, one_smul]

omit [CompleteSpace V] in
/-- Each `1 − λ_j` is at most `‖A‖`: it is the eigenvalue of `A` at the unit vector `φ_j`. -/
theorem one_sub_le_norm (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (j : ℕ) :
    1 - lam j ≤ ‖A‖ := by
  have hpos : 0 < 1 - lam j := lt_of_lt_of_le hδ (hlow j)
  have hnorm : ‖φ j‖ = 1 := φ.orthonormal.1 j
  have hle := A.le_opNorm (φ j)
  rw [apply_eigenvector hAK φ hlam j, norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos hpos] at hle
  linarith [hle]

omit [CompleteSpace V] in
/-- Every term of `τ_ℓ` is bounded by `‖(I − K)⁻¹‖`: the eigenvalues of `(I − K)⁻¹` are the
`1/(1 − λ_j)`, and an eigenvalue of a bounded operator is at most its norm. -/
theorem one_div_one_sub_le_norm_symm (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V))
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (e : V ≃L[ℝ] V) (he : (e : V →L[ℝ] V) = A) (j : ℕ) :
    1 / (1 - lam j) ≤ ‖(e.symm : V →L[ℝ] V)‖ := by
  have hpos : 0 < 1 - lam j := lt_of_lt_of_le hδ (hlow j)
  have hnorm : ‖φ j‖ = 1 := φ.orthonormal.1 j
  have hA : A (φ j) = (1 - lam j) • φ j := apply_eigenvector hAK φ hlam j
  have he' : ∀ x : V, e x = A x := fun x => by rw [← he]; rfl
  have hsymm : (e.symm : V →L[ℝ] V) (φ j) = (1 - lam j)⁻¹ • φ j := by
    have hfwd : e ((1 - lam j)⁻¹ • φ j) = φ j := by
      rw [he', map_smul, hA, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    calc (e.symm : V →L[ℝ] V) (φ j) = e.symm (φ j) := rfl
      _ = e.symm (e ((1 - lam j)⁻¹ • φ j)) := by rw [hfwd]
      _ = (1 - lam j)⁻¹ • φ j := e.symm_apply_apply _
  have hle := ContinuousLinearMap.le_opNorm (e.symm : V →L[ℝ] V) (φ j)
  rw [hsymm, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hpos)] at hle
  rw [one_div]
  linarith [hle]

omit [CompleteSpace V] in
/-- Quadratic-form bounds give an operator-norm bound: if `A` is symmetric with
`m ‖x‖² ≤ ⟪A x, x⟫ ≤ M ‖x‖²` and `m > 0`, then `‖A‖ ≤ M`.  Cauchy–Schwarz for the energy inner
product (`LinearMap.IsSymmetricCoercive.abs_energyInner_le`) applied to `x` and `A x` turns the
bound on the quadratic form into a bound on the norm. -/
theorem norm_le_of_isSymmetricBoundedBy {A : V →L[ℝ] V} {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hA : (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy m M) : ‖A‖ ≤ M := by
  have hcoer := hA.isSymmetricCoercive hm
  have hen : ∀ y : V, energyNorm (A : V →ₗ[ℝ] V) y ≤ Real.sqrt M * ‖y‖ := by
    intro y
    have hsq : energyNorm (A : V →ₗ[ℝ] V) y ^ 2 ≤ (Real.sqrt M * ‖y‖) ^ 2 := by
      rw [hcoer.energyNorm_sq, mul_pow, Real.sq_sqrt hM]
      exact hA.re_inner_le y
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (energyNorm_nonneg _ y), Real.sqrt_sq (by positivity)] at h1
  refine ContinuousLinearMap.opNorm_le_bound A hM fun x => ?_
  rcases eq_or_ne (A x) 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  have hAxpos : 0 < ‖A x‖ := norm_pos_iff.2 h0
  have hcs := hcoer.abs_energyInner_le x (A x)
  have hval : ‖energyInner (A : V →ₗ[ℝ] V) x (A x)‖ = ‖A x‖ ^ 2 := by
    rw [energyInner]
    simp
  rw [hval] at hcs
  have hbound : ‖A x‖ ^ 2 ≤ (Real.sqrt M * ‖x‖) * (Real.sqrt M * ‖A x‖) :=
    hcs.trans (mul_le_mul (hen x) (hen (A x)) (energyNorm_nonneg _ _) (by positivity))
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have heq : Real.sqrt M * ‖x‖ * (Real.sqrt M * ‖A x‖) = M * ‖x‖ * ‖A x‖ := by
    have hre : Real.sqrt M * ‖x‖ * (Real.sqrt M * ‖A x‖)
        = Real.sqrt M * Real.sqrt M * (‖x‖ * ‖A x‖) := by ring
    rw [hre, hMM]; ring
  rw [heq, pow_two] at hbound
  exact le_of_mul_le_mul_right hbound hAxpos

/-- **(5.6.8)**: in the setting of Theorem 5.6.2, `A = I − K` is positive definite in the sense of
(5.6.3) exactly when `δ = 1 − sup_j λ_j > 0`, `δ` being the infimum of the `1 − λ_j`.

Positivity at the eigenvector `φ_j` forces the coercivity constant below every `1 − λ_j`, hence
below their infimum; conversely `δ > 0` is itself a coercivity constant, by Parseval in the
eigenbasis (`isSymmetricBoundedBy_of_one_sub`). -/
theorem equation_5_6_8 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hlow : ∀ j, δ ≤ 1 - lam j)
    (hinf : ∀ ε > 0, ∃ j, 1 - lam j < δ + ε) (hupp : ∀ j, 1 - lam j ≤ Δ) :
    (∃ m > 0, (A : V →ₗ[ℝ] V).IsCoerciveWith m) ↔ 0 < δ := by
  constructor
  · rintro ⟨m, hm, hcoer⟩
    have hj : ∀ j, m ≤ 1 - lam j := by
      intro j
      have h := hcoer (φ j)
      have hval : (A : V →ₗ[ℝ] V) (φ j) = (1 - lam j) • φ j := apply_eigenvector hAK φ hlam j
      simpa [hval, real_inner_smul_left, real_inner_self_eq_norm_sq, φ.orthonormal.1 j] using h
    refine lt_of_lt_of_le hm (le_of_forall_pos_le_add fun ε hε => ?_)
    obtain ⟨j, hjlt⟩ := hinf ε hε
    exact le_of_lt (lt_of_le_of_lt (hj j) hjlt)
  · intro hδ
    exact ⟨δ, hδ, (isSymmetricBoundedBy_of_one_sub hAK hK φ hlam hlow hupp).isCoerciveWith⟩

/-- **(5.6.9)**: in the setting of Theorem 5.6.2, `‖A‖ = Δ` and `‖A⁻¹‖ = 1/δ`, with `Δ` the
supremum and `δ` the infimum of the `1 − λ_j`.  The inequalities `‖A‖ ≤ Δ` and `‖A⁻¹‖ ≤ 1/δ` are
the quadratic-form bounds of `isSymmetricBoundedBy_of_one_sub`; the reverse ones are the values of
`A` and of `A⁻¹` at the unit eigenvectors `φ_j`, which come arbitrarily close to `Δ` and to `δ`. -/
theorem equation_5_6_9 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ)
    (hsup : ∀ ε > 0, ∃ j, Δ - ε < 1 - lam j) (hinf : ∀ ε > 0, ∃ j, 1 - lam j < δ + ε)
    (e : V ≃L[ℝ] V) (he : (e : V →L[ℝ] V) = A) :
    ‖A‖ = Δ ∧ ‖(e.symm : V →L[ℝ] V)‖ = 1 / δ := by
  have hbdd := isSymmetricBoundedBy_of_one_sub hAK hK φ hlam hlow hupp
  have hΔ : 0 < Δ := lt_of_lt_of_le hδ ((hlow 0).trans (hupp 0))
  constructor
  · refine le_antisymm (norm_le_of_isSymmetricBoundedBy hδ hΔ.le hbdd) ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨j, hj⟩ := hsup ε hε
    have := one_sub_le_norm hAK φ hlam hδ hlow j
    linarith
  · -- `‖A⁻¹‖ ≤ 1/δ` from coercivity, `≥` from the eigenvector nearest the infimum
    have hle : ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 / δ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      have hAx : A ((e.symm : V →L[ℝ] V) y) = y := by
        rw [← he]
        exact e.apply_symm_apply y
      have hco : δ * ‖(e.symm : V →L[ℝ] V) y‖ ^ 2
          ≤ inner ℝ (A ((e.symm : V →L[ℝ] V) y)) ((e.symm : V →L[ℝ] V) y) := by
        simpa using hbdd.le_re_inner ((e.symm : V →L[ℝ] V) y)
      rw [hAx] at hco
      have hcs : inner ℝ y ((e.symm : V →L[ℝ] V) y) ≤ ‖y‖ * ‖(e.symm : V →L[ℝ] V) y‖ :=
        real_inner_le_norm _ _
      rcases eq_or_lt_of_le (norm_nonneg ((e.symm : V →L[ℝ] V) y)) with hx0 | hx0
      · rw [← hx0]
        positivity
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
        nlinarith [hco, hcs, hx0]
    refine le_antisymm hle ?_
    have hpos : 0 < ‖(e.symm : V →L[ℝ] V)‖ := by
      have h0 := one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he 0
      have hjpos : 0 < 1 - lam 0 := lt_of_lt_of_le hδ (hlow 0)
      have hd : 0 < 1 / (1 - lam 0) := by positivity
      linarith
    -- `1/‖A⁻¹‖` is a lower bound for the `1 - λ_j`, hence at most their infimum `δ`
    have hlb : 1 / ‖(e.symm : V →L[ℝ] V)‖ ≤ δ := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨j, hj⟩ := hinf ε hε
      have hjpos : 0 < 1 - lam j := lt_of_lt_of_le hδ (hlow j)
      have h2 := one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he j
      rw [div_le_iff₀ hjpos] at h2
      have h1 : 1 / ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 - lam j := by
        rw [div_le_iff₀ hpos]
        linarith [mul_comm ‖(e.symm : V →L[ℝ] V)‖ (1 - lam j)]
      linarith
    rw [div_le_iff₀ hpos] at hlb
    rw [div_le_iff₀ hδ]
    linarith [mul_comm δ ‖(e.symm : V →L[ℝ] V)‖]

/-- **(5.6.10)**: for `A = I − K` with `δ ≤ 1 − λ_j ≤ Δ`, the linear rate of (5.6.4) reads
`(Δ − δ)/(Δ + δ)`.  It is (5.6.4) with `m = δ` and `M = Δ`, the eigenvalue enclosure of `A`. -/
theorem equation_5_6_10 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ) (hstar : A ustar = f) (k : ℕ) :
    normA A (ustar - (cg A f u₀ (k + 1)).u)
      ≤ (Δ - δ) / (Δ + δ) * normA A (ustar - (cg A f u₀ k).u) := by
  rw [cg_u, cg_u, normA_eq, normA_eq]
  exact cg_energyNorm_error_step_le hδ
    (isSymmetricBoundedBy_of_one_sub hAK hK φ hlam hlow hupp) hstar k

/-- **Theorem 5.6.2** (Winther): superlinear convergence of the conjugate gradient method for a
second-kind equation `A u = f` with `A = I − K`.  The compact self-adjoint `K` is given through
its eigen-decomposition — a Hilbert basis `φ` of eigenvectors with eigenvalues `λ_j` enumerated so
that `|λ|` is antitone and `λ_j → 0`, which is what compactness supplies — together with the
enclosure `0 < δ ≤ 1 − λ_j ≤ Δ`.
Then (5.6.11) `‖u* − u_k‖ ≤ c_k^k ‖u* − u₀‖` with the rate `c_k` of (5.6.21), and `c_k → 0`.

Two departures from the book's statement, both recorded in `Numlib/Krylov/Convergence/Superlinear`:
the eigen-decomposition is taken as data rather than produced from compactness of `K`, because
Mathlib has no decreasing enumeration of the eigenvalues of a compact operator as an `ℕ`-sequence;
and the constant is `Krylov.wintherRate λ δ Δ k = (Δ/δ)^{1/(2k)} (2/k) ∑_{j<k} |λ_j|/(1 − λ_j)`,
which is sharper than the book's `(Δ/δ)^{3/(2k)}` prefactor and has the same limit `0`. -/
theorem theorem_5_6_2 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j)
    (hanti : Antitone fun j => |lam j|) (hlim : Tendsto lam atTop (𝓝 0)) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ) (hstar : A ustar = f) :
    (∀ k, ‖ustar - (cg A f u₀ k).u‖ ≤ Krylov.wintherRate lam δ Δ k ^ k * ‖ustar - u₀‖) ∧
      Tendsto (Krylov.wintherRate lam δ Δ) atTop (𝓝 0) := by
  have hΔ : 0 < Δ := hδ.trans_le ((hlow 0).trans (hupp 0))
  refine ⟨fun k => ?_, Krylov.winther_rate_tendsto_zero hδ hΔ hlim⟩
  rw [cg_u]
  exact Krylov.winther hAK (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK) φ
    (fun j => by simpa using hlam j) hanti hδ hlow hupp hstar k

/-- §5.6, **`τ_ℓ`** of Theorem 5.6.3: the Cesàro average
`τ_ℓ = (1/ℓ) ∑_{j < ℓ} |λ_j| / (1 − λ_j)` of the eigenvalue ratios of `K`, which is what makes the
superlinear rate of Theorem 5.6.2 tend to `0`.  The book indexes the eigenvalues from `1`; here
they are indexed from `0`, so the book's `λ_j` is `lam (j - 1)`. -/
noncomputable def tau (lam : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ)⁻¹ * ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)

/-- `τ_k` is the whole of `Krylov.wintherRate` beside its `(Δ/δ)^{1/(2k)}` prefactor: the book's
rate (5.6.21) is `(Δ/δ)^{3/(2k)} · 2 τ_k`, and the backbone proves the sharper form with the
exponent `1/(2k)`. -/
theorem wintherRate_eq_tau (lam : ℕ → ℝ) (δ Δ : ℝ) (k : ℕ) :
    Krylov.wintherRate lam δ Δ k = (Δ / δ) ^ (1 / (2 * k : ℝ)) * (2 * tau lam k) := by
  simp only [Krylov.wintherRate, tau]
  ring


omit [CompleteSpace V] in
/-- **Theorem 5.6.3(a)**: for a self-adjoint Hilbert–Schmidt `K`, the Cesàro average `τ_ℓ` is
squeezed between `(1/ℓ) |λ₁| / (1 − λ₁)` and `ℓ^{-1/2} ‖K‖_HS ‖(I − K)⁻¹‖`.  So `τ_ℓ → 0` at the
rate `ℓ^{-1/2}`, which is what makes the conjugate gradient method superlinearly convergent for a
second-kind equation with a Hilbert–Schmidt kernel, and the lower bound shows the rate cannot be
read off the leading eigenvalue alone.

The Hilbert–Schmidt norm enters only through `∑_j λ_j² = ‖K‖²_HS`, which is the hypothesis `hHS`
with `S = ‖K‖_HS`: that identity is Theorem 2.8.15 of the book, and Mathlib has no
Hilbert–Schmidt norm for the kernel operators of `C(Icc a b × Icc a b, ℝ)` to derive it from.  The
upper bound is then Cauchy–Schwarz applied to `∑_{j < ℓ} |λ_j|`, which is exactly why the exponent
is `-1/2`; `1/√ℓ` is written for the book's `ℓ^{-1/2}`. -/
theorem theorem_5_6_3_a (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (e : V ≃L[ℝ] V)
    (he : (e : V →L[ℝ] V) = A) {S : ℝ} (hS : 0 ≤ S) (hHS : HasSum (fun j => lam j ^ 2) (S ^ 2))
    {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (ℓ : ℝ)⁻¹ * (|lam 0| / (1 - lam 0)) ≤ tau lam ℓ ∧
      tau lam ℓ ≤ S * ‖(e.symm : V →L[ℝ] V)‖ / Real.sqrt ℓ := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hterm : ∀ j, 0 ≤ |lam j| / (1 - lam j) := fun j =>
    div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le hδ (hlow j)))
  have hC : 0 ≤ ‖(e.symm : V →L[ℝ] V)‖ := norm_nonneg _
  refine ⟨mul_le_mul_of_nonneg_left ?_ (by positivity), ?_⟩
  · exact Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_range.2 hℓ)
  -- the upper bound: bound each ratio by `|λ_j| ‖(I − K)⁻¹‖`, then Cauchy–Schwarz
  have hsum1 : ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ (∑ j ∈ Finset.range ℓ, |lam j|) * ‖(e.symm : V →L[ℝ] V)‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left
      (one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he j) (abs_nonneg _)
  have hpartial : ∑ j ∈ Finset.range ℓ, lam j ^ 2 ≤ S ^ 2 :=
    sum_le_hasSum (Finset.range ℓ) (fun j _ => sq_nonneg _) hHS
  have hcs : (∑ j ∈ Finset.range ℓ, |lam j|) ^ 2
      ≤ (ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, lam j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range ℓ) (f := fun j => |lam j|)
    simpa [sq_abs] using h
  have hnn : 0 ≤ ∑ j ∈ Finset.range ℓ, |lam j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsqrt : Real.sqrt ℓ * Real.sqrt ℓ = (ℓ : ℝ) := Real.mul_self_sqrt hℓ0.le
  have hsqrtpos : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ0
  have habs : ∑ j ∈ Finset.range ℓ, |lam j| ≤ Real.sqrt ℓ * S := by
    have hy : 0 ≤ Real.sqrt ℓ * S := mul_nonneg hsqrtpos.le hS
    have hsq2 : (Real.sqrt ℓ * S) ^ 2 = (ℓ : ℝ) * S ^ 2 := by
      rw [mul_pow, pow_two (Real.sqrt ℓ), hsqrt]
    have h1 : (∑ j ∈ Finset.range ℓ, |lam j|) ^ 2 ≤ (Real.sqrt ℓ * S) ^ 2 := by
      rw [hsq2]
      exact hcs.trans (mul_le_mul_of_nonneg_left hpartial hℓ0.le)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq hy] at h2
  have hmain : ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖ :=
    hsum1.trans (mul_le_mul_of_nonneg_right habs hC)
  have hfin : (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖)
      = S * ‖(e.symm : V →L[ℝ] V)‖ / Real.sqrt ℓ := by
    rw [eq_div_iff hsqrtpos.ne']
    have hre : (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖) * Real.sqrt ℓ
        = (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * Real.sqrt ℓ) * (S * ‖(e.symm : V →L[ℝ] V)‖) := by ring
    rw [hre, hsqrt, inv_mul_cancel₀ hℓ0.ne', one_mul]
  rw [tau]
  calc (ℓ : ℝ)⁻¹ * ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = S * ‖(e.symm : V →L[ℝ] V)‖ / Real.sqrt ℓ := hfin

omit [CompleteSpace V] in
/-- **Theorem 5.6.3(b)**: if the eigenvalues of `K` decay like `j^{-(p + 1/2)}` — which the book
quotes from Fenyő and Stolle for a symmetric kernel with continuous partial derivatives up to order
`p ≥ 1` — then `τ_ℓ ≤ (M/ℓ) ζ(p + 1/2) ‖(I − K)⁻¹‖`, one full order faster than the `ℓ^{-1/2}` of
part (a).

The decay is the hypothesis `hdecay`, not a conclusion: deriving it from smoothness of the kernel
is eigenvalue asymptotics for smooth kernels, of which Mathlib has nothing.  `ζ(p + 1/2)` is
written as the sum `∑' n, 1 / n^{p + 1/2}`, whose `n = 0` term vanishes. -/
theorem theorem_5_6_3_b (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (e : V ≃L[ℝ] V)
    (he : (e : V →L[ℝ] V) = A) {p M : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M)
    (hdecay : ∀ j : ℕ, |lam j| ≤ M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2))) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    tau lam ℓ ≤ M / ℓ * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hq : (1 : ℝ) < p + 1 / 2 := by linarith
  have hq0 : (0 : ℝ) < p + 1 / 2 := by linarith
  have hsummable : Summable fun n : ℕ => 1 / (n : ℝ) ^ (p + 1 / 2) :=
    Real.summable_one_div_nat_rpow.2 hq
  have hC : 0 ≤ ‖(e.symm : V →L[ℝ] V)‖ := norm_nonneg _
  have hstep : ∀ j : ℕ, |lam j| / (1 - lam j)
      ≤ M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by
    intro j
    calc |lam j| / (1 - lam j) = |lam j| * (1 / (1 - lam j)) := div_eq_mul_one_div _ _
      _ ≤ |lam j| * ‖(e.symm : V →L[ℝ] V)‖ :=
          mul_le_mul_of_nonneg_left
            (one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he j) (abs_nonneg _)
      _ ≤ M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ :=
          mul_le_mul_of_nonneg_right (hdecay j) hC
  have hshift : ∑ j ∈ Finset.range ℓ, 1 / ((j : ℝ) + 1) ^ (p + 1 / 2)
      = ∑ n ∈ Finset.range (ℓ + 1), 1 / (n : ℝ) ^ (p + 1 / 2) := by
    rw [Finset.sum_range_succ' (fun n => 1 / (n : ℝ) ^ (p + 1 / 2)) ℓ]
    simp only [Nat.cast_zero, Real.zero_rpow (ne_of_gt hq0), div_zero, add_zero, Nat.cast_add,
      Nat.cast_one]
  have hzeta : ∑ j ∈ Finset.range ℓ, 1 / ((j : ℝ) + 1) ^ (p + 1 / 2)
      ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2) := by
    rw [hshift]
    refine hsummable.sum_le_tsum _ fun n _ => ?_
    positivity
  have hsum : ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ M * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by
    calc ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
        ≤ ∑ j ∈ Finset.range ℓ, M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2))
            * ‖(e.symm : V →L[ℝ] V)‖ := Finset.sum_le_sum fun j _ => hstep j
      _ = M * ‖(e.symm : V →L[ℝ] V)‖
            * ∑ j ∈ Finset.range ℓ, 1 / ((j : ℝ) + 1) ^ (p + 1 / 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ M * ‖(e.symm : V →L[ℝ] V)‖ * ∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2) :=
          mul_le_mul_of_nonneg_left hzeta (by positivity)
      _ = M * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by ring
  rw [tau]
  calc (ℓ : ℝ)⁻¹ * ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ (ℓ : ℝ)⁻¹ * (M * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2))
          * ‖(e.symm : V →L[ℝ] V)‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M / ℓ * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by ring

end Superlinear

end AtkinsonHan.Chapter05
