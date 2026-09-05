import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.Superlinear
import Numlib.Krylov.Subspace
import Numlib.LinearSolve.Projection.Optimality

/-!
# Atkinson–Han §5.6: the conjugate gradient method for operator equations

Surface formalization of §5.6 of Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009.

Throughout, `V` is a real Hilbert space and `A : V →L[ℝ] V` is bounded, self-adjoint and positive
definite in the sense of (5.6.3), `√m ‖v‖ ≤ ‖v‖_A ≤ √M ‖v‖` with `m, M > 0`.  Contents:

* the `A`-inner product and `A`-norm of §5.6 (`innerA`, `normA`), identified with the backbone's
  `energyInner` and `energyNorm` (`Numlib/Analysis/InnerProductSpace/Energy.lean`);
* the identification of (5.6.3) with `LinearMap.IsSymmetricBoundedBy`
  (`Numlib/Analysis/InnerProductSpace/Coercive.lean`), and unique solvability of `A u = f`
  with `‖A⁻¹‖ ≤ 1/m`;
* the conjugate gradient iteration (5.6.2) as the book writes it (`cgStep`, `cg`), identified
  with the backbone's `CG.iterate` (`Numlib/Krylov/CG.lean`);
* Theorem 5.6.1 with the linear rate (5.6.4), the Chebyshev bound (5.6.5), the comparison
  (5.6.6) of the two rates, and the closing remark that `u_k` minimizes the `A`-norm of the error
  over `u₀ + 𝒦_k`.

`cg_energyNorm_error_step_le` is the one statement here that is not a book statement: it is the
per-step Kantorovich contraction in the backbone's own vocabulary, shared with §9.4, and belongs
in `Numlib/Krylov/Convergence/CG.lean`.

Theorem 5.6.2, Winther's superlinear convergence, is `theorem_5_6_2`, a specialization of the
backbone's `Krylov.winther`; the setting (5.6.7)–(5.6.9) is `isSymmetricBoundedBy_of_one_sub` and
the linear rate (5.6.10) for `A = I - K` is `equation_5_6_10`.  The eigen-decomposition of `K` is
taken as *data* rather than produced from compactness: what Mathlib lacks is not the spectral
theorem for compact self-adjoint operators, which it has, but the decreasing enumeration of the
eigenvalues of a compact operator as an `ℕ`-sequence.

Deferred (`plans/atkinsonhan-ch5.md` §3 item 3 and §4): Theorem 5.6.3, the rates for
Hilbert–Schmidt and `Cᵖ` kernels, which needs that same enumeration together with kernel
regularity.
-/

open Filter Topology

namespace AtkinsonHan.Ch05

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

theorem cg_zero (A : V →L[ℝ] V) (f u₀ : V) :
    cg A f u₀ 0 = ⟨u₀, f - A u₀, f - A u₀⟩ := rfl

theorem cg_succ (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    cg A f u₀ (k + 1) = cgStep A f (cg A f u₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The book's state read off from the backbone's CG state. -/
def ofCGState (s : CG.State V) : CGState V := ⟨s.x, s.r, s.p⟩

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

theorem cg_u (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).u = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).x := by
  rw [cg_eq_CG_iterate]
  rfl

theorem cg_r (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).r = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).r := by
  rw [cg_eq_CG_iterate]
  rfl

theorem cg_s (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).s = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).p := by
  rw [cg_eq_CG_iterate]
  rfl

end Iteration

section KantorovichStep

/-- One conjugate gradient step is at least as good as one steepest-descent step, so the energy
norm of the error contracts by the Kantorovich factor `(lmax - lmin) / (lmax + lmin)`.

Stated in the backbone's vocabulary because both §5.6 (`equation_5_6_4`) and §9.4
(`AtkinsonHan.Ch09.cg_energy_rate`) specialize it.  It is a two-line assembly of
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

/-- **Theorem 5.6.1** (Patterson): the conjugate gradient iterates converge to the solution of
`A u = f`, at the linear rate (5.6.4). -/
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
`‖u* - u_k‖_A ≤ 2 ((√M - √m)/(√M + √m))ᵏ ‖u* - u₀‖_A`.  This is the backbone's
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

end Superlinear

end AtkinsonHan.Ch05
