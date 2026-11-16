/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import Numlib.Krylov.Arnoldi
import Numlib.Projection.Optimality

/-!
# Specifications of Krylov iterates

Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and consider the system $Ax = b$ with a starting point $x_0$, the initial residual
$r_0 = b - A x_0$ and the Krylov spaces $\mathcal{K}_m = \mathcal{K}_m(A, r_0) =
\operatorname{span}\{r_0, A r_0, \dots, A^{m-1} r_0\}$. This file defines the iterates of Krylov
subspace methods by the property that they have, not by an algorithm. The minimal-residual iterate
minimizes $\|b - Ax\|$ over $x_0 + \mathcal{K}_m$, the Galerkin iterate has
$b - Ax \perp \mathcal{K}_m$, and the minimal-error iterate minimizes $\|x^* - x\|$ over
$x_0 + A \mathcal{K}_m(A, A(x^* - x_0))$.

The file proves the polynomial characterizations of these iterates ([saad2003iterative], Lemmas 6.28
and 6.31), existence and uniqueness results, and their behaviour at the grade of $r_0$, where the
Krylov spaces stop growing ([saad2003iterative], Proposition 6.10). It also defines the minimum-norm
minimal-residual iterate of MINRES-QLP, which is unique for every operator.

## Main definitions

* `Krylov.IsMinResidualIterate`: $x \in x_0 + \mathcal{K}_m$ minimizes the residual norm (GMRES,
  MINRES, CR, GCR, the full versions of ORTHOMIN and ORTHODIR, and MINRES-QLP on nonsingular
  systems).
* `Krylov.IsGalerkinIterate`: $x \in x_0 + \mathcal{K}_m$ and $b - Ax \perp \mathcal{K}_m$ (FOM, CG,
  D-Lanczos, the Lanczos method).
* `Krylov.IsMinErrorIterate`: $x$ minimizes $\|x^* - x\|$ over
  $x_0 + A \mathcal{K}_m(A, A(x^* - x_0))$ (SYMMLQ; CGNE and Craig's method on $A A^T$).
* `Krylov.IsMinNormMinResidualIterate`: the minimal-residual iterate of least norm (MINRES-QLP),
  which is unique on a singular system too.

## Main results

* `Krylov.exists_residual_poly`, `Krylov.exists_mem_of_residual_poly`: the points of
  $x_0 + \mathcal{K}_m$ are the points with residual $p(A) r_0$, where $\deg p \le m$ and
  $p(0) = 1$.
* `Krylov.IsMinResidualIterate.norm_residual_eq_iInf`: $\|r_m\| = \min \{\|p(A) r_0\| : \deg p \le
  m, \ p(0) = 1\}$ ([saad2003iterative], Lemma 6.31).
* `Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf`: for symmetric coercive $A$, $\|x^* -
  x_m\|_A = \min \{\|p(A)(x^* - x_0)\|_A : \deg p \le m, \ p(0) = 1\}$ ([saad2003iterative], Lemma
  6.28).
* `Krylov.IsGalerkinIterate.residual_mem_span`: the Galerkin residual is a multiple of the Arnoldi
  vector $v_m$ ([saad2003iterative], Proposition 6.7).
* `Krylov.IsMinResidualIterate.apply_eq_of_grade_le`,
  `Krylov.IsGalerkinIterate.apply_eq_of_grade_le`, `Krylov.grade_le_of_apply_eq`: the iterates are
  exact from the grade on, and an exact iterate at step $m$ forces the grade to be at most $m$
  ([saad2003iterative], Proposition 6.10).
* `Krylov.existsUnique_isMinNormMinResidualIterate`: the minimum-norm minimal-residual iterate
  exists and is unique, with no hypothesis on $A$.
* `Krylov.norm_le_of_apply_eq`: for symmetric $A$, an exact solution in $\mathcal{K}_m(A, b)$ is the
  minimum-norm solution (the core of [choi2006iterative], Theorem 2.25).

## Implementation notes

* A polynomial $p$ is a `Polynomial 𝕜`, $p(A) v$ is `Polynomial.aeval A p v`, and the condition
  $\deg p \le m$ is `p.degree ≤ m` in `WithBot ℕ`.
* The grade of $r_0$ is `Krylov.grade`, the dimension of the full Krylov space
  $\operatorname{span}\{A^i r_0 : i \in \mathbb{N}\}$. Results about the grade assume that this
  space is finite-dimensional.
* The minimal-error specification takes the target $x^*$ as an argument, so that it has a meaning
  when $A$ is singular.
-/

open Polynomial Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- The **minimal-residual Krylov iterate** at step $m$: $x - x_0 \in \mathcal{K}_m(A, r_0)$ with
$r_0 = b - A x_0$, and $\|b - Ax\| \le \|b - Ay\|$ for every $y$ with
$y - x_0 \in \mathcal{K}_m(A, r_0)$. This is the specification of GMRES, MINRES and CR. -/
abbrev IsMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinResidual A b x₀ (subspace A (b - A x₀) m) x

/-- The **Galerkin Krylov iterate** at step $m$: $x - x_0 \in \mathcal{K}_m(A, r_0)$ with
$r_0 = b - A x_0$, and $b - Ax$ is orthogonal to $\mathcal{K}_m(A, r_0)$. This is the
specification of FOM, CG and the Lanczos method. -/
abbrev IsGalerkinIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsGalerkin A b x₀ (subspace A (b - A x₀) m) x

/-- The **minimal-error Krylov iterate** at step $m$ for the target $x^*$:
$x - x_0 \in A \mathcal{K}_m(A, r_0)$ with $r_0 = A(x^* - x_0)$, and
$\|x^* - x\| \le \|x^* - y\|$ for every $y$ with $y - x_0 \in A \mathcal{K}_m(A, r_0)$. This is
the specification of SYMMLQ and CGNE.

When $A x^* = b$, the vector $r_0$ is the initial residual $b - A x_0$. The target $x^*$ is an
argument, so that the specification has a meaning for singular $A$. -/
abbrev IsMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinError xstar x₀ ((subspace A (A (xstar - x₀)) m).map A) x

section PolynomialGlue

/-- If $\deg g < m$ then $\deg (Xg) \le m$. -/
private theorem degree_X_mul_le {g : 𝕜[X]} {m : ℕ} (hg : g.degree < (m : WithBot ℕ)) :
    (X * g).degree ≤ (m : WithBot ℕ) := by
  rcases eq_or_ne g 0 with rfl | h0
  · simp
  rw [degree_eq_natDegree h0] at hg
  have hn : g.natDegree < m := by exact_mod_cast hg
  rw [degree_mul, degree_X, degree_eq_natDegree h0,
    show (1 : WithBot ℕ) + (g.natDegree : WithBot ℕ) = ((1 + g.natDegree : ℕ) : WithBot ℕ) by
      push_cast; ring]
  exact_mod_cast (by omega : 1 + g.natDegree ≤ m)

/-- If $\deg (Xg) \le m$ then $\deg g < m$. -/
private theorem degree_lt_of_degree_X_mul_le {g : 𝕜[X]} {m : ℕ}
    (h : (X * g).degree ≤ (m : WithBot ℕ)) : g.degree < (m : WithBot ℕ) := by
  rcases eq_or_ne g 0 with rfl | h0
  · simp
  rw [degree_mul, degree_X, degree_eq_natDegree h0,
    show (1 : WithBot ℕ) + (g.natDegree : WithBot ℕ) = ((1 + g.natDegree : ℕ) : WithBot ℕ) by
      push_cast; ring] at h
  have hn : 1 + g.natDegree ≤ m := by exact_mod_cast h
  rw [degree_eq_natDegree h0]
  exact_mod_cast (by omega : g.natDegree < m)

/-- For every polynomial $g$, $(1 - Xg)(A) v = v - A \, g(A) v$. -/
private theorem aeval_one_sub_X_mul (A : E →ₗ[𝕜] E) (g : 𝕜[X]) (v : E) :
    aeval A (1 - X * g) v = v - A (aeval A g v) := by
  simp [Module.End.mul_apply]

/-- The constant polynomial $1$ has degree at most $m$ for every $m$. The name differs from
Mathlib's `Polynomial.degree_one_le`, which is the case $m = 0$. -/
private theorem degree_one_le_natCast (m : ℕ) : (1 : 𝕜[X]).degree ≤ (m : WithBot ℕ) :=
  Polynomial.degree_one_le.trans (by exact_mod_cast Nat.zero_le m)

end PolynomialGlue

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ} {x : E}

/-- Let $r_0 = b - A x_0$. If $x - x_0 \in \mathcal{K}_m(A, r_0)$, then there is a polynomial $p$
with $\deg p \le m$ and $p(0) = 1$ such that
$$b - Ax = p(A) r_0.$$
The polynomial $p$ is a **residual polynomial** of $x$. -/
theorem exists_residual_poly (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    ∃ p : 𝕜[X], p.degree ≤ m ∧ p.eval 0 = 1 ∧ b - A x = aeval A p (b - A x₀) := by
  obtain ⟨g, hg, hgx⟩ := (mem_subspace_iff_exists_aeval A (b - A x₀)).1 hx
  refine ⟨1 - X * g, ?_, by simp, ?_⟩
  · exact le_trans (degree_sub_le _ _) (max_le (degree_one_le_natCast m) (degree_X_mul_le hg))
  · rw [aeval_one_sub_X_mul, hgx, residual_eq_sub_apply_sub A b x₀ x]

/-- Let $r_0 = b - A x_0$. For every polynomial $p$ with $\deg p \le m$ and $p(0) = 1$ there is an
$x$ with $x - x_0 \in \mathcal{K}_m(A, r_0)$ and $b - Ax = p(A) r_0$. This is the converse of
`Krylov.exists_residual_poly`. -/
theorem exists_mem_of_residual_poly (p : 𝕜[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    ∃ x, x - x₀ ∈ subspace A (b - A x₀) m ∧ b - A x = aeval A p (b - A x₀) := by
  obtain ⟨g, hg⟩ : X ∣ (1 - p) := by
    rw [X_dvd_iff, coeff_sub, coeff_one_zero, coeff_zero_eq_eval_zero, hp0, sub_self]
  have hpg : p = 1 - X * g := by rw [← hg]; ring
  have hgdeg : g.degree < (m : WithBot ℕ) := by
    refine degree_lt_of_degree_X_mul_le (m := m) ?_
    rw [← hg]
    exact le_trans (degree_sub_le _ _) (max_le (degree_one_le_natCast m) hp)
  refine ⟨x₀ + aeval A g (b - A x₀), ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact aeval_apply_mem_subspace A (b - A x₀) hgdeg
  rw [hpg, aeval_one_sub_X_mul, residual_eq_sub_apply_sub A b x₀ (x₀ + aeval A g (b - A x₀)),
    add_sub_cancel_left]

/-- Let $A$ be injective, let $A x^* = b$ and $r_0 = b - A x_0$. If a polynomial $p$ satisfies
$b - Ay = p(A) r_0$, then $x^* - y = p(A)(x^* - x_0)$. Thus a residual polynomial is also an
error polynomial. -/
theorem error_eq_aeval_of_injective (hA : Function.Injective A) {xstar y : E} (hstar : A xstar = b)
    {p : 𝕜[X]} (hres : b - A y = aeval A p (b - A x₀)) :
    xstar - y = aeval A p (xstar - x₀) := by
  refine hA ?_
  have hr : b - A x₀ = A (xstar - x₀) := by rw [map_sub, hstar]
  have hl : b - A y = A (xstar - y) := by rw [map_sub, hstar]
  rw [← hl, hres, hr, Module.End.aeval_apply_apply]

/-- Let $r_0 = b - A x_0$. If $x - x_0 \in \mathcal{K}_m(A, r_0)$, then the residual $b - Ax$ lies
in $\mathcal{K}_{m+1}(A, r_0)$. -/
theorem residual_mem_subspace_succ (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    b - A x ∈ subspace A (b - A x₀) (m + 1) := by
  rw [residual_eq_sub_apply_sub A b x₀ x]
  refine Submodule.sub_mem _ ?_ (map_subspace_le A (b - A x₀) m (Submodule.mem_map_of_mem hx))
  exact self_mem_subspace A (b - A x₀) m.succ_pos

section MinResidual

/-- For every operator $A$, every $b, x_0 \in E$ and every $m$, a minimal-residual iterate at step
$m$ exists. -/
theorem exists_isMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) :
    ∃ x, IsMinResidualIterate A b x₀ m x :=
  exists_isMinResidual b x₀ _

/-- Let $A$ be injective. For every $b, x_0 \in E$ and every $m$, there is exactly one
minimal-residual iterate at step $m$.

Existence holds for every $A$ (`Krylov.exists_isMinResidualIterate`), because the minimal
residual is the component of $r_0$ orthogonal to $A \mathcal{K}_m$. Injectivity makes the
iterate unique, and not only its residual. -/
theorem existsUnique_isMinResidualIterate_of_injective (hA : Function.Injective A) (b x₀ : E)
    (m : ℕ) : ∃! x, IsMinResidualIterate A b x₀ m x :=
  existsUnique_isMinResidual_of_injOn b x₀ _ hA.injOn

namespace IsMinResidualIterate

/-- Let $x$ be a minimal-residual iterate at step $m$ and $r_0 = b - A x_0$. For every polynomial
$p$ with $\deg p \le m$ and $p(0) = 1$,
$$\|b - Ax\| \le \|p(A) r_0\|.$$

Every such $p$ is the residual polynomial of a point of $x_0 + \mathcal{K}_m$
(`Krylov.exists_mem_of_residual_poly`), and $x$ minimizes the residual over these points. This
is the half of `Krylov.IsMinResidualIterate.norm_residual_eq_iInf` that convergence proofs use:
a polynomial that is small on the spectrum gives a bound on the residual. -/
theorem norm_residual_le_norm_aeval (hx : IsMinResidualIterate A b x₀ m x) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) : ‖b - A x‖ ≤ ‖aeval A p (b - A x₀)‖ := by
  obtain ⟨y, hy, hres⟩ := exists_mem_of_residual_poly (A := A) (b := b) (x₀ := x₀) p hp hp0
  rw [← hres]
  exact hx.min y hy

/-- Let $x$ be a minimal-residual iterate at step $m$ and $r_0 = b - A x_0$. Then
$$\|b - Ax\| = \inf \{\|p(A) r_0\| : \deg p \le m, \ p(0) = 1\},$$
and the infimum is attained by the residual polynomial of $x$. This is Lemma 6.31 of
[saad2003iterative]. -/
theorem norm_residual_eq_iInf (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ = ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ‖aeval A p.1 (b - A x₀)‖ := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, degree_one_le_natCast m, by simp⟩⟩
  have hbdd : BddBelow (Set.range
      fun p : {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} =>
        ‖aeval A p.1 (b - A x₀)‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact norm_nonneg _
  refine le_antisymm (le_ciInf fun p => hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2) ?_
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx.mem
  rw [hres]
  exact ciInf_le hbdd ⟨p, hp, hp0⟩

/-- If $x_k$ is a minimal-residual iterate at step $k$ for every $k$, then the residual norms
$\|b - A x_k\|$ are nonincreasing in $k$. -/
theorem norm_residual_antitone {x : ℕ → E} (hx : ∀ k, IsMinResidualIterate A b x₀ k (x k)) :
    Antitone fun k => ‖b - A (x k)‖ :=
  fun k l hkl => (hx k).norm_residual_le (hx l) (subspace_mono A (b - A x₀) hkl)

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $\ell$ be its grade. Let
$x$ be a minimal-residual iterate at step $m \ge \ell$. If $A$ is injective on
$\mathcal{K}_\ell(A, r_0)$, then $Ax = b$. This is the **lucky breakdown** of
[saad2003iterative], Proposition 6.10. -/
theorem apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsMinResidualIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m)
    (hinj : Set.InjOn A (subspace A (b - A x₀) (grade A (b - A x₀)))) : A x = b := by
  have hKg : subspace A (b - A x₀) m = subspace A (b - A x₀) (grade A (b - A x₀)) :=
    subspace_eq_of_grade_le A (b - A x₀) hm
  have hinvt : subspace A (b - A x₀) m ∈ Module.End.invtSubmodule A := by
    rw [hKg]; exact subspace_grade_mem_invtSubmodule A (b - A x₀)
  have hres : ∀ z ∈ subspace A (b - A x₀) m, A z ∈ subspace A (b - A x₀) m :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hinvt
  have hinj' : Set.InjOn A (subspace A (b - A x₀) m : Set E) := by rw [hKg]; exact hinj
  set f : subspace A (b - A x₀) m →ₗ[𝕜] subspace A (b - A x₀) m := A.restrict hres with hf
  have hval : ∀ z : subspace A (b - A x₀) m, ((f z : subspace A (b - A x₀) m) : E) = A (z : E) :=
    fun z => rfl
  have hfinj : Function.Injective f := by
    intro z w hzw
    exact Subtype.ext (hinj' z.2 w.2 (by rw [← hval z, ← hval w, hzw]))
  have hr₀ : b - A x₀ ∈ subspace A (b - A x₀) m := by
    rw [hKg, subspace_grade_eq_fullSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hfinj) ⟨b - A x₀, hr₀⟩
  refine hx.apply_eq_of_exists (y := x₀ + (z : E)) (by simp) ?_
  have hAz : A (z : E) = b - A x₀ := by rw [← hval z, hz]
  rw [map_add, hAz]
  abel

/-- The residual of a minimal-residual iterate is orthogonal to $A \mathcal{K}_m(A, r_0)$. Thus the
iterate is a Petrov–Galerkin iterate with the constraint space $A \mathcal{K}_m$. -/
theorem residual_mem_orthogonal (hx : IsMinResidualIterate A b x₀ m x) :
    b - A x ∈ ((subspace A (b - A x₀) m).map A)ᗮ :=
  hx.isPetrovGalerkin.orth

end IsMinResidualIterate

/-- Let $v$ have a finite-dimensional Krylov space. If a nonzero polynomial $s$ with $\deg s \le m$
satisfies $s(A) v = 0$, then the grade of $v$ is at most $m$. -/
theorem grade_le_of_aeval_eq_zero {v : E} [FiniteDimensional 𝕜 (fullSubspace A v)]
    {s : 𝕜[X]} (hs : s ≠ 0) (hdeg : s.natDegree ≤ m) (h0 : aeval A s v = 0) :
    grade A v ≤ m := by
  have hc : s.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hs
  have hCne : (C s.leadingCoeff⁻¹ : 𝕜[X]) ≠ 0 := by simpa using inv_ne_zero hc
  have hXs : (X ^ (m - s.natDegree) * s : 𝕜[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hs
  refine (grade_le_iff A v).2 ((pow_apply_mem_subspace_iff_exists_monic A v m).2
    ⟨C s.leadingCoeff⁻¹ * (X ^ (m - s.natDegree) * s), ?_, ?_, ?_⟩)
  · have hlc : (C s.leadingCoeff⁻¹ * (X ^ (m - s.natDegree) * s)).leadingCoeff = 1 := by
      rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_X,
        one_pow, one_mul, inv_mul_cancel₀ hc]
    exact hlc
  · rw [natDegree_mul hCne hXs, natDegree_C, zero_add,
      natDegree_mul (pow_ne_zero _ X_ne_zero) hs, natDegree_pow, natDegree_X, mul_one]
    omega
  · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h0, map_zero, map_zero]

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space. If
$x - x_0 \in \mathcal{K}_m(A, r_0)$ and $Ax = b$, then the grade of $r_0$ is at most $m$. This
is the converse direction of Proposition 6.10 of [saad2003iterative] (see also P-6.13 there).

No injectivity of $A$ is needed. If $x - x_0 = q(A) r_0$, then $r_0 = A q(A) r_0$, so $1 - Xq$
annihilates $r_0$. -/
theorem grade_le_of_apply_eq [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : x - x₀ ∈ subspace A (b - A x₀) m) (hAx : A x = b) : grade A (b - A x₀) ≤ m := by
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx
  refine grade_le_of_aeval_eq_zero (fun h => ?_) (natDegree_le_iff_degree_le.2 hp) ?_
  · rw [h] at hp0; simp at hp0
  · rw [← hres, hAx, sub_self]

/-! ### The minimum-norm minimal-residual iterate -/

/-- The **minimum-norm minimal-residual iterate** at step $m$, the specification of MINRES-QLP: $x$
is a minimal-residual iterate at step $m$, and $\|x\| \le \|y\|$ for every minimal-residual
iterate $y$ at step $m$.

On a singular system the minimal-residual iterates form an affine subspace
(`Krylov.isMinResidualIterate_iff_sub_mem`), so the minimal-residual specification does not
determine the iterate. The additional condition of least norm determines it, with no hypothesis
on $A$ (`Krylov.existsUnique_isMinNormMinResidualIterate`). When $A$ is injective, this
specification is equivalent to `Krylov.IsMinResidualIterate`, which then has a unique solution. -/
structure IsMinNormMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop where
  /-- The point $x$ minimizes the residual over $x_0 + \mathcal{K}_m$. -/
  isMinResidualIterate : IsMinResidualIterate A b x₀ m x
  /-- The point $x$ has the least norm among the minimizers. -/
  norm_le : ∀ y, IsMinResidualIterate A b x₀ m y → ‖x‖ ≤ ‖y‖

/-- Let $x_1$ be a minimal-residual iterate at step $m$. Then $x$ is a minimal-residual iterate at
step $m$ if and only if
$$x - x_1 \in \mathcal{K}_m(A, r_0) \cap \ker A.$$

All minimal-residual iterates have the same residual (`IsMinResidual.residual_unique`), so
they differ by elements of $\mathcal{K}_m$ that $A$ maps to $0$. -/
theorem isMinResidualIterate_iff_sub_mem {x₁ : E} (hx₁ : IsMinResidualIterate A b x₀ m x₁) :
    IsMinResidualIterate A b x₀ m x ↔
      x - x₁ ∈ subspace A (b - A x₀) m ⊓ LinearMap.ker A := by
  constructor
  · intro hx
    have hA : A (x - x₁) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact sub_right_injective (hx.residual_unique hx₁)
    exact ⟨by simpa using Submodule.sub_mem _ hx.mem hx₁.mem, hA⟩
  · rintro ⟨hmem, hker⟩
    have hA : A x = A x₁ := by
      rw [← sub_eq_zero, ← map_sub]
      exact hker
    refine ⟨by simpa using Submodule.add_mem _ hmem hx₁.mem, fun y hy => ?_⟩
    rw [hA]
    exact hx₁.min y hy

/-- If $x_1$ is a minimal-residual iterate, then $x$ is the minimum-norm minimal-residual iterate if
and only if $x$ is the best approximation of $0$ from $x_1 + (\mathcal{K}_m \cap \ker A)$. -/
private theorem isMinNormMinResidualIterate_iff_isMinError {x₁ : E}
    (hx₁ : IsMinResidualIterate A b x₀ m x₁) :
    IsMinNormMinResidualIterate A b x₀ m x ↔
      IsMinError 0 x₁ (subspace A (b - A x₀) m ⊓ LinearMap.ker A) x := by
  have hnorm : ∀ y : E, ‖(0 : E) - y‖ = ‖y‖ := fun y => by rw [zero_sub, norm_neg]
  constructor
  · rintro ⟨hx, hmin⟩
    exact ⟨(isMinResidualIterate_iff_sub_mem hx₁).1 hx, fun y hy => by
      rw [hnorm, hnorm]
      exact hmin y ((isMinResidualIterate_iff_sub_mem hx₁).2 hy)⟩
  · rintro ⟨hmem, hmin⟩
    refine ⟨(isMinResidualIterate_iff_sub_mem hx₁).2 hmem, fun y hy => ?_⟩
    have := hmin y ((isMinResidualIterate_iff_sub_mem hx₁).1 hy)
    rwa [hnorm, hnorm] at this

/-- For every operator $A$, every $b, x_0 \in E$ and every $m$, there is exactly one minimum-norm
minimal-residual iterate at step $m$.

The minimal-residual iterates form a nonempty translate of the finite-dimensional subspace
$\mathcal{K}_m \cap \ker A$, and a nonempty affine subspace of an inner product space has a
unique element of least norm. This makes the MINRES-QLP iterate well defined on a singular
system, where `Krylov.existsUnique_isMinResidualIterate_of_injective` does not apply. -/
theorem existsUnique_isMinNormMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) :
    ∃! x, IsMinNormMinResidualIterate A b x₀ m x := by
  obtain ⟨x₁, hx₁⟩ := exists_isMinResidualIterate A b x₀ m
  obtain ⟨z, hz⟩ :=
    exists_isMinError x₁ (subspace A (b - A x₀) m ⊓ LinearMap.ker A) 0
  refine ⟨z, (isMinNormMinResidualIterate_iff_isMinError hx₁).2 hz, fun y hy => ?_⟩
  exact IsMinError.unique ((isMinNormMinResidualIterate_iff_isMinError hx₁).1 hy) hz

/-- Let $A$ be injective. Then $x$ is the minimum-norm minimal-residual iterate at step $m$ if and
only if $x$ is a minimal-residual iterate at step $m$, because the minimal-residual iterate is
already unique. -/
theorem isMinNormMinResidualIterate_iff_isMinResidualIterate (hA : Function.Injective A) :
    IsMinNormMinResidualIterate A b x₀ m x ↔ IsMinResidualIterate A b x₀ m x := by
  obtain ⟨x', -, huniq⟩ := existsUnique_isMinResidualIterate_of_injective hA b x₀ m
  exact ⟨fun h => h.isMinResidualIterate,
    fun h => ⟨h, fun y hy => le_of_eq (congrArg norm ((huniq x h).trans (huniq y hy).symm))⟩⟩

end MinResidual

section MinError

/-- For every operator $A$, every $x^*, x_0 \in E$ and every $m$, a minimal-error iterate at step
$m$ exists. It is $x_0$ plus the orthogonal projection of $x^* - x_0$ onto $A \mathcal{K}_m$. -/
theorem exists_isMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) :
    ∃ x, IsMinErrorIterate A xstar x₀ m x :=
  exists_isMinError x₀ _ xstar

/-- For every operator $A$, two minimal-error iterates at the same step $m$ for the same target
$x^*$ are equal.

The iterate is the nearest point of the affine space $x_0 + A \mathcal{K}_m$ to $x^*$, and
nearest points are unique by the parallelogram law, however degenerate $A$ is. Compare
`Krylov.existsUnique_isMinResidualIterate_of_injective`, where the uniqueness of the iterate
needs injectivity. -/
theorem IsMinErrorIterate.unique {xstar x' : E} (hx : IsMinErrorIterate A xstar x₀ m x)
    (hx' : IsMinErrorIterate A xstar x₀ m x') : x = x' :=
  IsMinError.unique hx hx'

/-- If $x_k$ is a minimal-error iterate at step $k$ for the target $x^*$, for every $k$, then the
errors $\|x^* - x_k\|$ are nonincreasing in $k$. -/
theorem IsMinErrorIterate.norm_error_antitone {xstar : E} {x : ℕ → E}
    (hx : ∀ k, IsMinErrorIterate A xstar x₀ k (x k)) : Antitone fun k => ‖xstar - x k‖ :=
  fun k l hkl => (hx k).norm_error_le_of_le (hx l)
    (Submodule.map_mono (subspace_mono A (A (xstar - x₀)) hkl))

end MinError

section Galerkin

/-- Let $A$ be coercive: $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$ for some $c > 0$
and all $x$. For every $b, x_0 \in E$ and every $m$, there is exactly one Galerkin iterate at
step $m$. Thus FOM and CG are well defined with no further hypothesis.

Coercivity excludes the only obstruction, a nonzero $z \in \mathcal{K}_m$ with
$Az \perp \mathcal{K}_m$, which would leave the Galerkin condition underdetermined. Without
coercivity the iterate can fail to exist. `Krylov.existsUnique_isGalerkinIterate_iff_isUnit`
relates existence and uniqueness to the invertibility of the square Hessenberg matrix $H_m$. -/
theorem existsUnique_isGalerkinIterate_of_isCoercive (hA : A.IsCoercive) (b x₀ : E) (m : ℕ) :
    ∃! x, IsGalerkinIterate A b x₀ m x :=
  existsUnique_isGalerkin_of_isCoercive b x₀ _ hA

namespace IsGalerkinIterate

/-- Let $A$ be symmetric coercive, let $A x^* = b$, and let $x$ be a Galerkin iterate at step $m$.
For every polynomial $p$ with $\deg p \le m$ and $p(0) = 1$,
$$\|x^* - x\|_A \le \|p(A)(x^* - x_0)\|_A.$$

This is the energy-norm counterpart of
`Krylov.IsMinResidualIterate.norm_residual_le_norm_aeval`, and the half of
`Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf` ([saad2003iterative], Lemma 6.28) that the
Chebyshev convergence bounds use. The residual polynomial of a competitor is also its error
polynomial, because $A$ commutes with $p(A)$. -/
theorem energyNorm_error_le_energyNorm_aeval (hA : A.IsSymmetricCoercive)
    (hx : IsGalerkinIterate A b x₀ m x) {xstar : E} (hstar : A xstar = b) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    energyNorm A (xstar - x) ≤ energyNorm A (aeval A p (xstar - x₀)) := by
  obtain ⟨y, hy, hres⟩ := exists_mem_of_residual_poly (A := A) (b := b) (x₀ := x₀) p hp hp0
  rw [← error_eq_aeval_of_injective hA.isCoercive.injective hstar hres]
  exact IsGalerkin.energyNorm_le hA hx hstar hy

/-- Let $A$ be symmetric coercive, let $A x^* = b$, and let $x$ be a Galerkin iterate at step $m$.
Then
$$\|x^* - x\|_A = \inf \{\|p(A)(x^* - x_0)\|_A : \deg p \le m, \ p(0) = 1\},$$
and the infimum is attained. This is Lemma 6.28 of [saad2003iterative].

Here $\|z\|_A = \sqrt{\operatorname{Re} \langle Az, z \rangle}$ is `energyNorm`. -/
theorem energyNorm_error_eq_iInf (hA : A.IsSymmetricCoercive) (hx : IsGalerkinIterate A b x₀ m x)
    {xstar : E} (hstar : A xstar = b) :
    energyNorm A (xstar - x) =
      ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1},
        energyNorm A (aeval A p.1 (xstar - x₀)) := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, degree_one_le_natCast m, by simp⟩⟩
  have hbdd : BddBelow (Set.range
      fun p : {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} =>
        energyNorm A (aeval A p.1 (xstar - x₀))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact energyNorm_nonneg _ _
  refine le_antisymm
    (le_ciInf fun p => energyNorm_error_le_energyNorm_aeval hA hx hstar p.1 p.2.1 p.2.2) ?_
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx.mem
  rw [error_eq_aeval_of_injective hA.isCoercive.injective hstar hres]
  exact ciInf_le hbdd ⟨p, hp, hp0⟩

/-- Let $x$ be a Galerkin iterate at step $m$ and $r_0 = b - A x_0$. Then the residual $b - Ax$ is a
scalar multiple of the Arnoldi vector $v_m$ of $(A, r_0)$. This is Proposition 6.7 of
[saad2003iterative].

The statement holds for every operator $A$. After a breakdown $v_m = 0$, and then the residual
is $0$. -/
theorem residual_mem_span (hx : IsGalerkinIterate A b x₀ m x) :
    b - A x ∈ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m := by
  have hIio : Set.Iio (m + 1) = Set.Iio m ∪ {m} := by
    ext k; simp
  have hsup : subspace A (b - A x₀) (m + 1)
      = subspace A (b - A x₀) m ⊔ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m := by
    rw [← Arnoldi.span_vec A (b - A x₀) (m + 1), ← Arnoldi.span_vec A (b - A x₀) m, hIio,
      Set.image_union, Submodule.span_union, Set.image_singleton]
  have hmem := residual_mem_subspace_succ hx.mem
  rw [hsup, Submodule.mem_sup] at hmem
  obtain ⟨u, hu, w, hw, huw⟩ := hmem
  have hu0 : u = 0 := by
    have h1 : inner 𝕜 u (b - A x) = (0 : 𝕜) := IsPetrovGalerkin.inner_residual_eq_zero hx hu
    rw [← huw, inner_add_right] at h1
    have h2 : inner 𝕜 u w = (0 : 𝕜) := by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [inner_smul_right, (Submodule.mem_orthogonal _ _).1
        (Arnoldi.vec_mem_orthogonal A (b - A x₀) m) u hu, mul_zero]
    rw [h2, add_zero] at h1
    exact inner_self_eq_zero.1 h1
  rw [← huw, hu0, zero_add]
  exact hw

/-- If $x$ and $x'$ are Galerkin iterates at different steps $m \neq m'$, then their residuals are
orthogonal: $\langle b - Ax, b - Ax' \rangle = 0$. -/
theorem inner_residual_eq_zero {m' : ℕ} {x' : E} (hx : IsGalerkinIterate A b x₀ m x)
    (hx' : IsGalerkinIterate A b x₀ m' x') (h : m ≠ m') :
    inner 𝕜 (b - A x) (b - A x') = 0 := by
  have key : ∀ (k l : ℕ) (y y' : E), IsGalerkinIterate A b x₀ k y → IsGalerkinIterate A b x₀ l y' →
      k < l → inner 𝕜 (b - A y) (b - A y') = (0 : 𝕜) := by
    intro k l y y' hy hy' hkl
    exact IsPetrovGalerkin.inner_residual_eq_zero hy'
      (subspace_mono A (b - A x₀) hkl (residual_mem_subspace_succ hy.mem))
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact key m m' x x' hx hx' hlt
  · rw [← inner_conj_symm, key m' m x' x hx' hx hlt, map_zero]

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $x$ be a Galerkin iterate
at a step $m$ that is at least the grade of $r_0$. Then $Ax = b$. This combines Propositions 5.6
and 6.10 of [saad2003iterative].

No hypothesis on $A$ is needed: from the grade on, the residual lies in $\mathcal{K}_m$ and is
orthogonal to it. -/
theorem apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsGalerkinIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m) : A x = b := by
  refine hx.eq_of_invt ?_ ?_ ?_
  · rw [subspace_eq_of_grade_le A (b - A x₀) hm]
    exact subspace_grade_mem_invtSubmodule A (b - A x₀)
  · rw [subspace_eq_of_grade_le A (b - A x₀) hm, subspace_grade_eq_fullSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  · intro z hz hzo
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hzo z hz)

/-- Let $A$ be symmetric coercive and let $A x^* = b$. If $x_k$ is a Galerkin iterate at step $k$
for every $k$, then the energy-norm errors $\|x^* - x_k\|_A$ are nonincreasing in $k$. -/
theorem energyNorm_error_antitone (hA : A.IsSymmetricCoercive) {x : ℕ → E}
    (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k) :=
  fun k l hkl => IsGalerkin.energyNorm_le_of_le hA (hx k) (hx l)
    (subspace_mono A (b - A x₀) hkl) hstar

end IsGalerkinIterate

/-- Let $A$ be injective, let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $m$
be at least the grade of $r_0$. Then there is exactly one Galerkin iterate at step $m$, and it
solves $Ax = b$.

No coercivity is needed. The space $\mathcal{K}_m$ equals the space at the grade, which is
invariant under $A$ and contains $r_0$. The injective map $A$ maps this finite-dimensional space
onto itself, so exactly one point of $x_0 + \mathcal{K}_m$ has zero residual. Every Galerkin
iterate is exact there (`Krylov.IsGalerkinIterate.apply_eq_of_grade_le`), so it equals this
point. Compare `Krylov.existsUnique_isGalerkinIterate_of_isCoercive`, which needs coercivity but
no condition on $m$.

[quarteroni2000numerical] use this step without proof in the proof of Theorem 4.13, where they
"invert the first relation in (4.56)" at a breakdown $m < n$: the Hessenberg matrix $H_m$ is
nonsingular there because $A$ is. The matrix side is
`Krylov.existsUnique_isGalerkinIterate_iff_isUnit` in `Numlib.Krylov.Hessenberg`. -/
theorem existsUnique_isGalerkinIterate_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : Function.Injective A) (hm : grade A (b - A x₀) ≤ m) :
    ∃! x, IsGalerkinIterate A b x₀ m x := by
  have hKg : subspace A (b - A x₀) m = subspace A (b - A x₀) (grade A (b - A x₀)) :=
    subspace_eq_of_grade_le A (b - A x₀) hm
  have hinvt : subspace A (b - A x₀) m ∈ Module.End.invtSubmodule A := by
    rw [hKg]; exact subspace_grade_mem_invtSubmodule A (b - A x₀)
  have hres : ∀ z ∈ subspace A (b - A x₀) m, A z ∈ subspace A (b - A x₀) m :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hinvt
  set f : subspace A (b - A x₀) m →ₗ[𝕜] subspace A (b - A x₀) m := A.restrict hres with hf
  have hval : ∀ z : subspace A (b - A x₀) m, ((f z : subspace A (b - A x₀) m) : E) = A (z : E) :=
    fun z => rfl
  have hfinj : Function.Injective f := by
    intro z w hzw
    exact Subtype.ext (hA (by rw [← hval z, ← hval w, hzw]))
  have hr₀ : b - A x₀ ∈ subspace A (b - A x₀) m := by
    rw [hKg, subspace_grade_eq_fullSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hfinj) ⟨b - A x₀, hr₀⟩
  have hAz : A (z : E) = b - A x₀ := by rw [← hval z, hz]
  refine ⟨x₀ + (z : E), ⟨by simp, ?_⟩, fun y hy => ?_⟩
  · rw [map_add, hAz, show b - (A x₀ + (b - A x₀)) = 0 by abel]
    exact Submodule.zero_mem _
  · exact hA (by rw [hy.apply_eq_of_grade_le hm, map_add, hAz]; abel)

end Galerkin

/-- Let $A$ be symmetric and let $b$ lie in the range of $A$. Then every Krylov space of $b$ is
orthogonal to the kernel of $A$: $\mathcal{K}_m(A, b) \subseteq (\ker A)^\perp$.

This is why a Krylov method on a consistent singular system started at $0$ reaches the
minimum-norm solution. -/
theorem subspace_le_orthogonal_ker (hA : A.IsSymmetric) {b : E} (hb : b ∈ LinearMap.range A)
    (m : ℕ) : subspace A b m ≤ (LinearMap.ker A)ᗮ := by
  obtain ⟨c, rfl⟩ := hb
  rw [subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_orthogonal _ _).2 fun z hz => ?_
  dsimp only
  have hpow : (A ^ (i : ℕ)) (A c) = (A ^ ((i : ℕ) + 1)) c := by
    rw [pow_succ]
    rfl
  have hz0 : (A ^ ((i : ℕ) + 1)) z = 0 := by
    rw [pow_succ, Module.End.mul_apply, LinearMap.mem_ker.1 hz, map_zero]
  rw [hpow, ← hA.pow ((i : ℕ) + 1) z c, hz0, inner_zero_left]

/-- Let $A$ be symmetric. If $x \in \mathcal{K}_m(A, b)$ and $Ax = b$, then $\|x\| \le \|y\|$ for
every $y$ with $Ay = b$. Thus an exact Krylov solution of a consistent system, started at $0$,
is the minimum-norm solution. This is the core of Theorems 2.25 and 3.1 of [choi2006iterative].

The proof uses $\mathcal{K}_m(A, b) \subseteq (\ker A)^\perp$
(`Krylov.subspace_le_orthogonal_ker`). -/
theorem norm_le_of_apply_eq (hA : A.IsSymmetric) {b x : E} {m : ℕ} (hx : x ∈ subspace A b m)
    (hAx : A x = b) (y : E) (hy : A y = b) : ‖x‖ ≤ ‖y‖ := by
  have hker : y - x ∈ LinearMap.ker A := by
    simp [LinearMap.mem_ker, map_sub, hAx, hy]
  have h0 : inner 𝕜 x (y - x) = (0 : 𝕜) :=
    (Submodule.mem_orthogonal' _ _).1 (subspace_le_orthogonal_ker hA ⟨x, hAx⟩ m hx) _ hker
  have hsum : ‖x + (y - x)‖ * ‖x + (y - x)‖ = ‖x‖ * ‖x‖ + ‖y - x‖ * ‖y - x‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [show x + (y - x) = y from by abel] at hsum
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (y - x)]

end Krylov
