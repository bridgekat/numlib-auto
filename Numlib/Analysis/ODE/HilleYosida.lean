/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.InnerProductSpace.MaximalMonotone
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# The Hille–Yosida theorem on a real Hilbert space

Let $H$ be a real Hilbert space and $A : D(A) \subseteq H \to H$ a maximal monotone operator. This
file studies the evolution problem
$$u' + Au = 0 \quad \text{on } [0, \infty), \qquad u(0) = u_0,$$
following Chapter 7, §7.2–§7.4 of [brezis2011functional]. It constructs the contraction semigroup
$S_A(t)$, and proves existence and uniqueness of a solution $u \in C^1([0, \infty); H)$ for
$u_0 \in D(A)$, with $\|u(t)\| \le \|u_0\|$ and $\|u'(t)\| \le \|Au_0\|$ (the **Hille–Yosida
theorem**, Theorem 7.4). For $u_0 \in D(A^k)$ the solution is in $C^{k-j}([0, \infty); D(A^j))$ for
$j \le k$ (Theorem 7.5). If $A$ is moreover self-adjoint, every $u_0 \in H$ gives a solution that is
continuous on $[0, \infty)$, satisfies $\|Au(t)\| \le \|u_0\| / t$, and is in
$C^k((0, \infty); D(A^l))$ for all $k, l$ (Theorem 7.7).

With the Yosida approximation $A_\lambda$ of `LinearPMap.yosida`, the approximate problem
$u_\lambda' + A_\lambda u_\lambda = 0$ has the solution $u_\lambda(t) = e^{-tA_\lambda} u_0$, and
the semigroup is the limit $S_A(t) u_0 = \lim_{\lambda \to 0^+} e^{-tA_\lambda} u_0$. The shift of
Remark 6 of Chapter 7 says that $u$ solves $u' + Au + cu = 0$ if and only if $e^{ct} u$ solves
$u' + Au = 0$. It extends to the regularity classes: $C^n(s; D((A + cI)^j))$ is $C^n(s; D(A^j))$, so
Theorem 7.5 for a maximal monotone $A + cI$ can be read on $A$. The wave operator of §10.3 of
[brezis2011functional], for which $A + I$ is maximal monotone, needs exactly this.

## Main definitions

* `LinearPMap.IsSolutionOn`: $u$ solves $u' + Au = 0$ on a set of times $s$, with $u(0) = u_0$.
* `LinearPMap.expYosida`: the solution operator $e^{-tA_\lambda}$ of the approximate problem.
* `LinearPMap.semigroup`: the contraction semigroup $S_A(t) = \lim_{\lambda \to 0^+}
  e^{-tA_\lambda}$.
* `LinearPMap.ContDiffOnPowDomain`: the class $C^n(s; D(A^j))$.
* `LinearPMap.semigroupLift`: the element of $D(A^\ell)$ over $S_A(t) u_0$.

## Main results

* `LinearPMap.IsMonotone.eqOn_of_isSolutionOn`: uniqueness of the solution for a monotone $A$.
* `LinearPMap.IsMaximalMonotone.exists_isSolutionOn`: Theorem 7.4 (Hille–Yosida), existence for
  $u_0 \in D(A)$ with the two estimates.
* `LinearPMap.IsMaximalMonotone.semigroup_add`: the semigroup law $S_A(s + t) = S_A(s) S_A(t)$.
* `LinearPMap.IsMaximalMonotone.contDiffOnPowDomain_semigroup`: Theorem 7.5,
  $u \in C^{k-j}([0, \infty); D(A^j))$ for $u_0 \in D(A^k)$.
* `LinearPMap.exists_isSolutionOn_Ioi_of_isSelfAdjoint`: Theorem 7.7, the self-adjoint case.
* `LinearPMap.IsMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup`: Theorem 7.5 for a shifted
  operator $A + cI$.
* `LinearPMap.norm_applyL_semigroupLift_le`: the bound $\|A^j S_A(t) u_0\| \le (j/t)^j \|u_0\|$ in
  the self-adjoint case.
* `LinearPMap.IsSolutionOn.energy_Ioi`: the energy identity $\frac12 \|u(T)\|^2 + \int_0^T \langle
  Au, u \rangle = \frac12 \|u_0\|^2$.

## Proof outline

The approximate problem is solved in closed form, $u_\lambda(t) = e^{-tA_\lambda} u_0$, with
Mathlib's `NormedSpace.exp`, not by the Cauchy–Lipschitz theorem. This shortens the six steps of the
book in two ways. First, the derivatives $u_\lambda' = -e^{-tA_\lambda} A_\lambda u_0$ converge as
soon as $e^{-tA_\lambda} w \to S_A(t) w$ for every $w$ and $A_\lambda u_0 \to A u_0$. So Step 4,
Step 6 and Lemma 7.2 of the book are not needed, and existence holds for every $u_0 \in D(A)$ at
once. Second, the limit $S_A(t) u_0 = \lim e^{-tA_\lambda} u_0$ exists for every $u_0 \in H$. So the
semigroup is defined first, and the solution of the evolution problem is $t \mapsto S_A(t) u_0$.

The steps of the book that remain are these. Step 1 is uniqueness by monotonicity. Step 2 is Lemma
7.1 for a bounded monotone operator. Step 3 is the Cauchy estimate $\|u_\lambda(t) - u_\mu(t)\|^2
\le \|w_0 - w_1\|^2 + 4(\lambda + \mu) t M^2$ and the limit, uniform on bounded intervals. Step 5 is
the derivative of the uniform limit on a closed interval, through the fundamental theorem of
calculus, and the closed graph of $A$. Theorems 7.5 and 7.7 are inductions over the level $j$: they
apply the theory to the part of $A$ in the Hilbert space $D(A^j)$. The smoothing estimate
$\|A S_A(t) u_0\| \le \|u_0\| / t$ of Theorem 7.7 comes from a Lyapunov function, which replaces the
integrations by parts of the book by one derivative.

## Implementation notes

* The file is over $\mathbb{R}$. Time derivatives of $u : \mathbb{R} \to H$ need `NormedSpace ℝ H`,
  and the energy identity $\frac{d}{dt} \|u\|^2 = 2 \langle u', u \rangle$ used in every step
  (`HasDerivAt.norm_sq`) is stated for real inner product spaces. Each graph space $D(A^k)$ would
  need the real structure too. The proofs use only the real part of the inner product, so a complex
  version is a restatement, not a new proof.
* The operator $A$ is a partial linear map `H →ₗ.[ℝ] H`. The notions `LinearPMap.IsMonotone`,
  `LinearPMap.IsMaximalMonotone`, `LinearPMap.resolvent`, `LinearPMap.yosida`,
  `LinearPMap.PowDomain` and `LinearPMap.powPart` come from
  `Numlib.Analysis.InnerProductSpace.MaximalMonotone`.
* The parameter $\lambda > 0$ of the Yosida approximation is `c` in the Lean code. The declarations
  write $A_c$ for `A.yosida c`, $J_c$ for `A.resolvent c`, and $u_c(t) = e^{-tA_c} u_0$ for
  `A.expYosida c t u₀`.
* `LinearPMap.IsSolutionOn A u₀ s u` says that $u(0) = u_0$, $u(t) \in D(A)$ for $t \in s$, and the
  derivative of $u$ within $s$ at $t \in s$ is $-Au(t)$. It is one-sided at $t = 0$ when
  $s = [0, \infty)$. The class $C^1([0, \infty); H)$ of the book is `ContDiffOn ℝ 1 u (Ici 0)`, a
  separate conjunct in the theorems.
* The space $D(A^j)$ is `A.PowDomain j`, the tuples $x = (x_0, x_1, \dots, x_j)$ with
  $x_{i+1} = A x_i$, with the graph norm. The coordinate $x_i = A^i x_0$ is
  `LinearPMap.PowDomain.applyL A j i x`.
* The semigroup is a total function of $(A, t)$ with a junk value, like `LinearPMap.resolvent`.
  Every statement about `LinearPMap.semigroup` is made for an arbitrary real Hilbert space, so that
  it applies to the part of $A$ in $D(A^j)$.
* The self-adjoint results of Theorem 7.7 assume that $A$ is symmetric, `A.IsFormalAdjoint A`, and
  only the final theorem `LinearPMap.exists_isSolutionOn_Ioi_of_isSelfAdjoint` uses the hypothesis
  `IsSelfAdjoint A` of the book.
-/

open Filter Topology Set Metric WithLp
open scoped InnerProductSpace

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Solutions of the evolution equation -/

variable (A : H →ₗ.[ℝ] H) in
/-- A curve $u : \mathbb{R} \to H$ **solves the evolution problem** $u' + Au = 0$ on the set of
times $s \subseteq \mathbb{R}$, with the initial value $u_0$, if $u(0) = u_0$, $u(t) \in D(A)$
for every $t \in s$, and the derivative of $u$ within $s$ at every $t \in s$ is $-Au(t)$. This
is problem (6) of §7.2 of [brezis2011functional].

For $s = [0, \infty)$ the derivative at $t = 0$ is one-sided. The condition $u(0) = u_0$ is
asked also when $0 \notin s$. The requirement $u \in C^1$ of the book is a separate conjunct in
the theorems. -/
structure IsSolutionOn (u₀ : H) (s : Set ℝ) (u : ℝ → H) : Prop where
  /-- The initial condition $u(0) = u_0$. -/
  apply_zero : u 0 = u₀
  /-- The solution takes its values in $D(A)$ at the times in $s$. -/
  mem_domain : ∀ t ∈ s, u t ∈ A.domain
  /-- At every $t \in s$, the derivative of $u$ within $s$ is $-Au(t)$. -/
  hasDerivWithinAt : ∀ t (ht : t ∈ s), HasDerivWithinAt u (-A ⟨u t, mem_domain t ht⟩) s t

variable {A : H →ₗ.[ℝ] H} {u₀ v₀ : H} {s : Set ℝ} {u v : ℝ → H}

/-- A solution of $u' + Au = 0$ on $s$ is continuous on $s$. -/
theorem IsSolutionOn.continuousOn (h : A.IsSolutionOn u₀ s u) : ContinuousOn u s :=
  fun t ht => (h.hasDerivWithinAt t ht).continuousWithinAt

/-- A solution of $u' + Au = 0$ on $s$ is a solution on every subset of $s$. -/
theorem IsSolutionOn.mono (h : A.IsSolutionOn u₀ s u) {t : Set ℝ} (hts : t ⊆ s) :
    A.IsSolutionOn u₀ t u where
  apply_zero := h.apply_zero
  mem_domain x hx := h.mem_domain x (hts hx)
  hasDerivWithinAt x hx := (h.hasDerivWithinAt x (hts hx)).mono hts

/-- **Time shift.** If $u$ solves $u' + Au = 0$ on $[0, \infty)$ and $a \ge 0$, then
$t \mapsto u(t + a)$ solves it on $[0, \infty)$ with the initial value $u(a)$. This is Remark 5
of Chapter 7 of [brezis2011functional]. -/
theorem IsSolutionOn.comp_add (h : A.IsSolutionOn u₀ (Ici 0) u) {a : ℝ} (ha : 0 ≤ a) :
    A.IsSolutionOn (u a) (Ici 0) fun t => u (t + a) where
  apply_zero := by simp
  mem_domain t ht := h.mem_domain (t + a) (add_nonneg ht ha)
  hasDerivWithinAt t ht := by
    have h1 := h.hasDerivWithinAt (t + a) (add_nonneg ht ha)
    have h2 : HasDerivWithinAt (fun t : ℝ => t + a) 1 (Ici 0) t :=
      (hasDerivWithinAt_id _ _).add_const a
    have := h1.scomp t h2 fun x hx => add_nonneg hx ha
    simpa [Function.comp_def] using this

/-- **Remark 6** of Chapter 7 of [brezis2011functional], forward direction. Let $c \in \mathbb{R}$.
If $u$ solves $u' + Au + cu = 0$ on $s$ with $u(0) = u_0$, then $v(t) = e^{ct} u(t)$ solves
$v' + Av = 0$ on $s$ with $v(0) = u_0$.

The operator $A + cI$ is `(c • LinearMap.id) +ᵥ A`, with the domain $D(A)$. -/
theorem IsSolutionOn.exp_smul {c : ℝ}
    (h : ((c • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ s u) :
    A.IsSolutionOn u₀ s fun t => Real.exp (c * t) • u t := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (c * t)) (Real.exp (c * t) * c) t :=
    fun t => by simpa using ((hasDerivAt_id t).const_mul c).exp
  refine ⟨by simpa using h.apply_zero, fun t ht => Submodule.smul_mem _ _ (h.mem_domain t ht),
    fun t ht => ?_⟩
  have h2 := HasDerivWithinAt.smul (hexp t).hasDerivWithinAt (h.hasDerivWithinAt t ht)
  convert h2 using 1
  change -A (Real.exp (c * t) • ⟨u t, h.mem_domain t ht⟩) = _
  rw [map_smul, vadd_apply, LinearMap.smul_apply, LinearMap.id_apply]
  module

/-- **Remark 6** of Chapter 7 of [brezis2011functional]. Let $c \in \mathbb{R}$. A curve $u$ solves
$u' + Au + cu = 0$ on $s$ with $u(0) = u_0$ if and only if $v(t) = e^{ct} u(t)$ solves
$v' + Av = 0$ on $s$ with $v(0) = u_0$. -/
theorem isSolutionOn_smul_id_vadd_iff {c : ℝ} :
    ((c • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ s u ↔
      A.IsSolutionOn u₀ s fun t => Real.exp (c * t) • u t := by
  refine ⟨IsSolutionOn.exp_smul, fun h => ?_⟩
  have hA : ((-c) • LinearMap.id : H →ₗ[ℝ] H) +ᵥ ((c • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A) = A := by
    rw [← add_vadd, ← add_smul, neg_add_cancel, zero_smul, zero_vadd]
  rw [← hA] at h
  have h' := h.exp_smul
  convert h' using 1
  funext t
  rw [smul_smul, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_smul]

/-! ### Step 1: uniqueness by monotonicity -/

/-- **Step 1 of the proof of the Hille–Yosida theorem, quantitative form, on $(0, \infty)$.** Let
$A$ be monotone, and let $u$ and $v$ solve $u' + Au = 0$ on $(0, \infty)$ with the initial
values $u_0$ and $v_0$, and be continuous on $[0, \infty)$. Then $t \mapsto \|u(t) - v(t)\|$ is
nonincreasing on $[0, \infty)$.

The reason is $\frac12 \frac{d}{dt} \|u - v\|^2 = -\langle A(u - v), u - v \rangle \le 0$ on
$(0, \infty)$. This is Step 1 of the proof of Theorem 7.4 and the uniqueness part of the proof
of Theorem 7.7 of [brezis2011functional]. -/
theorem IsMonotone.antitoneOn_norm_sub_of_isSolutionOn_Ioi (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hv : A.IsSolutionOn v₀ (Ioi 0) v)
    (hu' : ContinuousOn u (Ici 0)) (hv' : ContinuousOn v (Ici 0)) :
    AntitoneOn (fun t => ‖u t - v t‖) (Ici 0) := by
  have key : ∀ x (hx : x ∈ Ioi (0 : ℝ)), HasDerivAt (fun t => ‖u t - v t‖ ^ 2)
      (2 * ⟪u x - v x, -A ⟨u x, hu.mem_domain x hx⟩ - -A ⟨v x, hv.mem_domain x hx⟩⟫_ℝ) x :=
    fun x hx => (((hu.hasDerivWithinAt x hx).sub (hv.hasDerivWithinAt x hx)).hasDerivAt
      (Ioi_mem_nhds hx)).norm_sq
  have hφ : AntitoneOn (fun t => ‖u t - v t‖ ^ 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ((hu'.sub hv').norm.pow 2) ?_ ?_
    · rw [interior_Ici]
      exact fun x hx => (key x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(key x hx).deriv]
      have hm := hA (⟨u x, hu.mem_domain x hx⟩ - ⟨v x, hv.mem_domain x hx⟩)
      rw [map_sub, Submodule.coe_sub, RCLike.re_to_real] at hm
      rw [neg_sub_neg, ← neg_sub (A ⟨u x, hu.mem_domain x hx⟩), inner_neg_right, real_inner_comm]
      linarith
  intro a ha b hb hab
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hφ ha hb hab)

/-- **The contraction estimate on $(0, \infty)$.** Let $A$ be monotone, and let $u$ and $v$ solve
$u' + Au = 0$ on $(0, \infty)$ with the initial values $u_0$ and $v_0$, and be continuous on
$[0, \infty)$. Then $\|u(t) - v(t)\| \le \|u_0 - v_0\|$ for every $t \ge 0$. -/
theorem IsMonotone.norm_sub_le_of_isSolutionOn_Ioi (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hv : A.IsSolutionOn v₀ (Ioi 0) v)
    (hu' : ContinuousOn u (Ici 0)) (hv' : ContinuousOn v (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u₀ - v₀‖ := by
  have := hA.antitoneOn_norm_sub_of_isSolutionOn_Ioi hu hv hu' hv' self_mem_Ici ht ht
  simp only [hu.apply_zero, hv.apply_zero] at this
  exact this

/-- **Step 1 of the proof of the Hille–Yosida theorem.** Let $A$ be monotone, and let $u$ and $v$
solve $u' + Au = 0$ on $[0, \infty)$ with the initial values $u_0$ and $v_0$. Then
$\|u(t) - v(t)\| \le \|u_0 - v_0\|$ for every $t \ge 0$. This is Step 1 of the proof of Theorem
7.4 of [brezis2011functional]. -/
theorem IsMonotone.norm_sub_le_of_isSolutionOn (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ici 0) u) (hv : A.IsSolutionOn v₀ (Ici 0) v) {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u₀ - v₀‖ :=
  hA.norm_sub_le_of_isSolutionOn_Ioi (hu.mono Ioi_subset_Ici_self) (hv.mono Ioi_subset_Ici_self)
    hu.continuousOn hv.continuousOn ht

/-- **Uniqueness in the Hille–Yosida theorem.** Let $A$ be monotone. Two solutions of $u' + Au = 0$
on $[0, \infty)$ with the same initial value agree on $[0, \infty)$. This is the uniqueness part
of Theorem 7.4 of [brezis2011functional]; monotonicity alone suffices. -/
theorem IsMonotone.eqOn_of_isSolutionOn (hA : A.IsMonotone) (hu : A.IsSolutionOn u₀ (Ici 0) u)
    (hv : A.IsSolutionOn u₀ (Ici 0) v) : EqOn u v (Ici 0) := fun t ht => by
  have := hA.norm_sub_le_of_isSolutionOn hu hv ht
  rw [sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- **Uniqueness in Theorem 7.7** of [brezis2011functional]. Let $A$ be monotone. Two solutions of
$u' + Au = 0$ on $(0, \infty)$ with the same initial value that are continuous on $[0, \infty)$
agree on $[0, \infty)$. -/
theorem IsMonotone.eqOn_of_isSolutionOn_Ioi (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hv : A.IsSolutionOn u₀ (Ioi 0) v)
    (hu' : ContinuousOn u (Ici 0)) (hv' : ContinuousOn v (Ici 0)) : EqOn u v (Ici 0) :=
  fun t ht => by
  have := hA.norm_sub_le_of_isSolutionOn_Ioi hu hv hu' hv' ht
  rw [sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end LinearPMap

/-! ### The exponential of a bounded operator, and Lemma 7.1 -/

section Exp

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Let $E$ be a real Banach space, $B : E \to E$ a bounded operator and $w \in E$. Then
$t \mapsto e^{-tB} w$ has the derivative $-B e^{-tB} w$ at every $t$: it solves $w' + Bw = 0$. -/
theorem hasDerivAt_exp_neg_smul_apply (B : E →L[ℝ] E) (w : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp ((-t) • B) w) (-(B (exp ((-t) • B) w))) t := by
  have h1 : HasDerivAt (fun t : ℝ => exp ((-t) • B)) ((-B) * exp ((-t) • B)) t := by
    have := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-B) t
    simpa only [smul_neg, neg_smul] using this
  have h3 := h1.clm_apply (hasDerivAt_const t w)
  simpa using h3

omit [CompleteSpace E] in
/-- For a bounded operator $B$ on a real normed space, $e^{-tB}$ commutes with $B$:
$B e^{-tB} w = e^{-tB} B w$. -/
theorem exp_neg_smul_apply_comm (B : E →L[ℝ] E) (w : E) (t : ℝ) :
    B (exp ((-t) • B) w) = exp ((-t) • B) (B w) := by
  have h : Commute B (exp ((-t) • B)) := ((Commute.refl B).smul_right (-t)).exp_right
  exact DFunLike.congr_fun h w

omit [CompleteSpace E] in
/-- For a bounded operator $B$ on a real normed space, $e^{-0 \cdot B} w = w$. -/
theorem exp_neg_smul_zero_apply (B : E →L[ℝ] E) (w : E) : exp ((-(0 : ℝ)) • B) w = w := by
  simp [exp_zero]

/-- Let $E$ be a real Banach space and $B : E \to E$ a bounded operator. For every $w \in E$, the
curve $t \mapsto e^{-tB} w$ is continuous. -/
theorem continuous_exp_neg_smul_apply (B : E →L[ℝ] E) (w : E) :
    Continuous fun t : ℝ => exp ((-t) • B) w :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_neg_smul_apply B w t).continuousAt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Lemma 7.1** of [brezis2011functional] for a bounded monotone operator. Let $H$ be a real
Hilbert space and $B : H \to H$ a bounded operator with $\langle Bv, v \rangle \ge 0$ for all
$v$. Then for every $w \in H$, the function $t \mapsto \|e^{-tB} w\|$ is nonincreasing on
$[0, \infty)$.

The reason is $\frac12 \frac{d}{dt} \|e^{-tB} w\|^2 = -\langle Bu, u \rangle \le 0$ with
$u = e^{-tB} w$. The second clause of the lemma in the book, about $\|w'(t)\|$, is this lemma
applied to $w' = e^{-tB}(-Bw)$. -/
theorem antitoneOn_norm_exp_neg_smul_apply (B : H →L[ℝ] H) (hB : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) (w : H) :
    AntitoneOn (fun t : ℝ => ‖exp ((-t) • B) w‖) (Ici 0) := by
  have key : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ‖exp ((-t) • B) w‖ ^ 2)
      (2 * ⟪exp ((-t) • B) w, -(B (exp ((-t) • B) w))⟫_ℝ) t :=
    fun t => (hasDerivAt_exp_neg_smul_apply B w t).norm_sq
  have hφ : AntitoneOn (fun t : ℝ => ‖exp ((-t) • B) w‖ ^ 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (key t).continuousAt.continuousWithinAt)
      (fun t _ => (key t).differentiableAt.differentiableWithinAt) fun t _ => ?_
    rw [(key t).deriv, inner_neg_right, real_inner_comm]
    linarith [hB (exp ((-t) • B) w)]
  intro a ha b hb hab
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hφ ha hb hab)

/-- Let $H$ be a real Hilbert space and $B : H \to H$ a bounded operator with
$\langle Bv, v \rangle \ge 0$ for all $v$. Then $\|e^{-tB} w\| \le \|w\|$ for every $w \in H$
and $t \ge 0$. -/
theorem norm_exp_neg_smul_apply_le (B : H →L[ℝ] H) (hB : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) (w : H) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp ((-t) • B) w‖ ≤ ‖w‖ := by
  have := antitoneOn_norm_exp_neg_smul_apply B hB w self_mem_Ici ht ht
  simp only [exp_neg_smul_zero_apply] at this
  exact this

/-- Let $H$ be a real Hilbert space and $B : H \to H$ a bounded operator with
$\langle Bv, v \rangle \ge 0$ for all $v$. Then $\|e^{-tB}\| \le 1$ for every $t \ge 0$. -/
theorem norm_exp_neg_smul_le_one (B : H →L[ℝ] H) (hB : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp ((-t) • B)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    exact norm_exp_neg_smul_apply_le B hB w ht

end Exp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : H →ₗ.[ℝ] H}

/-! ### The approximate problem $u_\lambda(t) = e^{-tA_\lambda} u_0$ -/

variable (A) in
/-- The solution operator $e^{-tA_c}$ of the approximate problem $u' + A_c u = 0$, for
$c, t \in \mathbb{R}$, where $A_c$ is the Yosida approximation `LinearPMap.yosida A c`. The
solution with the initial value $u_0$ is $u_c(t) = e^{-tA_c} u_0$. This is problem (7) of §7.2
of [brezis2011functional]. -/
def expYosida (c t : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp ((-t) • A.yosida c)

variable [CompleteSpace H]

/-- Let $H$ be complete. For every $c \in \mathbb{R}$ and $w \in H$, the curve
$t \mapsto e^{-tA_c} w$ has the derivative $-A_c e^{-tA_c} w$ at every $t$: it solves
$u' + A_c u = 0$. -/
theorem hasDerivAt_expYosida_apply (c : ℝ) (w : H) (t : ℝ) :
    HasDerivAt (fun t => A.expYosida c t w) (-(A.yosida c (A.expYosida c t w))) t :=
  hasDerivAt_exp_neg_smul_apply _ w t

omit [CompleteSpace H] in
/-- For every $c \in \mathbb{R}$, $e^{-0 \cdot A_c}$ is the identity. -/
theorem expYosida_zero (c : ℝ) : A.expYosida c 0 = 1 := by
  simp [expYosida, NormedSpace.exp_zero]

omit [CompleteSpace H] in
/-- The Yosida approximation $A_c$ commutes with $e^{-tA_c}$: $A_c e^{-tA_c} w = e^{-tA_c} A_c w$.
-/
theorem yosida_expYosida_comm (c t : ℝ) (w : H) :
    A.yosida c (A.expYosida c t w) = A.expYosida c t (A.yosida c w) :=
  exp_neg_smul_apply_comm _ w t

/-- Let $H$ be complete. For every $c \in \mathbb{R}$ and $w \in H$, the curve
$t \mapsto e^{-tA_c} w$ is continuous. -/
theorem continuous_expYosida_apply (c : ℝ) (w : H) : Continuous fun t => A.expYosida c t w :=
  continuous_exp_neg_smul_apply _ w

/-- Let $H$ be complete and $A$ maximal monotone. For $c > 0$, the Yosida approximation is monotone:
$\langle A_c v, v \rangle \ge 0$ for every $v \in H$. -/
theorem IsMaximalMonotone.inner_yosida_nonneg (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c)
    (v : H) : 0 ≤ ⟪A.yosida c v, v⟫_ℝ := by
  simpa using hA.re_inner_yosida_nonneg hc v

/-- **Estimate (8)** of Step 2 of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be
complete, $A$ maximal monotone and $c > 0$. Then $\|e^{-tA_c} w\| \le \|w\|$ for every $t \ge 0$
and $w \in H$.

This is Lemma 7.1 for $B = A_c$, which is monotone by Proposition 7.2 (e). -/
theorem IsMaximalMonotone.norm_expYosida_apply_le (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : 0 ≤ t) (w : H) : ‖A.expYosida c t w‖ ≤ ‖w‖ :=
  norm_exp_neg_smul_apply_le _ (hA.inner_yosida_nonneg hc) w ht

/-- Let $H$ be complete, $A$ maximal monotone and $c > 0$. For every $w \in H$, the function
$t \mapsto \|e^{-tA_c} w\|$ is nonincreasing on $[0, \infty)$. This is Lemma 7.1 of
[brezis2011functional] for $A_c$. -/
theorem IsMaximalMonotone.antitoneOn_norm_expYosida_apply (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) (w : H) : AntitoneOn (fun t => ‖A.expYosida c t w‖) (Ici 0) :=
  antitoneOn_norm_exp_neg_smul_apply _ (hA.inner_yosida_nonneg hc) w

/-- **Estimate (9)** of Step 2 of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be
complete, $A$ maximal monotone and $c > 0$. Then $\|A_c e^{-tA_c} w\| \le \|A_c w\|$ for every
$t \ge 0$ and $w \in H$, that is, $\|u_c'(t)\|$ is at most its value at $0$. -/
theorem IsMaximalMonotone.norm_yosida_expYosida_apply_le (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (w : H) :
    ‖A.yosida c (A.expYosida c t w)‖ ≤ ‖A.yosida c w‖ := by
  rw [yosida_expYosida_comm]
  exact hA.norm_expYosida_apply_le hc ht _

/-- **Estimate (9)** of the proof of Theorem 7.4 of [brezis2011functional], on the domain. Let $H$
be complete, $A$ maximal monotone and $c > 0$. For $u_0 \in D(A)$ and $t \ge 0$,
$$\|u_c'(t)\| = \|A_c e^{-tA_c} u_0\| \le \|A u_0\|.$$

The proof uses Proposition 7.2 (b), $\|A_c u_0\| \le \|A u_0\|$. -/
theorem IsMaximalMonotone.norm_yosida_expYosida_apply_le_norm_apply (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (u₀ : A.domain) :
    ‖A.yosida c (A.expYosida c t u₀)‖ ≤ ‖A u₀‖ :=
  (hA.norm_yosida_expYosida_apply_le hc ht u₀).trans (hA.norm_yosida_apply_le_norm_apply hc u₀)

/-- **The Cauchy estimate (13)** of Step 3 of the proof of Theorem 7.4 of [brezis2011functional],
for two initial values. Let $H$ be complete, $A$ maximal monotone, $c, d > 0$, $t \ge 0$ and
$w_0, w_1 \in H$. If $\|A_c w_0\| \le M$ and $\|A_d w_1\| \le M$, then
$$\|e^{-tA_c} w_0 - e^{-tA_d} w_1\|^2 \le \|w_0 - w_1\|^2 + 4(c + d) t M^2.$$

With two initial values the estimate also serves the derivatives. Proof idea:
$\varphi = \|u_c - u_d\|^2$ has the derivative $-2 \langle A_c u_c - A_d u_d, u_c - u_d
\rangle$. By the inequality (12) this is at most $-2 \langle A_c u_c - A_d u_d, c A_c u_c - d
A_d u_d \rangle$, which is at most $4(c + d) M^2$ by (9). -/
theorem IsMaximalMonotone.norm_expYosida_sub_expYosida_le (hA : A.IsMaximalMonotone) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {w₀ w₁ : H} {M : ℝ}
    (h₀ : ‖A.yosida c w₀‖ ≤ M) (h₁ : ‖A.yosida d w₁‖ ≤ M) :
    ‖A.expYosida c t w₀ - A.expYosida d t w₁‖ ^ 2 ≤ ‖w₀ - w₁‖ ^ 2 + 4 * (c + d) * t * M ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans h₀
  set φ : ℝ → ℝ := fun s => ‖A.expYosida c s w₀ - A.expYosida d s w₁‖ ^ 2 with hφ
  set φ' : ℝ → ℝ := fun s => 2 * ⟪A.expYosida c s w₀ - A.expYosida d s w₁,
    -(A.yosida c (A.expYosida c s w₀)) - -(A.yosida d (A.expYosida d s w₁))⟫_ℝ with hφ'
  have hderiv : ∀ s, HasDerivAt φ (φ' s) s := fun s =>
    ((hasDerivAt_expYosida_apply c w₀ s).sub (hasDerivAt_expYosida_apply d w₁ s)).norm_sq
  have hbound : ∀ s ∈ Ico 0 t, φ' s ≤ 4 * (c + d) * M ^ 2 := by
    intro s hs
    set x := A.expYosida c s w₀
    set y := A.expYosida d s w₁
    set a := A.yosida c x
    set b := A.yosida d y
    have ha : ‖a‖ ≤ M := (hA.norm_yosida_expYosida_apply_le hc hs.1 w₀).trans h₀
    have hb : ‖b‖ ≤ M := (hA.norm_yosida_expYosida_apply_le hd hs.1 w₁).trans h₁
    have h12 := hA.re_inner_yosida_sub_yosida_ge hc hd x y
    simp only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id] at h12
    have h2 : -(‖a - b‖ * ‖c • a - d • b‖) ≤ ⟪a - b, c • a - d • b⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have h3 : ‖a - b‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
    have h4 : ‖c • a - d • b‖ ≤ (c + d) * M := by
      calc ‖c • a - d • b‖ ≤ ‖c • a‖ + ‖d • b‖ := norm_sub_le _ _
        _ = c * ‖a‖ + d * ‖b‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]
        _ ≤ c * M + d * M := by gcongr
        _ = (c + d) * M := by ring
    have h5 : ‖a - b‖ * ‖c • a - d • b‖ ≤ 2 * M * ((c + d) * M) :=
      mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    simp only [hφ']
    rw [neg_sub_neg, ← neg_sub a b, inner_neg_right, real_inner_comm]
    nlinarith [h12, h2, h5]
  have hφ0 : φ 0 = ‖w₀ - w₁‖ ^ 2 := by simp [hφ, expYosida_zero]
  have := image_le_of_deriv_right_le_deriv_boundary (f := φ) (f' := φ') (a := 0) (b := t)
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    (fun s _ => (hderiv s).hasDerivWithinAt)
    (B := fun s => φ 0 + 4 * (c + d) * M ^ 2 * s) (B' := fun _ => 4 * (c + d) * M ^ 2)
    (by simp) (by fun_prop)
    (fun s _ => by
      simpa using (((hasDerivAt_id s).const_mul (4 * (c + d) * M ^ 2)).const_add
        (φ 0)).hasDerivWithinAt (s := Ici s)) hbound
    (right_mem_Icc.2 ht)
  rw [hφ0] at this
  linarith

/-! ### The semigroup $S_A(t) = \lim_{\lambda \to 0^+} e^{-tA_\lambda}$ -/

/-- **The Cauchy estimate on the domain, in $\varepsilon$–$\delta$ form.** Let $H$ be complete and
$A$ maximal monotone. For $v_0 \in D(A)$, $t \ge 0$ and $\varepsilon > 0$, there is $\delta > 0$
such that $\|e^{-tA_c} v_0 - e^{-tA_d} v_0\| < \varepsilon$ for all $c, d \in (0, \delta)$. -/
theorem IsMaximalMonotone.exists_forall_norm_expYosida_sub_lt (hA : A.IsMaximalMonotone)
    {t : ℝ} (ht : 0 ≤ t) (v₀ : A.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ c d : ℝ, 0 < c → c < δ → 0 < d → d < δ →
      ‖A.expYosida c t v₀ - A.expYosida d t v₀‖ < ε := by
  set M := ‖A v₀‖
  refine ⟨ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1)), by positivity, fun c d hc hcδ hd hdδ => ?_⟩
  have h := hA.norm_expYosida_sub_expYosida_le hc hd ht (hA.norm_yosida_apply_le_norm_apply hc v₀)
    (hA.norm_yosida_apply_le_norm_apply hd v₀)
  rw [sub_self, norm_zero, zero_pow two_ne_zero, zero_add] at h
  refine lt_of_pow_lt_pow_left₀ 2 hε.le (h.trans_lt ?_)
  have key : (c + d) * (t * M ^ 2) < 2 * (ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1))) * ((t + 1) *
      (M ^ 2 + 1)) := by
    have h1 : t * M ^ 2 ≤ (t + 1) * (M ^ 2 + 1) := by nlinarith
    calc (c + d) * (t * M ^ 2) ≤ (c + d) * ((t + 1) * (M ^ 2 + 1)) := by gcongr
      _ < 2 * (ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1))) * ((t + 1) * (M ^ 2 + 1)) := by
          gcongr
          linarith
  have : 2 * (ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1))) * ((t + 1) * (M ^ 2 + 1)) = ε ^ 2 / 4 := by
    field_simp
    ring
  rw [this] at key
  nlinarith [key, sq_nonneg ε]

/-- Let $H$ be complete and $A$ maximal monotone. For every $u_0 \in H$ and $t \ge 0$, the family
$e^{-tA_c} u_0$ is Cauchy as $c \to 0^+$.

The proof combines the Cauchy estimate on the dense domain with $\|e^{-tA_c}\| \le 1$. This is
Step 3 of the proof of Theorem 7.4 and Remark 4 (b) of Chapter 7 of [brezis2011functional]. -/
theorem IsMaximalMonotone.cauchy_map_expYosida (hA : A.IsMaximalMonotone) {t : ℝ} (ht : 0 ≤ t)
    (u₀ : H) : Cauchy (map (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0)) := by
  rw [cauchy_map_iff', Metric.uniformity_basis_dist.tendsto_right_iff]
  intro ε hε
  obtain ⟨v₀, hv₀, hd⟩ := hA.dense_domain.exists_dist_lt u₀ (by positivity : 0 < ε / 3)
  rw [dist_eq_norm] at hd
  obtain ⟨δ, hδ0, hδ⟩ := hA.exists_forall_norm_expYosida_sub_lt ht ⟨v₀, hv₀⟩
    (by positivity : 0 < ε / 3)
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < c ∧ c < δ := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with c hc
    exact hc
  rw [eventually_prod_iff]
  refine ⟨_, hev, _, hev, fun {c} hc {d} hd' => ?_⟩
  simp only [dist_eq_norm]
  calc ‖A.expYosida c t u₀ - A.expYosida d t u₀‖
      = ‖A.expYosida c t (u₀ - v₀) + (A.expYosida c t v₀ - A.expYosida d t v₀) +
          A.expYosida d t (v₀ - u₀)‖ := by
        rw [_root_.map_sub, _root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.expYosida c t (u₀ - v₀)‖ + ‖A.expYosida c t v₀ - A.expYosida d t v₀‖ +
          ‖A.expYosida d t (v₀ - u₀)‖ := norm_add₃_le
    _ ≤ ‖u₀ - v₀‖ + ‖A.expYosida c t v₀ - A.expYosida d t v₀‖ + ‖v₀ - u₀‖ := by
        gcongr
        · exact hA.norm_expYosida_apply_le hc.1 ht _
        · exact hA.norm_expYosida_apply_le hd'.1 ht _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev v₀ u₀]
        gcongr
        exact hδ c d hc.1 hc.2 hd'.1 hd'.2
    _ = ε := by ring

variable (A) in
open scoped Classical in
/-- **The contraction semigroup** $S_A(t)$ generated by $-A$: the limit
$$S_A(t) u_0 = \lim_{c \to 0^+} e^{-tA_c} u_0.$$
This is Remark 5 and Remark 4 (b) of Chapter 7 of [brezis2011functional].

The definition is a total function of $(A, t)$ with a junk value, like `LinearPMap.resolvent`.
If there is a bounded operator $S$ with $e^{-tA_c} u_0 \to S u_0$ for every $u_0$, it is that
operator (it is then unique); otherwise it is $0$. The definition assumes no completeness, so
that the semigroup of the part `A.powPart j` on $D(A^j)$ is well formed before completeness is
supplied. The properties are stated under `A.IsMaximalMonotone` and $t \ge 0$. -/
def semigroup (t : ℝ) : H →L[ℝ] H :=
  if h : ∃ S : H →L[ℝ] H, ∀ u₀, Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 (S u₀))
  then h.choose else 0

/-- Let $H$ be complete, $A$ maximal monotone and $t \ge 0$. There is a bounded operator $S$ on $H$
with $e^{-tA_c} u_0 \to S u_0$ as $c \to 0^+$ for every $u_0 \in H$. -/
theorem IsMaximalMonotone.exists_semigroup (hA : A.IsMaximalMonotone) {t : ℝ} (ht : 0 ≤ t) :
    ∃ S : H →L[ℝ] H, ∀ u₀, Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 (S u₀)) := by
  have hlim : ∀ u₀ : H, ∃ L : H, Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 L) :=
    fun u₀ => CompleteSpace.complete (hA.cauchy_map_expYosida ht u₀)
  choose L hL using hlim
  let Lₗ : H →ₗ[ℝ] H :=
    { toFun := L
      map_add' := fun x y => tendsto_nhds_unique (hL (x + y))
        (by simpa [_root_.map_add] using (hL x).add (hL y))
      map_smul' := fun a x => tendsto_nhds_unique (hL (a • x))
        (by simpa [_root_.map_smul] using (hL x).const_smul a) }
  refine ⟨Lₗ.mkContinuous 1 fun u₀ => ?_, hL⟩
  rw [one_mul]
  refine le_of_tendsto (hL u₀).norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hA.norm_expYosida_apply_le hc ht u₀

/-- **The defining property of the semigroup.** Let $H$ be complete, $A$ maximal monotone and
$t \ge 0$. For every $u_0 \in H$, $e^{-tA_c} u_0 \to S_A(t) u_0$ as $c \to 0^+$. This is Remark
4 (b) of Chapter 7 of [brezis2011functional]. -/
theorem IsMaximalMonotone.tendsto_expYosida_semigroup (hA : A.IsMaximalMonotone) {t : ℝ}
    (ht : 0 ≤ t) (u₀ : H) :
    Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 (A.semigroup t u₀)) := by
  have h := hA.exists_semigroup ht
  unfold semigroup
  rw [dite_eq_left h]
  exact h.choose_spec u₀

/-- **Remark 5 (a)** of Chapter 7 of [brezis2011functional], pointwise. Let $H$ be complete and $A$
maximal monotone. Then $\|S_A(t) u_0\| \le \|u_0\|$ for every $t \ge 0$ and $u_0 \in H$. -/
theorem IsMaximalMonotone.norm_semigroup_apply_le (hA : A.IsMaximalMonotone) {t : ℝ}
    (ht : 0 ≤ t) (u₀ : H) : ‖A.semigroup t u₀‖ ≤ ‖u₀‖ := by
  refine le_of_tendsto (hA.tendsto_expYosida_semigroup ht u₀).norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hA.norm_expYosida_apply_le hc ht u₀

/-- **Remark 5 (a)** of Chapter 7 of [brezis2011functional]. Let $H$ be complete and $A$ maximal
monotone. Then $S_A(t)$ is a contraction, $\|S_A(t)\| \le 1$, for every $t \ge 0$. This is the
estimate $\|u(t)\| \le \|u_0\|$ of Theorem 7.4. -/
theorem IsMaximalMonotone.norm_semigroup_le_one (hA : A.IsMaximalMonotone) {t : ℝ} (ht : 0 ≤ t) :
    ‖A.semigroup t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u₀ => by
    rw [one_mul]
    exact hA.norm_semigroup_apply_le ht u₀

/-- **Remark 5 (b)** of Chapter 7 of [brezis2011functional], second clause. Let $H$ be complete and
$A$ maximal monotone. Then $S_A(0) = I$. -/
theorem IsMaximalMonotone.semigroup_zero (hA : A.IsMaximalMonotone) : A.semigroup 0 = 1 := by
  ext u₀
  refine tendsto_nhds_unique (hA.tendsto_expYosida_semigroup le_rfl u₀) ?_
  simp only [expYosida_zero, one_apply_eq_self]
  exact tendsto_const_nhds

/-- Let $H$ be complete and $A$ maximal monotone. For every $w \in H$, the function
$t \mapsto \|S_A(t) w\|$ is nonincreasing on $[0, \infty)$.

It is a pointwise limit of the nonincreasing functions $t \mapsto \|e^{-tA_c} w\|$ (Lemma 7.1 of
[brezis2011functional] in the limit). -/
theorem IsMaximalMonotone.antitoneOn_norm_semigroup_apply (hA : A.IsMaximalMonotone) (w : H) :
    AntitoneOn (fun t => ‖A.semigroup t w‖) (Ici 0) := by
  intro a ha b hb hab
  refine le_of_tendsto_of_tendsto (hA.tendsto_expYosida_semigroup hb w).norm
    (hA.tendsto_expYosida_semigroup ha w).norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hA.antitoneOn_norm_expYosida_apply hc w ha hb hab

/-- **Estimate (13')** of Step 3 of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be
complete, $A$ maximal monotone and $c > 0$. For $u_0 \in D(A)$ and $t \ge 0$,
$$\|e^{-tA_c} u_0 - S_A(t) u_0\| \le 2 \sqrt{ct} \, \|A u_0\|.$$

The proof lets $d \to 0^+$ in the Cauchy estimate (13). -/
theorem IsMaximalMonotone.norm_expYosida_sub_semigroup_le (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (u₀ : A.domain) :
    ‖A.expYosida c t u₀ - A.semigroup t u₀‖ ≤ 2 * Real.sqrt (c * t) * ‖A u₀‖ := by
  have hsq : ‖A.expYosida c t u₀ - A.semigroup t u₀‖ ^ 2 ≤ 4 * c * t * ‖A u₀‖ ^ 2 := by
    have h1 : Tendsto (fun d : ℝ => ‖A.expYosida c t u₀ - A.expYosida d t u₀‖ ^ 2) (𝓝[>] 0)
        (𝓝 (‖A.expYosida c t u₀ - A.semigroup t u₀‖ ^ 2)) :=
      ((tendsto_const_nhds.sub (hA.tendsto_expYosida_semigroup ht u₀)).norm).pow 2
    have h2 : Tendsto (fun d : ℝ => ‖(u₀ : H) - u₀‖ ^ 2 + 4 * (c + d) * t * ‖A u₀‖ ^ 2)
        (𝓝[>] 0) (𝓝 (‖(u₀ : H) - u₀‖ ^ 2 + 4 * (c + 0) * t * ‖A u₀‖ ^ 2)) :=
      ((Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds)
    have := le_of_tendsto_of_tendsto h1 h2 (by
      filter_upwards [self_mem_nhdsWithin] with d hd
      exact hA.norm_expYosida_sub_expYosida_le hc hd ht
        (hA.norm_yosida_apply_le_norm_apply hc u₀) (hA.norm_yosida_apply_le_norm_apply hd u₀))
    simpa using this
  have h4 : (2 * Real.sqrt (c * t) * ‖A u₀‖) ^ 2 = 4 * c * t * ‖A u₀‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), h4]
  exact hsq

/-- **Uniform convergence on bounded intervals**, Step 3 of the proof of Theorem 7.4 of
[brezis2011functional]. Let $H$ be complete and $A$ maximal monotone. For every $w \in H$ and
$T \in \mathbb{R}$, $e^{-tA_c} w \to S_A(t) w$ uniformly in $t \in [0, T]$ as $c \to 0^+$.

On $D(A)$ this follows from (13'), and in general from the density of $D(A)$ and the contraction
property. -/
theorem IsMaximalMonotone.tendstoUniformlyOn_expYosida_semigroup (hA : A.IsMaximalMonotone)
    (w : H) {T : ℝ} :
    TendstoUniformlyOn (fun (c : ℝ) t => A.expYosida c t w) (fun t => A.semigroup t w)
      (𝓝[>] 0) (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨w₁, hw₁, hd⟩ := hA.dense_domain.exists_dist_lt w (by positivity : 0 < ε / 3)
  rw [dist_eq_norm] at hd
  have hlim : Tendsto (fun c : ℝ => 2 * Real.sqrt (c * T) * ‖A ⟨w₁, hw₁⟩‖) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun c : ℝ => 2 * Real.sqrt (c * T) * ‖A ⟨w₁, hw₁⟩‖) (𝓝 0)
        (𝓝 (2 * Real.sqrt (0 * T) * ‖A ⟨w₁, hw₁⟩‖)) := Continuous.tendsto (by fun_prop) 0
    simpa using this.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)),
    self_mem_nhdsWithin] with c hc hc0
  intro t ht
  have hc' : (0 : ℝ) < c := hc0
  rw [dist_eq_norm]
  calc ‖A.semigroup t w - A.expYosida c t w‖
      = ‖A.semigroup t (w - w₁) + (A.semigroup t w₁ - A.expYosida c t w₁) +
          A.expYosida c t (w₁ - w)‖ := by
        rw [_root_.map_sub, _root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.semigroup t (w - w₁)‖ + ‖A.semigroup t w₁ - A.expYosida c t w₁‖ +
          ‖A.expYosida c t (w₁ - w)‖ := norm_add₃_le
    _ ≤ ‖w - w₁‖ + 2 * Real.sqrt (c * T) * ‖A ⟨w₁, hw₁⟩‖ + ‖w₁ - w‖ := by
        gcongr
        · exact hA.norm_semigroup_apply_le ht.1 _
        · rw [norm_sub_rev]
          refine (hA.norm_expYosida_sub_semigroup_le hc' ht.1 ⟨w₁, hw₁⟩).trans ?_
          gcongr
          exact ht.2
        · exact hA.norm_expYosida_apply_le hc' ht.1 _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev w₁ w]
        gcongr
    _ = ε := by ring

/-- **The semigroup is strongly continuous on $[0, \infty)$.** Let $H$ be complete and $A$ maximal
monotone. For every $w \in H$, the curve $t \mapsto S_A(t) w$ is continuous on $[0, \infty)$.

It is a locally uniform limit of the continuous curves $t \mapsto e^{-tA_c} w$. This is the
claim $u \in C([0, \infty); H)$ of Step 3 of the proof of Theorem 7.4 of [brezis2011functional]. -/
theorem IsMaximalMonotone.continuousOn_semigroup_apply (hA : A.IsMaximalMonotone) (w : H) :
    ContinuousOn (fun t => A.semigroup t w) (Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have h1 : ContinuousOn (fun t => A.semigroup t w) (Icc 0 (t + 1)) :=
    (hA.tendstoUniformlyOn_expYosida_semigroup w).continuousOn
      (Eventually.of_forall fun c => (continuous_expYosida_apply c w).continuousOn).frequently
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h1 t ⟨ht', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **Remark 5 (c)** of Chapter 7 of [brezis2011functional]. Let $H$ be complete and $A$ maximal
monotone. For every $w \in H$, $S_A(t) w \to w$ as $t \to 0^+$. -/
theorem IsMaximalMonotone.tendsto_semigroup_apply_zero (hA : A.IsMaximalMonotone) (w : H) :
    Tendsto (fun t => A.semigroup t w) (𝓝[>] 0) (𝓝 w) := by
  have := (hA.continuousOn_semigroup_apply w 0 self_mem_Ici).tendsto
  rw [hA.semigroup_zero, one_apply_eq_self] at this
  exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- **Step 4** of the proof of Theorem 7.4 of [brezis2011functional], shortened. Let $H$ be complete
and $A$ maximal monotone. For $u_0 \in D(A)$ and $T \in \mathbb{R}$,
$$e^{-tA_c} A_c u_0 \to S_A(t) A u_0 \quad \text{uniformly in } t \in [0, T] \text{ as } c \to
  0^+.$$
So the derivatives $u_c'(t) = -e^{-tA_c} A_c u_0$ converge uniformly on $[0, T]$ to
$-S_A(t) A u_0$.

The proof uses $\|e^{-tA_c} A_c u_0 - S_A(t) A u_0\| \le \|A_c u_0 - A u_0\| + \|e^{-tA_c} A
u_0 - S_A(t) A u_0\|$ and Proposition 7.2 (d). The book proves this for $u_0 \in D(A^2)$ and
needs its Step 6 to remove that assumption. -/
theorem IsMaximalMonotone.tendstoUniformlyOn_deriv_expYosida (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {T : ℝ} :
    TendstoUniformlyOn (fun (c : ℝ) t => A.expYosida c t (A.yosida c u₀))
      (fun t => A.semigroup t (A u₀)) (𝓝[>] 0) (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (hA.tendsto_yosida_apply u₀)
  have h2 := Metric.tendstoUniformlyOn_iff.1
    (hA.tendstoUniformlyOn_expYosida_semigroup (A u₀) (T := T)) (ε / 2) (by positivity)
  filter_upwards [h1.eventually (gt_mem_nhds (half_pos hε)), h2, self_mem_nhdsWithin] with c hc1
    hc2 hc0
  intro t ht
  have hc' : (0 : ℝ) < c := hc0
  rw [dist_eq_norm]
  calc ‖A.semigroup t (A u₀) - A.expYosida c t (A.yosida c u₀)‖
      = ‖(A.semigroup t (A u₀) - A.expYosida c t (A u₀)) +
          A.expYosida c t (A u₀ - A.yosida c u₀)‖ := by
        rw [_root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.semigroup t (A u₀) - A.expYosida c t (A u₀)‖ +
          ‖A.expYosida c t (A u₀ - A.yosida c u₀)‖ := norm_add_le _ _
    _ ≤ dist (A.semigroup t (A u₀)) (A.expYosida c t (A u₀)) + ‖A u₀ - A.yosida c u₀‖ := by
        rw [dist_eq_norm]
        gcongr
        exact hA.norm_expYosida_apply_le hc' ht.1 _
    _ < ε / 2 + ε / 2 := by
        rw [norm_sub_rev]
        exact add_lt_add (hc2 t ht) hc1
    _ = ε := by ring

end LinearPMap

/-! ### The derivative of a uniform limit on a closed interval -/

section UniformLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The derivative of a uniform limit, on a closed interval.** Let $E$ be a real Banach space,
$a \le b$, and let $(F_i)$ be a family of curves $\mathbb{R} \to E$ indexed along a nontrivial
filter. Assume that eventually each $F_i$ has the derivative $F_i'(t)$ within $[a, b]$ at every
$t \in [a, b]$, with $F_i'$ continuous on $[a, b]$, that $F_i' \to g$ uniformly on $[a, b]$, and
that $F_i(t) \to f(t)$ for every $t \in [a, b]$. Then $f$ has the derivative $g(t)$ within
$[a, b]$ at every $t \in [a, b]$, the endpoints included.

This is a closed-interval version of Mathlib's `hasDerivAt_of_tendstoUniformlyOn`, which needs
an open set. Proof idea: $F_i(t) = F_i(a) + \int_a^t F_i'$, the integrals converge, so
$f(t) = f(a) + \int_a^t g$, which is differentiated within $[a, b]$. -/
theorem hasDerivWithinAt_Icc_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} [NeBot l]
    {a b : ℝ} (hab : a ≤ b) {F F' : ι → ℝ → E} {f g : ℝ → E}
    (hF : ∀ᶠ i in l, ∀ t ∈ Icc a b, HasDerivWithinAt (F i) (F' i t) (Icc a b) t)
    (hF' : ∀ᶠ i in l, ContinuousOn (F' i) (Icc a b))
    (hg : TendstoUniformlyOn F' g l (Icc a b))
    (hf : ∀ t ∈ Icc a b, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  have hgc : ContinuousOn g (Icc a b) := hg.continuousOn hF'.frequently
  -- the integral representation of each `F i`
  have hint : ∀ᶠ i in l, ∀ t ∈ Icc a b, F i t = F i a + ∫ s in a..t, F' i s := by
    filter_upwards [hF, hF'] with i hFi hF'i
    intro t ht
    have hderiv : ∀ x ∈ Ioo a t, HasDerivWithinAt (F i) (F' i x) (Ioi x) x := fun x hx =>
      ((hFi x ⟨hx.1.le, hx.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hx.1 (hx.2.trans_le ht.2))).hasDerivWithinAt
    have hcont : ContinuousOn (F i) (Icc a t) :=
      (HasDerivWithinAt.continuousOn hFi).mono (Icc_subset_Icc_right ht.2)
    have hii : IntervalIntegrable (F' i) MeasureTheory.volume a t :=
      (hF'i.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcont hderiv hii]
    abel
  -- the integrals converge
  have hlim : ∀ t ∈ Icc a b,
      Tendsto (fun i => ∫ s in a..t, F' i s) l (𝓝 (∫ s in a..t, g s)) := by
    intro t ht
    have hgi : IntervalIntegrable g MeasureTheory.volume a t :=
      (hgc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (b - a + 1) := by
      positivity
    filter_upwards [hF', Metric.tendstoUniformlyOn_iff.1 hg _ hε'] with i hF'i hi
    have hii : IntervalIntegrable (F' i) MeasureTheory.volume a t :=
      (hF'i.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [dist_eq_norm, ← intervalIntegral.integral_sub hii hgi]
    have hb : ∀ s ∈ uIoc a t, ‖F' i s - g s‖ ≤ ε / (b - a + 1) := by
      intro s hs
      rw [uIoc_of_le ht.1] at hs
      have := hi s ⟨hs.1.le, hs.2.trans ht.2⟩
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le
    calc ‖∫ s in a..t, (F' i s - g s)‖ ≤ ε / (b - a + 1) * |t - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ ≤ ε / (b - a + 1) * (b - a) := by
          gcongr
          rw [abs_of_nonneg (by linarith [ht.1])]
          linarith [ht.2]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  -- the limit `f` has the integral representation
  have hrep : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, g s := fun t ht =>
    tendsto_nhds_unique (hf t ht) (by
      refine ((hf a (left_mem_Icc.2 hab)).add (hlim t ht)).congr' ?_
      filter_upwards [hint] with i hi
      exact (hi t ht).symm)
  -- differentiate the representation
  intro t ht
  have : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hgi : IntervalIntegrable g MeasureTheory.volume a t :=
    (hgc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hd : HasDerivWithinAt (fun u => ∫ s in a..u, g s) (g t) (Icc a b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hgi
      (hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hgc t ht)
  exact (hd.const_add (f a)).congr hrep (hrep t ht)

end UniformLimit

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {A : H →ₗ.[ℝ] H}

/-! ### Step 5: the limit solves the equation -/

/-- **Step 5 (iii)** of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be complete and
$A$ maximal monotone. For $u_0 \in D(A)$ and $t \ge 0$, the curve $t \mapsto S_A(t) u_0$ has the
derivative $-S_A(t) A u_0$ within $[0, \infty)$ at $t$.

The proof applies `hasDerivWithinAt_Icc_of_tendstoUniformlyOn` to
$u_c(\cdot) = e^{-\cdot A_c} u_0$ on $[0, t + 1]$; the derivatives $-e^{-\cdot A_c} A_c u_0$
converge uniformly by Step 4. -/
theorem IsMaximalMonotone.hasDerivWithinAt_semigroup_apply (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => A.semigroup t u₀) (-(A.semigroup t (A u₀))) (Ici 0) t := by
  have hT : (0 : ℝ) ≤ t + 1 := by linarith
  have key := hasDerivWithinAt_Icc_of_tendstoUniformlyOn (l := 𝓝[>] (0 : ℝ)) hT
    (F := fun c t => A.expYosida c t u₀)
    (F' := fun c t => -(A.expYosida c t (A.yosida c u₀)))
    (f := fun t => A.semigroup t u₀) (g := fun t => -(A.semigroup t (A u₀)))
    (Eventually.of_forall fun c τ _ => by
      have := (hasDerivAt_expYosida_apply (A := A) c u₀ τ).hasDerivWithinAt (s := Icc 0 (t + 1))
      rwa [yosida_expYosida_comm] at this)
    (Eventually.of_forall fun c => (continuous_expYosida_apply c _).neg.continuousOn)
    (uniformContinuous_neg.comp_tendstoUniformlyOn
      (hA.tendstoUniformlyOn_deriv_expYosida u₀))
    (fun s hs => hA.tendsto_expYosida_semigroup hs.1 u₀)
  refine (key t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- **Step 5 (i)–(ii)** of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be complete
and $A$ maximal monotone. For $u_0 \in D(A)$ and $t \ge 0$, $S_A(t) u_0 \in D(A)$ and
$A S_A(t) u_0 = S_A(t) A u_0$.

Proof idea: the pairs $(J_c e^{-tA_c} u_0, A_c e^{-tA_c} u_0)$ lie on the graph of $A$ and
converge to $(S_A(t) u_0, S_A(t) A u_0)$, and the graph is closed. -/
theorem IsMaximalMonotone.exists_semigroup_apply_mem_domain (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : A.semigroup t u₀ ∈ A.domain, A ⟨A.semigroup t u₀, h⟩ = A.semigroup t (A u₀) := by
  have hcl : _root_.IsClosed (A.graph : Set (H × H)) := hA.isClosed
  have h1 : Tendsto (fun c : ℝ => A.resolvent c (A.expYosida c t u₀)) (𝓝[>] 0)
      (𝓝 (A.semigroup t u₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 : Tendsto (fun c : ℝ => ‖A.expYosida c t u₀ - A.semigroup t u₀‖ +
        ‖A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀‖) (𝓝[>] 0) (𝓝 (0 + 0)) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 (hA.tendsto_expYosida_semigroup ht u₀)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 (hA.tendsto_resolvent_apply _))
    rw [add_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun c => norm_nonneg _) ?_ h2
    filter_upwards [self_mem_nhdsWithin] with c hc
    calc ‖A.resolvent c (A.expYosida c t u₀) - A.semigroup t u₀‖
        = ‖A.resolvent c (A.expYosida c t u₀ - A.semigroup t u₀) +
            (A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀)‖ := by
          rw [_root_.map_sub]
          congr 1
          abel
      _ ≤ ‖A.resolvent c (A.expYosida c t u₀ - A.semigroup t u₀)‖ +
            ‖A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀‖ := norm_add_le _ _
      _ ≤ ‖A.expYosida c t u₀ - A.semigroup t u₀‖ +
            ‖A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀‖ := by
          gcongr
          exact hA.norm_resolvent_apply_le hc _
  have h2 : Tendsto (fun c : ℝ => A.expYosida c t (A.yosida c u₀)) (𝓝[>] 0)
      (𝓝 (A.semigroup t (A u₀))) :=
    (hA.tendstoUniformlyOn_deriv_expYosida u₀).tendsto_at ⟨ht, le_rfl⟩
  have hmem : (A.semigroup t u₀, A.semigroup t (A u₀)) ∈ A.graph := by
    refine hcl.mem_of_tendsto (h1.prodMk_nhds h2) ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [← yosida_expYosida_comm, hA.yosida_apply_eq_apply_resolvent hc]
    exact A.mem_graph ⟨_, hA.resolvent_apply_mem_domain hc _⟩
  rw [mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  change (y : H) = A.semigroup t u₀ at hy1
  change A y = A.semigroup t (A u₀) at hy2
  refine ⟨hy1 ▸ y.2, ?_⟩
  rw [show (⟨A.semigroup t u₀, hy1 ▸ y.2⟩ : A.domain) = y from Subtype.ext hy1.symm]
  exact hy2

/-- **Step 5 (i)** of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be complete and
$A$ maximal monotone. Then $S_A(t) u_0 \in D(A)$ for $u_0 \in D(A)$ and $t \ge 0$. -/
theorem IsMaximalMonotone.semigroup_apply_mem_domain (hA : A.IsMaximalMonotone) (u₀ : A.domain)
    {t : ℝ} (ht : 0 ≤ t) : A.semigroup t u₀ ∈ A.domain :=
  (hA.exists_semigroup_apply_mem_domain u₀ ht).fst

/-- **Step 5 (ii)** of the proof of Theorem 7.4 of [brezis2011functional]. Let $H$ be complete and
$A$ maximal monotone. Then $S_A(t)$ commutes with $A$ on $D(A)$: $A S_A(t) u_0 = S_A(t) A u_0$
for $u_0 \in D(A)$ and $t \ge 0$. -/
theorem IsMaximalMonotone.semigroup_apply_apply (hA : A.IsMaximalMonotone) (u₀ : A.domain)
    {t : ℝ} (ht : 0 ≤ t) :
    A ⟨A.semigroup t u₀, hA.semigroup_apply_mem_domain u₀ ht⟩ = A.semigroup t (A u₀) :=
  (hA.exists_semigroup_apply_mem_domain u₀ ht).snd

/-! ### Theorem 7.4 (Hille–Yosida) -/

/-- **Theorem 7.4** of [brezis2011functional], existence. Let $H$ be complete and $A$ maximal
monotone. For $u_0 \in D(A)$, the curve $t \mapsto S_A(t) u_0$ solves $u' + Au = 0$ on
$[0, \infty)$ with $u(0) = u_0$. -/
theorem IsMaximalMonotone.isSolutionOn_semigroup (hA : A.IsMaximalMonotone) (u₀ : A.domain) :
    A.IsSolutionOn u₀ (Ici 0) fun t => A.semigroup t u₀ where
  apply_zero := by simp [hA.semigroup_zero]
  mem_domain t ht := hA.semigroup_apply_mem_domain u₀ ht
  hasDerivWithinAt t ht := by
    have := hA.hasDerivWithinAt_semigroup_apply u₀ ht
    rwa [← hA.semigroup_apply_apply u₀ ht] at this

/-- Let $H$ be complete and $A$ maximal monotone. If $u$ solves $u' + Au = 0$ on $[0, \infty)$ with
$u(0) = u_0 \in D(A)$, then $u(t) = S_A(t) u_0$ for every $t \ge 0$.

With this theorem, every statement about the solution $u$ of problem (6) of the book transfers
to $S_A$. -/
theorem IsSolutionOn.eq_semigroup (hA : A.IsMaximalMonotone) {u₀ : A.domain} {u : ℝ → H}
    (hu : A.IsSolutionOn u₀ (Ici 0) u) : EqOn u (fun t => A.semigroup t u₀) (Ici 0) :=
  hA.isMonotone.eqOn_of_isSolutionOn hu (hA.isSolutionOn_semigroup u₀)

/-- **Theorem 7.4** of [brezis2011functional], the class $C^1([0, \infty); H)$. Let $H$ be complete
and $A$ maximal monotone. For $u_0 \in D(A)$, the curve $t \mapsto S_A(t) u_0$ is $C^1$ on
$[0, \infty)$; its derivative $-S_A(t) A u_0$ is continuous. -/
theorem IsMaximalMonotone.contDiffOn_semigroup_apply (hA : A.IsMaximalMonotone) (u₀ : A.domain) :
    ContDiffOn ℝ 1 (fun t => A.semigroup t u₀) (Ici 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht => (hA.hasDerivWithinAt_semigroup_apply u₀ ht).differentiableWithinAt,
    fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  refine (hA.continuousOn_semigroup_apply (A u₀)).neg.congr fun t ht => ?_
  exact (hA.hasDerivWithinAt_semigroup_apply u₀ ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- **Theorem 7.4** of [brezis2011functional], the estimate on the derivative. Let $H$ be complete
and $A$ maximal monotone. For $u_0 \in D(A)$ and $t \ge 0$,
$$\|u'(t)\| = \|A S_A(t) u_0\| \le \|A u_0\|, \qquad u(t) = S_A(t) u_0.$$
-/
theorem IsMaximalMonotone.norm_apply_semigroup_apply_le (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖A ⟨A.semigroup t u₀, hA.semigroup_apply_mem_domain u₀ ht⟩‖ ≤ ‖A u₀‖ := by
  rw [hA.semigroup_apply_apply u₀ ht]
  exact hA.norm_semigroup_apply_le ht _

/-- **The Lipschitz estimate in time.** Let $H$ be complete and $A$ maximal monotone. For
$u_0 \in D(A)$ and $t \ge 0$, $\|S_A(t) u_0 - u_0\| \le t \|A u_0\|$. -/
theorem IsMaximalMonotone.norm_semigroup_apply_sub_le (hA : A.IsMaximalMonotone) (u₀ : A.domain)
    {t : ℝ} (ht : 0 ≤ t) : ‖A.semigroup t u₀ - u₀‖ ≤ t * ‖A u₀‖ := by
  have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => A.semigroup t u₀)
    (f' := fun t => -(A.semigroup t (A u₀))) (a := 0) (b := t) (C := ‖A u₀‖)
    ((hA.continuousOn_semigroup_apply u₀).mono Icc_subset_Ici_self)
    (fun x hx => (hA.hasDerivWithinAt_semigroup_apply u₀ hx.1).mono (Ici_subset_Ici.2 hx.1))
    (fun x hx => by
      rw [norm_neg]
      exact hA.norm_semigroup_apply_le hx.1 _) t (right_mem_Icc.2 ht)
  simpa [hA.semigroup_zero, mul_comm] using this

/-- **Theorem 7.4** of [brezis2011functional] (the **Hille–Yosida theorem**). Let $H$ be a real
Hilbert space, $A$ maximal monotone and $u_0 \in D(A)$. Then the evolution problem $u' + Au = 0$
on $[0, \infty)$, $u(0) = u_0$ has a solution $u \in C^1([0, \infty); H)$ with
$$\|u(t)\| \le \|u_0\| \quad \text{and} \quad \|u'(t)\| = \|Au(t)\| \le \|A u_0\|, \qquad t \ge
  0.$$

The solution is $t \mapsto S_A(t) u_0$. Uniqueness is
`LinearPMap.IsMonotone.eqOn_of_isSolutionOn`. -/
theorem IsMaximalMonotone.exists_isSolutionOn (hA : A.IsMaximalMonotone) (u₀ : A.domain) :
    ∃ u : ℝ → H, ∃ hu : A.IsSolutionOn u₀ (Ici 0) u, ContDiffOn ℝ 1 u (Ici 0) ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖(u₀ : H)‖) ∧
      ∀ t (ht : 0 ≤ t), ‖A ⟨u t, hu.mem_domain t ht⟩‖ ≤ ‖A u₀‖ :=
  ⟨fun t => A.semigroup t u₀, hA.isSolutionOn_semigroup u₀, hA.contDiffOn_semigroup_apply u₀,
    fun _ ht => hA.norm_semigroup_apply_le ht u₀,
    fun _ ht => hA.norm_apply_semigroup_apply_le u₀ ht⟩

/-- **Remark 5 (b)** of Chapter 7 of [brezis2011functional], the semigroup law. Let $H$ be complete
and $A$ maximal monotone. Then $S_A(s + t) = S_A(s) S_A(t)$ for all $s, t \ge 0$.

Proof idea: both sides applied to $u_0 \in D(A)$ solve the problem with the initial value
$S_A(t) u_0 \in D(A)$. So they agree on the dense subspace $D(A)$, hence everywhere. -/
theorem IsMaximalMonotone.semigroup_add (hA : A.IsMaximalMonotone) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) : A.semigroup (s + t) = (A.semigroup s).comp (A.semigroup t) := by
  have h : ⇑(A.semigroup (s + t)) = ⇑((A.semigroup s).comp (A.semigroup t)) := by
    refine Continuous.ext_on hA.dense_domain (A.semigroup (s + t)).continuous
      ((A.semigroup s).comp (A.semigroup t)).continuous fun u₀ hu₀ => ?_
    have h1 : A.IsSolutionOn (A.semigroup t u₀) (Ici 0) fun τ => A.semigroup (τ + t) u₀ :=
      (hA.isSolutionOn_semigroup ⟨u₀, hu₀⟩).comp_add ht
    have h2 : A.IsSolutionOn (A.semigroup t u₀) (Ici 0)
        fun τ => A.semigroup τ (A.semigroup t u₀) :=
      hA.isSolutionOn_semigroup ⟨A.semigroup t u₀, hA.semigroup_apply_mem_domain ⟨u₀, hu₀⟩ ht⟩
    exact hA.isMonotone.eqOn_of_isSolutionOn h1 h2 hs
  exact ContinuousLinearMap.ext fun x => congrFun h x

/-! ### The classes $C^n(s; D(A^j))$ -/

open PowDomain

variable (A) in
/-- **The class $C^n(s; D(A^j))$**, used in Theorems 7.5 and 7.7 of [brezis2011functional]. A curve
$u : \mathbb{R} \to H$ is in this class if it lifts on $s$ to a $C^n$ map into the Hilbert space
$D(A^j)$: there is $v : \mathbb{R} \to D(A^j)$, $C^n$ on $s$, whose coordinate $v(t)_0$ is
$u(t)$ for $t \in s$.

The lift is unique on $s$, because its coordinates are $A^i u$.
`LinearPMap.contDiffOnPowDomain_iff` reads the condition coordinatewise. Users compose the lift
with bounded operators out of `A.PowDomain j`. -/
def ContDiffOnPowDomain (n : WithTop ℕ∞) (j : ℕ) (u : ℝ → H) (s : Set ℝ) : Prop :=
  ∃ v : ℝ → A.PowDomain j, (∀ t ∈ s, applyL A j 0 (v t) = u t) ∧ ContDiffOn ℝ n v s

omit [CompleteSpace H] in
/-- If $u$ is in $C^n(s; D(A^j))$ and $t \subseteq s$, then $u$ is in $C^n(t; D(A^j))$. -/
theorem ContDiffOnPowDomain.mono {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s t : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (hts : t ⊆ s) : A.ContDiffOnPowDomain n j u t :=
  let ⟨v, hv0, hv⟩ := h
  ⟨v, fun x hx => hv0 x (hts hx), hv.mono hts⟩

omit [CompleteSpace H] in
/-- If $u$ is in $C^n(s; D(A^j))$ and $m \le n$, then $u$ is in $C^m(s; D(A^j))$. -/
theorem ContDiffOnPowDomain.of_le {n m : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (hmn : m ≤ n) : A.ContDiffOnPowDomain m j u s :=
  let ⟨v, hv0, hv⟩ := h
  ⟨v, hv0, hv.of_le hmn⟩

omit [CompleteSpace H] in
/-- If $u$ is in $C^n(s; D(A^j))$ and $v = u$ on $s$, then $v$ is in $C^n(s; D(A^j))$. -/
theorem ContDiffOnPowDomain.congr {n : WithTop ℕ∞} {j : ℕ} {u v : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (huv : Set.EqOn u v s) :
    A.ContDiffOnPowDomain n j v s :=
  let ⟨w, hw0, hw⟩ := h
  ⟨w, fun t ht => (hw0 t ht).trans (huv ht), hw⟩

omit [CompleteSpace H] in
/-- $C^n(s; D(A^{j+1})) \subseteq C^n(s; D(A^j))$, through the inclusion
`LinearPMap.PowDomain.castL`. -/
theorem ContDiffOnPowDomain.castSucc {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n (j + 1) u s) : A.ContDiffOnPowDomain n j u s :=
  let ⟨v, hv0, hv⟩ := h
  ⟨fun t => castL A j (v t), fun t ht => by rw [applyL_castL]; exact hv0 t ht,
    (castL A j).contDiff.comp_contDiffOn hv⟩

/-- **The coordinatewise reading of $C^n(s; D(A^j))$.** Let $H$ be complete and $A$ closed. A curve
$u$ is in $C^n(s; D(A^j))$ if and only if there are curves $w_0, w_1, \dots, w_j$, each $C^n$ on
$s$, with $w_0 = u$ on $s$ and, at every $t \in s$, $w_i(t) \in D(A)$ and
$A w_i(t) = w_{i+1}(t)$ for $i < j$. Informally: $t \mapsto A^i u(t)$ is $C^n$ for every
$i \le j$.

The lift is recovered from the coordinates by the orthogonal projection onto the closed
submodule `LinearPMap.powGraph A j`. This projection is a left inverse of the inclusion, and it
makes the lift $C^n$. -/
theorem contDiffOnPowDomain_iff (hA : A.IsClosed) {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H}
    {s : Set ℝ} :
    A.ContDiffOnPowDomain n j u s ↔ ∃ w : Fin (j + 1) → ℝ → H, (∀ t ∈ s, w 0 t = u t) ∧
      (∀ i, ContDiffOn ℝ n (w i) s) ∧ ∀ t ∈ s, ∀ i : Fin j,
        ∃ h : w i.castSucc t ∈ A.domain, A ⟨w i.castSucc t, h⟩ = w i.succ t := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    exact ⟨fun i t => applyL A j i (v t), hv0, fun i => (applyL A j i).contDiff.comp_contDiffOn hv,
      fun t _ i => ⟨applyL_mem_domain (v t) i, apply_applyL (v t) i⟩⟩
  · rintro ⟨w, hw0, hw, hwA⟩
    have := hA.completeSpace_powDomain j
    let P := (A.powGraph j).orthogonalProjectionOnto
    let W : ℝ → PiLp 2 (fun _ : Fin (j + 1) => H) := fun t => toLp 2 fun i => w i t
    have hW : ContDiffOn ℝ n W s := (contDiffOn_piLp 2).2 fun i => hw i
    refine ⟨fun t => P (W t), fun t ht => ?_, P.contDiff.comp_contDiffOn hW⟩
    have hmem : W t ∈ A.powGraph j := fun i => hwA t ht i
    change ((P (W t) : A.PowDomain j) : PiLp 2 fun _ : Fin (j + 1) => H) 0 = u t
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_eq_self_iff.2 hmem]
    exact hw0 t ht

/-! ### The regularity ladder: the semigroup of the part of $A$ -/

/-- **The semigroup of the part is the restriction of the semigroup.** Let $H$ be complete and $A$
maximal monotone, and let $A_j$ be the part `A.powPart j` of $A$ in the Hilbert space $D(A^j)$.
For $x \in D(A^j)$, $t \ge 0$ and $i \le j$,
$$A^i \big(S_{A_j}(t) x\big) = S_A(t) A^i x.$$

Proof idea: both sides are continuous in $x$ and agree on the dense subspace $D(A^{j+1})$, where
$t \mapsto A^i S_{A_j}(t) x$ solves the problem in $H$ with the initial value $A^i x \in D(A)$.
This follows the proof of Theorem 7.5 of [brezis2011functional]. -/
theorem IsMaximalMonotone.applyL_semigroup_powPart (hA : A.IsMaximalMonotone) (j : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (x : A.PowDomain j) (i : Fin (j + 1)) :
    applyL A j i ((A.powPart j).semigroup t x) = A.semigroup t (applyL A j i x) := by
  have := hA.isClosed.completeSpace_powDomain j
  have hAj := hA.powPart j
  have hcont : ⇑((applyL A j i).comp ((A.powPart j).semigroup t)) =
      ⇑((A.semigroup t).comp (applyL A j i)) := by
    refine Continuous.ext_on (hA.dense_range_castL j) (by fun_prop) (by fun_prop) ?_
    rintro _ ⟨y, rfl⟩
    set x := castL A j y with hx
    have hxd : x ∈ (A.powPart j).domain := castL_mem_powPart_domain y
    have hsol1 : A.IsSolutionOn (applyL A j i x) (Ici 0)
        fun τ => applyL A j i ((A.powPart j).semigroup τ x) := by
      have hs := hAj.isSolutionOn_semigroup ⟨x, hxd⟩
      refine ⟨by rw [hs.apply_zero],
        fun τ hτ => applyL_mem_domain_of_mem_powPartDomain (hs.mem_domain τ hτ) i,
        fun τ hτ => ?_⟩
      have h1 := (applyL A j i).hasFDerivAt.comp_hasDerivWithinAt τ (hs.hasDerivWithinAt τ hτ)
      simpa [Function.comp_def, _root_.map_neg] using h1
    have hsol2 : A.IsSolutionOn (applyL A j i x) (Ici 0)
        fun τ => A.semigroup τ (applyL A j i x) :=
      hA.isSolutionOn_semigroup ⟨applyL A j i x, applyL_mem_domain_of_mem_powPartDomain hxd i⟩
    exact hA.isMonotone.eqOn_of_isSolutionOn hsol1 hsol2 ht
  exact congrFun hcont x

omit [CompleteSpace H] in
/-- For $j < m$ and $x \in D(A^m)$, the image of $x$ in $D(A^j)$ lies in the domain of the part
$A_j$ of $A$ in $D(A^j)$. This gives the initial values of the regularity ladder. -/
theorem castLE_mem_powPart_domain {j m : ℕ} (h : j < m) (x : A.PowDomain m) :
    castLE A h.le x ∈ (A.powPart j).domain := by
  rw [mem_powPart_domain_iff, applyL_castLE]
  exact applyL_mem_domain x ⟨j, h⟩

omit [CompleteSpace H] in
/-- For $j + 1 \le m$ and $x \in D(A^m)$, the part $A_j$ of $A$ in $D(A^j)$ maps the image of $x$ in
$D(A^j)$ to `shiftL A j` of the image of $x$ in $D(A^{j+1})$. In coordinates:
$A_j (x_0, \dots, x_j) = (x_1, \dots, x_{j+1})$. -/
theorem powPart_castLE {j m : ℕ} (h : j + 1 ≤ m) (x : A.PowDomain m) :
    A.powPart j ⟨castLE A (by omega) x, castLE_mem_powPart_domain (by omega) x⟩ =
      shiftL A j (castLE A h x) :=
  PowDomain.ext fun i => apply_applyL x ⟨i, by omega⟩

/-- **The regularity ladder behind Theorem 7.5.** Let $H$ be complete and $A$ maximal monotone. For
all $n, j, m \in \mathbb{N}$ with $j + n \le m$ and every $x \in D(A^m)$, the curve
$t \mapsto S_{A_j}(t) x$ in $D(A^j)$ is $C^n$ on $[0, \infty)$. Here $x$ is read in $D(A^j)$
through `LinearPMap.PowDomain.castLE`.

Proof idea: induction on $n$, for all $j$ at once. The derivative $-S_{A_j}(t) A_j x$ is the
shift of the solution one level up, which is $C^n$ by the induction hypothesis at $j + 1$. This
is the step "$\frac{d}{dt}(Au) = A \frac{du}{dt}$" of the proof of Theorem 7.5 of
[brezis2011functional]. -/
theorem IsMaximalMonotone.contDiffOn_semigroup_powPart (hA : A.IsMaximalMonotone) (n : ℕ) :
    ∀ (j m : ℕ) (h : j + n ≤ m) (x : A.PowDomain m),
      ContDiffOn ℝ n (fun t => (A.powPart j).semigroup t (castLE A (by omega) x)) (Ici 0) := by
  induction n with
  | zero =>
    intro j m _ x
    have := hA.isClosed.completeSpace_powDomain j
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hA.powPart j).continuousOn_semigroup_apply _
  | succ n ih =>
    intro j m h x
    have := hA.isClosed.completeSpace_powDomain j
    have hAj := hA.powPart j
    have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
        (fun t => (A.powPart j).semigroup t (castLE A (by omega) x))
        (-(shiftL A j ((A.powPart (j + 1)).semigroup t (castLE A (by omega) x)))) (Ici 0) t := by
      intro t ht
      have h1 := hAj.hasDerivWithinAt_semigroup_apply
        ⟨castLE A (by omega) x, castLE_mem_powPart_domain (by omega) x⟩ ht
      convert h1 using 2
      rw [powPart_castLE (by omega) x]
      refine PowDomain.ext fun i => ?_
      rw [applyL_shiftL, hA.applyL_semigroup_powPart (j + 1) ht,
        hA.applyL_semigroup_powPart j ht, applyL_shiftL]
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (hderiv t ht).differentiableWithinAt, fun h => by simp at h, ?_⟩
    have hih := ih (j + 1) m (by omega) x
    refine (((shiftL A j).contDiff.comp_contDiffOn hih).neg).congr fun t ht => ?_
    exact (hderiv t ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- **Theorem 7.5** of [brezis2011functional] (regularity). Let $H$ be complete, $A$ maximal
monotone, $x \in D(A^k)$ with $u_0 = x_0$, and $j \le k$. Then the solution $u(t) = S_A(t) u_0$
of the evolution problem is in $C^{k-j}([0, \infty); D(A^j))$.

The lift is $t \mapsto S_{A_j}(t) x$, which is $C^{k-j}$ by
`LinearPMap.IsMaximalMonotone.contDiffOn_semigroup_powPart`, and its coordinate $0$ is
$S_A(t) u_0$. The book states the theorem for $k \ge 2$; the cases $k = 0, 1$ are Theorem 7.4. -/
theorem IsMaximalMonotone.contDiffOnPowDomain_semigroup (hA : A.IsMaximalMonotone) {k : ℕ}
    (x : A.PowDomain k) {j : ℕ} (hj : j ≤ k) :
    A.ContDiffOnPowDomain (k - j : ℕ) j (fun t => A.semigroup t (applyL A k 0 x)) (Ici 0) := by
  refine ⟨fun t => (A.powPart j).semigroup t (castLE A hj x), fun t ht => ?_,
    hA.contDiffOn_semigroup_powPart (k - j) j k (by omega) x⟩
  rw [hA.applyL_semigroup_powPart j ht, applyL_castLE]
  rfl

end LinearPMap

/-! ### The self-adjoint case: the smoothing estimate for a bounded operator -/

section SelfAdjointExp

open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The smoothing estimate for a bounded self-adjoint monotone operator.** Let $H$ be a real
Hilbert space and $B : H \to H$ a bounded self-adjoint operator with
$\langle Bv, v \rangle \ge 0$ for all $v$. For $w \in H$ and $T > 0$,
$$\|B e^{-TB} w\| \le \frac{\|w\|}{T}.$$

Proof idea: with $u(t) = e^{-tB} w$, the function $\Phi(t) = \frac12 \|u\|^2 + t \langle Bu, u
\rangle + t^2 \|Bu\|^2$ has the derivative $\Phi' = -2t^2 \langle B(Bu), Bu \rangle \le 0$. So
$T^2 \|Bu(T)\|^2 \le \Phi(T) \le \Phi(0) = \frac12 \|w\|^2$. This is the chain (29)–(33) of the
proof of Theorem 7.7 of [brezis2011functional], with the integrations by parts replaced by one
derivative. It gives the sharper bound $\|w\| / (\sqrt2 T)$. -/
theorem norm_exp_neg_smul_apply_le_div (B : H →L[ℝ] H) (hB : IsSelfAdjoint B)
    (hB' : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) (w : H) {T : ℝ} (hT : 0 < T) :
    ‖B (exp ((-T) • B) w)‖ ≤ ‖w‖ / T := by
  have hsym : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ := fun x y => hB.isSymmetric x y
  set u : ℝ → H := fun t => exp ((-t) • B) w with hu
  have hu' : ∀ t, HasDerivAt u (-(B (u t))) t := fun t => hasDerivAt_exp_neg_smul_apply B w t
  have hBu' : ∀ t, HasDerivAt (fun t => B (u t)) (B (-(B (u t)))) t := fun t =>
    B.hasFDerivAt.comp_hasDerivAt t (hu' t)
  set Φ : ℝ → ℝ := fun t => (1 / 2) * ‖u t‖ ^ 2 + t * ⟪B (u t), u t⟫_ℝ + t ^ 2 * ‖B (u t)‖ ^ 2
    with hΦ
  have hΦ' : ∀ t, HasDerivAt Φ (-2 * t ^ 2 * ⟪B (B (u t)), B (u t)⟫_ℝ) t := fun t => by
    have e1 := (hu' t).norm_sq.const_mul (1 / 2 : ℝ)
    have e2 := (hasDerivAt_id t).mul (HasDerivAt.inner ℝ (hBu' t) (hu' t))
    have e3 := (hasDerivAt_pow 2 t).mul (hBu' t).norm_sq
    convert (e1.add e2).add e3 using 1
    · funext x
      simp only [hΦ, Pi.add_apply, Pi.mul_apply, id]
    · simp only [inner_neg_right, inner_neg_left, map_neg, real_inner_self_eq_norm_sq, id,
        Nat.cast_ofNat]
      rw [hsym (B (u t)) (u t), real_inner_self_eq_norm_sq,
        real_inner_comm (B (B (u t))) (B (u t)), real_inner_comm (u t) (B (u t))]
      ring
  have hΦa : AntitoneOn Φ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hΦ' t).continuousAt.continuousWithinAt)
      (fun t _ => (hΦ' t).differentiableAt.differentiableWithinAt) fun t _ => ?_
    rw [(hΦ' t).deriv]
    have := hB' (B (u t))
    nlinarith [sq_nonneg t]
  have h1 : Φ T ≤ Φ 0 := hΦa self_mem_Ici hT.le hT.le
  have h0 : Φ 0 = (1 / 2) * ‖w‖ ^ 2 := by simp [hΦ, hu]
  have h2 : T ^ 2 * ‖B (u T)‖ ^ 2 ≤ Φ T := by
    simp only [hΦ]
    have := hB' (u T)
    nlinarith [sq_nonneg ‖u T‖, hT.le]
  have h3 : (T * ‖B (u T)‖) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [mul_pow]
    nlinarith [h1, h2, h0, sq_nonneg ‖w‖]
  have h4 : T * ‖B (u T)‖ ≤ ‖w‖ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h3
  rw [le_div_iff₀ hT]
  linarith

end SelfAdjointExp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {A : H →ₗ.[ℝ] H}

open PowDomain

/-! ### The self-adjoint case: Theorem 7.7 -/

/-- **Step 1 of the proof of Theorem 7.7** of [brezis2011functional], for the approximations. Let
$H$ be complete, $A$ maximal monotone and symmetric, $c > 0$ and $T > 0$. For every $u_0 \in H$,
$$\|u_c'(T)\| = \|A_c e^{-TA_c} u_0\| \le \frac{\|u_0\|}{T}.$$
This is (33)–(34) of the book.

The proof applies `norm_exp_neg_smul_apply_le_div` to the self-adjoint monotone operator $A_c$. -/
theorem norm_yosida_expYosida_apply_le_div (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 < T) (u₀ : H) :
    ‖A.yosida c (A.expYosida c T u₀)‖ ≤ ‖u₀‖ / T :=
  norm_exp_neg_smul_apply_le_div _ (hA.isSelfAdjoint_yosida hs hc) (hA.inner_yosida_nonneg hc)
    u₀ hT

/-- **Estimate (27)** of the proof of Theorem 7.7 of [brezis2011functional], on the domain. Let $H$
be complete, $A$ maximal monotone and symmetric, $u_0 \in D(A)$ and $T > 0$. Then
$$\|S_A(T) A u_0\| \le \frac{\|u_0\|}{T}.$$
Since $S_A(T) A u_0 = A S_A(T) u_0$, this bounds $\|A S_A(T) u_0\|$.

It is the limit of the estimate for the approximations as $c \to 0^+$. -/
theorem norm_semigroup_apply_apply_le_div (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : A.domain) {T : ℝ} (hT : 0 < T) :
    ‖A.semigroup T (A u₀)‖ ≤ ‖(u₀ : H)‖ / T := by
  have h := (hA.tendstoUniformlyOn_deriv_expYosida u₀ (T := T)).tendsto_at
    (right_mem_Icc.2 hT.le)
  refine le_of_tendsto h.norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [← yosida_expYosida_comm]
  exact norm_yosida_expYosida_apply_le_div hA hs hc hT u₀

/-- **Step 2 of the proof of Theorem 7.7** of [brezis2011functional], the smoothing. Let $H$ be
complete and $A$ maximal monotone and symmetric. For every $u_0 \in H$ and $t > 0$,
$S_A(t) u_0 \in D(A)$ and
$$\|A S_A(t) u_0\| \le \frac{\|u_0\|}{t}.$$

Proof idea: approximate $u_0$ by $v_n \in D(A)$. Then $A S_A(t) v_n = S_A(t) A v_n$ is a Cauchy
sequence by (27), and the closed graph identifies the limit. The book uses $D(A^2)$ in place of
$D(A)$. -/
theorem semigroup_apply_mem_domain_of_isFormalAdjoint
    (hA : A.IsMaximalMonotone) (hs : A.IsFormalAdjoint A) (u₀ : H) {t : ℝ} (ht : 0 < t) :
    ∃ h : A.semigroup t u₀ ∈ A.domain, ‖A ⟨A.semigroup t u₀, h⟩‖ ≤ ‖u₀‖ / t := by
  have hcl : _root_.IsClosed (A.graph : Set (H × H)) := hA.isClosed
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.1 (hA.dense_domain u₀)
  -- the images `S(t) (A v_n)` form a Cauchy sequence
  have hcauchy : CauchySeq fun n => A.semigroup t (A ⟨v n, hv n⟩) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hvlim.cauchySeq (ε * t) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have := norm_semigroup_apply_apply_le_div hA hs (⟨v m, hv m⟩ - ⟨v n, hv n⟩) ht
    rw [map_sub, _root_.map_sub, Submodule.coe_sub, ← dist_eq_norm, ← dist_eq_norm,
      le_div_iff₀ ht] at this
    exact lt_of_mul_lt_mul_right (this.trans_lt (hN m hm n hn)) ht.le
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto (fun n => A.semigroup t (v n)) atTop (𝓝 (A.semigroup t u₀)) :=
    ((A.semigroup t).continuous.tendsto u₀).comp hvlim
  have hmem : (A.semigroup t u₀, f) ∈ A.graph := by
    refine hcl.mem_of_tendsto (hlim.prodMk_nhds hf) (Eventually.of_forall fun n => ?_)
    rw [← hA.semigroup_apply_apply ⟨v n, hv n⟩ ht.le]
    exact A.mem_graph ⟨A.semigroup t (v n), hA.semigroup_apply_mem_domain ⟨v n, hv n⟩ ht.le⟩
  rw [mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  change (y : H) = A.semigroup t u₀ at hy1
  change A y = f at hy2
  refine ⟨hy1 ▸ y.2, ?_⟩
  rw [show (⟨A.semigroup t u₀, hy1 ▸ y.2⟩ : A.domain) = y from Subtype.ext hy1.symm, hy2]
  refine le_of_tendsto_of_tendsto hf.norm (hvlim.norm.div_const t)
    (Eventually.of_forall fun n => ?_)
  exact norm_semigroup_apply_apply_le_div hA hs ⟨v n, hv n⟩ ht

/-- **Theorem 7.7** of [brezis2011functional], the equation for $t > 0$ and every initial value. Let
$H$ be complete and $A$ maximal monotone and symmetric. For $u_0 \in H$ and $t > 0$, the curve
$t \mapsto S_A(t) u_0$ has the derivative $-A S_A(t) u_0$ at $t$.

Proof idea: on $[\delta, \infty)$ with $0 < \delta < t$, $S_A(\tau) u_0 = S_A(\tau - \delta)
S_A(\delta) u_0$ with $S_A(\delta) u_0 \in D(A)$, and Theorem 7.4 gives the derivative of the
right side. -/
theorem hasDerivAt_semigroup_apply_of_isFormalAdjoint (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : H) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => A.semigroup t u₀)
      (-A ⟨A.semigroup t u₀, (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht).fst⟩)
      t := by
  set δ := t / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδt : δ < t := by linarith
  set w : A.domain := ⟨A.semigroup δ u₀,
    (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hδ0).fst⟩ with hw
  have hEq : ∀ τ ∈ Ici δ, A.semigroup τ u₀ = A.semigroup (τ - δ) w := fun τ hτ => by
    have hτ' : 0 ≤ τ - δ := by simp only [mem_Ici] at hτ; linarith
    have := congrArg (fun T : H →L[ℝ] H => T u₀) (hA.semigroup_add hτ' hδ0.le)
    simpa using this
  have h1 : HasDerivWithinAt (fun τ => A.semigroup (τ - δ) w) (-(A.semigroup (t - δ) (A w)))
      (Ici δ) t := by
    have := (hA.hasDerivWithinAt_semigroup_apply w (by linarith : 0 ≤ t - δ)).scomp t
      ((hasDerivWithinAt_id t (Ici δ)).sub_const δ)
      (fun τ hτ => by simp only [mem_Ici, id] at hτ ⊢; linarith)
    simpa [Function.comp_def] using this
  have h2 : HasDerivWithinAt (fun τ => A.semigroup τ u₀) (-(A.semigroup (t - δ) (A w))) (Ici δ) t :=
    h1.congr hEq (hEq t hδt.le)
  have h3 := h2.hasDerivAt (Ici_mem_nhds hδt)
  convert h3 using 2
  rw [← hA.semigroup_apply_apply w (by linarith : 0 ≤ t - δ)]
  congr 1
  exact Subtype.ext (hEq t hδt.le)

/-- **Theorem 7.7** of [brezis2011functional], existence and regularity. Let $H$ be complete and $A$
maximal monotone and symmetric. For every $u_0 \in H$, the curve $u(t) = S_A(t) u_0$ solves
$u' + Au = 0$ on $(0, \infty)$ with $u(0) = u_0$, is continuous on $[0, \infty)$ and $C^1$ on
$(0, \infty)$, and satisfies $\|u(t)\| \le \|u_0\|$ for $t \ge 0$. -/
theorem isSolutionOn_semigroup_Ioi (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : H) :
    A.IsSolutionOn u₀ (Ioi 0) (fun t => A.semigroup t u₀) ∧
      ContinuousOn (fun t => A.semigroup t u₀) (Ici 0) ∧
      ContDiffOn ℝ 1 (fun t => A.semigroup t u₀) (Ioi 0) ∧
      ∀ t, 0 ≤ t → ‖A.semigroup t u₀‖ ≤ ‖u₀‖ := by
  refine ⟨⟨by simp [hA.semigroup_zero],
    fun t ht => (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht).fst,
    fun t ht => (hasDerivAt_semigroup_apply_of_isFormalAdjoint hA hs u₀ ht).hasDerivWithinAt⟩,
    hA.continuousOn_semigroup_apply u₀, ?_, fun t ht => hA.norm_semigroup_apply_le ht u₀⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht => (hasDerivAt_semigroup_apply_of_isFormalAdjoint hA hs u₀
    ht).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  -- the derivative is continuous on `(0, ∞)`: on each `(δ, ∞)` it is `τ ↦ -S(τ - δ) (A (S(δ) u₀))`
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  set δ := t / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδt : δ < t := by linarith
  set w : A.domain := ⟨A.semigroup δ u₀,
    (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hδ0).fst⟩ with hw
  have hEq : ∀ τ ∈ Ioi δ, deriv (fun t => A.semigroup t u₀) τ =
      -(A.semigroup (τ - δ) (A w)) := fun τ hτ => by
    have hτ' : (0 : ℝ) < τ := by simp only [mem_Ioi] at hτ; linarith
    have hτ'' : (0 : ℝ) ≤ τ - δ := by simp only [mem_Ioi] at hτ; linarith
    rw [(hasDerivAt_semigroup_apply_of_isFormalAdjoint hA hs u₀ hτ').deriv,
      ← hA.semigroup_apply_apply w hτ'']
    have := congrArg (fun T : H →L[ℝ] H => T u₀) (hA.semigroup_add hτ'' hδ0.le)
    simp only [ContinuousLinearMap.comp_apply, sub_add_cancel] at this
    congr 1
    exact congrArg (fun z : A.domain => A z) (Subtype.ext this)
  have hcont : ContinuousOn (fun τ => -(A.semigroup (τ - δ) (A w))) (Ioi δ) := by
    refine ((hA.continuousOn_semigroup_apply (A w)).comp (continuousOn_id.sub continuousOn_const)
      fun τ hτ => ?_).neg
    simp only [mem_Ioi] at hτ
    simp only [mem_Ici, Pi.sub_apply, id]
    linarith
  exact ((hcont.congr hEq) t hδt).mono_of_mem_nhdsWithin (nhdsWithin_le_nhds (Ioi_mem_nhds hδt))

/-- **The smoothing at every order.** Let $H$ be complete and $A$ maximal monotone and symmetric.
For every $u_0 \in H$, $l \in \mathbb{N}$ and $\varepsilon > 0$,
$S_A(\varepsilon) u_0 \in D(A^l)$: there is $x \in D(A^l)$ with $x_0 = S_A(\varepsilon) u_0$.

Proof idea: induction on $l$, applying Step 2 of the proof of Theorem 7.7 to the part
`A.powPart l` in the Hilbert space $D(A^l)$ and the initial value $S_A(\varepsilon / 2) u_0$.
This is (26) of the proof of Theorem 7.7 of [brezis2011functional]. -/
theorem exists_powDomain_semigroup_apply_of_isFormalAdjoint
    (hA : A.IsMaximalMonotone) (hs : A.IsFormalAdjoint A) (u₀ : H) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : A.PowDomain l, applyL A l 0 x = A.semigroup ε u₀ := by
  induction l generalizing u₀ ε with
  | zero => exact ⟨PowDomain.mk A (fun _ => A.semigroup ε u₀) (fun i => i.elim0), rfl⟩
  | succ l ih =>
    have := hA.isClosed.completeSpace_powDomain l
    obtain ⟨y, hy⟩ := ih u₀ (half_pos hε)
    have hAl := hA.powPart l
    have hsl := hs.powPart l
    obtain ⟨hmem, -⟩ := semigroup_apply_mem_domain_of_isFormalAdjoint hAl hsl y (half_pos hε)
    refine ⟨snoc ((A.powPart l).semigroup (ε / 2) y) (mem_powPart_domain_iff.1 hmem), ?_⟩
    rw [show (0 : Fin (l + 2)) = (0 : Fin (l + 1)).castSucc from rfl, applyL_snoc_castSucc,
      hA.applyL_semigroup_powPart l (half_pos hε).le, hy, ← ContinuousLinearMap.comp_apply,
      ← hA.semigroup_add (half_pos hε).le (half_pos hε).le, add_halves]

/-- **Theorem 7.7 (26)** of [brezis2011functional]. Let $H$ be complete and $A$ maximal monotone and
symmetric. For every $u_0 \in H$, the curve $u(t) = S_A(t) u_0$ is in $C^k((0, \infty); D(A^l))$
for all $k, l \in \mathbb{N}$.

The lift is the unique element of $D(A^l)$ over $S_A(t) u_0$. Near $t > 0$ it is the lift of
Theorem 7.5 for the initial value $S_A(t/2) u_0 \in D(A^{l+k})$, shifted in time. -/
theorem contDiffOnPowDomain_semigroup_Ioi (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : H) (k l : ℕ) :
    A.ContDiffOnPowDomain k l (fun t => A.semigroup t u₀) (Ioi 0) := by
  have hex : ∀ t : ℝ, 0 < t → ∃ x : A.PowDomain l, applyL A l 0 x = A.semigroup t u₀ :=
    fun t ht => exists_powDomain_semigroup_apply_of_isFormalAdjoint hA hs u₀ l ht
  choose! v hv using hex
  refine ⟨v, fun t ht => hv t ht, fun t ht => ?_⟩
  have ht' : (0 : ℝ) < t := ht
  set ε := t / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεt : ε < t := by linarith
  obtain ⟨x, hx⟩ := exists_powDomain_semigroup_apply_of_isFormalAdjoint hA hs u₀ (l + k) hε0
  have h75 := hA.contDiffOnPowDomain_semigroup x (j := l) (by omega)
  rw [Nat.add_sub_cancel_left] at h75
  obtain ⟨v', hv'0, hv'⟩ := h75
  have hw : ContDiffOn ℝ k (fun τ => v' (τ - ε)) (Ici ε) :=
    hv'.comp (contDiffOn_id.sub contDiffOn_const) fun τ hτ => by
      simp only [mem_Ici] at hτ ⊢
      linarith
  have hagree : EqOn v (fun τ => v' (τ - ε)) (Ici ε) := fun τ hτ => by
    have hτ' : 0 ≤ τ - ε := by simp only [mem_Ici] at hτ; linarith
    apply applyL_zero_injective
    rw [hv τ (by linarith), hv'0 (τ - ε) hτ']
    simp only [hx]
    rw [← ContinuousLinearMap.comp_apply, ← hA.semigroup_add hτ' hε0.le, sub_add_cancel]
  have : ContDiffAt ℝ k v t :=
    (hw.contDiffAt (Ici_mem_nhds hεt)).congr_of_eventuallyEq
      (eventuallyEq_of_mem (Ici_mem_nhds hεt) hagree)
  exact this.contDiffWithinAt

/-- **Theorem 7.7** of [brezis2011functional]. Let $H$ be a real Hilbert space and $A$ a
self-adjoint maximal monotone operator. For every $u_0 \in H$, the evolution problem
$u' + Au = 0$ on $(0, \infty)$, $u(0) = u_0$ has a solution $u \in C([0, \infty); H) \cap
C^1((0, \infty); H)$ with
$$\|u(t)\| \le \|u_0\| \ (t \ge 0), \qquad \|u'(t)\| = \|Au(t)\| \le \frac{\|u_0\|}{t} \ (t >
  0),$$
and $u \in C^k((0, \infty); D(A^l))$ for all $k, l \in \mathbb{N}$.

Self-adjointness is `IsSelfAdjoint A` for the partial linear map $A$. The solution is
$t \mapsto S_A(t) u_0$. Uniqueness among the solutions on $(0, \infty)$ that are continuous on
$[0, \infty)$ is `LinearPMap.IsMonotone.eqOn_of_isSolutionOn_Ioi`. -/
theorem exists_isSolutionOn_Ioi_of_isSelfAdjoint (hA : A.IsMaximalMonotone)
    (hsa : IsSelfAdjoint A) (u₀ : H) :
    ∃ u : ℝ → H, ∃ hu : A.IsSolutionOn u₀ (Ioi 0) u, ContinuousOn u (Ici 0) ∧
      ContDiffOn ℝ 1 u (Ioi 0) ∧ (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖) ∧
      (∀ t (ht : 0 < t), ‖A ⟨u t, hu.mem_domain t ht⟩‖ ≤ ‖u₀‖ / t) ∧
      ∀ k l : ℕ, A.ContDiffOnPowDomain k l u (Ioi 0) := by
  have hs := hsa.isFormalAdjoint_self
  obtain ⟨h1, h2, h3, h4⟩ := isSolutionOn_semigroup_Ioi hA hs u₀
  exact ⟨fun t => A.semigroup t u₀, h1, h2, h3, h4,
    fun t ht => (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht).snd,
    fun k l => contDiffOnPowDomain_semigroup_Ioi hA hs u₀ k l⟩

section Shift

variable {B : H →ₗ.[ℝ] H}

/-! ### The regularity classes under the shift $A \mapsto A + cI$ -/

omit [CompleteSpace H] in
/-- **The class $C^n(s; D(A^j))$ is unchanged by a shift of the operator.** Let $B = A + cI$, that
is, `B.IsAddSmulId A c`. A curve of class $C^n(s; D(B^j))$ is of class $C^n(s; D(A^j))$.

The lift is transported by `LinearPMap.IsAddSmulId.transport`. -/
theorem IsAddSmulId.contDiffOnPowDomain {c : ℝ} (h : B.IsAddSmulId A c) {n : WithTop ℕ∞}
    {j : ℕ} {u : ℝ → H} {s : Set ℝ} (hu : B.ContDiffOnPowDomain n j u s) :
    A.ContDiffOnPowDomain n j u s :=
  let ⟨v, hv0, hv⟩ := hu
  ⟨fun t => h.transport j (v t), fun t ht => by rw [h.applyL_zero_transport, hv0 t ht],
    (h.transport j).contDiff.comp_contDiffOn hv⟩

omit [CompleteSpace H] in
/-- Let $f : \mathbb{R} \to \mathbb{R}$ be $C^n$ on $s$. If $u$ is in $C^n(s; D(A^j))$, then
$t \mapsto f(t) u(t)$ is in $C^n(s; D(A^j))$. -/
theorem ContDiffOnPowDomain.smul {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f s) (hu : A.ContDiffOnPowDomain n j u s) :
    A.ContDiffOnPowDomain n j (fun t => f t • u t) s :=
  let ⟨v, hv0, hv⟩ := hu
  ⟨fun t => f t • v t, fun t ht => by rw [_root_.map_smul, hv0 t ht], hf.smul hv⟩

/-- **Theorem 7.5 for the shifted semigroup**: Theorem 7.5 with Remark 6 of Chapter 7 of
[brezis2011functional]. Let $H$ be complete, let $B = A + cI$ be maximal monotone, let
$x \in D(A^k)$ with $u_0 = x_0$, and let $j \le k$. Then the curve
$t \mapsto e^{ct} S_B(t) u_0$, which is the solution of $u' + Au = 0$, is in
$C^{k-j}([0, \infty); D(A^j))$.

Proof idea: the initial value is transported to $D(B^k)$. Theorem 7.5 for $B$ gives the class
$C^{k-j}([0, \infty); D(B^j))$, which is $C^{k-j}([0, \infty); D(A^j))$ by
`LinearPMap.IsAddSmulId.contDiffOnPowDomain`, and the factor $e^{ct}$ is smooth. -/
theorem IsMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup {c : ℝ}
    (hB : B.IsMaximalMonotone) (h : B.IsAddSmulId A c) {k : ℕ} (x : A.PowDomain k) {j : ℕ}
    (hj : j ≤ k) :
    A.ContDiffOnPowDomain (k - j : ℕ) j
      (fun t => Real.exp (c * t) • B.semigroup t (applyL A k 0 x)) (Ici 0) := by
  have h1 := hB.contDiffOnPowDomain_semigroup (h.symm.transport k x) hj
  rw [h.symm.applyL_zero_transport] at h1
  exact (h.contDiffOnPowDomain h1).smul
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn

end Shift

end LinearPMap

/-! ### Lifts of the semigroup into $D(A^\ell)$, and the derivatives $(-A)^j S_A(t) u_0$ -/

namespace LinearPMap

open MeasureTheory PowDomain
open scoped ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {A : H →ₗ.[ℝ] H}

variable (A) in
/-- **The lift of $S_A(t) u_0$ into $D(A^\ell)$**: the element $x$ of $D(A^\ell)$ with
$x_0 = S_A(t) u_0$ if there is one, and $0$ otherwise.

Such an element is unique (`LinearPMap.PowDomain.applyL_zero_injective`). For a symmetric
maximal monotone $A$ and $t > 0$ it exists for every $u_0$
(`LinearPMap.exists_powDomain_semigroup_apply_of_isFormalAdjoint`), and its coordinates are the
iterates $A^j S_A(t) u_0$. -/
def semigroupLift (u₀ : H) (ℓ : ℕ) (t : ℝ) : A.PowDomain ℓ :=
  open Classical in
  if h : ∃ x : A.PowDomain ℓ, applyL A ℓ 0 x = A.semigroup t u₀ then h.choose else 0

variable (hA : A.IsMaximalMonotone) (hs : A.IsFormalAdjoint A) {u₀ : H} {ℓ : ℕ}
include hA hs

/-- Let $H$ be complete and $A$ maximal monotone and symmetric. For $t > 0$, the coordinate $0$ of
the lift of $S_A(t) u_0$ into $D(A^\ell)$ is $S_A(t) u_0$. -/
theorem applyL_zero_semigroupLift {t : ℝ} (ht : 0 < t) :
    applyL A ℓ 0 (semigroupLift A u₀ ℓ t) = A.semigroup t u₀ := by
  have h := exists_powDomain_semigroup_apply_of_isFormalAdjoint hA hs u₀ ℓ ht
  unfold semigroupLift
  rw [dite_eq_left h]
  exact h.choose_spec

/-- **The lift is unique.** Let $H$ be complete and $A$ maximal monotone and symmetric, and let
$t > 0$. Every $x \in D(A^\ell)$ with $x_0 = S_A(t) u_0$ is the lift
`LinearPMap.semigroupLift A u₀ ℓ t`. -/
theorem eq_semigroupLift {t : ℝ} (ht : 0 < t) {x : A.PowDomain ℓ}
    (hx : applyL A ℓ 0 x = A.semigroup t u₀) : x = semigroupLift A u₀ ℓ t :=
  applyL_zero_injective (hx.trans (applyL_zero_semigroupLift hA hs ht).symm)

/-- **The lift is the semigroup of the part.** Let $H$ be complete and $A$ maximal monotone and
symmetric, and let $A_\ell$ be the part of $A$ in $D(A^\ell)$. For $0 < \delta \le t$, the lift
of $S_A(t) u_0$ is $S_{A_\ell}(t - \delta)$ applied to the lift of $S_A(\delta) u_0$. -/
theorem semigroupLift_eq_semigroup_powPart {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    semigroupLift A u₀ ℓ t = (A.powPart ℓ).semigroup (t - δ) (semigroupLift A u₀ ℓ δ) := by
  refine (eq_semigroupLift hA hs (hδ.trans_le hδt) ?_).symm
  rw [hA.applyL_semigroup_powPart ℓ (by linarith) _ 0, applyL_zero_semigroupLift hA hs hδ,
    ← ContinuousLinearMap.comp_apply, ← hA.semigroup_add (by linarith) hδ.le, sub_add_cancel]

/-- **The semigroup transports the coordinates of the lift.** Let $H$ be complete and $A$ maximal
monotone and symmetric. For $0 < \delta \le t$ and every $i \le \ell$,
$$A^i S_A(t) u_0 = S_A(t - \delta) A^i S_A(\delta) u_0.$$
-/
theorem applyL_semigroupLift_eq {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (i : Fin (ℓ + 1)) :
    applyL A ℓ i (semigroupLift A u₀ ℓ t)
      = A.semigroup (t - δ) (applyL A ℓ i (semigroupLift A u₀ ℓ δ)) := by
  rw [semigroupLift_eq_semigroup_powPart hA hs hδ hδt, hA.applyL_semigroup_powPart ℓ (by linarith)]

/-- **The equation for the iterates.** Let $H$ be complete and $A$ maximal monotone and symmetric.
For $t > 0$ and $j < \ell$, the curve $\tau \mapsto A^j S_A(\tau) u_0$ has the derivative
$-A^{j+1} S_A(t) u_0$ at $t$.

Proof idea: near $t$, with $\delta = t/2$, the curve is $\tau \mapsto S_A(\tau - \delta) w_j$
with $w_j = A^j S_A(\delta) u_0 \in D(A)$. Its derivative is $-S_A(\tau - \delta) A w_j =
-S_A(\tau - \delta) w_{j+1}$ by Step 5 of the proof of Theorem 7.4. -/
theorem hasDerivAt_applyL_semigroupLift {t : ℝ} (ht : 0 < t) (j : Fin ℓ) :
    HasDerivAt (fun τ ↦ applyL A ℓ j.castSucc (semigroupLift A u₀ ℓ τ))
      (-(applyL A ℓ j.succ (semigroupLift A u₀ ℓ t))) t := by
  set δ := t / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδt : δ < t := by linarith
  set w : A.PowDomain ℓ := semigroupLift A u₀ ℓ δ with hw
  set wj : A.domain := ⟨applyL A ℓ j.castSucc w, applyL_mem_domain w j⟩ with hwj
  have hEq : ∀ τ ∈ Ioi δ, applyL A ℓ j.castSucc (semigroupLift A u₀ ℓ τ)
      = A.semigroup (τ - δ) wj := fun τ hτ ↦
    applyL_semigroupLift_eq hA hs hδ0 (le_of_lt hτ) j.castSucc
  have h1 : HasDerivAt (fun s ↦ A.semigroup s wj) (-(A.semigroup (t - δ) (A wj))) (t - δ) :=
    (hA.hasDerivWithinAt_semigroup_apply wj (by linarith)).hasDerivAt
      (Ici_mem_nhds (by linarith))
  have h2 : HasDerivAt (fun τ ↦ A.semigroup (τ - δ) wj) (-(A.semigroup (t - δ) (A wj))) t :=
    h1.comp_sub_const t δ
  have h3 : A wj = applyL A ℓ j.succ w := apply_applyL w j
  rw [h3, ← applyL_semigroupLift_eq hA hs hδ0 hδt.le j.succ] at h2
  exact h2.congr_of_eventuallyEq (eventually_of_mem (Ioi_mem_nhds hδt) hEq)

/-- Let $H$ be complete and $A$ maximal monotone and symmetric, and let $s, \tau > 0$. The shift of
the lift of $S_A(s + \tau) u_0$ into $D(A^{j+2})$ is the lift of $S_A(s) w$ into $D(A^{j+1})$,
where $w = A S_A(\tau) u_0$. In coordinates: $A^{i+1} S_A(s + \tau) u_0 = A^i S_A(s) A S_A(\tau)
u_0$. -/
theorem shiftL_semigroupLift {s τ : ℝ} (hs' : 0 < s) (hτ : 0 < τ) (j : ℕ) :
    shiftL A (j + 1) (semigroupLift A u₀ (j + 2) (s + τ))
      = semigroupLift A (A ⟨A.semigroup τ u₀,
          (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hτ).fst⟩) (j + 1) s := by
  refine eq_semigroupLift hA hs hs' ?_
  rw [applyL_zero_shiftL]
  set w : A.domain := ⟨A.semigroup τ u₀,
    (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hτ).fst⟩ with hw
  have h2 : applyL A (j + 2) 0 (semigroupLift A u₀ (j + 2) (s + τ)) = A.semigroup s w := by
    rw [applyL_zero_semigroupLift hA hs (by linarith), hA.semigroup_add hs'.le hτ.le]
    rfl
  have h3 := hA.semigroup_apply_apply w hs'.le
  rw [← h3]
  exact congrArg (fun z : A.domain ↦ A z) (Subtype.ext h2)

/-- **The parabolic bound on the top iterate.** Let $H$ be complete and $A$ maximal monotone and
symmetric. For every $j \in \mathbb{N}$, $u_0 \in H$ and $t > 0$,
$$\|A^{j+1} S_A(t) u_0\| \le \Big(\frac{j + 1}{t}\Big)^{j+1} \|u_0\|.$$

Proof idea: induction on $j$, with the subdivision $t = s + \tau$, $\tau = t / (j + 2)$. Then
$A^{j+2} S_A(t) u_0 = A^{j+1} S_A(s) A S_A(\tau) u_0$, with
$\|A S_A(\tau) u_0\| \le \|u_0\| / \tau$ by Theorem 7.7. -/
theorem norm_applyL_last_semigroupLift_le (j : ℕ) :
    ∀ (u₀ : H) {t : ℝ}, 0 < t →
      ‖applyL A (j + 1) (Fin.last (j + 1)) (semigroupLift A u₀ (j + 1) t)‖
        ≤ ((j + 1 : ℝ) / t) ^ (j + 1) * ‖u₀‖ := by
  induction j with
  | zero =>
    intro u₀ t ht
    obtain ⟨hmem, hbound⟩ := semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht
    have h3 : applyL A 1 (Fin.castSucc 0) (semigroupLift A u₀ 1 t) = A.semigroup t u₀ :=
      applyL_zero_semigroupLift hA hs ht
    have h1 : applyL A 1 (Fin.last 1) (semigroupLift A u₀ 1 t) = A ⟨A.semigroup t u₀, hmem⟩ := by
      change applyL A 1 (Fin.succ 0) (semigroupLift A u₀ 1 t) = _
      rw [← apply_applyL (semigroupLift A u₀ 1 t) 0]
      exact congrArg (fun z : A.domain ↦ A z) (Subtype.ext h3)
    rw [h1]
    refine hbound.trans (le_of_eq ?_)
    rw [Nat.cast_zero, zero_add, pow_one, div_mul_eq_mul_div, one_mul]
  | succ j ih =>
    intro u₀ t ht
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = t / (j + 2) := ⟨_, rfl⟩
    obtain ⟨s, hs'⟩ : ∃ s : ℝ, s = t - τ := ⟨_, rfl⟩
    have hτ0 : 0 < τ := by rw [hτ]; positivity
    have hs0 : 0 < s := by
      rw [hs', hτ, sub_pos, div_lt_iff₀ (by positivity)]
      nlinarith
    have hst : t = s + τ := by rw [hs']; ring
    obtain ⟨hmem, hw'⟩ := semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hτ0
    have key : applyL A (j + 2) (Fin.last (j + 2)) (semigroupLift A u₀ (j + 2) t)
        = applyL A (j + 1) (Fin.last (j + 1))
          (semigroupLift A (A ⟨A.semigroup τ u₀, hmem⟩) (j + 1) s) := by
      rw [hst, ← shiftL_semigroupLift hA hs hs0 hτ0 j, applyL_shiftL]
      rfl
    rw [key]
    refine (ih _ hs0).trans ?_
    have hs1 : (j + 1 : ℝ) / s = (j + 2 : ℝ) / t := by
      rw [div_eq_div_iff hs0.ne' ht.ne', hs', hτ]
      field_simp
      ring
    have hτ1 : ‖u₀‖ / τ = (j + 2 : ℝ) / t * ‖u₀‖ := by
      rw [hτ, div_div_eq_mul_div]
      ring
    calc ((j + 1 : ℝ) / s) ^ (j + 1) * ‖A ⟨A.semigroup τ u₀, hmem⟩‖
        ≤ ((j + 1 : ℝ) / s) ^ (j + 1) * (‖u₀‖ / τ) :=
          mul_le_mul_of_nonneg_left hw' (by positivity)
      _ = ((((j + 1 : ℕ) : ℝ) + 1) / t) ^ (j + 1 + 1) * ‖u₀‖ := by
          rw [hs1, hτ1]
          push_cast
          ring

/-- Let $H$ be complete and $A$ maximal monotone and symmetric, $j \le \ell$ and $t > 0$. The image
in $D(A^j)$ of the lift of $S_A(t) u_0$ into $D(A^\ell)$ is the lift into $D(A^j)$. -/
theorem castLE_semigroupLift {j : ℕ} (h : j ≤ ℓ) {t : ℝ} (ht : 0 < t) :
    castLE A h (semigroupLift A u₀ ℓ t) = semigroupLift A u₀ j t :=
  eq_semigroupLift hA hs ht (by rw [applyL_castLE]; exact applyL_zero_semigroupLift hA hs ht)

/-- **The parabolic bound at every order**, the estimate (27) of Theorem 7.7 of
[brezis2011functional] iterated. Let $H$ be complete and $A$ maximal monotone and symmetric. For
$t > 0$, every $u_0 \in H$ and every $j \le \ell$,
$$\|A^j S_A(t) u_0\| \le \Big(\frac{j}{t}\Big)^j \|u_0\|.$$
For $j = 0$ the factor $(0/t)^0$ is $1$. -/
theorem norm_applyL_semigroupLift_le {t : ℝ} (ht : 0 < t) (j : Fin (ℓ + 1)) :
    ‖applyL A ℓ j (semigroupLift A u₀ ℓ t)‖ ≤ ((j : ℕ) / t : ℝ) ^ (j : ℕ) * ‖u₀‖ := by
  have hcast : applyL A ℓ j (semigroupLift A u₀ ℓ t)
      = applyL A j (Fin.last j) (semigroupLift A u₀ j t) := by
    rw [← castLE_semigroupLift hA hs (Nat.lt_succ_iff.1 j.2) ht, applyL_castLE]
    rfl
  rw [hcast]
  generalize (j : ℕ) = k
  rcases k with _ | k
  · rw [Nat.cast_zero, pow_zero, one_mul]
    exact (hA.norm_semigroup_apply_le ht.le u₀).trans_eq' (by
      rw [show (Fin.last 0 : Fin 1) = 0 from rfl, applyL_zero_semigroupLift hA hs ht])
  · have := norm_applyL_last_semigroupLift_le hA hs k u₀ ht
    push_cast at this ⊢
    exact this

/-- **The lift is $C^\infty$ on $(0, \infty)$.** Let $H$ be complete and $A$ maximal monotone and
symmetric. For every $u_0 \in H$ and $\ell \in \mathbb{N}$, the curve $t \mapsto$ (the lift of
$S_A(t) u_0$ into $D(A^\ell)$) is $C^\infty$ on $(0, \infty)$.

The lifts of Theorem 7.7 at every order agree with `LinearPMap.semigroupLift` by uniqueness, so
the latter is $C^k$ on $(0, \infty)$ for every $k$. -/
theorem contDiffOn_semigroupLift (u₀ : H) (ℓ : ℕ) :
    ContDiffOn ℝ ∞ (semigroupLift A u₀ ℓ) (Ioi 0) := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  obtain ⟨v, hv0, hv⟩ := contDiffOnPowDomain_semigroup_Ioi hA hs u₀ k ℓ
  exact hv.congr fun t ht ↦ (eq_semigroupLift hA hs ht (hv0 t ht)).symm

omit hA hs [CompleteSpace H] in
/-- The graph norm on $D(A)$: $\|x\|^2 = \|x_0\|^2 + \|x_1\|^2$ for $x \in D(A)$, that is, for
`x : A.PowDomain 1`. -/
theorem norm_sq_powDomain_one (x : A.PowDomain 1) :
    ‖x‖ ^ 2 = ‖applyL A 1 0 x‖ ^ 2 + ‖applyL A 1 1 x‖ ^ 2 := by
  rw [PowDomain.norm_sq_eq, Fin.sum_univ_two]

omit hA hs [CompleteSpace H] in
/-- For $u_0 \in D(A)$ there is $x$ in $D(A)$ with the graph norm (`A.PowDomain 1`) with $x_0 = u_0$
and $x_1 = A u_0$. -/
theorem exists_powDomain_one (u₀ : A.domain) :
    ∃ x : A.PowDomain 1, applyL A 1 0 x = u₀ ∧ applyL A 1 1 x = A u₀ := by
  refine ⟨PowDomain.mk A ![(u₀ : H), A u₀] fun i ↦ ?_, rfl, rfl⟩
  rw [Fin.fin_one_eq_zero i]
  exact ⟨u₀.2, rfl⟩

omit hA hs [CompleteSpace H] in
/-- The zero curve solves $u' + Au = 0$ with the initial value $0$, on every set of times. -/
theorem isSolutionOn_zero (s : Set ℝ) : A.IsSolutionOn 0 s (fun _ ↦ (0 : H)) where
  apply_zero := rfl
  mem_domain _ _ := Submodule.zero_mem _
  hasDerivWithinAt t _ := by
    have : -A ⟨(0 : H), Submodule.zero_mem _⟩ = 0 := by
      rw [show (⟨(0 : H), Submodule.zero_mem _⟩ : A.domain) = 0 from rfl, map_zero, neg_zero]
    rw [this]
    exact hasDerivWithinAt_const t s (0 : H)

omit hA hs [CompleteSpace H] in
/-- **The abstract energy identity (6)** of the proof of Theorem 10.1 of [brezis2011functional]. Let
$A$ be monotone, and let $u$ solve $u' + Au = 0$ on $(0, \infty)$ with $u(0) = u_0$, with $u \in
C([0, \infty); H) \cap C^1((0, \infty); H)$. Let $g(t) = \langle Au(t), u(t) \rangle$ for
$t > 0$. Then for every $T > 0$, $g$ is integrable on $(0, T]$ and
$$\frac12 \|u(T)\|^2 + \int_0^T g(t) \, dt = \frac12 \|u_0\|^2.$$

Proof idea: $\varphi(t) = \frac12 \|u(t)\|^2$ is $C^1$ on $(0, \infty)$ with
$\varphi' = \langle u, u' \rangle = -g \le 0$. Integrability of $g$ on $(0, T]$ follows from
$\int_\varepsilon^T g = \varphi(\varepsilon) - \varphi(T) \le \frac12 \|u_0\|^2$, and the
identity from the fundamental theorem of calculus with the one-sided limits
$\varphi(\varepsilon) \to \varphi(0)$. -/
theorem IsSolutionOn.energy_Ioi (hA : A.IsMonotone) {u : ℝ → H}
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hc : ContinuousOn u (Ici 0))
    (hd : ContDiffOn ℝ 1 u (Ioi 0)) {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t), g t = ⟪A ⟨u t, hu.mem_domain t ht⟩, u t⟫_ℝ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t = 1 / 2 * ‖u₀‖ ^ 2 := by
  have hder : ∀ t (ht : 0 < t), HasDerivAt u (-(A ⟨u t, hu.mem_domain t ht⟩)) t := fun t ht ↦
    (hu.hasDerivWithinAt t ht).hasDerivAt (Ioi_mem_nhds ht)
  have hφ : ∀ t, 0 < t → HasDerivAt (fun t ↦ 1 / 2 * ‖u t‖ ^ 2) (-(g t)) t := by
    intro t ht
    have := (hder t ht).norm_sq.const_mul (1 / 2)
    convert this using 1
    rw [hg t ht, inner_neg_right, real_inner_comm]
    ring
  have hg0 : ∀ t, 0 < t → 0 ≤ g t := fun t ht ↦ by
    rw [hg t ht]
    simpa using hA ⟨u t, hu.mem_domain t ht⟩
  have hgc : ContinuousOn g (Ioi 0) := by
    have h1 : ContinuousOn (fun t ↦ ⟪-deriv u t, u t⟫_ℝ) (Ioi 0) :=
      (hd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).neg.inner
        (hd.continuousOn.mono le_rfl)
    refine h1.congr fun t ht ↦ ?_
    change g t = ⟪-deriv u t, u t⟫_ℝ
    rw [hg t ht, (hder t ht).deriv, neg_neg]
  have hL : Tendsto (fun t ↦ 1 / 2 * ‖u t‖ ^ 2) (𝓝[>] 0) (𝓝 (1 / 2 * ‖u₀‖ ^ 2)) := by
    rw [← hu.apply_zero]
    exact (continuousWithinAt_const.mul ((hc 0 self_mem_Ici).norm.pow 2)).tendsto.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  exact integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg hT hφ hg0 hgc
    (fun t _ ↦ by positivity) hL

end LinearPMap
