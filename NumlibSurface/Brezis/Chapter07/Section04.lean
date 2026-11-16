/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Brezis.Chapter07.Section03

/-!
# Brezis, Section 7.4: The self-adjoint case

This module formalizes Section 7.4 of [brezis2011functional] for a linear unbounded operator
$A : D(A) \subseteq H \to H$ on a real Hilbert space $H$. The source identifies $H^\star$ with $H$
and regards the adjoint $A^\star$ as an unbounded operator on $H$. The operator $A$ is symmetric if
$(Au, v) = (u, Av)$ for all $u, v \in D(A)$, and self-adjoint if $D(A^\star) = D(A)$ and
$A^\star = A$. A self-adjoint operator is symmetric (Remark 7), and a maximal monotone symmetric
operator is self-adjoint (Proposition 7.6). For a closed densely defined $A$, the maximal
monotonicity of $A$ is equivalent to that of $A^\star$, and to the monotonicity of both $A$ and
$A^\star$ (Remark 8). For a self-adjoint maximal monotone $A$, Theorem 7.7 solves the evolution
problem $du/dt + Au = 0$, $u(0) = u_0$ for every $u_0 \in H$, not only for $u_0 \in D(A)$: the
solution is smooth for $t > 0$, and $|du/dt(t)| \le |u_0|/t$.

Proposition 7.6 and Remark 8 specialize the backbone module
`Numlib.Analysis.InnerProductSpace.MaximalMonotone`, and Theorem 7.7 specializes
`Numlib.Analysis.ODE.HilleYosida`.

## Main definitions

* Section 7.4, definition of a symmetric operator, `Brezis.Chapter07.IsSymmetricOperator`:
  $(Au, v) = (u, Av)$ for all $u, v \in D(A)$, identified with Mathlib's
  `LinearPMap.IsFormalAdjoint A A` by `Brezis.Chapter07.isSymmetricOperator_iff`.
* Section 7.4, definition of a self-adjoint operator, `Brezis.Chapter07.IsSelfAdjointOperator`:
  $D(A^\star) = D(A)$ and $A^\star = A$, identified with Mathlib's `IsSelfAdjoint A` by
  `Brezis.Chapter07.isSelfAdjointOperator_iff`.

## Main results

* Remark 7, `Brezis.Chapter07.remark_7_7`: a self-adjoint operator is symmetric, and a densely
  defined $A$ is symmetric if and only if $A \subseteq A^\star$.
* Proposition 7.6, `Brezis.Chapter07.proposition_7_6`: a maximal monotone symmetric operator is
  self-adjoint.
* Remark 8, `Brezis.Chapter07.remark_7_8`, with the two equivalences
  `Brezis.Chapter07.remark_7_8_adjoint` and `Brezis.Chapter07.remark_7_8_closed`: $A$ is maximal
  monotone if and only if $A^\star$ is, if and only if $A$ is closed and densely defined and $A$ and
  $A^\star$ are monotone.
* Theorem 7.7, `Brezis.Chapter07.theorem_7_7`: for a self-adjoint maximal monotone $A$ and every
  $u_0 \in H$, the evolution problem has a unique solution, with $|u(t)| \le |u_0|$,
  $|du/dt(t)| = |Au(t)| \le |u_0|/t$, and $u \in C^k((0, +\infty); D(A^\ell))$ for all $k$ and
  $\ell$.

## Conventions

* The adjoint $A^\star$ is Mathlib's Hilbert-space adjoint `LinearPMap.adjoint`, written `A†`.
* Symmetry is Mathlib's `LinearPMap.IsFormalAdjoint A A`, and self-adjointness is Mathlib's
  `IsSelfAdjoint A`, that is, `A† = A`.

## Implementation notes

* The definitions of the source are stated in its words, as `Brezis.Chapter07.IsSymmetricOperator`
  and `Brezis.Chapter07.IsSelfAdjointOperator`. These names do not shadow the root `IsSelfAdjoint`
  inside the namespace.

## Deviations from the source

* **Remark 8** (reading). The equivalence of the maximal monotonicity of $A$ and of $A^\star$ is
  stated with the extra hypothesis that $D(A^\star)$ is dense, which gives $A^{\star\star} = A$. See
  `Brezis.Chapter07.remark_7_8_adjoint`.
* **Theorem 7.7** (generalization). Uniqueness is proved among all solutions on $(0, +\infty)$ that
  are continuous on $[0, +\infty)$, a larger class than the class of the source. See
  `Brezis.Chapter07.theorem_7_7`.

## Not formalized

* **Remark 7, the counterexample.** The claim that a symmetric $A$ may have $D(A) \neq D(A^\star)$
  is about a counterexample, which is not constructed.
* **Remark 8, the counterexample.** The claim that $A^\star$ need not be monotone when $A$ is a
  symmetric monotone operator is about a counterexample, which is not constructed.
* **Footnote 5.** It is a discussion and makes no precise statement.
-/

open Filter Topology Set
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace Brezis.Chapter07

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A : H →ₗ.[ℝ] H}

/-! ### The definitions -/

/-- **Section 7.4** of [brezis2011functional], definition of a symmetric operator. A linear
unbounded operator $A : D(A) \subseteq H \to H$ is **symmetric** if
$$(Au, v) = (u, Av) \quad \text{for all } u, v \in D(A).$$
-/
def IsSymmetricOperator (A : H →ₗ.[ℝ] H) : Prop :=
  ∀ u v : A.domain, ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ

/-- The symmetry of the source is Mathlib's `LinearPMap.IsFormalAdjoint A A`. -/
theorem isSymmetricOperator_iff (A : H →ₗ.[ℝ] H) : IsSymmetricOperator A ↔ A.IsFormalAdjoint A :=
  Iff.rfl

variable [CompleteSpace H]

/-- **Section 7.4** of [brezis2011functional], definition of a self-adjoint operator. Let $H$ be a
Hilbert space. A linear unbounded operator $A : D(A) \subseteq H \to H$ is **self-adjoint** if
$D(A^\star) = D(A)$ and $A^\star = A$ on this domain.

The adjoint $A^\star$ is Mathlib's `LinearPMap.adjoint`, written `A†`, which identifies
$H^\star$ with $H$ as the source does. -/
def IsSelfAdjointOperator (A : H →ₗ.[ℝ] H) : Prop :=
  A†.domain = A.domain ∧ ∀ (u : A.domain) (v : A†.domain), (u : H) = v → A† v = A u

/-- The self-adjointness of the source is Mathlib's `IsSelfAdjoint A`, that is, `A† = A`. -/
theorem isSelfAdjointOperator_iff (A : H →ₗ.[ℝ] H) : IsSelfAdjointOperator A ↔ IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  constructor
  · rintro ⟨hd, h⟩
    exact LinearPMap.dExt hd fun x y hxy => h y x hxy.symm
  · intro heq
    obtain ⟨hd, h⟩ := LinearPMap.dExt_iff.1 heq
    exact ⟨hd, fun u v huv => h huv.symm⟩

/-- **Remark 7** in Chapter 7 of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be a
linear unbounded operator with $D(A)$ dense in $H$. Then:

* if $A$ is self-adjoint, then $A$ is symmetric;
* $A$ is symmetric if and only if $A \subseteq A^\star$, that is, $D(A) \subseteq D(A^\star)$
  and $A^\star u = Au$ for all $u \in D(A)$.

The claim of the source that $A$ may be symmetric with $D(A) \neq D(A^\star)$ is about a
counterexample and is not formalized. For maximal monotone $A$ the two notions agree, by
Proposition 7.6. -/
theorem remark_7_7 (A : H →ₗ.[ℝ] H) (hd : Dense (A.domain : Set H)) :
    (IsSelfAdjointOperator A → IsSymmetricOperator A) ∧
      (IsSymmetricOperator A ↔ A.domain ≤ A†.domain ∧
        ∀ (u : A.domain) (v : A†.domain), (u : H) = v → A† v = A u) := by
  refine ⟨fun h => ((isSelfAdjointOperator_iff A).1 h).isFormalAdjoint_self, ?_⟩
  rw [isSymmetricOperator_iff, LinearPMap.IsFormalAdjoint.le_adjoint_iff hd]
  exact ⟨fun h => ⟨h.1, fun u v huv => (h.2 huv).symm⟩,
    fun h => ⟨h.1, fun u v huv => (h.2 u v huv).symm⟩⟩

/-- **Proposition 7.6** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be a
maximal monotone symmetric operator. Then $A$ is self-adjoint. -/
theorem proposition_7_6 (hA : IsMaximalMonotone A) (hs : IsSymmetricOperator A) :
    IsSelfAdjointOperator A :=
  (isSelfAdjointOperator_iff A).2 (hA.isMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint hs)

/-- **Remark 8** in Chapter 7 of [brezis2011functional], the first equivalence. Let $H$ be a Hilbert
space and let $A$ be a closed linear unbounded operator with $D(A)$ dense, and with $D(A^\star)$
dense. Then $A$ is maximal monotone if and only if $A^\star$ is maximal monotone.

**Reading.** The hypothesis that $D(A^\star)$ is dense is added. It gives $A^{\star\star} = A$,
which the argument uses. This hypothesis holds for every closed densely defined operator on a
Hilbert space; here it is stated explicitly. -/
theorem remark_7_8_adjoint (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) : IsMaximalMonotone A ↔ IsMaximalMonotone A† := by
  rw [isMaximalMonotone_iff, isMaximalMonotone_iff]
  exact LinearPMap.isMaximalMonotone_iff_adjoint hcl hd hd'

/-- **Remark 8** in Chapter 7 of [brezis2011functional], the second equivalence. Let $H$ be a
Hilbert space and let $A$ be a linear unbounded operator. Then $A$ is maximal monotone if and
only if $A$ is closed, $D(A)$ is dense, and $A$ and $A^\star$ are monotone.

This equivalence needs no hypothesis on $A$. -/
theorem remark_7_8_closed (A : H →ₗ.[ℝ] H) :
    IsMaximalMonotone A ↔
      A.IsClosed ∧ Dense (A.domain : Set H) ∧ IsMonotone A ∧ IsMonotone A† := by
  rw [isMaximalMonotone_iff, isMonotone_iff, isMonotone_iff]
  exact LinearPMap.isMaximalMonotone_iff_isClosed_dense_isMonotone

/-- **Remark 8** in Chapter 7 of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be a
closed linear unbounded operator with $D(A)$ and $D(A^\star)$ dense. Then the following are
equivalent:

* $A$ is maximal monotone;
* $A^\star$ is maximal monotone;
* $A$ is closed, $D(A)$ is dense, and $A$ and $A^\star$ are monotone.

**Reading.** The hypothesis that $D(A^\star)$ is dense is added, as in
`Brezis.Chapter07.remark_7_8_adjoint`.

The claim of the source that $A^\star$ need not be monotone when $A$ is merely symmetric and
monotone is about a counterexample and is not formalized. The version for Banach spaces is
Problem 16 of the source. -/
theorem remark_7_8 (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) :
    [IsMaximalMonotone A, IsMaximalMonotone A†,
      A.IsClosed ∧ Dense (A.domain : Set H) ∧ IsMonotone A ∧ IsMonotone A†].TFAE := by
  tfae_have 1 ↔ 2 := remark_7_8_adjoint hcl hd hd'
  tfae_have 1 ↔ 3 := remark_7_8_closed A
  tfae_finish

/-! ### Theorem 7.7 -/

/-- **Theorem 7.7** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be a
self-adjoint maximal monotone operator. Then for every $u_0 \in H$ there is a unique
$$u \in C([0, +\infty); H) \cap C^1((0, +\infty); H) \cap C((0, +\infty); D(A))$$
such that $du/dt + Au = 0$ on $(0, +\infty)$ and $u(0) = u_0$. Moreover:

* $|u(t)| \le |u_0|$ for all $t \ge 0$;
* $|du/dt(t)| = |Au(t)| \le |u_0|/t$ for all $t > 0$;
* (26) $u \in C^k((0, +\infty); D(A^\ell))$ for all integers $k, \ell \ge 0$.

**Generalization.** Uniqueness is proved in a larger class than in the source: every $v$ that
solves $dv/dt + Av = 0$ on $(0, +\infty)$ with $v(0) = u_0$ and is continuous on $[0, +\infty)$
agrees with $u$ on $[0, +\infty)$. No regularity of $v$ on $(0, +\infty)$ beyond
differentiability is assumed.

The equation is `LinearPMap.IsSolutionOn A u₀ (Set.Ioi 0) u`, and
$u \in C^k((0, +\infty); D(A^\ell))$ is `LinearPMap.ContDiffOnPowDomain A k ℓ u (Set.Ioi 0)`.
The solution is $t \mapsto S_A(t) u_0$. Step 1 of the source's proof is the backbone's estimate
`norm_exp_neg_smul_apply_le_div`, Step 2 is
`LinearPMap.semigroup_apply_mem_domain_of_isFormalAdjoint`, and (26) is
`LinearPMap.contDiffOnPowDomain_semigroup_Ioi`. -/
theorem theorem_7_7 (hA : IsMaximalMonotone A) (hs : IsSelfAdjointOperator A) (u₀ : H) :
    ∃ u : ℝ → H, ∃ hu : A.IsSolutionOn u₀ (Ioi 0) u,
      ContinuousOn u (Ici 0) ∧ ContDiffOn ℝ 1 u (Ioi 0) ∧ A.ContDiffOnPowDomain 0 1 u (Ioi 0) ∧
      (∀ v, A.IsSolutionOn u₀ (Ioi 0) v → ContinuousOn v (Ici 0) → EqOn v u (Ici 0)) ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖) ∧
      (∀ t (ht : 0 < t), ‖deriv u t‖ = ‖A ⟨u t, hu.mem_domain t ht⟩‖ ∧
        ‖A ⟨u t, hu.mem_domain t ht⟩‖ ≤ ‖u₀‖ / t) ∧
      ∀ k l : ℕ, A.ContDiffOnPowDomain k l u (Ioi 0) := by
  obtain ⟨u, hu, hc, hc1, hle, hdiv, hpow⟩ := LinearPMap.exists_isSolutionOn_Ioi_of_isSelfAdjoint
    hA.isMaximalMonotone ((isSelfAdjointOperator_iff A).1 hs) u₀
  refine ⟨u, hu, hc, hc1, by simpa using hpow 0 1,
    fun v hv hvc => hA.isMaximalMonotone.isMonotone.eqOn_of_isSolutionOn_Ioi hv hu hvc hc, hle,
    fun t ht => ⟨?_, hdiv t ht⟩, hpow⟩
  rw [((hu.hasDerivWithinAt t ht).hasDerivAt (Ioi_mem_nhds ht)).deriv, norm_neg]

end Brezis.Chapter07

end
