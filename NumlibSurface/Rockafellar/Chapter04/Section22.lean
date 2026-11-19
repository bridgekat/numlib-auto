/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.LinearInequalities
import NumlibSurface.Rockafellar.Chapter03.Section14

/-!
# Rockafellar, Section 22: Linear inequalities

This module formalizes the first part of Section 22 of [rockafellar1970convex]: finite systems of
weak and strict linear inequalities in $\mathbb{R}^n$, the theorems of the alternative that decide
their solvability, and Farkas' Lemma. For vectors $a_1, \dots, a_m \in \mathbb{R}^n$ and reals
$\alpha_1, \dots, \alpha_m$, the system $\langle a_i, x \rangle \le \alpha_i$, $i = 1, \dots, m$,
has a solution if and only if there are no $\lambda_i \ge 0$ with $\sum_i \lambda_i a_i = 0$ and
$\sum_i \lambda_i \alpha_i < 0$ (Theorem 22.1). Theorem 22.2 is the analogue for a system with
strict and weak inequalities. Theorem 22.3 describes the inequalities
$\langle a_0, x \rangle \le \alpha_0$ that every solution of a consistent system satisfies, and its
corollary, Farkas' Lemma, is the case $\alpha_i = 0$.

The module also sets up the reformulation of p. 202 that the second part of the section uses. With
$A$ the $m \times n$ matrix with rows $a_i$, a solution $x$ of a linear system becomes the vector
$(x, Ax) \in \mathbb{R}^{n+m}$, which lies in the subspace $L$ (the graph of $A$) and in a
generalized rectangle $I_1 \times \dots \times I_{n+m}$ of real intervals. The proofs specialize
`Numlib.Analysis.Convex.LinearInequalities`.

## Main definitions

* `Rockafellar.IsConsequence`: the inequality $\langle a_0, x \rangle \le \alpha_0$ is a consequence
  of a system of weak linear inequalities.
* `Rockafellar.IsRowsOf`: a linear map $A$ is the matrix with rows $a_1, \dots, a_m$.
* `Rockafellar.IsRealInterval`, `Rockafellar.rectangle`, `Rockafellar.intervalCombo`,
  `Rockafellar.posIntervalCombo`: real intervals, generalized rectangles, the set
  $\sum_j \zeta_j^* I_j$, and the condition $\sum_j \zeta_j^* I_j > 0$.
* `Rockafellar.intervalVector`, `Rockafellar.intervalSubspace`, `Rockafellar.leIntervals`,
  `Rockafellar.nonnegEqIntervals`: the vector $(x, Ax)$, the subspace $L$, and the intervals of the
  systems $Ax \le a$ and $x \ge 0$, $Ax = a$.

## Main results

* Theorem 22.1, `Rockafellar.theorem_22_1` (Gale's theorem of the alternative):
  $\langle a_i, x \rangle \le \alpha_i$ is solvable if and only if no $\lambda \ge 0$ has
  $\sum_i \lambda_i a_i = 0$ and $\sum_i \lambda_i \alpha_i < 0$. The matrix form is
  `Rockafellar.theorem_22_1_matrix`.
* Theorem 22.2, `Rockafellar.theorem_22_2` (Motzkin's transposition theorem): the alternative for a
  system of strict and weak linear inequalities whose weak part is consistent.
* Theorem 22.3, `Rockafellar.theorem_22_3`: $\langle a_0, x \rangle \le \alpha_0$ is a consequence
  of a consistent system if and only if $a_0 = \sum_i \lambda_i a_i$ and
  $\sum_i \lambda_i \alpha_i \le \alpha_0$ for some $\lambda \ge 0$.
* Corollary 22.3.1, `Rockafellar.corollary_22_3_1` (Farkas' Lemma): $\langle a_0, x \rangle \le 0$
  is a consequence of $\langle a_i, x \rangle \le 0$ if and only if $a_0$ is a nonnegative
  combination of the $a_i$. The form $K^{\circ\circ} = K$ is `Rockafellar.corollary_22_3_1_polar`.
* `Rockafellar.interval_reading_le`, `Rockafellar.interval_reading_nonneg_eq`: a linear system has a
  solution if and only if the subspace $L$ meets the corresponding rectangle.

## Conventions

* $\mathbb{R}^n$ is `Rockafellar.Rn n`. The inner product $\langle a, x \rangle$ is
  `Rockafellar.pairing n a x`.
* The source writes $\sum_j \zeta_j^* I_j > 0$ for the set containment
  $\sum_j \zeta_j^* I_j \subseteq (0, +\infty)$: the inequality $\zeta_1^* \zeta_1 + \dots +
  \zeta_N^* \zeta_N > 0$ holds for every choice of $\zeta_j \in I_j$. The source states this
  convention once, in a parenthesis on p. 202. It is `Rockafellar.posIntervalCombo`.

## Implementation notes

* The source writes $\langle a_i, x \rangle$ with the coefficient vector first, and the statements
  here follow it. The backbone writes `B x (a i)`, because in general the solution vector and the
  coefficient vectors lie in different spaces. On $\mathbb{R}^n$ the pairing is symmetric, and
  `Rockafellar.pairing_comm` is the only translation needed.
* A matrix $A \in \mathbb{R}^{m \times n}$ is a linear map `Rn n →ₗ[ℝ] Rn m`, and its transpose
  $A^*$ is `LinearMap.adjoint A`.

## Deviations from the source

* **Theorem 22.2** (generalization). The book requires at least one strict inequality.
  The Lean alternative also allows an empty strict family, in which case consistency
  of the weak subsystem gives feasibility.
* **Section 22, interval data** (generalization). The generalized rectangle, the set of
  weighted sums and the positivity condition are defined for arbitrary real subsets.
  Their use with intervals is the one in the book.

## Not formalized

* **Lemmas 22.4 and 22.5, Corollary 22.4.1, and Theorems 22.6 and 22.7 (Tucker's complementarity
  theorem).** These results rest on the elementary vectors of a subspace, a development that is
  combinatorial matroid theory rather than convex analysis. Theorems 22.6 and 22.7 rest also on
  Tucker representations of a subspace, which the source describes only as a procedure (solve the
  defining system for the last $N - n$ coordinates in terms of the first $n$, after some
  permutation); to state them needs a choice of $n$ independent coordinate positions and the
  resulting change of basis. The only other result of the source that rests on them is Corollary
  31.4.2.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-! ### Theorem 22.1: the alternative for a system of weak inequalities -/

/-- **Theorem 22.1** of [rockafellar1970convex] (Gale's theorem of the alternative). Let
$a_1, \dots, a_m \in \mathbb{R}^n$ and $\alpha_1, \dots, \alpha_m \in \mathbb{R}$. Then exactly
one of the following holds:

(a) there is $x \in \mathbb{R}^n$ with $\langle a_i, x \rangle \le \alpha_i$ for
$i = 1, \dots, m$;

(b) there are real numbers $\lambda_1, \dots, \lambda_m \ge 0$ with
$$\lambda_1 a_1 + \dots + \lambda_m a_m = 0, \qquad \lambda_1 \alpha_1 + \dots + \lambda_m
  \alpha_m < 0.$$

"Exactly one" is stated as the equivalence of (a) with the negation of (b). The direction from
(a) to the negation of (b) is the exclusivity, and the converse is the existence. -/
theorem theorem_22_1 (a : Fin m → Rn n) (α : Fin m → ℝ) :
    (∃ x : Rn n, ∀ i, pairing n (a i) x ≤ α i) ↔
      ¬ ∃ l : Fin m → ℝ, (∀ i, 0 ≤ l i) ∧ (∑ i, l i • a i = 0) ∧ ∑ i, l i * α i < 0 := by
  rw [← alternative_linear_system (B := pairing n) a α]
  exact exists_congr fun x => forall_pairing_le_comm a α x

/-! ### Theorem 22.2: the alternative for a mixed system -/

/-- **Theorem 22.2** of [rockafellar1970convex] (Motzkin's transposition theorem). Let $a_1, \dots,
a_p, b_1, \dots, b_q \in \mathbb{R}^n$ and $\alpha_1, \dots, \alpha_p, \beta_1, \dots, \beta_q
\in \mathbb{R}$, and assume that the system $\langle b_j, x \rangle \le \beta_j$,
$j = 1, \dots, q$, is consistent. Then exactly one of the following holds:

(a) there is $x \in \mathbb{R}^n$ with $\langle a_i, x \rangle < \alpha_i$ for every $i$ and
$\langle b_j, x \rangle \le \beta_j$ for every $j$;

(b) there are real numbers $\lambda_i \ge 0$, not all zero, and $\mu_j \ge 0$ with
$$\sum_i \lambda_i a_i + \sum_j \mu_j b_j = 0, \qquad \sum_i \lambda_i \alpha_i + \sum_j \mu_j
  \beta_j \le 0.$$

The source uses one index range $1, \dots, m$ and puts the strict inequalities first, up to $k$.
Here the strict and the weak inequalities are two separate families, indexed by `Fin p` and
`Fin q`. "Exactly one" is the equivalence of (a) with the negation of (b).

**Generalization.** The book requires $k \ge 1$. An empty strict family is also allowed
here, with feasibility supplied by the hypothesis on the weak subsystem. -/
theorem theorem_22_2 {p q : ℕ} (a : Fin p → Rn n) (α : Fin p → ℝ) (b : Fin q → Rn n)
    (β : Fin q → ℝ) (hcons : ∃ x : Rn n, ∀ j, pairing n (b j) x ≤ β j) :
    (∃ x : Rn n, (∀ i, pairing n (a i) x < α i) ∧ ∀ j, pairing n (b j) x ≤ β j) ↔
      ¬ ∃ (l : Fin p → ℝ) (μ : Fin q → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ (∃ i, l i ≠ 0) ∧
        (∑ i, l i • a i + ∑ j, μ j • b j = 0) ∧ ∑ i, l i * α i + ∑ j, μ j * β j ≤ 0 := by
  obtain ⟨x₀, hx₀⟩ := hcons
  rw [← alternative_linear_system_strict (B := pairing n) a α b β
    ⟨x₀, (forall_pairing_le_comm b β x₀).1 hx₀⟩]
  exact exists_congr fun x =>
    and_congr (forall_pairing_lt_comm a α x) (forall_pairing_le_comm b β x)

/-- **Section 22** of [rockafellar1970convex], p. 200. The consistency hypothesis of Theorem 22.2 is
decided by Theorem 22.1: for $b_1, \dots, b_q \in \mathbb{R}^n$ and
$\beta_1, \dots, \beta_q \in \mathbb{R}$, the system $\langle b_j, x \rangle \le \beta_j$ has no
solution if and only if there are $\mu_1, \dots, \mu_q \ge 0$ with $\sum_j \mu_j b_j = 0$ and
$\sum_j \mu_j \beta_j < 0$. -/
theorem not_consistent_iff {q : ℕ} (b : Fin q → Rn n) (β : Fin q → ℝ) :
    (¬ ∃ x : Rn n, ∀ j, pairing n (b j) x ≤ β j) ↔
      ∃ μ : Fin q → ℝ, (∀ j, 0 ≤ μ j) ∧ (∑ j, μ j • b j = 0) ∧ ∑ j, μ j * β j < 0 := by
  rw [theorem_22_1 b β, not_not]

/-! ### Theorem 22.3: consequences of a system -/

/-- **Section 22** of [rockafellar1970convex], p. 200, consequence of a system. Let
$a_0, a_1, \dots, a_m \in \mathbb{R}^n$ and $\alpha_0, \alpha_1, \dots, \alpha_m \in
\mathbb{R}$. The inequality $\langle a_0, x \rangle \le \alpha_0$ is a **consequence** of the
system $\langle a_i, x \rangle \le \alpha_i$, $i = 1, \dots, m$, if every solution $x$ of the
system satisfies it. -/
def IsConsequence (a : Fin m → Rn n) (α : Fin m → ℝ) (a₀ : Rn n) (α₀ : ℝ) : Prop :=
  ∀ x : Rn n, (∀ i, pairing n (a i) x ≤ α i) → pairing n a₀ x ≤ α₀

/-- The inequality $\langle a_0, x \rangle \le \alpha_0$ is a consequence of the system
$\langle a_i, x \rangle \le \alpha_i$ if and only if every $x$ with
$\langle x, a_i \rangle \le \alpha_i$ for all $i$ satisfies
$\langle x, a_0 \rangle \le \alpha_0$.

This is `Rockafellar.IsConsequence` with the pairing in the order of the backbone. -/
theorem isConsequence_iff {a : Fin m → Rn n} {α : Fin m → ℝ} {a₀ : Rn n} {α₀ : ℝ} :
    IsConsequence a α a₀ α₀ ↔
      ∀ x : Rn n, (∀ i, pairing n x (a i) ≤ α i) → pairing n x a₀ ≤ α₀ :=
  forall_congr' fun x => imp_congr (forall_pairing_le_comm a α x) (by rw [pairing_comm])

/-- **Theorem 22.3** of [rockafellar1970convex]. Let $a_0, a_1, \dots, a_m \in \mathbb{R}^n$ and
$\alpha_0, \alpha_1, \dots, \alpha_m \in \mathbb{R}$, and assume that the system
$\langle a_i, x \rangle \le \alpha_i$, $i = 1, \dots, m$, is consistent. Then
$\langle a_0, x \rangle \le \alpha_0$ is a consequence of the system if and only if there are
real numbers $\lambda_1, \dots, \lambda_m \ge 0$ with
$$\lambda_1 a_1 + \dots + \lambda_m a_m = a_0, \qquad \lambda_1 \alpha_1 + \dots + \lambda_m
  \alpha_m \le \alpha_0.$$
-/
theorem theorem_22_3 (a : Fin m → Rn n) (α : Fin m → ℝ) (a₀ : Rn n) (α₀ : ℝ)
    (hcons : ∃ x : Rn n, ∀ i, pairing n (a i) x ≤ α i) :
    IsConsequence a α a₀ α₀ ↔
      ∃ l : Fin m → ℝ, (∀ i, 0 ≤ l i) ∧ (∑ i, l i • a i = a₀) ∧ ∑ i, l i * α i ≤ α₀ := by
  obtain ⟨x₀, hx₀⟩ := hcons
  rw [isConsequence_iff]
  exact le_consequence_iff a α a₀ α₀ ⟨x₀, (forall_pairing_le_comm a α x₀).1 hx₀⟩

/-- **Corollary 22.3.1** of [rockafellar1970convex] (Farkas' Lemma). Let
$a_0, a_1, \dots, a_m \in \mathbb{R}^n$. The inequality $\langle a_0, x \rangle \le 0$ is a
consequence of the system $\langle a_i, x \rangle \le 0$, $i = 1, \dots, m$, if and only if
there are real numbers $\lambda_1, \dots, \lambda_m \ge 0$ with
$\lambda_1 a_1 + \dots + \lambda_m a_m = a_0$.

No consistency hypothesis is needed, because $x = 0$ solves the homogeneous system. -/
theorem corollary_22_3_1 (a : Fin m → Rn n) (a₀ : Rn n) :
    IsConsequence a (fun _ => 0) a₀ 0 ↔
      ∃ l : Fin m → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i • a i = a₀ := by
  rw [isConsequence_iff]
  exact farkas (B := pairing n) a a₀

/-- **Section 22** of [rockafellar1970convex], p. 200. Let $a_1, \dots, a_m \in \mathbb{R}^n$, and
let $K$ be the convex cone generated by $a_1, \dots, a_m$ (together with the origin). The
solution set of the system $\langle a_i, x \rangle \le 0$, $i = 1, \dots, m$, is the polar cone
$$K^\circ = \{x \mid \langle y, x \rangle \le 0 \text{ for every } y \in K\}.$$

The cone $K$ is `PointedCone.hull ℝ (Set.range a)`, and the polar is `ConvexAnalysis.polarCone`. -/
theorem solutions_eq_polarCone (a : Fin m → Rn n) :
    {x : Rn n | ∀ i, pairing n (a i) x ≤ 0}
      = polarCone (pairing n) (PointedCone.hull ℝ (Set.range a) : Set (Rn n)) :=
  (polarCone_hull_range_rn a).symm

/-- **Section 22** of [rockafellar1970convex], p. 200, Farkas' Lemma as a bipolar identity. Let $K$
be the convex cone generated by finitely many vectors $a_1, \dots, a_m \in \mathbb{R}^n$
(together with the origin). Then $K^{\circ\circ} = K$.

The cone $K$ is closed because it is finitely generated (Theorem 19.1), so Theorem 14.1 gives
$K^{\circ\circ} = \operatorname{cl} K = K$. -/
theorem corollary_22_3_1_polar (a : Fin m → Rn n) :
    polarCone (pairing n) (polarCone (pairing n)
        (PointedCone.hull ℝ (Set.range a) : Set (Rn n)))
      = (PointedCone.hull ℝ (Set.range a) : Set (Rn n)) := by
  rw [polarCone_hull_range_rn, polarCone_setOf_forall_le_zero_rn,
    (isClosed_coe_pointedCone_hull_range a).closure_eq]

/-! ### The matrix form -/

/-- **Section 22** of [rockafellar1970convex], p. 201, matrix form. A linear map
$A : \mathbb{R}^n \to \mathbb{R}^m$ **has rows** $a_1, \dots, a_m \in \mathbb{R}^n$ if
$(Ax)_i = \langle a_i, x \rangle$ for every $x \in \mathbb{R}^n$ and every $i$. Then the system
of alternative (a) of Theorem 22.1 reads $Ax \le a$, componentwise, with
$a = (\alpha_1, \dots, \alpha_m)$. -/
def IsRowsOf (A : Rn n →ₗ[ℝ] Rn m) (a : Fin m → Rn n) : Prop := ∀ x i, A x i = pairing n (a i) x

/-- **Section 22** of [rockafellar1970convex], p. 201. If $A : \mathbb{R}^n \to \mathbb{R}^m$ has
rows $a_1, \dots, a_m$, then its transpose satisfies $A^* w = \sum_i w_i a_i$ for every
$w \in \mathbb{R}^m$.

Thus the condition $\sum_i \lambda_i a_i = 0$ of Theorem 22.1(b) reads $A^* \lambda = 0$. The
transpose $A^*$ is `LinearMap.adjoint A`. -/
theorem adjoint_eq_sum_smul {A : Rn n →ₗ[ℝ] Rn m} {a : Fin m → Rn n} (h : IsRowsOf A a)
    (w : Rn m) : LinearMap.adjoint A w = ∑ i, w i • a i := by
  refine ext_inner_left ℝ fun x => ?_
  rw [← pairing_apply, ← isAdjointPair_adjoint A x w, pairing_apply, PiLp.inner_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, ← pairing_apply, pairing_comm, ← h x i]
  simp

/-- **Section 22** of [rockafellar1970convex], p. 201, Theorem 22.1 in matrix form. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ have rows $a_1, \dots, a_m$, and let $a \in \mathbb{R}^m$.
Then the system $Ax \le a$ has a solution $x \in \mathbb{R}^n$ if and only if there is no
$w \in \mathbb{R}^m$ with
$$w \ge 0, \qquad A^* w = 0, \qquad \langle w, a \rangle < 0.$$

The right-hand side $a$ is the vector `α`. -/
theorem theorem_22_1_matrix {A : Rn n →ₗ[ℝ] Rn m} {a : Fin m → Rn n} (h : IsRowsOf A a)
    (α : Rn m) :
    (∃ x : Rn n, ∀ i, A x i ≤ α i) ↔
      ¬ ∃ w : Rn m, (∀ i, 0 ≤ w i) ∧ LinearMap.adjoint A w = 0 ∧ pairing m w α < 0 := by
  have hsum : ∀ w : Rn m, pairing m w α = ∑ i, w i * α i := by
    intro w
    rw [pairing_apply, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hL : (∃ x : Rn n, ∀ i, A x i ≤ α i) ↔ ∃ x : Rn n, ∀ i, pairing n (a i) x ≤ α i :=
    exists_congr fun x => forall_congr' fun i => by rw [h x i]
  rw [hL, theorem_22_1 a fun i => α i]
  refine not_congr ⟨fun hl => ?_, fun hw => ?_⟩
  · obtain ⟨l, hl0, hla, hlα⟩ := hl
    refine ⟨WithLp.toLp 2 l, hl0, ?_, ?_⟩
    · rw [adjoint_eq_sum_smul h]
      exact hla
    · rw [hsum]
      exact hlα
  · obtain ⟨w, hw0, hwa, hwα⟩ := hw
    refine ⟨fun i => w i, hw0, ?_, ?_⟩
    · rw [← adjoint_eq_sum_smul h w]
      exact hwa
    · rw [← hsum w]
      exact hwα

/-! ### The interval form -/

/-- **Section 22** of [rockafellar1970convex], p. 202, real interval. A **real interval** is a
convex subset $I$ of $\mathbb{R}$. In the words of the source, "$I_j$ may be open or closed or
neither, and it may consist of just a single number". -/
def IsRealInterval (I : Set ℝ) : Prop := Convex ℝ I

/-- **Section 22** of [rockafellar1970convex], p. 203, generalized rectangle. For subsets
$I_1, \dots, I_N$ of $\mathbb{R}$, the **generalized rectangle** is
$$C = \{(\zeta_1, \dots, \zeta_N) \mid \zeta_j \in I_j, \ j = 1, \dots, N\} \subseteq
  \mathbb{R}^N.$$

Theorem 22.6 is about whether a subspace $L$ meets this set or is separated from it.

**Generalization.** The book uses intervals for the coordinate sets. The construction
also applies to nonconvex coordinate sets. -/
def rectangle {N : ℕ} (I : Fin N → Set ℝ) : Set (Rn N) := {z : Rn N | ∀ j, z j ∈ I j}

/-- A vector $z \in \mathbb{R}^N$ lies in the generalized rectangle of $I_1, \dots, I_N$ if and only
if $z_j \in I_j$ for every $j$. -/
@[simp] theorem mem_rectangle {N : ℕ} {I : Fin N → Set ℝ} {z : Rn N} :
    z ∈ rectangle I ↔ ∀ j, z j ∈ I j := Iff.rfl

/-- If $I_1, \dots, I_N$ are real intervals, then their generalized rectangle is convex. -/
theorem convex_rectangle {N : ℕ} {I : Fin N → Set ℝ} (h : ∀ j, IsRealInterval (I j)) :
    Convex ℝ (rectangle I) := by
  intro x hx y hy s t hs ht hst j
  simpa using h j (hx j) (hy j) hs ht hst

/-- **Section 22** of [rockafellar1970convex], p. 202. For $z^* = (\zeta_1^*, \dots, \zeta_N^*) \in
\mathbb{R}^N$ and subsets $I_1, \dots, I_N$ of $\mathbb{R}$, the **linear combination** of the
sets $I_j$ is the set
$$\zeta_1^* I_1 + \dots + \zeta_N^* I_N = \{\zeta_1^* \zeta_1 + \dots + \zeta_N^* \zeta_N \mid
  \zeta_j \in I_j\} \subseteq \mathbb{R}.$$

**Generalization.** The book uses this expression for intervals. The same set operation
accepts arbitrary coordinate sets.
-/
def intervalCombo {N : ℕ} (z : Rn N) (I : Fin N → Set ℝ) : Set ℝ := ∑ j, z j • I j

/-- **Section 22** of [rockafellar1970convex], p. 202, the condition $\sum_j \zeta_j^* I_j > 0$. For
$z^* \in \mathbb{R}^N$ and subsets $I_1, \dots, I_N$ of $\mathbb{R}$, the condition
$\sum_j \zeta_j^* I_j > 0$ means $\zeta_1^* \zeta_1 + \dots + \zeta_N^* \zeta_N > 0$ for every
choice of $\zeta_j \in I_j$, that is,
$$\zeta_1^* I_1 + \dots + \zeta_N^* I_N \subseteq (0, +\infty).$$

**Generalization.** The condition accepts any coordinate sets, including nonconvex ones.
-/
def posIntervalCombo {N : ℕ} (z : Rn N) (I : Fin N → Set ℝ) : Prop :=
  intervalCombo z I ⊆ Set.Ioi 0

/-- The condition $\sum_j \zeta_j^* I_j > 0$ holds if and only if every element $c$ of the set
$\sum_j \zeta_j^* I_j$ satisfies $c > 0$. -/
theorem posIntervalCombo_iff {N : ℕ} {z : Rn N} {I : Fin N → Set ℝ} :
    posIntervalCombo z I ↔ ∀ c ∈ intervalCombo z I, 0 < c := Iff.rfl

/-- **Section 22** of [rockafellar1970convex], p. 203. If $I_1, \dots, I_N$ are real intervals and
$z^* \in \mathbb{R}^N$, then $\sum_j \zeta_j^* I_j$ is a real interval. In the words of the
source, "a linear combination of convex sets is convex". -/
theorem isRealInterval_intervalCombo {N : ℕ} (z : Rn N) {I : Fin N → Set ℝ}
    (h : ∀ j, IsRealInterval (I j)) : IsRealInterval (intervalCombo z I) := by
  classical
  refine Finset.sum_induction _ (Convex ℝ) (fun s t hs ht => hs.add ht) ?_ ?_
  · rw [← Set.singleton_zero]
    exact convex_singleton 0
  · exact fun j _ => (h j).smul (z j)

/-!
### The interval reading of a linear system (p. 202)

A system in $\mathbb{R}^n$ with $m$ constraints becomes a problem about a rectangle in
$\mathbb{R}^N$, $N = n + m$. Append the $m$ constraint values to the $n$ unknowns. The system then
says that the resulting vector lies both in a fixed $n$-dimensional subspace $L$ (the graph of $A$,
written in $\mathbb{R}^N$) and in the generalized rectangle of the intervals $I_1, \dots, I_N$. The
original system survives only in the choice of the intervals.
-/

/-- **Section 22** of [rockafellar1970convex], p. 202. For a linear map
$A : \mathbb{R}^n \to \mathbb{R}^m$ and $x = (\xi_1, \dots, \xi_n) \in \mathbb{R}^n$, the
solution $x$ becomes the vector
$$z = (\xi_1, \dots, \xi_n, (Ax)_1, \dots, (Ax)_m) \in \mathbb{R}^{n+m}.$$

The concatenation of coordinates is `euclideanProdEquiv`. -/
noncomputable def intervalVector (A : Rn n →ₗ[ℝ] Rn m) (x : Rn n) : Rn (n + m) :=
  euclideanProdEquiv n m (x, A x)

/-- The first $n$ coordinates of the vector $(x, Ax) \in \mathbb{R}^{n+m}$ are the coordinates of
$x$: its coordinate $j \le n$ is $\xi_j$. -/
@[simp] theorem intervalVector_castAdd (A : Rn n →ₗ[ℝ] Rn m) (x : Rn n) (j : Fin n) :
    intervalVector A x (Fin.castAdd m j) = x j :=
  euclideanProdEquiv_apply_castAdd (x, A x) j

/-- The last $m$ coordinates of the vector $(x, Ax) \in \mathbb{R}^{n+m}$ are the coordinates of
$Ax$: its coordinate $n + i$ is $(Ax)_i$. -/
@[simp] theorem intervalVector_natAdd (A : Rn n →ₗ[ℝ] Rn m) (x : Rn n) (i : Fin m) :
    intervalVector A x (Fin.natAdd n i) = A x i :=
  euclideanProdEquiv_apply_natAdd (x, A x) i

/-- **Section 22** of [rockafellar1970convex], p. 202, the subspace $L$. For a linear map
$A : \mathbb{R}^n \to \mathbb{R}^m$ with matrix entries $\alpha_{ij}$, the subspace
$L \subseteq \mathbb{R}^{n+m}$ consists of the vectors $(\zeta_1, \dots, \zeta_{n+m})$ with
$$\zeta_{n+i} = \sum_{j=1}^n \alpha_{ij} \zeta_j, \qquad i = 1, \dots, m.$$
It is the graph of $A$, written in $\mathbb{R}^{n+m}$. Theorem 22.6 is stated in terms of $L$
instead of the matrix.

The subspace is the range of $x \mapsto (x, Ax)$. -/
noncomputable def intervalSubspace (A : Rn n →ₗ[ℝ] Rn m) : Submodule ℝ (Rn (n + m)) :=
  LinearMap.range ((euclideanProdEquiv n m).toLinearEquiv.toLinearMap.comp
    ((LinearMap.id : Rn n →ₗ[ℝ] Rn n).prod A))

/-- A vector $z \in \mathbb{R}^{n+m}$ lies in the subspace $L$ of $A$ if and only if $z = (x, Ax)$
for some $x \in \mathbb{R}^n$. -/
@[simp] theorem mem_intervalSubspace {A : Rn n →ₗ[ℝ] Rn m} {z : Rn (n + m)} :
    z ∈ intervalSubspace A ↔ ∃ x, intervalVector A x = z := Iff.rfl

/-- The vector $(x, Ax) \in \mathbb{R}^{n+m}$ lies in the generalized rectangle of
$I_1, \dots, I_{n+m}$ if and only if $\xi_j \in I_j$ for $j = 1, \dots, n$ and
$(Ax)_i \in I_{n+i}$ for $i = 1, \dots, m$. -/
theorem intervalVector_mem_rectangle {A : Rn n →ₗ[ℝ] Rn m} {x : Rn n}
    {I : Fin (n + m) → Set ℝ} :
    intervalVector A x ∈ rectangle I ↔
      (∀ j, x j ∈ I (Fin.castAdd m j)) ∧ ∀ i, A x i ∈ I (Fin.natAdd n i) := by
  rw [mem_rectangle]
  refine ⟨fun h => ⟨fun j => ?_, fun i => ?_⟩, fun h => Fin.addCases (fun j => ?_) fun i => ?_⟩
  · simpa using h (Fin.castAdd m j)
  · simpa using h (Fin.natAdd n i)
  · simpa using h.1 j
  · simpa using h.2 i

/-- **Section 22** of [rockafellar1970convex], p. 202, the intervals of the system $Ax \le a$. For
$a = (\alpha_1, \dots, \alpha_m) \in \mathbb{R}^m$, the intervals are $I_j = (-\infty, +\infty)$
for $j = 1, \dots, n$ and $I_{n+i} = (-\infty, \alpha_i]$ for $i = 1, \dots, m$. -/
def leIntervals (n : ℕ) {m : ℕ} (α : Rn m) : Fin (n + m) → Set ℝ :=
  Fin.addCases (fun _ : Fin n => Set.univ) fun i => Set.Iic (α i)

/-- The first $n$ intervals of the system $Ax \le a$ are $I_j = (-\infty, +\infty)$. -/
@[simp] theorem leIntervals_castAdd {n m : ℕ} (α : Rn m) (j : Fin n) :
    leIntervals n α (Fin.castAdd m j) = Set.univ := Fin.addCases_left j

/-- The last $m$ intervals of the system $Ax \le a$ are $I_{n+i} = (-\infty, \alpha_i]$. -/
@[simp] theorem leIntervals_natAdd {n m : ℕ} (α : Rn m) (i : Fin m) :
    leIntervals n α (Fin.natAdd n i) = Set.Iic (α i) := Fin.addCases_right i

/-- **Section 22** of [rockafellar1970convex], p. 202, the intervals of the system $x \ge 0$,
$Ax = a$. For $a = (\alpha_1, \dots, \alpha_m) \in \mathbb{R}^m$, the intervals are
$I_j = [0, +\infty)$ for $j = 1, \dots, n$ and $I_{n+i} = \{\alpha_i\}$ for $i = 1, \dots, m$. -/
def nonnegEqIntervals (n : ℕ) {m : ℕ} (α : Rn m) : Fin (n + m) → Set ℝ :=
  Fin.addCases (fun _ : Fin n => Set.Ici 0) fun i => {α i}

/-- The first $n$ intervals of the system $x \ge 0$, $Ax = a$ are $I_j = [0, +\infty)$. -/
@[simp] theorem nonnegEqIntervals_castAdd {n m : ℕ} (α : Rn m) (j : Fin n) :
    nonnegEqIntervals n α (Fin.castAdd m j) = Set.Ici 0 := Fin.addCases_left j

/-- The last $m$ intervals of the system $x \ge 0$, $Ax = a$ are $I_{n+i} = \{\alpha_i\}$. -/
@[simp] theorem nonnegEqIntervals_natAdd {n m : ℕ} (α : Rn m) (i : Fin m) :
    nonnegEqIntervals n α (Fin.natAdd n i) = {α i} := Fin.addCases_right i

/-- **Section 22** of [rockafellar1970convex], p. 202, the first interval reading. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear and $a = (\alpha_1, \dots, \alpha_m) \in
\mathbb{R}^m$. The system $Ax \le a$ has a solution $x \in \mathbb{R}^n$ if and only if the
subspace $L$ of $A$ meets the generalized rectangle of the intervals $I_j = (-\infty, +\infty)$,
$j \le n$, and $I_{n+i} = (-\infty, \alpha_i]$.

The second half of Section 22 is stated in terms of this correspondence. -/
theorem interval_reading_le (A : Rn n →ₗ[ℝ] Rn m) (α : Rn m) :
    (∃ x : Rn n, ∀ i, A x i ≤ α i) ↔
      ((intervalSubspace A : Set (Rn (n + m))) ∩ rectangle (leIntervals n α)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨intervalVector A x, ⟨x, rfl⟩, ?_⟩
    exact intervalVector_mem_rectangle.2 ⟨fun j => by simp, fun i => by simpa using hx i⟩
  · rintro ⟨z, ⟨x, rfl⟩, hz⟩
    exact ⟨x, fun i => by simpa using (intervalVector_mem_rectangle.1 hz).2 i⟩

/-- **Section 22** of [rockafellar1970convex], p. 202, the second interval reading. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear and $a = (\alpha_1, \dots, \alpha_m) \in
\mathbb{R}^m$. The system $x \ge 0$, $Ax = a$ has a solution $x \in \mathbb{R}^n$ if and only if
the subspace $L$ of $A$ meets the generalized rectangle of the intervals $I_j = [0, +\infty)$,
$j \le n$, and $I_{n+i} = \{\alpha_i\}$. -/
theorem interval_reading_nonneg_eq (A : Rn n →ₗ[ℝ] Rn m) (α : Rn m) :
    (∃ x : Rn n, (∀ j, 0 ≤ x j) ∧ A x = α) ↔
      ((intervalSubspace A : Set (Rn (n + m))) ∩ rectangle (nonnegEqIntervals n α)).Nonempty := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨intervalVector A x, ⟨x, rfl⟩, ?_⟩
    exact intervalVector_mem_rectangle.2 ⟨fun j => by simpa using hx j, fun i => by simp⟩
  · rintro ⟨z, ⟨x, rfl⟩, hz⟩
    obtain ⟨h1, h2⟩ := intervalVector_mem_rectangle.1 hz
    refine ⟨x, fun j => by simpa using h1 j, ?_⟩
    ext i
    simpa using h2 i

/-- The intervals of the system $Ax \le a$ are real intervals.

Therefore their rectangle is convex, which makes the alternative of Theorem 22.6 a separation
theorem. -/
theorem isRealInterval_leIntervals {n m : ℕ} (α : Rn m) (j : Fin (n + m)) :
    IsRealInterval (leIntervals n α j) := by
  refine Fin.addCases (fun j => ?_) (fun i => ?_) j
  · rw [leIntervals_castAdd]
    exact convex_univ
  · rw [leIntervals_natAdd]
    exact convex_Iic (α i)

/-- The intervals of the system $x \ge 0$, $Ax = a$ are real intervals. -/
theorem isRealInterval_nonnegEqIntervals {n m : ℕ} (α : Rn m) (j : Fin (n + m)) :
    IsRealInterval (nonnegEqIntervals n α j) := by
  refine Fin.addCases (fun j => ?_) (fun i => ?_) j
  · rw [nonnegEqIntervals_castAdd]
    exact convex_Ici (0 : ℝ)
  · rw [nonnegEqIntervals_natAdd]
    exact convex_singleton (α i)


end Rockafellar
