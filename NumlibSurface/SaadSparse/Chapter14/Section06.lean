/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Numlib.Eigen.MinMax
import NumlibSurface.SaadSparse.Chapter14.Section03

/-!
# Saad, Section 14.6: Graph partitioning

This module formalizes the partition and overlap definitions and the spectral analysis of
Section 14.6 of [saad2003iterative]. It uses Mathlib's graph Laplacian $L$. For a partition vector
$p$ with entries $\pm 1$, the quadratic form $p^T L p$ counts the edges that the partition cuts: it
is $4 n_c$, where $n_c$ is the number of cut edges. So bisection of a graph is the minimization of a
quadratic form over the vectors $p \in \{\pm 1\}^n$ with $(p, e) = 0$, where $e$ is the constant
vector. The continuous relaxation of this problem is a symmetric eigenvalue problem: the minimum of
the Rayleigh quotient of $L$ over the nonzero vectors orthogonal to $e$ is the second smallest
eigenvalue of $L$, attained at the Fiedler vector. This is the reason for Algorithm 14.7, whose
sorting and splitting step turns the minimizer back into a partition.

Sections 14.6.1 and 14.6.2 contribute the three numbered definitions of the section. Definition
14.13 is a map of the vertex set, a family of subsets that covers it; its subdomain spaces span the
whole space, which connects it to the Schwarz procedures of Section 14.3. Definitions 14.14 and
14.15 are the $k$-ply neighborhood system and the $(\alpha, k)$-overlap graph, the vocabulary of the
geometric separator theorem.

## Main definitions

* Definition 14.13, `SaadSparse.Chapter14.IsMap`: a family of subsets of the vertex set whose union
  is the whole set.
* Definition 14.13, `SaadSparse.Chapter14.IsProperMap`: a map whose subsets are pairwise disjoint.
* Definition 14.14, `SaadSparse.Chapter14.definition_14_14`: a $k$-ply neighborhood system of $n$
  closed disks in $\mathbb{R}^d$.
* Definition 14.15, `SaadSparse.Chapter14.definition_14_15`: the $(\alpha, k)$-overlap graph of a
  family of disks.

## Main results

* Definition 14.13, `SaadSparse.Chapter14.iSup_subdomainSpace_eq_top`: the subdomain spaces of a map
  span the whole space.
* Definition 14.14, `SaadSparse.Chapter14.definition_14_14_iff`: for disks of nonzero radius,
  "strictly interior" can be read as Mathlib's `interior` of the closed disk.
* Definition 14.15, `SaadSparse.Chapter14.definition_14_15_adj`: the edges of the overlap graph, as
  the book writes them.
* Section 14.6.3, `SaadSparse.Chapter14.lapMatrix_quadratic_partition`: for $p \in \{\pm 1\}^V$,
  $p^T L p$ is twice the number of ordered adjacent pairs that $p$ separates.
* Section 14.6.3, `SaadSparse.Chapter14.fiedlerVector`: for a connected graph, the minimum of the
  Rayleigh quotient of $L$ on the orthogonal complement of $e$ is the second smallest eigenvalue of
  $L$.

## Implementation notes

* The graph Laplacian is Mathlib's `SimpleGraph.lapMatrix`. As an operator on `EuclideanSpace ℝ V`
  it is `SaadSparse.Chapter14.lapOperator`.
* The eigenvalues of `Numlib.Eigen.MinMax` are indexed in decreasing order. So the second smallest
  of $m + 2$ eigenvalues has the index $m$.
* The vertex set of Definition 14.13 is the index set of the unknowns, so a map is a condition on
  the family $S$ of subsets of Section 14.3.1.

## Deviations from the source

* **§14.6.3, Laplacian sign** (correction). `SaadSparse.Chapter14.inner_lapOperator_self_nonneg`
  proves positive semidefiniteness for the displayed sign convention. The source says negative
  semidefinite, although its smallest-eigenvalue statement and Exercise 14.11 use the positive
  sign.
* **§14.6.3, Fiedler vector** (scope). `SaadSparse.Chapter14.fiedlerVector` characterizes the
  second smallest eigenvalue as the least Rayleigh quotient orthogonal to constants for a
  connected graph on at least two vertices. The statement makes no claim about the balance or
  output of the sign partition.
* **Definitions 14.13–14.15** (domain). `SaadSparse.Chapter14.IsMap` and
  `SaadSparse.Chapter14.IsProperMap` permit arbitrary families of subsets of a finite vertex
  set. `SaadSparse.Chapter14.definition_14_14` uses open balls for strict interior, and the
  equivalence with topological interiors of closed balls is stated for nonzero radii.
  `SaadSparse.Chapter14.definition_14_15` constructs a loopless graph for all $\alpha$ and ball
  families. The source assumes $\alpha\ge1$ and $k$-ply data and leaves distinctness implicit in
  the edge display.

## Not formalized

* **Theorem 14.16** (the geometric separator theorem of Miller, Teng, Thurston and Vavasis), stated
  over the $(\alpha, k)$-overlap graphs of `SaadSparse.Chapter14.definition_14_15`. The book quotes
  it without proof, and its proof needs stereographic projection into $S^d$, the existence of a
  centerpoint of a finite set, and an argument with a random great circle, none of which Mathlib
  has. The two definitions that it is stated over are formalized.
* **Coordinate and inertial bisection** (the rest of Section 14.6.2), **Section 14.6.4** (level-set
  expansion, the pseudo-peripheral node heuristic, recursive graph bisection, multinode expansion)
  and **Algorithms 14.7–14.10**. These are heuristics with no claim attached.
-/

open Finset Matrix

namespace SaadSparse.Chapter14

open Chapter12

/-! ### The minimum of the Rayleigh quotient on a hyperplane -/

section MinMax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Let $T$ be a symmetric operator on a real inner product space of dimension $m + 2$. Then on the
orthogonal complement of the eigenvector for the smallest eigenvalue, the Rayleigh quotient of
$T$ attains its minimum, and this minimum is the second smallest eigenvalue of $T$. -/
private theorem isLeast_rayleighQuotient_orthogonal_last {m : ℕ} {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = m + 2) :
    IsLeast {c : ℝ | ∃ x : E, x ≠ 0 ∧
        inner ℝ (hT.eigenvectorBasis hn (Fin.last (m + 1))) x = 0 ∧
        T.rayleighQuotient x = c}
      (hT.eigenvalues hn ⟨m, by omega⟩) := by
  set i : Fin (m + 2) := ⟨m, by omega⟩ with hi
  have hlast : (Fin.last (m + 1) : Fin (m + 2)) ≠ i := by
    simp [hi, Fin.ext_iff, Fin.last]
  constructor
  · refine ⟨hT.eigenvectorBasis hn i, hT.eigenvectorBasis_ne_zero hn i, ?_,
      hT.rayleighQuotient_eigenvectorBasis hn i⟩
    exact (hT.eigenvectorBasis hn).inner_eq_zero hlast
  · rintro c ⟨x, hx0, hxorth, rfl⟩
    refine hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn (s := Finset.Iic i) ?_ ?_ hx0
    · intro j hj
      exact hT.eigenvalues_antitone hn (Finset.mem_Iic.1 hj)
    · refine (hT.mem_eigenvectorSpan_iff hn).2 fun j hj => ?_
      have hjlast : j = Fin.last (m + 1) := by
        have hnot : ¬ j ≤ i := by simpa using hj
        have hj' : (i : ℕ) < (j : ℕ) := by
          simpa [Fin.le_def] using not_le.1 hnot
        have := j.isLt
        simp only [hi] at hj'
        exact Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hjlast, OrthonormalBasis.repr_apply_apply, hxorth]

end MinMax

/-! ### Section 14.6.3: The Laplacian quadratic form of a partition -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Section 14.6.3** of [saad2003iterative], the Laplacian quadratic form counts the cut. Let $G$
be a finite simple graph with Laplacian $L$, and let $p \in \mathbb{R}^V$ have all entries equal
to $1$ or $-1$. Then
$$p^T L p = 2 \cdot \#\{(u, v) \in V \times V : u \text{ and } v \text{ are adjacent and } p_u
  \ne p_v\}.$$

The set counts *ordered* pairs, so each cut edge appears twice, and the value is $4 n_c$ in the
notation of the book, where $n_c$ is the number of cut edges. The minimization of the number of
cut edges subject to $(p, e) = 0$, the condition that the two parts have the same size, is
therefore the minimization of a quadratic form over a discrete set. Its continuous relaxation is
`SaadSparse.Chapter14.fiedlerVector`. The quadratic form is
`Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) p p`.

**Reading.** Specializes quadratic form to sign vectors and counts ordered pairs, yielding four per
undirected cut edge.
-/
theorem lapMatrix_quadratic_partition {p : V → ℝ} (hp : ∀ i, p i = 1 ∨ p i = -1) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) p p
      = 2 * ({q ∈ (Finset.univ : Finset (V × V)) | G.Adj q.1 q.2 ∧ p q.1 ≠ p q.2}.card : ℝ) := by
  classical
  have key : ∀ i j : V, (if G.Adj i j then (p i - p j) ^ 2 else 0)
      = if G.Adj i j ∧ p i ≠ p j then (4 : ℝ) else 0 := by
    intro i j
    by_cases hadj : G.Adj i j
    · by_cases hne : p i = p j
      · simp [hadj, hne]
      · have h4 : (p i - p j) ^ 2 = 4 := by
          rcases hp i with h1 | h1 <;> rcases hp j with h2 | h2 <;> rw [h1, h2] <;>
            first
              | exact absurd (h1.trans h2.symm) hne
              | norm_num
        simp [hadj, hne, h4]
    · simp [hadj]
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  have hsum : (∑ i : V, ∑ j : V, if G.Adj i j then (p i - p j) ^ 2 else 0)
      = 4 * ({q ∈ (Finset.univ : Finset (V × V)) | G.Adj q.1 q.2 ∧ p q.1 ≠ p q.2}.card : ℝ) := by
    have h1 : (∑ i : V, ∑ j : V, if G.Adj i j then (p i - p j) ^ 2 else 0)
        = ∑ q : V × V, if G.Adj q.1 q.2 ∧ p q.1 ≠ p q.2 then (4 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum]
  ring

/-! ### Section 14.6.3: The Fiedler vector -/

/-- The graph Laplacian $L$ of $G$, as a linear operator on `EuclideanSpace ℝ V`. -/
noncomputable abbrev lapOperator : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  Matrix.toEuclideanLin (G.lapMatrix ℝ)

/-- The graph Laplacian $L$ is a symmetric operator. -/
theorem isSymmetric_lapOperator : (lapOperator G).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.2 (G.isHermitian_lapMatrix ℝ)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The constant vector $e = (1, \dots, 1)^T$ of Section 14.6.3 of [saad2003iterative]. Its
orthogonal complement is the constraint set of the bisection problem. -/
noncomputable def constVector (V : Type*) [Fintype V] : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun _ => (1 : ℝ)

/-- The constant vector is in the kernel of the graph Laplacian: $Le = 0$. This is the direction
that the bisection constraint $(p, e) = 0$ removes. -/
theorem lapOperator_constVector : lapOperator G (constVector V) = 0 := by
  refine WithLp.ofLp_injective 2 ?_
  have hconst : Matrix.mulVec (G.lapMatrix ℝ) (fun _ => (1 : ℝ)) = 0 := by
    ext i
    rw [SimpleGraph.lapMatrix_mulVec_apply]
    simp
  simpa [constVector, Matrix.toLpLin_apply] using hconst

/-- If the vertex set $V$ is nonempty, then the constant vector $e$ is nonzero. -/
theorem constVector_ne_zero (V : Type*) [Fintype V] [Nonempty V] : constVector V ≠ 0 := by
  intro h
  have := congrArg (fun z : EuclideanSpace ℝ V => WithLp.ofLp z (Classical.arbitrary V)) h
  simp [constVector] at this

/-- For every $x \in \mathbb{R}^V$, the Laplacian quadratic form is nonnegative: $(Lx, x) \ge 0$. It
is a sum of squares over the edges.

**Correction.** For the printed Laplacian, degree on the diagonal and $-1$ on edges give a
nonnegative quadratic form. The text describes it as negative semidefinite. -/
theorem inner_lapOperator_self_nonneg (x : EuclideanSpace ℝ V) :
    0 ≤ inner ℝ (lapOperator G x) x := by
  have h : inner ℝ (lapOperator G x) x
      = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (WithLp.ofLp x) (WithLp.ofLp x) := by
    rw [Matrix.toLinearMap₂'_apply', EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.toLpLin_apply]
  rw [h, SimpleGraph.lapMatrix_toLinearMap₂']
  positivity

/-- **Section 14.6.3** of [saad2003iterative], the Fiedler vector. Let $G$ be a connected graph on
$m + 2$ vertices, with Laplacian $L$ and constant vector $e$. Then the Rayleigh quotient
$(Lx, x)/(x, x)$ attains its minimum over the nonzero vectors $x$ with $(e, x) = 0$, and
$$\min_{x \ne 0, \ (e, x) = 0} \frac{(Lx, x)}{(x, x)} = \lambda_2(L),$$
the second smallest eigenvalue of $L$. A minimizer is a **Fiedler vector**.

This is the continuous relaxation of graph bisection, and Algorithm 14.7 computes it before it
sorts the entries and splits at the median. The eigenvalues of
`LinearMap.IsSymmetric.eigenvalues` are in decreasing order, so $\lambda_2(L)$ is the one with
index $m$. The number of vertices is given as `Module.finrank ℝ (EuclideanSpace ℝ V) = m + 2`.

**Scope.** The theorem gives the least Rayleigh quotient orthogonal to the constant vector on a
connected graph with at least two vertices. It does not formalize a sign partition or claim
that sign counts are balanced. -/
theorem fiedlerVector (hconn : G.Connected) {m : ℕ}
    (hn : Module.finrank ℝ (EuclideanSpace ℝ V) = m + 2) :
    IsLeast {c : ℝ | ∃ x : EuclideanSpace ℝ V, x ≠ 0 ∧ inner ℝ (constVector V) x = 0 ∧
        (lapOperator G).rayleighQuotient x = c}
      ((isSymmetric_lapOperator G).eigenvalues hn ⟨m, by omega⟩) := by
  classical
  have hL := isSymmetric_lapOperator G
  have hne : Nonempty V := hconn.nonempty
  -- the Rayleigh quotient of the Laplacian is nonnegative
  have hnonneg : ∀ x : EuclideanSpace ℝ V, x ≠ 0 → 0 ≤ (lapOperator G).rayleighQuotient x := by
    intro x hx
    have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    rw [LinearMap.rayleighQuotient]
    exact div_nonneg (by simpa using inner_lapOperator_self_nonneg G x) hpos.le
  -- and it vanishes at the constant vector, so the smallest eigenvalue is `0`
  have hR : (lapOperator G).rayleighQuotient (constVector V) = 0 := by
    rw [LinearMap.rayleighQuotient, lapOperator_constVector]
    simp
  have hzero : hL.eigenvalues hn (Fin.last (m + 1)) = 0 := by
    have hle : hL.eigenvalues hn (Fin.last (m + 1)) ≤ 0 := by
      have h := hL.le_rayleighQuotient_of_forall hn
        (fun i => hL.eigenvalues_antitone hn (Fin.le_last i)) (constVector_ne_zero V)
      rwa [hR] at h
    have hge : 0 ≤ hL.eigenvalues hn (Fin.last (m + 1)) := by
      rw [← hL.rayleighQuotient_eigenvectorBasis hn (Fin.last (m + 1))]
      exact hnonneg _ (hL.eigenvectorBasis_ne_zero hn _)
    linarith
  -- hence the last eigenvector is a nonzero multiple of the constant vector
  obtain ⟨c, hcne, hueq⟩ : ∃ c : ℝ, c ≠ 0 ∧
      hL.eigenvectorBasis hn (Fin.last (m + 1)) = c • constVector V := by
    have hker : lapOperator G (hL.eigenvectorBasis hn (Fin.last (m + 1))) = 0 := by
      rw [hL.apply_eigenvectorBasis hn (Fin.last (m + 1)), hzero]
      simp
    have h0 : Matrix.mulVec (G.lapMatrix ℝ)
        (WithLp.ofLp (hL.eigenvectorBasis hn (Fin.last (m + 1)))) = 0 := by
      have h : WithLp.ofLp (lapOperator G (hL.eigenvectorBasis hn (Fin.last (m + 1))))
          = (0 : V → ℝ) := by rw [hker]; rfl
      exact h
    have hconst := (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable G).1 h0
    refine ⟨WithLp.ofLp (hL.eigenvectorBasis hn (Fin.last (m + 1))) (Classical.arbitrary V),
      ?_, ?_⟩
    · intro h
      refine hL.eigenvectorBasis_ne_zero hn (Fin.last (m + 1)) ?_
      refine WithLp.ofLp_injective 2 ?_
      funext i
      simpa [h] using hconst i (Classical.arbitrary V) (hconn.preconnected _ _)
    · refine WithLp.ofLp_injective 2 ?_
      funext i
      simpa [constVector] using hconst i (Classical.arbitrary V) (hconn.preconnected _ _)
  -- orthogonality to the last eigenvector is orthogonality to the constant vector
  have hset : {c' : ℝ | ∃ x : EuclideanSpace ℝ V, x ≠ 0 ∧ inner ℝ (constVector V) x = 0 ∧
        (lapOperator G).rayleighQuotient x = c'}
      = {c' : ℝ | ∃ x : EuclideanSpace ℝ V, x ≠ 0 ∧
        inner ℝ (hL.eigenvectorBasis hn (Fin.last (m + 1))) x = 0 ∧
        (lapOperator G).rayleighQuotient x = c'} := by
    ext c'
    constructor <;> rintro ⟨x, hx0, hxo, rfl⟩ <;> refine ⟨x, hx0, ?_, rfl⟩
    · rw [hueq, real_inner_smul_left, hxo, mul_zero]
    · rw [hueq, real_inner_smul_left] at hxo
      exact (mul_eq_zero.1 hxo).resolve_left hcne
  rw [hset]
  exact isLeast_rayleighQuotient_orthogonal_last hL hn

/-! ### Section 14.6.1: Definition 14.13, a map of the vertex set -/

section Map

variable {n : ℕ} {ι : Type*}

/-- **Definition 14.13** of [saad2003iterative]. A family $S_i$, $i \in \iota$, of subsets of
$\{1, \dots, n\}$ is a **map** of the vertex set if its union is the whole set: every $j$ lies
in some $S_i$.

The vertex set of the book is the index set of the unknowns, so the family is the family $S$ of
Section 14.3.1, and the definition is the covering condition on it.

**Reading.** Cover via arbitrary index type of finite subsets of Fin n rather than an explicitly
finite list.
-/
def IsMap (S : ι → Finset (Fin n)) : Prop := ∀ j : Fin n, ∃ i, j ∈ S i

/-- **Definition 14.13** of [saad2003iterative], second part. A map $S_i$, $i \in \iota$, is a
**proper partition** if its subsets are pairwise disjoint; otherwise it is an overlapping
partition.

The Schwarz procedures of Section 14.3 are stated for the overlapping case. For a proper
partition they are block Jacobi and block Gauss–Seidel of Chapter 4.

**Reading.** Coverage plus pairwise disjointness for arbitrary index type.
-/
def IsProperMap (S : ι → Finset (Fin n)) : Prop :=
  IsMap S ∧ ∀ i i', i ≠ i' → Disjoint (S i) (S i')

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Definition 14.13** of [saad2003iterative], consequence. If the family $S_i$ is a map, then the
subdomain spaces $\operatorname{span}\{e_j : j \in S_i\}$ span $\mathbb{K}^n$:
$$\sum_i \operatorname{span}\{e_j : j \in S_i\} = \mathbb{K}^n.$$

This connects the combinatorial definition to the analytic hypotheses of Section 14.3. A family
that is not a map leaves some unknown untouched by every subdomain solve. So no Schwarz
procedure built on it can converge, and Assumption 1
(`SaadSparse.Chapter14.IsStableDecomposition`) fails. The subdomain space is
`SaadSparse.Chapter12.subdomainSpace`.

**Reading.** Additional consequence for algebraic coordinate subspaces of a cover.
-/
theorem iSup_subdomainSpace_eq_top {S : ι → Finset (Fin n)} (h : IsMap S) :
    ⨆ i, subdomainSpace 𝕜 (S i) = ⊤ := by
  refine top_unique ?_
  have hbasis : (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
      = Submodule.span 𝕜 (Set.range fun j : Fin n => EuclideanSpace.single j (1 : 𝕜)) := by
    have hb := (EuclideanSpace.basisFun (ι := Fin n) (𝕜 := 𝕜)).toBasis.span_eq
    rw [← hb]
    exact congrArg _ (congrArg Set.range (funext fun j => by
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]))
  rw [hbasis, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨i, hi⟩ := h j
  refine Submodule.mem_iSup_of_mem i ?_
  rw [subdomainSpace]
  exact Submodule.subset_span ⟨⟨j, hi⟩, rfl⟩

end Map

/-! ### Section 14.6.2: Definitions 14.14 and 14.15, neighborhood systems and overlap graphs -/

section Overlap

variable {d n : ℕ}

/-- **Definition 14.14** of [saad2003iterative]. A **$k$-ply neighborhood system** in $\mathbb{R}^d$
is a set of $n$ closed disks $D_1, \dots, D_n$ such that no point of $\mathbb{R}^d$ is strictly
interior to more than $k$ of them.

The disk $D_i$ is given by its centre $c_i$ and its radius $r_i$. "Strictly interior to $D_i$"
is membership in the open ball of centre $c_i$ and radius $r_i$, which is the interior of the
closed disk when $r_i \ne 0$; see `SaadSparse.Chapter14.definition_14_14_iff`.

**Reading.** Uses open balls for strict interior and total definition covering degenerate radii.
-/
def definition_14_14 (k : ℕ) (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin d), {i | x ∈ Metric.ball (c i) (r i)}.ncard ≤ k

/-- **Definition 14.14** of [saad2003iterative], with "strictly interior" read as Mathlib's
`interior`. Let $c_1, \dots, c_n \in \mathbb{R}^d$ and let $r_1, \dots, r_n$ be nonzero. Then
the disks form a $k$-ply neighborhood system if and only if no point of $\mathbb{R}^d$ lies in
the interior of more than $k$ of the closed disks $\bar{B}(c_i, r_i)$.

For a disk of nonzero radius, the open ball is the interior of the closed ball, so the two
readings of the condition agree.

**Reading.** Equates open balls and topological interiors of closed balls with explicit nonzero
radii.
-/
theorem definition_14_14_iff (k : ℕ) (c : Fin n → EuclideanSpace ℝ (Fin d)) {r : Fin n → ℝ}
    (hr : ∀ i, r i ≠ 0) :
    definition_14_14 k c r ↔
      ∀ x : EuclideanSpace ℝ (Fin d),
        {i | x ∈ interior (Metric.closedBall (c i) (r i))}.ncard ≤ k := by
  simp only [definition_14_14, interior_closedBall _ (hr _)]

/-- **Definition 14.15** of [saad2003iterative]. Let $\alpha \in \mathbb{R}$ and let
$D_1, \dots, D_n$ be closed disks in $\mathbb{R}^d$, with centres $c_i$ and radii $r_i$. The
**$(\alpha, k)$-overlap graph** has the vertex set $\{1, \dots, n\}$ and an edge $(i, j)$
exactly when
$$D_i \cap \alpha \cdot D_j \ne \emptyset \quad \text{and} \quad D_j \cap \alpha \cdot D_i \ne
  \emptyset,$$
where the dilation $\alpha \cdot D$ is the disk with the same centre and $\alpha$ times the
radius.

The book assumes $\alpha \ge 1$ and that the disks form a $k$-ply neighborhood system. Neither
condition enters the construction: they are the standing hypotheses under which Theorem 14.16
bounds the separator, and `SaadSparse.Chapter14.definition_14_14` states the second of them. The
graph is built with `SimpleGraph.fromRel`, so it has no loops.

**Reading.** Defines undirected loopless overlap graph for all α and arbitrary balls, without α≥1 or
k-ply prerequisites.
-/
def definition_14_15 (α : ℝ) (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j =>
    (Metric.closedBall (c i) (r i) ∩ Metric.closedBall (c j) (α * r j)).Nonempty ∧
      (Metric.closedBall (c j) (r j) ∩ Metric.closedBall (c i) (α * r i)).Nonempty

/-- **Definition 14.15** of [saad2003iterative], the edges. Vertices $i$ and $j$ of the
$(\alpha, k)$-overlap graph are adjacent if and only if $i \ne j$,
$D_i \cap \alpha \cdot D_j \ne \emptyset$ and $D_j \cap \alpha \cdot D_i \ne \emptyset$.

The edge set of the book is a subset of $V \times V$, and the condition that defines it is
already symmetric in $i$ and $j$. `SimpleGraph.fromRel` symmetrizes the condition and drops the
loops that it has at every $i$ whose disk is nonempty. So it adds nothing but the convention of
Section 3.3.2 that an adjacency graph has no loops.

**Reading.** Makes the distinct-vertex condition explicit in addition to both printed intersections.
-/
theorem definition_14_15_adj (α : ℝ) (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ)
    (i j : Fin n) :
    (definition_14_15 α c r).Adj i j ↔ i ≠ j ∧
      (Metric.closedBall (c i) (r i) ∩ Metric.closedBall (c j) (α * r j)).Nonempty ∧
        (Metric.closedBall (c j) (r j) ∩ Metric.closedBall (c i) (α * r i)).Nonempty := by
  rw [definition_14_15, SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ => or_iff_left_iff_imp.2 fun h => ⟨h.2, h.1⟩

end Overlap

end SaadSparse.Chapter14
