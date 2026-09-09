import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Numlib.Eigen.MinMax
import NumlibSurface.SaadSparse.Chapter14.Section03

/-!
# Saad §14.6: graph partitioning

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.6. Only §14.6.3, spectral bisection, carries a theorem, and it is a short one over
Mathlib's graph Laplacian; §14.6.1 and §14.6.2 contribute the three definitions the chapter numbers.

* `lapMatrix_quadratic_partition` is the identity that makes graph bisection a quadratic
  minimization: for a partition vector `p` with entries `±1`, the Laplacian quadratic form
  `pᵀ L p` counts the edges the partition cuts.  The double sum counts each cut edge twice, so the
  value is `4 n_c` in Saad's notation, where `n_c` is the number of cut edges.
* `IsMap` and `IsProperMap` are Definition 14.13, the covering family of subsets and the
  distinction between a proper and an overlapping partition, and `iSup_subdomainSpace_eq_top` is
  what the definition buys here: the subdomain spaces of a map span the whole space, so a family
  that is not a map leaves an unknown untouched by every subdomain solve and Assumption 1 of
  §14.3.4 fails outright.
* `definition_14_14` and `definition_14_15` are the `k`-ply neighborhood system and the
  `(α, k)`-overlap graph of §14.6.2, the vocabulary of the geometric separator theorem: `n` closed
  disks of which no point of `ℝ^d` is strictly interior to more than `k`, and the graph joining
  two disks that each meet the `α`-dilation of the other.  `definition_14_14_iff` reads "strictly
  interior" as Mathlib's `interior`, and `definition_14_15_adj` writes the edge set out.
* `fiedlerVector` is its continuous relaxation, which is the reason for Algorithm 14.7: the
  minimum of the Rayleigh quotient of `L` over the nonzero vectors orthogonal to the constant
  vector `e` is the second smallest eigenvalue of `L`, attained at the Fiedler vector.  Minimizing
  the cut subject to `(p, e) = 0` over `±1` vectors is thereby relaxed to a symmetric eigenvalue
  problem, and the sorting-and-splitting step of the algorithm turns the minimizer back into a
  partition.

## Not formalized here

Theorem 14.16, the geometric separator theorem of Miller, Teng, Thurston and Vavasis, over the
`(α, k)`-overlap graphs `definition_14_15` builds.  Saad quotes it without proof, and its proof
needs stereographic projection into `S^d`, the existence of a centerpoint of a finite set and a
random-great-circle argument — none of which Mathlib has.  The two definitions it is stated over
are geometry and are given above; the theorem itself is the piece that is out of reach.

The rest of §14.6.2 (coordinate and inertial bisection), §14.6.4 (level-set expansion, the
pseudo-peripheral node heuristic, recursive graph bisection, multinode expansion) and Algorithms
14.7–14.10 are heuristics with no claim attached.
-/

open Finset Matrix

namespace SaadSparse.Chapter14

open Chapter12

/-! ### The minimum of the Rayleigh quotient on a hyperplane -/

section MinMax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dual of `LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`: on the orthogonal
complement of the *last* eigenvector — the one for the smallest eigenvalue — the Rayleigh quotient
attains its minimum, and that minimum is the second smallest eigenvalue.  The eigenvalues of
`Numlib/Eigen/MinMax.lean` are indexed in decreasing order, so the second smallest of `m + 2` of
them is the one of index `m`. -/
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

/-! ### §14.6.3: the Laplacian quadratic form of a partition -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The Laplacian quadratic form counts the cut** (§14.6.3).  For a partition vector `p` whose
entries are `±1`, `pᵀ L p` is twice the number of *ordered* pairs of adjacent vertices that the
partition separates, that is `4 n_c` in Saad's notation, where `n_c` counts the cut edges
themselves.  Minimizing the number of cut edges subject to `(p, e) = 0` — the constraint that the
two parts have equal size — is therefore the minimization of a quadratic form over a discrete
set, whose continuous relaxation is `SaadSparse.Chapter14.fiedlerVector`. -/
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

/-! ### §14.6.3: the Fiedler vector -/

/-- The graph Laplacian as a symmetric operator on `EuclideanSpace ℝ V`. -/
noncomputable abbrev lapOperator : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  Matrix.toEuclideanLin (G.lapMatrix ℝ)

/-- The graph Laplacian is a symmetric operator. -/
theorem isSymmetric_lapOperator : (lapOperator G).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.2 (G.isHermitian_lapMatrix ℝ)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The constant vector `e` of §14.6.3, whose orthogonal complement is the constraint set of the
bisection problem. -/
noncomputable def constVector (V : Type*) [Fintype V] : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun _ => (1 : ℝ)

/-- §14.6.3: the constant vector spans the kernel direction the bisection constraint removes,
`L e = 0`. -/
theorem lapOperator_constVector : lapOperator G (constVector V) = 0 := by
  refine WithLp.ofLp_injective 2 ?_
  have hconst : Matrix.mulVec (G.lapMatrix ℝ) (fun _ => (1 : ℝ)) = 0 := by
    ext i
    rw [SimpleGraph.lapMatrix_mulVec_apply]
    simp
  simpa [constVector, Matrix.toLpLin_apply] using hconst

/-- The constant vector of a nonempty vertex set is nonzero. -/
theorem constVector_ne_zero (V : Type*) [Fintype V] [Nonempty V] : constVector V ≠ 0 := by
  intro h
  have := congrArg (fun z : EuclideanSpace ℝ V => WithLp.ofLp z (Classical.arbitrary V)) h
  simp [constVector] at this

/-- The Laplacian quadratic form is a sum of squares over the edges, hence nonnegative. -/
theorem inner_lapOperator_self_nonneg (x : EuclideanSpace ℝ V) :
    0 ≤ inner ℝ (lapOperator G x) x := by
  have h : inner ℝ (lapOperator G x) x
      = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (WithLp.ofLp x) (WithLp.ofLp x) := by
    rw [Matrix.toLinearMap₂'_apply', EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.toLpLin_apply]
  rw [h, SimpleGraph.lapMatrix_toLinearMap₂']
  positivity

/-- **The Fiedler vector** (§14.6.3), the continuous relaxation of graph bisection.  For a
connected graph on `m + 2` vertices, the minimum of the Rayleigh quotient of the Laplacian over
the nonzero vectors orthogonal to the constant vector `e` is attained, and equals the second
smallest eigenvalue of the Laplacian; a minimizer is a Fiedler vector.  This is what Algorithm
14.7 computes before sorting its entries and splitting at the median. -/
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

/-! ### §14.6.1: Definition 14.13, a map of the vertex set -/

section Map

variable {n : ℕ} {ι : Type*}

/-- **Definition 14.13**: a *map* of the vertex set is a family of subsets `V_1, …, V_s` whose
union is the whole set.  The book's vertex set is the index set of the unknowns, so the family here
is the family `S` of §14.3.1 and the definition is the covering condition on it. -/
def IsMap (S : ι → Finset (Fin n)) : Prop := ∀ j : Fin n, ∃ i, j ∈ S i

/-- **Definition 14.13**, second half: the map is a *proper partition* when the subsets are
pairwise disjoint, and an *overlapping partition* otherwise.  §14.3's Schwarz procedures are stated
for the overlapping case, and a proper partition is the block Jacobi / block Gauss–Seidel of
Chapter 4. -/
def IsProperMap (S : ι → Finset (Fin n)) : Prop :=
  IsMap S ∧ ∀ i i', i ≠ i' → Disjoint (S i) (S i')

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **What Definition 14.13 buys**: the subdomain spaces of a map span the whole space.  This is the
bridge between Saad's combinatorial vocabulary and the analytic hypotheses of §14.3 — a family that
is not a map leaves some unknown untouched by every subdomain solve, so no Schwarz procedure built
on it can converge, and Assumption 1 (`IsStableDecomposition`) fails outright. -/
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

/-! ### §14.6.2: Definitions 14.14 and 14.15, neighborhood systems and overlap graphs -/

section Overlap

variable {d n : ℕ}

/-- **Definition 14.14**: a *`k`-ply neighborhood system* in `ℝ^d` is a set of `n` closed disks
`D_1, …, D_n` such that no point of `ℝ^d` is strictly interior to more than `k` of them.

A closed disk is given by its centre `c i` and its radius `r i`, and "strictly interior to `D_i`"
is membership in the open ball, which is the interior of the closed one — `definition_14_14_iff`.
-/
def definition_14_14 (k : ℕ) (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin d), {i | x ∈ Metric.ball (c i) (r i)}.ncard ≤ k

/-- Definition 14.14 with "strictly interior" read as Mathlib's `interior`: for disks of nonzero
radius the open ball is the interior of the closed ball, so the two readings of the condition
agree. -/
theorem definition_14_14_iff (k : ℕ) (c : Fin n → EuclideanSpace ℝ (Fin d)) {r : Fin n → ℝ}
    (hr : ∀ i, r i ≠ 0) :
    definition_14_14 k c r ↔
      ∀ x : EuclideanSpace ℝ (Fin d),
        {i | x ∈ interior (Metric.closedBall (c i) (r i))}.ncard ≤ k := by
  simp only [definition_14_14, interior_closedBall _ (hr _)]

/-- **Definition 14.15**: for `α ≥ 1` and a `k`-ply neighborhood system `D_1, …, D_n`, the
*`(α, k)`-overlap graph* has vertex set `{1, …, n}` and an edge `(i, j)` exactly when
`D_i ∩ α·D_j ≠ ∅` and `D_j ∩ α·D_i ≠ ∅`, the dilation `α·D` being the disk with the same centre
and `α` times the radius.

Neither `1 ≤ α` nor the `k`-ply condition enters the construction: they are the standing hypotheses
under which Theorem 14.16 bounds the separator, and `definition_14_14` states the second of them.
-/
def definition_14_15 (α : ℝ) (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j =>
    (Metric.closedBall (c i) (r i) ∩ Metric.closedBall (c j) (α * r j)).Nonempty ∧
      (Metric.closedBall (c j) (r j) ∩ Metric.closedBall (c i) (α * r i)).Nonempty

/-- The edges of the `(α, k)`-overlap graph, as the book writes them.  The book's edge set is a
subset of `V × V`, and the condition cutting it out is already symmetric in `i` and `j`; so
`SimpleGraph.fromRel`, which symmetrizes and drops the loops the condition carries at every `i`
whose disk is nonempty, adds nothing but the loopless convention of §3.3.2's adjacency graph. -/
theorem definition_14_15_adj (α : ℝ) (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ)
    (i j : Fin n) :
    (definition_14_15 α c r).Adj i j ↔ i ≠ j ∧
      (Metric.closedBall (c i) (r i) ∩ Metric.closedBall (c j) (α * r j)).Nonempty ∧
        (Metric.closedBall (c j) (r j) ∩ Metric.closedBall (c i) (α * r i)).Nonempty := by
  rw [definition_14_15, SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ => or_iff_left_iff_imp.2 fun h => ⟨h.2, h.1⟩

end Overlap

end SaadSparse.Chapter14
