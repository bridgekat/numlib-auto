import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Numlib.Eigen.MinMax

/-!
# Saad §14.6: graph partitioning

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.6. Only §14.6.3, spectral bisection, carries a theorem, and it is a short one over
Mathlib's graph Laplacian.

* `lapMatrix_quadratic_partition` is the identity that makes graph bisection a quadratic
  minimization: for a partition vector `p` with entries `±1`, the Laplacian quadratic form
  `pᵀ L p` counts the edges the partition cuts.  The double sum counts each cut edge twice, so the
  value is `4 n_c` in Saad's notation, where `n_c` is the number of cut edges.
* `fiedlerVector` is its continuous relaxation, which is the reason for Algorithm 14.7: the
  minimum of the Rayleigh quotient of `L` over the nonzero vectors orthogonal to the constant
  vector `e` is the second smallest eigenvalue of `L`, attained at the Fiedler vector.  Minimizing
  the cut subject to `(p, e) = 0` over `±1` vectors is thereby relaxed to a symmetric eigenvalue
  problem, and the sorting-and-splitting step of the algorithm turns the minimizer back into a
  partition.

## Not formalized here

Definitions 14.13 (a map of a vertex set), 14.14 (`k`-ply neighborhood systems) and 14.15
(`(α, k)`-overlap graphs) exist only to state Theorem 14.16, the geometric separator theorem of
Miller, Teng, Thurston and Vavasis, which Saad quotes without proof.  §14.6.2 (coordinate and
inertial bisection), §14.6.4 (level-set expansion, the pseudo-peripheral node heuristic, recursive
graph bisection, multinode expansion) and Algorithms 14.7–14.10 are heuristics with no claim
attached.
-/

open Finset Matrix

namespace SaadSparse.Chapter14

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

theorem isSymmetric_lapOperator : (lapOperator G).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.2 (G.isHermitian_lapMatrix ℝ)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The constant vector `e` of §14.6.3, whose orthogonal complement is the constraint set of the
bisection problem. -/
noncomputable def constVector (V : Type*) [Fintype V] : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun _ => (1 : ℝ)

theorem lapOperator_constVector : lapOperator G (constVector V) = 0 := by
  refine WithLp.ofLp_injective 2 ?_
  have hconst : Matrix.mulVec (G.lapMatrix ℝ) (fun _ => (1 : ℝ)) = 0 := by
    ext i
    rw [SimpleGraph.lapMatrix_mulVec_apply]
    simp
  simpa [constVector, Matrix.toLpLin_apply] using hconst

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

end SaadSparse.Chapter14
