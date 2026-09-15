import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SimpleGraph.Finite
import Numlib.LinearAlgebra.Matrix.MMatrix
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section13

/-!
# Quarteroni–Sacco–Saleri §3.14: applications

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.14, over the backbone `Numlib/LinearAlgebra/Matrix/MMatrix`
(M-matrices, `Matrix.IsMMatrix`, the criterion
`Matrix.isMMatrix_of_isIrreduciblyDiagDominant` and the discrete maximum principle
`Matrix.IsMMatrix.nonneg_of_mulVec_nonneg`) and `Numlib/LinearAlgebra/Matrix/DiagDominant`
(irreducible diagonal dominance `Matrix.IsIrreduciblyDiagDominant` and the Gershgorin argument).

§3.14.1, the nodal analysis of a structured frame, is a MATLAB experiment with the reorderings of
§3.9 and states no result; §3.14.2 states one, that the matrix of the barycentric regularization
system (3.78) is symmetric positive definite and an M-matrix.

## Conventions

The triangulation enters only through its *node graph*: the vertices are the grid nodes, split as
`Fin n ⊕ Fin p` into the `n` interior nodes `N_h` and the `p` boundary nodes, and `G.Adj` is the
relation "`x_j` belongs to the patch `Z_i` of `x_i`". The book's `n_i = dim(Z_i)` is then
`G.degree (Sum.inl i)`, counting boundary neighbours too, and the matrix of (3.78) is
`regularizationMatrix G ∈ ℝ^{n×n}`, of order `N - N_b`: `n_i` on the diagonal, `-1` at an interior
neighbour, `0` elsewhere. The right-hand side collects the fixed boundary coordinates `z_j^{∂D}`
of the boundary neighbours.

The hypotheses are the book's, made explicit: the interior node graph is connected
(`(G.comap Sum.inl).Reachable`), and at least one interior node has a boundary neighbour. Without
the second the system is singular (the constant vector is in the kernel); without the first the
statement holds on each connected component separately.

## Contents

* `regularizationMatrix`, `regularizationMatrix_apply` — the matrix of (3.78).
* `posSemidef_of_isDiagDominant` — Gershgorin for the weak form of diagonal dominance.
* `equation_3_78` — the system, the symmetry, the M-matrix property, positive definiteness and
  the discrete maximum principle.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

/-! ### A Hermitian weakly diagonally dominant matrix is positive semidefinite -/

open scoped ComplexOrder in
-- TODO(backbone): belongs beside `Matrix.IsStrictDiagDominant.posDef` in
-- `Numlib/LinearAlgebra/Matrix/DiagDominant`, as `Matrix.IsDiagDominant.posSemidef`.
/-- A Hermitian, weakly row diagonally dominant matrix with nonnegative diagonal is positive
semidefinite: by Gershgorin's theorem every eigenvalue lies in a disc centred at some `a_kk ≥ 0`
of radius `∑_{j ≠ k} |a_kj| ≤ a_kk`, hence is nonnegative. It is the weak companion of the
backbone's `Matrix.IsStrictDiagDominant.posDef`; combined with nonsingularity
(`Matrix.PosSemidef.posDef_iff_isUnit`) it gives positive definiteness. -/
theorem posSemidef_of_isDiagDominant {𝕜 : Type*} [RCLike 𝕜] {N : Type*} [Fintype N]
    [DecidableEq N] {A : Matrix N N 𝕜} (hA : A.IsHermitian) (hd : A.IsDiagDominant)
    (hpos : ∀ i, 0 ≤ RCLike.re (A i i)) : A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  intro i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i : 𝕜) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⇑(hA.eigenvectorBasis i)) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, toLin'_apply, hA.mulVec_eigenvectorBasis,
        RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    · exact fun h => hA.eigenvectorBasis.orthonormal.ne_zero i ((WithLp.ofLp_eq_zero 2).mp h)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have hle := hk.trans (hd k)
  rw [← hA.coe_re_apply_self k, ← RCLike.ofReal_sub, RCLike.norm_ofReal, RCLike.norm_ofReal,
    abs_of_nonneg (hpos k)] at hle
  have h := (abs_le.mp hle).1
  simp only [Pi.zero_apply]
  linarith

/-! ### §3.14.2: the barycentric regularization of a triangular grid -/

section Regularization

variable {n p : ℕ} (G : SimpleGraph (Fin n ⊕ Fin p)) [DecidableRel G.Adj]

/-- **(3.78), the matrix of the barycentric regularization system.** The grid nodes are
`Fin n ⊕ Fin p`, the interior nodes `N_h` on the left and the fixed boundary nodes on the right,
and `G.Adj x y` says that `y` belongs to the patch `Z_x` of `x`. The `i`-th row of the system
`n_i z_i - ∑_{z_j ∈ Z_i ∩ N_h} z_j = ∑_{z_j ∈ Z_i ∩ ∂D} z_j^{∂D}` has matrix entries
`a_ii = n_i = dim(Z_i)`, `a_ij = -1` for an interior `z_j ∈ Z_i`, and `a_ij = 0` otherwise. -/
def regularizationMatrix : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then (G.degree (Sum.inl i) : ℝ)
    else if G.Adj (Sum.inl i) (Sum.inl j) then -1 else 0

/-- The entries of the matrix of (3.78). -/
@[simp]
theorem regularizationMatrix_apply (i j : Fin n) :
    regularizationMatrix G i j =
      if i = j then (G.degree (Sum.inl i) : ℝ)
      else if G.Adj (Sum.inl i) (Sum.inl j) then -1 else 0 := rfl

/-- The pattern of the matrix of (3.78) is irreducible when the interior node graph is connected:
a walk between two interior nodes is a chain of nonzero entries, and the positive diagonal closes
it into one of positive length. -/
private theorem isPatternIrreducible_regularizationMatrix
    (hconn : ∀ i j : Fin n, (G.comap Sum.inl).Reachable i j)
    (hdiag : ∀ i : Fin n, 0 < regularizationMatrix G i i) :
    (regularizationMatrix G).IsPatternIrreducible := by
  set B := (regularizationMatrix G).map fun x : ℝ => ‖x‖ with hB
  have hBnn : ∀ i j, 0 ≤ B i j := fun i j => by rw [hB, map_apply]; exact norm_nonneg _
  have hBdiag : ∀ i, 0 < B i i := fun i => by
    rw [hB, map_apply]
    exact norm_pos_iff.2 (hdiag i).ne'
  have hBpow : ∀ (k : ℕ) (i j : Fin n), 0 ≤ (B ^ k) i j := by
    intro k
    induction k with
    | zero =>
      intro i j
      rw [pow_zero]
      by_cases hij : i = j
      · rw [hij, one_apply_eq]; norm_num
      · rw [one_apply_ne hij]
    | succ k ih =>
      intro i j
      rw [pow_succ, mul_apply]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (ih i x) (hBnn x j)
  have hBadj : ∀ u v : Fin n, G.Adj (Sum.inl u) (Sum.inl v) → 0 < B u v := by
    intro u v hadj
    rw [hB, map_apply, regularizationMatrix_apply,
      ite_eq_right fun h => hadj.ne (congrArg Sum.inl h), ite_eq_left hadj]
    norm_num
  have hwalk : ∀ {i j : Fin n}, (G.comap Sum.inl).Walk i j → ∃ k, 0 < (B ^ k) i j := by
    intro i j w
    induction w with
    | nil => exact ⟨0, by rw [pow_zero, one_apply_eq]; norm_num⟩
    | @cons u v _ hadj _ ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [pow_succ']
      exact mul_apply_pos_of_pos_of_pos hBnn (hBpow k) (hBadj u v hadj) hk
  refine isPatternIrreducible_iff_exists_pow_pos.2 fun i j => ?_
  obtain ⟨w⟩ := hconn i j
  obtain ⟨k, hk⟩ := hwalk w
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  change 0 < (B ^ (k + 1)) i j
  rw [pow_succ]
  exact mul_apply_pos_of_pos_of_pos (hBpow k) hBnn hk (hBdiag j)

/-- **(3.78).** Let the interior node graph be connected and let at least one interior node have a
boundary neighbour — the hypothesis the book leaves implicit, without which the constant vector is
in the kernel. Then the matrix `A` of (3.78) is symmetric, it is an M-matrix
(`Matrix.isMMatrix_of_isIrreduciblyDiagDominant`: it is irreducibly diagonally dominant, with
positive diagonal and nonpositive off-diagonal entries), and it is positive definite. The system
`A z = b`, with `b_i` the sum of the fixed coordinates of the boundary nodes of the patch `Z_i`,
says exactly that every interior node is the centre of gravity of its patch, and the M-matrix
property gives the discrete maximum principle `A z ≥ 0 ⟹ z ≥ 0` — the new grid coordinates take
values between the minimum and the maximum attained on the boundary. -/
theorem equation_3_78 (hconn : ∀ i j : Fin n, (G.comap Sum.inl).Reachable i j)
    (hbdry : ∃ (i : Fin n) (q : Fin p), G.Adj (Sum.inl i) (Sum.inr q)) :
    (∀ (z : Fin n → ℝ) (i : Fin n),
        (regularizationMatrix G *ᵥ z) i = (G.degree (Sum.inl i) : ℝ) * z i -
          ∑ j ∈ univ.filter fun j => G.Adj (Sum.inl i) (Sum.inl j), z j) ∧
      (∀ (z : Fin n → ℝ) (zb : Fin p → ℝ),
        (regularizationMatrix G *ᵥ z =
            fun i => ∑ q ∈ univ.filter fun q => G.Adj (Sum.inl i) (Sum.inr q), zb q) ↔
          ∀ i, (G.degree (Sum.inl i) : ℝ) * z i =
            (∑ j ∈ univ.filter fun j => G.Adj (Sum.inl i) (Sum.inl j), z j) +
              ∑ q ∈ univ.filter fun q => G.Adj (Sum.inl i) (Sum.inr q), zb q) ∧
      (regularizationMatrix G).IsSymm ∧ (regularizationMatrix G).IsMMatrix ∧
        (regularizationMatrix G).PosDef ∧
        ∀ z : Fin n → ℝ, 0 ≤ regularizationMatrix G *ᵥ z → 0 ≤ z := by
  -- the rows of the system
  have hrow : ∀ (z : Fin n → ℝ) (i : Fin n),
      (regularizationMatrix G *ᵥ z) i = (G.degree (Sum.inl i) : ℝ) * z i -
        ∑ j ∈ univ.filter fun j => G.Adj (Sum.inl i) (Sum.inl j), z j := by
    intro z i
    rw [mulVec_apply_eq_sum]
    have hterm : ∀ j : Fin n, regularizationMatrix G i j * z j =
        (if i = j then (G.degree (Sum.inl i) : ℝ) * z j else 0) +
          if G.Adj (Sum.inl i) (Sum.inl j) then -z j else 0 := by
      intro j
      rw [regularizationMatrix_apply]
      rcases eq_or_ne i j with rfl | hij
      · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right G.irrefl, add_zero]
      · rw [ite_eq_right hij, ite_eq_right hij, zero_add]
        split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (mem_univ i), ← Finset.sum_filter, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  -- the entries off the diagonal
  have hoff : ∀ i j : Fin n, i ≠ j → regularizationMatrix G i j ≤ 0 := by
    intro i j hij
    rw [regularizationMatrix_apply, ite_eq_right hij]
    split_ifs <;> norm_num
  -- every interior node has a neighbour
  have hdegpos : ∀ i : Fin n, 0 < G.degree (Sum.inl i) := by
    intro i
    obtain ⟨i₀, q, hq⟩ := hbdry
    rcases eq_or_ne i i₀ with rfl | hne
    · exact (G.degree_pos_iff_exists_adj _).2 ⟨Sum.inr q, hq⟩
    · obtain ⟨w⟩ := hconn i i₀
      cases w with
      | nil => exact absurd rfl hne
      | cons hadj _ => exact (G.degree_pos_iff_exists_adj _).2 ⟨_, hadj⟩
  have hdiag : ∀ i : Fin n, 0 < regularizationMatrix G i i := by
    intro i
    rw [regularizationMatrix_apply, ite_eq_left rfl]
    exact_mod_cast hdegpos i
  -- the row sums off the diagonal count the interior neighbours
  have hrowsum : ∀ i : Fin n, ∑ j ∈ univ.erase i, ‖regularizationMatrix G i j‖ =
      (#(univ.filter fun j : Fin n => G.Adj (Sum.inl i) (Sum.inl j)) : ℝ) := by
    intro i
    have hcong : ∀ j ∈ univ.erase i, ‖regularizationMatrix G i j‖ =
        if G.Adj (Sum.inl i) (Sum.inl j) then (1 : ℝ) else 0 := by
      intro j hj
      rw [regularizationMatrix_apply, ite_eq_right (mem_erase.1 hj).1.symm]
      split_ifs <;> norm_num
    have hfilter : ((univ.erase i).filter fun j : Fin n => G.Adj (Sum.inl i) (Sum.inl j)) =
        univ.filter fun j : Fin n => G.Adj (Sum.inl i) (Sum.inl j) := by
      ext j
      simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
      exact ⟨fun h => h.2, fun h => ⟨fun hji => h.ne' (congrArg Sum.inl hji), h⟩⟩
    rw [Finset.sum_congr rfl hcong, Finset.sum_boole, hfilter]
  -- the interior neighbours are at most all the neighbours
  have hcard : ∀ i : Fin n,
      #(univ.filter fun j : Fin n => G.Adj (Sum.inl i) (Sum.inl j)) ≤ G.degree (Sum.inl i) := by
    intro i
    refine Finset.card_le_card_of_injOn Sum.inl (fun j hj => ?_) fun _ _ _ _ h =>
      Sum.inl_injective h
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 (by simpa using hj)
  have hdom : (regularizationMatrix G).IsDiagDominant := by
    intro i
    rw [hrowsum i, regularizationMatrix_apply, ite_eq_left rfl, Real.norm_natCast]
    exact_mod_cast hcard i
  -- at a node with a boundary neighbour the dominance is strict
  have hstrict : ∃ i, ∑ j ∈ univ.erase i, ‖regularizationMatrix G i j‖ <
      ‖regularizationMatrix G i i‖ := by
    obtain ⟨i₀, q, hq⟩ := hbdry
    refine ⟨i₀, ?_⟩
    rw [hrowsum i₀, regularizationMatrix_apply, ite_eq_left rfl, Real.norm_natCast]
    have hss : ((univ.filter fun j : Fin n => G.Adj (Sum.inl i₀) (Sum.inl j)).image Sum.inl) ⊂
        G.neighborFinset (Sum.inl i₀) := by
      refine (Finset.ssubset_iff_of_subset fun x hx => ?_).2
        ⟨Sum.inr q, (SimpleGraph.mem_neighborFinset _ _ _).2 hq, by simp⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 (by simpa using hj)
    have hlt := Finset.card_lt_card hss
    rw [Finset.card_image_of_injective _ Sum.inl_injective] at hlt
    exact_mod_cast hlt
  have hIDD : (regularizationMatrix G).IsIrreduciblyDiagDominant :=
    ⟨isPatternIrreducible_regularizationMatrix G hconn hdiag, hdom, hstrict⟩
  have hMM : (regularizationMatrix G).IsMMatrix :=
    isMMatrix_of_isIrreduciblyDiagDominant hIDD hdiag hoff
  -- symmetry and positive definiteness
  have hsymm : (regularizationMatrix G).IsSymm := by
    ext i j
    rw [transpose_apply]
    simp only [regularizationMatrix_apply]
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · rw [ite_eq_right hij.symm, ite_eq_right hij]
      by_cases hadj : G.Adj (Sum.inl i) (Sum.inl j)
      · rw [ite_eq_left hadj.symm, ite_eq_left hadj]
      · rw [ite_eq_right fun h => hadj h.symm, ite_eq_right hadj]
  have hHerm : (regularizationMatrix G).IsHermitian := by
    change (regularizationMatrix G)ᴴ = regularizationMatrix G
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  have hPD : (regularizationMatrix G).PosDef :=
    (Matrix.PosSemidef.posDef_iff_isUnit
      (posSemidef_of_isDiagDominant hHerm hdom fun i => by simp)).2 hMM.isUnit
  refine ⟨hrow, fun z zb => ?_, hsymm, hMM, hPD, fun z hz => hMM.nonneg_of_mulVec_nonneg hz⟩
  rw [funext_iff]
  exact forall_congr' fun i => by rw [hrow z i, sub_eq_iff_eq_add, add_comm]

end Regularization

end QuarteroniSaccoSaleri.Chapter03
