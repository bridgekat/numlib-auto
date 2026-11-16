/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SimpleGraph.Finite
import Numlib.LinearAlgebra.Matrix.MMatrix
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section13

/-!
# Quarteroni, Sacco and Saleri, Section 3.14: Applications

This module formalizes Section 3.14 of [quarteroni2000numerical]. Section 3.14.2 regularizes a
triangular grid: each interior node $z_i$ is moved to the centre of gravity of its patch $Z_i$, the
set of nodes adjacent to it, while the boundary nodes stay fixed. This gives the linear system
(3.78)
$$n_i z_i - \sum_{z_j \in Z_i \cap N_h} z_j = \sum_{z_j \in Z_i \cap \partial D} z_j^{\partial D},
  \qquad z_i \in N_h,$$
where $N_h$ is the set of interior nodes and $n_i$ is the number of nodes in $Z_i$. The module
proves the result that the section states: the matrix of (3.78) is symmetric positive definite and
an M-matrix. The M-matrix property gives the discrete maximum principle
$Az \ge 0 \Rightarrow z \ge 0$.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.MMatrix` (M-matrices
`Matrix.IsMMatrix`, the criterion `Matrix.isMMatrix_of_isIrreduciblyDiagDominant` and the discrete
maximum principle `Matrix.IsMMatrix.nonneg_of_mulVec_nonneg`) and
`Numlib.LinearAlgebra.Matrix.DiagDominant` (irreducible diagonal dominance
`Matrix.IsIrreduciblyDiagDominant`).

## Main definitions

* Equation (3.78), `QuarteroniSaccoSaleri.Chapter03.regularizationMatrix`: the matrix of the
  barycentric regularization system, with $n_i$ on the diagonal and $-1$ at each interior neighbour.

## Main results

* Equation (3.78), `QuarteroniSaccoSaleri.Chapter03.regularizationMatrix_apply`: the formula for the
  entries of the matrix.
* Equation (3.78), `QuarteroniSaccoSaleri.Chapter03.equation_3_78`: the system says that each
  interior node is the centre of gravity of its patch, and its matrix is symmetric, an M-matrix and
  positive definite, so that the discrete maximum principle holds.

## Conventions

* The triangulation enters only through its node graph `G : SimpleGraph (Fin n ⊕ Fin p)`. The
  vertices are the grid nodes: the $n$ interior nodes `Sum.inl i` and the $p$ boundary nodes
  `Sum.inr q`. The relation `G.Adj x y` says that $y$ belongs to the patch $Z_x$ of $x$.
* The book's $n_i = \dim(Z_i)$ is `G.degree (Sum.inl i)`. It counts boundary neighbours too.
* The matrix of (3.78) is `QuarteroniSaccoSaleri.Chapter03.regularizationMatrix G`, of order
  $n = N - N_b$. The right-hand side collects the fixed boundary coordinates $z_j^{\partial D}$ of
  the boundary neighbours.

## Deviations from the source

* **Equation (3.78)** (reading). The book leaves the hypotheses implicit. The statement assumes that
  the graph of the interior nodes is connected and that at least one interior node has a boundary
  neighbour. See `QuarteroniSaccoSaleri.Chapter03.equation_3_78`.

## Not formalized

* **Section 3.14.1**, the nodal analysis of a structured frame. It is a MATLAB experiment with the
  reorderings of Section 3.9, and it states no result.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

/-! ### Section 3.14.2: The barycentric regularization of a triangular grid -/

section Regularization

variable {n p : ℕ} (G : SimpleGraph (Fin n ⊕ Fin p)) [DecidableRel G.Adj]

/-- **Equation (3.78)** of [quarteroni2000numerical], the matrix of the barycentric regularization
system. Let $G$ be a simple graph on the grid nodes, which are $n$ interior nodes and $p$
boundary nodes, where $y$ is adjacent to $x$ if $y$ belongs to the patch $Z_x$ of $x$. Let $n_i$
be the number of neighbours of the interior node $i$, boundary nodes included. The **matrix of
the regularization system** is the $n \times n$ matrix $A$ with
$$a_{ii} = n_i, \qquad a_{ij} = -1 \text{ if the interior node } j \text{ is in } Z_i, \qquad
  a_{ij} = 0 \text{ otherwise}.$$
Its $i$-th row is the left-hand side of the equation $n_i z_i - \sum_{z_j \in Z_i \cap N_h}
z_j = \sum_{z_j \in Z_i \cap \partial D} z_j^{\partial D}$.

The grid nodes are `Fin n ⊕ Fin p`: the interior nodes $N_h$ are `Sum.inl i`, and the fixed
boundary nodes are `Sum.inr q`. The number $n_i$ is `G.degree (Sum.inl i)`. -/
def regularizationMatrix : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then (G.degree (Sum.inl i) : ℝ)
    else if G.Adj (Sum.inl i) (Sum.inl j) then -1 else 0

/-- **Equation (3.78)** of [quarteroni2000numerical], the entries. The entry $a_{ij}$ of the matrix
of the regularization system is $n_i$ if $i = j$, $-1$ if $i \neq j$ and the interior node $j$
is adjacent to the interior node $i$, and $0$ otherwise. -/
@[simp]
theorem regularizationMatrix_apply (i j : Fin n) :
    regularizationMatrix G i j =
      if i = j then (G.degree (Sum.inl i) : ℝ)
      else if G.Adj (Sum.inl i) (Sum.inl j) then -1 else 0 := rfl

/-- If the graph of the interior nodes is connected and the diagonal of the matrix of (3.78) is
positive, then the pattern of nonzero entries of this matrix is irreducible. -/
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
      rw [pow_succ, Matrix.mul_apply]
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

/-- **Equation (3.78)** of [quarteroni2000numerical]. Let $G$ be the node graph of a triangular grid
with $n$ interior nodes and $p$ boundary nodes, and let $A$ be the matrix of the regularization
system. Assume that the graph of the interior nodes is connected, and that at least one interior
node is adjacent to a boundary node. Then:

* for every $z \in \mathbb{R}^n$ and every interior node $i$, $(Az)_i = n_i z_i - \sum_{j} z_j$,
  where the sum is over the interior neighbours $j$ of $i$;
* for every $z \in \mathbb{R}^n$ and every vector $z^{\partial D} \in \mathbb{R}^p$ of boundary
  coordinates, $Az = b$ with $b_i = \sum_{q} z^{\partial D}_q$ over the boundary neighbours $q$
  of $i$ if and only if, for every interior node $i$,
$$n_i z_i = \sum_{z_j \in Z_i \cap N_h} z_j + \sum_{z_q \in Z_i \cap \partial D} z^{\partial
  D}_q,$$
that is, every interior node is the centre of gravity of its patch;
* $A$ is symmetric;
* $A$ is an M-matrix: its off-diagonal entries are nonpositive, it is nonsingular, and
  $A^{-1} \ge 0$ entrywise;
* $A$ is positive definite;
* the discrete maximum principle holds: for every $z \in \mathbb{R}^n$, $Az \ge 0$ implies
  $z \ge 0$.

**Reading.** The book leaves the hypotheses implicit. The statement assumes that the graph of
the interior nodes is connected, and that at least one interior node has a boundary neighbour.
Without the second hypothesis the matrix is singular, because the constant vector is in its
kernel. Without the first, the statement holds on each connected component separately.

The connectedness is `(G.comap Sum.inl).Reachable i j` for all interior nodes $i, j$. The
M-matrix property comes from `Matrix.isMMatrix_of_isIrreduciblyDiagDominant`: $A$ is irreducibly
diagonally dominant, with positive diagonal and nonpositive off-diagonal entries. The maximum
principle means that the new grid coordinates take values between the minimum and the maximum of
the boundary coordinates; this consequence is not part of the formal statement. -/
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
      (hdom.posSemidef hHerm fun i => by simp)).2 hMM.isUnit
  refine ⟨hrow, fun z zb => ?_, hsymm, hMM, hPD, fun z hz => hMM.nonneg_of_mulVec_nonneg hz⟩
  rw [funext_iff]
  exact forall_congr' fun i => by rw [hrow z i, sub_eq_iff_eq_add, add_comm]

end Regularization

end QuarteroniSaccoSaleri.Chapter03
