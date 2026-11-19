/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section08

/-!
# Saad, Section 6.9: GCR, ORTHOMIN and ORTHODIR

This module formalizes Section 6.9 of [saad2003iterative]. Lemma 6.21 says that any sequence of
directions $p_0, \dots, p_{m-1}$ that spans $\mathcal{K}_m(A, r_0)$ and is $A^T A$-orthogonal,
$(A p_i, A p_l) = 0$ for $i \ne l$, gives the approximation of smallest residual norm in
$x_0 + \mathcal{K}_m(A, r_0)$ in closed form,
$$x_m = x_0 + \sum_{i=0}^{m-1} \frac{(r_0, A p_i)}{(A p_i, A p_i)} p_i \quad (6.104), \qquad
  x_{j+1} = x_j + \frac{(r_j, A p_j)}{(A p_j, A p_j)} p_j \quad (6.105).$$
The three algorithms of the section are three ways to build such a sequence. GCR (Algorithm 6.21)
orthogonalizes the new residual against the previous directions, $p_{j+1} = r_{j+1} + \sum_{i=0}^{j}
\beta_{ij} p_i$ with $\beta_{ij} = -(A r_{j+1}, A p_i)/(A p_i, A p_i)$. ORTHODIR orthogonalizes
$A p_j$ in the same way (6.107). ORTHOMIN(k) is GCR with the sum truncated to the last $k$
directions. GCR and ORTHODIR are mathematically equivalent to full GMRES, and ORTHOMIN(k) with
$k \ge m$ is GCR.

The proofs specialize `Krylov.isMinResidualIterate_of_orthogonal_directions` of the backbone module
`Numlib.Krylov.CR`. The GMRES approximation is that of
`NumlibSurface.SaadSparse.Chapter06.Section05`.

## Main definitions

* Algorithm 6.21, `SaadSparse.Chapter06.gcrAux`: the triple $(x_j, r_j, p_j)$ after $j$ steps of
  GCR.
* Section 6.9, `SaadSparse.Chapter06.gcrRestarted`: the restarted method GCR(m).
* Section 6.9, `SaadSparse.Chapter06.orthominAux`: ORTHOMIN(k), GCR truncated to the last $k$
  directions.
* Equation (6.107), `SaadSparse.Chapter06.orthodirAux`: ORTHODIR.

## Main results

* Lemma 6.21, `SaadSparse.Chapter06.lemma_6_21`: $A^T A$-orthogonal directions that span
  $\mathcal{K}_m(A, r_0)$ give the minimal-residual approximation by (6.105), in the closed form
  (6.104).
* Equation (6.104), `SaadSparse.Chapter06.equation_6_104`: the closed form of the iterate of
  (6.105).
* Algorithm 6.21, `SaadSparse.Chapter06.algorithm_6_21_eq_gmres`: GCR is mathematically equivalent
  to full GMRES.
* Section 6.9, `SaadSparse.Chapter06.orthomin_eq_gcr`: ORTHOMIN(k) with $k \ge m$ is GCR.
* Section 6.9, `SaadSparse.Chapter06.orthodir_eq_gmres`: ORTHODIR is mathematically equivalent to
  full GMRES.

## Implementation notes

* The three algorithms carry the triple $(x_j, r_j, p_j)$. One step is
  `SaadSparse.Chapter06.gcrBody`, `SaadSparse.Chapter06.orthodirBody` or
  `SaadSparse.Chapter06.orthominBody`, a function of the whole history of triples, so that the three
  recursions differ only in this function.
* The truncated and restarted variants ORTHOMIN(k) and GCR(m) satisfy no global minimization
  property, and the book proves none.
* Indices start at $0$, as in the book: `gcrP A b x₀ j` is $p_j$. A quotient with denominator $0$ is
  $0$ in Lean.
* The definitions and the general lemmas are over the scalar field $\mathbb{K} = \mathbb{R}$ or
  $\mathbb{C}$, where $A^T A$-orthogonality becomes $A^H A$-orthogonality. The numbered results are
  stated over $\mathbb{R}$, the generality of the source.

## Deviations from the source

* **Generalization.** The minimal-residual proof uses the final span and explicit nonzero images.
  See `SaadSparse.Chapter06.isMinResidualIterate_of_orthogonalDirections`.
* **Generalization.** The closed form is valid without a spanning hypothesis or nonzero
  denominators. See `SaadSparse.Chapter06.equation_6_104`.
* **Reading.** The exact GCR recurrence totalizes division and does not model cached operation
  counts. See `SaadSparse.Chapter06.gcrBody`, `SaadSparse.Chapter06.gcrAux`,
  `SaadSparse.Chapter06.gcrX`, `SaadSparse.Chapter06.gcrR`, `SaadSparse.Chapter06.gcrP`,
  `SaadSparse.Chapter06.gcrAlpha`, `SaadSparse.Chapter06.gcrBeta`,
  `SaadSparse.Chapter06.gcrAlpha_eq`, `SaadSparse.Chapter06.gcrX_succ`,
  `SaadSparse.Chapter06.gcrR_succ`, `SaadSparse.Chapter06.gcrP_succ`.
* **Generalization.** The GCR step formulas extend to complex vectors and totalized division. See
  `SaadSparse.Chapter06.gcrStepAlpha`, `SaadSparse.Chapter06.gcrStepR`,
  `SaadSparse.Chapter06.gcrStepBeta`.
* **Reading.** ORTHODIR combines the source direction recurrence with the GCR state updates. See
  `SaadSparse.Chapter06.orthodirBody`, `SaadSparse.Chapter06.orthodirAux`,
  `SaadSparse.Chapter06.orthodirX`, `SaadSparse.Chapter06.orthodirR`,
  `SaadSparse.Chapter06.orthodirP`, `SaadSparse.Chapter06.orthodirAlpha`,
  `SaadSparse.Chapter06.orthodirBeta`, `SaadSparse.Chapter06.orthodirAlpha_eq`,
  `SaadSparse.Chapter06.orthodirX_succ`, `SaadSparse.Chapter06.orthodirR_succ`,
  `SaadSparse.Chapter06.orthodirP_succ`.
* **Reading.** ORTHOMIN clips the window to the available directions and allows an empty window. See
  `SaadSparse.Chapter06.orthominBody`, `SaadSparse.Chapter06.orthominAux`,
  `SaadSparse.Chapter06.orthominX`, `SaadSparse.Chapter06.orthominR`,
  `SaadSparse.Chapter06.orthominP`.
* **Reading.** Restarted GCR uses fixed cycle lengths and recomputes the initial residual at each
  restart. See `SaadSparse.Chapter06.gcrCycle`, `SaadSparse.Chapter06.gcrRestarted`,
  `SaadSparse.Chapter06.gcrRestarted_succ`.
* **Reading.** The GCR and ORTHODIR basis properties make the no-breakdown and grade conditions
  explicit. See `SaadSparse.Chapter06.inner_apply_gcrP_eq_zero`,
  `SaadSparse.Chapter06.inner_apply_orthodirP_eq_zero`, `SaadSparse.Chapter06.span_gcrP_eq`,
  `SaadSparse.Chapter06.span_orthodirP_eq`.
* **Reading.** The GCR and ORTHODIR minimal-residual specifications apply to prefixes without
  breakdown. See `SaadSparse.Chapter06.gcrX_isMinResidualIterate`,
  `SaadSparse.Chapter06.orthodirX_isMinResidualIterate`.
* **Scope.** The GMRES equivalence is stated for nonsingular systems before breakdown. See
  `SaadSparse.Chapter06.gcrX_eq_gmresFixed`, `SaadSparse.Chapter06.orthodirX_eq_gmresFixed`,
  `SaadSparse.Chapter06.algorithm_6_21_eq_gmres`, `SaadSparse.Chapter06.orthodir_eq_gmres`.
* **Lemma 6.21** (reading). The source asks that $\{p_0, \dots, p_{j-1}\}$ be a basis of
  $\mathcal{K}_j(A, r_0)$ for each $j \le m$. The library asks that $p_0, \dots, p_{m-1}$ span
  $\mathcal{K}_m(A, r_0)$ and that $A p_i \ne 0$. See `SaadSparse.Chapter06.lemma_6_21`.
-/

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-! ### A lemma on Krylov subspaces -/

/-- If $x \in \mathcal{K}_m(A, v)$, then $A x \in \mathcal{K}_{m+1}(A, v)$. -/
private theorem apply_mem_krylov_succ {v x : 𝔼} {m : ℕ} (h : x ∈ krylov A v m) :
    op A x ∈ krylov A v (m + 1) := by
  rw [krylov_eq] at h
  rw [krylov_eq]
  exact Krylov.map_subspace_le (op A) v m ⟨x, h, rfl⟩

/-! ### Lemma 6.21 and (6.104)–(6.105) -/

/-- Lemma 6.21 with (6.105), over $\mathbb{K}$: let $p_0, p_1, \dots$ be vectors with
$(A p_i, A p_l) = 0$ for $i \ne l$ and $A p_i \ne 0$, for $i, l < m$, such that
$p_0, \dots, p_{m-1}$ span $\mathcal{K}_m(A, r_0)$. If $x_0$ is the initial guess and $x_{j+1} =
x_j + \frac{(r_j, A p_j)}{(A p_j, A p_j)} p_j$ with $r_j = b - A x_j$ for every $j$, then $x_m$
minimizes the residual norm over $x_0 + \mathcal{K}_m(A, r_0)$.

**Generalization.** The minimal-residual statement works over the real or complex field. It requires
the final span equality and nonzero matrix images, without requiring that each intermediate prefix
span its Krylov space.
-/
theorem isMinResidualIterate_of_orthogonalDirections {m : ℕ} (p : ℕ → 𝔼)
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0)
    (hne : ∀ i < m, op A (p i) ≠ 0)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => p (i : ℕ)) = krylov A (r₀ A b x₀) m)
    (x : ℕ → 𝔼) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (op A (p j)) (b - op A (x j)) / inner 𝕜 (op A (p j)) (op A (p j))) • p j) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (x m) := by
  rw [krylov_eq] at hspan
  exact Krylov.isMinResidualIterate_of_orthogonal_directions p horth hne hspan x hx0 hstep

/-- If $x_{j+1} = x_j + c_j p_j$ for every $j$, then $b - A x_j = (b - A x_0) - \sum_{l < j} c_l A
p_l$. -/
private theorem residual_eq_sub_sum (p x : ℕ → 𝔼) (c : ℕ → 𝕜)
    (hstep : ∀ j, x (j + 1) = x j + c j • p j) (j : ℕ) :
    b - op A (x j) = (b - op A (x 0)) - ∑ l ∈ Finset.range j, c l • op A (p l) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : b - op A (x (j + 1)) = (b - op A (x j)) - c j • op A (p j) := by
      rw [hstep j, map_add, map_smul]
      abel
    rw [h, ih, Finset.sum_range_succ]
    abel

/-- **Equation (6.104)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0 \in \mathbb{K}^n$. Let $p_0, p_1, \dots$ be vectors with $(A p_i, A p_l) = 0$ for
$i \ne l$, $i, l < m$. Let $x_0, x_1, \dots$ be produced by the update (6.105), $x_{j+1} = x_j +
\frac{(r_j, A p_j)}{(A p_j, A p_j)} p_j$ with $r_j = b - A x_j$. Then
$$x_m = x_0 + \sum_{i=0}^{m-1} \frac{(r_0, A p_i)}{(A p_i, A p_i)} p_i.$$

The proof shows $(r_j, A p_j) = (r_0, A p_j)$ from the orthogonality. No hypothesis
$A p_i \ne 0$ is needed, because a quotient with denominator $0$ is $0$ on both sides. The real
form is part of `SaadSparse.Chapter06.lemma_6_21`.

**Generalization.** The closed-form identity follows from orthogonality and the recurrence alone,
over the real or complex field. Since division is totalized, it also holds when some images vanish
and requires no span equality.
-/
theorem equation_6_104 {m : ℕ} (p : ℕ → 𝔼)
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0)
    (x : ℕ → 𝔼) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (op A (p j)) (b - op A (x j)) / inner 𝕜 (op A (p j)) (op A (p j))) • p j) :
    x m = x₀ + ∑ i ∈ Finset.range m,
      (inner 𝕜 (op A (p i)) (r₀ A b x₀) / inner 𝕜 (op A (p i)) (op A (p i))) • p i := by
  have hres := residual_eq_sub_sum A b p x
    (fun l => inner 𝕜 (op A (p l)) (b - op A (x l)) / inner 𝕜 (op A (p l)) (op A (p l))) hstep
  have hnum : ∀ j < m, inner 𝕜 (op A (p j)) (b - op A (x j))
      = inner 𝕜 (op A (p j)) (r₀ A b x₀) := by
    intro j hj
    have hz : ∀ l ∈ Finset.range j,
        inner 𝕜 (op A (p j))
          ((inner 𝕜 (op A (p l)) (b - op A (x l)) / inner 𝕜 (op A (p l)) (op A (p l))) •
            op A (p l)) = 0 := by
      intro l hl
      have hlj := Finset.mem_range.1 hl
      rw [inner_smul_right, horth j hj l (by omega) (by omega), mul_zero]
    rw [hres j, hx0, inner_sub_right, inner_sum, Finset.sum_eq_zero hz, sub_zero]
  have hx : ∀ j ≤ m, x j = x₀ + ∑ i ∈ Finset.range j,
      (inner 𝕜 (op A (p i)) (r₀ A b x₀) / inner 𝕜 (op A (p i)) (op A (p i))) • p i := by
    intro j
    induction j with
    | zero => intro _; simpa using hx0
    | succ j ih =>
      intro hj
      rw [hstep j, hnum j (by omega), ih (by omega), Finset.sum_range_succ]
      abel
  exact hx m le_rfl

/-! ### The generic step and the orthogonality it produces -/

/-- The step length $\alpha_j = (r_j, A p_j)/(A p_j, A p_j)$ of line 3 of Algorithm 6.21, computed
from a triple $(x_j, r_j, p_j)$; GCR, ORTHOMIN(k) and ORTHODIR share it.

**Generalization.** The scalar and residual formulas also apply over the complex field, using
Mathlib's conjugate-linear first argument in the reversed order from the book. A zero matrix image
gives a totalized zero quotient.
-/
noncomputable def gcrStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op A s.2.2) s.2.1 / inner 𝕜 (op A s.2.2) (op A s.2.2)

/-- The next residual $r_{j+1} = r_j - \alpha_j A p_j$ of line 5 of Algorithm 6.21, computed from a
triple $(x_j, r_j, p_j)$; GCR, ORTHOMIN(k) and ORTHODIR share it.

**Generalization.** The scalar and residual formulas also apply over the complex field, using
Mathlib's conjugate-linear first argument in the reversed order from the book. A zero matrix image
gives a totalized zero quotient.
-/
noncomputable def gcrStepR (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - gcrStepAlpha A s • op A s.2.2

/-- The coefficient $-(A z, A p_i)/(A p_i, A p_i)$ for vectors $p_i$ and $z$. With $z = r_{j+1}$ it
is the coefficient $\beta_{ij}$ of line 6 of Algorithm 6.21 (GCR and ORTHOMIN(k)), and with
$z = A p_j$ it is the coefficient of (6.107) (ORTHODIR).

**Generalization.** The scalar and residual formulas also apply over the complex field, using
Mathlib's conjugate-linear first argument in the reversed order from the book. A zero matrix image
gives a totalized zero quotient.
-/
noncomputable def gcrStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (pi z : 𝔼) : 𝕜 :=
  -(inner 𝕜 (op A pi) (op A z) / inner 𝕜 (op A pi) (op A pi))

/-- Lines 3–7 of Algorithm 6.21 (GCR), applied to the history of triples $(x_i, r_i, p_i)$,
$i \le j$. The result is $x_{j+1} = x_j + \alpha_j p_j$, $r_{j+1} = r_j - \alpha_j A p_j$ and
$p_{j+1} = r_{j+1} + \sum_{i=0}^{j} \beta_{ij} p_i$ with $\beta_{ij} = -(A r_{j+1}, A p_i)/(A
p_i, A p_i)$.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrBody (A : Matrix (Fin n) (Fin n) 𝕜) {j : ℕ}
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  ((s (Fin.last j)).1 + gcrStepAlpha A (s (Fin.last j)) • (s (Fin.last j)).2.2,
    gcrStepR A (s (Fin.last j)),
    gcrStepR A (s (Fin.last j)) +
      ∑ i : Fin (j + 1),
        gcrStepBeta A (s i).2.2 (gcrStepR A (s (Fin.last j))) • (s i).2.2)

/-- Lines 3–5 of Algorithm 6.21 with the direction update (6.107) of ORTHODIR, applied to the
history of triples $(x_i, r_i, p_i)$, $i \le j$. The new direction is $p_{j+1} = A p_j +
\sum_{i=0}^{j} \beta_{ij} p_i$ with $\beta_{ij} = -(A^2 p_j, A p_i)/(A p_i, A p_i)$.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirBody (A : Matrix (Fin n) (Fin n) 𝕜) {j : ℕ}
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  ((s (Fin.last j)).1 + gcrStepAlpha A (s (Fin.last j)) • (s (Fin.last j)).2.2,
    gcrStepR A (s (Fin.last j)),
    op A (s (Fin.last j)).2.2 +
      ∑ i : Fin (j + 1),
        gcrStepBeta A (s i).2.2 (op A (s (Fin.last j)).2.2) • (s i).2.2)

/-- Lines 3–5 of Algorithm 6.21 with the truncated lines 6a–7a of ORTHOMIN(k), applied to the
history of triples $(x_i, r_i, p_i)$, $i \le j$. The direction update of GCR uses only the
directions $p_i$ with $j - k + 1 \le i \le j$.

**Reading.** The starting index of the window is clipped to zero. The parameter may also be zero,
giving an empty orthogonalization sum. The definition uses the totalized GCR update and does not
enforce convergence.
-/
noncomputable def orthominBody (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) {j : ℕ}
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  ((s (Fin.last j)).1 + gcrStepAlpha A (s (Fin.last j)) • (s (Fin.last j)).2.2,
    gcrStepR A (s (Fin.last j)),
    gcrStepR A (s (Fin.last j)) +
      ∑ i : Fin (j + 1), if j + 1 ≤ (i : ℕ) + k then
        gcrStepBeta A (s i).2.2 (gcrStepR A (s (Fin.last j))) • (s i).2.2
      else 0)

/-- If $k$ is at least the number $j + 1$ of directions, the step of ORTHOMIN(k) is the step of GCR.
-/
private theorem orthominBody_eq_gcrBody {k j : ℕ} (hk : j + 1 ≤ k)
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : orthominBody A k s = gcrBody A s := by
  rw [orthominBody, gcrBody]
  refine congrArg _ (congrArg _ (congrArg _ (Finset.sum_congr rfl fun i _ => ?_)))
  exact ite_eq_left_of_eq_true _ _ (eq_true (by omega))

/-- If each new direction is a vector $z_j$ minus its $A^H A$-projections on the previous
directions, and $A p_i \ne 0$, then the vectors $A p_i$ are pairwise orthogonal; GCR takes
$z_j = r_{j+1}$ and ORTHODIR takes $z_j = A p_j$. -/
private theorem inner_apply_eq_zero_of_recur (p z : ℕ → 𝔼) {m : ℕ}
    (hrec : ∀ j, p (j + 1) = z j + ∑ i ∈ Finset.range (j + 1), gcrStepBeta A (p i) (z j) • p i)
    (hne : ∀ i < m, op A (p i) ≠ 0) :
    ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0 := by
  have key : ∀ N, N ≤ m → ∀ i < N, ∀ l < N, i ≠ l →
      inner 𝕜 (op A (p i)) (op A (p l)) = 0 := by
    intro N
    induction N with
    | zero => intro _ i hi; omega
    | succ N ih =>
      intro hN
      have ihN := ih (by omega)
      have hlast : ∀ i < N, inner 𝕜 (op A (p i)) (op A (p N)) = 0 := by
        intro i hi
        obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
        have hnz : inner 𝕜 (op A (p i)) (op A (p i)) ≠ 0 := fun h =>
          hne i (by omega) (inner_self_eq_zero.1 h)
        have happ : op A (p (j + 1)) = op A (z j) +
            ∑ l ∈ Finset.range (j + 1), gcrStepBeta A (p l) (z j) • op A (p l) := by
          rw [hrec j, map_add, map_sum]
          exact congrArg _ (Finset.sum_congr rfl fun l _ => map_smul _ _ _)
        have hsum : ∑ l ∈ Finset.range (j + 1),
            gcrStepBeta A (p l) (z j) * inner 𝕜 (op A (p i)) (op A (p l))
            = gcrStepBeta A (p i) (z j) * inner 𝕜 (op A (p i)) (op A (p i)) := by
          refine Finset.sum_eq_single i (fun l hl hli => ?_) fun h =>
            absurd (Finset.mem_range.2 hi) h
          rw [ihN i hi l (Finset.mem_range.1 hl) (Ne.symm hli), mul_zero]
        rw [happ, inner_add_right, inner_sum]
        simp only [inner_smul_right]
        rw [hsum, gcrStepBeta, neg_mul, div_mul_cancel₀ _ hnz, add_neg_cancel]
      intro i hi l hl hil
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | rfl
        · exact ihN i hi' l hl' hil
        · exact hlast i hi'
      · rw [← inner_conj_symm, hlast l (by omega), map_zero]
  exact key m le_rfl

/-- The directions of a recursion of the form of GCR stay in the Krylov subspaces:
$p_j \in \mathcal{K}_{j+1}(A, v)$. -/
private theorem mem_krylov_of_recur (p z : ℕ → 𝔼) (v : 𝔼) (c : ℕ → ℕ → 𝕜) (hp0 : p 0 = v)
    (hrec : ∀ j, p (j + 1) = z j + ∑ i ∈ Finset.range (j + 1), c i j • p i)
    (hz : ∀ j, (∀ i ≤ j, p i ∈ krylov A v (i + 1)) → z j ∈ krylov A v (j + 2)) (j : ℕ) :
    p j ∈ krylov A v (j + 1) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [hp0]; exact self_mem_krylov A v one_pos
    | succ j =>
      have hp : ∀ i ≤ j, p i ∈ krylov A v (i + 1) := fun i hi => ih i (by omega)
      rw [hrec j]
      refine Submodule.add_mem _ (hz j hp) (Submodule.sum_mem _ fun i hi => ?_)
      exact Submodule.smul_mem _ _
        (krylov_mono A _ (by have := Finset.mem_range.1 hi; omega) (hp i (by
          have := Finset.mem_range.1 hi; omega)))

/-- If $m$ is at most the grade of $r_0$, then $A^H A$-orthogonal directions $p_0, \dots, p_{m-1}$
with $A p_i \ne 0$ and $p_j \in \mathcal{K}_{j+1}(A, r_0)$ span $\mathcal{K}_m(A, r_0)$. -/
private theorem span_eq_krylov (p : ℕ → 𝔼) {m : ℕ}
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0)
    (hne : ∀ i < m, op A (p i) ≠ 0)
    (hmem : ∀ j, p j ∈ krylov A (r₀ A b x₀) (j + 1))
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => p (i : ℕ)) = krylov A (r₀ A b x₀) m := by
  have hindep : LinearIndependent 𝕜 fun i : Fin m => p (i : ℕ) := by
    have h1 : LinearIndependent 𝕜 ((op A) ∘ fun i : Fin m => p (i : ℕ)) :=
      linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => hne i i.2)
        fun i l hil => horth i i.2 l l.2 fun h => hil (Fin.ext h)
    exact LinearIndependent.of_comp (op A) h1
  have hle : Submodule.span 𝕜 (Set.range fun i : Fin m => p (i : ℕ))
      ≤ krylov A (r₀ A b x₀) m := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact krylov_mono A _ i.2 (hmem (i : ℕ))
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_eq_card hindep, finrank_krylov, min_eq_left hm, Fintype.card_fin]

/-- The residual of a recursion of the form of GCR is the true residual $b - A x_j$. -/
private theorem residual_eq_of_recur (x r p : ℕ → 𝔼) (c : ℕ → 𝕜) (hr0 : r 0 = b - op A (x 0))
    (hx : ∀ j, x (j + 1) = x j + c j • p j) (hr : ∀ j, r (j + 1) = r j - c j • op A (p j))
    (j : ℕ) : r j = b - op A (x j) := by
  induction j with
  | zero => exact hr0
  | succ j ih =>
    rw [hr j, ih, hx j, map_add, map_smul]
    abel

/-! ### Algorithm 6.21: GCR -/

/-- **Algorithm 6.21** of [saad2003iterative] (GCR). For $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $j \ge 0$, this is the triple $(x_j, r_j, p_j)$ after $j$ steps,
started from $r_0 = b - A x_0$ and $p_0 = r_0$; each step is `SaadSparse.Chapter06.gcrBody`.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrAux (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℕ → 𝔼 × 𝔼 × 𝔼
  | 0 => (x₀, b - op A x₀, b - op A x₀)
  | j + 1 => gcrBody A fun i : Fin (j + 1) => gcrAux A b x₀ (i : ℕ)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The iterate $x_j$ of Algorithm 6.21 after $j$ steps.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrX (j : ℕ) : 𝔼 := (gcrAux A b x₀ j).1

/-- The residual $r_j$ of Algorithm 6.21 after $j$ steps.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrR (j : ℕ) : 𝔼 := (gcrAux A b x₀ j).2.1

/-- The direction $p_j$ of Algorithm 6.21 after $j$ steps.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrP (j : ℕ) : 𝔼 := (gcrAux A b x₀ j).2.2

/-- The step length $\alpha_j = (r_j, A p_j)/(A p_j, A p_j)$ of line 3 of Algorithm 6.21.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrAlpha (j : ℕ) : 𝕜 := gcrStepAlpha A (gcrAux A b x₀ j)

/-- The coefficient $\beta_{ij} = -(A r_{j+1}, A p_i)/(A p_i, A p_i)$ of line 6 of Algorithm 6.21.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
noncomputable def gcrBeta (i j : ℕ) : 𝕜 :=
  gcrStepBeta A (gcrP A b x₀ i) (gcrR A b x₀ (j + 1))

/-- The iterate $x_0$ of Algorithm 6.21 is the initial guess. -/
@[simp] theorem gcrX_zero : gcrX A b x₀ 0 = x₀ := by rw [gcrX, gcrAux]

/-- The residual $r_0$ of Algorithm 6.21 is $b - A x_0$. -/
@[simp] theorem gcrR_zero : gcrR A b x₀ 0 = b - op A x₀ := by rw [gcrR, gcrAux]

/-- Algorithm 6.21, line 1: $p_0 = r_0$. -/
@[simp] theorem gcrP_zero : gcrP A b x₀ 0 = gcrR A b x₀ 0 := by rw [gcrP, gcrR, gcrAux]

/-- Algorithm 6.21, line 3: $\alpha_j = (r_j, A p_j)/(A p_j, A p_j)$.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
theorem gcrAlpha_eq (j : ℕ) : gcrAlpha A b x₀ j =
    inner 𝕜 (op A (gcrP A b x₀ j)) (gcrR A b x₀ j) /
      inner 𝕜 (op A (gcrP A b x₀ j)) (op A (gcrP A b x₀ j)) := rfl

/-- Algorithm 6.21, line 4: $x_{j+1} = x_j + \alpha_j p_j$.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
theorem gcrX_succ (j : ℕ) :
    gcrX A b x₀ (j + 1) = gcrX A b x₀ j + gcrAlpha A b x₀ j • gcrP A b x₀ j := by
  rw [gcrX, gcrAux]
  rfl

/-- Algorithm 6.21, line 5: $r_{j+1} = r_j - \alpha_j A p_j$.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
theorem gcrR_succ (j : ℕ) :
    gcrR A b x₀ (j + 1) = gcrR A b x₀ j - gcrAlpha A b x₀ j • op A (gcrP A b x₀ j) := by
  rw [gcrR, gcrAux]
  rfl

/-- Algorithm 6.21, line 7: $p_{j+1} = r_{j+1} + \sum_{i=0}^{j} \beta_{ij} p_i$.

**Reading.** Lean uses exact finite sums and totalized quotients for every step over the real or
complex field, with no convergence test. It carries the history of iterates, residuals and
directions. The source separately describes caching the matrix images to use one matrix-vector
product per step.
-/
theorem gcrP_succ (j : ℕ) : gcrP A b x₀ (j + 1) =
    gcrR A b x₀ (j + 1) + ∑ i ∈ Finset.range (j + 1), gcrBeta A b x₀ i j • gcrP A b x₀ i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => gcrBeta A b x₀ i j • gcrP A b x₀ i) (j + 1)]
  simp only [gcrBeta, gcrR_succ]
  rw [gcrP, gcrAux]
  rfl

/-- The residual carried by Algorithm 6.21 is the true residual: $r_j = b - A x_j$. -/
theorem gcrR_eq_residual (j : ℕ) : gcrR A b x₀ j = b - op A (gcrX A b x₀ j) :=
  residual_eq_of_recur A b (gcrX A b x₀) (gcrR A b x₀) (gcrP A b x₀) (gcrAlpha A b x₀)
    (by rw [gcrR_zero, gcrX_zero]) (gcrX_succ A b x₀) (gcrR_succ A b x₀) j

/-- The direction $p_j$ of Algorithm 6.21 lies in $\mathcal{K}_{j+1}(A, r_0)$. -/
theorem gcrP_mem_krylov (j : ℕ) : gcrP A b x₀ j ∈ krylov A (r₀ A b x₀) (j + 1) := by
  refine mem_krylov_of_recur A (gcrP A b x₀) (fun j => gcrR A b x₀ (j + 1)) (r₀ A b x₀)
    (gcrBeta A b x₀) (by rw [gcrP_zero, gcrR_zero]) (gcrP_succ A b x₀) (fun j hp => ?_) j
  have hr : ∀ l, l ≤ j + 1 → gcrR A b x₀ l ∈ krylov A (r₀ A b x₀) (l + 1) := by
    intro l
    induction l with
    | zero => intro _; rw [gcrR_zero]; exact self_mem_krylov A _ one_pos
    | succ l ih =>
      intro hl
      rw [gcrR_succ]
      exact Submodule.sub_mem _ (krylov_mono A _ (by omega) (ih (by omega)))
        (Submodule.smul_mem _ _ (apply_mem_krylov_succ A (hp l (by omega))))
  exact hr (j + 1) le_rfl

/-- Section 6.9: if $A p_i \ne 0$ for every $i < m$, then the vectors $A p_i$, $i < m$, built by
Algorithm 6.21 are orthogonal. This is the hypothesis of Lemma 6.21.

**Reading.** The proofs explicitly require nonzero matrix images in the prefix. The span conclusions
also require the prefix length to be at most the grade. The source motivates the recurrences using
those directions as Krylov bases.
-/
theorem inner_apply_gcrP_eq_zero {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0) :
    ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (gcrP A b x₀ i)) (op A (gcrP A b x₀ l)) = 0 :=
  inner_apply_eq_zero_of_recur A (gcrP A b x₀) (fun j => gcrR A b x₀ (j + 1))
    (gcrP_succ A b x₀) hne

/-- If $A p_i \ne 0$ for every $i < m$ and $m$ is at most the grade of $r_0$, then the directions
$p_0, \dots, p_{m-1}$ of Algorithm 6.21 span $\mathcal{K}_m(A, r_0)$.

**Reading.** The proofs explicitly require nonzero matrix images in the prefix. The span conclusions
also require the prefix length to be at most the grade. The source motivates the recurrences using
those directions as Krylov bases.
-/
theorem span_gcrP_eq {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => gcrP A b x₀ (i : ℕ))
      = krylov A (r₀ A b x₀) m :=
  span_eq_krylov A b x₀ (gcrP A b x₀) (inner_apply_gcrP_eq_zero A b x₀ hne) hne
    (gcrP_mem_krylov A b x₀) hm

/-- GCR is mathematically equivalent to full GMRES: if $A p_i \ne 0$ for every $i < m$ and $m$ is at
most the grade of $r_0$, then the iterate $x_m$ of Algorithm 6.21 minimizes the residual norm
over $x_0 + \mathcal{K}_m(A, r_0)$, by Lemma 6.21.

**Reading.** The conclusion requires a prefix up to the grade with nonzero matrix images for every
direction. This ensures that the source's orthogonal direction construction gives the intended
Krylov space.
-/
theorem gcrX_isMinResidualIterate {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gcrX A b x₀ m) := by
  refine isMinResidualIterate_of_orthogonalDirections A b x₀ (gcrP A b x₀)
    (inner_apply_gcrP_eq_zero A b x₀ hne) hne (span_gcrP_eq A b x₀ hne hm) (gcrX A b x₀)
    (gcrX_zero A b x₀) fun j => ?_
  rw [gcrX_succ, gcrAlpha_eq, gcrR_eq_residual]

/-! ### ORTHODIR -/

/-- **ORTHODIR** ([saad2003iterative], Section 6.9). For $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $j \ge 0$, this is the triple $(x_j, r_j, p_j)$ after $j$ steps,
started from $r_0 = b - A x_0$ and $p_0 = r_0$, with the direction update (6.107), $p_{j+1} = A
p_j + \sum_{i=0}^{j} \beta_{ij} p_i$, and the iterate update (6.105).

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirAux (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℕ → 𝔼 × 𝔼 × 𝔼
  | 0 => (x₀, b - op A x₀, b - op A x₀)
  | j + 1 => orthodirBody A fun i : Fin (j + 1) => orthodirAux A b x₀ (i : ℕ)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The iterate $x_j$ of ORTHODIR after $j$ steps.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirX (j : ℕ) : 𝔼 := (orthodirAux A b x₀ j).1

/-- The residual $r_j$ of ORTHODIR after $j$ steps.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirR (j : ℕ) : 𝔼 := (orthodirAux A b x₀ j).2.1

/-- The direction $p_j$ of ORTHODIR after $j$ steps.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirP (j : ℕ) : 𝔼 := (orthodirAux A b x₀ j).2.2

/-- The step length $\alpha_j = (r_j, A p_j)/(A p_j, A p_j)$ of (6.105) in ORTHODIR.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirAlpha (j : ℕ) : 𝕜 := gcrStepAlpha A (orthodirAux A b x₀ j)

/-- The coefficient $\beta_{ij} = -(A^2 p_j, A p_i)/(A p_i, A p_i)$ of (6.107).

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
noncomputable def orthodirBeta (i j : ℕ) : 𝕜 :=
  gcrStepBeta A (orthodirP A b x₀ i) (op A (orthodirP A b x₀ j))

/-- The iterate $x_0$ of ORTHODIR is the initial guess. -/
@[simp] theorem orthodirX_zero : orthodirX A b x₀ 0 = x₀ := by rw [orthodirX, orthodirAux]

/-- The residual $r_0$ of ORTHODIR is $b - A x_0$. -/
@[simp] theorem orthodirR_zero : orthodirR A b x₀ 0 = b - op A x₀ := by
  rw [orthodirR, orthodirAux]

/-- The first direction of ORTHODIR is $p_0 = r_0$. -/
@[simp] theorem orthodirP_zero : orthodirP A b x₀ 0 = orthodirR A b x₀ 0 := by
  rw [orthodirP, orthodirR, orthodirAux]

/-- The step length of ORTHODIR is $\alpha_j = (r_j, A p_j)/(A p_j, A p_j)$.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
theorem orthodirAlpha_eq (j : ℕ) : orthodirAlpha A b x₀ j =
    inner 𝕜 (op A (orthodirP A b x₀ j)) (orthodirR A b x₀ j) /
      inner 𝕜 (op A (orthodirP A b x₀ j)) (op A (orthodirP A b x₀ j)) := rfl

/-- Equation (6.105) for ORTHODIR: $x_{j+1} = x_j + \alpha_j p_j$.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
theorem orthodirX_succ (j : ℕ) : orthodirX A b x₀ (j + 1) =
    orthodirX A b x₀ j + orthodirAlpha A b x₀ j • orthodirP A b x₀ j := by
  rw [orthodirX, orthodirAux]
  rfl

/-- The residual update of ORTHODIR: $r_{j+1} = r_j - \alpha_j A p_j$.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
theorem orthodirR_succ (j : ℕ) : orthodirR A b x₀ (j + 1) =
    orthodirR A b x₀ j - orthodirAlpha A b x₀ j • op A (orthodirP A b x₀ j) := by
  rw [orthodirR, orthodirAux]
  rfl

/-- Equation (6.107): $p_{j+1} = A p_j + \sum_{i=0}^{j} \beta_{ij} p_i$.

**Reading.** The source gives the direction and coefficient update. Lean supplies the GCR initial
data and residual and iterate updates, uses complex inner products when needed, and defines the
recurrence at all indices with totalized division.
-/
theorem orthodirP_succ (j : ℕ) : orthodirP A b x₀ (j + 1) = op A (orthodirP A b x₀ j) +
    ∑ i ∈ Finset.range (j + 1), orthodirBeta A b x₀ i j • orthodirP A b x₀ i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => orthodirBeta A b x₀ i j • orthodirP A b x₀ i)
    (j + 1), orthodirP, orthodirAux]
  rfl

/-- The residual carried by ORTHODIR is the true residual: $r_j = b - A x_j$. -/
theorem orthodirR_eq_residual (j : ℕ) : orthodirR A b x₀ j = b - op A (orthodirX A b x₀ j) :=
  residual_eq_of_recur A b (orthodirX A b x₀) (orthodirR A b x₀) (orthodirP A b x₀)
    (orthodirAlpha A b x₀) (by rw [orthodirR_zero, orthodirX_zero]) (orthodirX_succ A b x₀)
    (orthodirR_succ A b x₀) j

/-- The direction $p_j$ of ORTHODIR lies in $\mathcal{K}_{j+1}(A, r_0)$. -/
theorem orthodirP_mem_krylov (j : ℕ) :
    orthodirP A b x₀ j ∈ krylov A (r₀ A b x₀) (j + 1) :=
  mem_krylov_of_recur A (orthodirP A b x₀) (fun j => op A (orthodirP A b x₀ j)) (r₀ A b x₀)
    (orthodirBeta A b x₀) (by rw [orthodirP_zero, orthodirR_zero]) (orthodirP_succ A b x₀)
    (fun j hp => apply_mem_krylov_succ A (hp j le_rfl)) j

/-- Section 6.9: if $A p_i \ne 0$ for every $i < m$, then ORTHODIR builds $A^H A$-orthogonal
directions: $(A p_i, A p_l) = 0$ for $i \ne l < m$.

**Reading.** The proofs explicitly require nonzero matrix images in the prefix. The span conclusions
also require the prefix length to be at most the grade. The source motivates the recurrences using
those directions as Krylov bases.
-/
theorem inner_apply_orthodirP_eq_zero {m : ℕ} (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0) :
    ∀ i < m, ∀ l < m, i ≠ l →
      inner 𝕜 (op A (orthodirP A b x₀ i)) (op A (orthodirP A b x₀ l)) = 0 :=
  inner_apply_eq_zero_of_recur A (orthodirP A b x₀) (fun j => op A (orthodirP A b x₀ j))
    (orthodirP_succ A b x₀) hne

/-- If $A p_i \ne 0$ for every $i < m$ and $m$ is at most the grade of $r_0$, then the directions
$p_0, \dots, p_{m-1}$ of ORTHODIR span $\mathcal{K}_m(A, r_0)$.

**Reading.** The proofs explicitly require nonzero matrix images in the prefix. The span conclusions
also require the prefix length to be at most the grade. The source motivates the recurrences using
those directions as Krylov bases.
-/
theorem span_orthodirP_eq {m : ℕ} (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => orthodirP A b x₀ (i : ℕ))
      = krylov A (r₀ A b x₀) m :=
  span_eq_krylov A b x₀ (orthodirP A b x₀) (inner_apply_orthodirP_eq_zero A b x₀ hne) hne
    (orthodirP_mem_krylov A b x₀) hm

/-- ORTHODIR is mathematically equivalent to full GMRES: if $A p_i \ne 0$ for every $i < m$ and $m$
is at most the grade of $r_0$, then the iterate $x_m$ of ORTHODIR minimizes the residual norm
over $x_0 + \mathcal{K}_m(A, r_0)$, by Lemma 6.21.

**Reading.** The conclusion requires a prefix up to the grade with nonzero matrix images for every
direction. This ensures that the source's orthogonal direction construction gives the intended
Krylov space.
-/
theorem orthodirX_isMinResidualIterate {m : ℕ} (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (orthodirX A b x₀ m) := by
  refine isMinResidualIterate_of_orthogonalDirections A b x₀ (orthodirP A b x₀)
    (inner_apply_orthodirP_eq_zero A b x₀ hne) hne (span_orthodirP_eq A b x₀ hne hm)
    (orthodirX A b x₀) (orthodirX_zero A b x₀) fun j => ?_
  rw [orthodirX_succ, orthodirAlpha_eq, orthodirR_eq_residual]

/-! ### ORTHOMIN(k) and GCR(m): the truncated and restarted variants -/

/-- **ORTHOMIN(k)** ([saad2003iterative], Section 6.9). For $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $j \ge 0$, this is the triple $(x_j, r_j, p_j)$ after $j$ steps of
Algorithm 6.21 with lines 6–7 truncated to the last $k$ directions.

Because of the truncation the method satisfies no global minimization property, and the book
proves none. The only statement about it is `SaadSparse.Chapter06.orthomin_eq_gcr`.

**Reading.** The starting index of the window is clipped to zero. The parameter may also be zero,
giving an empty orthogonalization sum. The definition uses the totalized GCR update and does not
enforce convergence.
-/
noncomputable def orthominAux (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k : ℕ) :
    ℕ → 𝔼 × 𝔼 × 𝔼
  | 0 => (x₀, b - op A x₀, b - op A x₀)
  | j + 1 => orthominBody A k fun i : Fin (j + 1) => orthominAux A b x₀ k (i : ℕ)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The iterate $x_j$ of ORTHOMIN(k) after $j$ steps.

**Reading.** The starting index of the window is clipped to zero. The parameter may also be zero,
giving an empty orthogonalization sum. The definition uses the totalized GCR update and does not
enforce convergence.
-/
noncomputable def orthominX (k j : ℕ) : 𝔼 := (orthominAux A b x₀ k j).1

/-- The residual $r_j$ of ORTHOMIN(k) after $j$ steps.

**Reading.** The starting index of the window is clipped to zero. The parameter may also be zero,
giving an empty orthogonalization sum. The definition uses the totalized GCR update and does not
enforce convergence.
-/
noncomputable def orthominR (k j : ℕ) : 𝔼 := (orthominAux A b x₀ k j).2.1

/-- The direction $p_j$ of ORTHOMIN(k) after $j$ steps.

**Reading.** The starting index of the window is clipped to zero. The parameter may also be zero,
giving an empty orthogonalization sum. The definition uses the totalized GCR update and does not
enforce convergence.
-/
noncomputable def orthominP (k j : ℕ) : 𝔼 := (orthominAux A b x₀ k j).2.2

/-- The iterate $x_0$ of ORTHOMIN(k) is the initial guess. -/
@[simp] theorem orthominX_zero (k : ℕ) : orthominX A b x₀ k 0 = x₀ := by
  rw [orthominX, orthominAux]

/-- The residual $r_0$ of ORTHOMIN(k) is $b - A x_0$. -/
@[simp] theorem orthominR_zero (k : ℕ) : orthominR A b x₀ k 0 = b - op A x₀ := by
  rw [orthominR, orthominAux]

/-- The first direction of ORTHOMIN(k) is $p_0 = r_0$. -/
@[simp] theorem orthominP_zero (k : ℕ) : orthominP A b x₀ k 0 = orthominR A b x₀ k 0 := by
  rw [orthominP, orthominR, orthominAux]

/-- **Section 6.9** of [saad2003iterative], ORTHOMIN(k) with $k \ge m$ is GCR. Let
$A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $k \ge 0$. For every $j \le k$,
the triple $(x_j, r_j, p_j)$ after $j$ steps of ORTHOMIN(k) is the triple after $j$ steps of GCR
(Algorithm 6.21).

With a window at least as wide as the number of steps taken, no direction is dropped. The
statement holds for every matrix $A$. -/
theorem orthomin_eq_gcr {k : ℕ} : ∀ j ≤ k, orthominAux A b x₀ k j = gcrAux A b x₀ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    cases j with
    | zero => rw [orthominAux, gcrAux]
    | succ j =>
      have hs : (fun i : Fin (j + 1) => orthominAux A b x₀ k (i : ℕ))
          = fun i : Fin (j + 1) => gcrAux A b x₀ (i : ℕ) :=
        funext fun i => ih (i : ℕ) (by omega) (by omega)
      rw [orthominAux, gcrAux, hs, orthominBody_eq_gcrBody A hj]

/-- If $m \le k$, the iterate $x_m$ of ORTHOMIN(k) is the iterate $x_m$ of GCR. -/
theorem orthominX_eq_gcrX {k m : ℕ} (hk : m ≤ k) : orthominX A b x₀ k m = gcrX A b x₀ m := by
  rw [orthominX, gcrX, orthomin_eq_gcr A b x₀ m hk]

/-- One cycle of GCR(m): the iterate $x_m$ after $m$ steps of Algorithm 6.21 from the initial guess
$x_0$.

**Reading.** The source names the restarted variant. Lean defines it as a specified number of cycles
of a fixed length, recomputing the residual from the output iterate at each restart. It also permits
cycles of length zero.
-/
noncomputable def gcrCycle (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼) : 𝔼 :=
  gcrX A b x₀ m

/-- **Section 6.9** of [saad2003iterative], the restarted method GCR(m). For
$A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $m, k \ge 0$, this is the iterate
after $k$ cycles, where each cycle runs $m$ steps of Algorithm 6.21 from the result of the
previous cycle, and the first cycle starts from $x_0$.

The restarted method satisfies no global minimization property, and the book proves none. One
cycle is `SaadSparse.Chapter06.gcrCycle`.

**Reading.** The source names the restarted variant. Lean defines it as a specified number of cycles
of a fixed length, recomputing the residual from the output iterate at each restart. It also permits
cycles of length zero.
-/
noncomputable def gcrRestarted (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼)
    (k : ℕ) : 𝔼 :=
  (gcrCycle A b m)^[k] x₀

/-- GCR(m) after $0$ cycles gives the initial guess $x_0$. -/
@[simp] theorem gcrRestarted_zero (m : ℕ) : gcrRestarted A b m x₀ 0 = x₀ := rfl

/-- GCR(m) after $k + 1$ cycles is one cycle applied to the iterate after $k$ cycles.

**Reading.** The source names the restarted variant. Lean defines it as a specified number of cycles
of a fixed length, recomputing the residual from the output iterate at each restart. It also permits
cycles of length zero.
-/
theorem gcrRestarted_succ (m k : ℕ) :
    gcrRestarted A b m x₀ (k + 1) = gcrCycle A b m (gcrRestarted A b m x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-! ### The GMRES approximation -/

/-- The grade $\mu$ of $v_1 = r_0/\|r_0\|_2$ is the grade of $r_0$, because the two vectors are
proportional. -/
theorem grade_r₀_eq_grade_v₁ : grade A (r₀ A b x₀) = grade A (v₁ A b x₀) := by
  rw [grade_eq, grade_v₁]

/-- GCR computes the GMRES approximation, so it is "mathematically equivalent to the full GMRES
algorithm" (Section 6.9). If $A$ is nonsingular, $A p_i \ne 0$ for every $i < m$, and $m$ is at
most the grade of $r_0$, then the iterate $x_m$ of Algorithm 6.21 is the approximation after $m$
steps of GMRES (Algorithm 6.9).

**Reading.** Lean compares the fixed-length iterates up to the grade, with nonsingularity ensuring
uniqueness of the minimizer and nonzero direction images preventing division by zero. The book
describes the equivalence in terms of the underlying orthogonal Krylov basis.
-/
theorem gcrX_eq_gmresFixed (hA : IsUnit A) {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) : gcrX A b x₀ m = gmresFixed A b x₀ m := by
  have hm' : m ≤ grade A (v₁ A b x₀) := by rwa [← grade_r₀_eq_grade_v₁]
  obtain ⟨z, -, hz⟩ :=
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [hz _ (gcrX_isMinResidualIterate A b x₀ hne hm),
    hz _ (gmresFixed_isMinResidualIterate A b x₀ hm' (isUnit_R_of_isUnit A b x₀ hA hm'))]

/-- ORTHODIR computes the GMRES approximation (Section 6.9). If $A$ is nonsingular, $A p_i \ne 0$
for every $i < m$, and $m$ is at most the grade of $r_0$, then the iterate $x_m$ of ORTHODIR is
the approximation after $m$ steps of GMRES (Algorithm 6.9).

**Reading.** Lean compares the fixed-length iterates up to the grade, with nonsingularity ensuring
uniqueness of the minimizer and nonzero direction images preventing division by zero. The book
describes the equivalence in terms of the underlying orthogonal Krylov basis.
-/
theorem orthodirX_eq_gmresFixed (hA : IsUnit A) {m : ℕ}
    (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0) (hm : m ≤ grade A (r₀ A b x₀)) :
    orthodirX A b x₀ m = gmresFixed A b x₀ m := by
  have hm' : m ≤ grade A (v₁ A b x₀) := by rwa [← grade_r₀_eq_grade_v₁]
  obtain ⟨z, -, hz⟩ :=
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [hz _ (orthodirX_isMinResidualIterate A b x₀ hne hm),
    hz _ (gmresFixed_isMinResidualIterate A b x₀ hm' (isUnit_R_of_isUnit A b x₀ hA hm'))]

end General

/-! ### The results of Section 6.9, over the real numbers -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- **Lemma 6.21** of [saad2003iterative], with (6.104) and (6.105). Let
$A \in \mathbb{R}^{n \times n}$, let $b, x_0 \in \mathbb{R}^n$ and $r_0 = b - A x_0$. Let
$p_0, \dots, p_{m-1}$ span $\mathcal{K}_m(A, r_0)$, be $A^T A$-orthogonal, $(A p_i, A p_l) = 0$
for $i \ne l$, and satisfy $A p_i \ne 0$. Let $x_0, x_1, \dots$ be produced by (6.105),
$$x_{j+1} = x_j + \frac{(r_j, A p_j)}{(A p_j, A p_j)} p_j, \qquad r_j = b - A x_j.$$
Then $x_m$ has the smallest residual norm in $x_0 + \mathcal{K}_m(A, r_0)$, and
$$x_m = x_0 + \sum_{i=0}^{m-1} \frac{(r_0, A p_i)}{(A p_i, A p_i)} p_i. \quad (6.104)$$

**Reading.** The source asks that $\{p_0, \dots, p_{j-1}\}$ be a basis of
$\mathcal{K}_j(A, r_0)$ for each $j \le m$, and its formulas divide by $(A p_i, A p_i)$. The
statement here asks only that $p_0, \dots, p_{m-1}$ span $\mathcal{K}_m(A, r_0)$, and it makes
the nonvanishing of the denominators, $A p_i \ne 0$, an explicit hypothesis. With the
orthogonality these conditions make $p_0, \dots, p_{m-1}$ a basis of $\mathcal{K}_m(A, r_0)$;
bases of the smaller subspaces $\mathcal{K}_j$ are not needed.

The update (6.105) is assumed for every $j$, and $p_i$ is defined for every $i$; only
$p_0, \dots, p_{m-1}$ enter the hypotheses. The minimal-residual property is
`Krylov.IsMinResidualIterate`, and the form over the scalar field `𝕜` is
`SaadSparse.Chapter06.isMinResidualIterate_of_orthogonalDirections`. -/
theorem lemma_6_21 {m : ℕ} (p : ℕ → EuclideanSpace ℝ (Fin n))
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner ℝ (op A (p i)) (op A (p l)) = 0)
    (hne : ∀ i < m, op A (p i) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range fun i : Fin m => p (i : ℕ)) = krylov A (r₀ A b x₀) m)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner ℝ (op A (p j)) (b - op A (x j)) / inner ℝ (op A (p j)) (op A (p j))) • p j) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (x m) ∧
      x m = x₀ + ∑ i ∈ Finset.range m,
        (inner ℝ (op A (p i)) (r₀ A b x₀) / inner ℝ (op A (p i)) (op A (p i))) • p i :=
  ⟨isMinResidualIterate_of_orthogonalDirections A b x₀ p horth hne hspan x hx0 hstep,
    equation_6_104 A b x₀ p horth x hx0 hstep⟩

/-- **Algorithm 6.21** of [saad2003iterative], GCR is mathematically equivalent to full GMRES. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b, x_0 \in \mathbb{R}^n$, let $m$ be at
most the grade of $r_0$, and let the directions $p_i$ of Algorithm 6.21 satisfy $A p_i \ne 0$
for $i < m$. Then the directions are $A^T A$-orthogonal, $(A p_i, A p_l) = 0$ for $i \ne l < m$;
the iterate $x_m$ minimizes the residual norm over $x_0 + \mathcal{K}_m(A, r_0)$; and $x_m$ is
the approximation after $m$ steps of GMRES (Algorithm 6.9).

The GMRES approximation is `SaadSparse.Chapter06.gmresFixed`. The nonsingularity of $A$ is used
only for the last conclusion.

**Reading.** Lean compares the fixed-length iterates up to the grade, with nonsingularity ensuring
uniqueness of the minimizer and nonzero direction images preventing division by zero. The book
describes the equivalence in terms of the underlying orthogonal Krylov basis.
-/
theorem algorithm_6_21_eq_gmres (hA : IsUnit A) {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    (∀ i < m, ∀ l < m, i ≠ l → inner ℝ (op A (gcrP A b x₀ i)) (op A (gcrP A b x₀ l)) = 0) ∧
      Krylov.IsMinResidualIterate (op A) b x₀ m (gcrX A b x₀ m) ∧
      gcrX A b x₀ m = gmresFixed A b x₀ m :=
  ⟨inner_apply_gcrP_eq_zero A b x₀ hne, gcrX_isMinResidualIterate A b x₀ hne hm,
    gcrX_eq_gmresFixed A b x₀ hA hne hm⟩

/-- Section 6.9: ORTHODIR is mathematically equivalent to full GMRES. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $m$ be at most the grade of $r_0$, and let
the ORTHODIR directions satisfy $A p_i \ne 0$ for $i < m$. Then $(A p_i, A p_l) = 0$ for
$i \ne l < m$, the iterate $x_m$ minimizes the residual norm over $x_0 + \mathcal{K}_m(A, r_0)$,
and $x_m$ is the approximation after $m$ steps of GMRES.

**Reading.** Lean compares the fixed-length iterates up to the grade, with nonsingularity ensuring
uniqueness of the minimizer and nonzero direction images preventing division by zero. The book
describes the equivalence in terms of the underlying orthogonal Krylov basis.
-/
theorem orthodir_eq_gmres (hA : IsUnit A) {m : ℕ}
    (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0) (hm : m ≤ grade A (r₀ A b x₀)) :
    (∀ i < m, ∀ l < m, i ≠ l →
        inner ℝ (op A (orthodirP A b x₀ i)) (op A (orthodirP A b x₀ l)) = 0) ∧
      Krylov.IsMinResidualIterate (op A) b x₀ m (orthodirX A b x₀ m) ∧
      orthodirX A b x₀ m = gmresFixed A b x₀ m :=
  ⟨inner_apply_orthodirP_eq_zero A b x₀ hne, orthodirX_isMinResidualIterate A b x₀ hne hm,
    orthodirX_eq_gmresFixed A b x₀ hA hne hm⟩

/-- Section 6.9: if $m \le k$, the iterate $x_m$ of ORTHOMIN(k) is the iterate $x_m$ of GCR, over
$\mathbb{R}$. -/
theorem orthomin_eq_gcr_book {k m : ℕ} (hk : m ≤ k) :
    orthominX A b x₀ k m = gcrX A b x₀ m :=
  orthominX_eq_gcrX A b x₀ hk

end BookResults

end SaadSparse.Chapter06
