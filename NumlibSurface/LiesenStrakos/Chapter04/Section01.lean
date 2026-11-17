import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Numlib.Krylov.Subspace

/-!
# Liesen and Strakoš, Section 4.1: CG-like descent methods

Section 4.1 of [liesen2013krylov] relates error minimization over successive direction spans
to the choice of line-search coefficients and the mutual orthogonality of those directions.
The given positive definite inner product is the inner product of the ambient space.

## Main definitions

* Equations (4.1.1)–(4.1.2), `LiesenStrakos.IsCGLikeDescent`: the direction spans are
  Krylov spaces and the iterates minimize the error over the corresponding affine spaces.

## Main results

* Lemma 4.1.1 (1), `LiesenStrakos.lemma_4_1_1_forward`: orthogonal directions
  and nonzero line-search coefficients give successive error minimization.
* Lemma 4.1.1 (2), `LiesenStrakos.lemma_4_1_1_backward`: successive error minimization
  and nonzero line-search numerators give the coefficients and orthogonality.
-/

open scoped InnerProductSpace

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The linear span of $p_0,\dots,p_{j-1}$, where $p_i$ are the successive search directions. -/
def directionSpan (p : ℕ → E) (j : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (p '' Set.Iio j)

private theorem directionSpan_mono (p : ℕ → E) {i j : ℕ} (h : i ≤ j) :
    directionSpan (𝕜 := 𝕜) p i ≤ directionSpan p j :=
  Submodule.span_mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi h))

private theorem direction_mem_span (p : ℕ → E) {i j : ℕ} (h : i < j) :
    p i ∈ directionSpan (𝕜 := 𝕜) p j :=
  Submodule.subset_span ⟨i, h, rfl⟩

/-- At step $j$, $u_j$ minimizes the distance to $x$ over the affine space obtained by translating
the first $j$ search directions' span by $u_0$. -/
def IsDirectionErrorMinimizer (x : E) (u p : ℕ → E) (j : ℕ) : Prop :=
  ‖x - u j‖ = ⨅ z : directionSpan (𝕜 := 𝕜) p j, ‖x - (u 0 + z)‖

/-- A CG-like descent method updates $u_j$ along a nonzero direction $p_j$. The span of the
first $j$ directions is the $j$-th Krylov subspace of $A$ at $b-Au_0$, and $u_j$ minimizes
the error norm on the corresponding affine space. These are the conditions around (4.1.1)
and (4.1.2) in [liesen2013krylov]. -/
def IsCGLikeDescent (A : Module.End 𝕜 E) (x b : E) (u p : ℕ → E) (α : ℕ → 𝕜)
    (n : ℕ) : Prop :=
  A x = b ∧
    (∀ j < n, p j ≠ 0 ∧ u (j + 1) = u j + α j • p j) ∧
    ∀ j ≤ n, directionSpan (𝕜 := 𝕜) p j = Krylov.subspace A (b - A (u 0)) j ∧
      IsDirectionErrorMinimizer (𝕜 := 𝕜) x u p j

private theorem step_diff_mem {u p : ℕ → E} {α : ℕ → 𝕜} {n : ℕ}
    (hstep : ∀ j < n, u (j + 1) = u j + α j • p j) {j : ℕ} (hj : j ≤ n) :
    u j - u 0 ∈ directionSpan (𝕜 := 𝕜) p j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp := direction_mem_span (𝕜 := 𝕜) p (Nat.lt_succ_self j)
    have hu := directionSpan_mono (𝕜 := 𝕜) p (Nat.le_succ j) (ih (by omega))
    rw [hstep j (by omega), add_comm (u j), add_sub_assoc]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hp) hu

private theorem isDirectionErrorMinimizer_iff {x : E} {u p : ℕ → E} {j : ℕ}
    (hu : u j - u 0 ∈ directionSpan (𝕜 := 𝕜) p j) :
    IsDirectionErrorMinimizer (𝕜 := 𝕜) x u p j ↔
      ∀ i < j, inner 𝕜 (p i) (x - u j) = 0 := by
  have he : x - u 0 - (u j - u 0) = x - u j := by abel
  have ha (z : directionSpan (𝕜 := 𝕜) p j) : x - (u 0 + z) = x - u 0 - z := by abel
  have hproj := (directionSpan (𝕜 := 𝕜) p j).norm_eq_iInf_iff_inner_eq_zero
    (u := x - u 0) hu
  rw [he] at hproj
  simp only [IsDirectionErrorMinimizer, ha, hproj]
  refine ⟨fun h i hi => inner_eq_zero_symm.mp (h _ (direction_mem_span p hi)), fun h w hw => ?_⟩
  have hincl : directionSpan (𝕜 := 𝕜) p j ≤ (𝕜 ∙ (x - u j)).orthogonal := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (h i hi)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hincl hw)

private theorem inner_error_step {x : E} {u p : ℕ → E} {α : ℕ → 𝕜} {i j : ℕ}
    (hstep : u (j + 1) = u j + α j • p j) :
    inner 𝕜 (p i) (x - u (j + 1)) =
      inner 𝕜 (p i) (x - u j) - α j * inner 𝕜 (p i) (p j) := by
  rw [hstep, ← sub_sub, inner_sub_right, inner_smul_right]

/-- Pairwise orthogonal nonzero directions with nonzero line-search coefficients yield minimal
errors in every successive affine span. This is Lemma 4.1.1 (1) of [liesen2013krylov]. -/
theorem lemma_4_1_1_forward {x : E} {u p : ℕ → E} {α : ℕ → 𝕜} {n : ℕ}
    (hstep : ∀ j < n, u (j + 1) = u j + α j • p j)
    (hp : ∀ j < n, p j ≠ 0)
    (hα : ∀ j < n, α j = inner 𝕜 (p j) (x - u j) / inner 𝕜 (p j) (p j) ∧ α j ≠ 0)
    (hortho : ∀ i < n, ∀ j < n, i ≠ j → inner 𝕜 (p i) (p j) = 0) :
    ∀ j ≤ n, IsDirectionErrorMinimizer (𝕜 := 𝕜) x u p j := by
  have herr : ∀ j ≤ n, ∀ i < j, inner 𝕜 (p i) (x - u j) = 0 := by
    intro j hj
    induction j with
    | zero => exact fun _ hi => (Nat.not_lt_zero _ hi).elim
    | succ j ih =>
      intro i hi
      have hjn : j < n := by omega
      rw [inner_error_step (hstep j hjn)]
      by_cases hij : i = j
      · subst i
        rw [(hα j hjn).1, div_mul_cancel₀ _ (inner_self_ne_zero.2 (hp j hjn)), sub_self]
      · rw [ih (by omega) i (by omega), hortho i (by omega) j hjn hij, mul_zero, sub_zero]
  exact fun j hj => (isDirectionErrorMinimizer_iff (step_diff_mem hstep hj)).2 (herr j hj)

/-- Successive error minimization and nonzero line-search numerators give the nonzero
line-search coefficients and pairwise orthogonality. This is Lemma 4.1.1 (2) of
[liesen2013krylov]. -/
theorem lemma_4_1_1_backward {x : E} {u p : ℕ → E} {α : ℕ → 𝕜} {n : ℕ}
    (hstep : ∀ j < n, u (j + 1) = u j + α j • p j)
    (hp : ∀ j < n, p j ≠ 0)
    (hmin : ∀ j ≤ n, IsDirectionErrorMinimizer (𝕜 := 𝕜) x u p j)
    (hnonzero : ∀ j < n, inner 𝕜 (p j) (x - u j) ≠ 0) :
    (∀ j < n, α j = inner 𝕜 (p j) (x - u j) / inner 𝕜 (p j) (p j) ∧ α j ≠ 0) ∧
      ∀ i < n, ∀ j < n, i ≠ j → inner 𝕜 (p i) (p j) = 0 := by
  have herr (j : ℕ) (hj : j ≤ n) :=
    (isDirectionErrorMinimizer_iff (step_diff_mem hstep hj)).1 (hmin j hj)
  have hα : ∀ j < n, α j = inner 𝕜 (p j) (x - u j) / inner 𝕜 (p j) (p j) ∧ α j ≠ 0 := by
    intro j hj
    have hd := herr (j + 1) (by omega) j (Nat.lt_succ_self _)
    rw [inner_error_step (hstep j hj), sub_eq_zero] at hd
    have hn := inner_self_ne_zero (𝕜 := 𝕜) |>.2 (hp j hj)
    refine ⟨(eq_div_iff hn).2 hd.symm, ?_⟩
    intro h
    exact hnonzero j hj (by simpa [h] using hd)
  have hortho (i j : ℕ) (hij : i < j) (hj : j < n) : inner 𝕜 (p i) (p j) = 0 := by
    have hd := herr (j + 1) (by omega) i (by omega)
    rw [inner_error_step (hstep j hj), herr j hj.le i hij, zero_sub, neg_eq_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left (hα j hj).2
  refine ⟨hα, fun i hi j hj hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hortho i j h hj
  · exact inner_eq_zero_symm.mp (hortho j i h hi)

end LiesenStrakos
