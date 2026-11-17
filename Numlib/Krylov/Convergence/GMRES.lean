/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Iterate

/-!
# Orthogonal residual expansions for GMRES

A basis adapted to the increasing family of image Krylov subspaces gives the GMRES
residual as a sum of the basis coefficients outside the current subspace. Each step
removes one orthogonal term.
-/

open Finset

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem inner_prefix (d : ℕ) {w : Fin d → E} (hw : Orthonormal 𝕜 w)
    (r : E) (n : ℕ) (i : Fin d) :
    inner 𝕜 (w i) (∑ j : Fin d with j.val < n, inner 𝕜 (w j) r • w j) =
      if i.val < n then inner 𝕜 (w i) r else 0 := by
  classical
  rw [inner_sum]
  simp only [inner_smul_right, (orthonormal_iff_ite.mp hw), mul_ite, mul_one, mul_zero]
  by_cases hi : i.val < n
  · rw [ite_eq_left hi, sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hi'
      exact False.elim (hi' (by simpa using hi))
  · rw [ite_eq_right hi]
    refine sum_eq_zero fun j hj => ?_
    have hij : i ≠ j := by
      intro he
      subst j
      exact hi (by simpa using hj)
    simp [hij]

private theorem mem_span_prefix (d : ℕ) (w : Fin d → E) (n : ℕ) (c : Fin d → 𝕜) :
    ∑ i : Fin d with i.val < n, c i • w i ∈
      Submodule.span 𝕜 (w '' {i | i.val < n}) := by
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, ?_, rfl⟩)
  simpa using hi

variable {A : E →ₗ[𝕜] E} {b x₀ : E}

/-- Let an orthonormal family $(w_i)$ have a prefix of length $n$ spanning $A\mathcal K_n$.
If $x_n$ is the GMRES iterate, its residual is $r_0$ minus the prefix of the orthogonal
expansion of $r_0$ in that family. -/
theorem IsMinResidualIterate.residual_eq_sub_sum_prefix {d n : ℕ} {w : Fin d → E}
    (hw : Orthonormal 𝕜 w)
    (hspan : Submodule.span 𝕜 (w '' {i | i.val < n}) = (subspace A (b - A x₀) n).map A)
    {x : E} (hx : IsMinResidualIterate A b x₀ n x) :
    b - A x = (b - A x₀) - ∑ i : Fin d with i.val < n, inner 𝕜 (w i) (b - A x₀) • w i := by
  let S := Submodule.span 𝕜 (w '' {i | i.val < n})
  let P := ∑ i : Fin d with i.val < n, inner 𝕜 (w i) (b - A x₀) • w i
  have hP : P ∈ S := mem_span_prefix d w n _
  have hxS : A (x - x₀) ∈ S := by
    dsimp only [S]
    rw [hspan]
    exact Submodule.mem_map_of_mem hx.mem
  have hxr : b - A x ∈ Sᗮ := by
    dsimp only [S]
    rw [hspan]
    exact hx.residual_mem_orthogonal
  have hsub : (b - A x₀) - P ∈ Sᗮ := by
    apply Submodule.mem_orthogonal_span.2
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i.val < n := hi
    rw [inner_sub_right, inner_prefix d hw, ite_eq_left hi', sub_self]
  have he : A (x - x₀) - P = ((b - A x₀) - P) - (b - A x) := by
    rw [map_sub]
    abel
  have hm : A (x - x₀) - P ∈ S ⊓ Sᗮ :=
    ⟨Submodule.sub_mem _ hxS hP, he.symm ▸ Submodule.sub_mem _ hsub hxr⟩
  rw [S.inf_orthogonal_eq_bot, Submodule.mem_bot, he, sub_eq_zero] at hm
  exact hm.symm

variable [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Let $A$ be injective and let the residual $r_0=b-Ax_0$ have finite grade $d$.
Suppose an orthonormal family $(w_i)$ of size $d$ is adapted to the mapped Krylov flag:
its first $n$ vectors span $A\mathcal K_n$ for each $n\le d$. For each $n\le d$ the GMRES
residual is the tail of the expansion of $r_0$ in this family. -/
theorem IsMinResidualIterate.residual_eq_sum_tail (hinj : Function.Injective A)
    {w : Fin (grade A (b - A x₀)) → E} (hw : Orthonormal 𝕜 w)
    (hspan : ∀ n ≤ grade A (b - A x₀),
      Submodule.span 𝕜 (w '' {i | i.val < n}) = (subspace A (b - A x₀) n).map A)
    {x : ℕ → E} (hx : ∀ n, IsMinResidualIterate A b x₀ n (x n))
    {n : ℕ} (hn : n ≤ grade A (b - A x₀)) :
    b - A (x n) =
      ∑ i : Fin (grade A (b - A x₀)) with n ≤ i.val, inner 𝕜 (w i) (b - A x₀) • w i := by
  let d := grade A (b - A x₀)
  have hterm : A (x d) = b := (hx d).apply_eq_of_grade_le le_rfl hinj.injOn
  have hd := (hx d).residual_eq_sub_sum_prefix hw (hspan d le_rfl)
  rw [hterm, sub_self] at hd
  have hd' : b - A x₀ = ∑ i : Fin d, inner 𝕜 (w i) (b - A x₀) • w i := by
    have h := sub_eq_zero.mp hd.symm
    rw [Finset.sum_filter] at h
    refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact ite_eq_left i.isLt
  have hs := (hx n).residual_eq_sub_sum_prefix hw (hspan n hn)
  have he := sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < n)
    (fun i : Fin d => inner 𝕜 (w i) (b - A x₀) • w i)
  simp only [not_lt] at he
  suffices h : b - A (x n) = (∑ i : Fin d, inner 𝕜 (w i) (b - A x₀) • w i) -
      ∑ i : Fin d with i.val < n, inner 𝕜 (w i) (b - A x₀) • w i by
    rw [h, ← he]
    abel
  rw [hs]
  exact congrArg (fun v => v - (∑ i : Fin d with i.val < n, inner 𝕜 (w i) (b - A x₀) • w i)) hd'


omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- With the adapted orthonormal family of `Krylov.IsMinResidualIterate.residual_eq_sum_tail`,
the $(n+1)$-st step removes the term $w_n\langle w_n,r_0\rangle$ from $r_n$. This term is
orthogonal to $r_{n+1}$, so the squared residual norm decreases by $|\langle w_n,r_0\rangle|^2$.
The coefficient can also be read as $\langle w_n,r_n\rangle$. Indices begin at zero. -/
theorem IsMinResidualIterate.residual_succ_decomposition
    {w : Fin (grade A (b - A x₀)) → E} (hw : Orthonormal 𝕜 w)
    (hspan : ∀ n ≤ grade A (b - A x₀),
      Submodule.span 𝕜 (w '' {i | i.val < n}) = (subspace A (b - A x₀) n).map A)
    {x : ℕ → E} (hx : ∀ n, IsMinResidualIterate A b x₀ n (x n))
    (j : Fin (grade A (b - A x₀))) :
    b - A (x j.val) = inner 𝕜 (w j) (b - A x₀) • w j + (b - A (x (j.val + 1))) ∧
    inner 𝕜 (w j) (b - A (x j.val)) = inner 𝕜 (w j) (b - A x₀) ∧
    ‖b - A (x j.val)‖ ^ 2 - ‖b - A (x (j.val + 1))‖ ^ 2 =
      ‖inner 𝕜 (w j) (b - A x₀)‖ ^ 2 := by
  let d := grade A (b - A x₀)
  let r (n : ℕ) := b - A (x n)
  let c (i : Fin d) := inner 𝕜 (w i) (b - A x₀)
  let p (n : ℕ) := univ.filter (fun i : Fin d => i.val < n)
  have hp : p (j.val + 1) = insert j (p j.val) := by
    ext i
    simp only [p, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hi
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
      · exact Or.inl (Fin.ext he)
      · exact Or.inr hl
    · rintro (rfl | hi) <;> omega
  have hj : j ∉ p j.val := by simp [p]
  have hs (n : ℕ) (hn : n ≤ d) :
      r n = (b - A x₀) - ∑ i ∈ p n, c i • w i :=
    (hx n).residual_eq_sub_sum_prefix hw (hspan n hn)
  have he : r j.val = c j • w j + r (j.val + 1) := by
    rw [hs j.val j.isLt.le, hs (j.val + 1) (Nat.succ_le_of_lt j.isLt), hp, sum_insert hj]
    abel
  have how : w j ∈ (subspace A (b - A x₀) (j.val + 1)).map A := by
    rw [← hspan _ (Nat.succ_le_of_lt j.isLt)]
    exact Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩
  have ho : inner 𝕜 (w j) (r (j.val + 1)) = 0 :=
    (Submodule.mem_orthogonal _ _).1 (hx (j.val + 1)).residual_mem_orthogonal _ how
  refine ⟨he, ?_, ?_⟩
  · change inner 𝕜 (w j) (r j.val) = c j
    rw [he, inner_add_right, inner_smul_right, ho, add_zero, (orthonormal_iff_ite.mp hw)]
    simp
  · change ‖r j.val‖ ^ 2 - ‖r (j.val + 1)‖ ^ 2 = ‖c j‖ ^ 2
    have hh : inner 𝕜 (c j • w j) (r (j.val + 1)) = 0 := by
      rw [inner_smul_left, ho, mul_zero]
    conv_lhs =>
      lhs
      rw [he, norm_add_sq (𝕜 := 𝕜), hh, map_zero, mul_zero, add_zero,
        norm_smul, hw.norm_eq_one, mul_one]
    ring

end Krylov
