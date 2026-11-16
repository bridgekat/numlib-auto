/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Operations`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp

/-!
# Functions of one coordinate of a Euclidean space

Let $\iota$ be a finite index set, let $g : \mathbb{R} \to \mathbb{R}$, and let $i \in \iota$. This
module studies the function $w \mapsto g(w_i)$ on the Euclidean space $\mathbb{R}^\iota$
(`EuclideanSpace ℝ ι`). It is $C^n$ at $v$ when $g$ is $C^n$ at $v_i$, and its $k$-th derivative
tensor is
$$\nabla^k \big(w \mapsto g(w_i)\big)(v)[m_1, \dots, m_k] = g^{(k)}(v_i) \prod_{j=1}^{k} (m_j)_i,$$
with norm at most $|g^{(k)}(v_i)|$.

## Main results

* `ContDiffAt.comp_coord`: the smoothness of $w \mapsto g(w_i)$.
* `ContDiffAt.iteratedFDeriv_comp_coord_apply`: the formula for its derivative tensors.
* `ContDiffAt.norm_iteratedFDeriv_comp_coord_le`: the bound of the norm of its derivative tensors.
-/

open Finset

section Coord

variable {ι : Type*} [Fintype ι] {g : ℝ → ℝ} {v : EuclideanSpace ℝ ι} {k : ℕ}

/-- The coordinate projection $w \mapsto w_i$ of $\mathbb{R}^\iota$ has operator norm at most $1$.
-/
theorem EuclideanSpace.norm_proj_le (i : ι) :
    ‖(EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul]
  simpa using PiLp.norm_apply_le w i

/-- In $\mathbb{R}^\iota$, $|w_i| \le \|w\|$ for every $w$ and every $i \in \iota$. -/
theorem EuclideanSpace.abs_apply_le_norm (w : EuclideanSpace ℝ ι) (i : ι) : |w i| ≤ ‖w‖ := by
  simpa using PiLp.norm_apply_le w i

/-- If $g : \mathbb{R} \to \mathbb{R}$ is $C^n$ at $v_i$, then $w \mapsto g(w_i)$ is $C^n$ at
$v \in \mathbb{R}^\iota$. Here $n$ can be infinite or $\omega$. -/
theorem ContDiffAt.comp_coord {n : WithTop ℕ∞} (i : ι) (hg : ContDiffAt ℝ n g (v i)) :
    ContDiffAt ℝ n (fun w : EuclideanSpace ℝ ι => g (w i)) v :=
  hg.comp v (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff.contDiffAt

/-- If $g$ is $C^k$ at $v_i$, then $\nabla^k (w \mapsto g(w_i))(v)$ is the $k$-linear map
$g^{(k)}(v_i)$ composed in each argument with the projection $w \mapsto w_i$:
$$\nabla^k \big(w \mapsto g(w_i)\big)(v)[m_1, \dots, m_k] = \nabla^k g(v_i)[(m_1)_i, \dots,
  (m_k)_i].$$
-/
theorem ContDiffAt.iteratedFDeriv_comp_coord (i : ι) (hg : ContDiffAt ℝ k g (v i)) :
    iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v =
      (iteratedFDeriv ℝ k g (v i)).compContinuousLinearMap
        fun _ => (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  hg.iteratedFDeriv_comp_continuousLinearMap (EuclideanSpace.proj i) le_rfl

/-- If $g$ is $C^k$ at $v_i$, then for all $m_1, \dots, m_k \in \mathbb{R}^\iota$
$$\nabla^k \big(w \mapsto g(w_i)\big)(v)[m_1, \dots, m_k] = g^{(k)}(v_i) \prod_{j=1}^{k}
  (m_j)_i.$$
-/
theorem ContDiffAt.iteratedFDeriv_comp_coord_apply (i : ι) (hg : ContDiffAt ℝ k g (v i))
    (m : Fin k → EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v m =
      iteratedDeriv k g (v i) * ∏ j, m j i := by
  rw [hg.iteratedFDeriv_comp_coord i, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul, mul_comm]
  rfl

/-- If $g$ is $C^k$ at $v_i$, then for every $h \in \mathbb{R}^\iota$
$$\nabla^k \big(w \mapsto g(w_i)\big)(v)[h, \dots, h] = g^{(k)}(v_i) \, h_i^k.$$
-/
theorem ContDiffAt.iteratedFDeriv_comp_coord_apply_const (i : ι) (hg : ContDiffAt ℝ k g (v i))
    (h : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v (fun _ => h) =
      iteratedDeriv k g (v i) * h i ^ k := by
  rw [hg.iteratedFDeriv_comp_coord_apply i, prod_const, card_univ, Fintype.card_fin]

/-- If $g$ is $C^k$ at $v_i$, then $\|\nabla^k (w \mapsto g(w_i))(v)\| \le |g^{(k)}(v_i)|$. -/
theorem ContDiffAt.norm_iteratedFDeriv_comp_coord_le (i : ι) (hg : ContDiffAt ℝ k g (v i)) :
    ‖iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v‖ ≤
      |iteratedDeriv k g (v i)| := by
  rw [hg.iteratedFDeriv_comp_coord i]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [prod_const, card_univ, Fintype.card_fin, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (EuclideanSpace.norm_proj_le i))

end Coord
