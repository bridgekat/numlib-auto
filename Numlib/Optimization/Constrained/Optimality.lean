import Numlib.Optimization.Unconstrained.Optimality
import Numlib.Analysis.Calculus.LocalExtr.RightDerivative
import Mathlib.Tactic

/-!
# Necessary optimality conditions along convex feasible rays

A feasible displacement supplies a segment through a constrained local minimizer.
Its one-sided scalar restriction gives the variational inequality, a nonnegative Hessian
quadratic form on first-order critical directions, and a nonnegative cubic derivative on
directions where both lower directional derivatives vanish. Smoothness is required only
on an open neighborhood of the convex feasible set.
-/

open Set Filter Topology

namespace Constrained

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A locally minimizing function restricted to a feasible convex ray has a
nonnegative first nonvanishing directional derivative. -/
theorem higher_directional_nonneg {f : E → ℝ} {C S : Set E} {x v : E} {k : ℕ}
    (hk : 0 < k) (hC : Convex ℝ C) (hx : x ∈ C) (hv : x + v ∈ C)
    (hmin : IsLocalMinOn f C x) (hS : IsOpen S) (hCS : C ⊆ S)
    (hf : ContDiffOn ℝ k f S)
    (hzero : ∀ j, 0 < j → j < k →
      iteratedDeriv j (fun t : ℝ => f (x + t • v)) 0 = 0) :
    0 ≤ iteratedDeriv k (fun t : ℝ => f (x + t • v)) 0 := by
  have hline : ContDiff ℝ k (fun t : ℝ => x + t • v) := by fun_prop
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ C := by
    intro t ht
    simpa using hC.add_smul_sub_mem hx hv ht
  have hmline : IsLocalMinOn (fun t : ℝ => f (x + t • v)) (Icc 0 1) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMinOn f C (x + (0 : ℝ) • v) by simpa using hmin).comp_continuousOn
        (s := Icc (0 : ℝ) 1) (g := fun t : ℝ => x + t • v) hmem
        hline.continuous.continuousOn (by simp)
  have hfline : ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ k (fun t : ℝ => f (x + t • v)) t := by
    intro t ht
    exact (hf.contDiffAt (hS.mem_nhds (hCS (hmem t ht)))).comp t hline.contDiffAt
  exact hmline.iteratedDeriv_nonneg_of_lower_eq_zero hk hfline hzero

/-- The first-order variational inequality on a convex feasible set. -/
theorem first_order_nonneg {f : E → ℝ} {C S : Set E} {x v : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hv : x + v ∈ C)
    (hmin : IsLocalMinOn f C x) (hS : IsOpen S) (hCS : C ⊆ S)
    (hf : ContDiffOn ℝ 1 f S) : 0 ≤ fderiv ℝ f x v := by
  have hdiff := (hf.contDiffAt (hS.mem_nhds (hCS hx))).differentiableAt (by norm_num)
  simpa using Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn hC hx hmin
    hdiff.hasFDerivAt (x + v) hv

/-- The Hessian is nonnegative along a feasible displacement orthogonal to the gradient. -/
theorem second_order_nonneg {f : E → ℝ} {C S : Set E} {x v : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hv : x + v ∈ C)
    (hmin : IsLocalMinOn f C x) (hS : IsOpen S) (hCS : C ⊆ S)
    (hf : ContDiffOn ℝ 2 f S) (hfirst : fderiv ℝ f x v = 0) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hS.mem_nhds (hCS hx))
  have hderiv : deriv (fun t : ℝ => f (x + t • v)) 0 = fderiv ℝ f x v := by
    simpa using ((hfx.differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt v).deriv
  have hzero : ∀ j : ℕ, 0 < j → j < 2 →
      iteratedDeriv j (fun t : ℝ => f (x + t • v)) 0 = 0 := by
    intro j hj hj2
    have : j = 1 := by omega
    subst j
    simpa [iteratedDeriv_one, hderiv] using hfirst
  have h := higher_directional_nonneg (by norm_num : 0 < 2) hC hx hv hmin hS hCS hf hzero
  rwa [Descent.iteratedDeriv_two_affineLine x hfx v] at h

/-- The third derivative is nonnegative along a feasible displacement where the
first and second directional derivatives vanish. -/
theorem third_order_nonneg {f : E → ℝ} {C S : Set E} {x v : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hv : x + v ∈ C)
    (hmin : IsLocalMinOn f C x) (hS : IsOpen S) (hCS : C ⊆ S)
    (hf : ContDiffOn ℝ 3 f S) (hfirst : fderiv ℝ f x v = 0)
    (hsecond : fderiv ℝ (fderiv ℝ f) x v v = 0) :
    0 ≤ iteratedFDeriv ℝ 3 f x (fun _ => v) := by
  have hfx : ContDiffAt ℝ 3 f x := hf.contDiffAt (hS.mem_nhds (hCS hx))
  have hderiv : deriv (fun t : ℝ => f (x + t • v)) 0 = fderiv ℝ f x v := by
    simpa using ((hfx.differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt v).deriv
  have hzero : ∀ j : ℕ, 0 < j → j < 3 →
      iteratedDeriv j (fun t : ℝ => f (x + t • v)) 0 = 0 := by
    intro j hj hj3
    have hjcases : j = 1 ∨ j = 2 := by omega
    rcases hjcases with rfl | rfl
    · simpa [iteratedDeriv_one, hderiv] using hfirst
    · rw [Descent.iteratedDeriv_two_affineLine x (hfx.of_le (by norm_num)) v, hsecond]
  have h := higher_directional_nonneg (by norm_num : 0 < 3) hC hx hv hmin hS hCS hf hzero
  rwa [Descent.iteratedDeriv_three_affineLine x hfx v] at h

end Constrained
