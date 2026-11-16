/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MultivariateTaylor.Basic

/-!
# Taylor polynomials of linear compositions and of finite sums

Let $E$, $F$ and $G$ be real normed spaces. For $f \colon E \to F$ and a point $x \in E$, the Taylor
polynomial of degree $p$ of $f$ at $x$ is $T_{f,p}(x, s) = \sum_{i=0}^{p} \frac{1}{i!} \nabla^i
f(x)[s]^i$ (`taylorPolynomial`, from `Numlib.Analysis.Calculus.MultivariateTaylor.Basic`). This
module shows that the Taylor polynomial commutes with composition on the right by a continuous
linear map, with multiplication by a fixed vector, and with finite sums. Only smoothness at the base
point is assumed.

Together these rules give the Taylor models of a partially separable function
$f = \sum_i f_i \circ U_i$:
$$T_{f,p}(x, s) = \sum_i T_{f_i,p}(U_i x, U_i s),$$
as in (5.2.2) of [cartis2022evaluation].

## Main results

* `taylorPolynomial_comp_continuousLinearMap`: $T_{g \circ U, p}(x, s) = T_{g, p}(Ux, Us)$ for a
  continuous linear map $U$.
* `taylorPolynomial_smul_const`: $T_{g v, p}(x, s) = T_{g, p}(x, s) \, v$ for a real-valued $g$ and
  a fixed vector $v$.
* `taylorPolynomial_finset_sum`: $T_{\sum_i f_i, p}(x, s) = \sum_i T_{f_i, p}(x, s)$.
* `taylorPolynomial_finset_sum_comp_continuousLinearMap`: the Taylor model of a partially separable
  function.
-/

open Finset Filter
open scoped Nat Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Let $U \colon E \to F$ be a continuous linear map, let $x \in E$, and let $g \colon F \to G$ be
of class $C^n$ at $Ux$. Then for every $i \le n$,
$$\nabla^i (g \circ U)(x) = \nabla^i g(Ux) \circ (U, \dots, U).$$

This is a pointwise version of `ContinuousLinearMap.iteratedFDeriv_comp_right`. -/
theorem ContDiffAt.iteratedFDeriv_comp_continuousLinearMap {g : F → G} (U : E →L[ℝ] F) {x : E}
    {n : ℕ} (hg : ContDiffAt ℝ n g (U x)) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (g ∘ U) x =
      (iteratedFDeriv ℝ i g (U x)).compContinuousLinearMap fun _ => U := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨t, htu, ht, hxt⟩ := mem_nhds_iff.1 hu
  have hpre : IsOpen (U ⁻¹' t) := ht.preimage U.continuous
  have h := U.iteratedFDerivWithin_comp_right (hgu.mono htu) ht.uniqueDiffOn
    hpre.uniqueDiffOn hxt (i := i) (by exact_mod_cast hi)
  rwa [iteratedFDerivWithin_of_isOpen i hpre (show x ∈ U ⁻¹' t from hxt),
    iteratedFDerivWithin_of_isOpen i ht hxt] at h

/-- **Taylor polynomial of a linear composition.** Let $U \colon E \to F$ be a continuous linear
map, let $x \in E$, and let $g \colon F \to G$ be of class $C^p$ at $Ux$. Then for every
$s \in E$,
$$T_{g \circ U, p}(x, s) = T_{g, p}(Ux, Us).$$

This is one ingredient of (5.2.2) of [cartis2022evaluation]. -/
theorem taylorPolynomial_comp_continuousLinearMap {g : F → G} (U : E →L[ℝ] F) {p : ℕ} {x : E}
    (hg : ContDiffAt ℝ p g (U x)) (s : E) :
    taylorPolynomial (g ∘ U) p x s = taylorPolynomial g p (U x) (U s) := by
  simp only [taylorPolynomial_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hg.iteratedFDeriv_comp_continuousLinearMap U (Nat.lt_succ_iff.1 (mem_range.1 hi)),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- **Taylor polynomial of a scalar function times a fixed vector.** Let $g \colon E \to \mathbb{R}$
be of class $C^p$ at $x$, and let $v \in F$. Then for every $s \in E$,
$$T_{y \mapsto g(y) v, \, p}(x, s) = T_{g, p}(x, s) \, v.$$
-/
theorem taylorPolynomial_smul_const {g : E → ℝ} {p : ℕ} {x : E} (hg : ContDiffAt ℝ p g x) (v : F)
    (s : E) : taylorPolynomial (fun y => g y • v) p x s = taylorPolynomial g p x s • v := by
  have hcomp : (fun y => g y • v) =
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v) ∘ g := by
    funext y
    simp
  rw [hcomp, taylorPolynomial_apply, taylorPolynomial_apply, sum_smul]
  refine sum_congr rfl fun i hi => ?_
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ hg
    (by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hi))]
  simp [smul_smul]

/-- **Taylor polynomial of a finite sum.** Let $t$ be a finite index set, and let
$f_i \colon E \to F$ be of class $C^p$ at $x$ for every $i \in t$. Then for every $s \in E$,
$$T_{\sum_{i \in t} f_i, \, p}(x, s) = \sum_{i \in t} T_{f_i, p}(x, s).$$

This is one ingredient of (5.2.2) of [cartis2022evaluation]. -/
theorem taylorPolynomial_finset_sum {ι : Type*} {f : ι → E → F} {t : Finset ι} {p : ℕ} {x : E}
    (hf : ∀ i ∈ t, ContDiffAt ℝ p (f i) x) (s : E) :
    taylorPolynomial (fun y => ∑ i ∈ t, f i y) p x s = ∑ i ∈ t, taylorPolynomial (f i) p x s := by
  simp only [taylorPolynomial_apply]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk' : (k : WithTop ℕ∞) ≤ p := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [iteratedFDeriv_fun_sum_apply fun i hi => (hf i hi).of_le hk', ← smul_sum,
    _root_.sum_apply]

/-- **Taylor models of partially separable functions.** Let $t$ be a finite index set. For
$i \in t$, let $G_i$ be a real normed space, let $U_i \colon E \to G_i$ be a continuous linear
map, and let $f_i \colon G_i \to F$ be of class $C^p$ at $U_i x$. Let
$f = \sum_{i \in t} f_i \circ U_i$. Then for every $s \in E$,
$$T_{f,p}(x, s) = \sum_{i \in t} T_{f_i,p}(U_i x, U_i s).$$

This is (5.2.2) of [cartis2022evaluation]. -/
theorem taylorPolynomial_finset_sum_comp_continuousLinearMap {ι : Type*} {G : ι → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)] {f : ∀ i, G i → F}
    (U : ∀ i, E →L[ℝ] G i) {t : Finset ι} {p : ℕ} {x : E}
    (hf : ∀ i ∈ t, ContDiffAt ℝ p (f i) (U i x)) (s : E) :
    taylorPolynomial (fun y => ∑ i ∈ t, f i (U i y)) p x s =
      ∑ i ∈ t, taylorPolynomial (f i) p (U i x) (U i s) := by
  rw [taylorPolynomial_finset_sum (f := fun i y => f i (U i y))
    fun i hi => (hf i hi).comp x (U i).contDiff.contDiffAt]
  exact sum_congr rfl fun i hi => taylorPolynomial_comp_continuousLinearMap (U i) (hf i hi) s
