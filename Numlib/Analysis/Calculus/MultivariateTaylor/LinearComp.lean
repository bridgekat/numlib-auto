import Numlib.Analysis.Calculus.MultivariateTaylor.Basic

/-!
# Taylor polynomials of linear compositions and of finite sums

For the Taylor polynomial `T_{f,p}(x, s) = taylorPolynomial f p x s` of
`Numlib.Analysis.Calculus.MultivariateTaylor.Basic`:

* `taylorPolynomial_comp_continuousLinearMap`: `T_{g ∘ U, p}(x, s) = T_{g, p}(U x, U s)` for a
  continuous linear map `U`;
* `taylorPolynomial_smul_const`: `T_{g v, p}(x, s) = T_{g, p}(x, s) v` for scalar `g`;
* `taylorPolynomial_finset_sum`: `T_{∑ᵢ fᵢ, p}(x, s) = ∑ᵢ T_{fᵢ, p}(x, s)`;
* `taylorPolynomial_finset_sum_comp_continuousLinearMap`: the combination below.

Together they give the Taylor models of partially separable functions `f = ∑ᵢ fᵢ ∘ Uᵢ`,
`T_{f,p}(x, s) = ∑ᵢ T_{fᵢ,p}(Uᵢ x, Uᵢ s)` ([cartis2022evaluation], (5.2.2)). Only smoothness at the
base point is assumed.
-/

open Finset Filter
open scoped Nat Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The iterated derivative of `g ∘ U` at `x`, for `U` continuous linear and `g` of class `C^n`
at `U x`: `∇^i (g ∘ U)(x) = ∇^i g(U x) ∘ (U, …, U)` for `i ≤ n`. (A pointwise version of
`ContinuousLinearMap.iteratedFDeriv_comp_right`.) -/
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

/-- **Taylor polynomial of a linear composition** ([cartis2022evaluation], (5.2.2)): if `g` is
`C^p` at `U x`, then `T_{g ∘ U, p}(x, s) = T_{g, p}(U x, U s)`. -/
theorem taylorPolynomial_comp_continuousLinearMap {g : F → G} (U : E →L[ℝ] F) {p : ℕ} {x : E}
    (hg : ContDiffAt ℝ p g (U x)) (s : E) :
    taylorPolynomial (g ∘ U) p x s = taylorPolynomial g p (U x) (U s) := by
  simp only [taylorPolynomial_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hg.iteratedFDeriv_comp_continuousLinearMap U (Nat.lt_succ_iff.1 (mem_range.1 hi)),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- **Taylor polynomial of a scalar function times a fixed vector**: if `g : E → ℝ` is `C^p` at
`x`, then `T_{g v, p}(x, s) = T_{g, p}(x, s) v`. -/
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

/-- **Taylor polynomial of a finite sum** ([cartis2022evaluation], (5.2.2)): if every `f i` is
`C^p` at `x`, then `T_{∑ᵢ fᵢ, p}(x, s) = ∑ᵢ T_{fᵢ, p}(x, s)`. -/
theorem taylorPolynomial_finset_sum {ι : Type*} {f : ι → E → F} {t : Finset ι} {p : ℕ} {x : E}
    (hf : ∀ i ∈ t, ContDiffAt ℝ p (f i) x) (s : E) :
    taylorPolynomial (fun y => ∑ i ∈ t, f i y) p x s = ∑ i ∈ t, taylorPolynomial (f i) p x s := by
  simp only [taylorPolynomial_apply]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk' : (k : WithTop ℕ∞) ≤ p := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [iteratedFDeriv_fun_sum_apply fun i hi => (hf i hi).of_le hk', ← smul_sum,
    _root_.sum_apply]

/-- **Taylor models of partially separable functions** ([cartis2022evaluation], (5.2.2)): for
`f = ∑ᵢ fᵢ ∘ Uᵢ` with `Uᵢ` continuous linear and each `fᵢ` of class `C^p` at `Uᵢ x`,
`T_{f,p}(x, s) = ∑ᵢ T_{fᵢ,p}(Uᵢ x, Uᵢ s)`. -/
theorem taylorPolynomial_finset_sum_comp_continuousLinearMap {ι : Type*} {G : ι → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)] {f : ∀ i, G i → F}
    (U : ∀ i, E →L[ℝ] G i) {t : Finset ι} {p : ℕ} {x : E}
    (hf : ∀ i ∈ t, ContDiffAt ℝ p (f i) (U i x)) (s : E) :
    taylorPolynomial (fun y => ∑ i ∈ t, f i (U i y)) p x s =
      ∑ i ∈ t, taylorPolynomial (f i) p (U i x) (U i s) := by
  rw [taylorPolynomial_finset_sum (f := fun i y => f i (U i y))
    fun i hi => (hf i hi).comp x (U i).contDiff.contDiffAt]
  exact sum_congr rfl fun i hi => taylorPolynomial_comp_continuousLinearMap (U i) (hf i hi) s
