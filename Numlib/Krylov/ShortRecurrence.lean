import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Polynomial.EraseLead
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.FullGrade

/-!
# Bandwidth of the Arnoldi recurrence

If an adjoint is a polynomial of degree at most $s$ in the original operator, the Arnoldi
coefficients above the $s$-th superdiagonal vanish. For an initial vector of grade at least
$s+2$, a polynomial of exact degree $s$ gives a nonzero entry on that superdiagonal.

## Main definitions

* `Arnoldi.HasUpperBandwidth`: bandwidth at most $s$ before breakdown.

## Main results

* `Arnoldi.hasUpperBandwidth_of_adjoint_eq_aeval`: the upper bandwidth bound.
* `Arnoldi.coeff_ne_zero_of_adjoint_eq_aeval`: sharpness at the first row.
* `Arnoldi.continuousAt_orthogonalVec`: the unnormalized vectors depend continuously on the
  start before breakdown.
* `Arnoldi.coeff_zero_of_uniform_hasUpperBandwidth`: uniform rectangular bandwidth
  forces a coefficient in the last column to vanish by continuity from full-grade starts.
-/

open Polynomial Krylov
open scoped InnerProductSpace

namespace Arnoldi

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (A : Module.End 𝕜 E) (v : E)

/-- All entries above the $s$-th superdiagonal of the rectangular Arnoldi matrix
before breakdown vanish. -/
def HasUpperBandwidth (s : ℕ) : Prop :=
  (hessenberg A v (grade A v - 1)).HasUpperBandwidthRect s

variable [FiniteDimensional 𝕜 E]

/-- If $A^*=p(A)$ for a polynomial of degree at most $s$, then every Arnoldi coefficient
$h_{ij}$ with $j>i+s$ vanishes. -/
theorem hasUpperBandwidth_of_adjoint_eq_aeval {p : 𝕜[X]} {s : ℕ}
    (hp : p.degree ≤ s) (hA : A.adjoint = aeval A p) :
    HasUpperBandwidth A v s := by
  intro i j hij
  apply coeff_eq_zero_of_adjoint_mem A v
    (B := A.adjoint) (fun x y => (A.adjoint_inner_left x y).symm)
    (fun x => ?_) (show (i : ℕ) + (s + 1) ≤ (j : ℕ) by omega)
  rw [hA]
  exact aeval_apply_mem_subspace A x (hp.trans_lt (by exact_mod_cast Nat.lt_succ_self s))

/-- If $A^*=p(A)$ for a polynomial of degree $s$ and $v$ has grade at least $s+2$,
then the first row has a nonzero entry in column $s$ with zero-based numbering. -/
theorem coeff_ne_zero_of_adjoint_eq_aeval {p : 𝕜[X]} {s : ℕ}
    (hp : p.degree = s) (hA : A.adjoint = aeval A p) (hs : s + 2 ≤ grade A v) :
    coeff A v 0 s ≠ 0 := by
  have hv : v ≠ 0 := by
    rintro rfl
    rw [grade_zero] at hs
    omega
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  have hdeg : p.natDegree = s := WithBot.coe_inj.mp ((degree_eq_natDegree hp0).symm.trans hp)
  have hlow : aeval A p.eraseLead v ∈ subspace A v s :=
    aeval_apply_mem_subspace A v ((degree_eraseLead_lt hp0).trans_le (le_of_eq hp))
  have hinner : inner 𝕜 (aeval A p.eraseLead v) (vec A v s) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hlow (vec_mem_orthogonal A v s)
  have htop : inner 𝕜 ((A ^ s) v) (vec A v s) ≠ 0 := by
    intro h
    have hz : inner 𝕜 (vec A v s) ((A ^ s) v) = 0 := by
      rw [← inner_conj_symm, h, map_zero]
    exact (not_le_of_gt (show s < grade A v by omega))
      ((vec_eq_zero_iff A v s).1 (vec_eq_zero_of_inner_pow_apply_eq_zero A v hz))
  have hr : (‖v‖⁻¹ : 𝕜) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hv)
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hsplit : aeval A p v = aeval A p.eraseLead v + p.leadingCoeff • (A ^ s) v := by
    conv_lhs => rw [← eraseLead_add_monomial_natDegree_leadingCoeff p]
    rw [map_add, LinearMap.add_apply, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, hdeg]
  rw [coeff, ← A.adjoint_inner_left, vec_zero A v hv, hA, map_smul, inner_smul_left, hsplit,
    inner_add_left, hinner, zero_add, inner_smul_left]
  exact mul_ne_zero (star_ne_zero.2 hr) (mul_ne_zero (star_ne_zero.2 hlead) htop)

/-- The unnormalized Arnoldi vector of index $j$ is the Gram–Schmidt residual of $A^jv$
after projection onto the preceding Krylov subspace. -/
noncomputable def orthogonalVec (j : ℕ) : E :=
  InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) v) j

private theorem orthogonalVec_ne_zero_of_lt_grade {j : ℕ} (hj : j < grade A v) :
    orthogonalVec A v j ≠ 0 := by
  intro h
  have hz : vec A v j = 0 := by
    change (‖orthogonalVec A v j‖ : 𝕜)⁻¹ • orthogonalVec A v j = 0
    rw [h, smul_zero]
  exact hj.not_ge ((vec_eq_zero_iff A v j).1 hz)

/-- Before breakdown, each unnormalized Arnoldi vector is continuous as a function of the
starting vector. -/
theorem continuousAt_orthogonalVec {j : ℕ} (hj : j < grade A v) :
    ContinuousAt (fun w : E => orthogonalVec A w j) v := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have heq (w : E) :
        orthogonalVec A w j = (A ^ j) w - ∑ i ∈ Finset.Iio j,
          (inner 𝕜 (orthogonalVec A w i) ((A ^ j) w) / (‖orthogonalVec A w i‖ : 𝕜) ^ 2) •
            orthogonalVec A w i :=
      eq_sub_of_add_eq (InnerProductSpace.gramSchmidt_def'' 𝕜
        (fun i : ℕ => (A ^ i) w) j).symm
    simp only [heq]
    have hpow : ContinuousAt (fun w : E => (A ^ j) w) v :=
      (A ^ j).continuous_of_finiteDimensional.continuousAt
    apply hpow.sub
    refine tendsto_finsetSum _ fun i hi => ?_
    have hij := Finset.mem_Iio.mp hi
    have hc := ih i hij (hij.trans hj)
    have hd : ContinuousAt (fun w : E => (‖orthogonalVec A w i‖ : 𝕜) ^ 2) v :=
      (RCLike.continuous_ofReal.continuousAt.comp hc.norm).pow 2
    exact ((hc.inner hpow).div hd (pow_ne_zero _ (RCLike.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (orthogonalVec_ne_zero_of_lt_grade A v (hij.trans hj)))))).smul hc

/-- Before breakdown, the normalized Arnoldi vector of index $j$ is continuous as a function
of the starting vector. -/
theorem continuousAt_vec {j : ℕ} (hj : j < grade A v) :
    ContinuousAt (fun w : E => vec A w j) v := by
  change ContinuousAt (fun w : E => (‖orthogonalVec A w j‖ : 𝕜)⁻¹ • orthogonalVec A w j) v
  have hc := continuousAt_orthogonalVec A v hj
  exact ((RCLike.continuous_ofReal.continuousAt.comp hc.norm).inv₀
    (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (orthogonalVec_ne_zero_of_lt_grade A v hj)))).smul hc

/-- Uniform pre-breakdown upper bandwidth also forces entries above the band in a last
column, by continuing the coefficient from full-grade starting vectors. -/
theorem coeff_zero_of_uniform_hasUpperBandwidth {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {A : Module.End ℂ V} {s : ℕ}
    (hmin : s + 2 < (minpoly ℂ A).natDegree)
    (h : ∀ v : V, HasUpperBandwidth A v s) (v : V) (hv : s + 2 ≤ grade A v) :
    coeff A v 0 (s + 1) = 0 := by
  let S := {w : V | grade A w = (minpoly ℂ A).natDegree}
  let f (w : V) := coeff A w 0 (s + 1)
  have hcont : ContinuousAt f v := by
    change ContinuousAt (fun w : V => inner ℂ (vec A w 0) (A (vec A w (s + 1)))) v
    exact (continuousAt_vec A v (by omega)).inner
      (A.continuous_of_finiteDimensional.continuousAt.comp (continuousAt_vec A v (by omega)))
  have hdense := (Krylov.dense_fullGrade A) v
  have heq : f '' S ⊆ {0} := by
    rintro _ ⟨w, hw, rfl⟩
    change grade A w = (minpoly ℂ A).natDegree at hw
    let i : Fin (grade A w - 1 + 1) := ⟨0, Nat.zero_lt_succ _⟩
    let j : Fin (grade A w - 1) := ⟨s + 1, by omega⟩
    change f w = 0
    have hband : (Arnoldi.hessenberg A w (grade A w - 1)).HasUpperBandwidthRect s := h w
    exact hband i j (by simp [i, j])
  have hf := mem_closure_image hcont hdense
  exact (closure_minimal heq isClosed_singleton hf : f v ∈ ({0} : Set ℂ))

end Arnoldi
