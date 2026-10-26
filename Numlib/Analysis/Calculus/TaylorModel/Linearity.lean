import Numlib.Analysis.Calculus.TaylorModel.Holder
import Numlib.Analysis.Calculus.TaylorModel.Perturbation

/-!
# Finite Taylor decrement linearity

Finite Taylor decrements preserve addition and scalar multiplication. Constants vanish,
and actual affine-line derivatives agree with the diagonal tensors under finite pointwise
smoothness.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Finite actual Taylor decrements are additive for functions smooth to the model degree. -/
theorem decrement_add_of_contDiffAt {f g : E → ℝ} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hg : ContDiffAt ℝ p g x) (d : E) :
    decrement (f + g) p x d = decrement f p x d + decrement g p x d := by
  change jetDecrement (ftaylorSeries ℝ (f + g) x) p d = _
  change _ = jetDecrement (ftaylorSeries ℝ f x) p d +
    jetDecrement (ftaylorSeries ℝ g x) p d
  simp only [jetDecrement_eq_sum, ftaylorSeries]
  have he (i : ℕ) (hi : i ∈ Finset.range p) :
      iteratedFDeriv ℝ (i + 1) (f + g) x =
        iteratedFDeriv ℝ (i + 1) f x + iteratedFDeriv ℝ (i + 1) g x :=
    iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast Finset.mem_range.mp hi))
      (hg.of_le (by exact_mod_cast Finset.mem_range.mp hi))
  rw [show (∑ i ∈ Finset.range p, (((i + 1).factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ (i + 1) (f + g) x (fun _ => d)) =
      (∑ i ∈ Finset.range p, (((i + 1).factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ (i + 1) f x (fun _ => d)) +
      (∑ i ∈ Finset.range p, (((i + 1).factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ (i + 1) g x (fun _ => d)) from by
    rw [← Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro i hi
    rw [he i hi];simp only [add_apply, smul_add]]
  ring

/-- Actual finite Taylor decrements commute with scalar multiplication. -/
theorem decrement_smul_of_contDiffAt {f : E → ℝ} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (a : ℝ) (d : E) :
    decrement (a • f) p x d = a * decrement f p x d := by
  change jetDecrement (ftaylorSeries ℝ (a • f) x) p d = _
  change _ = a * jetDecrement (ftaylorSeries ℝ f x) p d
  simp only [jetDecrement_eq_sum, ftaylorSeries]
  have he (i : ℕ) (hi : i ∈ Finset.range p) :
      iteratedFDeriv ℝ (i + 1) (a • f) x = a • iteratedFDeriv ℝ (i + 1) f x :=
    by
      change iteratedFDeriv ℝ (i + 1) (fun z => a • f z) x = _
      exact iteratedFDeriv_const_smul_apply' (hf.of_le
        (by exact_mod_cast Finset.mem_range.mp hi))
  rw [show (∑ i ∈ Finset.range p, (((i + 1).factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ (i + 1) (a • f) x (fun _ => d)) =
      a * ∑ i ∈ Finset.range p, (((i + 1).factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ (i + 1) f x (fun _ => d) from by
    rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi
    rw [he i hi];simp only [smul_apply, smul_eq_mul];ring]
  ring

/-- Every constant has zero finite Taylor decrement, including at degree zero. -/
theorem decrement_const (b : ℝ) (p : ℕ) (x d : E) :
    decrement (fun _ => b) p x d = 0 := by
  change jetDecrement (ftaylorSeries ℝ (fun _ : E => b) x) p d = 0
  simp only [jetDecrement_eq_sum, ftaylorSeries]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro i hi
  rw [iteratedFDeriv_const_of_ne (by omega : i + 1 ≠ 0)]
  simp
end TaylorModel

open Filter Set Topology
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Actual affine-line derivatives agree with diagonal tensors under pointwise finite smoothness. -/
theorem iteratedDeriv_affineLine_at {f : E → G} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hj : j ≤ p) (d : E) :
    iteratedDeriv j (fun t : ℝ => f (x + t • d)) 0 =
      iteratedFDeriv ℝ j f x (fun _ => d) := by
  obtain ⟨U, hU, ho, hx⟩ := mem_nhds_iff.mp (hf.eventually (by simp))
  have hfU : ContDiffOn ℝ p f U := by
    intro y hy
    have hh : ContDiffAt ℝ p f y := hU hy
    exact hh.contDiffWithinAt
  have hh := iteratedDeriv_affineLine_of_contDiffOn ho hfU hj x d 0
    (by simpa only [zero_smul, add_zero] using hx)
  simpa only [zero_smul, add_zero] using hh
end TaylorModel
