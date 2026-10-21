import Numlib.Analysis.Calculus.SquaredNormJets
import Mathlib.Tactic

/-!
# Bounded Lipschitz jets on a set

Quantitative bounds concern actual ambient derivative tensors on the specified set only.
Smoothness is supplied on an open neighborhood; the set itself can have empty interior.
Including order zero gives a product algebra, with natural powers of every degree.
-/

noncomputable section
open Set
open scoped ContDiff
namespace BoundedLipschitzJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All actual jets through order `p`, including values, are bounded and Lipschitz on `C`.
The open smoothness neighborhood carries no quantitative jet bounds. -/
structure On (f : E → ℝ) (p : ℕ) (C : Set E) (M L : ℝ) : Prop where
  neighborhood : ∃ U : Set E, IsOpen U ∧ C ⊆ U ∧ ContDiffOn ℝ p f U
  bound_nonneg : 0 ≤ M
  lipschitz_nonneg : 0 ≤ L
  bound : ∀ j ≤ p, ∀ x ∈ C, ‖iteratedFDeriv ℝ j f x‖ ≤ M
  lipschitz : ∀ j ≤ p, ∀ x ∈ C, ∀ y ∈ C,
    ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L * ‖y - x‖

/-- Actual positive-order jets are bounded and Lipschitz on `C`; values need not be bounded.
The function itself is smooth on an open neighborhood of `C`. -/
structure PositiveOn (f : E → ℝ) (p : ℕ) (C : Set E) (M L : ℝ) : Prop where
  neighborhood : ∃ U : Set E, IsOpen U ∧ C ⊆ U ∧ ContDiffOn ℝ p f U
  bound_nonneg : 0 ≤ M
  lipschitz_nonneg : 0 ≤ L
  bound : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ‖iteratedFDeriv ℝ j f x‖ ≤ M
  lipschitz : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ∀ y ∈ C,
    ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L * ‖y - x‖

variable {f g : E → ℝ} {p : ℕ} {C : Set E} {M L N K : ℝ}

/-- Order-specific bounds on a common open smooth extension give common positive-jet
constants by a finite sum. Quantitative assumptions are imposed on `C` only. -/
theorem positiveOn_of_order_bounds {U : Set E} (hU : IsOpen U) (hCU : C ⊆ U)
    (hf : ContDiffOn ℝ p f U) (B A : ℕ → ℝ)
    (hB : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    (hA : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ A j * ‖y - x‖) :
    PositiveOn f p C (∑ j ∈ Finset.Icc 1 p, max 0 (B j))
      (∑ j ∈ Finset.Icc 1 p, max 0 (A j)) := by
  have hsum (v : ℕ → ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 p) :
      v j ≤ ∑ i ∈ Finset.Icc 1 p, max 0 (v i) :=
    (le_max_right _ _).trans
      (Finset.single_le_sum (fun i _ => le_max_left 0 (v i)) hj)
  refine ⟨⟨U, hU, hCU, hf⟩, Finset.sum_nonneg (fun _ _ => le_max_left _ _),
    Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_, ?_⟩
  · intro j hj hjp x hx
    exact (hB j hj hjp x hx).trans (hsum B j (Finset.mem_Icc.mpr ⟨hj, hjp⟩))
  · intro j hj hjp x hx y hy
    exact (hA j hj hjp x hx y hy).trans (mul_le_mul_of_nonneg_right
      (hsum A j (Finset.mem_Icc.mpr ⟨hj, hjp⟩)) (norm_nonneg _))

/-- A full jet envelope retains the positive-order bounds with the same constants. -/
theorem On.positive (hf : On f p C M L) : PositiveOn f p C M L :=
  ⟨hf.neighborhood, hf.bound_nonneg, hf.lipschitz_nonneg,
    fun j _ hjp x hx => hf.bound j hjp x hx,
    fun j _ hjp x hx y hy => hf.lipschitz j hjp x hx y hy⟩

/-- The open smooth extension gives ambient differentiability at every point of `C`. -/
theorem On.contDiffAt (hf : On f p C M L) {x : E} (hx : x ∈ C) :
    ContDiffAt ℝ p f x := by
  obtain ⟨U, hU, hCU, hfU⟩ := hf.neighborhood
  exact (hfU x (hCU hx)).contDiffAt (hU.mem_nhds (hCU hx))

/-- Positive-jet assumptions also give the actual ambient smooth jet on the boundary of `C`. -/
theorem PositiveOn.contDiffAt (hf : PositiveOn f p C M L) {x : E} (hx : x ∈ C) :
    ContDiffAt ℝ p f x := by
  obtain ⟨U, hU, hCU, hfU⟩ := hf.neighborhood
  exact (hfU x (hCU hx)).contDiffAt (hU.mem_nhds (hCU hx))

/-- Order zero in a full jet envelope bounds the actual function value. -/
theorem On.norm_value_le (hf : On f p C M L) {x : E} (hx : x ∈ C) : ‖f x‖ ≤ M := by
  simpa only [norm_iteratedFDeriv_zero] using hf.bound 0 (Nat.zero_le p) x hx

/-- Order zero in a full jet envelope is Lipschitz continuity of the actual values. -/
theorem On.norm_sub_le (hf : On f p C M L) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ‖f y - f x‖ ≤ L * ‖y - x‖ := by
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] using hf.lipschitz 0 (Nat.zero_le p) x hx y hy

/-- Bounded first derivatives on a convex set give Lipschitz continuity of values on that set. -/
theorem PositiveOn.norm_sub_le (hf : PositiveOn f p C M L) (hp : 1 ≤ p)
    (hC : Convex ℝ C) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ‖f y - f x‖ ≤ M * ‖y - x‖ := by
  apply hC.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf.contDiffAt hz).differentiableAt (by exact_mod_cast (by omega : p ≠ 0))) _ hx hy
  intro z hz
  simpa only [norm_iteratedFDeriv_one] using hf.bound 1 le_rfl hp z hz

/-- A value bound completes positive jets on a convex set to a full jet envelope.
No derivative bounds outside `C` are introduced. -/
theorem PositiveOn.with_value_bound (hf : PositiveOn f p C M L) (hp : 1 ≤ p)
    (hC : Convex ℝ C) {R : ℝ} (hR : ∀ x ∈ C, ‖f x‖ ≤ R) :
    On f p C (max R M) (max M L) where
  neighborhood := hf.neighborhood
  bound_nonneg := hf.bound_nonneg.trans (le_max_right _ _)
  lipschitz_nonneg := hf.bound_nonneg.trans (le_max_left _ _)
  bound j hj x hx := by
    by_cases hj0 : j = 0
    · subst j
      simpa only [norm_iteratedFDeriv_zero] using (hR x hx).trans (le_max_left R M)
    · exact (hf.bound j (by omega) hj x hx).trans (le_max_right _ _)
  lipschitz j hj x hx y hy := by
    by_cases hj0 : j = 0
    · subst j
      have h := hf.norm_sub_le hp hC hx hy
      have he : ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 f x‖ = ‖f y - f x‖ := by
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map]
      rw [he]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact (hf.lipschitz j (by omega) hj x hx y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- Subtracting a constant target preserves all positive derivative bounds. -/
theorem PositiveOn.sub_const (hf : PositiveOn f p C M L) (a : ℝ) :
    PositiveOn (fun x => f x - a) p C M L := by
  have heq (j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) (x : E) (hx : x ∈ C) :
      iteratedFDeriv ℝ j (fun z => f z - a) x = iteratedFDeriv ℝ j f x := by
    rw [fun_iteratedFDeriv_sub_apply ((hf.contDiffAt hx).of_le (by exact_mod_cast hjp))
      contDiffAt_const, iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    simp
  refine ⟨?_, hf.bound_nonneg, hf.lipschitz_nonneg, ?_, ?_⟩
  · obtain ⟨U, ho, hC, hs⟩ := hf.neighborhood
    exact ⟨U, ho, hC, hs.sub contDiffOn_const⟩
  · intro j hj hjp x hx
    rw [heq j hj hjp x hx]
    exact hf.bound j hj hjp x hx
  · intro j hj hjp x hx y hy
    rw [heq j hj hjp x hx, heq j hj hjp y hy]
    exact hf.lipschitz j hj hjp x hx y hy

/-- Constants have bounded full jets and zero Lipschitz constant. -/
theorem on_const (a : ℝ) : On (fun _ : E => a) p C |a| 0 where
  neighborhood := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  bound_nonneg := abs_nonneg _
  lipschitz_nonneg := le_rfl
  bound j _ x _ := by
    by_cases hj : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
    · simp only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply, norm_zero]
      exact abs_nonneg _
  lipschitz j _ x _ y _ := by
    by_cases hj : j = 0
    · subst j
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, sub_self, norm_zero,
        zero_mul, le_refl]
    · simp only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_self, norm_zero,
        zero_mul, le_refl]

/-- Adding full jet envelopes adds both quantitative constants. -/
theorem On.add (hf : On f p C M L) (hg : On g p C N K) :
    On (fun x => f x + g x) p C (M + N) (L + K) where
  neighborhood := by
    obtain ⟨U, ho, hCU, hfu⟩ := hf.neighborhood
    obtain ⟨V, hv, hCV, hgv⟩ := hg.neighborhood
    exact ⟨U ∩ V, ho.inter hv, fun x hx => ⟨hCU hx, hCV hx⟩,
      (hfu.mono inter_subset_left).add (hgv.mono inter_subset_right)⟩
  bound_nonneg := add_nonneg hf.bound_nonneg hg.bound_nonneg
  lipschitz_nonneg := add_nonneg hf.lipschitz_nonneg hg.lipschitz_nonneg
  bound j hj x hx := by
    rw [fun_iteratedFDeriv_add_apply ((hf.contDiffAt hx).of_le (by exact_mod_cast hj))
      ((hg.contDiffAt hx).of_le (by exact_mod_cast hj))]
    exact (norm_add_le _ _).trans (add_le_add (hf.bound j hj x hx) (hg.bound j hj x hx))
  lipschitz j hj x hx y hy := by
    rw [fun_iteratedFDeriv_add_apply ((hf.contDiffAt hx).of_le (by exact_mod_cast hj))
      ((hg.contDiffAt hx).of_le (by exact_mod_cast hj)),
      fun_iteratedFDeriv_add_apply ((hf.contDiffAt hy).of_le (by exact_mod_cast hj))
      ((hg.contDiffAt hy).of_le (by exact_mod_cast hj))]
    have he : iteratedFDeriv ℝ j f y + iteratedFDeriv ℝ j g y -
        (iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x) =
        (iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x) +
          (iteratedFDeriv ℝ j g y - iteratedFDeriv ℝ j g x) := by abel
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add (hf.lipschitz j hj x hx y hy)
      (hg.lipschitz j hj x hx y hy)).trans_eq (by ring))

/-- Scalar multiplication scales full-jet constants by its absolute value. -/
theorem On.const_mul (hf : On f p C M L) (a : ℝ) :
    On (fun x => a * f x) p C (|a| * M) (|a| * L) where
  neighborhood := by
    obtain ⟨U, ho, hC, hs⟩ := hf.neighborhood
    exact ⟨U, ho, hC, contDiffOn_const.mul hs⟩
  bound_nonneg := mul_nonneg (abs_nonneg _) hf.bound_nonneg
  lipschitz_nonneg := mul_nonneg (abs_nonneg _) hf.lipschitz_nonneg
  bound j hj x hx := by
    change ‖iteratedFDeriv ℝ j (fun z => a • f z) x‖ ≤ |a| * M
    rw [iteratedFDeriv_const_smul_apply'
      ((hf.contDiffAt hx).of_le (by exact_mod_cast hj)), norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.bound j hj x hx) (abs_nonneg _)
  lipschitz j hj x hx y hy := by
    simp only [← smul_eq_mul, iteratedFDeriv_const_smul_apply'
      ((hf.contDiffAt hx).of_le (by exact_mod_cast hj)),
      iteratedFDeriv_const_smul_apply' ((hf.contDiffAt hy).of_le (by exact_mod_cast hj)),
      ← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf.lipschitz j hj x hx y hy) (abs_nonneg _)).trans_eq
      (by ring)

/-- Point-local scalar Leibniz bound with uniform bounds on every jet, including order zero. -/
theorem norm_iteratedFDeriv_mul_le {f g : E → ℝ} {x : E} {j : ℕ} {M N : ℝ}
    (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x)
    (hfjet : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hgjet : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ≤ N) :
    ‖iteratedFDeriv ℝ j (fun z => f z * g z) x‖ ≤ (2 : ℝ) ^ j * M * N := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hfjet 0 (Nat.zero_le j))
  have h := SquaredNormJets.norm_iteratedFDeriv_bilinear_le
    (ContinuousLinearMap.mul ℝ ℝ) hf hg
  apply h.trans
  apply (mul_le_of_le_one_left (by positivity) (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M * N := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      gcongr
      · exact hfjet i hij
      · exact hgjet (j - i) (Nat.sub_le _ _)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j

/-- Point-local stability of actual product jets. The input differences concern only actual
jets of the factors and give the product difference estimate by the bilinear Leibniz bound. -/
theorem norm_iteratedFDeriv_mul_sub_le {f₀ f₁ g₀ g₁ : E → ℝ} {x : E} {j : ℕ}
    {M N L K t : ℝ} (hf₀ : ContDiffAt ℝ j f₀ x) (hf₁ : ContDiffAt ℝ j f₁ x)
    (hg₀ : ContDiffAt ℝ j g₀ x) (hg₁ : ContDiffAt ℝ j g₁ x)
    (hfjet : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f₀ x‖ ≤ M)
    (hgjet : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g₁ x‖ ≤ N)
    (hfdiff : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f₁ x - iteratedFDeriv ℝ i f₀ x‖ ≤ L * t)
    (hgdiff : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g₁ x - iteratedFDeriv ℝ i g₀ x‖ ≤ K * t) :
    ‖iteratedFDeriv ℝ j (fun z => f₁ z * g₁ z) x -
      iteratedFDeriv ℝ j (fun z => f₀ z * g₀ z) x‖ ≤
        (2 : ℝ) ^ j * (L * N + M * K) * t := by
  have hfd : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z => f₁ z - f₀ z) x‖ ≤ L * t := by
    intro i hi
    rw [fun_iteratedFDeriv_sub_apply (hf₁.of_le (by exact_mod_cast hi))
      (hf₀.of_le (by exact_mod_cast hi))]
    exact hfdiff i hi
  have hgd : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z => g₁ z - g₀ z) x‖ ≤ K * t := by
    intro i hi
    rw [fun_iteratedFDeriv_sub_apply (hg₁.of_le (by exact_mod_cast hi))
      (hg₀.of_le (by exact_mod_cast hi))]
    exact hgdiff i hi
  have h₁ := norm_iteratedFDeriv_mul_le (hf₁.sub hf₀) hg₁ hfd hgjet
  have h₂ := norm_iteratedFDeriv_mul_le hf₀ (hg₁.sub hg₀) hfjet hgd
  have heq : (fun z => f₁ z * g₁ z - f₀ z * g₀ z) =
      (fun z => (f₁ z - f₀ z) * g₁ z + f₀ z * (g₁ z - g₀ z)) := by funext z; ring
  rw [← fun_iteratedFDeriv_sub_apply (hf₁.mul hg₁) (hf₀.mul hg₀), heq,
    fun_iteratedFDeriv_add_apply ((hf₁.sub hf₀).mul hg₁) (hf₀.mul (hg₁.sub hg₀))]
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- Product closure on the original set; bounds on an open neighborhood are unnecessary. -/
theorem On.mul (hf : On f p C M L) (hg : On g p C N K) :
    On (fun x => f x * g x) p C ((2 : ℝ) ^ p * M * N)
      ((2 : ℝ) ^ p * (L * N + M * K)) where
  neighborhood := by
    obtain ⟨U, ho, hCU, hfu⟩ := hf.neighborhood
    obtain ⟨V, hv, hCV, hgv⟩ := hg.neighborhood
    exact ⟨U ∩ V, ho.inter hv, fun x hx => ⟨hCU hx, hCV hx⟩,
      (hfu.mono inter_subset_left).mul (hgv.mono inter_subset_right)⟩
  bound_nonneg := mul_nonneg (mul_nonneg (by positivity) hf.bound_nonneg) hg.bound_nonneg
  lipschitz_nonneg := mul_nonneg (by positivity)
    (add_nonneg (mul_nonneg hf.lipschitz_nonneg hg.bound_nonneg)
      (mul_nonneg hf.bound_nonneg hg.lipschitz_nonneg))
  bound j hj x hx := by
    apply (norm_iteratedFDeriv_mul_le ((hf.contDiffAt hx).of_le (by exact_mod_cast hj))
      ((hg.contDiffAt hx).of_le (by exact_mod_cast hj))
      (fun i hi => hf.bound i (hi.trans hj) x hx)
      (fun i hi => hg.bound i (hi.trans hj) x hx)).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
        hf.bound_nonneg) hg.bound_nonneg
  lipschitz j hj x hx y hy := by
    let F : E → ℝ := fun z => f (z + (y - x))
    let G : E → ℝ := fun z => g (z + (y - x))
    have hxy : x + (y - x) = y := by abel
    have hF : ContDiffAt ℝ j F x := by
      have h : ContDiffAt ℝ j f y := (hf.contDiffAt hy).of_le (by exact_mod_cast hj)
      rw [← hxy] at h
      exact h.comp x (contDiffAt_id.add contDiffAt_const)
    have hG : ContDiffAt ℝ j G x := by
      have h : ContDiffAt ℝ j g y := (hg.contDiffAt hy).of_le (by exact_mod_cast hj)
      rw [← hxy] at h
      exact h.comp x (contDiffAt_id.add contDiffAt_const)
    have hFi (i : ℕ) : iteratedFDeriv ℝ i F x = iteratedFDeriv ℝ i f y := by
      simpa only [F, hxy] using iteratedFDeriv_comp_add_right i (y - x) x (f := f)
    have hGi (i : ℕ) : iteratedFDeriv ℝ i G x = iteratedFDeriv ℝ i g y := by
      simpa only [G, hxy] using iteratedFDeriv_comp_add_right i (y - x) x (f := g)
    have hh := norm_iteratedFDeriv_mul_sub_le
      ((hf.contDiffAt hx).of_le (by exact_mod_cast hj)) hF
      ((hg.contDiffAt hx).of_le (by exact_mod_cast hj)) hG
      (fun i hi => hf.bound i (hi.trans hj) x hx)
      (fun i hi => by rw [hGi]; exact hg.bound i (hi.trans hj) y hy)
      (fun i hi => by rw [hFi]; exact hf.lipschitz i (hi.trans hj) x hx y hy)
      (fun i hi => by rw [hGi]; exact hg.lipschitz i (hi.trans hj) x hx y hy)
    have heq : (fun z => F z * G z) = (fun z => (fun w => f w * g w) (z + (y - x))) := rfl
    rw [heq, iteratedFDeriv_comp_add_right (𝕜 := ℝ) j (y - x) x
      (f := fun w => f w * g w), hxy] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
      (add_nonneg (mul_nonneg hf.lipschitz_nonneg hg.bound_nonneg)
        (mul_nonneg hf.bound_nonneg hg.lipschitz_nonneg))

/-- Finite sums of scalar full jet envelopes have the sums of their constants. -/
theorem On.sum {ι : Type*} (s : Finset ι) {r : ι → E → ℝ} {M L : ι → ℝ}
    (hr : ∀ i ∈ s, On (r i) p C (M i) (L i)) :
    On (fun x => ∑ i ∈ s, r i x) p C (∑ i ∈ s, M i) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (on_const (p := p) (C := C) 0)
  | @insert a s ha ih =>
    have h := (hr a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hr i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.sum_insert ha] using h

/-- Every natural power has a full jet envelope, with constants derived by product closure. -/
theorem On.pow (hf : On f p C M L) (k : ℕ) : ∃ B A : ℝ, On (fun x => f x ^ k) p C B A := by
  induction k with
  | zero => exact ⟨1, 0, by simpa using (on_const (p := p) (C := C) 1)⟩
  | succ k ih =>
    obtain ⟨B, A, hk⟩ := ih
    exact ⟨_, _, by simpa only [pow_succ] using hk.mul hf⟩

end BoundedLipschitzJets
