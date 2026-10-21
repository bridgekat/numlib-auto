import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual derivatives of half squared norm compositions

The ordered finite partition expansion uses actual Fréchet derivatives and symmetrizes their
arguments. Bilinear norm estimates apply to all orders. Centering a difference of squared
norms at one residual value isolates its sole unbounded factor, so the derivative bounds and
Lipschitz estimates depend affinely on that residual norm.
-/

noncomputable section
open Set Filter Topology
open scoped InnerProductSpace ContDiff
namespace SquaredNormJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Bilinear
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Point-local bilinear Leibniz norm estimate, with actual iterated Fréchet derivatives. -/
theorem norm_iteratedFDeriv_bilinear_le {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun z => B (f z) (g z)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V, hV, hgV⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨W, hWUV, hWo, hxW⟩ := mem_nhds_iff.mp (inter_mem hU hV)
  have hfW := hfU.mono (hWUV.trans inter_subset_left)
  have hgW := hgV.mono (hWUV.trans inter_subset_right)
  have hh := B.norm_iteratedFDerivWithin_le_of_bilinear hfW hgW hWo.uniqueDiffOn hxW
    (le_refl (n : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hWo hxW] using hh

end Bilinear

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The half squared norm, as a real-valued objective. -/
def halfNormSq (v : F) : ℝ := ‖v‖ ^ 2 / 2

/-- Half squared norm is smooth at every finite order. -/
theorem contDiff_halfNormSq (n : ℕ) : ContDiff ℝ n (halfNormSq : F → ℝ) := by
  exact (contDiff_norm_sq ℝ).div_const 2

/-- The all-order derivative expansion is a sum over ordered finite partitions. Grouping
arguments by these partitions provides the symmetrization required by the product rule. -/
theorem iteratedFDeriv_comp_eq_sum {r : E → F} {x : E} {n : ℕ}
    (hr : ContDiffAt ℝ n r x) :
    iteratedFDeriv ℝ n (fun z => halfNormSq (r z)) x =
      ∑ c : OrderedFinpartition n,
        (ftaylorSeries ℝ (halfNormSq : F → ℝ) (r x)).compAlongOrderedFinpartition
          (ftaylorSeries ℝ r x) c := by
  exact iteratedFDeriv_comp (contDiff_halfNormSq n).contDiffAt hr le_rfl

/-- The half squared norm is half the real inner product with itself. -/
theorem halfNormSq_eq_inner (v : F) : halfNormSq v = (1 / 2 : ℝ) * ⟪v, v⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq, halfNormSq]
  ring

/-- The actual derivative of a real inner product satisfies the binomial Leibniz bound. -/
theorem norm_iteratedFDeriv_inner_le {f g : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun z => ⟪f z, g z⟫_ℝ) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  apply (norm_iteratedFDeriv_bilinear_le (innerSL ℝ) hf hg).trans
  exact mul_le_of_le_one_left (by positivity) (norm_innerSL_le ℝ)

/-- A positive-order derivative bound affine in the residual norm bound. The common `M`
may bound every positive residual derivative through this order. -/
theorem norm_iteratedFDeriv_comp_le {r : E → F} {x : E} {n : ℕ} {R M : ℝ}
    (hn : 1 ≤ n) (hr : ContDiffAt ℝ n r x) (hR : ‖r x‖ ≤ R) (hM : 0 ≤ M)
    (hjet : ∀ i ∈ Finset.Icc 1 n, ‖iteratedFDeriv ℝ i r x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun z => halfNormSq (r z)) x‖ ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ n * ((R + M) * M) := by
  have hR₀ : 0 ≤ R := (norm_nonneg _).trans hR
  have hfun : (fun z => halfNormSq (r z)) =
      (fun z => (1 / 2 : ℝ) • ⟪r z, r z⟫_ℝ) := by
    funext z
    exact halfNormSq_eq_inner _
  rw [hfun, iteratedFDeriv_const_smul_apply' (hr.inner ℝ hr), norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_iteratedFDeriv_inner_le hr hr).trans
  have heach : ∀ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ i r x‖ * ‖iteratedFDeriv ℝ (n - i) r x‖ ≤ (R + M) * M := by
    intro i hi
    have hiN : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi₀ : i = 0
    · subst i
      simp only [norm_iteratedFDeriv_zero, Nat.sub_zero]
      have hp := mul_le_mul hR (hjet n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))
        (norm_nonneg _) hR₀
      nlinarith only [hp, sq_nonneg M]
    by_cases hin : i = n
    · subst i
      rw [Nat.sub_self, norm_iteratedFDeriv_zero]
      have hp := mul_le_mul (hjet n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)) hR
        (norm_nonneg _) hM
      nlinarith only [hp, sq_nonneg M]
    · have hp := mul_le_mul (hjet i (Finset.mem_Icc.mpr ⟨by omega, hiN⟩))
        (hjet (n - i) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (norm_nonneg _) hM
      nlinarith only [hp, mul_nonneg hR₀ hM]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((R + M) * M) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (heach i hi) (Nat.cast_nonneg (n.choose i))
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n

/-- A centered squared-norm difference isolates the residual value at the reference point.
This identity is valid globally, so it can be differentiated at any order. -/
theorem halfNormSq_sub_centered (u v a : F) :
    halfNormSq v - halfNormSq u = ⟪a, v - u⟫_ℝ +
      (1 / 2 : ℝ) * ⟪v - u, v + u - (2 : ℝ) • a⟫_ℝ := by
  simp only [halfNormSq_eq_inner, inner_sub_left, inner_add_right,
    inner_sub_right, real_inner_smul_right, real_inner_comm]
  ring

/-- Point-local stability of every positive squared-norm derivative. The hypotheses concern
actual residual jets, their differences, and the residual value difference. No derivative
expansion is assumed. The coefficient is affine in the reference residual bound `R`. -/
theorem norm_iteratedFDeriv_halfNormSq_sub_le {f g : E → F} {x : E} {n : ℕ}
    {R M L t : ℝ} (hn : 1 ≤ n) (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hR : ‖f x‖ ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hzero : ‖g x - f x‖ ≤ M * t)
    (hfjet : ∀ i ∈ Finset.Icc 1 n, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hgjet : ∀ i ∈ Finset.Icc 1 n, ‖iteratedFDeriv ℝ i g x‖ ≤ M)
    (hdiff : ∀ i ∈ Finset.Icc 1 n,
      ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i f x‖ ≤ L * t) :
    ‖iteratedFDeriv ℝ n (fun z => halfNormSq (g z)) x -
      iteratedFDeriv ℝ n (fun z => halfNormSq (f z)) x‖ ≤
        (R * L + (2 : ℝ) ^ n * M * (M + L)) * t := by
  let d : E → F := fun z => g z - f z
  let a : E → F := fun z => g z + f z - (2 : ℝ) • f x
  have hd : ContDiffAt ℝ n d x := hg.sub hf
  have ha : ContDiffAt ℝ n a x := (hg.add hf).sub contDiffAt_const
  have hR₀ : 0 ≤ R := (norm_nonneg _).trans hR
  have hdjet (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
      ‖iteratedFDeriv ℝ i d x‖ ≤ L * t ∧ ‖iteratedFDeriv ℝ i d x‖ ≤ 2 * M := by
    have hfi : ContDiffAt ℝ i f x := hf.of_le (by exact_mod_cast (Finset.mem_Icc.mp hi).2)
    have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast (Finset.mem_Icc.mp hi).2)
    have he : iteratedFDeriv ℝ i d x =
        iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i f x :=
      fun_iteratedFDeriv_sub_apply hgi hfi
    rw [he]
    refine ⟨hdiff i hi, ?_⟩
    exact (norm_sub_le _ _).trans (by linarith [hfjet i hi, hgjet i hi])
  have hajet (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
      ‖iteratedFDeriv ℝ i a x‖ ≤ 2 * M := by
    have hfi : ContDiffAt ℝ i f x := hf.of_le (by exact_mod_cast (Finset.mem_Icc.mp hi).2)
    have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast (Finset.mem_Icc.mp hi).2)
    have he : iteratedFDeriv ℝ i a x =
        iteratedFDeriv ℝ i g x + iteratedFDeriv ℝ i f x := by
      dsimp only [a]
      rw [fun_iteratedFDeriv_sub_apply (hgi.add hfi) contDiffAt_const,
        fun_iteratedFDeriv_add_apply hgi hfi,
        iteratedFDeriv_const_of_ne
          (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hi).1)),
        Pi.zero_apply, sub_zero]
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hfjet i hi, hgjet i hi])
  have ha₀ : ‖a x‖ ≤ M * t := by
    have he : a x = g x - f x := by dsimp [a]; module
    simpa only [he] using hzero
  have hp : ‖iteratedFDeriv ℝ n (fun z => ⟪d z, a z⟫_ℝ) x‖ ≤
      (2 : ℝ) ^ n * (2 * M * (M + L) * t) := by
    apply (norm_iteratedFDeriv_inner_le hd ha).trans
    have heach : ∀ i ∈ Finset.range (n + 1),
        ‖iteratedFDeriv ℝ i d x‖ * ‖iteratedFDeriv ℝ (n - i) a x‖ ≤
          2 * M * (M + L) * t := by
      intro i hi
      have hiN : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi₀ : i = 0
      · subst i
        simp only [norm_iteratedFDeriv_zero, Nat.sub_zero]
        have hh := mul_le_mul hzero (hajet n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))
          (norm_nonneg _) (mul_nonneg hM ht)
        have hML := mul_nonneg hM hL
        dsimp only [d]
        nlinarith only [hh, mul_nonneg hML ht]
      by_cases hin : i = n
      · subst i
        rw [Nat.sub_self, norm_iteratedFDeriv_zero]
        have hh := mul_le_mul (hdjet n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)).2 ha₀
          (norm_nonneg _) (by positivity : 0 ≤ 2 * M)
        nlinarith only [hh, mul_nonneg (mul_nonneg hM hL) ht]
      · have hh := mul_le_mul (hdjet i (Finset.mem_Icc.mpr ⟨by omega, hiN⟩)).1
          (hajet (n - i) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (norm_nonneg _)
          (mul_nonneg hL ht)
        nlinarith only [hh, mul_nonneg (sq_nonneg M) ht]
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (2 * M * (M + L) * t) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (heach i hi) (Nat.cast_nonneg (n.choose i))
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hl : ‖iteratedFDeriv ℝ n (fun z => ⟪f x, d z⟫_ℝ) x‖ ≤ R * L * t := by
    have hh := (innerSL ℝ (f x)).norm_iteratedFDeriv_comp_left hd (le_refl (n : ℕ∞ω))
    have hnD := (hdjet n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)).1
    simp only [innerSL_apply_norm] at hh
    exact hh.trans (by nlinarith [mul_le_mul hR hnD (norm_nonneg _) hR₀])
  have hfun : (fun z => halfNormSq (g z) - halfNormSq (f z)) =
      (fun z => ⟪f x, d z⟫_ℝ + (1 / 2 : ℝ) • ⟪d z, a z⟫_ℝ) := by
    funext z
    exact halfNormSq_sub_centered (f z) (g z) (f x)
  have hlinear : ContDiffAt ℝ n (fun z => ⟪f x, d z⟫_ℝ) x :=
    contDiffAt_const.inner ℝ hd
  have hproduct : ContDiffAt ℝ n (fun z => ⟪d z, a z⟫_ℝ) x := hd.inner ℝ ha
  have hnorm : ‖iteratedFDeriv ℝ n (fun z => halfNormSq (g z) - halfNormSq (f z)) x‖ ≤
      R * L * t + (1 / 2 : ℝ) * ((2 : ℝ) ^ n * (2 * M * (M + L) * t)) := by
    rw [hfun, fun_iteratedFDeriv_add_apply hlinear (hproduct.const_smul (1 / 2 : ℝ)),
      iteratedFDeriv_const_smul_apply' hproduct]
    apply (norm_add_le _ _).trans
    apply add_le_add hl
    simpa only [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
      mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hgf : ContDiffAt ℝ n (fun z => halfNormSq (g z)) x :=
    (contDiff_halfNormSq n).contDiffAt.comp x hg
  have hff : ContDiffAt ℝ n (fun z => halfNormSq (f z)) x :=
    (contDiff_halfNormSq n).contDiffAt.comp x hf
  rw [fun_iteratedFDeriv_sub_apply hgf hff] at hnorm
  convert hnorm using 1
  ring

/-- On an open convex domain, bounded positive residual jets and Lipschitz positive jets
imply a Lipschitz estimate for every positive squared-residual derivative. Only the reference
point's residual is bounded; the comparison point ranges over the entire domain. -/
theorem norm_iteratedFDeriv_comp_sub_le {r : E → F} {U : Set E} {x y : E}
    {n : ℕ} {R M L : ℝ} (hn : 1 ≤ n) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hr : ContDiffOn ℝ n r U) (hx : x ∈ U) (hy : y ∈ U)
    (hR : ‖r x‖ ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hjet : ∀ i ∈ Finset.Icc 1 n, ∀ z ∈ U, ‖iteratedFDeriv ℝ i r z‖ ≤ M)
    (hLip : ∀ i ∈ Finset.Icc 1 n, ∀ u ∈ U, ∀ v ∈ U,
      ‖iteratedFDeriv ℝ i r v - iteratedFDeriv ℝ i r u‖ ≤ L * ‖v - u‖) :
    ‖iteratedFDeriv ℝ n (fun z => halfNormSq (r z)) y -
      iteratedFDeriv ℝ n (fun z => halfNormSq (r z)) x‖ ≤
        (R * L + (2 : ℝ) ^ n * M * (M + L)) * ‖y - x‖ := by
  have hrAt (z : E) (hz : z ∈ U) : ContDiffAt ℝ n r z :=
    (hr z hz).contDiffAt (hU.mem_nhds hz)
  have hzero : ‖r y - r x‖ ≤ M * ‖y - x‖ := by
    apply hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hrAt z hz).differentiableAt
        (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)))) _ hx hy
    intro z hz
    simpa only [norm_iteratedFDeriv_one] using
      hjet 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩) z hz
  let g : E → F := fun z => r (z + (y - x))
  have hxy : x + (y - x) = y := by abel
  have hg : ContDiffAt ℝ n g x := by
    have hh : ContDiffAt ℝ n r (x + (y - x)) := by rw [hxy]; exact hrAt y hy
    exact hh.comp x ((contDiffAt_id : ContDiffAt ℝ n (fun z : E => z) x).add
      contDiffAt_const)
  have hgjet (i : ℕ) : iteratedFDeriv ℝ i g x = iteratedFDeriv ℝ i r y := by
    simpa only [g, hxy] using iteratedFDeriv_comp_add_right i (y - x) x (f := r)
  have hh := norm_iteratedFDeriv_halfNormSq_sub_le hn (hrAt x hx) hg hR hM hL
    (norm_nonneg (y - x)) (by simpa only [g, hxy] using hzero)
    (fun i hi => hjet i hi x hx) (fun i hi => by rw [hgjet]; exact hjet i hi y hy)
    (fun i hi => by rw [hgjet]; exact hLip i hi x hx y hy)
  have hfun : (fun z => halfNormSq (g z)) =
      (fun z => (fun v => halfNormSq (r v)) (z + (y - x))) := rfl
  rw [hfun, iteratedFDeriv_comp_add_right (𝕜 := ℝ) n (y - x) x
    (f := fun v => halfNormSq (r v)), hxy] at hh
  exact hh

end SquaredNormJets
