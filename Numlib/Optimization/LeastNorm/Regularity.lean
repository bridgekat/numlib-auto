import Numlib.Analysis.Calculus.IteratedBilinearBounds
import Numlib.Optimization.LeastNorm.Run
import Mathlib.Analysis.Calculus.MeanValue
open scoped BigOperators
/-!
# Actual derivative bounds for least-squares residual merits

Binomial Leibniz estimates give bounds affine in the current residual norm.
All constants are fixed before a level-set radius is selected. The local
open convex domain and actual residual derivative bounds are retained.
-/

namespace LeastNorm

/-- Bound a binomial product-difference term while keeping zeroth-order
residual values separate from bounded positive-order derivatives. -/
theorem product_difference_term_le (a b d : ℕ → ℝ) {n i : ℕ} {B L R : ℝ}
    (hn : 0 < n) (hi : i ≤ n) (hB : 0 ≤ B) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (ha : ∀ j, 0 ≤ a j) (hd : ∀ j, 0 ≤ d j)
    (hb0 : b 0 ≤ a 0 + B * R) (hd0 : d 0 ≤ B * R)
    (hapos : ∀ j, 1 ≤ j → j ≤ n → a j ≤ B)
    (hbpos : ∀ j, 1 ≤ j → j ≤ n → b j ≤ B)
    (hdpos : ∀ j, 1 ≤ j → j ≤ n → d j ≤ L * R ∧ d j ≤ 2 * B) :
    d i * a (n - i) + b i * d (n - i) ≤
      (3 * B ^ 2 + 2 * B * L + 2 * L * a 0) * R := by
  have ha0 := ha 0
  have hBL : 0 ≤ B * L * R := by positivity
  have hLA : 0 ≤ L * a 0 * R := by positivity
  have hBB : 0 ≤ B ^ 2 * R := by positivity
  by_cases hi0 : i = 0
  · subst i
    simp only [Nat.sub_zero]
    have h1 := mul_le_mul hd0 (hapos n hn le_rfl) (ha n) (by positivity : 0 ≤ B * R)
    have h2 := mul_le_mul_of_nonneg_left (hdpos n hn le_rfl).1 (ha 0)
    have h3 := mul_le_mul_of_nonneg_left (hdpos n hn le_rfl).2
      (mul_nonneg hB hR)
    have h4 := mul_le_mul_of_nonneg_right hb0 (hd n)
    nlinarith
  · have hip : 1 ≤ i := by omega
    by_cases hik : n - i = 0
    · have hin : i = n := by omega
      subst i
      simp only [Nat.sub_self]
      have h1 := mul_le_mul_of_nonneg_right (hdpos n hn le_rfl).1 (ha 0)
      have h2 := mul_le_mul (hbpos n hn le_rfl) hd0 (hd 0) hB
      nlinarith
    · have hk : 1 ≤ n - i := by omega
      have h1 := mul_le_mul (hdpos i hip hi).1 (hapos (n - i) hk (Nat.sub_le _ _))
        (ha _) (mul_nonneg hL hR)
      have h2 := mul_le_mul (hbpos i hip hi) (hdpos (n - i) hk (Nat.sub_le _ _)).1
        (hd _) hB
      nlinarith

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual positive-order derivative of a squared residual norm has
an affine bound in the current residual norm. -/
theorem norm_sq_derivative_bound {f : E → F} {n : ℕ} {S : Set E}
    (hn : 0 < n) (hf : ContDiffOn ℝ n f S) (hS : IsOpen S)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    {x : E} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x‖ ≤
      (2 : ℝ) ^ n * (B ^ 2 + B * ‖f x‖) := by
  have hnorm := (innerSL ℝ (E := F)).norm_iteratedFDerivWithin_le_of_bilinear
    hf hf hS.uniqueDiffOn hx le_rfl
  have he : (fun z => innerSL ℝ (f z) (f z)) = fun z => ‖f z‖ ^ 2 := by
    funext z; exact real_inner_self_eq_norm_sq (f z)
  rw [he, iteratedFDerivWithin_of_isOpen n hS hx] at hnorm
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ i f S x‖ * ‖iteratedFDerivWithin ℝ (n - i) f S x‖ := by
    positivity
  apply (hnorm.trans (mul_le_of_le_one_left hsum
    (norm_innerSL_le (𝕜 := ℝ) (E := F)))).trans
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ B ^ 2 + B * ‖f x‖ := by
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hk : n - i ≤ n := Nat.sub_le _ _
    by_cases hi0 : i = 0
    · subst i
      simp only [norm_iteratedFDeriv_zero, Nat.sub_zero]
      have hh := mul_le_mul_of_nonneg_left (hb n hn le_rfl x hx) (norm_nonneg (f x))
      nlinarith [sq_nonneg B]
    · by_cases hk0 : n - i = 0
      · rw [hk0, norm_iteratedFDeriv_zero]
        have hh := mul_le_mul_of_nonneg_right (hb i (by omega) hin x hx) (norm_nonneg (f x))
        nlinarith [sq_nonneg B]
      · have hh := mul_le_mul (hb i (by omega) hin x hx)
          (hb (n - i) (by omega) hk x hx) (norm_nonneg _) hB
        nlinarith [mul_nonneg hB (norm_nonneg (f x))]
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (B ^ 2 + B * ‖f x‖) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [iteratedFDerivWithin_of_isOpen i hS hx,
          iteratedFDerivWithin_of_isOpen (n - i) hS hx, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * (B ^ 2 + B * ‖f x‖) := by
      rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      exact_mod_cast Nat.sum_range_choose n

/-- Bound actual squared-norm derivative differences on an open convex domain,
with affine dependence on the residual norm at the first endpoint. -/
theorem norm_sq_derivative_difference_bound {f : E → F} {n : ℕ} {S : Set E}
    (hn : 0 < n) (hf : ContDiffOn ℝ n f S) (hS : IsOpen S) (hconv : Convex ℝ S)
    {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hl : ∀ j, 1 ≤ j → j ≤ n → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x -
      iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) y‖ ≤
      (2 : ℝ) ^ n * (3 * B ^ 2 + 2 * B * L + 2 * L * ‖f x‖) * ‖x - y‖ := by
  have hv : ‖f x - f y‖ ≤ B * ‖x - y‖ := by
    apply hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by exact_mod_cast hn.ne'))
      (fun z hz => ?_) hy hx
    rw [←norm_iteratedFDeriv_one f]
    exact hb 1 le_rfl hn z hz
  have hnormy : ‖f y‖ ≤ ‖f x‖ + B * ‖x - y‖ := by
    calc ‖f y‖ ≤ ‖f x‖ + ‖f y - f x‖ := by
          have he : f y = f x + (f y - f x) := by abel
          calc ‖f y‖ = ‖f x + (f y - f x)‖ := congrArg norm he
            _ ≤ _ := norm_add_le _ _
      _ = ‖f x‖ + ‖f x - f y‖ := by rw [norm_sub_rev]
      _ ≤ _ := add_le_add le_rfl hv
  apply (norm_iteratedFDeriv_norm_sq_sub_le hf hS hx hy).trans
  let C := (3 * B ^ 2 + 2 * B * L + 2 * L * ‖f x‖) * ‖x - y‖
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖ + ‖iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) f x - iteratedFDeriv ℝ (n - i) f y‖ ≤ C := by
    intro i hi
    have hh := product_difference_term_le (fun j => ‖iteratedFDeriv ℝ j f x‖)
      (fun j => ‖iteratedFDeriv ℝ j f y‖)
      (fun j => ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖)
      (R := ‖x - y‖) hn (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hB hL (norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (by simpa only [norm_iteratedFDeriv_zero] using hnormy)
      (by simpa only [norm_iteratedFDeriv_zero_sub] using hv)
      (fun j hj hjn => hb j hj hjn x hx) (fun j hj hjn => hb j hj hjn y hy)
      (fun j hj hjn => ⟨hl j hj hjn x hx y hy,
        (norm_sub_le _ _).trans (by linarith [hb j hj hjn x hx, hb j hj hjn y hy])⟩)
    simpa only [norm_iteratedFDeriv_zero] using hh
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C := by
        exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hterm i hi)
          (Nat.cast_nonneg _))
    _ = ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ))) * C := by rw [Finset.sum_mul]
    _ = _ := by
      have he : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [he]
      dsimp [C]
      ring

/-- The actual least-squares merit derivative is half the squared-norm derivative. -/
theorem iteratedFDeriv_merit {f : E → F} {n : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ n f S) (hS : IsOpen S) {x : E} (hx : x ∈ S) :
    iteratedFDeriv ℝ n (LeastNorm.merit f) x =
      (1 / 2 : ℝ) • iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x := by
  have he : LeastNorm.merit f = fun z => (1 / 2 : ℝ) • ‖f z‖ ^ 2 := by
    funext z
    simp only [LeastNorm.merit, smul_eq_mul]
    ring
  rw [he]
  exact iteratedFDeriv_const_smul_apply (a := (1 / 2 : ℝ))
    ((hf.norm_sq (𝕜 := ℝ)).contDiffAt (hS.mem_nhds hx))

/-- The factor one half can be discarded in a squared-norm derivative bound. -/
theorem norm_merit_derivative_le_norm_sq {f : E → F} {n : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ n f S) (hS : IsOpen S) {x : E} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ n (LeastNorm.merit f) x‖ ≤
      ‖iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x‖ := by
  rw [iteratedFDeriv_merit hf hS hx, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_div, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [norm_nonneg (iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x)]

/-- The factor one half can be discarded in a derivative difference bound. -/
theorem norm_merit_derivative_sub_le_norm_sq {f : E → F} {n : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ n f S) (hS : IsOpen S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖iteratedFDeriv ℝ n (LeastNorm.merit f) x -
      iteratedFDeriv ℝ n (LeastNorm.merit f) y‖ ≤
      ‖iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x -
        iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) y‖ := by
  rw [iteratedFDeriv_merit hf hS hx, iteratedFDeriv_merit hf hS hy, ←smul_sub, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_div, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [norm_nonneg (iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x -
    iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) y)]

/-- A residual norm bound gives explicit uniform bounds on all positive
derivatives and their differences, independent of the selected derivative order. -/
theorem merit_derivative_bounds_of_residual_bound {f : E → F} {p j : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ p f S) (hS : IsOpen S) (hconv : Convex ℝ S)
    {B L R : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : ∀ i, 1 ≤ i → i ≤ p → ∀ z ∈ S, ‖iteratedFDeriv ℝ i f z‖ ≤ B)
    (hl : ∀ i, 1 ≤ i → i ≤ p → ∀ z ∈ S, ∀ w ∈ S,
      ‖iteratedFDeriv ℝ i f z - iteratedFDeriv ℝ i f w‖ ≤ L * ‖z - w‖)
    (hj : 1 ≤ j) (hjp : j ≤ p) {x : E} (hx : x ∈ S) (hxr : ‖f x‖ ≤ R) :
    (∀ y ∈ S, ‖iteratedFDeriv ℝ j (LeastNorm.merit f) x -
      iteratedFDeriv ℝ j (LeastNorm.merit f) y‖ ≤
      ((2 : ℝ) ^ p * (3 * B ^ 2 + 2 * B * L + 2 * L * R)) * ‖x - y‖) ∧
      ‖iteratedFDeriv ℝ j (LeastNorm.merit f) x‖ ≤ (2 : ℝ) ^ p * (B ^ 2 + B * R) := by
  have hfj : ContDiffOn ℝ j f S := hf.of_le (by exact_mod_cast hjp)
  have hbj : ∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ S, ‖iteratedFDeriv ℝ i f z‖ ≤ B :=
    fun i hi hij => hb i hi (hij.trans hjp)
  have hlj : ∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ S, ∀ w ∈ S,
      ‖iteratedFDeriv ℝ i f z - iteratedFDeriv ℝ i f w‖ ≤ L * ‖z - w‖ :=
    fun i hi hij => hl i hi (hij.trans hjp)
  have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ p :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjp
  have hP : 0 ≤ (2 : ℝ) ^ p := by positivity
  have hinside : (2 : ℝ) ^ j * (3 * B ^ 2 + 2 * B * L + 2 * L * ‖f x‖) ≤
      (2 : ℝ) ^ p * (3 * B ^ 2 + 2 * B * L + 2 * L * R) := by
    have h1 := mul_le_mul_of_nonneg_right hpow
      (show 0 ≤ 3 * B ^ 2 + 2 * B * L + 2 * L * ‖f x‖ by positivity)
    have h2 := mul_le_mul_of_nonneg_left hxr (show 0 ≤ 2 * (2 : ℝ) ^ p * L by positivity)
    nlinarith
  have hnorm : (2 : ℝ) ^ j * (B ^ 2 + B * ‖f x‖) ≤
      (2 : ℝ) ^ p * (B ^ 2 + B * R) := by
    have h1 := mul_le_mul_of_nonneg_right hpow
      (show 0 ≤ B ^ 2 + B * ‖f x‖ by positivity)
    have h2 := mul_le_mul_of_nonneg_left hxr (mul_nonneg hP hB)
    nlinarith
  refine ⟨?_, ?_⟩
  · intro y hy
    exact ((norm_merit_derivative_sub_le_norm_sq hfj hS hx hy).trans
      (norm_sq_derivative_difference_bound hj hfj hS hconv hB hL hbj hlj hx hy)).trans
        (mul_le_mul_of_nonneg_right hinside (norm_nonneg _))
  · exact (norm_merit_derivative_le_norm_sq hfj hS hx).trans
      ((norm_sq_derivative_bound hj hfj hS hB hbj hx).trans hnorm)

/-- Actual bounded Lipschitz residual derivatives give least-squares merit
regularity on every residual level, with four constants chosen before that level. -/
theorem merit_regularity_on_residual_levels {f : E → F} {p : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ p f S) (hS : IsOpen S) (hconv : Convex ℝ S)
    {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hl : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖) :
    ∃ LA ≥ 1, ∃ LB ≥ 1, ∃ BA ≥ 1, ∃ BB ≥ 1,
      ContDiffOn ℝ p (LeastNorm.merit f) S ∧
      ∀ R : ℝ, 0 ≤ R → ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ‖f x‖ ≤ R →
        (∀ y ∈ S, ‖iteratedFDeriv ℝ j (LeastNorm.merit f) x -
          iteratedFDeriv ℝ j (LeastNorm.merit f) y‖ ≤ (LA + LB * R) * ‖x - y‖) ∧
        ‖iteratedFDeriv ℝ j (LeastNorm.merit f) x‖ ≤ BA + BB * R := by
  let P : ℝ := 2 ^ p
  let LA := 1 + P * (3 * B ^ 2 + 2 * B * L)
  let LB := 1 + 2 * P * L
  let BA := 1 + P * B ^ 2
  let BB := 1 + P * B
  have hP : 0 ≤ P := by positivity
  refine ⟨LA, by dsimp [LA]; exact le_add_of_nonneg_right (by positivity),
    LB, by dsimp [LB]; exact le_add_of_nonneg_right (by positivity),
    BA, by dsimp [BA]; exact le_add_of_nonneg_right (by positivity),
    BB, by dsimp [BB]; exact le_add_of_nonneg_right (by positivity), ?_, ?_⟩
  · have hh := (hf.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ)
    convert hh using 1
    funext z
    simp only [LeastNorm.merit, smul_eq_mul]
    ring
  · intro R hR j hj hjp x hx hxr
    have hj0 : 0 < j := hj
    have hfj : ContDiffOn ℝ j f S := hf.of_le (by exact_mod_cast hjp)
    have hbj : ∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ S, ‖iteratedFDeriv ℝ i f z‖ ≤ B :=
      fun i hi hij => hb i hi (hij.trans hjp)
    have hlj : ∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ S, ∀ w ∈ S,
        ‖iteratedFDeriv ℝ i f z - iteratedFDeriv ℝ i f w‖ ≤ L * ‖z - w‖ :=
      fun i hi hij => hl i hi (hij.trans hjp)
    have hpow : (2 : ℝ) ^ j ≤ P := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjp
    have hinside : (2 : ℝ) ^ j * (3 * B ^ 2 + 2 * B * L + 2 * L * ‖f x‖) ≤
        LA + LB * R := by
      have h1 := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ 3 * B ^ 2 + 2 * B * L + 2 * L * ‖f x‖ by positivity)
      have h2 := mul_le_mul_of_nonneg_left hxr (show 0 ≤ 2 * P * L by positivity)
      dsimp [LA, LB]
      nlinarith
    have hnorm : (2 : ℝ) ^ j * (B ^ 2 + B * ‖f x‖) ≤ BA + BB * R := by
      have h1 := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ B ^ 2 + B * ‖f x‖ by positivity)
      have h2 := mul_le_mul_of_nonneg_left hxr (mul_nonneg hP hB)
      dsimp [BA, BB]
      nlinarith
    refine ⟨?_, ?_⟩
    · intro y hy
      exact ((norm_merit_derivative_sub_le_norm_sq hfj hS hx hy).trans
        (norm_sq_derivative_difference_bound hj0 hfj hS hconv hB hL hbj hlj hx hy)).trans
          (by nlinarith [mul_le_mul_of_nonneg_right hinside (norm_nonneg (x - y))])
    · exact (norm_merit_derivative_le_norm_sq hfj hS hx).trans
        ((norm_sq_derivative_bound hj0 hfj hS hB hbj hx).trans hnorm)
end LeastNorm
