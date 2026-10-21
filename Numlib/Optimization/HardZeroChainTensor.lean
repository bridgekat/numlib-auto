import Numlib.Optimization.HardZeroChainBounds
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.Calculus.SymmetricDerivativeNorm
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Dimension independent derivatives of adjacent coordinate interactions

Complementary scalar derivative orders retain the scalar Gaussian growth exponent.
Banach's theorem for symmetric forms on real Hilbert spaces then converts diagonal
estimates into actual multilinear operator estimates, including independent directions.
-/

noncomputable section
open Real
open scoped ContDiff
namespace Optimization.HardZeroChain

/-- Products of complementary powers on the unit interval are controlled by two squares. -/
theorem complementary_powers_le_sq_add_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) {r k : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    a ^ k * b ^ (r - k) ≤ a ^ 2 + b ^ 2 := by
  by_cases hka : 2 ≤ k
  · have hpow : a ^ k ≤ a ^ 2 := pow_le_pow_of_le_one ha ha1 hka
    have hpb : b ^ (r - k) ≤ 1 := pow_le_one₀ hb hb1
    calc
      _ ≤ a ^ 2 * 1 := mul_le_mul hpow hpb (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg b]
  by_cases hkb : 2 ≤ r - k
  · have hpow : b ^ (r - k) ≤ b ^ 2 := pow_le_pow_of_le_one hb hb1 hkb
    have hpa : a ^ k ≤ 1 := pow_le_one₀ ha ha1
    calc
      _ ≤ 1 * b ^ 2 := mul_le_mul hpa hpow (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg a]
  have hk1 : k = 1 := by omega
  have hrk : r - k = 1 := by omega
  rw [hrk, hk1, pow_one, pow_one]
  nlinarith [sq_nonneg (a - b)]

/-- A sum of adjacent complementary coordinate powers is bounded independently of dimension. -/
theorem sum_adjacent_powers_le {n r k : ℕ} (hr : 2 ≤ r) (hk : k ≤ r)
    (h : ZeroChains.Space (n + 1)) (hh : ‖h‖ ≤ 1) :
    ∑ i : Fin n, ‖h i.castSucc‖ ^ k * ‖h i.succ‖ ^ (r - k) ≤ 2 := by
  have hcoord (i : Fin (n + 1)) : ‖h i‖ ≤ 1 := (PiLp.norm_apply_le h i).trans hh
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ ↦ complementary_powers_le_sq_add_sq (norm_nonneg _) (norm_nonneg _)
      (hcoord i.castSucc) (hcoord i.succ) hr hk)
  have hnorm : ∑ i : Fin (n + 1), ‖h i‖ ^ 2 ≤ 1 := by
    rw [← PiLp.norm_sq_eq_of_L2]
    nlinarith [norm_nonneg h]
  have ha : ∑ i : Fin n, ‖h i.castSucc‖ ^ 2 ≤ 1 := by
    have he := Fin.sum_univ_castSucc (fun i : Fin (n + 1) ↦ ‖h i‖ ^ 2)
    nlinarith [sq_nonneg ‖h (Fin.last n)‖]
  have hb : ∑ i : Fin n, ‖h i.succ‖ ^ 2 ≤ 1 := by
    have he := Fin.sum_univ_succ (fun i : Fin (n + 1) ↦ ‖h i‖ ^ 2)
    nlinarith [sq_nonneg ‖h 0‖]
  rw [Finset.sum_add_distrib] at hs
  linarith

/-- Scalar derivatives along an affine line are the scaled actual scalar derivatives. -/
theorem iteratedDeriv_affine {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (r : ℕ) (a b t : ℝ) :
    iteratedDeriv r (fun z ↦ f (a + z * b)) t =
      b ^ r * iteratedDeriv r f (a + t * b) := by
  have he : (fun z ↦ f (a + z * b)) = (fun z ↦ (fun y ↦ f (a + y)) (b * z)) := by
    funext z
    congr 1
    ring
  have hs : ContDiff ℝ (r : ℕ) (fun y ↦ f (a + y)) :=
    (hf.comp (by fun_prop)).of_le (by simp)
  rw [he, iteratedDeriv_comp_const_mul hs b, iteratedDeriv_comp_const_add]
  simp only [mul_comm]

/-- The higher product rule for two linear coordinates, evaluated on a diagonal. -/
theorem iteratedFDeriv_coordinate_product {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : E →L[ℝ] ℝ) (r : ℕ) (x h : E) :
    iteratedFDeriv ℝ r (fun y ↦ f (a y) * g (b y)) x (fun _ ↦ h) =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        (a h ^ k * iteratedDeriv k f (a x)) *
        (b h ^ (r - k) * iteratedDeriv (r - k) g (b x)) := by
  have hs : ContDiff ℝ ∞ (fun y ↦ f (a y) * g (b y)) :=
    (hf.comp a.contDiff).mul (hg.comp b.contDiff)
  rw [iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_univ
    (hs.of_le (by simp)).contDiffOn (Set.mem_univ x) h]
  have he : (fun t : ℝ ↦ f (a (x + t • h)) * g (b (x + t • h))) =
      fun t ↦ f (a x + t * a h) * g (b x + t * b h) := by
    funext t
    simp
  have hfa : ContDiff ℝ (r : ℕ) (fun t : ℝ ↦ f (a x + t * a h)) :=
    (hf.comp (by fun_prop)).of_le (by simp)
  have hgb : ContDiff ℝ (r : ℕ) (fun t : ℝ ↦ g (b x + t * b h)) :=
    (hg.comp (by fun_prop)).of_le (by simp)
  rw [he, iteratedDeriv_fun_mul hfa.contDiffAt hgb.contDiffAt]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDeriv_affine hf, iteratedDeriv_affine hg]
  simp

/-- A chain of adjacent scalar products. -/
def adjacentProduct (n : ℕ) (f g : ℝ → ℝ) (x : ZeroChains.Space (n + 1)) : ℝ :=
  ∑ i : Fin n, f (x i.castSucc) * g (x i.succ)

/-- An adjacent product evaluates to the sum over its actual neighboring coordinates. -/
@[simp] theorem adjacentProduct_apply (n : ℕ) (f g : ℝ → ℝ)
    (x : ZeroChains.Space (n + 1)) :
    adjacentProduct n f g x = ∑ i : Fin n, f (x i.castSucc) * g (x i.succ) := rfl

/-- Adjacent products inherit infinite smoothness from their scalar factors. -/
@[fun_prop] theorem contDiff_adjacentProduct (n : ℕ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (adjacentProduct n f g) := by
  apply ContDiff.sum
  intro i _
  exact (hf.comp (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff).mul
    (hg.comp (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff)

/-- Complementary scalar bounds control the full derivative tensor of an adjacent product
chain, with a constant independent of its length. Banach's exact symmetric norm theorem
supplies control of arbitrary independent directions from the diagonal estimate. -/
theorem norm_iteratedFDeriv_adjacentProduct_le (n : ℕ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {r : ℕ} (hr : 2 ≤ r)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, k ≤ r → ∀ a b, ‖iteratedDeriv k f a‖ *
      ‖iteratedDeriv (r - k) g b‖ ≤ B) (x : ZeroChains.Space (n + 1)) :
    ‖iteratedFDeriv ℝ r (adjacentProduct n f g) x‖ ≤ 2 * 2 ^ r * B := by
  have hs : ContDiff ℝ (r : ℕ) (adjacentProduct n f g) :=
    (contDiff_adjacentProduct n hf hg).of_le (by simp)
  rw [← hs.contDiffAt.diagonalNorm_iteratedFDeriv_eq_norm (by omega)]
  apply ContinuousMultilinearMap.diagonalNorm_le _ (by positivity)
  intro h hh
  change ‖iteratedFDeriv ℝ r (adjacentProduct n f g) x (fun _ ↦ h)‖ ≤ _
  have hterm (i : Fin n) : ContDiff ℝ (r : ℕ)
      (fun y : ZeroChains.Space (n + 1) ↦ f (y i.castSucc) * g (y i.succ)) :=
    ((hf.comp (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff).mul
      (hg.comp (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff)).of_le (by simp)
  unfold adjacentProduct
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ (hterm i).contDiffAt)]
  simp only [sum_apply]
  have hformula (i : Fin n) := iteratedFDeriv_coordinate_product hf hg
    (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc)
    (EuclideanSpace.proj (𝕜 := ℝ) i.succ) r x h
  simp only [EuclideanSpace.coe_proj] at hformula
  simp_rw [hformula]
  calc
    _ ≤ ∑ i : Fin n, ∑ k ∈ Finset.range (r + 1),
        (r.choose k : ℝ) * (‖h i.castSucc‖ ^ k * ‖h i.succ‖ ^ (r - k)) * B := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_mul, norm_pow, norm_natCast]
      have hsc := hb k (by simpa using Finset.mem_range.mp hk) (x i.castSucc) (x i.succ)
      calc
        _ = (r.choose k : ℝ) * (‖h i.castSucc‖ ^ k * ‖h i.succ‖ ^ (r - k)) *
            (‖iteratedDeriv k f (x i.castSucc)‖ *
              ‖iteratedDeriv (r - k) g (x i.succ)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        (∑ i : Fin n, ‖h i.castSucc‖ ^ k * ‖h i.succ‖ ^ (r - k)) * B := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * 2 * B := by
      apply Finset.sum_le_sum
      intro k hk
      gcongr
      exact sum_adjacent_powers_le hr (by simpa using Finset.mem_range.mp hk) h hh.le
    _ = 2 * 2 ^ r * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hc : (∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ)) = 2 ^ r := by
        exact_mod_cast Nat.sum_range_choose r
      rw [hc]
      ring

/-- Pullback by a contraction does not increase the norm of a scalar derivative tensor. -/
theorem norm_iteratedFDeriv_scalar_comp_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (f ∘ L) x‖ ≤ ‖iteratedDeriv r f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  apply ((iteratedFDeriv ℝ r f (L x)).norm_compContinuousLinearMap_le _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

/-- All actual chain derivatives of order at least two have one dimension independent
Gaussian growth constant. The estimate is for the full operator norm. -/
theorem uniform_chain_derivative_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℕ, 2 ≤ r → ∀ n : ℕ,
      ∀ x : ZeroChains.Space (n + 1),
      ‖iteratedFDeriv ℝ r (chain n) x‖ ≤ exp ((5 / 2 : ℝ) * r * log r + C * r) := by
  obtain ⟨c, hc, hb⟩ := scalar_derivative_bounds_up_to
  refine ⟨2 * c + log 2 + 5, ?_, fun r hr n x ↦ ?_⟩
  · have := log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  let B := exp ((5 / 2 : ℝ) * r * log r + c * (r + 2))
  have hB : 0 ≤ B := (exp_pos _).le
  have hprod : ∀ k, k ≤ r → ∀ a b, ‖iteratedDeriv k psi a‖ *
      ‖iteratedDeriv (r - k) phi b‖ ≤ B := by
    intro k hk a b
    apply (mul_le_mul ((hb r (by omega) k hk a).1)
      ((hb r (by omega) (r - k) (Nat.sub_le _ _) b).2)
      (norm_nonneg _) (exp_pos _).le).trans
    rw [← exp_add]
    apply exp_le_exp.mpr
    have hkr : (k : ℝ) + (r - k : ℕ) = r := by exact_mod_cast Nat.add_sub_of_le hk
    nlinarith [congrArg (fun t : ℝ ↦ t * log r) hkr,
      congrArg (fun t : ℝ ↦ c * t) hkr]
  have hpos := norm_iteratedFDeriv_adjacentProduct_le n contDiff_psi
    Analysis.FlatGaussian.contDiff_primitive hr hB hprod x
  have hneg := norm_iteratedFDeriv_adjacentProduct_le n
    (contDiff_psi.comp contDiff_neg) (Analysis.FlatGaussian.contDiff_primitive.comp contDiff_neg)
    hr hB (fun k hk a b ↦ by
      change ‖iteratedDeriv k (fun t ↦ psi (-t)) a‖ *
        ‖iteratedDeriv (r - k) (fun t ↦ phi (-t)) b‖ ≤ B
      simpa only [iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg, norm_one,
        one_pow, one_mul] using hprod k hk (-a) (-b)) x
  let L := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    simpa only [L, EuclideanSpace.coe_proj, one_mul] using PiLp.norm_apply_le y 0
  have hseed := norm_iteratedFDeriv_scalar_comp_le
    Analysis.FlatGaussian.contDiff_primitive L hL r x
  have hseedB : ‖iteratedFDeriv ℝ r (phi ∘ L) x‖ ≤ B := by
    apply hseed.trans
    apply ((hb r (by omega) r le_rfl (L x)).2).trans
    apply exp_le_exp.mpr
    nlinarith
  have he : chain n = -(phi ∘ L) +
      (adjacentProduct n (fun t ↦ psi (-t)) (fun t ↦ phi (-t)) -
        adjacentProduct n psi phi) := by
    funext y
    simp [chain, adjacentProduct, L, Finset.sum_sub_distrib]
  have hs : ContDiff ℝ (r : ℕ) (phi ∘ L) :=
    (Analysis.FlatGaussian.contDiff_primitive.comp L.contDiff).of_le (by simp)
  have hp : ContDiff ℝ (r : ℕ) (adjacentProduct n psi phi) :=
    (contDiff_adjacentProduct n contDiff_psi
      Analysis.FlatGaussian.contDiff_primitive).of_le (by simp)
  have hm : ContDiff ℝ (r : ℕ)
      (adjacentProduct n (fun t ↦ psi (-t)) (fun t ↦ phi (-t))) :=
    (contDiff_adjacentProduct n (contDiff_psi.comp contDiff_neg)
      (Analysis.FlatGaussian.contDiff_primitive.comp contDiff_neg)).of_le (by simp)
  have hsum : ‖iteratedFDeriv ℝ r (chain n) x‖ ≤ 5 * 2 ^ r * B := by
    rw [he]
    change ‖iteratedFDeriv ℝ r (-(phi ∘ L) +
      (adjacentProduct n (fun t ↦ psi (-t)) (fun t ↦ phi (-t)) -
        adjacentProduct n psi phi)) x‖ ≤ _
    rw [iteratedFDeriv_add_apply (f := -(phi ∘ L)) (g :=
      adjacentProduct n (fun t ↦ psi (-t)) (fun t ↦ phi (-t)) -
        adjacentProduct n psi phi) hs.neg.contDiffAt (hm.sub hp).contDiffAt,
      iteratedFDeriv_neg_apply, iteratedFDeriv_sub_apply hm.contDiffAt hp.contDiffAt]
    have hseedNeg : ‖-iteratedFDeriv ℝ r (phi ∘ L) x‖ ≤ B := by
      simpa only [norm_neg] using hseedB
    have hn := (norm_add_le (-iteratedFDeriv ℝ r (phi ∘ L) x) _).trans
      (add_le_add hseedNeg ((norm_sub_le _ _).trans (add_le_add hneg hpos)))
    apply hn.trans
    have hpow : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    nlinarith
  apply hsum.trans
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hfive : (5 : ℝ) ≤ exp (5 * r) := by linarith [add_one_le_exp (5 * (r : ℝ))]
  calc
    5 * 2 ^ r * B ≤ exp (5 * r) * exp ((r : ℝ) * log 2) * B := by
      rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
      gcongr
    _ = exp (5 * r + r * log 2 + ((5 / 2 : ℝ) * r * log r + c * (r + 2))) := by
      rw [← exp_add, ← exp_add]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith

/-- Increasing a positive integer order by one costs only a linear term in its logarithmic
Gaussian growth exponent. -/
theorem succ_mul_log_succ_le {p : ℕ} (hp : 1 ≤ p) :
    ((p : ℝ) + 1) * log ((p : ℝ) + 1) ≤ p * log p + 3 * p := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : (0 : ℝ) < p := by positivity
  have hlog : log ((p : ℝ) + 1) ≤ log p + 1 := by
    calc
      _ ≤ log (2 * (p : ℝ)) := log_le_log (by positivity) (by linarith)
      _ = log 2 + log p := log_mul (by norm_num) (ne_of_gt hpp)
      _ ≤ _ := by linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogp : log (p : ℝ) ≤ p := by linarith [log_le_sub_one_of_pos hpp]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (p : ℝ) + 1 by positivity)
  nlinarith

/-- A single shifted-order bound has the exponent required for derivative Lipschitz
continuity, uniformly in both order and dimension. -/
theorem uniform_chain_succ_derivative_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 1 ≤ p → ∀ n : ℕ,
      ∀ x : ZeroChains.Space (n + 1),
      ‖iteratedFDeriv ℝ (p + 1) (chain n) x‖ ≤
        exp ((5 / 2 : ℝ) * p * log p + C * p) := by
  obtain ⟨c, hc, hb⟩ := uniform_chain_derivative_bounds
  refine ⟨2 * c + 8, (by linarith), fun p hp n x ↦ ?_⟩
  apply (hb (p + 1) (by omega) n x).trans
  apply exp_le_exp.mpr
  push_cast
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog := succ_mul_log_succ_le hp
  have hcp : c * ((p : ℝ) + 1) ≤ 2 * c * p := by nlinarith
  nlinarith

/-- The actual next derivative is bounded on a tuple containing an independent direction
and repeated directions. No relation between the displacement and repeated direction is
required, and the constant is independent of order and dimension. -/
theorem uniform_chain_mixed_derivative_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 1 ≤ p → ∀ n : ℕ,
      ∀ x h v : ZeroChains.Space (n + 1),
      ‖iteratedFDeriv ℝ (p + 1) (chain n) x (Fin.cons v (fun _ ↦ h))‖ ≤
        exp ((5 / 2 : ℝ) * p * log p + C * p) * ‖v‖ * ‖h‖ ^ p := by
  obtain ⟨c, hc, hb⟩ := uniform_chain_succ_derivative_bounds
  refine ⟨c, hc, fun p hp n x h v ↦ ?_⟩
  apply ((iteratedFDeriv ℝ (p + 1) (chain n) x).le_opNorm _).trans
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have he := mul_le_mul_of_nonneg_right (hb p hp n x)
    (show 0 ≤ ‖v‖ * ‖h‖ ^ p by positivity)
  simpa only [mul_assoc] using he

/-- A single constant controls the Lipschitz norm of every positive-order actual chain
derivative, uniformly in dimension. The mean-value argument uses the full next-order
operator bound, so its displacement direction is independent of the repeated directions. -/
theorem uniform_chain_derivative_lipschitz :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 1 ≤ p → ∀ n : ℕ,
      ∀ x y : ZeroChains.Space (n + 1),
      ‖iteratedFDeriv ℝ p (chain n) x - iteratedFDeriv ℝ p (chain n) y‖ ≤
        exp ((5 / 2 : ℝ) * p * log p + C * p) * ‖x - y‖ := by
  obtain ⟨c, hc, hb⟩ := uniform_chain_succ_derivative_bounds
  refine ⟨c, hc, fun p hp n x y ↦ ?_⟩
  have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ p (chain n)) :=
    (contDiff_chain n).iteratedFDeriv_right (by simp)
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
    (fun z _ ↦ (hd.differentiable (by norm_num)).differentiableAt)
    (fun z _ ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hb p hp n z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

end Optimization.HardZeroChain
