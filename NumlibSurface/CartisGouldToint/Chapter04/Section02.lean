import Numlib.Optimization.HardZeroChainGradient
import Numlib.Optimization.HardZeroChainTensor
import Numlib.Optimization.DerivativeOracleMethods
import Numlib.Optimization.OracleMinimax
import Numlib.Optimization.OracleRegularizationCost
import Numlib.Optimization.HardZeroChainScaling
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section01.Complexity

/-!
# Chapter 4, Section 2: derivative oracles and higher-order zero chains

The oracle method receives the entire finite history of actual values and derivatives.
Its rule is specified in every finite Euclidean dimension. The first attainment time includes
infinity, and complexity is the best worst-case value over dimension-varying function classes.

Coordinates are zero based: the source's first `k` coordinates have indices strictly below
`k`. A mixed derivative exposes every coordinate occurring in a nonzero entry, for each order
one through `p`, exactly as in (4.2.1) and (4.2.4). The rotation action is the actual pullback
by the adjoint of an isometric embedding; no resisting-oracle lower bound is assumed here.
The function class makes explicit the Lipschitz parameter suppressed in the notation
`F(Δ,p)`, and uses the highest-derivative norm from the preceding section.
-/

noncomputable section
open scoped ContDiff ENNReal
open Optimization.ZeroChains Optimization.DerivativeOracle

namespace CartisGouldToint.Chapter04.Section02

/-- Deterministic order-`p` methods, specified by finite histories of actual value and
Fréchet-derivative oracle responses in every Euclidean dimension. -/
abbrev derivativeOracleMethod (p : ℕ) := Method p

/-- The explicit smooth difficult chain in `n + 1` Euclidean coordinates.
The supplied OCR of (4.2.6) has the seed `-Psi(x₁) Phi(x₁)`. We use the corrected
seed `-Psi(1) Phi(x₁)`, verified in Carmon, Duchi, Hinder and Sidford,
*Lower Bounds for Finding Stationary Points I*, arXiv:1710.11606v3,
equation (10), page 12. The scalar factors are the actual flat exponential and
improper Gaussian integral; their regularity is proved in the backbone. -/
abbrev difficultZeroChain (n : ℕ) : Space (n + 1) → ℝ := Optimization.HardZeroChain.chain n

/-- The explicit difficult chain is infinitely smooth in every finite dimension. -/
theorem difficultZeroChain_smooth (n : ℕ) : ContDiff ℝ ∞ (difficultZeroChain n) :=
  Optimization.HardZeroChain.contDiff_chain n

/-- The difficult chain has the full support law for every derivative order. This proves
clause (i) of Lemma 4.2.5; all four clauses are collected in `lemma_4_2_5`. -/
theorem difficultZeroChain_isZeroChain (n p : ℕ) : IsZeroChain p (difficultZeroChain n) :=
  Optimization.HardZeroChain.isZeroChain n p

/-- Clause (iii) of Lemma 4.2.5: the actual objective is bounded below and its initial gap
is at most twelve times the Euclidean dimension. -/
theorem difficultZeroChain_gap (n : ℕ) :
    BddBelow (Set.range (difficultZeroChain n)) ∧
      difficultZeroChain n 0 - sInf (Set.range (difficultZeroChain n)) ≤ 12 * (n + 1 : ℝ) :=
  ⟨Optimization.HardZeroChain.bddBelow_chain n, Optimization.HardZeroChain.chain_initial_gap n⟩

/-- Clause (ii) of Lemma 4.2.5: a coordinate with magnitude below one forces the
actual Euclidean gradient norm to exceed one. -/
theorem difficultZeroChain_gradient (n : ℕ) (x : Space (n + 1))
    (hx : ∃ i : Fin (n + 1), |x i| < 1) : 1 < ‖gradient (difficultZeroChain n) x‖ :=
  Optimization.HardZeroChain.one_lt_norm_gradient_chain n x hx

/-- The source's function class, with explicit derivative Lipschitz parameter and positive
order and gap budget. Smoothness is `C^∞`; the lower bound is the actual infimum. -/
def functionClass (p : ℕ) (Δ L : ℝ) : Set Objective :=
  {f | 1 ≤ p ∧ 0 < Δ ∧ 1 ≤ L ∧ FunctionClass p Δ L f.1 f.2}

/-- Function-class membership uses exactly the earlier section's f.DpL assumption, together
with infinite smoothness, a lower bound and the initial objective gap. -/
theorem mem_functionClass_iff {n p : ℕ} (f : Space n → ℝ) (Δ L : ℝ) :
    (⟨n, f⟩ : Objective) ∈ functionClass p Δ L ↔
      1 ≤ p ∧ 0 < Δ ∧ ContDiff ℝ ∞ f ∧
      Section01.higherOrderLipschitz f p L ∧ BddBelow (Set.range f) ∧
      f 0 - sInf (Set.range f) ≤ Δ := by
  constructor
  · rintro ⟨hp, hΔ, hL, hf⟩
    exact ⟨hp, hΔ, hf.smooth, ⟨hf.smooth.of_le (by simp), hL, hf.lipschitz⟩,
      hf.bounded_below, hf.initial_gap⟩
  · rintro ⟨hp, hΔ, hsmooth, hL, hb, hgap⟩
    exact ⟨hp, hΔ, hL.constant_ge_one,
      ⟨hsmooth, hb, hgap, zero_le_one.trans hL.constant_ge_one, hL.bound⟩⟩

/-- Order-`p` zero chains: actual mixed derivative supports satisfy (4.2.4). -/
abbrev zeroChain {n : ℕ} (p : ℕ) (f : Space n → ℝ) := IsZeroChain p f

/-- Zero-respecting methods obey the full history rule (4.2.1) on every objective. -/
abbrev zeroRespectingMethod {p : ℕ} (M : derivativeOracleMethod p) := M.IsZeroRespecting

/-- The first gradient-tolerance attainment, with infinity for nontermination. -/
abbrev stoppingTime {p n : ℕ} (M : derivativeOracleMethod p) (f : Space n → ℝ)
    (ε : ℝ) := firstStationaryTime f (M.iterate f) ε

/-- Best worst-case complexity (4.2.2), over a class that can contain different dimensions. -/
abbrev oracleComplexity {p : ℕ} (methods : Set (derivativeOracleMethod p))
    (functions : Set Objective) (ε : ℝ) := minimax methods functions ε

/-- Tail-vanishing form of the zero-chain support rule, for every positive derivative order. -/
theorem zeroChain_mixedPartial_eq_zero {n p : ℕ} {f : Space n → ℝ}
    (hf : zeroChain p f) {k : ℕ} {x : Space n}
    (hx : ∀ i : Fin n, k ≤ i.val → x i = 0) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p)
    (v : Fin q → Fin n) {i : Fin n} (hi : k + 1 ≤ i.val) (hv : ∃ a, v a = i) :
    mixedPartial q f x v = 0 := hf.mixedPartial_eq_zero hx hq hqp v hi hv

/-- The rectangular rotation action is an actual objective pullback, with transformed mixed
basis vectors; it does not assert preservation of the fixed canonical support sets. -/
theorem rotated_mixedPartial {n m p : ℕ} {f : Space n → ℝ}
    (hf : zeroChain p f) {q : ℕ} (hq : q ≤ p)
    (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m) (v : Fin q → Fin m) :
    mixedPartial q (rotate U f) x v =
      iteratedFDeriv ℝ q f (U.toContinuousLinearMap.adjoint x)
        (fun a => U.toContinuousLinearMap.adjoint (EuclideanSpace.single (v a) 1)) :=
  mixedPartial_rotate hf.smooth hq U x v

/-- Lemma 4.2.1: input division by a nonzero scalar and arbitrary output scaling preserve
an order-`p` zero chain. The proof also handles zero output. -/
theorem lemma_4_2_1 {n p : ℕ} {f : Space n → ℝ} (hf : zeroChain p f)
    (μ₁ : ℝ) {μ₂ : ℝ} (_hμ₂ : μ₂ ≠ 0) :
    zeroChain p (fun x => μ₁ * f (μ₂⁻¹ • x)) := hf.rescale μ₁ μ₂⁻¹

/-- Lemma 4.2.2: the `k`th iterate of a zero-respecting method on a zero chain has zero
coordinates from the source's `k+1`st coordinate onwards. -/
theorem lemma_4_2_2 {n p : ℕ} {f : Space n → ℝ} (hf : zeroChain p f)
    (M : derivativeOracleMethod p) (hM : zeroRespectingMethod M) (k : ℕ)
    (i : Fin n) (hi : k ≤ i.val) : M.iterate f k i = 0 :=
  (coordinateSupport_subset_initial_iff (M.iterate f k) k).mp
    (hf.support_iterate (hM n f) k) i hi

/-- Lemma 4.2.3: a zero chain with a hidden last coordinate forces at least its dimension
iterations, both for its singleton class and for the full admissible function class. -/
theorem lemma_4_2_3 {n p : ℕ} {f : Space (n + 1) → ℝ} {Δ L ε : ℝ}
    (hf : zeroChain p f) (hclass : (⟨n + 1, f⟩ : Objective) ∈ functionClass p Δ L)
    (_hε : 0 < ε)
    (hhidden : ∀ x : Space (n + 1), x (Fin.last n) = 0 → ε < ‖gradient f x‖) :
    (n + 1 : ℕ∞) ≤ oracleComplexity (zeroRespectingMethods p) {⟨n + 1, f⟩} ε ∧
    oracleComplexity (zeroRespectingMethods p) {⟨n + 1, f⟩} ε ≤
      oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε := by
  constructor
  · exact hf.le_minimax (zeroRespectingMethods p) {⟨n + 1, f⟩} (by simp)
      (fun M hM => hM (n + 1) f) hhidden
  · exact minimax_mono_functions (zeroRespectingMethods p)
      (Set.singleton_subset_iff.mpr hclass) ε

/-- Theorem 4.2.4: unrestricted deterministic methods have at least the zero-respecting
minimax complexity. A singleton lower bound also transfers to the complete rectangular
rotation orbit in dimension `n + K`, which is contained in the admissible function class.
The method transformation is uniform before the objective; the rotation is chosen from its
actual finite oracle history. The conclusions hold for every tolerance, including positive
`epsilon₁` as required in the source. -/
theorem theorem_4_2_4 (p : ℕ) (Δ L ε : ℝ) :
    oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ≤
      oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε ∧
    ∀ n (f : Space n → ℝ), (⟨n, f⟩ : Objective) ∈ functionClass p Δ L →
      ∀ K : ℕ, (K : ℕ∞) ≤ oracleComplexity (zeroRespectingMethods p) {⟨n, f⟩} ε →
        oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (rotationOrbit f K) ε ≤
          oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε ∧
        (K : ℕ∞) ≤
          oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (rotationOrbit f K) ε := by
  have hrotate : ∀ {n m : ℕ} {f : Space n → ℝ},
      (⟨n, f⟩ : Objective) ∈ functionClass p Δ L →
      ∀ U : Space n →ₗᵢ[ℝ] Space m, (⟨m, rotate U f⟩ : Objective) ∈ functionClass p Δ L := by
    intro n m f hf U
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.rotate (lt_of_lt_of_le Nat.zero_lt_one hf.1) U⟩
  constructor
  · exact minimax_zeroRespecting_le_all (functionClass p Δ L)
      (fun f hf => hf.2.2.2.smooth.of_le (by simp)) hrotate ε
  · intro n f hf K hK
    constructor
    · apply minimax_mono_functions
      rintro g ⟨U, rfl⟩
      exact hrotate hf U
    · exact le_minimax_rotationOrbit (hf.2.2.2.smooth.of_le (by simp)) ε hK

/-- The coordinate form of clause (ii) of Lemma 4.2.5, including the earlier small
coordinate witnessing a gradient component with magnitude greater than one. -/
theorem difficultZeroChain_gradient_coordinate (n : ℕ) (x : Space (n + 1))
    (i : Fin (n + 1)) (hi : |x i| < 1) :
    ∃ j : Fin (n + 1), j ≤ i ∧ |x j| < 1 ∧
      |gradient (difficultZeroChain n) x j| ≤ ‖gradient (difficultZeroChain n) x‖ ∧
      1 < |gradient (difficultZeroChain n) x j| := by
  obtain ⟨j, hji, hj, hg⟩ :=
    Optimization.HardZeroChain.exists_gradient_chain_lt_neg_one_before n x i hi
  refine ⟨j, hji, hj, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient (difficultZeroChain n) x) j
  · rw [abs_of_neg (by linarith : gradient (difficultZeroChain n) x j < 0)]
    linarith

/-- Full Lemma 4.2.5 for the difficult chain with the retained primary-source seed
correction documented in `difficultZeroChain`: the seed is `-Psi(1) Phi(x₁)` as in
Carmon, Duchi, Hinder and Sidford, *Lower Bounds for Finding Stationary Points I*,
arXiv:1710.11606v3, equation (10), page 12. All four clauses hold simultaneously;
the constant precedes quantification over both derivative order and dimension. -/
theorem lemma_4_2_5 :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ n : ℕ,
      ContDiff ℝ ∞ (difficultZeroChain n) ∧
      (∀ p : ℕ, 1 ≤ p → zeroChain p (difficultZeroChain n)) ∧
      (∀ x : Space (n + 1), ∀ i : Fin (n + 1), |x i| < 1 →
        ∃ j : Fin (n + 1), j ≤ i ∧ |x j| < 1 ∧
          |gradient (difficultZeroChain n) x j| ≤ ‖gradient (difficultZeroChain n) x‖ ∧
          1 < |gradient (difficultZeroChain n) x j|) ∧
      (BddBelow (Set.range (difficultZeroChain n)) ∧
        difficultZeroChain n 0 - sInf (Set.range (difficultZeroChain n)) ≤ 12 * (n + 1 : ℝ)) ∧
      (∀ p : ℕ, 1 ≤ p → Section01.higherOrderLipschitz (difficultZeroChain n) p
        (Real.exp ((5 / 2 : ℝ) * p * Real.log p + c₁ * p))) := by
  obtain ⟨c, hc, hb⟩ := Optimization.HardZeroChain.uniform_chain_derivative_lipschitz
  refine ⟨c, (by linarith), fun n ↦ ⟨difficultZeroChain_smooth n,
    (fun p _ ↦ difficultZeroChain_isZeroChain n p),
    (fun x i hi ↦ difficultZeroChain_gradient_coordinate n x i hi),
    difficultZeroChain_gap n, fun p hp ↦ ?_⟩⟩
  refine ⟨(difficultZeroChain_smooth n).of_le (by simp), ?_, fun x y ↦ ?_⟩
  · apply Real.one_le_exp_iff.mpr
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hlog := Real.log_nonneg hpR
    positivity
  · exact (ContinuousMultilinearMap.diagonalNorm_le_norm _).trans (hb p hp n x y)

/-- The actual scaled objective (4.2.8), with `μ = (epsilon D_p/L)^(1/p)` and output
factor `epsilon * μ = μ^(p+1)L/D_p`. Here `D_p` is the dimension-uniform hard-chain
derivative budget, distinct from the requested class budget `L`. -/
abbrev scaledDifficultZeroChain (n p : ℕ) (L ε : ℝ) : Space (n + 1) → ℝ :=
  Optimization.HardZeroChain.scaledChain n p L ε

/-- The scaled hard chain is an actual member of the textbook class when its explicit
initial-gap bound fits. The objective is smooth and bounded below, with its actual infimum. -/
theorem scaledDifficultZeroChain_mem_functionClass (n : ℕ) {p : ℕ} (hp : 1 ≤ p)
    {Δ L ε : ℝ} (hΔ : 0 < Δ) (hL : 1 ≤ L) (hε : 0 < ε)
    (hgap : 12 * (n + 1 : ℝ) * ε * Optimization.HardZeroChain.inputScale p L ε ≤ Δ) :
    (⟨n + 1, scaledDifficultZeroChain n p L ε⟩ : Objective) ∈ functionClass p Δ L :=
  ⟨hp, hΔ, hL, Optimization.HardZeroChain.scaledChain_functionClass n hp
    (lt_of_lt_of_le zero_lt_one hL) hε hgap⟩

/-- The exact finite-dimensional witness behind the lower complexity bound. The orbit
lives in dimension `(n+1)+(n+1)` and has lower bound `n+1`; increasing the ambient dimension
does not double the iteration lower bound. -/
theorem scaledDifficultZeroChain_rotation_complexity (n : ℕ) {p : ℕ} (hp : 1 ≤ p)
    {Δ L ε : ℝ} (hΔ : 0 < Δ) (hL : 1 ≤ L) (hε : 0 < ε)
    (hgap : 12 * (n + 1 : ℝ) * ε * Optimization.HardZeroChain.inputScale p L ε ≤ Δ) :
    (n + 1 : ℕ∞) ≤ oracleComplexity (Set.univ : Set (derivativeOracleMethod p))
      (rotationOrbit (scaledDifficultZeroChain n p L ε) (n + 1)) ε ∧
    oracleComplexity (Set.univ : Set (derivativeOracleMethod p))
      (rotationOrbit (scaledDifficultZeroChain n p L ε) (n + 1)) ε ≤
        oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε := by
  have hm := scaledDifficultZeroChain_mem_functionClass n hp hΔ hL hε hgap
  have hz := Optimization.HardZeroChain.scaledChain_isZeroChain n p L ε
  have hg := Optimization.HardZeroChain.scaledChain_gradient n (p := p)
    (lt_of_lt_of_le zero_lt_one hL) hε
  have hsingle := (lemma_4_2_3 hz hm hε hg).1
  have ht := (theorem_4_2_4 p Δ L ε).2 (n + 1) _ hm (n + 1) hsingle
  exact ⟨ht.2, ht.1⟩

/-- With valid source parameters the textbook function class equals the reusable smooth
oracle class, so its actual scaling and minimax results apply without changing objectives. -/
theorem functionClass_eq_oracleFunctionClass {p : ℕ} (hp : 1 ≤ p) {Δ L : ℝ}
    (hΔ : 0 < Δ) (hL : 1 ≤ L) :
    functionClass p Δ L = Optimization.DerivativeOracle.functionClass p Δ L := by
  ext f
  simp only [functionClass, Optimization.DerivativeOracle.functionClass, Set.mem_ofPred_eq,
    hp, hΔ, hL, true_and]

/-- The lower-bound inequalities in (4.2.7), with the necessary finite floor retained for
all positive tolerances. `D_p` denotes the fixed hard-chain derivative budget. This proves
only the lower-bound part of Theorem 4.2.6; the ARp optimal-order conclusion is separate. -/
theorem theorem_4_2_6_lower_bound {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hΔ : 0 < Δ) (hL : 1 ≤ L) (hε : 0 < ε) :
    (⌊Δ / 12 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p))⌋₊ : ℕ∞) ≤
      oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ∧
    oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ≤
      oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε := by
  have heq := functionClass_eq_oracleFunctionClass hp hΔ hL
  rw [heq]
  rw [← Optimization.HardZeroChain.dimensionBudget_eq_order hp (lt_of_lt_of_le zero_lt_one hL) hε]
  exact Optimization.HardZeroChain.minimax_lower_bounds hp hΔ.le
    (lt_of_lt_of_le zero_lt_one hL) hε

/-- For sufficiently small tolerance, (4.2.7) has constant `c₀ = 1/24`. The precise
threshold is that the unrounded dimension budget is at least two. The ceiling expresses
the real-power lower rate in extended naturals, preserving infinite complexity. -/
theorem theorem_4_2_6_lower_order {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hΔ : 0 < Δ) (hL : 1 ≤ L) (hε : 0 < ε)
    (hsmall : 2 ≤ Δ / 12 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p))) :
    (⌈Δ / 24 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p))⌉₊ : ℕ∞) ≤
      oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ∧
    oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ≤
      oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε := by
  refine ⟨?_, (theorem_4_2_6_lower_bound hp hΔ hL hε).2⟩
  have hhalf := Optimization.HardZeroChain.ceil_half_dimensionBudget_le_minimax hp hΔ.le
    (lt_of_lt_of_le zero_lt_one hL) hε
  have heq := functionClass_eq_oracleFunctionClass hp hΔ hL
  rw [heq]
  rw [Optimization.HardZeroChain.dimensionBudget_eq_order hp
    (lt_of_lt_of_le zero_lt_one hL) hε] at hhalf
  have he : (Δ / 12 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p))) / 2 =
      Δ / 24 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p)) := by ring
  simpa only [he] using hhalf hsmall

open Optimization.HigherOrderRegularization Optimization.ParameterUpdates

/-- The matching ARp exponent follows from the actual first-order run theorem, with the
objective gap replaced by the class budget. This is a statement about legal algorithm
prefixes, including acceptance/update and model-residual laws; it does not assert existence
of a dimension-polymorphic oracle method implementing those prefixes. -/
theorem theorem_4_2_6_arp_run_upper_bound {n p : ℕ} {Δ L : ℝ}
    {f : Space n → ℝ} (hf : (⟨n, f⟩ : Objective) ∈ functionClass p Δ L)
    {params : RegularizationParameters} {theta epsilon : Fin 3 → ℝ}
    {x s : ℕ → Space n} {sigma : ℕ → ℝ} (hx : x 0 = 0)
    (hprefix : ∀ N, (∀ k < N, ¬Section01.arpStationary 1 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      Section01.arpPrefix params 1 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S (theta 0) *
      (Δ / (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, Section01.algorithm_4_1_1 params 1 p theta epsilon f x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  obtain ⟨hp, _, _, hL, hb, hgap⟩ := (mem_functionClass_iff f Δ L).mp hf
  obtain ⟨K, hK, hF, hD⟩ := Section01.theorem_4_1_5_first_order hL
    (fun y => csInf_le hb ⟨y, rfl⟩) hprefix
  have h0 := hprefix 0 (by simp)
  have hsigma := h0.toTrialPrefix.toRegularizationPrefix.pos (by omega : 0 ≤ 0)
  have hepsilon := h0.epsilon_pos 0 (by decide)
  have hS : 0 ≤ max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
    hsigma.le.trans (le_max_left _ _)
  have hA := firstOrderComplexityConstant_pos params p (zero_le_one.trans hL.constant_ge_one)
    hS (h0.theta_pos 0)
  have hQ := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (by simpa only [hx] using hgap)
      (Real.rpow_pos_of_pos hepsilon (((p + 1 : ℕ) : ℝ) / p)).le) hA.le
  have hC : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 := by
    have hlog := Real.log_pos params.one_lt_gamma2
    positivity
  dsimp only at hF hD ⊢
  rw [hx] at hF hD
  refine ⟨K, hK, hF.trans ?_, by linarith [hQ]⟩
  linarith [mul_le_mul_of_nonneg_left hQ hC]

/-- The actual raw-history ARp oracle method attains a uniform first-order budget on every
member of the textbook class, in every dimension. The method is fixed before the objective;
its queries include every rejected trial. -/
theorem theorem_4_2_6_arp_oracle_upper_bound {n p : ℕ} {Δ L ε : ℝ}
    {f : Space n → ℝ}
    (hf : (⟨n, f⟩ : Objective) ∈ functionClass p Δ L) (hε : 0 < ε) :
    firstStationaryTime f
      ((regularizationMethod
        (Optimization.DerivativeOracle.regularizationParameters L) p).iterate f)
      ε ≤ (⌈regularizationCost p Δ L ε⌉₊ : ℕ∞) := by
  let P := Optimization.DerivativeOracle.regularizationParameters L
  let x := fun i => (actualState (p := p) P f i).point
  let s := fun i => (actualState (p := p) P f i).step
  let sigma := fun i => (actualState (p := p) P f i).sigma
  obtain ⟨hp, _, _, hL, _, _⟩ := (mem_functionClass_iff f Δ L).mp hf
  obtain ⟨K, hK, hF, _⟩ := theorem_4_2_6_arp_run_upper_bound hf
    (params := P) (theta := fun _ => 1 / 2) (epsilon := fun _ => ε)
    (x := x) (s := s) (sigma := sigma) (by simp [x])
    (fun N hfirst => actualState_runPrefix P hp hL.smooth hε N hfirst)
  have htime := actualState_firstStationaryTime_le (p := p) P f hK.terminal.first
  have hcost : (functionEvaluations K : ℝ) ≤ regularizationCost p Δ L ε := by
    simpa only [sigma, actualState_zero, regularizationCost, P] using hF
  have hKreal : (K : ℝ) ≤ regularizationCost p Δ L ε :=
    (by simp [functionEvaluations] : (K : ℝ) ≤ (functionEvaluations K : ℝ)).trans hcost
  have hKN : K ≤ ⌈regularizationCost p Δ L ε⌉₊ := by
    exact_mod_cast hKreal.trans (Nat.le_ceil _)
  exact htime.trans (by exact_mod_cast hKN)

/-- The actual dimension-polymorphic ARp implementation gives the unrestricted minimax upper
bound; no existence or quality of algorithm prefixes is assumed. -/
theorem theorem_4_2_6_minimax_upper_bound {p : ℕ} {Δ L ε : ℝ} (hε : 0 < ε) :
    oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε ≤
      (⌈regularizationCost p Δ L ε⌉₊ : ℕ∞) := by
  apply iInf_le_of_le
    ⟨regularizationMethod
      (Optimization.DerivativeOracle.regularizationParameters L) p, Set.mem_univ _⟩
  apply iSup_le
  intro f
  exact theorem_4_2_6_arp_oracle_upper_bound f.property hε

/-- The constructed ARp method has the optimal real-power order, with strictly positive
leading coefficient depending only on `p` and a fixed positive additive overhead. -/
theorem theorem_4_2_6_arp_oracle_order_upper_bound {n p : ℕ} {Δ L ε : ℝ}
    {f : Space n → ℝ} (hf : (⟨n, f⟩ : Objective) ∈ functionClass p Δ L) (hε : 0 < ε) :
    firstStationaryTime f
      ((regularizationMethod
        (Optimization.DerivativeOracle.regularizationParameters L) p).iterate f) ε ≤
      (⌈regularizationRateConstant p *
        (Δ * L ^ ((p : ℝ)⁻¹) * ε ^ (-(((p + 1 : ℕ) : ℝ) / p))) +
          regularizationOverhead⌉₊ : ℕ∞) := by
  obtain ⟨hp, hΔ, _, hL, _, _⟩ := (mem_functionClass_iff f Δ L).mp hf
  exact (theorem_4_2_6_arp_oracle_upper_bound hf hε).trans
    (by exact_mod_cast Nat.ceil_mono (regularizationCost_le_order hp hΔ.le hL.constant_ge_one hε))

/-- Theorem 4.2.6: unrestricted deterministic order-p complexity has the hard-chain lower
order, and one actual ARp oracle method attains the matching upper order. The necessary
small-tolerance condition accounts for the integer chain length; the lower coefficient is
`1/24`. Both constants in the upper bound are fixed independently of dimension, gap,
Lipschitz budget and tolerance. Queries include unsuccessful trials. -/
theorem theorem_4_2_6 {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hΔ : 0 < Δ) (hL : 1 ≤ L) (hε : 0 < ε)
    (hsmall : 2 ≤ Δ / 12 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p))) :
    0 < regularizationRateConstant p ∧ 0 < regularizationOverhead ∧
    (⌈Δ / 24 * (L / Optimization.HardZeroChain.derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p))⌉₊ : ℕ∞) ≤
      oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ∧
    oracleComplexity (zeroRespectingMethods p) (functionClass p Δ L) ε ≤
      oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε ∧
    oracleComplexity (Set.univ : Set (derivativeOracleMethod p)) (functionClass p Δ L) ε ≤
      (⌈regularizationRateConstant p *
        (Δ * L ^ ((p : ℝ)⁻¹) * ε ^ (-(((p + 1 : ℕ) : ℝ) / p))) +
          regularizationOverhead⌉₊ : ℕ∞) ∧
    ∀ n (f : Space n → ℝ), (⟨n, f⟩ : Objective) ∈ functionClass p Δ L →
      firstStationaryTime f
        ((regularizationMethod
          (Optimization.DerivativeOracle.regularizationParameters L) p).iterate f) ε ≤
        (⌈regularizationRateConstant p *
          (Δ * L ^ ((p : ℝ)⁻¹) * ε ^ (-(((p + 1 : ℕ) : ℝ) / p))) +
            regularizationOverhead⌉₊ : ℕ∞) := by
  obtain ⟨hlower, hcompare⟩ := theorem_4_2_6_lower_order hp hΔ hL hε hsmall
  refine ⟨regularizationRateConstant_pos p, regularizationOverhead_pos,
    hlower, hcompare, ?_, fun _ _ hf => theorem_4_2_6_arp_oracle_order_upper_bound hf hε⟩
  exact (theorem_4_2_6_minimax_upper_bound hε).trans
    (by exact_mod_cast Nat.ceil_mono (regularizationCost_le_order hp hΔ.le hL hε))

end CartisGouldToint.Chapter04.Section02
