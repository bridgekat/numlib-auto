import Numlib.Optimization.HardZeroChainGradient
import Numlib.Optimization.HardZeroChainTensor
import Numlib.Optimization.OracleScaling
import Numlib.Optimization.OracleMinimax
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scaled hard chains and oracle minimax lower bounds

A fixed derivative-growth constant is independent of the oracle order and dimension.
Scaling the explicit smooth hard chain gives an admissible objective whose hidden coordinate
has gradient norm strictly above the requested tolerance. The initial-gap budget determines
an exact integer dimension. All bounds include the zero-dimension branch and take values
in extended naturals, so nontermination remains infinite.
-/

noncomputable section
open scoped ContDiff ENNReal

namespace Optimization.HardZeroChain
open ZeroChains DerivativeOracle

/-- A fixed constant in the dimension-uniform derivative growth estimate. -/
def smoothnessConstant : ℝ := Classical.choose uniform_chain_derivative_lipschitz

/-- The fixed derivative-growth constant is at least one. -/
theorem one_le_smoothnessConstant : 1 ≤ smoothnessConstant :=
  (Classical.choose_spec uniform_chain_derivative_lipschitz).1

/-- The common derivative Lipschitz budget for order `p`, independent of dimension. -/
def derivativeBudget (p : ℕ) : ℝ :=
  Real.exp ((5 / 2 : ℝ) * p * Real.log p + smoothnessConstant * p)

/-- The common derivative budget is strictly positive. -/
theorem derivativeBudget_pos (p : ℕ) : 0 < derivativeBudget p := Real.exp_pos _

/-- The explicit chain has the common full-tensor derivative Lipschitz budget. -/
theorem chain_derivative_lipschitz (p : ℕ) (hp : 1 ≤ p) (n : ℕ)
    (x y : Space (n + 1)) :
    ‖iteratedFDeriv ℝ p (chain n) x - iteratedFDeriv ℝ p (chain n) y‖ ≤
      derivativeBudget p * ‖x - y‖ :=
  (Classical.choose_spec uniform_chain_derivative_lipschitz).2 p hp n x y

/-- Input length scale making the scaled hard chain's gradient threshold equal to epsilon. -/
def inputScale (p : ℕ) (L ε : ℝ) : ℝ :=
  (ε * derivativeBudget p / L) ^ ((p : ℝ)⁻¹)

/-- Positive tolerance and Lipschitz budget give a positive input scale. -/
theorem inputScale_pos (p : ℕ) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    0 < inputScale p L ε :=
  Real.rpow_pos_of_pos (div_pos (mul_pos hε (derivativeBudget_pos p)) hL) _

/-- The `p`th power of the positive input scale is its defining ratio. -/
theorem inputScale_pow {p : ℕ} (hp : 1 ≤ p) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    inputScale p L ε ^ p = ε * derivativeBudget p / L := by
  exact Real.rpow_inv_natCast_pow
    (div_pos (mul_pos hε (derivativeBudget_pos p)) hL).le (by omega)

/-- The scaled objective is an actual scalar rescaling of the smooth difficult chain. -/
def scaledChain (n p : ℕ) (L ε : ℝ) : Space (n + 1) → ℝ :=
  rescale (ε * inputScale p L ε) (inputScale p L ε)⁻¹ (chain n)

/-- The scaled objective has the source's exact output factor and inverse-input formula. -/
theorem scaledChain_eq_source (n : ℕ) {p : ℕ} (hp : 1 ≤ p) {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (x : Space (n + 1)) :
    scaledChain n p L ε x =
      (inputScale p L ε ^ (p + 1) * L / derivativeBudget p) *
        chain n ((inputScale p L ε)⁻¹ • x) := by
  have hD := derivativeBudget_pos p
  have he : ε * inputScale p L ε = inputScale p L ε ^ (p + 1) * L / derivativeBudget p := by
    rw [pow_succ, inputScale_pow hp hL hε]
    field_simp
  simp only [scaledChain, rescale, he]

/-- The scaled chain's highest-derivative Lipschitz budget is exactly the prescribed one. -/
theorem scaledChain_lipschitz_budget {p : ℕ} (hp : 1 ≤ p) {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    (ε * inputScale p L ε) * (inputScale p L ε)⁻¹ ^ (p + 1) * derivativeBudget p = L := by
  have hμ := inputScale_pos p hL hε
  have hpow := inputScale_pow hp hL hε
  rw [pow_succ, inv_pow]
  field_simp
  nlinarith [(eq_div_iff hL.ne').mp hpow]

/-- The scaled chain belongs to the actual smooth function class whenever its explicit
initial-gap budget fits. -/
theorem scaledChain_functionClass (n : ℕ) {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε)
    (hgap : 12 * (n + 1 : ℝ) * ε * inputScale p L ε ≤ Δ) :
    FunctionClass p Δ L (n + 1) (scaledChain n p L ε) := by
  have hf : FunctionClass p (12 * (n + 1 : ℝ)) (derivativeBudget p) (n + 1) (chain n) :=
    ⟨contDiff_chain n, bddBelow_chain n, chain_initial_gap n,
      (derivativeBudget_pos p).le, fun x y =>
        (ContinuousMultilinearMap.diagonalNorm_le_norm _).trans
          (chain_derivative_lipschitz p hp n x y)⟩
  have hs := hf.rescale (mul_pos hε (inputScale_pos p hL hε))
    (inv_pos.mpr (inputScale_pos p hL hε))
  rw [scaledChain_lipschitz_budget hp hL hε] at hs
  exact ⟨hs.smooth, hs.bounded_below,
    hs.initial_gap.trans (by nlinarith [hgap]), hs.lipschitz_nonneg, hs.lipschitz⟩

/-- Every scaled hard chain remains a zero chain for its full oracle order. -/
theorem scaledChain_isZeroChain (n p : ℕ) (L ε : ℝ) :
    IsZeroChain p (scaledChain n p L ε) :=
  (isZeroChain n p).rescale _ _

/-- A hidden final coordinate forces the actual scaled gradient strictly above tolerance. -/
theorem scaledChain_gradient (n : ℕ) {p : ℕ} {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (x : Space (n + 1)) (hx : x (Fin.last n) = 0) :
    ε < ‖gradient (scaledChain n p L ε) x‖ := by
  have hμ := inputScale_pos p hL hε
  have hsmall : |((inputScale p L ε)⁻¹ • x) (Fin.last n)| < 1 := by
    simp [hx]
  have hg := one_lt_norm_gradient_chain n ((inputScale p L ε)⁻¹ • x)
    ⟨Fin.last n, hsmall⟩
  have hs : ContDiff ℝ 1 (chain n) := (contDiff_chain n).of_le (by simp)
  change ε < ‖gradient (rescale _ _ (chain n)) x‖
  rw [gradient_rescale hs, mul_inv_cancel_right₀ hμ.ne', norm_smul,
    Real.norm_eq_abs, abs_of_pos hε]
  nlinarith

/-- Each positive integer dimension fitting the gap budget is a zero-respecting minimax
lower bound, using the actual scaled objective as a witness. -/
theorem dimension_le_minimax (n : ℕ) {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε)
    (hgap : 12 * (n + 1 : ℝ) * ε * inputScale p L ε ≤ Δ) :
    (n + 1 : ℕ∞) ≤ minimax (zeroRespectingMethods p) (DerivativeOracle.functionClass p Δ L) ε := by
  exact (scaledChain_isZeroChain n p L ε).le_minimax
    (zeroRespectingMethods p) (DerivativeOracle.functionClass p Δ L)
    (scaledChain_functionClass n hp hL hε hgap)
    (fun M hM => hM (n + 1) _) (scaledChain_gradient n hL hε)

/-- The exact number of hard-chain coordinates allowed by the initial-gap budget. -/
def dimensionBudget (p : ℕ) (Δ L ε : ℝ) : ℝ :=
  Δ / (12 * ε * inputScale p L ε)

/-- The floor of the dimension budget is a minimax lower bound at every positive tolerance;
a budget below one gives the correct trivial zero bound. -/
theorem floor_dimensionBudget_le_minimax {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hΔ : 0 ≤ Δ) (hL : 0 < L) (hε : 0 < ε) :
    (⌊dimensionBudget p Δ L ε⌋₊ : ℕ∞) ≤
      minimax (zeroRespectingMethods p) (DerivativeOracle.functionClass p Δ L) ε := by
  have hμ := inputScale_pos p hL hε
  have hB : 0 ≤ dimensionBudget p Δ L ε := by unfold dimensionBudget; positivity
  have hfloor := Nat.floor_le hB
  cases hd : ⌊dimensionBudget p Δ L ε⌋₊ with
  | zero => simp
  | succ n =>
    apply dimension_le_minimax n hp hL hε
    rw [hd] at hfloor
    dsimp only [dimensionBudget] at hfloor
    have h := (le_div_iff₀ (show 0 < 12 * ε * inputScale p L ε by positivity)).mp hfloor
    push_cast at h
    nlinarith [h]

/-- The dimension budget has the familiar inverse-tolerance order, with the hard chain's
fixed smoothness normalization separated from the requested class constant. -/
theorem dimensionBudget_eq_order {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    dimensionBudget p Δ L ε = Δ / 12 *
      (L / derivativeBudget p) ^ ((p : ℝ)⁻¹) *
      ε ^ (-(((p + 1 : ℕ) : ℝ) / p)) := by
  have hD := derivativeBudget_pos p
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have he : ((p + 1 : ℕ) : ℝ) / p = 1 + (p : ℝ)⁻¹ := by
    push_cast
    field_simp
  rw [he, Real.rpow_neg hε.le, Real.rpow_add hε, Real.rpow_one]
  unfold dimensionBudget inputScale
  rw [Real.div_rpow (mul_pos hε hD).le hL.le,
    Real.mul_rpow hε.le hD.le, Real.div_rpow hL.le hD.le]
  have hεr := Real.rpow_pos_of_pos hε ((p : ℝ)⁻¹)
  have hLr := Real.rpow_pos_of_pos hL ((p : ℝ)⁻¹)
  have hDr := Real.rpow_pos_of_pos hD ((p : ℝ)⁻¹)
  field_simp

/-- Once the dimension budget is at least two, rounding costs at most a factor of two.
The ceiling embeds the real lower rate faithfully into extended-natural complexity. -/
theorem ceil_half_dimensionBudget_le_minimax {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hΔ : 0 ≤ Δ) (hL : 0 < L) (hε : 0 < ε)
    (hsmall : 2 ≤ dimensionBudget p Δ L ε) :
    (⌈dimensionBudget p Δ L ε / 2⌉₊ : ℕ∞) ≤
      minimax (zeroRespectingMethods p) (DerivativeOracle.functionClass p Δ L) ε := by
  have hfloor := Nat.lt_floor_add_one (dimensionBudget p Δ L ε)
  have hhalf : ⌈dimensionBudget p Δ L ε / 2⌉₊ ≤ ⌊dimensionBudget p Δ L ε⌋₊ :=
    Nat.ceil_le.mpr (by linarith)
  exact (by exact_mod_cast hhalf : (⌈dimensionBudget p Δ L ε / 2⌉₊ : ℕ∞) ≤
    (⌊dimensionBudget p Δ L ε⌋₊ : ℕ∞)).trans
      (floor_dimensionBudget_le_minimax hp hΔ hL hε)

/-- The rounded hard-chain lower bound transfers to all deterministic oracle methods.
The comparison uses a uniform raw-history method transformation before the objective. -/
theorem minimax_lower_bounds {p : ℕ} (hp : 1 ≤ p) {Δ L ε : ℝ}
    (hΔ : 0 ≤ Δ) (hL : 0 < L) (hε : 0 < ε) :
    (⌊dimensionBudget p Δ L ε⌋₊ : ℕ∞) ≤
      minimax (zeroRespectingMethods p) (DerivativeOracle.functionClass p Δ L) ε ∧
    minimax (zeroRespectingMethods p) (DerivativeOracle.functionClass p Δ L) ε ≤
      minimax (Set.univ : Set (Method p)) (DerivativeOracle.functionClass p Δ L) ε := by
  refine ⟨floor_dimensionBudget_le_minimax hp hΔ hL hε, ?_⟩
  exact minimax_zeroRespecting_le_all (DerivativeOracle.functionClass p Δ L)
    (fun f hf => hf.smooth.of_le (by simp))
    (fun hf U => hf.rotate (by omega) U) ε

end Optimization.HardZeroChain
