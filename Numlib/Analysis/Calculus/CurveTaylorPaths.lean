import Numlib.Analysis.Calculus.CurveTaylorExpansion
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Taylor coefficients on paths with a prescribed asymptotic jet

A path need not be differentiable: it suffices to equal its finite polynomial jet up to a
little-o remainder. Strict differentiability transports this remainder through a smooth
objective. Local minima on a constraint set then give the usual coefficient sign along
actual eventually feasible paths.
-/

noncomputable section
open Filter Asymptotics Set
open scoped Topology
namespace CurveTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A one-sided path agrees with the polynomial specified by its finite jet to little-o order. -/
def HasCurveJet (x : E) (j : ℕ) (s : ℕ → E) (gamma : ℝ → E) : Prop :=
  (fun t => gamma t - (x + displacement j s t)) =o[𝓝[>] 0] (fun t : ℝ => t ^ j)

/-- A realizable jet has an actual asymptotic path lying eventually in the given set. -/
def RealizableJet (S : Set E) (x : E) (j : ℕ) (s : ℕ → E) : Prop :=
  ∃ gamma, HasCurveJet x j s gamma ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma t ∈ S

/-- The path-jet condition is precisely its little-o error condition. -/
@[simp] theorem hasCurveJet_iff (x : E) (j : ℕ) (s : ℕ → E) (gamma : ℝ → E) :
    HasCurveJet x j s gamma ↔
      (fun t => gamma t - (x + displacement j s t)) =o[𝓝[>] 0] (fun t : ℝ => t ^ j) := Iff.rfl

/-- Realizability exposes the actual path and its eventual feasibility. -/
@[simp] theorem realizableJet_iff (S : Set E) (x : E) (j : ℕ) (s : ℕ → E) :
    RealizableJet S x j s ↔
      ∃ gamma, HasCurveJet x j s gamma ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma t ∈ S := Iff.rfl

/-- An exact polynomial path has its defining asymptotic jet. -/
theorem hasCurveJet_polynomial (x : E) (j : ℕ) (s : ℕ → E) :
    HasCurveJet x j s (fun t => x + displacement j s t) := by
  simp only [HasCurveJet, sub_self]
  exact isLittleO_zero _ _

/-- Eventual inclusion of the exact polynomial path suffices for realizability. -/
theorem realizableJet_of_polynomial {S : Set E} (x : E) (j : ℕ) (s : ℕ → E)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + displacement j s t ∈ S) :
    RealizableJet S x j s := ⟨_, hasCurveJet_polynomial x j s, h⟩

/-- Enlarging the feasible set preserves an actual realizing path. -/
theorem RealizableJet.mono {S T : Set E} {x : E} {j : ℕ} {s : ℕ → E}
    (h : RealizableJet S x j s) (hST : S ⊆ T) : RealizableJet T x j s := by
  obtain ⟨gamma, hg, hS⟩ := h
  exact ⟨gamma, hg, hS.mono fun _ ht => hST ht⟩

/-- Every path with a positive-order asymptotic jet converges to the base point. -/
theorem HasCurveJet.tendsto {x : E} {j : ℕ} {s : ℕ → E} {gamma : ℝ → E}
    (h : HasCurveJet x j s gamma) (hj : 1 ≤ j) :
    Tendsto gamma (𝓝[>] 0) (𝓝 x) := by
  have ht : Tendsto (fun t : ℝ => t ^ j) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Pi.pow_def, id_eq, zero_pow (by omega : j ≠ 0)] using
      ((continuous_id.pow j).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have he := h.trans_tendsto ht
  have hp : Tendsto (fun t => x + displacement j s t) (𝓝[>] 0) (𝓝 x) := by
    simpa only [displacement_zero, add_zero] using
      (((continuous_displacement j s).tendsto 0).mono_left nhdsWithin_le_nhds).const_add x
  simpa only [sub_add_cancel, zero_add] using he.add hp

/-- A smooth objective carries the little-o path error to a little-o objective error. -/
theorem HasCurveJet.objective_error {x : E} {j : ℕ} {s : ℕ → E} {gamma : ℝ → E}
    (h : HasCurveJet x j s gamma) (hj : 1 ≤ j) {f : E → ℝ}
    (hf : ContDiffAt ℝ j f x) :
    (fun t => f (gamma t) - f (x + displacement j s t)) =o[𝓝[>] 0]
      (fun t : ℝ => t ^ j) := by
  have hp : Tendsto (fun t => x + displacement j s t) (𝓝[>] 0) (𝓝 x) := by
    simpa only [displacement_zero, add_zero] using
      (((continuous_displacement j s).tendsto 0).mono_left nhdsWithin_le_nhds).const_add x
  have hd := hf.hasStrictFDerivAt (by exact_mod_cast (by omega : j ≠ 0))
  exact (hd.isBigO_sub.comp_tendsto ((h.tendsto hj).prodMk_nhds hp)).trans_isLittleO h

/-- The first potentially nonzero coefficient controls the objective along any realizing path. -/
theorem HasCurveJet.tendsto_objective_div_pow {x : E} {j : ℕ} {s : ℕ → E}
    {gamma : ℝ → E} (h : HasCurveJet x j s gamma) (hj : 1 ≤ j)
    {f : E → ℝ} (hf : ContDiffAt ℝ j f x)
    (hs : ∀ d, 1 ≤ d → d < j → coefficient f x d s = 0) :
    Tendsto (fun t : ℝ => (f (gamma t) - f x) / t ^ j) (𝓝[>] 0)
      (𝓝 (coefficient f x j s)) := by
  have he := (h.objective_error hj hf).tendsto_div_nhds_zero
  have hp := tendsto_objective_displacement_div_pow hj hf s hs
  convert he.add hp using 1
  · ext t
    ring
  · simp

/-- A local constrained minimum forces nonnegativity along an actual feasible path. -/
theorem RealizableJet.coefficient_nonneg {S : Set E} {x : E} {j : ℕ} {s : ℕ → E}
    (h : RealizableJet S x j s) (hj : 1 ≤ j) {f : E → ℝ}
    (hf : ContDiffAt ℝ j f x) (hmin : IsLocalMinOn f S x)
    (hs : ∀ d, 1 ≤ d → d < j → coefficient f x d s = 0) :
    0 ≤ coefficient f x j s := by
  obtain ⟨gamma, hg, hS⟩ := h
  apply ge_of_tendsto (hg.tendsto_objective_div_pow hj hf hs)
  have ht : Tendsto gamma (𝓝[>] 0) (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hg.tendsto hj, hS⟩
  filter_upwards [ht.eventually hmin, self_mem_nhdsWithin] with t hm ht0
  exact div_nonneg (sub_nonneg.mpr hm) (pow_nonneg (le_of_lt ht0) j)

/-- The vector-valued Taylor coefficient uses the same ordered positive compositions. -/
def vectorCoefficient {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (j : ℕ) (s : ℕ → E) : F :=
  ∑ k ∈ Finset.Icc 1 j, (k.factorial : ℝ)⁻¹ •
    ∑ l ∈ compositionIndices j k, iteratedFDeriv ℝ k f x (fun i => s (l i))

/-- The vector-valued coefficient agrees exactly with the established scalar coefficient. -/
@[simp] theorem vectorCoefficient_real (f : E → ℝ) (x : E) (j : ℕ) (s : ℕ → E) :
    vectorCoefficient f x j s = coefficient f x j s := by
  simp only [vectorCoefficient, coefficient, smul_eq_mul]

/-- There is no constant displacement coefficient for vector-valued functions either. -/
@[simp] theorem vectorCoefficient_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (s : ℕ → E) : vectorCoefficient f x 0 s = 0 := by
  simp [vectorCoefficient]

/-- Vector coefficients depend only on the active finite jet. -/
theorem vectorCoefficient_congr_jet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (j : ℕ) {s t : ℕ → E}
    (h : ∀ i, 1 ≤ i → i ≤ j → s i = t i) :
    vectorCoefficient f x j s = vectorCoefficient f x j t := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  funext i
  exact h _ ((mem_compositionIndices.mp hl).1 i) (by omega)

end CurveTaylor
