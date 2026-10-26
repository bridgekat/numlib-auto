import Numlib.Optimization.HighOrder.CurveOptimality
import Numlib.Optimization.Constrained.LagrangianStability

/-!
# Necessary conditions from realized equality-feasible curve jets

Actual finite curve derivatives determine the composition coefficients. A local
minimum on the true equality feasible set therefore gives the necessary
Lagrangian coefficient inequalities for every multiplier. The geometric
qualification requires realization of each admissible jet, rather than the
source's insufficient existence of some nonzero formal jet.
-/

open Filter Set Topology

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual finite curve jets determine every composition derivative through that order. -/
theorem iteratedDeriv_comp_eq_of_curve_jets {q n : ℕ} (hn : n ≤ q)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ q f x)
    {γ η : ℝ → E} (hγ : ContDiffAt ℝ q γ 0) (hη : ContDiffAt ℝ q η 0)
    (hγ0 : γ 0 = x) (hη0 : η 0 = x)
    (hjets : ∀ i, 1 ≤ i → i ≤ q → iteratedDeriv i γ 0 = iteratedDeriv i η 0) :
    iteratedDeriv n (f ∘ γ) 0 = iteratedDeriv n (f ∘ η) 0 := by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hγ0 ▸ hf) hγ
    (by exact_mod_cast hn),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hη0 ▸ hf) hη
    (by exact_mod_cast hn)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hγ0, hη0]
  congr 1
  funext j
  apply hjets
  · exact c.partSize_pos j
  · exact (c.partSize_le j).trans hn
end TaylorModel

namespace Constrained
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite jet realized by an actual smooth curve eventually feasible to the right.
The jet matches the actual derivatives of its polynomial representative. -/
structure FeasibleCurveJet (X : Set E) (x : E) (s : ℕ → E) (j : ℕ) : Prop where
  realized : ∃ γ : ℝ → E, ContDiffAt ℝ j γ 0 ∧ γ 0 = x ∧
    (∀ i, 1 ≤ i → i ≤ j →
      iteratedDeriv i γ 0 = iteratedDeriv i (fun t => x + polynomialCurve s j t) 0) ∧
    ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ X

/-- At an actual constrained local minimum, the first nonvanishing coefficient along
a realized feasible curve is nonnegative. -/
theorem curveCoefficient_nonneg_of_feasibleJet {X : Set E} {f : E → ℝ}
    {x : E} {s : ℕ → E} {j : ℕ} (hj : 0 < j)
    (hf : ContDiffAt ℝ j f x) (hmin : IsLocalMinOn f X x)
    (hjet : FeasibleCurveJet X x s j)
    (hzero : ∀ i, 0 < i → i < j → curveCoefficient f x s i = 0) :
    0 ≤ curveCoefficient f x s j := by
  obtain ⟨γ, hγ, hγ0, hγjet, hγX⟩ := hjet.realized
  let η : ℝ → E := fun t => x + polynomialCurve s j t
  have hη : ContDiffAt ℝ j η 0 :=
    (contDiff_const.add (polynomialCurve_contDiff s j)).contDiffAt
  have hη0 : η 0 = x := by simp [η, polynomialCurve_zero]
  have hcompose : ∀ i, i ≤ j → iteratedDeriv i (f ∘ γ) 0 =
      (i.factorial : ℝ) * curveCoefficient f x s i := by
    intro i hi
    rw [TaylorModel.iteratedDeriv_comp_eq_of_curve_jets hi hf hγ hη hγ0 hη0 hγjet]
    exact iteratedDeriv_polynomialCurve hi hf s
  have he : Filter.Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[X] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa [hγ0] using hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      hγX⟩
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), (f ∘ γ) 0 ≤ (f ∘ γ) t := by
    simpa only [Function.comp_apply, hγ0] using he.eventually hmin
  have hD := ScalarOptimality.iteratedDeriv_nonneg_of_right_min hj
    ((show ContDiffAt ℝ j f (γ 0) by simpa only [hγ0] using hf).comp 0 hγ)
    hright (fun i hi hij => by rw [hcompose i hij.le, hzero i hi hij, mul_zero])
  rw [hcompose j le_rfl] at hD
  exact nonneg_of_mul_nonneg_right hD (by positivity : (0 : ℝ) < j.factorial)

end Constrained

namespace Constrained
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every formally equality-feasible jet already realized in the simple feasible set
can be realized in the actual equality-feasible set with the same finite derivatives. -/
def EqualityJetRealizable {m : ℕ} (X : Set E) (c : E → EuclideanSpace ℝ (Fin m)) (x : E)
    (q : ℕ) : Prop :=
  ∀ j, 0 < j → j ≤ q → ∀ s : ℕ → E, FeasibleCurveJet X x s j →
    (∀ a i, 0 < i → i ≤ j → curveCoefficient (fun z => c z a) x s i = 0) →
    FeasibleCurveJet (X ∩ {z | c z = 0}) x s j

/-- Zero equality constraints satisfy jet realizability for every feasible set and order. -/
theorem equalityJetRealizable_zero (X : Set E) (x : E) (q m : ℕ) :
    EqualityJetRealizable X (fun _ => (0 : EuclideanSpace ℝ (Fin m))) x q := by
  intro j hj hjq s hs _
  simpa only [Set.ofPred_true, inter_univ] using hs

/-- Equality-jet realizability gives all curve-based necessary Lagrangian conditions
for every multiplier, with the actual ordered-composition coefficients. -/
theorem curve_lagrangian_nonneg_of_realizable {m q j : ℕ}
    {X : Set E} {f : E → ℝ} {c : E → EuclideanSpace ℝ (Fin m)} {x : E}
    (hf : ContDiffAt ℝ q f x) (hc : ContDiffAt ℝ q c x)
    (hmin : IsLocalMinOn f (X ∩ {z | c z = 0}) x) (hcx : c x = 0)
    (hqual : EqualityJetRealizable X c x q)
    (y : EuclideanSpace ℝ (Fin m)) (hj : 0 < j) (hjq : j ≤ q) (s : ℕ → E)
    (hs : FeasibleCurveJet X x s j)
    (hconstraint : ∀ a i, 0 < i → i ≤ j → curveCoefficient (fun z => c z a) x s i = 0)
    (hzero : ∀ i, 0 < i → i < j →
      curveCoefficient (vectorLagrangian f c y) x s i = 0) :
    0 ≤ curveCoefficient (vectorLagrangian f c y) x s j := by
  have hfeas := hqual j hj hjq s hs hconstraint
  have hL : IsLocalMinOn (vectorLagrangian f c y) (X ∩ {z | c z = 0}) x := by
    have hlocal : ∀ᶠ z in 𝓝[X ∩ {z | c z = 0}] x,
        vectorLagrangian f c y x ≤ vectorLagrangian f c y z := by
      filter_upwards [hmin, self_mem_nhdsWithin] with z hz hzmem
      have hcz : c z = 0 := hzmem.2
      simpa only [vectorLagrangian, hcx, hcz, inner_zero_right, sub_zero] using hz
    exact hlocal
  have hLs : ContDiffAt ℝ j (vectorLagrangian f c y) x :=
    (hf.sub ((innerSL ℝ y).contDiff.contDiffAt.comp x hc)).of_le (by exact_mod_cast hjq)
  exact curveCoefficient_nonneg_of_feasibleJet hj hLs hL hfeas hzero

end Constrained
