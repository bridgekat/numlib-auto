import Numlib.Optimization.InnerInspectionCertificates
import Numlib.Optimization.CompositeInnerExistence

/-!
# Certificates at returned composite inner states

Passing a generalized test retains its actual direction. Later halving only changes the
currently inspected radius, so every earlier passing certificate remains valid. Thus the
returned execution carries all actual witnesses required by the source model-step condition.
-/

noncomputable section
open scoped Nat
namespace Optimization.CompositeRegularization
open CompositeTaylorModels
open HigherOrderApproximateRegularization (Parameters InnerState InnerInitial InnerPhase)
open HigherOrderApproximateRegularization
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def certificate (P : Parameters) (g : E → ℝ) (v : E → F) (h : F → ℝ)
    (i : ℕ) (s : E) (δ : ℝ) : Prop :=
  ∃ d : E, GapWitness g v h i s δ P.fraction d ∧
    decrement g v h i s d ≤ P.fraction * P.theta * P.epsilon i * δ ^ i / (i ! : ℝ)

private abbrev passedOrders (P : Parameters) (g : E → ℝ) (v : E → F) (h : F → ℝ) :=
  HigherOrderApproximateRegularization.InnerCertificates.PassedOrders (certificate P g v h)

private abbrev epochInvariant (P : Parameters) (g : E → ℝ) (v : E → F) (h : F → ℝ) :=
  HigherOrderApproximateRegularization.InnerCertificates.EpochInvariant P.q (certificate P g v h)

private theorem epoch_pass {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {long : InnerState E → Prop} {a : InnerState E} {j : ℕ}
    (ha : passedOrders P g v h a j) (d : E)
    (hw : GapWitness g v h j a.step (a.radii j) P.fraction d)
    (htest : decrement g v h j a.step d ≤
      P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
    epochInvariant P g v h long
      ⟨a.mu, a.radii, a.step, if j = P.q then .returned else .inspect (j + 1)⟩ :=
  HigherOrderApproximateRegularization.InnerCertificates.pass ha ⟨d, hw, htest⟩

private theorem epoch_halve {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {a : InnerState E} {j : ℕ} (ha : passedOrders P g v h a j) :
    passedOrders P g v h
      ⟨a.mu, Function.update a.radii j (a.radii j / 2), a.step, .inspect j⟩ j :=
  HigherOrderApproximateRegularization.InnerCertificates.halve ha

private theorem epoch_of_ne_minimize {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {long : InnerState E → Prop}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ Set.univ h}
    {z : E} {a b : InnerState E} (ht : InnerTransition P g v h convex hconv z a b)
    (hne : a.phase ≠ .minimize) (ha : epochInvariant P g v h long a) :
    epochInvariant P g v h long b := by
  cases ht with
  | minimize hphase s hfrac => exact (hne hphase).elim
  | pass j hphase hj hjq d hw htest =>
    apply epoch_pass (d := d) (hw := hw) (htest := htest)
    simpa only [epochInvariant, InnerCertificates.EpochInvariant, hphase] using ha
  | halve j hphase hj hjq hbranch d hw hfail hsmall =>
    apply epoch_halve
    simpa only [epochInvariant, InnerCertificates.EpochInvariant, hphase] using ha
  | improve => trivial

private theorem epoch_raw {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ Set.univ h} {z : E} {a b : InnerState E}
    (ht : InnerTransition P g v h convex hconv z a b)
    (ha : epochInvariant P g v h (fun a => 1 ≤ ‖a.step‖) a) :
    epochInvariant P g v h (fun a => 1 ≤ ‖a.step‖) b := by
  by_cases hphase : a.phase = .minimize
  · cases ht with
    | minimize hp s hfrac =>
      by_cases hs : 1 ≤ ‖s‖
      · simp only [hs, ite_true, epochInvariant, InnerCertificates.EpochInvariant]
        exact Or.inl trivial
      · simp only [ite_eq_right hs, epochInvariant, InnerCertificates.EpochInvariant,
          InnerCertificates.PassedOrders]
        intro i hi hij
        omega
    | pass => simp_all
    | halve => simp_all
    | improve => trivial
  · exact epoch_of_ne_minimize ht hphase ha

/-- A raw returned state is either on the source's weak norm boundary or has actual witnesses
passing every model Taylor-gap test at its final point and radii. -/
theorem InnerExecution.return_quality {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ Set.univ h} {z : E} {N : ℕ}
    (run : InnerExecution P g v h convex hconv z N) (hreturn : (run.state N).phase = .returned) :
    1 ≤ ‖(run.state N).step‖ ∨ ∀ j, 1 ≤ j → j ≤ P.q → ∃ d : E,
      GapWitness g v h j (run.state N).step ((run.state N).radii j) P.fraction d ∧
      decrement g v h j (run.state N).step d ≤
        P.fraction * P.theta * P.epsilon j * (run.state N).radii j ^ j / (j ! : ℝ) := by
  have hi : ∀ k, k ≤ N → epochInvariant P g v h (fun a => 1 ≤ ‖a.step‖) (run.state k) := by
    intro k hk
    induction k with
    | zero => simp only [epochInvariant, InnerCertificates.EpochInvariant, run.initial.2.2.2]
    | succ k ih => exact epoch_raw (run.transition k (by omega)) (ih (by omega))
  have hf := hi N le_rfl
  simp only [epochInvariant, InnerCertificates.EpochInvariant, hreturn,
    InnerCertificates.PassedOrders, certificate] at hf
  exact hf.imp_right (fun hp j hj hjq => hp j hj (by omega))


end Optimization.CompositeRegularization
