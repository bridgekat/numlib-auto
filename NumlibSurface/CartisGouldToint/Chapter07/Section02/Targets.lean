import NumlibSurface.CartisGouldToint.Chapter07.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import Numlib.Optimization.TargetLeastSquares
import Numlib.Optimization.ComponentSmoothness

/-!
# Chapter 7, Section 2: residuals and varying targets

The target residual has the Euclidean sum norm. Pointwise smoothness of its squared norm
gives uniform derivative control on a bounded target interval through an explicit affine
identity, rather than an inference from pointwise parameter continuity. Componentwise
sufficient conditions use actual positive jets bounded on the convex constraint set and a
common open smooth extension. Polynomial closure covers every positive even residual exponent.
-/

noncomputable section
namespace CartisGouldToint.Chapter07.Section02
open Optimization.ConstrainedRegularization
variable {n m : ℕ}

/-- The augmented Euclidean residual (7.2.4), with the objective residual last. -/
def targetResidual (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => c x i) (f x - t))

/-- The augmented residual retains every constraint component. -/
@[simp] theorem targetResidual_castSucc (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    targetResidual f c t x i.castSucc = c x i := by simp [targetResidual]

/-- The final component is the objective minus the target. -/
@[simp] theorem targetResidual_last (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    targetResidual f c t x (Fin.last m) = f x - t := by simp [targetResidual]

/-- Its squared norm is the sum of the actual constraint and scalar residual squares. -/
theorem targetResidual_norm_sq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖targetResidual f c t x‖ ^ 2 = ‖c x‖ ^ 2 + (f x - t) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, targetResidual, Fin.sum_univ_castSucc]

/-- The squared residual objective `mu_2` in (7.2.5). -/
abbrev targetObjective (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ) :=
  Optimization.TargetLeastSquares.objective f c t

/-- The actual Euclidean norm gives the half squared residual objective. -/
theorem targetObjective_eq_half_norm_sq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    targetObjective f c t x = ‖targetResidual f c t x‖ ^ 2 / 2 := by
  rw [targetResidual_norm_sq]
  rfl

/-- The norm objective `mu_1` is exactly the square root of twice `mu_2`. -/
theorem norm_targetResidual_eq_sqrt (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖targetResidual f c t x‖ = Real.sqrt (2 * targetObjective f c t x) := by
  rw [targetObjective_eq_half_norm_sq]
  have he : 2 * (‖targetResidual f c t x‖ ^ 2 / 2) = ‖targetResidual f c t x‖ ^ 2 := by ring
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- The near-feasible region `F_beta` in (7.2.7). -/
def nearFeasibleSet (C : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (beta : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := {x ∈ C | ‖c x‖ ≤ beta}

/-- Membership in the near-feasible region exposes both constraints. -/
@[simp] theorem mem_nearFeasibleSet {C : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {beta : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ nearFeasibleSet C c beta ↔ x ∈ C ∧ ‖c x‖ ≤ beta := Iff.rfl

/-- The actual derivative of the squared residual, in the book's primal variable. -/
theorem targetObjective_hasFDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x) (t : ℝ) :
    HasFDerivAt (targetObjective f c t)
      ((innerSL ℝ (c x)).comp c' + (f x - t) • f') x :=
  Optimization.TargetLeastSquares.objective_hasFDerivAt hf hc t

/-- C.CNe, residual smoothness, targetwise squared-residual smoothness and f.B.Fb.
The objective bounds on the empty near-feasible region are vacuous, as in the source. -/
structure GeneralConstraintSmoothnessAssumptions (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (ell beta low up : ℝ) : Prop where
  constraintSet : Chapter06.Section01.ConvexConstraintAssumptions C
  residual : ∃ L, SmoothOn (Chapter05.Section01.residualPowerObjective c ell) C p L
  targets : ∀ t : ℝ, ∃ L, SmoothOn (targetObjective f c t) C p L
  bounds : ∀ x ∈ nearFeasibleSet C c beta, low ≤ f x ∧ f x ≤ up

/-- Lemma 7.2.5: pointwise assumptions give a single derivative Lipschitz constant
on the reached target interval. The same constant controls every actual inner parameter
sequence whose initial regularization value is the fixed source initialization. -/
theorem lemma_7_2_5 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {p : ℕ} {ell beta low up : ℝ}
    (h : GeneralConstraintSmoothnessAssumptions f c C p ell beta low up) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ t ∈ Set.Icc (low - 1) up, SmoothOn (targetObjective f c t) C p L) ∧
      ∀ (params : Chapter02.Section04.regularizationParameters) (sigma0 t : ℝ),
        t ∈ Set.Icc (low - 1) up →
        ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ),
          sigma 0 = sigma0 → TrialPrefix params p (targetObjective f c t) C x s sigma N →
          ∀ k ≤ N, sigma k ≤ max sigma0 (params.gamma3 * (L / (1 - params.eta2))) := by
  obtain ⟨L₀, h₀⟩ := h.targets 0
  obtain ⟨L₁, h₁⟩ := h.targets 1
  let B := max |low - 1| |up|
  let L := (1 + B) * L₀ + B * L₁
  have hB : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
  have hL : 0 ≤ L := add_nonneg (mul_nonneg (by positivity) h₀.nonneg)
    (mul_nonneg hB h₁.nonneg)
  have ht (t : ℝ) (ht : t ∈ Set.Icc (low - 1) up) :
      SmoothOn (targetObjective f c t) C p L :=
    Optimization.TargetLeastSquares.smoothOn_of_target_mem_Icc h₀ h₁ ht
  refine ⟨L, hL, ht, ?_⟩
  intro params sigma0 t ht' x s sigma N hs0 hr k hk
  simpa only [hs0] using hr.sigma_upper (ht t ht') h.constraintSet.convex hk

/-- The componentwise f.D1pL.C and c.D1pL.C alternative. One open neighborhood supplies
actual C^p smoothness of the objective and all constraint components. Their positive derivative
tensors have order-specific bounds and Lipschitz constants on `C` alone. -/
structure ComponentDerivativeAssumptions
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) : Prop where
  neighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ C ⊆ U ∧
    ContDiffOn ℝ p f U ∧ ∀ i, ContDiffOn ℝ p (fun x => c x i) U
  objective : ∃ B A : ℕ → ℝ,
    (∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) ∧
    (∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ A j * ‖y - x‖)
  constraint : ∀ i, ∃ B A : ℕ → ℝ,
    (∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ‖iteratedFDeriv ℝ j (fun z => c z i) x‖ ≤ B j) ∧
    (∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ j (fun z => c z i) y -
        iteratedFDeriv ℝ j (fun z => c z i) x‖ ≤ A j * ‖y - x‖)

/-- The componentwise objective assumption gives a common bound for its actual positive jets. -/
theorem ComponentDerivativeAssumptions.objective_jets
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {p : ℕ}
    (h : ComponentDerivativeAssumptions f c C p) :
    ∃ M L : ℝ, BoundedLipschitzJets.PositiveOn f p C M L := by
  obtain ⟨U, hU, hCU, hf, _⟩ := h.neighborhood
  obtain ⟨B, A, hB, hA⟩ := h.objective
  exact ⟨_, _, BoundedLipschitzJets.positiveOn_of_order_bounds hU hCU hf B A hB hA⟩

/-- Every constraint component has actual positive jets bounded on `C`, with no bounds
required on its smooth open extension. -/
theorem ComponentDerivativeAssumptions.constraint_jets
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {p : ℕ}
    (h : ComponentDerivativeAssumptions f c C p) (i : Fin m) :
    ∃ M L : ℝ, BoundedLipschitzJets.PositiveOn (fun x => c x i) p C M L := by
  obtain ⟨U, hU, hCU, _, hc⟩ := h.neighborhood
  obtain ⟨B, A, hB, hA⟩ := h.constraint i
  exact ⟨_, _, BoundedLipschitzJets.positiveOn_of_order_bounds hU hCU (hc i) B A hB hA⟩

/-- For a fixed target, the actual constraint-residual and objective-target-residual bounds
complete the componentwise sufficient condition for squared target residual smoothness. -/
theorem component_target_smoothness_sufficient
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {p : ℕ} (hp : 1 ≤ p) (hC : Convex ℝ C)
    (h : ComponentDerivativeAssumptions f c C p) {Rc Rt t : ℝ}
    (hcvalue : ∀ x ∈ C, ‖c x‖ ≤ Rc) (ht : ∀ x ∈ C, |f x - t| ≤ Rt) :
    ∃ L : ℝ, SmoothOn (targetObjective f c t) C p L := by
  classical
  obtain ⟨Mf, Lf, hf⟩ := h.objective_jets
  choose M L hc using h.constraint_jets
  apply Optimization.ComponentSmoothness.smoothOn_target hp hC hc hcvalue hf t
  simpa only [Real.norm_eq_abs] using ht

/-- The componentwise sufficient condition covers every positive even integer ell=2k.
Actual bounded and Lipschitz positive jets on convex `C`, a bounded constraint residual, and
a bounded scalar objective yield the norm-power and all squared-target smoothness assumptions.
Target-uniform constants follow from the affine target identity, and are chosen before every
bounded target family. No quantitative hypothesis is imposed outside `C`. -/
theorem component_smoothness_sufficient
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {p : ℕ} (hp : 1 ≤ p) (hC : Convex ℝ C)
    (h : ComponentDerivativeAssumptions f c C p) {Rc Rf : ℝ}
    (hcvalue : ∀ x ∈ C, ‖c x‖ ≤ Rc) (hfvalue : ∀ x ∈ C, |f x| ≤ Rf) :
    (∀ k : ℕ, 1 ≤ k → ∃ L : ℝ,
      SmoothOn (Chapter05.Section01.residualPowerObjective c (2 * (k : ℝ))) C p L) ∧
    (∀ t : ℝ, ∃ L : ℝ, SmoothOn (targetObjective f c t) C p L) ∧
    ∃ L₀ L₁ : ℝ, 0 ≤ L₀ ∧ 0 ≤ L₁ ∧
      ∀ B t : ℝ, |t| ≤ B → SmoothOn (targetObjective f c t) C p
        ((1 + B) * L₀ + B * L₁) := by
  classical
  obtain ⟨Mf, Lf, hf⟩ := h.objective_jets
  choose M L hc using h.constraint_jets
  have hfv : ∀ x ∈ C, ‖f x‖ ≤ Rf := by simpa only [Real.norm_eq_abs] using hfvalue
  refine ⟨fun k _ => Optimization.ComponentSmoothness.smoothOn_residualPower_even
    hp hC hc hcvalue k,
    Optimization.ComponentSmoothness.smoothOn_all_targets hp hC hc hcvalue hf hfv, ?_⟩
  obtain ⟨L₀, L₁, h₀, h₁, hu⟩ :=
    Optimization.ComponentSmoothness.smoothOn_targets_uniform hp hC hc hcvalue hf hfv
  exact ⟨L₀, L₁, h₀.nonneg, h₁.nonneg, hu⟩

/-- The componentwise sufficient condition constructs the original minimal assumption bundle,
including objective bounds on the near-feasible region, for every positive even exponent. -/
theorem ComponentDerivativeAssumptions.toGeneralConstraintSmoothnessAssumptions
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {p : ℕ} (hp : 1 ≤ p)
    (hC : Chapter06.Section01.ConvexConstraintAssumptions C)
    (h : ComponentDerivativeAssumptions f c C p) {Rc Rf : ℝ}
    (hcvalue : ∀ x ∈ C, ‖c x‖ ≤ Rc) (hfvalue : ∀ x ∈ C, |f x| ≤ Rf)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℝ) :
    GeneralConstraintSmoothnessAssumptions f c C p (2 * (k : ℝ)) beta (-Rf) Rf := by
  obtain ⟨hphi, htarget, _⟩ := component_smoothness_sufficient hp hC.convex h hcvalue hfvalue
  refine ⟨hC, hphi k hk, htarget, ?_⟩
  intro x hx
  exact abs_le.mp (hfvalue x (mem_nearFeasibleSet.mp hx).1)

end CartisGouldToint.Chapter07.Section02
