import Numlib.Optimization.ConstrainedTaylorCriticality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Target translations of actual bounded Lipschitz jets

Subtracting a fixed target leaves every positive derivative unchanged. Finite families
share a common neighbourhood and jet constants. Their squared-residual sums have actual
all-order estimates uniform in every target, including arbitrarily large targets.
-/

noncomputable section
open Set
namespace Optimization.ConstrainedTaylorCriticality
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Positive derivative bounds and Lipschitz constants are invariant under a constant
codomain translation; they are uniform in the translated target. -/
theorem HasBoundedLipschitzJets.sub_const {f : E → F} {p : ℕ} {U : Set E} {M L : ℝ}
    (hf : HasBoundedLipschitzJets f p U M L) (a : F) :
    HasBoundedLipschitzJets (fun x => f x - a) p U M L := by
  have heq (j : ℕ) (hj : j ∈ Finset.Icc 1 p) (x : E) (hx : x ∈ U) :
      iteratedFDeriv ℝ j (fun z => f z - a) x = iteratedFDeriv ℝ j f x := by
    have hfj : ContDiffAt ℝ j f x :=
      ((hf.contDiffOn.of_le (by exact_mod_cast (Finset.mem_Icc.mp hj).2)) x hx).contDiffAt
        (hf.isOpen.mem_nhds hx)
    change iteratedFDeriv ℝ j (f - fun _ => a) x = _
    have hj0 : j ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hj).1)
    rw [iteratedFDeriv_sub_apply hfj contDiffAt_const]
    simp only [iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, sub_zero]
  exact ⟨hf.isOpen, hf.convex, hf.contDiffOn.sub contDiffOn_const,
    hf.bound_nonneg, hf.lipschitz_nonneg,
    fun j hj x hx => by rw [heq j hj x hx]; exact hf.bound j hj x hx,
    fun j hj x hx y hy => by rw [heq j hj x hx, heq j hj y hy]; exact hf.lipschitz j hj x hx y hy⟩

/-- Restricting the open convex domain and enlarging both common constants preserves
actual bounded Lipschitz jets. -/
theorem HasBoundedLipschitzJets.mono {f : E → F} {p : ℕ} {U V : Set E}
    {M L M' L' : ℝ} (hf : HasBoundedLipschitzJets f p U M L)
    (hV : IsOpen V) (hcV : Convex ℝ V) (hVU : V ⊆ U)
    (hM : M ≤ M') (hL : L ≤ L') : HasBoundedLipschitzJets f p V M' L' := by
  refine ⟨hV, hcV, hf.contDiffOn.mono hVU, hf.bound_nonneg.trans hM,
    hf.lipschitz_nonneg.trans hL, ?_, ?_⟩
  · intro j hj x hx
    exact (hf.bound j hj x (hVU hx)).trans hM
  · intro j hj x hx y hy
    exact (hf.lipschitz j hj x (hVU hx) y (hVU hy)).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- Positive jets are bounded and Lipschitz on some open convex neighbourhood of `X`.
The function itself need not be bounded, and the neighbourhood need not be a level set. -/
def HasBoundedLipschitzJetsNear (f : E → F) (p : ℕ) (X : Set E) : Prop :=
  ∃ U M L, X ⊆ U ∧ HasBoundedLipschitzJets f p U M L

/-- A neighbourhood jet assumption is exactly an open convex-domain bound containing
`X`; this exposes its witnesses without unfolding the implementation. -/
theorem hasBoundedLipschitzJetsNear_iff {f : E → F} {p : ℕ} {X : Set E} :
    HasBoundedLipschitzJetsNear f p X ↔
      ∃ U M L, X ⊆ U ∧ HasBoundedLipschitzJets f p U M L := Iff.rfl

/-- A finite family with separate neighbourhoods and constants admits one common
neighbourhood and common constants. Empty families impose no restrictions. -/
theorem HasBoundedLipschitzJetsNear.exists_common {ι : Type*} [Finite ι]
    {f : ι → E → F} {p : ℕ} {X : Set E}
    (hf : ∀ i, HasBoundedLipschitzJetsNear (f i) p X) :
    ∃ U M L, X ⊆ U ∧ IsOpen U ∧ Convex ℝ U ∧ 0 ≤ M ∧ 0 ≤ L ∧
      ∀ i, HasBoundedLipschitzJets (f i) p U M L := by
  classical
  let := Fintype.ofFinite ι
  choose U M L hX h using hf
  refine ⟨⋂ i, U i, ∑ i, M i, ∑ i, L i, ?_,
    isOpen_iInter_of_finite (fun i => (h i).isOpen),
    convex_iInter (fun i => (h i).convex),
    Finset.sum_nonneg (fun i _ => (h i).bound_nonneg),
    Finset.sum_nonneg (fun i _ => (h i).lipschitz_nonneg), ?_⟩
  · intro x hx
    exact mem_iInter.mpr (fun i => hX i hx)
  · intro i
    exact (h i).mono (isOpen_iInter_of_finite (fun k => (h k).isOpen))
      (convex_iInter (fun k => (h k).convex)) (iInter_subset U i)
      (Finset.single_le_sum (fun k _ => (h k).bound_nonneg) (Finset.mem_univ i))
      (Finset.single_le_sum (fun k _ => (h k).lipschitz_nonneg) (Finset.mem_univ i))

/-- Finite sums of scalar squared residuals have actual all-order bounds affine in a
common residual bound. Both coefficients are uniform in every constant target vector. -/
theorem finite_squared_residual_jet_bounds {ι : Type*} [Fintype ι]
    {r : ι → E → ℝ} {p : ℕ} {U : Set E} {M L : ℝ}
    (hr : ∀ i, HasBoundedLipschitzJets (r i) p U M L) (a : ι → ℝ) :
    ContDiffOn ℝ p (fun x => ∑ i, squaredResidual (fun z => r i z - a i) x) U ∧
      ∀ j ∈ Finset.Icc 1 p,
        (∀ x ∈ U, ∀ R : ℝ, (∀ i, ‖r i x - a i‖ ≤ R) →
          ‖iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) x‖ ≤
            Fintype.card ι * ((1 / 2 : ℝ) * 2 ^ j * M ^ 2 +
              ((1 / 2 : ℝ) * 2 ^ j * M) * R)) ∧
        (∀ x ∈ U, ∀ R : ℝ, (∀ i, ‖r i x - a i‖ ≤ R) → ∀ y ∈ U,
          ‖iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) y -
            iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) x‖ ≤
              Fintype.card ι * (2 ^ j * M * (M + L) + L * R) * ‖y - x‖) := by
  classical
  have hs (i : ι) (R : ℝ) := squared_residual_jet_bounds (R := R) ((hr i).sub_const (a i))
  have hc (i : ι) : ContDiffOn ℝ p (squaredResidual (fun z => r i z - a i)) U :=
    (hs i 0).1
  have heq (j : ℕ) (hj : j ∈ Finset.Icc 1 p) (x : E) (hx : x ∈ U) :
      iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) x =
        ∑ i, iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) x := by
    apply iteratedFDeriv_fun_sum_apply
    intro i _
    exact (((hc i).of_le (by exact_mod_cast (Finset.mem_Icc.mp hj).2)) x hx).contDiffAt
      ((hr i).isOpen.mem_nhds hx)
  refine ⟨ContDiffOn.sum (fun i _ => hc i), ?_⟩
  intro j hj
  constructor
  · intro x hx R hR
    rw [heq j hj x hx]
    calc
      ‖∑ i, iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) x‖ ≤
          ∑ i, ‖iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : ι, ((1 / 2 : ℝ) * 2 ^ j * M ^ 2 +
          ((1 / 2 : ℝ) * 2 ^ j * M) * R) :=
        Finset.sum_le_sum (fun i _ => ((hs i R).2 j hj).1 x hx (hR i))
      _ = _ := by simp; ring
  · intro x hx R hR y hy
    rw [heq j hj y hy, heq j hj x hx, ← Finset.sum_sub_distrib]
    calc
      ‖∑ i, (iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) y -
          iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) x)‖ ≤
          ∑ i, ‖iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) y -
            iteratedFDeriv ℝ j (squaredResidual (fun w => r i w - a i)) x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : ι, ((2 : ℝ) ^ j * M * (M + L) + L * R) * ‖y - x‖ :=
        Finset.sum_le_sum (fun i _ => ((hs i R).2 j hj).2 x hx (hR i) y hy)
      _ = _ := by simp; ring

/-- On a common neighbourhood, finite scalar least-squares families have all positive
jet norms and Lipschitz bounds affine in a component residual bound. The coefficients are
at least one and are chosen before every target vector and every reference bound. -/
theorem finite_squared_residual_jet_bounds_near {ι : Type*} [Fintype ι]
    {r : ι → E → ℝ} {p : ℕ} {X : Set E}
    (hr : ∀ i, HasBoundedLipschitzJetsNear (r i) p X) :
    ∃ (U : Set E) (LA LB BA BB : ℕ → ℝ),
      X ⊆ U ∧ IsOpen U ∧ Convex ℝ U ∧
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j) ∧
      ∀ a : ι → ℝ,
        ContDiffOn ℝ p (fun x => ∑ i, squaredResidual (fun z => r i z - a i) x) U ∧
        ∀ j ∈ Finset.Icc 1 p, ∀ R : ℝ, 0 ≤ R → ∀ x ∈ U,
          (∀ i, ‖r i x - a i‖ ≤ R) →
          ‖iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) x‖ ≤
              BA j + BB j * R ∧
          ∀ y ∈ U,
            ‖iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) y -
              iteratedFDeriv ℝ j (fun z => ∑ i, squaredResidual (fun w => r i w - a i) z) x‖ ≤
                (LA j + LB j * R) * ‖y - x‖ := by
  classical
  obtain ⟨U, M, L, hX, ho, hc, _hM, _hL, h⟩ :=
    HasBoundedLipschitzJetsNear.exists_common hr
  let d : ℝ := Fintype.card ι
  let LA : ℕ → ℝ := fun j => max 1 (d * (2 ^ j * M * (M + L)))
  let LB : ℕ → ℝ := fun _ => max 1 (d * L)
  let BA : ℕ → ℝ := fun j => max 1 (d * ((1 / 2 : ℝ) * 2 ^ j * M ^ 2))
  let BB : ℕ → ℝ := fun j => max 1 (d * ((1 / 2 : ℝ) * 2 ^ j * M))
  refine ⟨U, LA, LB, BA, BB, hX, ho, hc,
    fun _ => ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _⟩, ?_⟩
  intro a
  have hb := finite_squared_residual_jet_bounds h a
  refine ⟨hb.1, ?_⟩
  intro j hj R hR x hx hrx
  constructor
  · apply ((hb.2 j hj).1 x hx R hrx).trans
    calc
      d * ((1 / 2 : ℝ) * 2 ^ j * M ^ 2 + (1 / 2 : ℝ) * 2 ^ j * M * R) =
          d * ((1 / 2 : ℝ) * 2 ^ j * M ^ 2) + d * ((1 / 2 : ℝ) * 2 ^ j * M) * R := by ring
      _ ≤ BA j + BB j * R := add_le_add (le_max_right _ _)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
  · intro y hy
    apply ((hb.2 j hj).2 x hx R hrx y hy).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      d * (2 ^ j * M * (M + L) + L * R) =
          d * (2 ^ j * M * (M + L)) + d * L * R := by ring
      _ ≤ LA j + LB j * R := add_le_add (le_max_right _ _)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A Euclidean squared residual is the sum of its scalar component squared residuals. -/
theorem squaredResidual_euclidean_eq_sum {ι : Type*} [Fintype ι]
    (r : E → EuclideanSpace ℝ ι) :
    squaredResidual r = fun x => ∑ i, squaredResidual (fun z => r z i) x := by
  funext x
  simp only [squaredResidual, EuclideanSpace.norm_sq_eq, Finset.sum_div]

end Optimization.ConstrainedTaylorCriticality
