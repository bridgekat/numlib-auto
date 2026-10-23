import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Smooth and Lipschitz gluing on real half-lines

Matching actual jets through a finite order give a piecewise function of that
same finite smoothness. The derivative at the join is derived by gluing its
within-derivative filters on the two closed half-lines. Iteration then gives an
exact formula for every derivative through that order. The Lipschitz gluing
lemma retains the common constant on any set containing the join.
-/

open Set Filter
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Functions with a common derivative and matching value at the join can be
glued across the two real half-lines without changing that derivative. -/
theorem hasDerivAt_piecewise_Iic {f g : ℝ → F} {c : ℝ} {d : F}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfg : f c = g c) :
    HasDerivAt ((Iic c).piecewise f g) d c := by
  have hl : HasDerivWithinAt ((Iic c).piecewise f g) d (Iic c) c :=
    hf.hasDerivWithinAt.congr_of_mem (fun x hx => piecewise_eq_of_mem (Iic c) f g hx) (by simp)
  have hr : HasDerivWithinAt ((Iic c).piecewise f g) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr_of_mem _ (by simp)
    intro x hx
    by_cases hxc : x ≤ c
    · have heq : x = c := le_antisymm hxc hx
      subst x
      simp [hfg]
    · simp [hxc]
  have hu := hl.union hr
  rw [Iic_union_Ici] at hu
  exact hu.hasDerivAt (by simp)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
private theorem piecewise_Iic_eventuallyEq_left {f g : ℝ → F} {x c : ℝ} (h : x < c) :
    (Iic c).piecewise f g =ᶠ[nhds x] f := by
  filter_upwards [eventually_lt_nhds h] with y hy
  exact piecewise_eq_of_mem (Iic c) f g hy.le

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
private theorem piecewise_Iic_eventuallyEq_right {f g : ℝ → F} {x c : ℝ} (h : c < x) :
    (Iic c).piecewise f g =ᶠ[nhds x] g := by
  filter_upwards [eventually_gt_nhds h] with y hy
  exact piecewise_eq_of_notMem _ _ _ (not_le_of_gt hy)

/-- Matching values and first derivatives preserve global differentiability
when gluing two differentiable functions across a real breakpoint. -/
theorem differentiable_piecewise_Iic {f g : ℝ → F} {c : ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f c = g c) (hderiv : deriv f c = deriv g c) :
    Differentiable ℝ ((Iic c).piecewise f g) := by
  intro x
  rcases lt_trichotomy x c with h | rfl | h
  · exact (hf x).congr_of_eventuallyEq (piecewise_Iic_eventuallyEq_left h)
  · exact (hasDerivAt_piecewise_Iic (hf x).hasDerivAt
      ((hg x).hasDerivAt.congr_deriv hderiv.symm) hfg).differentiableAt
  · exact (hg x).congr_of_eventuallyEq (piecewise_Iic_eventuallyEq_right h)

/-- The genuine derivative of the glued function is the gluing of its derivatives. -/
theorem deriv_piecewise_Iic {f g : ℝ → F} {c : ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f c = g c) (hderiv : deriv f c = deriv g c) :
    deriv ((Iic c).piecewise f g) = (Iic c).piecewise (deriv f) (deriv g) := by
  funext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [(piecewise_Iic_eventuallyEq_left h).deriv_eq]
    simp [h.le]
  · rw [(hasDerivAt_piecewise_Iic (hf x).hasDerivAt
      ((hg x).hasDerivAt.congr_deriv hderiv.symm) hfg).deriv]
    simp
  · rw [(piecewise_Iic_eventuallyEq_right h).deriv_eq]
    simp [not_le_of_gt h]

/-- Every actual derivative through the matching finite jet order is the
piecewise derivative of the two branches. -/
theorem iteratedDeriv_piecewise_Iic {f g : ℝ → F} {c : ℝ} {p j : ℕ}
    (hf : ContDiff ℝ p f) (hg : ContDiff ℝ p g)
    (hjet : ∀ i ≤ p, iteratedDeriv i f c = iteratedDeriv i g c) (hj : j ≤ p) :
    iteratedDeriv j ((Iic c).piecewise f g) =
      (Iic c).piecewise (iteratedDeriv j f) (iteratedDeriv j g) := by
  have hid : ∀ j, j ≤ p → iteratedDeriv j ((Iic c).piecewise f g) =
      (Iic c).piecewise (iteratedDeriv j f) (iteratedDeriv j g) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [iteratedDeriv_succ, ih (by omega)]
      have hD : deriv (iteratedDeriv k f) c = deriv (iteratedDeriv k g) c := by
        simpa only [← iteratedDeriv_succ] using hjet (k + 1) hk
      rw [deriv_piecewise_Iic
        (hf.differentiable_iteratedDeriv k (by exact_mod_cast (show k < p by omega)))
        (hg.differentiable_iteratedDeriv k (by exact_mod_cast (show k < p by omega)))
        (hjet k (by omega)) hD]
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
  exact hid j hj

/-- Matching actual finite jets preserve precisely the corresponding finite
smoothness when two globally smooth branches are glued across a breakpoint. -/
theorem contDiff_piecewise_Iic {f g : ℝ → F} {c : ℝ} {p : ℕ}
    (hf : ContDiff ℝ p f) (hg : ContDiff ℝ p g)
    (hjet : ∀ j ≤ p, iteratedDeriv j f c = iteratedDeriv j g c) :
    ContDiff ℝ p ((Iic c).piecewise f g) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j hj
    rw [iteratedDeriv_piecewise_Iic hf hg hjet hj]
    apply Continuous.piecewise _ (hf.continuous_iteratedDeriv j (by exact_mod_cast hj))
      (hg.continuous_iteratedDeriv j (by exact_mod_cast hj))
    intro x hx
    rw [frontier_Iic, mem_singleton_iff] at hx
    subst x
    exact hjet j hj
  · intro j hj
    rw [iteratedDeriv_piecewise_Iic hf hg hjet hj.le]
    apply differentiable_piecewise_Iic
      (hf.differentiable_iteratedDeriv j (by exact_mod_cast hj))
      (hg.differentiable_iteratedDeriv j (by exact_mod_cast hj)) (hjet j hj.le)
    simpa only [← iteratedDeriv_succ] using hjet (j + 1) (by omega)

omit [NormedSpace ℝ F] in
/-- A common Lipschitz constant on the two half-lines is preserved by gluing
matching endpoint values, on any set that contains the join. -/
theorem LipschitzOnWith.piecewise_Iic {f g : ℝ → F} {c : ℝ} {S : Set ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (S ∩ Iic c))
    (hg : LipschitzOnWith L g (S ∩ Ici c)) (hc : c ∈ S) (hfg : f c = g c) :
    LipschitzOnWith L ((Iic c).piecewise f g) S := by
  have hle : ∀ x ∈ S, ∀ y ∈ S, x ≤ y →
      ‖(Iic c).piecewise f g x - (Iic c).piecewise f g y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    intro x hxS y hyS hxy
    by_cases hy : y ≤ c
    · have hx : x ≤ c := hxy.trans hy
      simpa only [piecewise_eq_of_mem (Iic c) f g hx, piecewise_eq_of_mem (Iic c) f g hy] using
        hf.norm_sub_le ⟨hxS,hx⟩ ⟨hyS,hy⟩
    · have hcy : c ≤ y := (lt_of_not_ge hy).le
      by_cases hx : x ≤ c
      · rw [piecewise_eq_of_mem (Iic c) f g hx, piecewise_eq_of_notMem (Iic c) f g hy]
        have hleft := hf.norm_sub_le ⟨hxS,hx⟩ ⟨hc,by simp⟩
        have hright : ‖f c - g y‖ ≤ (L : ℝ) * ‖c - y‖ := by
          rw [hfg]
          exact hg.norm_sub_le ⟨hc,by simp⟩ ⟨hyS,hcy⟩
        calc
          _ ≤ ‖f x - f c‖ + ‖f c - g y‖ := by
            simpa only [dist_eq_norm] using dist_triangle (f x) (f c) (g y)
          _ ≤ (L : ℝ) * ‖x - c‖ + (L : ℝ) * ‖c - y‖ := add_le_add hleft hright
          _ = _ := by
            simp only [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx),
              abs_of_nonpos (sub_nonpos.mpr hcy), abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
      · simpa only [piecewise_eq_of_notMem (Iic c) f g hx, piecewise_eq_of_notMem (Iic
        c) f g hy] using
          hg.norm_sub_le ⟨hxS,(lt_of_not_ge hx).le⟩ ⟨hyS,hcy⟩
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hle x hx y hy hxy
  · have hh := hle y hy x hx hyx
    rw [norm_sub_rev ((Iic c).piecewise f g y), norm_sub_rev y] at hh
    exact hh
