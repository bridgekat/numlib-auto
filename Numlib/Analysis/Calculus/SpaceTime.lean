/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.FDeriv.Partial` (the partial operators on `E × ℝ`) and
`Mathlib.Analysis.Calculus.Deriv.Comp` (a bounded linear map commutes with `d/dt`).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Calculus.DerivativeTest
import Numlib.Analysis.Calculus.IteratedFDeriv

/-!
# Calculus on `E × ℝ`: the time derivative and the spatial Laplacian

The two partial operators on a function `w : E × ℝ → ℝ` of space and time, for `E` a
finite-dimensional real inner product space: the time derivative `∂ₜ w` (`Heat.timeDeriv`) and
the spatial Laplacian `Δ_x w` (`Heat.spaceLaplacian`, Mathlib's `InnerProductSpace.laplacian` of
the slice `y ↦ w (y, t)`), with their smoothness, their locality on open sets, their commutation
`∂ₜ Δ_x = Δ_x ∂ₜ` on smooth functions (`Heat.timeDeriv_spaceLaplacian`, from the symmetry of the
iterated derivative, `Numlib/Analysis/Calculus/IteratedFDeriv`) and the iterates of both.
The names carry the `Heat` namespace of the modules that first used them
(`Numlib/Analysis/PDE/Heat/Classical`, the classical heat equation; `Numlib/Analysis/PDE/Wave`,
Remark 10 of [brezis2011functional] chapter 10); nothing here is about the heat equation.

The last sections are the elementary facts that a bounded linear map commutes with the
derivative of a curve (`Bochner.hasDerivWithinAt_of_forall_add_smul_norm_le`), stated for an
additive homogeneous map with a norm bound, the form in which the evaluation at a point of a
canonical `C^k(Ω̄)` representative enters the space–time bridge of
`Numlib/Analysis/PDE/Bochner/SpaceTime`, and the second iterated derivative within a set as a
twice-iterated `derivWithin` (`iteratedDerivWithin_two`).

## References

[brezis2011functional], chapter 10, Remark 4 and Remark 10.
-/

open Filter Set Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Heat

/-! ### The time derivative and the spatial Laplacian of a function of `(x, t)` -/

section SpaceTimeCalculus

variable {w w₁ w₂ : E × ℝ → ℝ}

/-- **The time derivative** `∂ₜ w` of a function of `(x, t)`, as a function of `(x, t)`:
`timeDeriv w (x, t) = d/dt w (x, t)`. -/
noncomputable def timeDeriv (w : E × ℝ → ℝ) : E × ℝ → ℝ :=
  fun p ↦ deriv (fun s ↦ w (p.1, s)) p.2

/-- **The spatial Laplacian** `Δ_x w` of a function of `(x, t)`, as a function of `(x, t)`:
`spaceLaplacian w (x, t) = Δ (w (·, t)) x`. -/
noncomputable def spaceLaplacian (w : E × ℝ → ℝ) : E × ℝ → ℝ :=
  fun p ↦ Δ (fun y ↦ w (y, p.2)) p.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `timeDeriv w (x, t)` is the derivative of `s ↦ w (x, s)` at `t`. -/
@[simp]
theorem timeDeriv_apply (w : E × ℝ → ℝ) (x : E) (t : ℝ) :
    timeDeriv w (x, t) = deriv (fun s ↦ w (x, s)) t := rfl

/-- `spaceLaplacian w (x, t)` is the Laplacian of `y ↦ w (y, t)` at `x`. -/
@[simp]
theorem spaceLaplacian_apply (w : E × ℝ → ℝ) (x : E) (t : ℝ) :
    spaceLaplacian w (x, t) = Δ (fun y ↦ w (y, t)) x := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The derivatives of a spatial slice `y ↦ w (y, t)` are the derivatives of `w` along the
directions `(m k, 0)`: the slice is `w` composed with the affine map `y ↦ (y, 0) + (0, t)`. -/
theorem iteratedFDeriv_slice_fst [NormedSpace ℝ E] {n : WithTop ℕ∞} (hw : ContDiff ℝ n w)
    {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) (t : ℝ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (fun y ↦ w (y, t)) x m = iteratedFDeriv ℝ i w (x, t) fun k ↦ (m k, 0) := by
  have h1 : (fun y ↦ w (y, t)) =
      (fun q : E × ℝ ↦ w (q + (0, t))) ∘ (ContinuousLinearMap.inl ℝ E ℝ) :=
    funext fun y ↦ by simp
  have h2 : ContDiff ℝ n fun q : E × ℝ ↦ w (q + (0, t)) := hw.comp (contDiff_id.add contDiff_const)
  rw [h1, (ContinuousLinearMap.inl ℝ E ℝ).iteratedFDeriv_comp_right h2 x hi,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  simp

/-- The spatial Laplacian through the standard orthonormal basis `b` of `E`:
`Δ_x w (x, t) = ∑ i, D² w (x, t) [(b i, 0), (b i, 0)]`. -/
theorem spaceLaplacian_eq_sum_iteratedFDeriv (hw : ContDiff ℝ 2 w) (p : E × ℝ) :
    spaceLaplacian w p = ∑ i, iteratedFDeriv ℝ 2 w p
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] := by
  obtain ⟨x, t⟩ := p
  rw [spaceLaplacian_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y ↦ w (y, t)) (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_slice_fst hw le_rfl]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The time derivative is the derivative of `w` in the direction `(0, 1)`. -/
theorem timeDeriv_eq_fderiv [NormedSpace ℝ E] (hw : ContDiff ℝ 1 w) (p : E × ℝ) :
    timeDeriv w p = fderiv ℝ w p (0, 1) := by
  obtain ⟨x, t⟩ := p
  have h : HasDerivAt (fun s : ℝ ↦ (x, s)) ((0 : E), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact ((hw.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt t h).deriv

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The time derivative of a smooth function is smooth. -/
theorem contDiff_timeDeriv [NormedSpace ℝ E] (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (timeDeriv w) := by
  have : timeDeriv w = fun p ↦ fderiv ℝ w p (0, 1) :=
    funext fun p ↦ timeDeriv_eq_fderiv (hw.of_le (by simp)) p
  rw [this]
  exact hw.fderiv_apply_right (0, 1)

/-- The spatial Laplacian of a smooth function is smooth. -/
theorem contDiff_spaceLaplacian (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (spaceLaplacian w) := by
  have : spaceLaplacian w = fun p ↦ ∑ i, iteratedFDeriv ℝ 2 w p
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] :=
    funext fun p ↦ spaceLaplacian_eq_sum_iteratedFDeriv (hw.of_le (by simp)) p
  rw [this]
  refine ContDiff.sum fun i _ ↦ ?_
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E × ℝ) ℝ _).contDiff.comp
    (hw.iteratedFDeriv_right (m := ∞) (i := 2) (by simp))

/-- **The time derivative commutes with the spatial Laplacian** on a smooth function:
`∂ₜ (Δ_x w) = Δ_x (∂ₜ w)`. Both sides are `∑ i, D³ w [(0, 1), (b i, 0), (b i, 0)]`: the left
side by differentiating the second derivative along `(0, 1)` outermost
(`iteratedFDeriv_succ_apply_left_of_differentiableAt`), the right side by taking the derivative
along `(0, 1)` innermost (`ContDiff.iteratedFDeriv_succ_apply_left'`, the symmetry of the
iterated derivative). -/
theorem timeDeriv_spaceLaplacian (hw : ContDiff ℝ ∞ w) :
    timeDeriv (spaceLaplacian w) = spaceLaplacian (timeDeriv w) := by
  funext p
  have hL : spaceLaplacian w = fun q ↦ ∑ i, iteratedFDeriv ℝ 2 w q
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] :=
    funext fun q ↦ spaceLaplacian_eq_sum_iteratedFDeriv (hw.of_le (by simp)) q
  have hd : ∀ m : Fin 2 → E × ℝ, ∀ q, DifferentiableAt ℝ (fun z ↦ iteratedFDeriv ℝ 2 w z m) q :=
    fun m q ↦ ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E × ℝ) ℝ m).contDiff.comp
      (hw.iteratedFDeriv_right (m := ∞) (i := 2) (by simp))).differentiable (by simp) q
  have hT : timeDeriv w = fun q ↦ fderiv ℝ w q (0, 1) :=
    funext fun q ↦ timeDeriv_eq_fderiv (hw.of_le (by simp)) q
  have hL' : spaceLaplacian w = ∑ i, fun q ↦ iteratedFDeriv ℝ 2 w q
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] := by
    rw [hL]
    funext q
    simp only [Finset.sum_apply]
  rw [timeDeriv_eq_fderiv ((contDiff_spaceLaplacian hw).of_le (by simp)),
    spaceLaplacian_eq_sum_iteratedFDeriv ((contDiff_timeDeriv hw).of_le (by simp)), hL',
    fderiv_sum fun i _ ↦ hd _ p, sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set m : Fin 2 → E × ℝ := ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)]
  have h3 := iteratedFDeriv_succ_apply_left_of_differentiableAt
    ((hw.iteratedFDeriv_right (m := 1) (i := 2) (by simp)).differentiable one_ne_zero p)
    (Fin.cons (0, 1) m)
  rw [Fin.tail_cons, Fin.cons_zero] at h3
  have h4 := hw.iteratedFDeriv_succ_apply_left' 2 (Fin.cons (0, 1) m) p
  rw [Fin.tail_cons, Fin.cons_zero] at h4
  rw [hT, ← h3, h4]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The time derivative is local: functions agreeing on an open set have the same time
derivative there. -/
theorem timeDeriv_eqOn [NormedSpace ℝ E] {V : Set (E × ℝ)} (hV : IsOpen V) (h : EqOn w₁ w₂ V) :
    EqOn (timeDeriv w₁) (timeDeriv w₂) V := by
  rintro ⟨x, t⟩ hp
  have hmem : (fun s : ℝ ↦ (x, s)) ⁻¹' V ∈ 𝓝 t :=
    (hV.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
  exact Filter.EventuallyEq.deriv_eq (eventually_of_mem hmem fun s hs ↦ h hs)

/-- The spatial Laplacian is local: functions agreeing on an open set have the same spatial
Laplacian there. -/
theorem spaceLaplacian_eqOn {V : Set (E × ℝ)} (hV : IsOpen V) (h : EqOn w₁ w₂ V) :
    EqOn (spaceLaplacian w₁) (spaceLaplacian w₂) V := by
  rintro ⟨x, t⟩ hp
  have hmem : (fun y : E ↦ (y, t)) ⁻¹' V ∈ 𝓝 x :=
    (hV.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp
  exact (laplacian_congr_nhds (eventually_of_mem hmem fun y hy ↦ h hy)).eq_of_nhds

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The time derivative of a scalar multiple. -/
theorem timeDeriv_const_smul (c : ℝ) (w : E × ℝ → ℝ) :
    timeDeriv (c • w) = c • timeDeriv w := by
  funext ⟨x, t⟩
  simp only [timeDeriv_apply, Pi.smul_apply, smul_eq_mul]
  exact congrFun (deriv_const_mul_field' c) t

/-- The spatial Laplacian of a scalar multiple of a smooth function. -/
theorem spaceLaplacian_const_smul (c : ℝ) (hw : ContDiff ℝ ∞ w) :
    spaceLaplacian (c • w) = c • spaceLaplacian w := by
  funext ⟨x, t⟩
  have : (fun y ↦ (c • w) (y, t)) = c • fun y ↦ w (y, t) := rfl
  have hslice : ContDiffAt ℝ 2 (fun y ↦ w (y, t)) x :=
    (hw.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  change Δ (fun y ↦ (c • w) (y, t)) x = c • Δ (fun y ↦ w (y, t)) x
  rw [this, laplacian_smul c hslice]

/-- Iterating the spatial Laplacian preserves smoothness. -/
theorem contDiff_spaceLaplacian_iterate (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    ContDiff ℝ ∞ (spaceLaplacian^[j] w) := by
  induction j with
  | zero => exact hw
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiff_spaceLaplacian ih

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Iterating the time derivative preserves smoothness. -/
theorem contDiff_timeDeriv_iterate [NormedSpace ℝ E] (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    ContDiff ℝ ∞ (timeDeriv^[j] w) := by
  induction j with
  | zero => exact hw
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiff_timeDeriv ih

/-- The time derivative commutes with the iterated spatial Laplacian on a smooth function. -/
theorem timeDeriv_spaceLaplacian_iterate (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    timeDeriv (spaceLaplacian^[j] w) = spaceLaplacian^[j] (timeDeriv w) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      timeDeriv_spaceLaplacian (contDiff_spaceLaplacian_iterate hw j), ih]

/-- The iterated spatial Laplacian is local. -/
theorem spaceLaplacian_iterate_eqOn {V : Set (E × ℝ)} (hV : IsOpen V) (h : EqOn w₁ w₂ V)
    (j : ℕ) : EqOn (spaceLaplacian^[j] w₁) (spaceLaplacian^[j] w₂) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact spaceLaplacian_eqOn hV ih

/-- The iterated spatial Laplacian of a scalar multiple of a smooth function. -/
theorem spaceLaplacian_iterate_const_smul (c : ℝ) (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    spaceLaplacian^[j] (c • w) = c • spaceLaplacian^[j] w := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      spaceLaplacian_const_smul c (contDiff_spaceLaplacian_iterate hw j)]

/-- The iterated spatial Laplacian, on a slice, is the iterated Laplacian of the slice. -/
theorem spaceLaplacian_iterate_slice (w : E × ℝ → ℝ) (j : ℕ) (t : ℝ) :
    (fun y ↦ spaceLaplacian^[j] w (y, t)) = Laplacian.laplacian^[j] fun y ↦ w (y, t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The iterated time derivative, on a slice, is the iterated derivative of the slice. -/
theorem timeDeriv_iterate_slice [NormedSpace ℝ E] (w : E × ℝ → ℝ) (j : ℕ) (x : E) :
    (fun s ↦ timeDeriv^[j] w (x, s)) = deriv^[j] fun s ↦ w (x, s) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

end SpaceTimeCalculus

/-- The iterated derivatives of a function vanishing on an open set vanish there. -/
theorem iterate_deriv_eq_zero_of_eqOn {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : EqOn f 0 s) (j : ℕ) : EqOn (deriv^[j] f) 0 s := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro t ht
    rw [Function.iterate_succ_apply', Pi.zero_apply,
      Filter.EventuallyEq.deriv_eq (eventually_of_mem (hs.mem_nhds ht) ih), deriv_zero,
      Pi.zero_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The iterated time derivatives of a smooth function vanishing on `{x} × (0, T)` vanish at
`(x, 0)`**: they vanish on `{x} × (0, T)` (`iterate_deriv_eq_zero_of_eqOn`) and are
continuous. -/
theorem timeDeriv_iterate_apply_zero_eq_zero [NormedSpace ℝ E] {T : ℝ} {u : E × ℝ → ℝ}
    (hT : 0 < T) (hsmooth : ContDiff ℝ ∞ u) {x : E} (hx : ∀ t ∈ Ioo 0 T, u (x, t) = 0) (n : ℕ) :
    timeDeriv^[n] u (x, 0) = 0 := by
  have h1 : EqOn (fun s ↦ timeDeriv^[n] u (x, s)) 0 (Ioo 0 T) := by
    rw [timeDeriv_iterate_slice]
    exact iterate_deriv_eq_zero_of_eqOn isOpen_Ioo (fun t ht ↦ hx t ht) n
  have h2 : EqOn (fun s ↦ timeDeriv^[n] u (x, s)) 0 (Icc 0 T) := by
    rw [← closure_Ioo hT.ne]
    exact h1.of_subset_closure ((contDiff_timeDeriv_iterate hsmooth n).continuous.comp
      (continuous_const.prodMk continuous_id)).continuousOn continuousOn_const subset_closure
      subset_rfl
  exact h2 (left_mem_Icc.2 hT.le)

end Heat

/-! ### Evaluation of a bounded linear family commutes with `d/dt` -/

namespace Bochner

section Linear

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {Φ : V → W}

/-- An additive, homogeneous map bounded by `C ‖w‖` is Lipschitz with constant `C`. -/
theorem norm_sub_le_of_forall_add_smul_norm_le (hadd : ∀ w₁ w₂, Φ (w₁ + w₂) = Φ w₁ + Φ w₂)
    (hsmul : ∀ (c : ℝ) w, Φ (c • w) = c • Φ w) {C : ℝ} (hb : ∀ w, ‖Φ w‖ ≤ C * ‖w‖) (w₁ w₂ : V) :
    ‖Φ w₁ - Φ w₂‖ ≤ C * ‖w₁ - w₂‖ := by
  let L : V →ₗ[ℝ] W := ⟨⟨Φ, hadd⟩, hsmul⟩
  have : Φ w₁ - Φ w₂ = Φ (w₁ - w₂) := (map_sub L w₁ w₂).symm
  rw [this]
  exact hb _

/-- **A bounded linear map commutes with the derivative of a curve**: if `Φ` is additive,
homogeneous and bounded by `C ‖w‖`, then `Φ ∘ v` has derivative `Φ v'` within `s` wherever `v`
has derivative `v'`. This is how the evaluation at a point of the canonical `C^k(Ω̄)`
representative — a bounded linear functional of `w ∈ H^m(Ω)` — commutes with `d/dt`. -/
theorem hasDerivWithinAt_of_forall_add_smul_norm_le (hadd : ∀ w₁ w₂, Φ (w₁ + w₂) = Φ w₁ + Φ w₂)
    (hsmul : ∀ (c : ℝ) w, Φ (c • w) = c • Φ w) {C : ℝ} (hb : ∀ w, ‖Φ w‖ ≤ C * ‖w‖)
    {v : ℝ → V} {v' : V} {s : Set ℝ} {t : ℝ} (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun r ↦ Φ (v r)) (Φ v') s t := by
  let L : V →L[ℝ] W := LinearMap.mkContinuous ⟨⟨Φ, hadd⟩, hsmul⟩ C hb
  exact L.hasFDerivAt.comp_hasDerivWithinAt t hv

end Linear

end Bochner

/-! ### The second iterated derivative within a set -/

/-- `iteratedDerivWithin 2 f s = derivWithin (derivWithin f s) s`. -/
theorem iteratedDerivWithin_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (s : Set ℝ) : iteratedDerivWithin 2 f s = derivWithin (derivWithin f s) s :=
  iteratedDerivWithin_succ.trans (congrArg (fun g ↦ derivWithin g s) iteratedDerivWithin_one)
