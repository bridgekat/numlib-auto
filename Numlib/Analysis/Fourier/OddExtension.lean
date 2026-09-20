/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`, beside the density of the trigonometric
polynomials.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.SineBasis
import Numlib.Analysis.Fourier.TrigonometricBasis

/-!
# The odd periodic extension, and the density of the sine polynomials in `C₀[0, π]`

The space `C₀[0, π]` of continuous functions on `[0, π]` vanishing at both ends, in which the
sine polynomials `sinePolynomial n c = ∑_{j < n} c j sin ((j + 1) x)` are a dense subspace: the
natural phase space of the Dirichlet problem in the uniform norm.

* `oddReflect v : ℝ → ℝ`, for `v : C(Icc 0 π, ℝ)`, is the odd reflection of `v` about `0` (the
  argument clamped to `[0, π]`), and `oddPeriodicExtend v : ℝ → ℝ` its `2π`-periodic extension:
  odd and `2π`-periodic (`oddPeriodicExtend_neg`, `oddPeriodicExtend_periodic`), continuous when
  `v 0 = v π = 0` (`continuous_oddPeriodicExtend`), equal to `v` on `[0, π]` and bounded by
  `‖v‖`; `eq_of_odd_of_periodic_of_eqOn_Icc` says that an odd `2π`-periodic function is
  determined by its values on `[0, π]`, which identifies the extension of a sine polynomial with
  the sine polynomial itself (`oddPeriodicExtend_sinePolynomial`).
* `exists_mem_span_sinMap_norm_sub_lt`: **the sine polynomials are uniformly dense in
  `C₀[0, π]`**. The odd `2π`-periodic extension of `v` is a continuous function on the circle,
  uniformly approximable by real trigonometric polynomials
  (`exists_mem_span_trigFun_norm_sub_lt`, `Numlib.Analysis.Fourier.TrigonometricBasis`); the
  odd part of the approximant is a sine polynomial that is as close, since the target is odd.

## References

[han2009theoretical] §6.2, Exercise 6.2.1.
-/

open Filter Set Topology Finset
open scoped Real

noncomputable section

/-! ### The odd `2π`-periodic extension of a function on `[0, π]` -/

section OddPeriodicExtend

/-- The odd reflection of `v : C(Icc 0 π, ℝ)` about `0`: `v y` for `y ≥ 0` and `-v (-y)` for
`y < 0`, the argument clamped to `[0, π]`. Only its values on `[-π, π]` are used. -/
noncomputable def oddReflect (v : C(Icc (0 : ℝ) π, ℝ)) (y : ℝ) : ℝ :=
  if 0 ≤ y then v (projIcc 0 π Real.pi_pos.le y) else -v (projIcc 0 π Real.pi_pos.le (-y))

variable {v w : C(Icc (0 : ℝ) π, ℝ)}

/-- On `[0, π]` the odd reflection is `v` itself. -/
theorem oddReflect_of_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) π) : oddReflect v y = v ⟨y, hy⟩ := by
  rw [oddReflect, ite_eq_left hy.1, projIcc_of_mem]

/-- On `[-π, 0)` the odd reflection is `-v (-y)`. -/
theorem oddReflect_of_neg_mem {y : ℝ} (hy : -y ∈ Icc (0 : ℝ) π) (hy' : y < 0) :
    oddReflect v y = -v ⟨-y, hy⟩ := by
  rw [oddReflect, ite_eq_right (not_le.2 hy'), projIcc_of_mem]

/-- The odd reflection is odd, provided `v 0 = 0`. -/
theorem oddReflect_neg (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0) (y : ℝ) :
    oddReflect v (-y) = -oddReflect v y := by
  unfold oddReflect
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [ite_eq_left (neg_nonneg.2 hy.le), ite_eq_right (not_le.2 hy), neg_neg]
  · simp [h0]
  · rw [ite_eq_right (not_le.2 (neg_neg_iff_pos.2 hy)), ite_eq_left hy.le, neg_neg]

/-- The odd reflection is continuous, provided `v 0 = 0`. -/
theorem continuous_oddReflect (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0) :
    Continuous (oddReflect v) := by
  unfold oddReflect
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · exact (v.continuous.comp continuous_projIcc).continuousOn
  · exact ((v.continuous.comp continuous_projIcc).comp continuous_neg).neg.continuousOn
  · intro y hy
    subst hy
    simp [h0]

/-- The odd reflection is bounded by `‖v‖`. -/
theorem abs_oddReflect_le (y : ℝ) : |oddReflect v y| ≤ ‖v‖ := by
  unfold oddReflect
  split_ifs
  · exact (Real.norm_eq_abs _).symm.trans_le (v.norm_coe_le_norm _)
  · rw [abs_neg]
    exact (Real.norm_eq_abs _).symm.trans_le (v.norm_coe_le_norm _)

/-- The odd reflection is additive in `v`. -/
theorem oddReflect_add (v w : C(Icc (0 : ℝ) π, ℝ)) (y : ℝ) :
    oddReflect (v + w) y = oddReflect v y + oddReflect w y := by
  unfold oddReflect
  split_ifs <;> simp only [ContinuousMap.add_apply]
  ring

/-- The odd reflection is homogeneous in `v`. -/
theorem oddReflect_smul (a : ℝ) (v : C(Icc (0 : ℝ) π, ℝ)) (y : ℝ) :
    oddReflect (a • v) y = a * oddReflect v y := by
  unfold oddReflect
  split_ifs <;> simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- **The odd `2π`-periodic extension** of `v : C(Icc 0 π, ℝ)` to the whole line: the
`2π`-periodic function that agrees with the odd reflection of `v` on `[-π, π)`. -/
noncomputable def oddPeriodicExtend (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) : ℝ :=
  AddCircle.liftIco (2 * π) (-π) (oddReflect v) (x : AddCircle (2 * π))

/-- The extension is `2π`-periodic. -/
theorem oddPeriodicExtend_periodic (v : C(Icc (0 : ℝ) π, ℝ)) :
    Function.Periodic (oddPeriodicExtend v) (2 * π) := by
  intro x
  simp only [oddPeriodicExtend, AddCircle.coe_add_period]

/-- On `[-π, π)` the extension is the odd reflection. -/
theorem oddPeriodicExtend_of_mem_Ico {x : ℝ} (hx : x ∈ Ico (-π) π) :
    oddPeriodicExtend v x = oddReflect v x :=
  AddCircle.liftIco_coe_apply (by rw [show -π + 2 * π = π by ring]; exact hx)

/-- The extension is the odd reflection evaluated at the representative in `[-π, π)`. -/
theorem oddPeriodicExtend_eq (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    oddPeriodicExtend v x
      = oddReflect v (AddCircle.equivIco (2 * π) (-π) (x : AddCircle (2 * π)) : ℝ) := rfl

/-- The extension is additive in `v`. -/
theorem oddPeriodicExtend_add (v w : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    oddPeriodicExtend (v + w) x = oddPeriodicExtend v x + oddPeriodicExtend w x := by
  simp only [oddPeriodicExtend_eq, oddReflect_add]

/-- The extension is homogeneous in `v`. -/
theorem oddPeriodicExtend_smul (a : ℝ) (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    oddPeriodicExtend (a • v) x = a * oddPeriodicExtend v x := by
  simp only [oddPeriodicExtend_eq, oddReflect_smul]

/-- The extension is bounded by `‖v‖`. -/
theorem abs_oddPeriodicExtend_le (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    |oddPeriodicExtend v x| ≤ ‖v‖ := by
  rw [oddPeriodicExtend_eq]
  exact abs_oddReflect_le _

/-- The odd reflection vanishes at `-π` when `v π = 0`. -/
theorem oddReflect_neg_pi (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) :
    oddReflect v (-π) = 0 := by
  rw [oddReflect_of_neg_mem (by rw [neg_neg]; exact right_mem_Icc.2 Real.pi_pos.le)
    (neg_neg_iff_pos.2 Real.pi_pos)]
  simp only [neg_neg, neg_eq_zero]
  convert hπ

/-- The extension vanishes at `π` when `v π = 0`. -/
theorem oddPeriodicExtend_pi (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) :
    oddPeriodicExtend v π = 0 := by
  rw [show π = -π + 2 * π by ring, oddPeriodicExtend_periodic,
    oddPeriodicExtend_of_mem_Ico ⟨le_rfl, by linarith [Real.pi_pos]⟩, oddReflect_neg_pi hπ]

/-- The extension agrees with `v` on `[0, π]`. -/
theorem oddPeriodicExtend_of_mem (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) π) : oddPeriodicExtend v x = v ⟨x, hx⟩ := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [oddPeriodicExtend_pi hπ]
    exact hπ.symm
  · rw [oddPeriodicExtend_of_mem_Ico ⟨by linarith [hx.1, Real.pi_pos], hlt⟩, oddReflect_of_mem hx]

/-- The extension is continuous when `v` vanishes at both ends. -/
theorem continuous_oddPeriodicExtend (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0)
    (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) : Continuous (oddPeriodicExtend v) := by
  refine (AddCircle.liftIco_continuous ?_ (continuous_oddReflect h0).continuousOn).comp
    (AddCircle.continuous_mk' _)
  rw [show -π + 2 * π = π by ring, oddReflect_neg_pi hπ, oddReflect_of_mem (right_mem_Icc.2
    Real.pi_pos.le), hπ]

/-- The extension is odd when `v` vanishes at both ends. -/
theorem oddPeriodicExtend_neg (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0)
    (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) (x : ℝ) :
    oddPeriodicExtend v (-x) = -oddPeriodicExtend v x := by
  -- the sum `x ↦ u (-x) + u x` is periodic and vanishes on `[-π, π)`, hence everywhere
  set g : ℝ → ℝ := fun x => oddPeriodicExtend v (-x) + oddPeriodicExtend v x with hg
  have hgp : Function.Periodic g (2 * π) := by
    intro y
    simp only [hg, neg_add, oddPeriodicExtend_periodic v y]
    rw [show -y + -(2 * π) = -y - 2 * π by ring, (oddPeriodicExtend_periodic v).sub_eq]
  have hg0 : ∀ y ∈ Ico (-π) π, g y = 0 := by
    intro y hy
    simp only [hg]
    rcases eq_or_lt_of_le hy.1 with rfl | hlt
    · rw [neg_neg, oddPeriodicExtend_pi hπ, oddPeriodicExtend_of_mem_Ico hy, oddReflect_neg_pi hπ,
        add_zero]
    · rw [oddPeriodicExtend_of_mem_Ico hy, oddPeriodicExtend_of_mem_Ico
        ⟨by linarith [hy.2], by linarith⟩, oddReflect_neg h0, neg_add_cancel]
  obtain ⟨y, hy, hxy⟩ := hgp.exists_mem_Ico Real.two_pi_pos x (-π)
  rw [show -π + 2 * π = π by ring] at hy
  have : g x = 0 := hxy.trans (hg0 y hy)
  simp only [hg] at this
  linarith

/-- **An odd `2π`-periodic function is determined by its values on `[0, π]`.** -/
theorem eq_of_odd_of_periodic_of_eqOn_Icc {f g : ℝ → ℝ} (hfo : ∀ x, f (-x) = -f x)
    (hgo : ∀ x, g (-x) = -g x) (hfp : Function.Periodic f (2 * π))
    (hgp : Function.Periodic g (2 * π)) (h : ∀ x ∈ Icc (0 : ℝ) π, f x = g x) : f = g := by
  funext x
  obtain ⟨n, hn, -⟩ := existsUnique_add_zsmul_mem_Ico Real.two_pi_pos x (-π)
  rw [← hfp.zsmul n x, ← hgp.zsmul n x]
  set y := x + n • (2 * π)
  rcases le_or_gt 0 y with hy | hy
  · exact h y ⟨hy, by linarith [hn.2]⟩
  · rw [← neg_neg y, hfo, hgo, h (-y) ⟨by linarith, by linarith [hn.1]⟩]

/-- The sine polynomial vanishes at `0`. -/
theorem sinePolynomial_zero_apply (n : ℕ) (c : ℕ → ℝ) :
    sinePolynomial n c ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0 := by
  simp [sinePolynomial_apply]

/-- The sine polynomial vanishes at `π`. -/
theorem sinePolynomial_pi_apply (n : ℕ) (c : ℕ → ℝ) :
    sinePolynomial n c ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0 := by
  rw [sinePolynomial_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show ((j : ℝ) + 1) * π = ((j + 1 : ℕ) : ℝ) * π by push_cast; ring, Real.sin_nat_mul_pi,
    mul_zero]

/-- The odd periodic extension of a sine polynomial is the sine polynomial itself, on the
whole line. -/
theorem oddPeriodicExtend_sinePolynomial (n : ℕ) (c : ℕ → ℝ) :
    oddPeriodicExtend (sinePolynomial n c)
      = fun x => ∑ j ∈ range n, c j * Real.sin (((j : ℝ) + 1) * x) := by
  have h0 := sinePolynomial_zero_apply n c
  have hπ := sinePolynomial_pi_apply n c
  refine eq_of_odd_of_periodic_of_eqOn_Icc (oddPeriodicExtend_neg h0 hπ) (fun x => ?_)
    (oddPeriodicExtend_periodic _) (fun x => ?_) (fun x hx => ?_)
  · simp only [mul_neg, Real.sin_neg, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((j : ℝ) + 1) * (x + 2 * π) = ((j : ℝ) + 1) * x + ((j + 1 : ℕ) : ℝ) * (2 * π) by
      push_cast; ring, Real.sin_add_nat_mul_two_pi]
  · rw [oddPeriodicExtend_of_mem hπ hx, sinePolynomial_apply]

end OddPeriodicExtend

/-! ### The density of the sine polynomials in `C₀[0, π]` -/

section Density

open Submodule

/-- The odd part of a continuous function on the circle of circumference `2π`, restricted to
`[0, π]`: `P ↦ (P x - P (-x)) / 2`. -/
private noncomputable def oddPartRestrict :
    C(AddCircle (2 * π), ℝ) →ₗ[ℝ] C(Icc (0 : ℝ) π, ℝ) where
  toFun P := ⟨fun x =>
    (P ((x : ℝ) : AddCircle (2 * π)) - P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))) / 2, by fun_prop⟩
  map_add' P Q := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
    ring
  map_smul' a P := by
    ext x
    simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.coe_mk, RingHom.id_apply]
    ring

private theorem oddPartRestrict_apply (P : C(AddCircle (2 * π), ℝ)) (x : Icc (0 : ℝ) π) :
    oddPartRestrict P x
      = (P ((x : ℝ) : AddCircle (2 * π)) - P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))) / 2 := rfl

/-- The odd part does not increase the uniform norm. -/
private theorem norm_oddPartRestrict_le (P : C(AddCircle (2 * π), ℝ)) :
    ‖oddPartRestrict P‖ ≤ ‖P‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  rw [oddPartRestrict_apply, Real.norm_eq_abs, abs_div, abs_two, div_le_iff₀ two_pos]
  calc |P ((x : ℝ) : AddCircle (2 * π)) - P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))|
      ≤ |P ((x : ℝ) : AddCircle (2 * π))| + |P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))| :=
        abs_sub _ _
    _ ≤ ‖P‖ + ‖P‖ := add_le_add (P.norm_coe_le_norm _) (P.norm_coe_le_norm _)
    _ = ‖P‖ * 2 := by ring

/-- The odd part of a real trigonometric polynomial on the circle is a sine polynomial. -/
private theorem oddPartRestrict_trigFun_mem (m : ℤ) :
    oddPartRestrict (trigFun (2 * π) m) ∈ span ℝ (range sinMap) := by
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have hmem : (√2 : ℝ) • sinMap (m.natAbs - 1) ∈ span ℝ (range sinMap) :=
      Submodule.smul_mem _ _ (subset_span ⟨_, rfl⟩)
    convert hmem using 1
    ext x
    rw [oddPartRestrict_apply, trigFun_coe_of_neg hm, trigFun_coe_of_neg hm,
      ContinuousMap.smul_apply, sinMap_apply, smul_eq_mul]
    have hcast : ((m.natAbs - 1 : ℕ) : ℝ) + 1 = -(m : ℝ) := by
      have h1 : 1 ≤ m.natAbs := Int.natAbs_pos.2 hm.ne
      rw [Nat.cast_sub h1, Nat.cast_one, sub_add_cancel, Nat.cast_natAbs, Int.cast_abs,
        abs_of_neg (by exact_mod_cast hm)]
    rw [hcast, mul_neg, Real.sin_neg]
    ring
  · have h0 : oddPartRestrict (trigFun (2 * π) 0) = 0 := by
      ext x
      rw [oddPartRestrict_apply, trigFun_zero]
      simp
    rw [h0]
    exact Submodule.zero_mem _
  · have h0 : oddPartRestrict (trigFun (2 * π) m) = 0 := by
      ext x
      rw [oddPartRestrict_apply, trigFun_coe_of_pos hm, trigFun_coe_of_pos hm]
      simp only [mul_neg, Real.cos_neg, sub_self, zero_div, ContinuousMap.zero_apply]
    rw [h0]
    exact Submodule.zero_mem _

/-- **The sine polynomials are uniformly dense in `C₀[0, π]`**: a continuous function on `[0, π]`
vanishing at both ends is uniformly within `ε` of a sine polynomial, for every `ε > 0`.
The odd `2π`-periodic extension is a continuous function on the circle, hence uniformly
approximable by a real trigonometric polynomial, whose odd part is a sine polynomial as close to
the (odd) target. This is [han2009theoretical] Exercise 6.2.1. -/
theorem exists_mem_span_sinMap_norm_sub_lt {v : C(Icc (0 : ℝ) π, ℝ)}
    (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0)
    (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ span ℝ (range sinMap), ‖v - p‖ < ε := by
  set F : C(AddCircle (2 * π), ℝ) := ⟨AddCircle.liftIco (2 * π) (-π) (oddReflect v), by
    refine AddCircle.liftIco_continuous ?_ (continuous_oddReflect h0).continuousOn
    rw [show -π + 2 * π = π by ring, oddReflect_neg_pi hπ,
      oddReflect_of_mem (right_mem_Icc.2 Real.pi_pos.le), hπ]⟩ with hF
  have hFx : ∀ x : ℝ, F (x : AddCircle (2 * π)) = oddPeriodicExtend v x := fun x => rfl
  obtain ⟨P, hP, hPF⟩ := exists_mem_span_trigFun_norm_sub_lt F hε
  refine ⟨oddPartRestrict P, ?_, ?_⟩
  · have hle : span ℝ (range (trigFun (2 * π)))
        ≤ (span ℝ (range sinMap)).comap oddPartRestrict :=
      span_le.2 (range_subset_iff.2 fun m => oddPartRestrict_trigFun_mem m)
    exact hle hP
  · have hFv : oddPartRestrict F = v := by
      ext x
      rw [oddPartRestrict_apply, hFx, hFx, oddPeriodicExtend_neg h0 hπ,
        oddPeriodicExtend_of_mem hπ x.2]
      ring
    calc ‖v - oddPartRestrict P‖ = ‖oddPartRestrict (F - P)‖ := by rw [map_sub, hFv]
      _ ≤ ‖F - P‖ := norm_oddPartRestrict_le _
      _ < ε := by rwa [norm_sub_rev]

end Density

end
