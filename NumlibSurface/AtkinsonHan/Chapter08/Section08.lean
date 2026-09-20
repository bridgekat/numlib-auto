import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.Zero
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.Variational.PLaplacianEnergy
import NumlibSurface.AtkinsonHan.Chapter03.Section03
import NumlibSurface.AtkinsonHan.Chapter05.Section03

/-!
# Atkinson–Han §8.8: a nonlinear problem

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.8.

The section studies the boundary value problem `−div [(1 + |∇u|²)^{p/2 − 1} ∇u] = f` in `Ω`,
`u = 0` on `Γ` (8.8.1)–(8.8.2), `1 < p < ∞`, through its weak formulation (8.8.6),
`a(u; u, v) = ℓ(v)` for all `v ∈ V`, and the minimization problem (8.8.9) of the energy
`E(v) = (1/p) ∫_Ω (1 + |∇v|²)^{p/2} − ℓ(v)` (8.8.10) on `V = W_0^{1,p}(Ω)`.

## The setting

`Ω ⊆ B(0, R) ⊆ ℝ^{d+1}` is a bounded open set (the book writes `ℝ^d`; the dimension is written
`d + 1` because the backbone's Poincaré inequality is), `p : ℝ≥0∞` with `1 < p < ∞`, and

* `V = W_0^{1,p}(Ω)` is the backbone's `SobolevEuclideanZero (d + 1) 1 p Ω`, the closure of
  `C_0^∞(Ω)` in the `W^{1,p}(Ω)` of the multi-index formulation of Definition 7.2.2, carrying the
  `W^{1,p}` norm `‖·‖_{1,p}`; the AH surface's `AtkinsonHan.Chapter07.definition_7_2_9 1 p Ω` is
  the same closure in the tensor formulation, whose norm is equivalent but not equal;
* `∇v : Ω → ℝ^{d+1}`, the gradient as a vector-valued function `x ↦ (∂ᵢv(x))ᵢ`, is the
  backbone's `SobolevMultiIndex.gradFn v`, with its `L^p` membership and the comparison of the
  Euclidean and `ℓ^p` gradient norms in `Numlib/Analysis/Sobolev/Cutoff.lean`;
* `normV v = ‖v‖_V = (∫_Ω |∇v|^p)^{1/p}` is the norm (8.8.5), and `energyFunctional f`,
  `formA` are `E` and the form `a(w; u, v) = ∫_Ω (1 + |∇w|²)^{p/2 − 1} ∇u · ∇v` of (8.8.7);
* `f ∈ V'` is any element of the dual `StrongDual ℝ V` — the book's `V' = W^{-1,p*}(Ω)`, and its
  `ℓ(v) = ∫ f v` is `f v`.

## The two norms

The book takes `‖·‖_V` as the norm of `V` and states its equivalence with `‖·‖_{1,p}` as
Exercise 8.8.1; the type `V` carries `‖·‖_{1,p}`, and the equivalence is here as
`normV_le` and `norm_le_normV` (Poincaré's inequality, `SobolevEuclideanZero.norm_le_gradNorm` of
`Numlib/Analysis/Sobolev/Poincare.lean`, together with the comparison of the Euclidean norm of
`∇v` with the `ℓ^p` norm of its components), so that every topological statement — coercivity,
continuity, reflexivity — is the same for either norm.  This is the cheaper of the two options
(a `NormedAddCommGroup` instance on a type synonym would have to redo the completeness and
reflexivity of `V`); the constants are explicit but not sharp.

## Main results

* `lemma_8_8_1` — coercivity: `E(v) ≥ (1/p) ‖v‖_V^p − C ‖v‖_V`, hence `E(v) → ∞` as
  `‖v‖_V → ∞` (`IsCoerciveFunctionalOn`);
* `lemma_8_8_2` — continuity, from the convexity of `E` and its local boundedness
  (`ConvexOn.continuousOn_tfae`), rather than the book's mean-value estimate;
* `lemma_8_8_3` — strict convexity, from the strict convexity of `ξ ↦ (1 + |ξ|²)^{p/2}`
  (`PLaplacian.strictConvexOn_kernel`, the book's Exercise 5.3.13) and Poincaré's inequality
  (`∇u = ∇v` a.e. forces `u = v`);
* `lemma_8_8_4` — the Gâteaux derivative (8.8.11), `⟨E'(u), v⟩ = a(u; u, v) − ℓ(v)`, by dominated
  convergence (`PLaplacian.hasDerivAt_energy_line`), `E'(u)` being the bounded functional
  `energyDeriv f u` built from the `L^p`–`L^{p'}` pairing `MeasureTheory.Lp.toDualCLM`;
* `theorem_8_8_5` — the weak formulation (8.8.6) and the minimization problem (8.8.9) are
  equivalent and both have a unique solution, for every `p ∈ (1, ∞)`: Theorem 3.3.12 on the
  reflexive space `V` (`SobolevMultiIndexZero.instIsReflexive`, from the reflexivity of `L^p`)
  and Theorem 5.3.19.

The analysis of the integral term with the gradient abstracted away is the backbone module
`Numlib/Variational/PLaplacianEnergy.lean`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter08

open SobolevMultiIndex

/-! ### The space `V`, its norm (8.8.5), the energy (8.8.10) and the form (8.8.7) -/

section Energy

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The norm (8.8.5)**, `‖v‖_V = (∫_Ω |∇v|^p)^{1/p}` on `V = W_0^{1,p}(Ω)`, with the Euclidean
norm of the gradient. -/
noncomputable def normV (v : SobolevEuclideanZero (d + 1) 1 p Ω) : ℝ :=
  (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
    ‖gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) x‖ ^ p.toReal) ^ (1 / p.toReal)

/-- **The energy functional (8.8.10)**, `E(v) = (1/p) ∫_Ω (1 + |∇v|²)^{p/2} − ℓ(v)`, for
`ℓ = f ∈ V'`: the backbone's `PLaplacian.energy` of the gradient. -/
noncomputable def energyFunctional (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) : ℝ :=
  (1 / p.toReal) * PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) - f v

/-- **The form (8.8.7)**, `a(w; u, v) = ∫_Ω (1 + |∇w|²)^{p/2 − 1} ∇u · ∇v`. -/
noncomputable def formA (w u v : SobolevEuclideanZero (d + 1) 1 p Ω) : ℝ :=
  ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
    PLaplacian.derivWeight p.toReal (gradFn (w : SobolevEuclidean (d + 1) 1 p Ω) x)
      * ⟪gradFn (u : SobolevEuclidean (d + 1) 1 p Ω) x,
          gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) x⟫_ℝ

variable {Ω}

/-- `‖v‖_V ≥ 0`. -/
theorem normV_nonneg (v : SobolevEuclideanZero (d + 1) 1 p Ω) : 0 ≤ normV Ω v :=
  Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- `‖v‖_V^p = ∫_Ω |∇v|^p`. -/
theorem normV_rpow (hp' : p ≠ ⊤) (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    normV Ω v ^ p.toReal = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ‖gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) x‖ ^ p.toReal := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  rw [normV, ← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hpr.ne', Real.rpow_one]

/-- **Exercise 8.8.1, one half**: `‖v‖_V ≤ (d + 1) ‖v‖_{1,p}`. -/
theorem normV_le (hp' : p ≠ ⊤) (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    normV Ω v ≤ (d + 1 : ℝ) * ‖v‖ := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  have h1 := integral_norm_gradFn_rpow_le hp' (v : SobolevEuclidean (d + 1) 1 p Ω)
  simp only [Fintype.card_fin] at h1
  have h2 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) ≤ ‖v‖ :=
    SobolevMultiIndex.gradNorm_le_norm _
  rw [← normV_rpow hp'] at h1
  have h3 : normV Ω v ^ p.toReal ≤ ((d + 1 : ℝ) * ‖v‖) ^ p.toReal := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
    refine h1.trans ?_
    push_cast
    gcongr
    exact SobolevMultiIndex.gradNorm_nonneg _
  exact (Real.rpow_le_rpow_iff (normV_nonneg v) (by positivity) hpr).1 h3

/-- **Exercise 8.8.1, the other half — Poincaré's inequality**: for `Ω ⊆ B(0, R)`,
`‖v‖_{1,p} ≤ (1 + (2R)^p)^{1/p} (d + 1)^{1/p} ‖v‖_V`. -/
theorem norm_le_normV (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    ‖v‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * (d + 1 : ℝ) ^ (1 / p.toReal)
      * normV Ω v := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  have hP := SobolevEuclideanZero.norm_le_gradNorm hp' hR hΩ v
  have h1 := gradNorm_rpow_le_integral hp' (v : SobolevEuclidean (d + 1) 1 p Ω)
  simp only [Fintype.card_fin] at h1
  rw [← normV_rpow hp'] at h1
  have h2 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω)
      ≤ (d + 1 : ℝ) ^ (1 / p.toReal) * normV Ω v := by
    have h3 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal
        ≤ ((d + 1 : ℝ) ^ (1 / p.toReal) * normV Ω v) ^ p.toReal := by
      rw [Real.mul_rpow (by positivity) (normV_nonneg v), ← Real.rpow_mul (by positivity),
        one_div_mul_cancel hpr.ne', Real.rpow_one]
      exact_mod_cast h1
    exact (Real.rpow_le_rpow_iff (SobolevMultiIndex.gradNorm_nonneg _)
      (mul_nonneg (by positivity) (normV_nonneg v)) hpr).1 h3
  calc ‖v‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal)
        * SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) := hP
    _ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * ((d + 1 : ℝ) ^ (1 / p.toReal) * normV Ω v) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end Energy

/-! ### Lemmas 8.8.1–8.8.3: coercivity, continuity, strict convexity -/

section Lemmas

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Poincaré's inequality as injectivity of the gradient**: `u, v ∈ W_0^{1,p}(Ω)` with
`∇u = ∇v` almost everywhere are equal, `Ω` being bounded. -/
theorem eq_of_gradFn_ae_eq (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {u v : SobolevEuclideanZero (d + 1) 1 p Ω}
    (h : gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) : u = v := by
  have h0 : gradFn ((u - v : SobolevEuclideanZero (d + 1) 1 p Ω) : SobolevEuclidean (d + 1) 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 0 := by
    filter_upwards [gradFn_sub (u : SobolevEuclidean (d + 1) 1 p Ω) v, h] with x h1 h2
    rw [Submodule.coe_sub, h1, Pi.sub_apply, h2, sub_self, Pi.zero_apply]
  have hg := gradNorm_eq_zero_of_gradFn_ae_eq_zero hp' h0
  have hP := SobolevEuclideanZero.norm_le_gradNorm hp' hR hΩ (u - v)
  rw [hg, mul_zero] at hP
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hP)

/-- **Lemma 8.8.1 (coercivity)**: on a bounded open `Ω ⊆ B(0, R)`, for `1 < p < ∞` and
`f ∈ V'`, the energy (8.8.10) satisfies `E(v) ≥ (1/p) ‖v‖_V^p − C ‖v‖_V` for a constant `C`
(the book's `‖f‖_{V'}`, here `‖f‖` times the constant of Poincaré's inequality), and is therefore
coercive: `E(v) → ∞` as `‖v‖ → ∞` (`IsCoerciveFunctionalOn`, Definition 3.3.9; the two norms
being equivalent, in either of them).  The bound `(1/p) ∫ |∇v|^p ≤ (1/p) ∫ (1 + |∇v|²)^{p/2}` is
`PLaplacian.integral_norm_rpow_le_energy`. -/
theorem lemma_8_8_1 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    (∃ C : ℝ, ∀ v, (1 / p.toReal) * normV Ω v ^ p.toReal - C * normV Ω v
      ≤ energyFunctional Ω f v) ∧
    IsCoerciveFunctionalOn (energyFunctional Ω f) univ := by
  have hpr : 1 < p.toReal := PLaplacian.one_lt_toReal hp hp'
  have hpr0 : 0 < p.toReal := by linarith
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  -- the constant of Poincaré's inequality
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 < K ∧ ∀ v : SobolevEuclideanZero (d + 1) 1 p Ω,
      ‖v‖ ≤ K * normV Ω v :=
    ⟨_, by positivity, fun v ↦ norm_le_normV hp' hR hΩ v⟩
  have hlow : ∀ v : SobolevEuclideanZero (d + 1) 1 p Ω,
      (1 / p.toReal) * normV Ω v ^ p.toReal - (‖f‖ * K) * normV Ω v ≤ energyFunctional Ω f v := by
    intro v
    have h1 : normV Ω v ^ p.toReal ≤ PLaplacian.energy p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) := by
      rw [normV_rpow hp']
      exact PLaplacian.integral_norm_rpow_le_energy hp.le hp' (memLp_gradFn _)
    have h2 : f v ≤ ‖f‖ * K * normV Ω v := by
      calc f v ≤ ‖f v‖ := Real.le_norm_self _
        _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
        _ ≤ ‖f‖ * (K * normV Ω v) := mul_le_mul_of_nonneg_left (hK v) (norm_nonneg _)
        _ = ‖f‖ * K * normV Ω v := by ring
    unfold energyFunctional
    have h3 : (1 / p.toReal) * normV Ω v ^ p.toReal ≤ (1 / p.toReal) * PLaplacian.energy p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  refine ⟨⟨‖f‖ * K, hlow⟩, ?_⟩
  -- coercivity in the `W^{1,p}` norm
  refine isCoerciveFunctionalOn_of_rpow_sub_mul_le (c := 1 / (p.toReal * K ^ p.toReal))
    (C := ‖f‖) (by positivity) hpr fun v _ ↦ ?_
  have h4 : ‖v‖ ^ p.toReal ≤ K ^ p.toReal * normV Ω v ^ p.toReal := by
    rw [← Real.mul_rpow hK0.le (normV_nonneg v)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hK v) hpr0.le
  have h5 : 1 / (p.toReal * K ^ p.toReal) * ‖v‖ ^ p.toReal
      ≤ (1 / p.toReal) * normV Ω v ^ p.toReal := by
    have hKp : 0 < K ^ p.toReal := by positivity
    calc 1 / (p.toReal * K ^ p.toReal) * ‖v‖ ^ p.toReal
        ≤ 1 / (p.toReal * K ^ p.toReal) * (K ^ p.toReal * normV Ω v ^ p.toReal) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (1 / p.toReal) * normV Ω v ^ p.toReal := by
          field_simp
  have h6 : f v ≤ ‖f‖ * ‖v‖ := (Real.le_norm_self _).trans (f.le_opNorm v)
  have h7 : normV Ω v ^ p.toReal ≤ PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) := by
    rw [normV_rpow hp']
    exact PLaplacian.integral_norm_rpow_le_energy hp.le hp' (memLp_gradFn _)
  have h8 : (1 / p.toReal) * normV Ω v ^ p.toReal ≤ (1 / p.toReal) * PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
    mul_le_mul_of_nonneg_left h7 (by positivity)
  unfold energyFunctional
  linarith

/-- `v ↦ c Φ(v) − f(v)` is convex when `c ≥ 0`, `f` is linear and `Φ` satisfies the convexity
inequality; stated abstractly so that the typed Sobolev instance is a single application. -/
theorem convexOn_const_mul_sub_of_forall {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : V → ℝ} (f : V →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hΦ : ∀ u v : V, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      Φ (a • u + b • v) ≤ a * Φ u + b * Φ v) :
    ConvexOn ℝ univ fun v ↦ c * Φ v - f v := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  have hf : f (a • u + b • v) = a * f u + b * f v := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [hf]
  nlinarith [mul_le_mul_of_nonneg_left (hΦ u v a b ha hb hab) hc]

/-- `v ↦ c Φ(v) − f(v)` is strictly convex when `c > 0`, `f` is linear and `Φ` satisfies the
strict convexity inequality; stated abstractly so that the typed Sobolev instance is a single
application. -/
theorem strictConvexOn_const_mul_sub_of_forall {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {Φ : V → ℝ} (f : V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hΦ : ∀ u v : V, u ≠ v → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      Φ (a • u + b • v) < a * Φ u + b * Φ v) :
    StrictConvexOn ℝ univ fun v ↦ c * Φ v - f v := by
  refine ⟨convex_univ, fun u _ v _ huv a b ha hb hab ↦ ?_⟩
  have hf : f (a • u + b • v) = a * f u + b * f v := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [hf]
  nlinarith [mul_lt_mul_of_pos_left (hΦ u v huv a b ha hb hab) hc]

/-- **The energy is convex** (the non-strict half of Lemma 8.8.3): the convexity of the kernel
`ξ ↦ (1 + |ξ|²)^{p/2}` under the integral (`PLaplacian.energy_combo_le`), the gradient being
linear (`gradFn_combo`). -/
theorem convexOn_energyFunctional (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    ConvexOn ℝ univ (energyFunctional Ω f) := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  refine convexOn_const_mul_sub_of_forall f (by positivity) fun u v a b ha hb hab ↦ ?_
  calc PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn ((a • u + b • v : SobolevEuclideanZero (d + 1) 1 p Ω) :
          SobolevEuclidean (d + 1) 1 p Ω))
      = PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (a • gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
          + b • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
        PLaplacian.energy_congr_ae p (gradFn_combo a b (u : SobolevEuclidean (d + 1) 1 p Ω) v)
    _ ≤ _ := PLaplacian.energy_combo_le (p := p) Fact.out hp'
        (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
        (memLp_gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) ha hb hab

/-- **Lemma 8.8.3 (strict convexity)**: on a bounded open `Ω ⊆ B(0, R)`, for `1 < p < ∞`, the
energy (8.8.10) is strictly convex.  The strict convexity of `ξ ↦ (1/p)(1 + |ξ|²)^{p/2}` on
`ℝ^{d+1}` (Exercise 5.3.13, `PLaplacian.strictConvexOn_kernel`) gives a strict inequality under
the integral wherever `∇u ≠ ∇v` (`PLaplacian.energy_combo_lt`), and `∇u = ∇v` almost
everywhere forces `u = v` by Poincaré's inequality (`eq_of_gradFn_ae_eq`). -/
theorem lemma_8_8_3 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    StrictConvexOn ℝ univ (energyFunctional Ω f) := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  have hpr : 0 < 1 / p.toReal := by
    have := PLaplacian.one_lt_toReal hp hp'
    positivity
  refine strictConvexOn_const_mul_sub_of_forall f hpr fun u v huv a b ha hb hab ↦ ?_
  have hne : ¬ gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) :=
    fun h ↦ huv (eq_of_gradFn_ae_eq hp' hR hΩ h)
  calc PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn ((a • u + b • v : SobolevEuclideanZero (d + 1) 1 p Ω) :
          SobolevEuclidean (d + 1) 1 p Ω))
      = PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (a • gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
          + b • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
        PLaplacian.energy_congr_ae p (gradFn_combo a b (u : SobolevEuclidean (d + 1) 1 p Ω) v)
    _ < _ := PLaplacian.energy_combo_lt hp hp'
        (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
        (memLp_gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) hne ha hb hab

/-- **The energy is bounded above on bounded sets**: `E(v) ≤ (1/p) 2^p (|Ω| + (d+1)^p ‖v‖^p)
+ ‖f‖ ‖v‖` (`PLaplacian.energy_le` and `integral_norm_gradFn_rpow_le`). -/
theorem energyFunctional_le (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    energyFunctional Ω f v ≤ (1 / p.toReal) * (2 ^ p.toReal
      * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).real univ
        + (d + 1 : ℝ) ^ p.toReal * ‖v‖ ^ p.toReal)) + ‖f‖ * ‖v‖ := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  have hpr : 0 ≤ 1 / p.toReal := by positivity
  have h1 := PLaplacian.energy_le (p := p) Fact.out hp'
    (memLp_gradFn (v : SobolevEuclidean _ 1 p Ω))
  have h2 := integral_norm_gradFn_rpow_le hp' (v : SobolevEuclidean (d + 1) 1 p Ω)
  simp only [Fintype.card_fin] at h2
  have h3 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal
      ≤ ‖v‖ ^ p.toReal :=
    Real.rpow_le_rpow (SobolevMultiIndex.gradNorm_nonneg _)
      (SobolevMultiIndex.gradNorm_le_norm _) ENNReal.toReal_nonneg
  have h4 : -(f v) ≤ ‖f‖ * ‖v‖ := by
    have := f.le_opNorm v
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (f v)]
  have h5 : PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) ≤ 2 ^ p.toReal
      * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).real univ
        + (d + 1 : ℝ) ^ p.toReal * ‖v‖ ^ p.toReal) := by
    refine h1.trans ?_
    gcongr
    refine h2.trans ?_
    push_cast
    gcongr
  unfold energyFunctional
  nlinarith [mul_le_mul_of_nonneg_left h5 hpr]

/-- **Lemma 8.8.2 (continuity)**: on a bounded open `Ω ⊆ B(0, R)`, for `1 ≤ p < ∞`, the energy
(8.8.10) is continuous on `V`.  The book estimates `|E(v) − E(u)|` by a mean-value argument and
Hölder's inequality; here continuity follows from the convexity of `E`
(`convexOn_energyFunctional`) and its boundedness on balls (`energyFunctional_le`), a convex
function bounded above near every point being continuous (`ConvexOn.continuousOn_tfae`). -/
theorem lemma_8_8_2 (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    Continuous (energyFunctional Ω f) := by
  rw [← continuousOn_univ]
  refine ((convexOn_energyFunctional hp' hΩ f).continuousOn_tfae isOpen_univ univ_nonempty).out 5 2
    |>.1 fun x₀ _ ↦ ?_
  refine ⟨(1 / p.toReal) * (2 ^ p.toReal
      * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).real univ
        + (d + 1 : ℝ) ^ p.toReal * (‖x₀‖ + 1) ^ p.toReal)) + ‖f‖ * (‖x₀‖ + 1), ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with v hv
  have hv1 : ‖v‖ ≤ ‖x₀‖ + 1 := by
    have := mem_ball_iff_norm.1 hv
    linarith [norm_le_norm_add_norm_sub' v x₀]
  refine (energyFunctional_le hp' hΩ f v).trans ?_
  gcongr

end Lemmas

/-! ### Lemma 8.8.4: the Gâteaux derivative (8.8.11) -/

section Gateaux

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

attribute [local instance] ENNReal.fact_one_le_conjExponent

/-- The weight `(1 + |∇u|²)^{p/2 − 1} ∂ᵢu ∈ L^{p'}(Ω)` of the derivative (8.8.11), as an element
of `L^{p'}(Ω)` (`PLaplacian.memLp_derivWeight_mul`). -/
noncomputable def weightedDeriv (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) (i : Fin (d + 1)) :
    Lp ℝ (ENNReal.conjExponent p) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  haveI := isFiniteMeasure_restrict_of_subset_ball hΩ
  (PLaplacian.memLp_derivWeight_mul hp hp' (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
    (Lp.aestronglyMeasurable (SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω)
      (MultiIndexLE.single i)))
    fun x ↦ by
      rw [← Real.norm_eq_abs]
      exact norm_le_norm_gradFn _ x i).toLp _

/-- The weight `(1 + |∇u|²)^{p/2 − 1} ∂ᵢu` as a function, almost everywhere. -/
theorem coeFn_weightedDeriv (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) (i : Fin (d + 1)) :
    (weightedDeriv hp hp' hΩ u i : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ PLaplacian.derivWeight p.toReal (gradFn (u : SobolevEuclidean (d + 1) 1 p Ω) x)
          * SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω)
            (MultiIndexLE.single i) x :=
  MemLp.coeFn_toLp _

/-- **The Gâteaux derivative `E'(u) ∈ V'` of (8.8.11)** as a bounded linear functional:
`v ↦ ∑ᵢ ∫_Ω (1 + |∇u|²)^{p/2 − 1} ∂ᵢu ∂ᵢv − ℓ(v)`, each term the `L^p`–`L^{p'}` pairing
`MeasureTheory.Lp.toDualCLM` of the weight `weightedDeriv u i ∈ L^{p'}(Ω)` with `∂ᵢv ∈ L^p(Ω)`.
Its value is `a(u; u, v) − ℓ(v)` (`energyDeriv_apply`). -/
noncomputable def energyDeriv (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω) :=
  (∑ i : Fin (d + 1), (Lp.toDualCLM ℝ p (ENNReal.conjExponent p)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (weightedDeriv hp hp' hΩ u i)).comp
    ((SobolevMultiIndex.weakDerivL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      (MultiIndexLE.single i)).comp (SobolevEuclideanZero (d + 1) 1 p Ω).subtypeL)) - f

/-- **`⟨E'(u), v⟩ = a(u; u, v) − ℓ(v)`**, the formula (8.8.11). -/
theorem energyDeriv_apply (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (u v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    energyDeriv hp hp' hΩ f u v = formA Ω u u v - f v := by
  have hint : ∀ i : Fin (d + 1), Integrable (fun x ↦ (weightedDeriv hp hp' hΩ u i : _ → ℝ) x
      * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 p Ω) (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun i ↦
    (Lp.memLp (weightedDeriv hp hp' hΩ u i)).integrable_mul (Lp.memLp _)
  have h1 : energyDeriv hp hp' hΩ f u v = (∑ i : Fin (d + 1),
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), (weightedDeriv hp hp' hΩ u i : _ → ℝ) x
        * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 p Ω)
          (MultiIndexLE.single i) x) - f v := by
    simp only [energyDeriv, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
      Lp.toDualCLM_apply]
    rfl
  rw [h1, formA, ← integral_finsetSum _ fun i _ ↦ hint i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun i ↦ coeFn_weightedDeriv hp hp' hΩ u i] with x hx
  simp only [hx, inner_gradFn, Finset.mul_sum, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- `(1/c) ∫ c a b − r = ∫ a b − r` for `c ≠ 0`; stated abstractly so that the typed Sobolev
instance is a single application. -/
theorem one_div_mul_integral_const_mul_mul_sub {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {c : ℝ} (hc : c ≠ 0) (a b : X → ℝ) (r : ℝ) :
    (1 / c) * (∫ x, c * a x * b x ∂μ) - r = (∫ x, a x * b x ∂μ) - r := by
  have e : (fun x ↦ c * a x * b x) = fun x ↦ c * (a x * b x) := by
    funext x
    ring
  rw [e, integral_const_mul]
  field_simp

/-- The derivative along a line of `v ↦ c Ψ(v) − f(v)` with `f` linear, from that of `Ψ`; stated
abstractly so that the typed Sobolev instance is a single application. -/
theorem hasDerivAt_line_of_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {E : V → ℝ}
    (f : V →L[ℝ] ℝ) {c : ℝ} {Ψ : ℝ → ℝ} {u v : V} {Ψ' : ℝ}
    (hE : ∀ t : ℝ, E (u + t • v) = c * Ψ t - f (u + t • v)) (hΨ : HasDerivAt Ψ Ψ' 0) :
    HasDerivAt (fun t : ℝ ↦ E (u + t • v)) (c * Ψ' - f v) 0 := by
  have hfun : (fun t : ℝ ↦ E (u + t • v)) = fun t ↦ c * Ψ t - (f u + t * f v) := by
    funext t
    rw [hE t, map_add, map_smul, smul_eq_mul]
  rw [hfun]
  have h := (hΨ.const_mul c).sub (((hasDerivAt_id (0 : ℝ)).const_mul (f v)).const_add (f u))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [Pi.sub_apply, id, mul_comm]
  · simp

/-- **Lemma 8.8.4 (Gâteaux differentiability)**: on a bounded open `Ω ⊆ B(0, R)`, for
`1 < p < ∞` and `f ∈ V'`, the energy (8.8.10) is Gâteaux differentiable at every `u ∈ V`, with
derivative `E'(u) = energyDeriv f u`,

  `⟨E'(u), v⟩ = ∫_Ω (1 + |∇u|²)^{p/2 − 1} ∇u · ∇v − ℓ(v)`   (8.8.11).

The difference quotient converges by dominated convergence with the dominating function
`[1 + (|∇u| + |∇v|)²]^{(p−1)/2} |∇v| ∈ L¹(Ω)` (`PLaplacian.hasDerivAt_energy_line`,
`PLaplacian.integrable_kernelBound_mul`), exactly as in the book. -/
theorem lemma_8_8_4 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) :
    Chapter05.HasGateauxDerivAt (energyFunctional Ω f) (energyDeriv hp hp' hΩ f u) u ∧
      ∀ v, energyDeriv hp hp' hΩ f u v = formA Ω u u v - f v := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  refine ⟨fun v ↦ ?_, energyDeriv_apply hp hp' hΩ f u⟩
  rw [energyDeriv_apply]
  -- the line `t ↦ E(u + t v)` is `t ↦ (1/p) Φ(∇u + t ∇v) − f(u + t v)`
  have hΦ : ∀ t : ℝ, PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn ((u + t • v : SobolevEuclideanZero (d + 1) 1 p Ω) : SobolevEuclidean (d + 1) 1 p Ω))
      = PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
          + t • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) := by
    intro t
    have hcoe : ((u + t • v : SobolevEuclideanZero (d + 1) 1 p Ω) : SobolevEuclidean (d + 1) 1 p Ω)
        = (u : SobolevEuclidean (d + 1) 1 p Ω) + t • (v : SobolevEuclidean (d + 1) 1 p Ω) := rfl
    rw [hcoe]
    refine PLaplacian.energy_congr_ae p ?_
    filter_upwards [gradFn_add (u : SobolevEuclidean (d + 1) 1 p Ω) (t • v),
      gradFn_smul t (v : SobolevEuclidean (d + 1) 1 p Ω)] with x h1 h2
    rw [h1, Pi.add_apply, h2]
    rfl
  have hE : ∀ t : ℝ, energyFunctional Ω f (u + t • v) = (1 / p.toReal) * PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
        + t • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) - f (u + t • v) := fun t ↦
    congrArg (fun z ↦ (1 / p.toReal) * z - f (u + t • v)) (hΦ t)
  have hD := PLaplacian.hasDerivAt_energy_line hp hp'
    (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
    (memLp_gradFn (v : SobolevEuclidean (d + 1) 1 p Ω))
  have key := hasDerivAt_line_of_eq f hE hD
  have hpr : 0 < p.toReal := by linarith [PLaplacian.one_lt_toReal hp hp']
  exact key.congr_deriv (one_div_mul_integral_const_mul_mul_sub hpr.ne' _ _ _)

end Gateaux

/-! ### Theorem 8.8.5: existence, uniqueness, and the equivalence of (8.8.6) and (8.8.9) -/

section Main

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A linear functional nonnegative on all the differences `v − w` vanishes identically; stated
abstractly so that the typed Sobolev instance is a single application. -/
theorem forall_nonneg_sub_iff_forall_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (w : V) : (∀ v, 0 ≤ L (v - w)) ↔ ∀ v, L v = 0 := by
  constructor
  · intro H v
    have h1 := H (v + w)
    have h2 := H (-v + w)
    rw [add_sub_cancel_right] at h1 h2
    rw [map_neg] at h2
    linarith
  · intro H v
    rw [H]

/-- **Theorem 8.8.5**: on a bounded open `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`, for `1 < p < ∞` and `f ∈ V'`,
the minimization problem (8.8.9) `u ∈ V`, `E(u) = inf_V E` has exactly one solution, it is
equivalent to the weak formulation (8.8.6) `u ∈ V`, `a(u; u, v) = ℓ(v)` for all `v ∈ V`, and so
(8.8.6) has exactly one solution as well.

Existence is Theorem 3.3.12 (`Chapter03.theorem_3_3_12`) on the reflexive space
`V = W_0^{1,p}(Ω)` — reflexive for every `1 < p < ∞` by `SobolevMultiIndexZero.instIsReflexive`
and the reflexivity of `L^p(Ω)` (`MeasureTheory.Lp.instIsReflexive`) — for the coercive
(Lemma 8.8.1), continuous (Lemma 8.8.2) energy, convex by Lemma 8.8.3; uniqueness is the strict
convexity of Lemma 8.8.3 (`IsMinOn.eq_of_strictConvexOn`); the equivalence is Theorem 5.3.19 in
its subspace form (`Chapter05.theorem_5_3_19_submodule`, on `K = V`) with the Gâteaux derivative
of Lemma 8.8.4: `u` minimizes `E` iff `⟨E'(u), v⟩ = a(u; u, v) − ℓ(v) = 0` for all `v`. -/
theorem theorem_8_8_5 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    (∃! u, IsMinOn (energyFunctional Ω f) univ u) ∧
    (∀ u, IsMinOn (energyFunctional Ω f) univ u ↔ ∀ v, formA Ω u u v = f v) ∧
    ∃! u : SobolevEuclideanZero (d + 1) 1 p Ω, ∀ v, formA Ω u u v = f v := by
  have : Fact (1 < p) := ⟨hp⟩
  have : Fact (p ≠ ⊤) := ⟨hp'⟩
  have hconv := convexOn_energyFunctional hp' hΩ f
  have hcont := lemma_8_8_2 hp' hΩ f
  have hcoer := (lemma_8_8_1 hp hp' hR hΩ f).2
  have hstrict := lemma_8_8_3 hp hp' hR hΩ f
  obtain ⟨u, -, humin⟩ := Chapter03.theorem_3_3_12 univ_nonempty isClosed_univ convex_univ hconv
    (hcont.lowerSemicontinuous.lowerSemicontinuousOn univ) (Or.inr hcoer)
  have huniq : ∀ w, IsMinOn (energyFunctional Ω f) univ w → w = u := fun w hw ↦
    IsMinOn.eq_of_strictConvexOn hstrict hw humin (mem_univ _) (mem_univ _)
  have hiff : ∀ w, IsMinOn (energyFunctional Ω f) univ w ↔ ∀ v, formA Ω w w v = f v := fun w ↦ by
    have h := Chapter05.theorem_5_3_19 (V := SobolevEuclideanZero (d + 1) 1 p Ω) (K := univ)
      (f := energyFunctional Ω f) (f' := fun w ↦ energyDeriv hp hp' hΩ f w)
      (fun w _ ↦ (lemma_8_8_4 hp hp' hΩ f w).1) hconv (mem_univ w)
    have h2 := forall_nonneg_sub_iff_forall_eq_zero (V := SobolevEuclideanZero (d + 1) 1 p Ω)
      (energyDeriv hp hp' hΩ f w) w
    refine h.trans ⟨fun H v ↦ ?_, fun H v _ ↦ ?_⟩
    · have := (h2.1 fun v ↦ H v (mem_univ v)) v
      rw [energyDeriv_apply] at this
      exact sub_eq_zero.1 this
    · refine h2.2 (fun v ↦ ?_) v
      rw [energyDeriv_apply]
      exact sub_eq_zero.2 (H v)
  exact ⟨⟨u, humin, huniq⟩, hiff, ⟨u, (hiff u).1 humin, fun w hw ↦ huniq w ((hiff w).2 hw)⟩⟩

end Main

end AtkinsonHan.Chapter08
