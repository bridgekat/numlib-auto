import Numlib.Analysis.PDE.DirichletLaplacian

/-!
# The obstacle problem: the Lewy–Stampacchia inequality and `H²` regularity

The obstacle problem for the Laplacian on a bounded open `Ω ⊆ ℝ^N`, with obstacle `ψ ∈ H¹(Ω)`
and load `f ∈ L²(Ω)`, is the variational inequality

`u ∈ K := {v ∈ H¹₀(Ω) : v ≥ ψ a.e.}`,  `∫_Ω ∇u · ∇(v − u) ≥ ∫_Ω f (v − u)` for all `v ∈ K`

([han2009theoretical] Example 11.1.1, Example 11.3.10; [brezis2011functional] Chapter 9,
Comments). Its solution has one more derivative than the variational setting shows: when the
obstacle has `−Δψ ∈ L²(Ω)`, the **Lewy–Stampacchia inequality** `f ≤ −Δu ≤ max (f, −Δψ)` holds,
so `−Δu ∈ L²(Ω)`, and on a `C²` domain the linear regularity theory
(`Elliptic.regularity_dirichlet`) gives `u ∈ H²(Ω)` with the bound
`‖u‖_{H²} ≤ C (‖f‖_{L²} + ‖Δψ‖_{L²} + ‖u‖_{L²})` — the `p = 2` case of
[han2009theoretical] Theorem 11.3.12 (Brezis–Stampacchia).

## The argument

* `Elliptic.IsObstacleSolution Ω ψ f u` is the variational inequality above, on `u ∈ H¹(Ω)`.
* The lower bound `f ≤ −Δu` (`Elliptic.IsObstacleSolution.load_le_dirichletForm`) is the
  inequality tested with `v = u + Φ`, `Φ ∈ H¹₀(Ω)`, `Φ ≥ 0`.
* The upper bound (`Elliptic.IsObstacleSolution.dirichletForm_le_load_sup`) is the classical
  truncation argument: for `Φ ∈ H¹₀(Ω)`, `Φ ≥ 0` and `ε > 0`, the admissible competitor
  `v = u − min (ε Φ, u − ψ) = max (u − ε Φ, ψ)` gives, with `z = u − ψ ≥ 0` and
  `−Δψ = q ∈ L²(Ω)`,

  `∫_Ω ∇z · ∇(min (ε Φ, z)) ≤ ∫_Ω (f − q) min (ε Φ, z) ≤ ε ∫_Ω (f − q)⁺ Φ`;

  the left side is `ε ∫_{z ≥ εΦ} ∇z · ∇Φ + ∫_{z < εΦ} |∇z|² ≥ ε ∫_{z ≥ εΦ} ∇z · ∇Φ`
  (`∇ min (a, b) = 1_{a ≤ b} ∇a + 1_{a > b} ∇b`, from `∇ w⁺ = 1_{w > 0} ∇w`), and as `ε ↓ 0` the
  set `{z ≥ εΦ}` fills `{z > 0}`, on whose complement `∇z = 0` (Stampacchia), so
  `∫_Ω ∇z · ∇Φ ≤ ∫_Ω (f − q)⁺ Φ`, i.e. `∫_Ω ∇u · ∇Φ ≤ ∫_Ω max (f, q) Φ`. The one delicate point is
  `min (ε Φ, z) ∈ H¹₀(Ω)`: it is `ε Φ − (ε Φ − z)⁺` with `0 ≤ (ε Φ − z)⁺ ≤ ε Φ`, and a function
  squeezed between `0` and an element of `H¹₀(Ω)` lies in `H¹₀(Ω)`
  (`SobolevEuclideanZero.mem_of_nonneg_of_le`, on a `C¹` chart domain: its extension by zero is
  `min (ṽ⁺, w̄)` with `ṽ` a Sobolev extension of the function and `w̄` the extension by zero of the
  majorant, hence lies in `H¹(ℝ^N)`, and Proposition 9.18 concludes).
* The two bounds make the functional `Φ ↦ ∫_Ω ∇u · ∇Φ − ∫_Ω f Φ` on `H¹₀(Ω)` nonnegative on the
  nonnegative `Φ` and dominated there by `∫_Ω (max (f, q) − f) Φ`, hence bounded by
  `2 ‖max (f, q) − f‖_{L²} ‖Φ‖_{L²}` on all of `H¹₀(Ω)` (`Φ = Φ⁺ − Φ⁻`); the Hahn–Banach and Riesz
  theorems represent it as `Φ ↦ ∫_Ω h Φ` with `h ∈ L²(Ω)`
  (`Elliptic.IsObstacleSolution.exists_dirichletForm_eq_load`), which is `−Δu = f + h ∈ L²(Ω)`.
* `Elliptic.regularity_obstacle`: on a `C²` chart domain with bounded boundary, `u ∈ H²(Ω)`
  with the bound.

## References

[han2009theoretical] Theorem 11.3.12 (quoted there from Brezis–Stampacchia and
Gilbarg–Trudinger); Kinderlehrer–Stampacchia, *An Introduction to Variational Inequalities and
Their Applications*, Chapter IV; Rodrigues, *Obstacle Problems in Mathematical Physics*, §5:4.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### A function squeezed between `0` and an `H¹₀` function lies in `H¹₀` -/

section Sandwich

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **A function squeezed between `0` and an element of `H¹₀(Ω)` lies in `H¹₀(Ω)`**, on a `C¹`
chart domain with bounded boundary: for `v ∈ H¹(Ω)` and `w ∈ H¹₀(Ω)` with `0 ≤ v ≤ w` almost
everywhere on `Ω`, `v ∈ H¹₀(Ω)`. The extension by zero of `v` is `min (ṽ⁺, w̄)`, where `ṽ` is a
Sobolev extension of `v` to `ℝ^N` (Theorem 9.7, `SobolevEuclidean.exists_extensionL`) and `w̄` the
extension by zero of `w` (`SobolevEuclideanZero.extendZeroL`), both in `H¹(ℝ^N)`, so it lies in
`H¹(ℝ^N)` (`MemSobolevMultiIndex.posPart`), and Proposition 9.18 (iii) ⇒ (i)
(`SobolevEuclideanZero.mem_of_indicator_memSobolev`) concludes. (Belongs beside
`SobolevEuclideanZero.mem_of_indicator_memSobolev` in `Numlib/Analysis/Sobolev/Zero.lean`.) -/
theorem SobolevEuclideanZero.mem_of_nonneg_of_le
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {v w : SobolevEuclidean (d + 1) 1 2 Ω} (hw : w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hv0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn v x)
    (hvw : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn v x ≤ fn w x) :
    v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω := by
  have hΩm := Ω.isOpen.measurableSet
  -- a Sobolev extension `ṽ` of `v`, and the extension by zero `w̄` of `w`
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL (p := 2) hΩ hΓ
  obtain ⟨V, hV⟩ : ∃ V : SobolevEuclidean (d + 1) 1 2 ⊤, V = P v := ⟨_, rfl⟩
  have hVv : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn v := by
    rw [hV]
    exact (hP v).1
  obtain ⟨W, hW⟩ : ∃ W : SobolevEuclidean (d + 1) 1 2 ⊤,
      W = SobolevEuclideanZero.extendZeroL (d + 1) 2 Ω ⟨w, hw⟩ := ⟨_, rfl⟩
  have hWw : fn W =ᵐ[volume] (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fn w) := by
    rw [hW]
    exact SobolevEuclideanZero.fn_extendZeroL _
  -- almost everywhere for `volume.restrict ⊤` is almost everywhere
  have htop : ∀ {q : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
      (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))).restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        q x) ↔ ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))), q x := by
    intro q
    rw [Opens.coe_top, Measure.restrict_univ]
  -- `A = ṽ⁺` and `Q = (A − w̄)⁺`, in `H¹(ℝ^N)`
  obtain ⟨A, hA⟩ := ((memSobolevMultiIndex V).posPart one_le_two).exists_sobolevMultiIndex
  obtain ⟨Q, hQ⟩ := ((memSobolevMultiIndex (A - W)).posPart one_le_two).exists_sobolevMultiIndex
  have hAW := Lp.coeFn_sub (weakDeriv A 0) (weakDeriv W 0)
  have hAQ := Lp.coeFn_sub (weakDeriv A 0) (weakDeriv Q 0)
  -- `A − Q = min (ṽ⁺, w̄)` is the extension by zero of `v`
  have hind : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))),
      fn (A - Q) x = (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fn v) x := by
    filter_upwards [htop.1 hAQ, htop.1 hA, htop.1 hQ, htop.1 hAW, hWw, (ae_restrict_iff' hΩm).1 hVv,
      (ae_restrict_iff' hΩm).1 hv0, (ae_restrict_iff' hΩm).1 hvw] with x h1 h2 h3 h4 h5 h6 h7 h8
    have e1 : fn (A - Q) x = fn A x - fn Q x := h1
    have e4 : fn (A - W) x = fn A x - fn W x := h4
    rw [e1, h3, e4, h2, h5]
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    · rw [indicator_of_mem hx, indicator_of_mem hx, h6 hx, max_eq_left (h7 hx),
        max_eq_right (by linarith [h8 hx]), sub_zero]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, sub_zero,
        max_eq_left (le_max_right _ _), sub_self]
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fn v)) 1 2 ⊤ volume :=
    (memSobolevMultiIndex (A - Q)).congr_ae (htop.2 hind)
  obtain ⟨v', hv', hvv'⟩ := SobolevEuclideanZero.mem_of_indicator_memSobolev (p := 2)
    (by norm_num) hΩ hmem
  rwa [SobolevMultiIndex.ext_of_fn_ae_eq hvv'.symm]

end Sandwich

namespace Elliptic

/-! ### The obstacle problem and the lower bound `f ≤ −Δu` -/

section Obstacle

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

open SobolevMultiIndex

/-- **A solution of the obstacle problem** with obstacle `ψ ∈ H¹(Ω)` and load `f ∈ L²(Ω)`:
`u ∈ H¹₀(Ω)`, `u ≥ ψ` almost everywhere, and `∫_Ω ∇u · ∇(v − u) ≥ ∫_Ω f (v − u)` for every
`v ∈ H¹₀(Ω)` with `v ≥ ψ` almost everywhere ([han2009theoretical] (11.1.7)). -/
structure IsObstacleSolution (ψ : SobolevEuclidean N 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : SobolevEuclidean N 1 2 Ω) : Prop where
  /-- `u ∈ H¹₀(Ω)`. -/
  mem_zero : u ∈ SobolevEuclideanZero N 1 2 Ω
  /-- `u ≥ ψ` almost everywhere on `Ω`. -/
  ae_le : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn ψ x ≤ fn u x
  /-- The variational inequality. -/
  ineq : ∀ v ∈ SobolevEuclideanZero N 1 2 Ω,
    (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn ψ x ≤ fn v x) →
      load Ω f (v - u) ≤ dirichletForm Ω u (v - u)

variable {Ω}

/-- **The lower bound `f ≤ −Δu` of the Lewy–Stampacchia inequality**: for `Φ ∈ H¹₀(Ω)`, `Φ ≥ 0`,
`∫_Ω f Φ ≤ ∫_Ω ∇u · ∇Φ` — the variational inequality tested with `v = u + Φ`. -/
theorem IsObstacleSolution.load_le_dirichletForm {ψ : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean N 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero N 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ fn Φ x) :
    load Ω f Φ ≤ dirichletForm Ω u Φ := by
  have h := hu.ineq (u + Φ) (add_mem hu.mem_zero hΦ) (by
    filter_upwards [hu.ae_le, hΦ0, Lp.coeFn_add (weakDeriv u 0) (weakDeriv Φ 0)] with x h1 h2 h3
    have e : fn (u + Φ) x = fn u x + fn Φ x := h3
    rw [e]
    linarith)
  rwa [add_sub_cancel_left] at h

end Obstacle

/-! ### The upper bound `−Δu ≤ max (f, −Δψ)`: the truncation step -/

section Upper

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- `f v` is integrable on `Ω` for `f ∈ L²(Ω)`, `v ∈ H¹(Ω)`. -/
theorem integrable_mul_fn (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclidean (d + 1) 1 2 Ω) :
    Integrable (fun x ↦ f x * fn v x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (L2.integrable_inner (𝕜 := ℝ) f (weakDeriv v 0)).congr
    (Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial]
      rw [mul_comm]
      rfl)

/-- The product of two partial derivatives of `H¹(Ω)` elements is integrable on `Ω`. -/
theorem integrable_weakDeriv_mul_weakDeriv (v w : SobolevEuclidean (d + 1) 1 2 Ω)
    (i : Fin (d + 1)) :
    Integrable (fun x ↦ weakDeriv v (MultiIndexLE.single i) x
      * weakDeriv w (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (L2.integrable_inner (𝕜 := ℝ) (weakDeriv v (MultiIndexLE.single i))
    (weakDeriv w (MultiIndexLE.single i))).congr
    (Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial]
      rw [mul_comm])

/-- The partial derivatives of `ε Φ − z` are `ε ∂ᵢΦ − ∂ᵢz`, almost everywhere. -/
theorem weakDeriv_smul_sub_ae_eq (ε : ℝ) (Φ z : SobolevEuclidean (d + 1) 1 2 Ω)
    (i : Fin (d + 1)) :
    ⇑(weakDeriv (ε • Φ - z) (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x
        - weakDeriv z (MultiIndexLE.single i) x := by
  have h1 : weakDeriv (ε • Φ - z) (MultiIndexLE.single i)
      = ε • weakDeriv Φ (MultiIndexLE.single i) - weakDeriv z (MultiIndexLE.single i) := by
    rw [← weakDerivL_apply, map_sub, map_smul, weakDerivL_apply, weakDerivL_apply]
  rw [h1]
  filter_upwards [Lp.coeFn_sub (ε • weakDeriv Φ (MultiIndexLE.single i))
    (weakDeriv z (MultiIndexLE.single i)),
    Lp.coeFn_smul ε (weakDeriv Φ (MultiIndexLE.single i))] with x hx1 hx2
  rw [hx1, Pi.sub_apply, hx2, Pi.smul_apply, smul_eq_mul]

/-- The function of `ε Φ − z` is `ε Φ − z`, almost everywhere. -/
theorem fn_smul_sub_ae_eq (ε : ℝ) (Φ z : SobolevEuclidean (d + 1) 1 2 Ω) :
    fn (ε • Φ - z) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * fn Φ x - fn z x := by
  filter_upwards [Lp.coeFn_sub (weakDeriv (ε • Φ) 0) (weakDeriv z 0),
    Lp.coeFn_smul ε (weakDeriv Φ 0)] with x h1 h2
  have e : fn (ε • Φ - z) x = fn (ε • Φ) x - fn z x := h1
  have e2 : fn (ε • Φ) x = ε * fn Φ x := by
    rw [show fn (ε • Φ) x = (ε • fn Φ) x from h2, Pi.smul_apply, smul_eq_mul]
  rw [e, e2]

/-- **The truncation `min (ε Φ, z)` as an element of `H¹₀(Ω)`**, for `Φ ∈ H¹₀(Ω)`, `Φ ≥ 0`,
`z ∈ H¹(Ω)`, `z ≥ 0` and `ε > 0`, on a `C¹` chart domain with bounded boundary: it is
`ε Φ − (ε Φ − z)⁺`, the positive part `P = (ε Φ − z)⁺` lying in `H¹₀(Ω)` because `0 ≤ P ≤ ε Φ`
(`SobolevEuclideanZero.mem_of_nonneg_of_le`). The partial derivatives are
`∂ᵢ min (ε Φ, z) = ε ∂ᵢΦ − 1_{εΦ > z} (ε ∂ᵢΦ − ∂ᵢz)`
(`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart`). -/
theorem exists_min_elem
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x)
    {z : SobolevEuclidean (d + 1) 1 2 Ω}
    (hz0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn z x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      (fn θ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ ε * fn Φ x - max (ε * fn Φ x - fn z x) 0) ∧
      ∀ i, ⇑(weakDeriv θ (MultiIndexLE.single i))
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x
          - {x | 0 < fn (ε • Φ - z) x}.indicator
            (weakDeriv (ε • Φ - z) (MultiIndexLE.single i)) x := by
  have hyfn := fn_smul_sub_ae_eq ε Φ z
  obtain ⟨P, hP⟩ :=
    ((memSobolevMultiIndex (ε • Φ - z)).posPart one_le_two).exists_sobolevMultiIndex
  have hεΦ : fn (ε • Φ) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      ε • fn Φ := Lp.coeFn_smul ε (weakDeriv Φ 0)
  have hP0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn P x := by
    filter_upwards [hP] with x hx
    rw [hx]
    exact le_max_right _ _
  have hPle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn P x ≤ fn (ε • Φ) x := by
    filter_upwards [hP, hyfn, hz0, hεΦ, hΦ0] with x h1 h2 h3 h4 h5
    rw [h1, h2, h4, Pi.smul_apply, smul_eq_mul]
    exact max_le (by linarith) (mul_nonneg hε.le h5)
  have hPmem : P ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    SobolevEuclideanZero.mem_of_nonneg_of_le hΩ hΓ
      ((SobolevEuclideanZero (d + 1) 1 2 Ω).smul_mem ε hΦ) hP0 hPle
  refine ⟨ε • Φ - P, sub_mem ((SobolevEuclideanZero (d + 1) 1 2 Ω).smul_mem ε hΦ) hPmem,
    ?_, fun i ↦ ?_⟩
  · filter_upwards [Lp.coeFn_sub (weakDeriv (ε • Φ) 0) (weakDeriv P 0), hεΦ, hP, hyfn]
      with x h1 h2 h3 h4
    have e : fn (ε • Φ - P) x = fn (ε • Φ) x - fn P x := h1
    rw [e, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
  · have h1 : weakDeriv (ε • Φ - P) (MultiIndexLE.single i)
        = ε • weakDeriv Φ (MultiIndexLE.single i) - weakDeriv P (MultiIndexLE.single i) := by
      rw [← weakDerivL_apply, map_sub, map_smul, weakDerivL_apply, weakDerivL_apply]
    have h2 := weakDeriv_single_ae_eq_of_fn_ae_eq_posPart hP i
    rw [h1]
    filter_upwards [Lp.coeFn_sub (ε • weakDeriv Φ (MultiIndexLE.single i))
      (weakDeriv P (MultiIndexLE.single i)), Lp.coeFn_smul ε (weakDeriv Φ (MultiIndexLE.single i)),
      h2] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, Pi.smul_apply, smul_eq_mul, hx3]

/-- **The variational inequality tested with `v = u − θ`**: for `θ ∈ H¹₀(Ω)` with `θ ≤ u − ψ`,
`∫_Ω ∇u · ∇θ ≤ ∫_Ω f θ`. -/
theorem IsObstacleSolution.dirichletForm_le_load_of_le {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {θ : SobolevEuclidean (d + 1) 1 2 Ω} (hθ : θ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hθz : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ fn u x - fn ψ x) :
    dirichletForm Ω u θ ≤ load Ω f θ := by
  have hvψ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn ψ x ≤ fn (u - θ) x := by
    filter_upwards [Lp.coeFn_sub (weakDeriv u 0) (weakDeriv θ 0), hθz] with x h1 h2
    have e : fn (u - θ) x = fn u x - fn θ x := h1
    rw [e]
    linarith
  have hVI := hu.ineq (u - θ) (sub_mem hu.mem_zero hθ) hvψ
  rw [sub_sub_cancel_left, (load Ω f).map_neg, (dirichletForm Ω u).map_neg,
    neg_le_neg_iff] at hVI
  exact hVI

/-- `∫_Ω ∇z · ∇θ ≤ ∫_Ω (f − q) θ` for `z = u − ψ`, `−Δψ = q` and `θ` as in
`IsObstacleSolution.dirichletForm_le_load_of_le`. -/
theorem IsObstacleSolution.dirichletForm_sub_le {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {θ : SobolevEuclidean (d + 1) 1 2 Ω} (hθ : θ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hθz : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ fn u x - fn ψ x) {z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ) :
    dirichletForm Ω z θ ≤ load Ω (f - q) θ := by
  have hVI := hu.dirichletForm_le_load_of_le hθ hθz
  have huzψ : u = z + ψ := by
    rw [hz, sub_add_cancel]
  have hsplit : dirichletForm Ω u θ = dirichletForm Ω z θ + load Ω q θ := by
    rw [huzψ, dirichletForm_add_left, hψ θ hθ]
  have e : load Ω (f - q) θ = load Ω f θ - load Ω q θ := by
    simp only [load_apply_inner, inner_sub_left]
  refine le_of_le_of_eq ?_ e.symm
  calc dirichletForm Ω z θ = dirichletForm Ω u θ - load Ω q θ := eq_sub_of_add_eq hsplit.symm
    _ ≤ load Ω f θ - load Ω q θ := sub_le_sub_right hVI _

/-- `∫_Ω g θ ≤ ε ∫_Ω g⁺ Φ` for `0 ≤ θ ≤ ε Φ`. -/
theorem load_le_smul_load_sup_zero
    (g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {θ Φ : SobolevEuclidean (d + 1) 1 2 Ω} {ε : ℝ}
    (hθ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn θ x)
    (hθle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ ε * fn Φ x) :
    load Ω g θ ≤ ε * load Ω (g ⊔ 0) Φ := by
  rw [load_apply, load_apply, ← integral_const_mul]
  refine integral_mono_ae (integrable_mul_fn _ _) ((integrable_mul_fn _ _).const_mul ε) ?_
  filter_upwards [hθ0, hθle, Lp.coeFn_sup g 0, Lp.coeFn_zero ℝ 2
    (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))] with x h1 h2 h3 h4
  simp only [h3, h4, Pi.sup_apply, Pi.zero_apply]
  calc g x * fn θ x ≤ max (g x) 0 * fn θ x :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h1
    _ ≤ max (g x) 0 * (ε * fn Φ x) :=
        mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = ε * (max (g x) 0 * fn Φ x) := by ring

/-- **One component of `∫_Ω ∇z · ∇ min (ε Φ, z)`**: with `∂ᵢθ = ε ∂ᵢΦ − 1_{y > 0} (ε ∂ᵢΦ − ∂ᵢz)`,
`∂ᵢz ∂ᵢθ = 1_{y ≤ 0} ε ∂ᵢz ∂ᵢΦ + 1_{y > 0} (∂ᵢz)² ≥ 1_{y ≤ 0} ε ∂ᵢz ∂ᵢΦ`. -/
theorem integral_indicator_le_integral_weakDeriv_mul {θ z Φ y : SobolevEuclidean (d + 1) 1 2 Ω}
    {ε : ℝ} (i : Fin (d + 1))
    (hDθ : ⇑(weakDeriv θ (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x
        - {x | 0 < fn y x}.indicator (weakDeriv y (MultiIndexLE.single i)) x)
    (hDy : ⇑(weakDeriv y (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x - weakDeriv z (MultiIndexLE.single i) x) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ε * {x | fn y x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        weakDeriv z (MultiIndexLE.single i) x * weakDeriv θ (MultiIndexLE.single i) x := by
  have hint : Integrable (fun x ↦ ε * {x | fn y x ≤ 0}.indicator
      (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
    refine ((integrable_weakDeriv_mul_weakDeriv z Φ i).indicator₀ ?_).const_mul ε
    exact nullMeasurableSet_le (Lp.aestronglyMeasurable (weakDeriv y 0)).aemeasurable
      aemeasurable_const
  refine integral_mono_ae hint (integrable_weakDeriv_mul_weakDeriv z θ i) ?_
  filter_upwards [hDθ, hDy] with x hx1 hx2
  rw [hx1]
  by_cases hyx : 0 < fn y x
  · rw [indicator_of_mem (show x ∈ {x | 0 < fn y x} from hyx), hx2,
      indicator_of_notMem (show x ∉ {x | fn y x ≤ 0} from not_le.2 hyx)]
    nlinarith [sq_nonneg (weakDeriv z (MultiIndexLE.single i) x)]
  · rw [indicator_of_notMem (show x ∉ {x | 0 < fn y x} from hyx),
      indicator_of_mem (show x ∈ {x | fn y x ≤ 0} from not_lt.1 hyx)]
    ring_nf
    exact le_refl _

/-- **The truncation step of the Lewy–Stampacchia argument.** Let `u` solve the obstacle problem
with obstacle `ψ` and load `f`, where `−Δψ = q ∈ L²(Ω)` weakly, on a `C¹` chart domain with
bounded boundary; let `Φ ∈ H¹₀(Ω)`, `Φ ≥ 0`, and `ε > 0`. With `z = u − ψ ≥ 0`, the competitor
`v = u − min (ε Φ, z) = max (u − ε Φ, ψ)` is admissible, and the variational inequality gives

`ε ∑ᵢ ∫_{εΦ ≤ z} ∂ᵢz ∂ᵢΦ ≤ ∫_Ω ∇z · ∇(min (ε Φ, z)) ≤ ∫_Ω (f − q) min (ε Φ, z) ≤ ε ∫_Ω (f − q)⁺ Φ`,

the middle inequality being the variational inequality minus `−Δψ = q`
(`IsObstacleSolution.dirichletForm_sub_le`), the first the formula
`∇ min (ε Φ, z) = 1_{εΦ ≤ z} ε ∇Φ + 1_{εΦ > z} ∇z` (`integral_indicator_le_integral_weakDeriv_mul`),
and the last `0 ≤ min (ε Φ, z) ≤ ε Φ` (`load_le_smul_load_sup_zero`); the membership
`min (ε Φ, z) ∈ H¹₀(Ω)` is `exists_min_elem`. -/
theorem IsObstacleSolution.truncation_step
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x)
    {ε : ℝ} (hε : 0 < ε) {z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ) :
    ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        {x | fn (ε • Φ - z) x ≤ 0}.indicator
          (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ load Ω ((f - q) ⊔ 0) Φ := by
  have hzfn : fn z =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fn u - fn ψ := by
    rw [hz]
    exact Lp.coeFn_sub (weakDeriv u 0) (weakDeriv ψ 0)
  have hz0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn z x := by
    filter_upwards [hzfn, hu.ae_le] with x h1 h2
    rw [h1, Pi.sub_apply]
    linarith
  obtain ⟨θ, hθmem, hθfn, hDθ⟩ := exists_min_elem hΩ hΓ hΦ hΦ0 hz0 hε
  have hθ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn θ x := by
    filter_upwards [hθfn, hz0, hΦ0] with x h1 h2 h3
    rw [h1]
    rcases le_total (ε * fn Φ x - fn z x) 0 with h | h
    · rw [max_eq_right h, sub_zero]
      exact mul_nonneg hε.le h3
    · rw [max_eq_left h]
      linarith
  have hθle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ ε * fn Φ x := by
    filter_upwards [hθfn] with x h1
    rw [h1]
    linarith [le_max_right (ε * fn Φ x - fn z x) 0]
  have hθz : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ fn u x - fn ψ x := by
    filter_upwards [hθfn, hzfn] with x h1 h2
    rw [h1]
    rw [Pi.sub_apply] at h2
    linarith [le_max_left (ε * fn Φ x - fn z x) 0]
  have hmid := hu.dirichletForm_sub_le hψ hθmem hθz hz
  have hright := load_le_smul_load_sup_zero (f - q) hθ0 hθle
  have hleft : ε * ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ dirichletForm Ω z θ := by
    have hi : ∀ i, ε * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        {x | fn (ε • Φ - z) x ≤ 0}.indicator
          (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
        ≤ ⟪weakDeriv z (MultiIndexLE.single i), weakDeriv θ (MultiIndexLE.single i)⟫_ℝ := by
      intro i
      rw [L2.inner_eq_integral_mul, ← integral_const_mul]
      exact integral_indicator_le_integral_weakDeriv_mul i (hDθ i)
        (weakDeriv_smul_sub_ae_eq ε Φ z i)
    rw [dirichletForm_apply_inner, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hi i
  exact le_of_mul_le_mul_left (hleft.trans (hmid.trans hright)) hε

end Upper

/-! ### The upper bound: the limit `ε ↓ 0` -/

section UpperLimit

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- `∫_Ω ∇u · ∇Φ = ∫_Ω ∇z · ∇Φ + ∫_Ω q Φ` for `z = u − ψ`, `−Δψ = q` weakly and `Φ ∈ H¹₀(Ω)`. -/
theorem dirichletForm_eq_dirichletForm_sub_add_load {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {u z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletForm Ω u Φ = dirichletForm Ω z Φ + load Ω q Φ := by
  have huzψ : u = z + ψ := by
    rw [hz, sub_add_cancel]
  rw [huzψ, dirichletForm_add_left, hψ Φ hΦ]

/-- `max (a − b) 0 + b = max a b`. -/
theorem max_sub_zero_add (a b : ℝ) : max (a - b) 0 + b = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.2 h), max_eq_right h, zero_add]
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_left h, sub_add_cancel]

/-- `(f − q)⁺ + q = max (f, q)` in `L²(Ω)`. -/
theorem sub_sup_zero_add_eq_sup
    (f q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (f - q) ⊔ 0 + q = f ⊔ q := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add ((f - q) ⊔ 0) q, Lp.coeFn_sup (f - q) 0, Lp.coeFn_sub f q,
    Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
    Lp.coeFn_sup f q] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.sup_apply, h3, Pi.sub_apply, h4, Pi.zero_apply, h5, Pi.sup_apply]
  exact max_sub_zero_add _ _

/-- `∫_Ω (f − q)⁺ Φ + ∫_Ω q Φ = ∫_Ω max (f, q) Φ`. -/
theorem load_sub_sup_zero_add_load
    (f q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (Φ : SobolevEuclidean (d + 1) 1 2 Ω) :
    load Ω ((f - q) ⊔ 0) Φ + load Ω q Φ = load Ω (f ⊔ q) Φ := by
  exact (load_add (Ω := Ω) ((f - q) ⊔ 0) q Φ).symm.trans
    (congrArg (fun g ↦ load Ω g Φ) (sub_sup_zero_add_eq_sup f q))

/-- **The Lewy–Stampacchia upper bound for `z = u − ψ`**: `∫_Ω ∇z · ∇Φ ≤ ∫_Ω (f − q)⁺ Φ` for
`Φ ∈ H¹₀(Ω)`, `Φ ≥ 0`. The truncation step `IsObstacleSolution.truncation_step` at
`ε = 1/(n+1)` and dominated convergence: as `n → ∞`, `1_{ε_n Φ ≤ z} → 1_{z > 0}` where `z > 0`, and
`∂ᵢz = 0` almost everywhere on `{z = 0}`
(`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart`,
since `z = z⁺`), so `∑ᵢ ∫_{ε_n Φ ≤ z} ∂ᵢz ∂ᵢΦ → ∑ᵢ ∫_Ω ∂ᵢz ∂ᵢΦ`. -/
theorem IsObstacleSolution.dirichletForm_sub_le_load_sup_zero
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x)
    {z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ) :
    dirichletForm Ω z Φ ≤ load Ω ((f - q) ⊔ 0) Φ := by
  have hzfn : fn z =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fn u - fn ψ := by
    rw [hz]
    exact Lp.coeFn_sub (weakDeriv u 0) (weakDeriv ψ 0)
  have hz0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn z x := by
    filter_upwards [hzfn, hu.ae_le] with x h1 h2
    rw [h1, Pi.sub_apply]
    linarith
  -- `∂ᵢz = 0` where `z = 0`
  have hDz : ∀ i, ⇑(weakDeriv z (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      {x | 0 < fn z x}.indicator (weakDeriv z (MultiIndexLE.single i)) := fun i ↦
    weakDeriv_single_ae_eq_of_fn_ae_eq_posPart (u := z) (v := z)
      (by filter_upwards [hz0] with x hx; rw [max_eq_left hx]) i
  -- the sequence `ε n = 1/(n+1)`
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by rw [hεdef]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := hεdef ▸ tendsto_one_div_add_atTop_nhds_zero_nat
  have hstep : ∀ n, ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε n • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ load Ω ((f - q) ⊔ 0) Φ := fun n ↦
    hu.truncation_step hΩ hΓ hψ hΦ hΦ0 (hεpos n) hz
  have hyfn : ∀ n, fn (ε n • Φ - z) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε n * fn Φ x - fn z x := fun n ↦ fn_smul_sub_ae_eq (ε n) Φ z
  -- the limit of each component
  have hlim : ∀ i, Tendsto (fun n ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε n • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x)
      atTop (𝓝 (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x)) := by
    intro i
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x‖)
      (fun n ↦ ?_) (integrable_weakDeriv_mul_weakDeriv z Φ i).norm
      (fun n ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
    · exact (aestronglyMeasurable_indicator_iff₀ (nullMeasurableSet_le
        (Lp.aestronglyMeasurable (weakDeriv (ε n • Φ - z) 0)).aemeasurable aemeasurable_const)).2
        (integrable_weakDeriv_mul_weakDeriv z Φ i).aestronglyMeasurable.restrict
    · filter_upwards [ae_all_iff.2 hyfn, hDz i] with x hx hDx
      by_cases hzx : 0 < fn z x
      · have hev : ∀ᶠ n in atTop, fn (ε n • Φ - z) x ≤ 0 := by
          have h1 : Tendsto (fun n ↦ ε n * fn Φ x - fn z x) atTop
              (𝓝 (0 * fn Φ x - fn z x)) := (hεt.mul_const _).sub_const _
          rw [zero_mul, zero_sub] at h1
          filter_upwards [h1.eventually (gt_mem_nhds (neg_lt_zero.2 hzx))] with n hn
          rw [hx n]
          exact hn.le
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        rw [indicator_of_mem (show x ∈ {x | fn (ε n • Φ - z) x ≤ 0} from hn)]
      · have h0 : weakDeriv z (MultiIndexLE.single i) x = 0 := by
          rw [hDx, indicator_of_notMem (show x ∉ {x | 0 < fn z x} from hzx)]
        have hzero : ∀ n, {x | fn (ε n • Φ - z) x ≤ 0}.indicator
            (fun x ↦ weakDeriv z (MultiIndexLE.single i) x
              * weakDeriv Φ (MultiIndexLE.single i) x) x = 0 := fun n ↦ by
          rw [Set.indicator_apply]
          split_ifs
          · rw [h0, zero_mul]
          · rfl
        simp only [hzero, h0, zero_mul]
        exact tendsto_const_nhds
  have hsum : Tendsto (fun n ↦ ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε n • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x)
      atTop (𝓝 (∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x)) :=
    tendsto_finsetSum _ fun i _ ↦ hlim i
  have hzΦ := le_of_tendsto' hsum hstep
  have e : dirichletForm Ω z Φ = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x := by
    rw [dirichletForm_apply_inner]
    simp only [L2.inner_eq_integral_mul]
  exact e.trans_le hzΦ

/-- **The upper bound `−Δu ≤ max (f, −Δψ)` of the Lewy–Stampacchia inequality**: on a `C¹`
chart domain with bounded boundary, if `u` solves the obstacle problem with obstacle `ψ` and load
`f`, and `−Δψ = q ∈ L²(Ω)` weakly, then `∫_Ω ∇u · ∇Φ ≤ ∫_Ω max (f, q) Φ` for every `Φ ∈ H¹₀(Ω)`,
`Φ ≥ 0`: `∫_Ω ∇(u − ψ) · ∇Φ ≤ ∫_Ω (f − q)⁺ Φ`
(`IsObstacleSolution.dirichletForm_sub_le_load_sup_zero`)
plus `∫_Ω ∇ψ · ∇Φ = ∫_Ω q Φ`, and `(f − q)⁺ + q = max (f, q)`. -/
theorem IsObstacleSolution.dirichletForm_le_load_sup
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x) :
    dirichletForm Ω u Φ ≤ load Ω (f ⊔ q) Φ := by
  obtain ⟨z, hz⟩ : ∃ z : SobolevEuclidean (d + 1) 1 2 Ω, z = u - ψ := ⟨_, rfl⟩
  have h1 := hu.dirichletForm_sub_le_load_sup_zero hΩ hΓ hψ hΦ hΦ0 hz
  have h2 := dirichletForm_eq_dirichletForm_sub_add_load hψ hz hΦ
  have h3 := load_sub_sup_zero_add_load f q Φ
  linarith

end UpperLimit

/-! ### From the two-sided bound to `−Δu ∈ L²(Ω)` -/

section Representation

/-- **A functional dominated by an `L²`-type seminorm through an injective map into a Hilbert
space is an inner product**: if `T : V → ℝ` is continuous linear with `|T v| ≤ C ‖ι v‖` for an
injective `ι : V → H`, `H` a real Hilbert space, then `T v = ⟪h, ι v⟫` for some `h ∈ H` with
`‖h‖ ≤ C` — the Hahn–Banach theorem on the range of `ι` and the Riesz representation. -/
theorem exists_inner_of_forall_abs_le {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (ι : V →L[ℝ] H)
    (hι : Function.Injective ι) (T : V →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ v, |T v| ≤ C * ‖ι v‖) :
    ∃ h : H, ‖h‖ ≤ C ∧ ∀ v, T v = ⟪h, ι v⟫_ℝ := by
  obtain ⟨S, hS⟩ : ∃ S : Submodule ℝ H, S = LinearMap.range (ι : V →ₗ[ℝ] H) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : V ≃ₗ[ℝ] LinearMap.range (ι : V →ₗ[ℝ] H),
      e = LinearEquiv.ofInjective (ι : V →ₗ[ℝ] H) hι := ⟨_, rfl⟩
  have hev : ∀ v, ((e v : LinearMap.range (ι : V →ₗ[ℝ] H)) : H) = ι v := fun v ↦ by
    rw [he]
    exact LinearEquiv.ofInjective_apply _ _
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : LinearMap.range (ι : V →ₗ[ℝ] H) →ₗ[ℝ] ℝ,
      ℓ₀ = (T : V →ₗ[ℝ] ℝ).comp e.symm.toLinearMap := ⟨_, rfl⟩
  have hℓ₀apply : ∀ y, ℓ₀ y = T (e.symm y) := fun y ↦ by rw [hℓ₀]; rfl
  have hbound : ∀ y : LinearMap.range (ι : V →ₗ[ℝ] H), ‖ℓ₀ y‖ ≤ C * ‖y‖ := fun y ↦ by
    have hy : ι (e.symm y) = (y : H) := by
      rw [← hev (e.symm y), e.apply_symm_apply]
    rw [hℓ₀apply, Real.norm_eq_abs, ← Submodule.norm_coe, ← hy]
    exact hT _
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : StrongDual ℝ (LinearMap.range (ι : V →ₗ[ℝ] H)),
      ℓ = LinearMap.mkContinuous ℓ₀ C hbound := ⟨_, rfl⟩
  have hℓapply : ∀ y, ℓ y = ℓ₀ y := fun y ↦ by rw [hℓ]; rfl
  have hℓnorm : ‖ℓ‖ ≤ C := by rw [hℓ]; exact LinearMap.mkContinuous_norm_le _ hC _
  obtain ⟨g, hg, hnorm⟩ := exists_extension_norm_eq (LinearMap.range (ι : V →ₗ[ℝ] H)) ℓ
  refine ⟨(InnerProductSpace.toDual ℝ H).symm g, ?_, fun v ↦ ?_⟩
  · rw [LinearIsometryEquiv.norm_map, hnorm]
    exact hℓnorm
  · rw [InnerProductSpace.toDual_symm_apply, ← hev v, hg (e v), hℓapply, hℓ₀apply,
      e.symm_apply_apply]

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **A continuous linear functional on `H¹₀(Ω)` bounded by the `L²` norm is `Φ ↦ ∫_Ω h Φ`** for
some `h ∈ L²(Ω)` with `‖h‖₂ ≤ C`: `exists_inner_of_forall_abs_le` along the injective inclusion
`SobolevMultiIndexZero.fnL : H¹₀(Ω) → L²(Ω)`. -/
theorem exists_load_eq_of_forall_abs_le (T : SobolevEuclideanZero N 1 2 Ω →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hT : ∀ Φ : SobolevEuclideanZero N 1 2 Ω,
      |T Φ| ≤ C * ‖weakDeriv (Φ : SobolevEuclidean N 1 2 Ω) 0‖) :
    ∃ h : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), ‖h‖ ≤ C ∧
      ∀ Φ : SobolevEuclideanZero N 1 2 Ω, T Φ = load Ω h Φ := by
  obtain ⟨h, hh, hT'⟩ := exists_inner_of_forall_abs_le
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    SobolevMultiIndexZero.fnL_injective T hC hT
  exact ⟨h, hh, fun Φ ↦ (hT' Φ).trans (load_apply_inner Ω h Φ).symm⟩

end Representation

section LpBound

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **The two-sided Lewy–Stampacchia bound on nonnegative `Φ`**: for `Φ ∈ H¹₀(Ω)`, `Φ ≥ 0`,
`|∫_Ω ∇u · ∇Φ − ∫_Ω f Φ| ≤ ‖max (f, q) − f‖₂ ‖Φ‖₂`, from
`IsObstacleSolution.load_le_dirichletForm` and `IsObstacleSolution.dirichletForm_le_load_sup`. -/
theorem IsObstacleSolution.abs_dirichletForm_sub_load_le_of_nonneg
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x) :
    |dirichletForm Ω u Φ - load Ω f Φ| ≤ ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ := by
  have h1 := hu.load_le_dirichletForm hΦ hΦ0
  have h2 := hu.dirichletForm_le_load_sup hΩ hΓ hψ hΦ hΦ0
  have h3 : load Ω (f ⊔ q) Φ - load Ω f Φ = load Ω (f ⊔ q - f) Φ := by
    simp only [load_apply_inner, inner_sub_left]
  have h4 := abs_load_le Ω (f ⊔ q - f) Φ
  rw [abs_of_nonneg (by linarith)]
  linarith [le_abs_self (load Ω (f ⊔ q - f) Φ)]

/-- **The decomposition `Φ = Φ⁺ − Φ⁻` in `H¹₀(Ω)`**, with `‖Φ^±‖₂ ≤ ‖Φ‖₂`. -/
theorem _root_.SobolevEuclideanZero.exists_eq_sub_of_nonneg {Φ : SobolevEuclidean (d + 1) 1 2 Ω}
    (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ∃ P ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, ∃ Q ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      Φ = P - Q ∧
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn P x) ∧
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Q x) ∧
      ‖weakDeriv P 0‖ ≤ ‖weakDeriv Φ 0‖ ∧ ‖weakDeriv Q 0‖ ≤ ‖weakDeriv Φ 0‖ := by
  obtain ⟨P, hP⟩ := ((memSobolevMultiIndex Φ).posPart one_le_two).exists_sobolevMultiIndex
  obtain ⟨Q, hQ⟩ := ((memSobolevMultiIndex (-Φ)).posPart one_le_two).exists_sobolevMultiIndex
  have hPmem : P ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    SobolevEuclideanZero.posPart_mem (p := 2) (by norm_num) ⟨Φ, hΦ⟩ hP
  have hQmem : Q ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    SobolevEuclideanZero.posPart_mem (p := 2) (by norm_num) ⟨-Φ, neg_mem hΦ⟩ hQ
  have hnegΦ : fn (-Φ) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] -fn Φ := by
    have h1 : weakDeriv (-Φ) 0 = -weakDeriv Φ 0 := by
      rw [← weakDerivL_apply, map_neg, weakDerivL_apply]
    rw [show fn (-Φ) = ⇑(weakDeriv (-Φ) 0) from rfl, h1]
    exact Lp.coeFn_neg _
  refine ⟨P, hPmem, Q, hQmem, ?_, ?_, ?_, ?_, ?_⟩
  · refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
    filter_upwards [Lp.coeFn_sub (weakDeriv P 0) (weakDeriv Q 0), hP, hQ, hnegΦ]
      with x h1 h2 h3 h4
    have e : fn (P - Q) x = fn P x - fn Q x := h1
    rw [e, h2, h3, h4, Pi.neg_apply]
    rcases le_total (fn Φ x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
      ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
      ring
  · filter_upwards [hP] with x hx
    rw [hx]
    exact le_max_right _ _
  · filter_upwards [hQ] with x hx
    rw [hx]
    exact le_max_right _ _
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hP] with x hx
    have e : (weakDeriv P 0) x = max (fn Φ x) 0 := hx
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    change |max (fn Φ x) 0| ≤ |fn Φ x|
    exact abs_le.2 ⟨by linarith [abs_nonneg (fn Φ x), le_max_right (fn Φ x) 0],
      max_le (le_abs_self _) (abs_nonneg _)⟩
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hQ, hnegΦ] with x hx hx'
    have e : (weakDeriv Q 0) x = max (-fn Φ x) 0 := by
      rw [show (weakDeriv Q 0) x = fn Q x from rfl, hx, hx', Pi.neg_apply]
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    change |max (-fn Φ x) 0| ≤ |fn Φ x|
    exact abs_le.2 ⟨by linarith [abs_nonneg (fn Φ x), le_max_right (-fn Φ x) 0],
      max_le (by linarith [neg_abs_le (fn Φ x), le_abs_self (fn Φ x)]) (abs_nonneg _)⟩

/-- **The Lewy–Stampacchia functional is `L²`-bounded on all of `H¹₀(Ω)`**:
`|∫_Ω ∇u · ∇Φ − ∫_Ω f Φ| ≤ 2 ‖max (f, q) − f‖₂ ‖Φ‖₂`, by splitting `Φ = Φ⁺ − Φ⁻`. -/
theorem IsObstacleSolution.abs_dirichletForm_sub_load_le
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    |dirichletForm Ω u Φ - load Ω f Φ| ≤ 2 * ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ := by
  obtain ⟨P, hPmem, Q, hQmem, hΦPQ, hP0, hQ0, hPn, hQn⟩ :=
    SobolevEuclideanZero.exists_eq_sub_of_nonneg hΦ
  have h1 := hu.abs_dirichletForm_sub_load_le_of_nonneg hΩ hΓ hψ hPmem hP0
  have h2 := hu.abs_dirichletForm_sub_load_le_of_nonneg hΩ hΓ hψ hQmem hQ0
  have e : dirichletForm Ω u Φ - load Ω f Φ
      = (dirichletForm Ω u P - load Ω f P) - (dirichletForm Ω u Q - load Ω f Q) := by
    rw [hΦPQ, (dirichletForm Ω u).map_sub, (load Ω f).map_sub]
    ring
  rw [e]
  have hg0 : 0 ≤ ‖f ⊔ q - f‖ := norm_nonneg _
  calc |(dirichletForm Ω u P - load Ω f P) - (dirichletForm Ω u Q - load Ω f Q)|
      ≤ |dirichletForm Ω u P - load Ω f P| + |dirichletForm Ω u Q - load Ω f Q| :=
        abs_sub _ _
    _ ≤ ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ + ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hPn hg0))
          (h2.trans (mul_le_mul_of_nonneg_left hQn hg0))
    _ = 2 * ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ := by ring

/-- **`−Δu ∈ L²(Ω)` for the solution of the obstacle problem**: on a `C¹` chart domain with
bounded boundary, with `−Δψ = q ∈ L²(Ω)`, there is `h ∈ L²(Ω)` with `‖h‖₂ ≤ 2 ‖max (f, q) − f‖₂`
and `∫_Ω ∇u · ∇Φ = ∫_Ω (f + h) Φ` for every `Φ ∈ H¹₀(Ω)`, i.e. `−Δu = f + h`. The Lewy–Stampacchia
bound `|∫_Ω ∇u · ∇Φ − ∫_Ω f Φ| ≤ 2 ‖max (f, q) − f‖₂ ‖Φ‖₂` and the representation
`exists_load_eq_of_forall_abs_le`. -/
theorem IsObstacleSolution.exists_dirichletForm_eq_load
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u) :
    ∃ h : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ‖h‖ ≤ 2 * ‖f ⊔ q - f‖ ∧
      ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u Φ = load Ω (f + h) Φ := by
  obtain ⟨T, hT⟩ : ∃ T : SobolevEuclideanZero (d + 1) 1 2 Ω →L[ℝ] ℝ,
      T = (dirichletForm Ω u - load Ω f).comp (SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL :=
    ⟨_, rfl⟩
  have hTapply : ∀ Φ : SobolevEuclideanZero (d + 1) 1 2 Ω,
      T Φ = dirichletForm Ω u Φ - load Ω f Φ := fun Φ ↦ by rw [hT]; rfl
  obtain ⟨h, hh, hTh⟩ := exists_load_eq_of_forall_abs_le T (C := 2 * ‖f ⊔ q - f‖)
    (by positivity) fun Φ ↦ by
    rw [hTapply]
    exact hu.abs_dirichletForm_sub_load_le hΩ hΓ hψ Φ.2
  refine ⟨h, hh, fun Φ hΦ ↦ ?_⟩
  have := hTh ⟨Φ, hΦ⟩
  rw [hTapply] at this
  rw [load_add]
  linarith

end LpBound

/-! ### `H²` regularity of the solution of the obstacle problem -/

section Regularity

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- The solution of the obstacle problem is a weak solution of `−Δu + u = f + h + u` on `H¹₀(Ω)`
once `−Δu = f + h` is known, i.e. a Galerkin solution for the form of `−Δ + 1`. -/
theorem IsObstacleSolution.isGalerkinSolution_laplace {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {h : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u Φ = load Ω (f + h) Φ) :
    IsGalerkinSolution (laplaceForm Ω) (load Ω (f + h + weakDeriv u 0))
      (SobolevEuclideanZero (d + 1) 1 2 Ω) u := by
  refine ⟨hu.mem_zero, fun Φ hΦ ↦ ?_⟩
  rw [laplaceForm_apply_eq_dirichletForm_add_weakDeriv, heq Φ hΦ]
  simp only [load_apply_inner, inner_add_left]

/-- **`H²` regularity for the obstacle problem** — the `p = 2` case of [han2009theoretical]
Theorem 11.3.12 (Brezis–Stampacchia), for the Laplacian. On a `C²` chart domain `Ω ⊆ ℝ^{d+1}` with
bounded boundary there is a constant `C` such that for every obstacle `ψ ∈ H¹(Ω)` with
`−Δψ = q ∈ L²(Ω)` weakly, every load `f ∈ L²(Ω)` and every solution `u` of the obstacle problem,
`u ∈ H²(Ω)`, and every `U ∈ H²(Ω)` with function `u` has
`‖U‖_{H²(Ω)} ≤ C (‖f‖₂ + 2 ‖max (f, q) − f‖₂ + ‖u‖₂)`.

The Lewy–Stampacchia inequality gives `−Δu = f + h` with `h ∈ L²(Ω)`, `‖h‖₂ ≤ 2 ‖max (f, q) − f‖₂`
(`IsObstacleSolution.exists_dirichletForm_eq_load`), so `u` is the weak solution of
`−Δu + u = f + h + u` on `H¹₀(Ω)`, and the linear regularity theory
(`Elliptic.regularity_dirichlet`, [brezis2011functional] Theorem 9.25) applies; its constant is
the one here. -/
theorem regularity_obstacle
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : SobolevEuclidean (d + 1) 1 2 Ω)
        (q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
        (∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ) →
        ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
          (u : SobolevEuclidean (d + 1) 1 2 Ω), IsObstacleSolution Ω ψ f u →
          MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω
            volume ∧
          ∀ U : SobolevEuclidean (d + 1) 2 2 Ω,
            fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u →
            ‖U‖ ≤ C * (‖f‖ + 2 * ‖f ⊔ q - f‖ + ‖weakDeriv u 0‖) := by
  obtain ⟨C, hC0, hC⟩ := regularity_dirichlet hΩ hΓ
  refine ⟨C, hC0, fun ψ q hψ f u hu ↦ ?_⟩
  obtain ⟨h, hh, heq⟩ := hu.exists_dirichletForm_eq_load (hΩ.of_le (by norm_num)) hΓ hψ
  obtain ⟨hmem, hbound⟩ := hC (f + h + weakDeriv u 0) u (hu.isGalerkinSolution_laplace heq)
  refine ⟨hmem, fun U hU ↦ (hbound U hU).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  calc ‖f + h + weakDeriv u 0‖ ≤ ‖f + h‖ + ‖weakDeriv u 0‖ := norm_add_le _ _
    _ ≤ ‖f‖ + ‖h‖ + ‖weakDeriv u 0‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖f‖ + 2 * ‖f ⊔ q - f‖ + ‖weakDeriv u 0‖ := by gcongr

end Regularity

/-! ### Obstacles in `H²(Ω)`: `−Δψ ∈ L²(Ω)` -/

section ObstacleH2

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **The weak Laplacian of an `H²(Ω)` function is its distributional one**: if `w ∈ H²(Ω)` and
`v ∈ H¹(Ω)` have the same function, then `∫_Ω ∇v · ∇Φ = ∫_Ω (−∑ᵢ ∂ᵢᵢw) Φ` for every `Φ ∈ H¹₀(Ω)`.
For a test function `Φ`, `∫ ∂ᵢv ∂ᵢΦ = −∫ ∂ᵢᵢw Φ` is the weak-derivative identity of the `H²`
element (the first derivatives of `w` and `v` agree by uniqueness of weak derivatives), and the
identity extends from the test functions to `H¹₀(Ω)`
(`Elliptic.dirichletForm_eq_load_of_forall_testFunctions`). This is the identity inside
`mem_dirichletLaplacianDomain_of_sobolev_two` (`Numlib/Analysis/PDE/DirichletLaplacian.lean`),
freed of the hypothesis `v ∈ H¹₀(Ω)`, which the obstacle needs since `ψ ∉ H¹₀(Ω)` in general. -/
theorem dirichletForm_eq_load_neg_sobolevLaplacianL (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω}
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w) :
    ∀ Φ ∈ SobolevEuclideanZero N 1 2 Ω,
      dirichletForm Ω v Φ = load Ω (-sobolevLaplacianL Ω w) Φ := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  -- the first derivatives of `v` are the functions of the `∂ᵢ w ∈ H¹(Ω)`
  have hd : ∀ i, ⇑(weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) := by
    intro i
    have h1 := (weakDeriv_hasWeakIteratedLineDerivOn_single v i).congr_ae hvw
      (EventuallyEq.refl _ _)
    have h2 := hasWeakIteratedLineDerivOn_fn_partialDeriv i w
    rw [EuclideanSpace.basisFun_toBasis_apply] at h2
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq h2)
  -- the datum, as a function
  have hg : ⇑(-sobolevLaplacianL Ω w) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ -∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x := by
    rw [sobolevLaplacianL_apply]
    filter_upwards [Lp.coeFn_neg
      (∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))),
      Lp.coeFn_finsetSum Finset.univ
        fun i ↦ weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))] with x hx1 hx2
    rw [hx1, Pi.neg_apply, hx2, Finset.sum_apply]
  -- the equation against test functions
  have heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω v Φ = load Ω (-sobolevLaplacianL Ω w) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [dirichletForm_apply_eq_of_ae_eq hd hψ, load_apply_eq_of_ae_eq hg hψ]
    have hterm : ∀ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) x
          * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x * ψ x := by
      intro i
      have key := (weakDeriv_hasWeakIteratedLineDerivOn_single
        (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) i)
        |>.integral_fderiv_mul_eq_of_eqOn ψ (fun _ _ ↦ rfl)
      rw [weakDeriv_partialDeriv] at key
      calc ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) x
              * fderiv ℝ ψ x (EuclideanSpace.single i 1)
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              fderiv ℝ ψ x (EuclideanSpace.single i 1)
                * fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w)
                  x :=
            integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              ψ x * weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x := key
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x * ψ x := by
            congr 1
            exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    simp only [hterm, Finset.sum_neg_distrib]
    have hI : ∀ i, Integrable
        (fun x ↦ weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x * ψ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ by
      have := ((weakDeriv_hasWeakIteratedLineDerivOn_single
        (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) i)
        |>.integrable_smul_weakDeriv ψ).integrableOn (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
      rw [weakDeriv_partialDeriv] at this
      exact this.congr (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    rw [← integral_finsetSum _ fun i _ ↦ hI i, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [Finset.sum_mul, neg_mul])
  exact fun Φ hΦ ↦ dirichletForm_eq_load_of_forall_testFunctions heq hΦ

/-- `‖∑ᵢ ∂ᵢᵢ w‖₂ ≤ N ‖w‖_{H²}`. -/
theorem norm_sobolevLaplacianL_le (w : SobolevEuclidean N 2 2 Ω) :
    ‖sobolevLaplacianL Ω w‖ ≤ N * ‖w‖ := by
  rw [sobolevLaplacianL_apply]
  calc ‖∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))‖
      ≤ ∑ i, ‖weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ‖w‖ := Finset.sum_le_sum fun i _ ↦ norm_weakDeriv_le w _
    _ = N * ‖w‖ := by simp

end ObstacleH2

/-! ### Two norm estimates for the bound of Theorem 11.3.12 -/

section Estimates

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **The positive part is contractive in `H¹(Ω)`**: if `w ∈ H¹(Ω)` has function `ψ⁺` for
`ψ ∈ H¹(Ω)`, then `‖w‖_{H¹} ≤ ‖ψ‖_{H¹}`, since `|ψ⁺| ≤ |ψ|` and `∂ᵢψ⁺ = 1_{ψ > 0} ∂ᵢψ`. -/
theorem _root_.SobolevEuclidean.norm_le_of_fn_ae_eq_posPart {ψ w : SobolevEuclidean N 1 2 Ω}
    (hw : fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ max (fn ψ x) 0) :
    ‖w‖ ≤ ‖ψ‖ := by
  have h0 : ‖weakDeriv w 0‖ ≤ ‖weakDeriv ψ 0‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hw] with x hx
    have e : (weakDeriv w 0) x = max (fn ψ x) 0 := hx
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    change |max (fn ψ x) 0| ≤ |fn ψ x|
    exact abs_le.2 ⟨by linarith [abs_nonneg (fn ψ x), le_max_right (fn ψ x) 0],
      max_le (le_abs_self _) (abs_nonneg _)⟩
  have hi : ∀ i, ‖weakDeriv w (MultiIndexLE.single i)‖ ≤ ‖weakDeriv ψ (MultiIndexLE.single i)‖ :=
    fun i ↦ by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [weakDeriv_single_ae_eq_of_fn_ae_eq_posPart hw i] with x hx
      rw [hx]
      exact norm_indicator_le_norm_self _ _
  have hsq : ‖w‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    refine add_le_add (pow_le_pow_left₀ (norm_nonneg _) h0 2)
      (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- `‖max (f, q) − f‖₂ ≤ ‖q − f‖₂`, since `max (f, q) − f = (q − f)⁺`. -/
theorem norm_sup_sub_le (f q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖f ⊔ q - f‖ ≤ ‖q - f‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (f ⊔ q) f, Lp.coeFn_sup f q, Lp.coeFn_sub q f] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.sup_apply, h3, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total (f x) (q x) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, sub_self, abs_zero]
    exact abs_nonneg _

end Estimates

/-! ### The a priori `H¹` bound and the `H²` bound for obstacles in `H²(Ω)` -/

section APriori

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- The real inequality behind the a priori bound: `t² ≤ K (s t + s²)` with `K ≥ 1` forces
`t ≤ 2 K s`. -/
theorem le_two_mul_of_sq_le {K s t : ℝ} (hK : 1 ≤ K) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : t ^ 2 ≤ K * (s * t + s ^ 2)) : t ≤ 2 * K * s := by
  by_contra hcon
  have hlt : 2 * K * s < t := lt_of_not_ge hcon
  have hKs : 0 ≤ K * s := mul_nonneg (by linarith) hs
  nlinarith [mul_lt_mul_of_pos_left hlt (show (0 : ℝ) < t by linarith), mul_nonneg hKs hs,
    mul_nonneg hKs ht]

/-- **Poincaré's inequality for the Dirichlet form**: `‖u‖²_{H¹} ≤ (1 + (2R)²) ∫_Ω |∇u|²` for
`u ∈ H¹₀(Ω)` and `Ω ⊆ B(0, R)` (`SobolevEuclideanZero.norm_le_gradNorm` at `p = 2`). -/
theorem norm_sq_le_dirichletForm_self {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ‖u‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * dirichletForm Ω u u := by
  have hP := SobolevEuclideanZero.norm_le_gradNorm (p := 2) (by norm_num) hR hΩ ⟨u, hu⟩
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow] at hP
  rw [dirichletForm_self_eq_gradNorm_sq]
  have hK : (0 : ℝ) ≤ 1 + (2 * R) ^ 2 := by positivity
  calc ‖u‖ ^ 2 ≤ (√(1 + (2 * R) ^ 2) * gradNorm u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
    _ = (1 + (2 * R) ^ 2) * gradNorm u ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]

/-- **The a priori `H¹` bound for the obstacle problem**: for `Ω ⊆ B(0, R)`, an admissible
`w ∈ H¹₀(Ω)` with `w ≥ ψ` and a solution `u` of the obstacle problem,
`‖u‖_{H¹} ≤ 2 (1 + (2R)²) (‖w‖_{H¹} + ‖f‖₂)`. Testing the variational inequality with `v = w`
gives `a(u, u) ≤ a(u, w) − ℓ(w) + ℓ(u) ≤ ‖u‖ ‖w‖ + ‖f‖ ‖w‖ + ‖f‖ ‖u‖`, and
`a(u, u) ≥ (1 + (2R)²)⁻¹ ‖u‖²` by Poincaré's inequality. -/
theorem IsObstacleSolution.norm_le {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {w : SobolevEuclidean (d + 1) 1 2 Ω} (hw : w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hψw : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn ψ x ≤ fn w x) :
    ‖u‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖w‖ + ‖f‖) := by
  have hK : (1 : ℝ) ≤ 1 + (2 * R) ^ 2 := by
    have := sq_nonneg (2 * R)
    linarith
  have hpos : (0 : ℝ) < 1 + (2 * R) ^ 2 := by positivity
  have hVI := hu.ineq w hw hψw
  have e1 : load Ω f (w - u) = load Ω f w - load Ω f u := (load Ω f).map_sub w u
  have e2 : dirichletForm Ω u (w - u) = dirichletForm Ω u w - dirichletForm Ω u u :=
    (dirichletForm Ω u).map_sub w u
  have hα := norm_sq_le_dirichletForm_self hR hΩ hu.mem_zero
  have hM : |dirichletForm Ω u w| ≤ ‖u‖ * ‖w‖ := by
    have := dirichletForm_isBoundedWith Ω u w
    rwa [one_mul, Real.norm_eq_abs] at this
  have hℓ : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω, |load Ω f v| ≤ ‖f‖ * ‖v‖ := fun v ↦
    (abs_load_le Ω f v).trans (mul_le_mul_of_nonneg_left (norm_weakDeriv_le v 0) (norm_nonneg _))
  have hℓw := hℓ w
  have hℓu := hℓ u
  have h2 : ‖u‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * (‖u‖ * ‖w‖ + ‖f‖ * ‖w‖ + ‖f‖ * ‖u‖) := by
    refine hα.trans (mul_le_mul_of_nonneg_left ?_ hpos.le)
    have := abs_le.1 hM
    have := abs_le.1 hℓw
    have := abs_le.1 hℓu
    linarith
  have hquad : ‖u‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * ((‖w‖ + ‖f‖) * ‖u‖ + (‖w‖ + ‖f‖) ^ 2) := by
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hpos.le)
    nlinarith [norm_nonneg u, norm_nonneg w, norm_nonneg f]
  exact le_two_mul_of_sq_le hK (by positivity) (norm_nonneg _) hquad

/-- **[han2009theoretical] Theorem 11.3.12 at `p = 2`, for the Laplacian, an obstacle in
`H²(Ω)` and a `C²` domain**: on a `C²` chart domain `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}` there is a constant
`C` such that for every obstacle `ψ ∈ H¹(Ω)` which is the function of some `Ψ ∈ H²(Ω)` and whose
positive part is the function of an element of `H¹₀(Ω)` (the book's "`ψ ≤ 0` on `Γ`"), every
`f ∈ L²(Ω)` and every solution `u` of the obstacle problem, `u ∈ H²(Ω)` with
`‖u‖_{H²(Ω)} ≤ C (‖f‖_{L²(Ω)} + ‖Ψ‖_{H²(Ω)})`.

The obstacle has `−Δψ = q := −∑ᵢ ∂ᵢᵢΨ ∈ L²(Ω)` weakly
(`dirichletForm_eq_load_neg_sobolevLaplacianL`), so `regularity_obstacle` bounds `‖u‖_{H²}` by
`C₀ (‖f‖ + 2 ‖max (f, q) − f‖ + ‖u‖₂)`;
`‖max (f, q) − f‖ ≤ ‖q − f‖ ≤ ‖f‖ + (d + 1) ‖Ψ‖_{H²}` and the a priori bound
`IsObstacleSolution.norm_le` tested with `w = ψ⁺ ∈ H¹₀(Ω)`, `‖ψ⁺‖_{H¹} ≤ ‖ψ‖_{H¹} ≤ ‖Ψ‖_{H²}`,
give `‖u‖₂ ≤ 2 (1 + (2R)²) (‖Ψ‖_{H²} + ‖f‖)`. -/
theorem regularity_obstacle_sobolev_two {R : ℝ} (hR : 0 ≤ R)
    (hΩb : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ψ : SobolevEuclidean (d + 1) 2 2 Ω) (ψ : SobolevEuclidean (d + 1) 1 2 Ω),
        fn ψ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn Ψ →
        (∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
          fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            fun x ↦ max (fn ψ x) 0) →
        ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
          (u : SobolevEuclidean (d + 1) 1 2 Ω), IsObstacleSolution Ω ψ f u →
          MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω
            volume ∧
          ∀ U : SobolevEuclidean (d + 1) 2 2 Ω,
            fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u →
            ‖U‖ ≤ C * (‖f‖ + ‖Ψ‖) := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (isBounded_ball.subset hΩb).closure.subset frontier_subset_closure
  obtain ⟨C₀, hC₀, hreg⟩ := regularity_obstacle hΩ hΓ
  refine ⟨C₀ * (3 + 2 * ((d : ℝ) + 1) + 2 * (1 + (2 * R) ^ 2)), by positivity,
    fun Ψ ψ hψΨ hψ f u hu ↦ ?_⟩
  obtain ⟨w, hw, hwψ⟩ := hψ
  have hq := dirichletForm_eq_load_neg_sobolevLaplacianL Ψ hψΨ
  obtain ⟨hmem, hbound⟩ := hreg ψ _ hq f u hu
  refine ⟨hmem, fun U hU ↦ (hbound U hU).trans ?_⟩
  -- `‖ψ‖_{H¹} ≤ ‖Ψ‖_{H²}`
  have hψ1 : ‖ψ‖ ≤ ‖Ψ‖ := by
    have e : ψ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 Ω volume
        (by norm_num) Ψ :=
      SobolevMultiIndex.ext_of_fn_ae_eq hψΨ
    rw [e]
    exact norm_toLowerOrder_le _ _
  -- `‖max (f, q) − f‖ ≤ ‖f‖ + (d + 1) ‖Ψ‖`
  have h1 : ‖f ⊔ -sobolevLaplacianL Ω Ψ - f‖ ≤ ‖f‖ + ((d : ℝ) + 1) * ‖Ψ‖ := by
    refine (norm_sup_sub_le f _).trans ((norm_sub_le _ f).trans ?_)
    rw [norm_neg]
    have := norm_sobolevLaplacianL_le Ψ
    push_cast at this
    linarith
  -- `‖u‖₂ ≤ ‖u‖_{H¹} ≤ 2 (1 + (2R)²) (‖Ψ‖ + ‖f‖)`
  have hw1 : ‖w‖ ≤ ‖Ψ‖ := (SobolevEuclidean.norm_le_of_fn_ae_eq_posPart hwψ).trans hψ1
  have hu1 : ‖u‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖w‖ + ‖f‖) :=
    hu.norm_le hR hΩb hw (by
      filter_upwards [hwψ] with x hx
      rw [hx]
      exact le_max_left _ _)
  have hK0 : (0 : ℝ) ≤ 1 + (2 * R) ^ 2 := by positivity
  have hu2 : ‖weakDeriv u 0‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖Ψ‖ + ‖f‖) :=
    (norm_weakDeriv_le u 0).trans
      (hu1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg _
  have hΨ0 : 0 ≤ ‖Ψ‖ := norm_nonneg _
  have hd1 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  calc C₀ * (‖f‖ + 2 * ‖f ⊔ -sobolevLaplacianL Ω Ψ - f‖ + ‖weakDeriv u 0‖)
      ≤ C₀ * ((3 + 2 * ((d : ℝ) + 1) + 2 * (1 + (2 * R) ^ 2)) * (‖f‖ + ‖Ψ‖)) :=
        mul_le_mul_of_nonneg_left (by
          linarith [mul_nonneg hd1 hf0, mul_nonneg hK0 hf0, mul_nonneg hK0 hΨ0,
            mul_nonneg hd1 hΨ0]) hC₀
    _ = C₀ * (3 + 2 * ((d : ℝ) + 1) + 2 * (1 + (2 * R) ^ 2)) * (‖f‖ + ‖Ψ‖) := by ring

end APriori

end Elliptic

end
