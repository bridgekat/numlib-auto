import Numlib.Analysis.PDE.Elliptic.MaximumPrinciple
import Numlib.Analysis.PDE.Heat

/-!
# The maximum principle for the heat equation

The weak maximum principle for the heat equation by Stampacchia's truncation method in time:
[brezis2011functional] Theorem 10.3 (`min{0, inf u₀} ≤ u(t) ≤ max{0, sup u₀}`) and
Corollary 10.4 (positivity, the `L^∞` contraction), for the solutions of
`Numlib/Analysis/PDE/Heat` on an **arbitrary** open set. The classical maximum principle of
Theorem 10.6 is in `Heat/Classical`.

## The argument

Three ingredients, all elementary on the weak solution: (a) a truncation `G` of class `C¹` with
`0 ≤ G' ≤ 1`, `G = 0` on `(−∞, 0]`, `G > 0` on `(0, ∞)` — the function of the proof of
Theorem 9.27, chapter 9's `Elliptic.IsStampacchiaTruncation G 1`, here `Heat.IsTruncation` — with
primitive `H(s) = ∫₀ˢ G` (`Heat.truncationPrimitive`); (b) the functional
`Φ(v) = ∫_Ω H(v − K)` on `L²(Ω)` (`Heat.truncationFunctional`), finite for `K ≥ 0` since
`0 ≤ H(s) ≤ s²`, and its derivative along a `C¹` curve, `d/dt Φ(u(t)) = ⟪G(u(t) − K), u'(t)⟫`,
obtained from the elementary estimate `|H(a) − H(b) − G(b)(a − b)| ≤ (a − b)²` rather than
from the Fréchet differentiability of a Nemytskii operator; (c) `G(v − K) ∈ H¹₀(Ω)` with
`∇G(v − K) = G'(v − K) ∇v` for `v ∈ H¹₀(Ω)` — chapter 9's chain rule (Proposition 9.5) with
`SobolevMultiIndexZero.contDiff_comp_mem`, applied to `t ↦ G(t − K)`, which vanishes at `0`
because `K ≥ 0`. With (a)–(c): `φ(t) = Φ(u(t))` is continuous on `[0, ∞)`, `φ(0) = 0` when
`u₀ ≤ K` a.e., `φ ≥ 0`, `C¹` on `(0, ∞)` with `φ' = ⟪G(u − K), Δu⟫ = −∫ G'(u − K) |∇u|² ≤ 0`,
so `φ ≡ 0`, i.e. `u(t) ≤ K` a.e. The theorem is stated for every admissible bound `K ≥ 0`; the
book's `K = max{0, sup u₀}` is the least such `K`, and the surface recovers the `essSup` form.

Corollary 10.5 (`u ∈ C(Q̄)` for continuous data vanishing on `Γ`) is planned here
(`Heat.exists_testFunction_tendsto_of_continuousOn`, `Heat.IsSolution.continuousOn_spaceTime`)
and not yet proved.

## References

[brezis2011functional], §10.2: Theorem 10.3, Corollary 10.4, and the proof of Theorem 9.27.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

/-! ### The truncation and its primitive -/

/-- **A truncation function**: `G ∈ C¹(ℝ)` with `0 ≤ G' ≤ 1`, `G = 0` on `(−∞, 0]` and `G > 0`
on `(0, ∞)` — the function `G` fixed in the proof of [brezis2011functional] Theorem 9.27 and
reused in Theorem 10.3, chapter 9's `Elliptic.IsStampacchiaTruncation` with `M = 1`. -/
abbrev IsTruncation (G : ℝ → ℝ) : Prop := IsStampacchiaTruncation G 1

/-- A truncation function exists (`Elliptic.stampacchiaTruncation`). -/
theorem exists_isTruncation : ∃ G : ℝ → ℝ, IsTruncation G :=
  ⟨_, isStampacchiaTruncation_stampacchiaTruncation⟩

variable {G : ℝ → ℝ}

/-- `|G a − G b| ≤ |a − b|`: a truncation is `1`-Lipschitz. -/
theorem IsTruncation.abs_sub_le (hG : IsTruncation G) (a b : ℝ) : |G a - G b| ≤ |a - b| := by
  simpa using abs_sub_le_mul_of_abs_deriv_le hG.contDiff hG.abs_deriv_le a b

/-- `|G s| ≤ |s|`. -/
theorem IsTruncation.abs_le (hG : IsTruncation G) (s : ℝ) : |G s| ≤ |s| := by
  simpa [hG.zero] using hG.abs_sub_le s 0

/-- `G s ≤ s` for `s ≥ 0`. -/
theorem IsTruncation.le_self (hG : IsTruncation G) {s : ℝ} (hs : 0 ≤ s) : G s ≤ s :=
  (le_abs_self _).trans ((hG.abs_le s).trans_eq (abs_of_nonneg hs))

/-- **The primitive `H(s) = ∫₀ˢ G`** of a truncation ([brezis2011functional], proof of
Theorem 10.3). -/
def truncationPrimitive (G : ℝ → ℝ) (s : ℝ) : ℝ := ∫ σ in (0 : ℝ)..s, G σ

/-- `H' = G`. -/
theorem hasDerivAt_truncationPrimitive (hG : IsTruncation G) (s : ℝ) :
    HasDerivAt (truncationPrimitive G) (G s) s :=
  (hG.contDiff.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- `H` is continuous. -/
theorem continuous_truncationPrimitive (hG : IsTruncation G) :
    Continuous (truncationPrimitive G) :=
  continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_truncationPrimitive hG s).continuousAt

/-- `H = 0` on `(−∞, 0]`. -/
theorem truncationPrimitive_of_nonpos (hG : IsTruncation G) {s : ℝ} (hs : s ≤ 0) :
    truncationPrimitive G s = 0 := by
  unfold truncationPrimitive
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun σ hσ ↦ ?_).trans
    intervalIntegral.integral_zero
  rw [uIcc_of_ge hs] at hσ
  exact hG.eq_zero_of_nonpos σ hσ.2

/-- `H > 0` on `(0, ∞)`. -/
theorem truncationPrimitive_pos (hG : IsTruncation G) {s : ℝ} (hs : 0 < s) :
    0 < truncationPrimitive G s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hG.contDiff.continuous.intervalIntegrable _ _)
    (fun σ hσ ↦ hG.pos_of_pos σ hσ.1) hs

/-- `H ≥ 0`. -/
theorem truncationPrimitive_nonneg (hG : IsTruncation G) (s : ℝ) :
    0 ≤ truncationPrimitive G s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [truncationPrimitive_of_nonpos hG hs]
  · exact (truncationPrimitive_pos hG hs).le

/-- `H s = 0` forces `s ≤ 0`. -/
theorem le_zero_of_truncationPrimitive_eq_zero (hG : IsTruncation G) {s : ℝ}
    (h : truncationPrimitive G s = 0) : s ≤ 0 := by
  by_contra hs
  exact (truncationPrimitive_pos hG (not_le.1 hs)).ne' h

/-- **`H s ≤ s²`**: `G σ ≤ σ` on `[0, s]`. -/
theorem truncationPrimitive_le_sq (hG : IsTruncation G) (s : ℝ) :
    truncationPrimitive G s ≤ s ^ 2 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [truncationPrimitive_of_nonpos hG hs]
    positivity
  · have h1 : ‖∫ σ in (0 : ℝ)..s, G σ‖ ≤ s * |s - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ by
        rw [uIoc_of_le hs.le] at hσ
        rw [Real.norm_eq_abs, abs_of_nonneg (hG.nonneg σ)]
        exact (hG.le_self hσ.1.le).trans hσ.2
    rw [sub_zero, abs_of_pos hs, ← sq] at h1
    exact (le_abs_self _).trans h1

/-- **The second-order bound** `|H a − H b − G b (a − b)| ≤ (a − b)²`, from
`H a − H b − G b (a − b) = ∫_b^a (G σ − G b) dσ` and the Lipschitz bound on `G`. -/
theorem abs_truncationPrimitive_sub_sub_le (hG : IsTruncation G) (a b : ℝ) :
    |truncationPrimitive G a - truncationPrimitive G b - G b * (a - b)| ≤ (a - b) ^ 2 := by
  have hI : ∀ x y : ℝ, IntervalIntegrable G volume x y := fun x y ↦
    hG.contDiff.continuous.intervalIntegrable x y
  have h1 : truncationPrimitive G a - truncationPrimitive G b = ∫ σ in b..a, G σ :=
    intervalIntegral.integral_interval_sub_left (hI 0 a) (hI 0 b)
  have h2 : G b * (a - b) = ∫ σ in b..a, G b := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [h1, h2, ← intervalIntegral.integral_sub (hI b a) (intervalIntegrable_const)]
  have h3 : ‖∫ σ in b..a, (G σ - G b)‖ ≤ |a - b| * |a - b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ by
      rw [Real.norm_eq_abs]
      refine (hG.abs_sub_le σ b).trans ?_
      rcases le_or_gt b a with hba | hab
      · rw [uIoc_of_le hba] at hσ
        rw [abs_of_nonneg (by linarith [hσ.1]), abs_of_nonneg (by linarith)]
        linarith [hσ.2]
      · rw [uIoc_of_ge hab.le] at hσ
        rw [abs_of_nonpos (by linarith [hσ.2]), abs_of_neg (by linarith)]
        linarith [hσ.1]
  rw [Real.norm_eq_abs] at h3
  calc |∫ σ in b..a, (G σ - G b)| ≤ |a - b| * |a - b| := h3
    _ = (a - b) ^ 2 := by rw [← sq, sq_abs]

/-- **`0 ≤ H(s − K) ≤ s²` for `K ≥ 0`**: the integrand of the truncation functional is
dominated by `s²`. -/
theorem truncationPrimitive_sub_le_sq (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K) (s : ℝ) :
    truncationPrimitive G (s - K) ≤ s ^ 2 := by
  rcases le_or_gt (s - K) 0 with hs | hs
  · rw [truncationPrimitive_of_nonpos hG hs]
    positivity
  · refine (truncationPrimitive_le_sq hG _).trans ?_
    have : 0 ≤ s := by linarith
    nlinarith

/-! ### The truncation functional `Φ(v) = ∫_Ω H(v − K)` on `L²(Ω)` -/

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- `‖v‖² = ∫_Ω v²` in `L²(Ω)`. -/
theorem norm_sq_eq_integral_sq (w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖w‖ ^ 2 = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), w x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ (sq _).symm)

/-- `v² ∈ L¹(Ω)` for `v ∈ L²(Ω)`. -/
theorem integrable_sq (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Integrable (fun x ↦ v x ^ 2) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)

/-- **The integrand `H(v − K)` is integrable** on `Ω` for `v ∈ L²(Ω)` and `K ≥ 0`: it is
measurable and dominated by `v²`. -/
theorem integrable_truncationPrimitive_sub (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Integrable (fun x ↦ truncationPrimitive G (v x - K))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine (integrable_sq v).mono' ((continuous_truncationPrimitive hG).comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable v).sub aestronglyMeasurable_const)) (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (truncationPrimitive_nonneg hG _)]
  exact truncationPrimitive_sub_le_sq hG hK _

variable (Ω) in
/-- **The truncation functional** `Φ(v) = ∫_Ω H(v(x) − K) dx` of the proof of
[brezis2011functional] Theorem 10.3, as a function of `v ∈ L²(Ω)`; the book's
`φ(t) = Φ(u(t))`. -/
def truncationFunctional (G : ℝ → ℝ) (K : ℝ)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : ℝ :=
  ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), truncationPrimitive G (v x - K)

/-- `Φ ≥ 0`. -/
theorem truncationFunctional_nonneg (hG : IsTruncation G) (K : ℝ)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    0 ≤ truncationFunctional Ω G K v :=
  integral_nonneg fun _ ↦ truncationPrimitive_nonneg hG _

/-- `Φ(v) = 0` when `v ≤ K` almost everywhere. -/
theorem truncationFunctional_eq_zero_of_ae_le (hG : IsTruncation G) {K : ℝ}
    {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hv : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), v x ≤ K) :
    truncationFunctional Ω G K v = 0 := by
  unfold truncationFunctional
  rw [integral_eq_zero_of_ae]
  filter_upwards [hv] with x hx
  exact truncationPrimitive_of_nonpos hG (by linarith)

/-- **`Φ(v) = 0` forces `v ≤ K` almost everywhere**, for `K ≥ 0`: the nonnegative integrand
`H(v − K)` vanishes a.e., and `H(s) = 0` only for `s ≤ 0`. -/
theorem ae_le_of_truncationFunctional_eq_zero (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : truncationFunctional Ω G K v = 0) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), v x ≤ K := by
  have := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x ↦ truncationPrimitive_nonneg hG (v x - K))
    (integrable_truncationPrimitive_sub hG hK v)).1 h
  filter_upwards [this] with x hx
  have := le_zero_of_truncationPrimitive_eq_zero hG hx
  linarith

/-- **`G(v − K) ∈ L²(Ω)`** for `v ∈ L²(Ω)`, `K ≥ 0`: `|G(s − K)| ≤ |s|`. -/
theorem memLp_truncation_sub (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    MemLp (fun x ↦ G (v x - K)) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine (Lp.memLp v).of_ae_norm_le_mul (hG.contDiff.continuous.comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable v).sub aestronglyMeasurable_const)) (c := 1)
    (Eventually.of_forall fun x ↦ ?_)
  rw [one_mul]
  rcases le_or_gt (v x - K) 0 with hs | hs
  · rw [hG.eq_zero_of_nonpos _ hs, abs_zero]
    exact abs_nonneg _
  · rw [abs_of_pos (hG.pos_of_pos _ hs)]
    exact (hG.le_self hs.le).trans ((sub_le_self _ hK).trans (le_abs_self _))

variable (Ω) in
/-- **The truncation `G(v − K)` as an element of `L²(Ω)`**, the book's `G(u(t) − K)`. -/
def truncationL2 (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (memLp_truncation_sub hG hK v).toLp _

/-- The function of `truncationL2 v` is `G(v − K)`. -/
theorem coeFn_truncationL2 (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⇑(truncationL2 Ω hG hK v) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ G (v x - K) :=
  (memLp_truncation_sub hG hK v).coeFn_toLp

/-- `‖G(v − K)‖ ≤ ‖v‖`. -/
theorem norm_truncationL2_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖truncationL2 Ω hG hK v‖ ≤ ‖v‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_truncationL2 hG hK v] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_or_gt (v x - K) 0 with hs | hs
  · rw [hG.eq_zero_of_nonpos _ hs, abs_zero]
    exact abs_nonneg _
  · rw [abs_of_pos (hG.pos_of_pos _ hs)]
    exact (hG.le_self hs.le).trans ((sub_le_self _ hK).trans (le_abs_self _))

/-- **The key estimate** `|Φ(v + w) − Φ(v) − ⟪G(v − K), w⟫| ≤ ‖w‖²` ([brezis2011functional],
proof of Theorem 10.3, the differentiation of `φ`): integrate the pointwise second-order bound
`|H(a) − H(b) − G(b)(a − b)| ≤ (a − b)²`. -/
theorem abs_truncationFunctional_sub_sub_inner_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    |truncationFunctional Ω G K (v + w) - truncationFunctional Ω G K v
      - ⟪truncationL2 Ω hG hK v, w⟫_ℝ| ≤ ‖w‖ ^ 2 := by
  have h1 := integrable_truncationPrimitive_sub hG hK (v + w)
  have h2 := integrable_truncationPrimitive_sub hG hK v
  have h3 : Integrable (fun x ↦ truncationL2 Ω hG hK v x * w x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (L2.integrable_inner (𝕜 := ℝ) (truncationL2 Ω hG hK v) w).congr
      (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])
  have h12 : Integrable (fun x ↦ truncationPrimitive G ((v + w) x - K)
      - truncationPrimitive G (v x - K)) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    h1.sub h2
  have h123 : Integrable (fun x ↦ truncationPrimitive G ((v + w) x - K)
      - truncationPrimitive G (v x - K) - truncationL2 Ω hG hK v x * w x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := h12.sub h3
  rw [L2.inner_eq_integral_mul, truncationFunctional, truncationFunctional, ← integral_sub h1 h2,
    ← integral_sub h12 h3, norm_sq_eq_integral_sq]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae h123.abs (integrable_sq w) ?_)
  filter_upwards [Lp.coeFn_add v w, coeFn_truncationL2 hG hK v] with x hx1 hx2
  rw [hx1, Pi.add_apply, hx2]
  have := abs_truncationPrimitive_sub_sub_le hG (v x + w x - K) (v x - K)
  rwa [show v x + w x - K - (v x - K) = w x by ring] at this

/-- **`Φ` is Lipschitz on bounded sets**: `|Φ(w) − Φ(v)| ≤ ‖v‖ ‖w − v‖ + ‖w − v‖²`. -/
theorem abs_truncationFunctional_sub_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    |truncationFunctional Ω G K w - truncationFunctional Ω G K v|
      ≤ ‖v‖ * ‖w - v‖ + ‖w - v‖ ^ 2 := by
  have h1 := abs_truncationFunctional_sub_sub_inner_le hG hK v (w - v)
  rw [add_sub_cancel] at h1
  have h2 : |⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| ≤ ‖v‖ * ‖w - v‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_truncationL2_le hG hK v) (norm_nonneg _))
  calc |truncationFunctional Ω G K w - truncationFunctional Ω G K v|
      = |(truncationFunctional Ω G K w - truncationFunctional Ω G K v
          - ⟪truncationL2 Ω hG hK v, w - v⟫_ℝ) + ⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| := by
        congr 1
        ring
    _ ≤ |truncationFunctional Ω G K w - truncationFunctional Ω G K v
          - ⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| + |⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| :=
        abs_add_le _ _
    _ ≤ ‖w - v‖ ^ 2 + ‖v‖ * ‖w - v‖ := add_le_add h1 h2
    _ = ‖v‖ * ‖w - v‖ + ‖w - v‖ ^ 2 := add_comm _ _

/-- **`Φ` is continuous on `L²(Ω)`.** -/
theorem continuous_truncationFunctional (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K) :
    Continuous (truncationFunctional Ω G K) := by
  refine continuous_iff_continuousAt.2 fun v ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun w ↦ ‖v‖ * ‖w - v‖ + ‖w - v‖ ^ 2) (𝓝 v) (𝓝 (‖v‖ * 0 + 0 ^ 2)) := by
    have h0 : Tendsto (fun w ↦ ‖w - v‖) (𝓝 v) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id
    exact (h0.const_mul _).add (h0.pow 2)
  rw [mul_zero, zero_pow two_ne_zero, add_zero] at hlim
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun w ↦ (Real.norm_eq_abs _).trans_le (abs_truncationFunctional_sub_le hG hK v w)) hlim

/-! ### The truncation of an `H¹₀` function, and `⟪A u, G(u − K)⟫ ≥ 0` -/

/-- **`G(v − K) ∈ H¹₀(Ω)` with `∇G(v − K) = G'(v − K) ∇v`** for `v ∈ H¹₀(Ω)` and `K ≥ 0`
(Proposition 9.5 and `SobolevMultiIndexZero.contDiff_comp_mem`, the function `t ↦ G(t − K)`
vanishing at `0` because `K ≥ 0`): there is `w ∈ H¹₀(Ω)` whose function is `G(v − K)` and
whose partial derivatives are `G'(v − K) ∂ᵢv` almost everywhere. -/
theorem truncation_comp_mem_sobolevZero (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω) :
    ∃ w : SobolevEuclidean N 1 2 Ω, w ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ G (fn v x - K)) ∧
      ∀ i, (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ deriv G (fn v x - K) * weakDeriv v (MultiIndexLE.single i) x := by
  obtain ⟨w, hw⟩ := exists_truncation_elem hG v (Or.inr hK)
  refine ⟨w, ?_, hw, fun i ↦ weakDeriv_single_ae_eq_of_fn_ae_eq_truncation hG hw i⟩
  exact SobolevMultiIndexZero.contDiff_comp_mem ENNReal.ofNat_ne_top hv (hG.contDiff_sub K)
    (by rw [zero_sub]; exact hG.eq_zero_of_nonpos (-K) (by linarith)) (hG.abs_deriv_sub_le K) hw

/-- **`∫_Ω ∇v · ∇G(v − K) = ∫_Ω G'(v − K) |∇v|² ≥ 0`** for `v ∈ H¹₀(Ω)` and the element `w` of
`truncation_comp_mem_sobolevZero`. -/
theorem dirichletForm_truncation_nonneg (hG : IsTruncation G) {K : ℝ}
    {v w : SobolevEuclidean N 1 2 Ω}
    (hw : ∀ i, (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ deriv G (fn v x - K) * weakDeriv v (MultiIndexLE.single i) x) :
    0 ≤ dirichletForm Ω v w := by
  rw [dirichletForm_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_all_iff.2 hw] with x hx
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [hx i, mul_comm, mul_assoc]
  exact mul_nonneg (hG.deriv_nonneg _) (mul_self_nonneg _)

/-- **`⟪A f, G(f − K)⟫ ≥ 0`** for `f ∈ D(A)` and `K ≥ 0` ([brezis2011functional], proof of
Theorem 10.3: `∫ G(u − K) Δu = −∫ G'(u − K) |∇u|² ≤ 0`): the truncation `G(f − K)` is the function
of an element of `H¹₀(Ω)`, and the defining identity of `A` reads
`⟪A f, G(f − K)⟫ = ∫ ∇v · ∇G(v − K)`. -/
theorem dirichletLaplacian_inner_truncationL2_nonneg (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (f : (dirichletLaplacian Ω).domain) :
    0 ≤ ⟪dirichletLaplacian Ω f, truncationL2 Ω hG hK f⟫_ℝ := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  obtain ⟨w, hw, hwv, hwd⟩ := truncation_comp_mem_sobolevZero hG hK hv
  have hfv : (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn v :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ)) hvf.symm)
  have he : truncationL2 Ω hG hK f = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume w := by
    refine Lp.ext ?_
    filter_upwards [coeFn_truncationL2 hG hK f, hwv, hfv] with x hx1 hx2 hx3
    rw [hx1, fnL_apply, hx2, hx3]
  rw [he, dirichletLaplacian_inner_eq_dirichletForm f hv hvf hw]
  exact dirichletForm_truncation_nonneg hG hwd

/-! ### Theorem 10.3 -/

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- `φ(t) = Φ(u(t))` is continuous on `[0, ∞)`. -/
theorem continuousOn_truncationFunctional (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) : ContinuousOn (fun t ↦ truncationFunctional Ω G K (u t)) (Ici 0) :=
  (continuous_truncationFunctional hG hK).comp_continuousOn h.continuousOn

/-- **The derivative of `φ(t) = Φ(u(t))`** ([brezis2011functional], proof of Theorem 10.3, (18)):
for `t > 0`, `φ'(t) = ⟪G(u(t) − K), u'(t)⟫`. From the key estimate
`|Φ(u(t')) − Φ(u(t)) − ⟪G(u(t) − K), u(t') − u(t)⟫| ≤ ‖u(t') − u(t)‖² = o(t' − t)` and the
differentiability of `t' ↦ ⟪G(u(t) − K), u(t')⟫`. -/
theorem hasDerivAt_truncationFunctional (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ truncationFunctional Ω G K (u t))
      ⟪truncationL2 Ω hG hK (u t), deriv u t⟫_ℝ t := by
  set g := truncationL2 Ω hG hK (u t) with hg
  rw [hasDerivAt_iff_isLittleO]
  -- the quadratic remainder
  have hA : (fun t' ↦ truncationFunctional Ω G K (u t') - truncationFunctional Ω G K (u t)
      - ⟪g, u t' - u t⟫_ℝ) =o[𝓝 t] fun t' ↦ t' - t := by
    have hO : (fun t' ↦ u t' - u t) =O[𝓝 t] fun t' ↦ t' - t := (h.hasDerivAt ht).isBigO_sub
    have h0 : (fun t' ↦ ‖u t' - u t‖) =o[𝓝 t] fun _ ↦ (1 : ℝ) := by
      rw [Asymptotics.isLittleO_one_iff]
      exact tendsto_iff_norm_sub_tendsto_zero.1 (h.hasDerivAt ht).continuousAt.tendsto
    have hsq : (fun t' ↦ ‖u t' - u t‖ * ‖u t' - u t‖) =o[𝓝 t] fun t' ↦ (t' - t) * 1 :=
      hO.norm_left.mul_isLittleO h0
    refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t' ↦ ?_)).trans_isLittleO
      (hsq.congr_right fun t' ↦ mul_one _)
    rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (mul_self_nonneg _), ← sq]
    have := abs_truncationFunctional_sub_sub_inner_le hG hK (u t) (u t' - u t)
    rwa [add_sub_cancel] at this
  -- the linear part
  have hB : (fun t' ↦ ⟪g, u t' - u t⟫_ℝ - (t' - t) • ⟪g, deriv u t⟫_ℝ) =o[𝓝 t]
      fun t' ↦ t' - t := by
    have hd : HasDerivAt (fun t' ↦ ⟪g, u t'⟫_ℝ) ⟪g, deriv u t⟫_ℝ t := by
      have := (hasDerivAt_const t g).inner ℝ (h.hasDerivAt ht)
      rw [inner_zero_left, add_zero, ← h.deriv_eq ht] at this
      exact this
    refine (hasDerivAt_iff_isLittleO.1 hd).congr_left fun t' ↦ ?_
    rw [inner_sub_right]
  refine (hA.add hB).congr_left fun t' ↦ ?_
  ring

/-- **`φ' ≤ 0` on `(0, ∞)`**: `φ'(t) = ⟪G(u(t) − K), u'(t)⟫ = −⟪A u(t), G(u(t) − K)⟫ ≤ 0`. -/
theorem inner_truncationL2_deriv_nonpos (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) {t : ℝ} (ht : 0 < t) :
    ⟪truncationL2 Ω hG hK (u t), deriv u t⟫_ℝ ≤ 0 := by
  rw [h.deriv_eq ht, inner_neg_right, real_inner_comm, neg_nonpos]
  exact dirichletLaplacian_inner_truncationL2_nonneg hG hK ⟨u t, h.mem_domain ht⟩

/-- **`φ(t) = Φ(u(t))` is nonincreasing on `[0, ∞)`.** -/
theorem antitoneOn_truncationFunctional (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) : AntitoneOn (fun t ↦ truncationFunctional Ω G K (u t)) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (h.continuousOn_truncationFunctional hG hK)
    ?_ ?_
  · rw [interior_Ici]
    intro t ht
    exact (h.hasDerivAt_truncationFunctional hG hK ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(h.hasDerivAt_truncationFunctional hG hK ht).deriv]
    exact h.inner_truncationL2_deriv_nonpos hG hK ht

/-- **Theorem 10.3, the upper bound** ([brezis2011functional]): for `K ≥ 0` with `u₀ ≤ K`
almost everywhere on `Ω`, `u(t) ≤ K` almost everywhere on `Ω` for every `t ≥ 0`. Stampacchia's
truncation in time: `φ(t) = ∫_Ω H(u(t) − K)` is continuous on `[0, ∞)`, `φ(0) = 0`, `φ ≥ 0`, and
nonincreasing, so `φ ≡ 0` and `H(u(t) − K) = 0` a.e. The book's `K = max{0, sup u₀}` is the least
admissible `K`. Any open `Ω`. -/
theorem le_of_le (h : IsSolution Ω u₀ u) {K : ℝ} (hK : 0 ≤ K)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), u₀ x ≤ K) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), u t x ≤ K := by
  obtain ⟨G, hG⟩ := exists_isTruncation
  have h0 : truncationFunctional Ω G K (u 0) = 0 := by
    rw [h.apply_zero]
    exact truncationFunctional_eq_zero_of_ae_le hG hu₀
  have hle : truncationFunctional Ω G K (u t) ≤ truncationFunctional Ω G K (u 0) :=
    h.antitoneOn_truncationFunctional hG hK self_mem_Ici ht ht
  rw [h0] at hle
  exact ae_le_of_truncationFunctional_eq_zero hG hK
    (le_antisymm hle (truncationFunctional_nonneg hG K _))

/-- `−u` is a solution with datum `−u₀`. -/
theorem neg (h : IsSolution Ω u₀ u) : IsSolution Ω (-u₀) (-u) where
  toIsSolutionOn :=
    { apply_zero := by rw [Pi.neg_apply, h.apply_zero]
      mem_domain := fun t ht ↦ neg_mem (h.mem_domain ht)
      hasDerivWithinAt := fun t ht ↦ by
        have h1 := (h.hasDerivAt ht).neg.hasDerivWithinAt (s := Ioi 0)
        refine h1.congr_deriv ?_
        have e : (⟨(-u) t, neg_mem (h.mem_domain ht)⟩ : (dirichletLaplacian Ω).domain)
            = -⟨u t, h.mem_domain ht⟩ := Subtype.ext rfl
        rw [neg_neg, e, LinearPMap.map_neg, neg_neg] }
  continuousOn := h.continuousOn.neg
  contDiffOn := h.contDiffOn.neg

/-- **Theorem 10.3, the lower bound** ([brezis2011functional]): for `K ≥ 0` with `−K ≤ u₀`
almost everywhere, `−K ≤ u(t)` almost everywhere for every `t ≥ 0` (`le_of_le` for `−u`). -/
theorem ge_of_ge (h : IsSolution Ω u₀ u) {K : ℝ} (hK : 0 ≤ K)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), -K ≤ u₀ x) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), -K ≤ u t x := by
  have h1 := h.neg.le_of_le hK (K := K) ?_ ht
  · filter_upwards [h1, Lp.coeFn_neg (u t)] with x hx hx'
    rw [Pi.neg_apply, hx', Pi.neg_apply] at hx
    linarith
  · filter_upwards [hu₀, Lp.coeFn_neg u₀] with x hx hx'
    rw [hx', Pi.neg_apply]
    linarith

/-- **Corollary 10.4 (i)** ([brezis2011functional]): `0 ≤ u₀` a.e. on `Ω` implies `0 ≤ u(t)`
a.e. on `Ω` for every `t ≥ 0`. -/
theorem nonneg (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ u₀ x) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ u t x := by
  have := h.ge_of_ge le_rfl (K := 0) (by simpa using hu₀) ht
  simpa using this

/-- **Corollary 10.4 (ii)** ([brezis2011functional]): `‖u(t)‖_{L^∞(Ω)} ≤ ‖u₀‖_{L^∞(Ω)}` for
every `t ≥ 0` — both bounds of Theorem 10.3 with `K = ‖u₀‖_∞` (trivial when `u₀ ∉ L^∞`). The
book's `‖u‖_{L^∞(Q)}` is this bound for every `t`. -/
theorem eLpNorm_top_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (u t) ∞ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ eLpNorm u₀ ∞ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _),
    eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  rcases eq_or_ne (eLpNormEssSup u₀ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ⊤
    with htop | hne
  · rw [htop]
    exact le_top
  set K := (eLpNormEssSup u₀ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
    with hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hb : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |u₀ x| ≤ K := by
    filter_upwards [ae_le_eLpNormEssSup (f := u₀)
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx
    rw [Real.enorm_eq_ofReal_abs] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hx
  have h1 := h.le_of_le hK0 (hb.mono fun x hx ↦ (le_abs_self _).trans hx) ht
  have h2 := h.ge_of_ge hK0 (hb.mono fun x hx ↦ (abs_le.1 hx).1) ht
  calc eLpNormEssSup (u t) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ENNReal.ofReal K := by
        refine eLpNormEssSup_le_of_ae_bound ?_
        filter_upwards [h1, h2] with x hx1 hx2
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨hx2, hx1⟩
    _ = eLpNormEssSup u₀ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
        ENNReal.ofReal_toReal hne

end IsSolution

end Heat
