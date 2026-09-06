/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.NumericalRange`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Order.IntermediateValue

/-!
# The numerical range of a complex operator

The *numerical range* (or *field of values*) of a linear operator `T` on a complex inner product
space is the set of values of its Rayleigh quotient `⟪x, T x⟫ / ⟪x, x⟫` at the nonzero vectors.
Its basic structural property is the **Toeplitz–Hausdorff theorem**: the numerical range is a
convex subset of `ℂ`. It is stated without proof in [saad2003iterative], Proposition 1.18.

## Main results

* `LinearMap.numericalRange`: the numerical range of `T : E →ₗ[ℂ] E`.
* `LinearMap.mem_numericalRange_smul_add`: the numerical range transforms affinely,
  `N(c • T + b) = c • N(T) + b` for `c ≠ 0`, stated as an equivalence between memberships.
* `LinearMap.convex_numericalRange`: the Toeplitz–Hausdorff theorem.

## Implementation notes

The usual textbook proof reduces the problem to a `2 × 2` matrix and computes that the numerical
range of a `2 × 2` matrix is a filled ellipse. The proof here avoids that computation entirely and
needs no finite dimensionality.

After the affine normalisation `mem_numericalRange_smul_add` it is enough to show that `0` and `1`
in the numerical range force the whole real interval `[0, 1]` into it. Pick `x` and `z` with
`⟪x, T x⟫ = 0` and `⟪z, T z⟫ = ⟪z, z⟫`. Rescaling `z` by a suitable complex `ζ ≠ 0` — the *phase*
step, and the only place where the field being `ℂ` rather than `ℝ` is used — makes the cross term
`⟪x, T y⟫ + ⟪y, T x⟫` real, where `y = ζ • z`. Along the real segment `u t = (1 - t) • x + t • y`
the quadratic form `⟪u t, T (u t)⟫` is then *real* for every `t`, and equals
`(1 - t) t δ + t² ‖y‖²`; dividing by `‖u t‖²` gives a continuous real function of `t` running from
`0` to `1`, and the intermediate value theorem finishes.
-/

open scoped ComplexConjugate

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The **numerical range** (or *field of values*) of a complex linear operator: the set of values
of the Rayleigh quotient `⟪x, T x⟫ / ⟪x, x⟫` at the nonzero vectors `x`. -/
def numericalRange (T : E →ₗ[ℂ] E) : Set ℂ :=
  {z | ∃ x : E, x ≠ 0 ∧ inner ℂ x (T x) / inner ℂ x x = z}

/-- Membership in the numerical range, unfolded. -/
theorem mem_numericalRange {T : E →ₗ[ℂ] E} {z : ℂ} :
    z ∈ T.numericalRange ↔ ∃ x : E, x ≠ 0 ∧ inner ℂ x (T x) / inner ℂ x x = z := Iff.rfl

private theorem inner_self_ne_zero_of_ne_zero {x : E} (hx : x ≠ 0) : (inner ℂ x x : ℂ) ≠ 0 :=
  fun h => hx (inner_self_eq_zero.1 h)

/-- The Rayleigh quotient of `c • T + b` is `c` times that of `T`, plus `b`. -/
theorem inner_smul_add_smul_id_div (T : E →ₗ[ℂ] E) (c b : ℂ) {x : E} (hx : x ≠ 0) :
    inner ℂ x ((c • T + b • (LinearMap.id : E →ₗ[ℂ] E)) x) / inner ℂ x x
      = c * (inner ℂ x (T x) / inner ℂ x x) + b := by
  have h := inner_self_ne_zero_of_ne_zero hx
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_add_right,
    inner_smul_right]
  field_simp

/-- The numerical range transforms affinely: `c z + b` lies in the numerical range of
`c • T + b` exactly when `z` lies in that of `T`. -/
theorem mem_numericalRange_smul_add {T : E →ₗ[ℂ] E} {c : ℂ} (hc : c ≠ 0) (b z : ℂ) :
    c * z + b ∈ (c • T + b • LinearMap.id).numericalRange ↔ z ∈ T.numericalRange := by
  constructor
  · rintro ⟨x, hx, hq⟩
    rw [inner_smul_add_smul_id_div T c b hx] at hq
    exact ⟨x, hx, mul_left_cancel₀ hc (add_right_cancel hq)⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx, by rw [inner_smul_add_smul_id_div T c b hx, hq]⟩

/-- The core of the Toeplitz–Hausdorff theorem, after the phase has been fixed: if `⟪x, T x⟫ = 0`,
`⟪y, T y⟫ = ⟪y, y⟫` and the cross term `⟪x, T y⟫ + ⟪y, T x⟫` is real, then the quadratic form of
`T` is real along the whole real segment from `x` to `y`, and the intermediate value theorem puts
every `t ∈ [0, 1]` into the numerical range. -/
private theorem ofReal_mem_numericalRange_aux (T : E →ₗ[ℂ] E) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxx : (inner ℂ x (T x) : ℂ) = 0) (hyy : (inner ℂ y (T y) : ℂ) = inner ℂ y y)
    (him : ((inner ℂ x (T y) : ℂ) + inner ℂ y (T x)).im = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) ∈ T.numericalRange := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, (inner ℂ x (T y) : ℂ) + inner ℂ y (T x) = (δ : ℂ) :=
    ⟨((inner ℂ x (T y) : ℂ) + inner ℂ y (T x)).re, Complex.ext rfl (by simpa using him)⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ → E, ∀ s : ℝ, u s = ((1 - s : ℝ) : ℂ) • x + ((s : ℝ) : ℂ) • y :=
    ⟨_, fun _ => rfl⟩
  have hune : ∀ s : ℝ, u s ≠ 0 := by
    intro s hs
    rw [hu] at hs
    rcases eq_or_ne s 0 with rfl | hs0
    · exact hx (by simpa using hs)
    · have hsc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
      have h2 : ((s : ℝ) : ℂ) • y = -(((1 - s : ℝ) : ℂ) • x) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs
      have h3 : y = (-(((1 - s : ℝ) : ℂ)) / ((s : ℝ) : ℂ)) • x := by
        rw [div_eq_inv_mul, ← smul_smul, neg_smul, ← h2, smul_smul, inv_mul_cancel₀ hsc, one_smul]
      have h4 : (inner ℂ y (T y) : ℂ) = 0 := by
        rw [h3, map_smul, inner_smul_left, inner_smul_right, hxx, mul_zero, mul_zero]
      rw [hyy] at h4
      exact hy (inner_self_eq_zero.1 h4)
  have hinner : ∀ s : ℝ, (inner ℂ (u s) (u s) : ℂ) = ((‖u s‖ ^ 2 : ℝ) : ℂ) := by
    intro s; rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl
  have hnum : ∀ s : ℝ, (inner ℂ (u s) (T (u s)) : ℂ)
      = (((1 - s) * s * δ + s ^ 2 * ‖y‖ ^ 2 : ℝ) : ℂ) := by
    intro s
    have hTu : T (u s) = ((1 - s : ℝ) : ℂ) • T x + ((s : ℝ) : ℂ) • T y := by
      rw [hu]; simp
    rw [hTu, hu]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    rw [hxx, hyy, inner_self_eq_norm_sq_to_K]
    push_cast
    linear_combination ((1 - (s : ℂ)) * (s : ℂ)) * hδ
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      ∀ s : ℝ, g s = ((1 - s) * s * δ + s ^ 2 * ‖y‖ ^ 2) / ‖u s‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hquot : ∀ s : ℝ, (inner ℂ (u s) (T (u s)) : ℂ) / inner ℂ (u s) (u s) = ((g s : ℝ) : ℂ) := by
    intro s; rw [hnum, hinner, hg]; push_cast; ring
  have hucont : Continuous u := by
    have hfun : u = fun s : ℝ => ((1 - s : ℝ) : ℂ) • x + ((s : ℝ) : ℂ) • y := funext hu
    rw [hfun]
    exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul
      continuous_const).add ((Complex.continuous_ofReal.comp continuous_id).smul continuous_const)
  have hgcont : Continuous g := by
    have hfun : g = fun s : ℝ => ((1 - s) * s * δ + s ^ 2 * ‖y‖ ^ 2) / ‖u s‖ ^ 2 := funext hg
    rw [hfun]
    exact Continuous.div (by fun_prop) (hucont.norm.pow 2)
      fun s => pow_ne_zero _ (norm_ne_zero_iff.2 (hune s))
  have hg0 : g 0 = 0 := by rw [hg]; norm_num
  have hg1 : g 1 = 1 := by
    have hu1 : u 1 = y := by rw [hu]; norm_num
    have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [hg, hu1]
    field_simp
    ring
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hgcont.continuousOn
    (show t ∈ Set.Icc (g 0) (g 1) by rw [hg0, hg1]; exact ⟨ht0, ht1⟩)
  exact ⟨u s, hune s, by rw [hquot s, hs]⟩

/-- Every complex number can be rotated onto the real axis by multiplication with a nonzero
scalar. -/
private theorem exists_ne_zero_mul_im_eq_zero (d : ℂ) : ∃ ζ : ℂ, ζ ≠ 0 ∧ (ζ * d).im = 0 := by
  rcases eq_or_ne d 0 with rfl | h
  · exact ⟨1, one_ne_zero, by simp⟩
  · refine ⟨conj d, by simpa only [ne_eq, map_eq_zero] using h, ?_⟩
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- If `0` and `1` belong to the numerical range, so does every real number between them. -/
private theorem ofReal_mem_numericalRange (T : E →ₗ[ℂ] E) (h0 : (0 : ℂ) ∈ T.numericalRange)
    (h1 : (1 : ℂ) ∈ T.numericalRange) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) ∈ T.numericalRange := by
  obtain ⟨x, hx, hqx⟩ := h0
  obtain ⟨z, hz, hqz⟩ := h1
  have hxne := inner_self_ne_zero_of_ne_zero hx
  have hzne := inner_self_ne_zero_of_ne_zero hz
  have hxx : (inner ℂ x (T x) : ℂ) = 0 := by simpa using (div_eq_iff hxne).1 hqx
  have hzz : (inner ℂ z (T z) : ℂ) = inner ℂ z z := by simpa using (div_eq_iff hzne).1 hqz
  obtain ⟨ζ, hζ, hζim⟩ :=
    exists_ne_zero_mul_im_eq_zero ((inner ℂ x (T z) : ℂ) - conj (inner ℂ z (T x) : ℂ))
  refine ofReal_mem_numericalRange_aux T hx (smul_ne_zero hζ hz) hxx ?_ ?_ ht0 ht1
  · simp only [map_smul, inner_smul_left, inner_smul_right, hzz]
  · simp only [map_smul, inner_smul_left, inner_smul_right]
    rw [show (ζ * (inner ℂ x (T z) : ℂ) + conj ζ * (inner ℂ z (T x) : ℂ)).im
        = (ζ * ((inner ℂ x (T z) : ℂ) - conj (inner ℂ z (T x) : ℂ))).im by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
        Complex.conj_im]
      ring]
    exact hζim

/-- **The Toeplitz–Hausdorff theorem**: the numerical range of a linear operator on a complex
inner product space is convex. -/
theorem convex_numericalRange (T : E →ₗ[ℂ] E) : Convex ℝ T.numericalRange := by
  intro p hp q hq a b ha hb hab
  rcases eq_or_ne p q with rfl | hpq
  · have h : a • p + b • p = p := by rw [← add_smul, hab, one_smul]
    rw [h]; exact hp
  · have hqp : q - p ≠ 0 := sub_ne_zero.2 (Ne.symm hpq)
    have hc0 : (q - p)⁻¹ ≠ 0 := inv_ne_zero hqp
    have h0 : (0 : ℂ) ∈ ((q - p)⁻¹ • T + (-((q - p)⁻¹ * p)) • LinearMap.id).numericalRange := by
      have h := (mem_numericalRange_smul_add (T := T) hc0 (-((q - p)⁻¹ * p)) p).2 hp
      rwa [add_neg_cancel] at h
    have h1 : (1 : ℂ) ∈ ((q - p)⁻¹ • T + (-((q - p)⁻¹ * p)) • LinearMap.id).numericalRange := by
      have h := (mem_numericalRange_smul_add (T := T) hc0 (-((q - p)⁻¹ * p)) q).2 hq
      rwa [show (q - p)⁻¹ * q + -((q - p)⁻¹ * p) = 1 by field_simp; ring] at h
    have hb1 : b ≤ 1 := by linarith
    have hbmem := ofReal_mem_numericalRange _ h0 h1 hb hb1
    have hz : (q - p)⁻¹ * ((b : ℂ) * (q - p) + p) + -((q - p)⁻¹ * p) = (b : ℂ) := by
      field_simp
      ring
    have hmem := (mem_numericalRange_smul_add (T := T) hc0 (-((q - p)⁻¹ * p))
      ((b : ℂ) * (q - p) + p)).1 (by rw [hz]; exact hbmem)
    have heq : a • p + b • q = (b : ℂ) * (q - p) + p := by
      have ha' : a = 1 - b := by linarith
      rw [Complex.real_smul, Complex.real_smul, ha']
      push_cast
      ring
    rw [heq]
    exact hmem

/-! ### Berger's power inequality -/

section PowerInequality

/-- An operator is *accretive* when the real part of its quadratic form is everywhere
nonnegative. -/
private def Accretive (T : Module.End ℂ E) : Prop := ∀ x : E, 0 ≤ (inner ℂ x (T x) : ℂ).re

/-- The quadratic form of `1 - c • T`. -/
private theorem inner_one_sub_smul (c : ℂ) (T : Module.End ℂ E) (x : E) :
    (inner ℂ x ((1 - c • T) x) : ℂ) = (inner ℂ x x : ℂ) - c * inner ℂ x (T x) := by
  simp [inner_sub_right, inner_smul_right]

private theorem accretive_sum {ι : Type*} {s : Finset ι} {f : ι → Module.End ℂ E}
    (h : ∀ i ∈ s, Accretive (f i)) : Accretive (∑ i ∈ s, f i) := by
  intro x
  rw [LinearMap.sum_apply, inner_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun i hi => h i hi x

private theorem accretive_real_smul {r : ℝ} (hr : 0 ≤ r) {T : Module.End ℂ E} (h : Accretive T) :
    Accretive (((r : ℂ)) • T) := by
  intro x
  rw [LinearMap.smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hr (h x)

/-- An invertible accretive operator has an accretive inverse: writing `x` for `u⁻¹ y`, the two
quadratic forms `⟪y, u⁻¹ y⟫` and `⟪x, u x⟫` are complex conjugates of one another. -/
private theorem accretive_units_inv {u : (Module.End ℂ E)ˣ} (h : Accretive (u : Module.End ℂ E)) :
    Accretive (↑u⁻¹ : Module.End ℂ E) := by
  intro y
  have hy : (u : Module.End ℂ E) ((↑u⁻¹ : Module.End ℂ E) y) = y :=
    congrArg (fun f : Module.End ℂ E => f y) u.mul_inv
  have hx := h ((↑u⁻¹ : Module.End ℂ E) y)
  rw [hy, ← inner_conj_symm, Complex.conj_re] at hx
  exact hx

variable [FiniteDimensional ℂ E]

/-- On a finite-dimensional space a strictly accretive operator is invertible: its kernel is
trivial because the quadratic form vanishes there. -/
private theorem isUnit_of_re_inner_pos {T : Module.End ℂ E}
    (h : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (T x) : ℂ).re) : IsUnit T := by
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hpos := h x hx0
    rw [hx, inner_zero_right] at hpos
    simp at hpos
  exact (Module.End.isUnit_iff T).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- The heart of the power inequality. If the quadratic form of `T` is dominated by `‖x‖²` then,
for every `z` in the open unit disc, `1 - zᵏ Tᵏ` is accretive.

The `k` shifted operators `B j = 1 - ωʲ z T`, with `ω` a primitive `k`-th root of unity, are
strictly accretive, hence invertible, and each satisfies `B j * D j = 1 - zᵏ Tᵏ` for the geometric
sum `D j = ∑_{m < k} (ωʲ z T)ᵐ`. Summing the `D j` over `j` collapses to `k`, because
`∑_j ωʲᵐ` vanishes for `0 < m < k`; so `(k⁻¹ ∑_j (B j)⁻¹) (1 - zᵏ Tᵏ) = 1`. The left factor is
accretive, being an average of inverses of accretive operators, and the inverse of an accretive
operator is accretive — which, applied once more, is the claim. -/
private theorem accretive_one_sub_smul_pow (T : Module.End ℂ E)
    (hT : ∀ x : E, ‖(inner ℂ x (T x) : ℂ)‖ ≤ ‖x‖ ^ 2) {k : ℕ} (hk : 0 < k) {z : ℂ}
    (hz : ‖z‖ < 1) : Accretive (1 - (z ^ k) • T ^ k) := by
  classical
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω k :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / k), Complex.isPrimitiveRoot_exp k hk.ne'⟩
  have hωk : ω ^ k = 1 := hω.pow_eq_one
  have hωnorm : ‖ω‖ = 1 := by
    have hpow : ‖ω‖ ^ k = 1 := by rw [← norm_pow, hωk, norm_one]
    rcases lt_trichotomy ‖ω‖ 1 with h | h | h
    · have := pow_lt_one₀ (norm_nonneg ω) h hk.ne'
      linarith
    · exact h
    · have := one_lt_pow₀ h hk.ne'
      linarith
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Module.End ℂ E, ∀ j, B j = 1 - (ω ^ j * z) • T := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Module.End ℂ E,
      ∀ j, D j = ∑ m ∈ Finset.range k, ((ω ^ j * z) • T) ^ m := ⟨_, fun _ => rfl⟩
  have hnormcoef : ∀ j : ℕ, ‖ω ^ j * z‖ = ‖z‖ := by
    intro j; rw [norm_mul, norm_pow, hωnorm, one_pow, one_mul]
  have hBre : ∀ (j : ℕ) (x : E), (inner ℂ x (B j x) : ℂ).re
      = ‖x‖ ^ 2 - ((ω ^ j * z) * inner ℂ x (T x)).re := by
    intro j x
    have hre : (inner ℂ x x : ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [hB, inner_one_sub_smul, Complex.sub_re, hre]
  have hBpos : ∀ (j : ℕ) (x : E), x ≠ 0 → 0 < (inner ℂ x (B j x) : ℂ).re := by
    intro j x hx
    rw [hBre]
    have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    have h1 : ((ω ^ j * z) * inner ℂ x (T x)).re ≤ ‖z‖ * ‖x‖ ^ 2 :=
      calc ((ω ^ j * z) * inner ℂ x (T x)).re ≤ ‖(ω ^ j * z) * (inner ℂ x (T x) : ℂ)‖ :=
            Complex.re_le_norm _
        _ = ‖z‖ * ‖(inner ℂ x (T x) : ℂ)‖ := by rw [norm_mul, hnormcoef]
        _ ≤ ‖z‖ * ‖x‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_left (hT x) (norm_nonneg z)
    nlinarith
  have hBacc : ∀ j : ℕ, Accretive (B j) := by
    intro j x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (hBpos j x hx).le
  have hBunit : ∀ j : ℕ, IsUnit (B j) := fun j => isUnit_of_re_inner_pos (hBpos j)
  have hBD : ∀ j : ℕ, B j * D j = 1 - (z ^ k) • T ^ k := by
    intro j
    rw [hB, hD, mul_neg_geom_sum, smul_pow, mul_pow, ← pow_mul, mul_comm j k, pow_mul, hωk,
      one_pow, one_mul]
  have hDsum : ∑ j ∈ Finset.range k, D j = ((k : ℂ)) • (1 : Module.End ℂ E) := by
    have hcoef : ∀ m ∈ Finset.range k, (∑ j ∈ Finset.range k, (ω ^ j * z) ^ m)
        = if m = 0 then (k : ℂ) else 0 := by
      intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · simp
      · rw [show (if m = 0 then (k : ℂ) else 0) = 0 from by simp [hm0]]
        have hrw : ∀ j : ℕ, (ω ^ j * z) ^ m = z ^ m * (ω ^ m) ^ j := by
          intro j
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j m, mul_comm]
        simp only [hrw, ← Finset.mul_sum]
        have hne : ω ^ m ≠ 1 := hω.pow_ne_one_of_pos_of_lt hm0 (Finset.mem_range.1 hm)
        rw [geom_sum_eq hne, ← pow_mul, mul_comm m k, pow_mul, hωk, one_pow, sub_self, zero_div,
          mul_zero]
    calc ∑ j ∈ Finset.range k, D j
        = ∑ m ∈ Finset.range k, (∑ j ∈ Finset.range k, (ω ^ j * z) ^ m) • T ^ m := by
          simp only [hD, smul_pow]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
      _ = ∑ m ∈ Finset.range k, (if m = 0 then (k : ℂ) else 0) • T ^ m :=
          Finset.sum_congr rfl fun m hm => by rw [hcoef m hm]
      _ = ((k : ℂ)) • (1 : Module.End ℂ E) := by
          rw [Finset.sum_eq_single 0 (fun m _ hm => by simp [hm])
            (fun h => absurd (Finset.mem_range.2 hk) h)]
          simp
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ E, P = 1 - (z ^ k) • T ^ k := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Module.End ℂ E,
      S = ∑ j ∈ Finset.range k, (↑((hBunit j).unit)⁻¹ : Module.End ℂ E) := ⟨_, rfl⟩
  have hSP : S * P = ((k : ℂ)) • 1 := by
    rw [hS, Finset.sum_mul, ← hDsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hu : ((hBunit j).unit : Module.End ℂ E) = B j := (hBunit j).unit_spec
    calc (↑((hBunit j).unit)⁻¹ : Module.End ℂ E) * P
        = (↑((hBunit j).unit)⁻¹ : Module.End ℂ E) * (B j * D j) := by rw [hBD, hP]
      _ = ((↑((hBunit j).unit)⁻¹ : Module.End ℂ E)
            * ((hBunit j).unit : Module.End ℂ E)) * D j := by rw [hu, mul_assoc]
      _ = D j := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hMP : (((k : ℂ))⁻¹ • S) * P = 1 := by
    rw [smul_mul_assoc, hSP, smul_smul, inv_mul_cancel₀ hkne, one_smul]
  have hPinj : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have happ := congrArg (fun f : Module.End ℂ E => f x) hMP
    simp only [Module.End.mul_apply, Module.End.one_apply, hx, map_zero] at happ
    exact happ.symm
  have hPunit : IsUnit P :=
    (Module.End.isUnit_iff P).2 ⟨hPinj, LinearMap.injective_iff_surjective.1 hPinj⟩
  have hPspec : (hPunit.unit : Module.End ℂ E) = P := hPunit.unit_spec
  have hinvP : (↑(hPunit.unit)⁻¹ : Module.End ℂ E) = ((k : ℂ))⁻¹ • S := by
    calc (↑(hPunit.unit)⁻¹ : Module.End ℂ E)
        = ((((k : ℂ))⁻¹ • S) * P) * (↑(hPunit.unit)⁻¹ : Module.End ℂ E) := by rw [hMP, one_mul]
      _ = (((k : ℂ))⁻¹ • S)
            * ((hPunit.unit : Module.End ℂ E) * (↑(hPunit.unit)⁻¹ : Module.End ℂ E)) := by
          rw [hPspec, mul_assoc]
      _ = ((k : ℂ))⁻¹ • S := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have haccS : Accretive S := by
    rw [hS]
    exact accretive_sum fun j _ =>
      accretive_units_inv (u := (hBunit j).unit) (by rw [(hBunit j).unit_spec]; exact hBacc j)
  have haccInv : Accretive (↑(hPunit.unit)⁻¹ : Module.End ℂ E) := by
    rw [hinvP, show ((k : ℂ))⁻¹ = ((((k : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; ring]
    exact accretive_real_smul (by positivity) haccS
  have haccP : Accretive P := by
    have h := accretive_units_inv (u := (hPunit.unit)⁻¹) haccInv
    rwa [inv_inv, hPspec] at h
  rw [← hP]
  exact haccP

/-- The normalised power inequality: a quadratic form dominated by `‖x‖²` stays dominated by it
under powers. -/
private theorem norm_inner_pow_le_one {T : Module.End ℂ E}
    (hT : ∀ x : E, ‖(inner ℂ x (T x) : ℂ)‖ ≤ ‖x‖ ^ 2) {k : ℕ} (hk : 0 < k) (x : E) :
    ‖(inner ℂ x ((T ^ k) x) : ℂ)‖ ≤ ‖x‖ ^ 2 := by
  have key : ∀ ζ : ℂ, ‖ζ‖ < 1 → (ζ * inner ℂ x ((T ^ k) x)).re ≤ ‖x‖ ^ 2 := by
    intro ζ hζ
    obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq ζ hk
    have hz : ‖z‖ < 1 := by
      by_contra hcon
      have h1 : (1 : ℝ) ≤ ‖z‖ ^ k := one_le_pow₀ (not_lt.1 hcon)
      rw [← norm_pow] at h1
      linarith
    have hacc := accretive_one_sub_smul_pow T hT hk hz x
    have hre : (inner ℂ x x : ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [inner_one_sub_smul, Complex.sub_re, hre] at hacc
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (inner ℂ x ((T ^ k) x) : ℂ) := ⟨_, rfl⟩
  rw [← hc]
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [norm_zero]; positivity
  by_contra hcon0
  have hcon : ‖x‖ ^ 2 < ‖c‖ := not_le.1 hcon0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hlt : ‖x‖ ^ 2 / ‖c‖ < 1 := (div_lt_one hcpos).2 hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between hlt
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
  have hζ : ‖((t / ‖c‖ : ℝ) : ℂ) * (starRingEnd ℂ) c‖ < 1 := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_mul_cancel₀ _ hcpos.ne']
    exact ht2
  have hval := key _ hζ
  rw [← hc, mul_assoc, Complex.conj_mul'] at hval
  have hre : (((t / ‖c‖ : ℝ) : ℂ) * ((‖c‖ : ℝ) : ℂ) ^ 2).re = t * ‖c‖ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp
  rw [hre] at hval
  rw [div_lt_iff₀ hcpos] at ht1
  linarith

/-- **Berger's power inequality** for the numerical radius: if the quadratic form of `T` is
dominated by `c ‖x‖²` then the quadratic form of `Tᵏ` is dominated by `cᵏ ‖x‖²`. Equivalently, the
numerical radius is *power-bounded*, `ν(Tᵏ) ≤ ν(T)ᵏ` — an inequality that is far from obvious,
since the numerical radius is not submultiplicative.

The proof is Pearcy's: no unitary dilation is used, only an averaging of the resolvents
`(1 - ωʲ z T)⁻¹` over the `k`-th roots of unity `ωʲ`. See
`LinearMap.accretive_one_sub_smul_pow` for the construction. -/
theorem norm_inner_pow_le {T : Module.End ℂ E} {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ x : E, ‖(inner ℂ x (T x) : ℂ)‖ ≤ c * ‖x‖ ^ 2) {k : ℕ} (hk : 0 < k) (x : E) :
    ‖(inner ℂ x ((T ^ k) x) : ℂ)‖ ≤ c ^ k * ‖x‖ ^ 2 := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · have hT0 : T = 0 := by
      rw [← inner_map_self_eq_zero T]
      intro y
      rw [← inner_conj_symm]
      have h := hT y
      rw [zero_mul] at h
      simp [norm_le_zero_iff.1 h]
    rw [hT0]
    simp [zero_pow hk.ne']
  · have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcpos.ne'
    have hnorm : ∀ y : E, ‖(inner ℂ y ((((c : ℂ))⁻¹ • T) y) : ℂ)‖ ≤ ‖y‖ ^ 2 := by
      intro y
      rw [LinearMap.smul_apply, inner_smul_right, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hcpos]
      rw [inv_mul_le_iff₀ hcpos]
      exact hT y
    have h := norm_inner_pow_le_one hnorm hk x
    rw [smul_pow, LinearMap.smul_apply, inner_smul_right, norm_mul, norm_pow, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, inv_pow,
      inv_mul_le_iff₀ (by positivity)] at h
    exact h

end PowerInequality

end LinearMap
