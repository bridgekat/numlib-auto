import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Numlib.Approximation.Hyperinterpolation
import Numlib.Approximation.Quadrature
import Numlib.Approximation.TrapezoidExactness

/-!
# A product quadrature rule on the unit disk

Gauss–Legendre in the radius and the periodic trapezoidal rule in the angle give a product rule on
the closed unit disk of the plane,

`∫_{𝔹₂} f ≈ (2 π / (2 n + 1)) ∑_{l ≤ n} ∑_{m ≤ 2 n} ω_l r_l f (r_l cos θ_m, r_l sin θ_m)`,
`θ_m = 2 π m / (2 n + 1)`,

with `(r_l, ω_l)` the `(n + 1)`-point Gauss–Legendre rule on `[0, 1]`. Its nodes lie in the open
disk, its weights are positive, and it is exact on every polynomial of total degree at most `2 n` —
which is what `Approximation.IsExactOn` names, and what hyperinterpolation of degree `n` consumes.

The proof is the change of variables to polar coordinates, `setIntegral_diskProd_eq_polar`, after
which a monomial `x^a y^b` factors as `r^{a + b + 1} cos^a θ sin^b θ` and the two factors are
handled by the two one-dimensional rules: Gauss–Legendre reproduces `∫_0^1 r^{a+b+1}` because
`a + b + 1 ≤ 2 n + 1`, and the trapezoidal rule reproduces `∫_0^{2π} cos^a θ sin^b θ` because
`a + b < 2 n + 1`, by `Quadrature.trapezoid_eq_integral_cos_pow_mul_sin_pow`.

## Main definitions

* `Quadrature.diskProd` and `Quadrature.unitDisk` — the closed unit disk, as a subset of `ℝ × ℝ`
  and of `Fin 2 → ℝ`.
* `Quadrature.unitIntervalMeasure` — Lebesgue measure on `(0, 1)`, the weight of the radial rule.

## Main results

* `Quadrature.setIntegral_diskProd_eq_polar` — the polar change of variables on the disk.
* `Quadrature.isMvWeight_unitDisk` — Lebesgue measure on the disk is a polynomial weight.
* `Quadrature.node_mem_Ioo` — the nodes of a positive-weight rule exact to degree `2 m − 1` on
  `(0, 1)` lie in `(0, 1)`. This is what makes the product weights positive.
* `Quadrature.exists_diskRule` — the rule itself, with positive weights, nodes in the open disk,
  and exactness on the polynomials of total degree at most `2 n`.

## The degree of exactness

[han2009theoretical] assert after (14.3.1) that the rule is exact on `Π_{2n+1}^2`. **That is one
degree too many**, and the statement here is exactness on `Π_{2n}^2`. A monomial `x^a y^b` of odd
total degree `d` integrates to zero over the disk, and its angular factor `cos^a θ sin^b θ` is a
trigonometric polynomial carrying only the frequencies of the parity of `d` and of modulus at most
`d`; the `N = 2 n + 1` equispaced angles annihilate a frequency `k` unless `N ∣ k`, so for `d < N`
the quadrature also gives zero, but for `d = N = 2 n + 1` the two extreme frequencies `± N` survive
with total weight `2 N Re c_N ≠ 0` whenever `a` is odd. The smallest instance is `n = 1`, `f = x³`:
the integral is `0` while the rule returns `(2π/3) (∑_l ω_l r_l⁴) (3/4) ≈ 0.3055`. Nothing in the
book depends on the discarded degree: (14.3.3) needs only exactness on `Π_{2n}^2`, since it applies
the rule to products of two elements of `Π_n^2`.
-/

open Finset MeasureTheory OrthogonalPolynomial Polynomial Set

open scoped Real

namespace Quadrature

/-! ### The radial rule: Gauss–Legendre on `(0, 1)` -/

/-- Lebesgue measure on `(0, 1)`, the weight of the Gauss–Legendre rule on the unit interval. -/
noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- Lebesgue measure on `(0, 1)` has finite moments and infinite support, so Gauss quadrature
applies to it. -/
theorem isWeight_unitIntervalMeasure : IsWeight unitIntervalMeasure := by
  constructor
  · intro n
    exact ((continuous_pow n).continuousOn.integrableOn_Icc
      (a := (0 : ℝ)) (b := 1)).mono_set Set.Ioo_subset_Icc_self
  · intro s hs hzero
    rw [unitIntervalMeasure, Measure.restrict_apply hs.measurableSet.compl] at hzero
    rw [show sᶜ ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 \ s by ext x; simp [and_comm],
      measure_sdiff_null (hs.measure_zero volume), Real.volume_Ioo] at hzero
    norm_num at hzero

/-- If a polynomial is nonnegative on `(0, 1)` and its integral there vanishes, it vanishes almost
everywhere on `(0, 1)`. -/
theorem ae_eq_zero_of_integral_eq_zero {p : ℝ[X]} (hnn : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ p.eval x)
    (h : ∫ x, p.eval x ∂unitIntervalMeasure = 0) :
    (fun x => p.eval x) =ᵐ[unitIntervalMeasure] 0 := by
  refine (integral_eq_zero_iff_of_nonneg_ae ?_
    (isWeight_unitIntervalMeasure.integrable_eval p)).1 h
  rw [unitIntervalMeasure]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx

/-- The nodes of a rule with positive weights that is exact to degree `2 m − 1` for the weight on
`(0, 1)` lie in `(0, 1)`. Testing the rule against `t ∏_{j ≠ l} (t − ρ_j)²` and against
`(1 − t) ∏_{j ≠ l} (t − ρ_j)²` isolates the `l`-th node and pins its sign. -/
theorem node_mem_Ioo {m : ℕ} {ρ ω : Fin m → ℝ} (hinj : Function.Injective ρ)
    (hω : ∀ l, 0 < ω l)
    (hex : ∀ p : ℝ[X], p.degree < ((2 * m : ℕ) : WithBot ℕ) →
      ∑ l, ω l * p.eval (ρ l) = ∫ t, p.eval t ∂unitIntervalMeasure)
    (l : Fin m) : ρ l ∈ Set.Ioo (0 : ℝ) 1 := by
  classical
  set q : ℝ[X] := ∏ j ∈ Finset.univ.erase l, (X - C (ρ j)) ^ 2 with hqdef
  have hqeval : ∀ t : ℝ, q.eval t = ∏ j ∈ Finset.univ.erase l, (t - ρ j) ^ 2 := by
    intro t; simp [hqdef, eval_prod]
  have hqnn : ∀ t : ℝ, 0 ≤ q.eval t := by
    intro t; rw [hqeval]; exact Finset.prod_nonneg fun j _ => sq_nonneg _
  have hqzero : ∀ j : Fin m, j ≠ l → q.eval (ρ j) = 0 := by
    intro j hj
    rw [hqeval]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) (by ring)
  have hqpos : 0 < q.eval (ρ l) := by
    rw [hqeval]
    refine Finset.prod_pos fun j hj => ?_
    have hne : ρ l - ρ j ≠ 0 :=
      sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hinj h.symm)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hm : 0 < m := Fin.pos l
  have hqdeg : q.natDegree ≤ 2 * (m - 1) := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hcong : ∀ j ∈ Finset.univ.erase l, ((X - C (ρ j)) ^ 2 : ℝ[X]).natDegree = 2 := by
      intro j _
      simp
    rw [Finset.sum_congr rfl hcong, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    omega
  have hsum : ∀ p : ℝ[X], (∀ j : Fin m, j ≠ l → p.eval (ρ j) = 0) →
      ∑ j, ω j * p.eval (ρ j) = ω l * p.eval (ρ l) :=
    fun p hp => Finset.sum_eq_single l (fun j _ hj => by rw [hp j hj, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h)
  have hQ : ω l * q.eval (ρ l) = ∫ t, q.eval t ∂unitIntervalMeasure := by
    rw [← hsum q hqzero]
    refine hex q ?_
    have hqne : q ≠ 0 := fun h => by simp [h] at hqpos
    rw [← Polynomial.natDegree_lt_iff_degree_lt hqne]
    omega
  have hIQ : 0 < ∫ t, q.eval t ∂unitIntervalMeasure := hQ ▸ mul_pos (hω l) hqpos
  have key : ∀ g : ℝ[X], (∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < g.eval t) →
      g.natDegree ≤ 1 → 0 < g.eval (ρ l) := by
    intro g hg hgdeg
    have hgq : ∀ j : Fin m, j ≠ l → (g * q).eval (ρ j) = 0 := by
      intro j hj
      simp [hqzero j hj]
    have hgqne : g * q ≠ 0 := by
      refine mul_ne_zero (fun h => ?_) (fun h => by simp [h] at hqpos)
      have := hg (1 / 2) (by norm_num)
      simp [h] at this
    have h1 : ω l * (g.eval (ρ l) * q.eval (ρ l)) = ∫ t, (g * q).eval t ∂unitIntervalMeasure := by
      rw [show ω l * (g.eval (ρ l) * q.eval (ρ l)) = ω l * (g * q).eval (ρ l) by simp,
        ← hsum (g * q) hgq]
      refine hex _ ?_
      rw [← Polynomial.natDegree_lt_iff_degree_lt hgqne]
      have := Polynomial.natDegree_mul_le (p := g) (q := q)
      omega
    have hnn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ (g * q).eval t := by
      intro t ht
      rw [Polynomial.eval_mul]
      exact mul_nonneg (hg t ht).le (hqnn t)
    have h2 : 0 < ∫ t, (g * q).eval t ∂unitIntervalMeasure := by
      refine lt_of_le_of_ne (integral_nonneg_of_ae ?_) fun h => ?_
      · rw [unitIntervalMeasure]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx
      · have hae := ae_eq_zero_of_integral_eq_zero hnn h.symm
        have hqae : (fun x => q.eval x) =ᵐ[unitIntervalMeasure] 0 := by
          have hmem : ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ioo (0 : ℝ) 1 := by
            rw [unitIntervalMeasure]
            exact ae_restrict_mem measurableSet_Ioo
          filter_upwards [hae, hmem] with x hx hxm
          simp only [Polynomial.eval_mul, Pi.zero_apply] at hx ⊢
          exact (mul_eq_zero.1 hx).resolve_left (ne_of_gt (hg x hxm))
        rw [integral_eq_zero_of_ae hqae] at hIQ
        exact lt_irrefl 0 hIQ
    nlinarith [hω l, hqpos, h1, h2]
  constructor
  · simpa using key X (fun t ht => by simpa using ht.1) (by simp)
  · have := key (1 - X) (fun t ht => by simpa using ht.2) (by compute_degree)
    simpa using this

/-! ### The unit disk and its polar parametrization -/

/-- The closed unit disk of the plane, as a subset of `ℝ × ℝ`. -/
def diskProd : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 ≤ 1}

/-- The closed unit disk of the plane, as a subset of `Fin 2 → ℝ`. -/
def unitDisk : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 ≤ 1}

/-- The closed unit disk of `ℝ × ℝ` is measurable. -/
theorem measurableSet_diskProd : MeasurableSet diskProd :=
  measurableSet_le (by fun_prop) measurable_const

/-- The closed unit disk of `Fin 2 → ℝ` is compact: it is closed and contained in the unit ball of
the supremum norm. -/
theorem isCompact_unitDisk : IsCompact unitDisk := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (by fun_prop) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun y hy => ?_
  have h0 : y 0 ^ 2 ≤ 1 := le_trans (by nlinarith [sq_nonneg (y 1)]) hy
  have h1 : y 1 ^ 2 ≤ 1 := le_trans (by nlinarith [sq_nonneg (y 0)]) hy
  rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
  intro i
  fin_cases i <;>
    simpa [Real.dist_eq, abs_le] using abs_le.1 (abs_le_one_iff_mul_self_le_one.2 (by nlinarith))

/-- The closed unit disk of `Fin 2 → ℝ` is measurable. -/
theorem measurableSet_unitDisk : MeasurableSet unitDisk :=
  measurableSet_le (by fun_prop) measurable_const

/-- Lebesgue measure on the closed unit disk is a weight for multivariate polynomials, so that the
rule below is one the hyperinterpolation results of `Numlib.Approximation.Hyperinterpolation`
accept. -/
theorem isMvWeight_unitDisk : Approximation.IsMvWeight (volume.restrict unitDisk) := by
  refine Approximation.isMvWeight_restrict isCompact_unitDisk measurableSet_unitDisk
    isCompact_unitDisk.measure_lt_top.ne ?_
  have hopen : IsOpen {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hsub : {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 < 1} ⊆ unitDisk :=
    fun y hy => show y 0 ^ 2 + y 1 ^ 2 ≤ 1 from le_of_lt hy
  have hsubint : {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 < 1} ⊆ interior unitDisk :=
    interior_maximal hsub hopen
  exact ⟨0, hsubint (by simp)⟩

/-- **The integral over the unit disk in polar coordinates**: for a continuous integrand,
`∫_{𝔹₂} G = ∫_0^1 ∫_{-π}^{π} r G (r cos θ, r sin θ) dθ dr`. -/
theorem setIntegral_diskProd_eq_polar {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    ∫ q in diskProd, G q
      = ∫ r in Ioc (0 : ℝ) 1, ∫ θ in Ioo (-π) π, r * G (r * Real.cos θ, r * Real.sin θ) := by
  set T : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π with hT
  set F : ℝ × ℝ → ℝ := fun p => p.1 * G (p.1 * Real.cos p.2, p.1 * Real.sin p.2) with hF
  have hFcont : Continuous F := by fun_prop
  have hTmeas : MeasurableSet T := (measurableSet_Ioc).prod measurableSet_Ioo
  have hTS : T ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono Set.Ioc_subset_Ioi_self (subset_refl _)
  have key := integral_comp_polarCoord_symm (Set.indicator diskProd G)
  rw [integral_indicator measurableSet_diskProd] at key
  rw [← key]
  have heq : ∀ p ∈ polarCoord.target,
      p.1 • Set.indicator diskProd G (polarCoord.symm p) = Set.indicator T F p := by
    intro p hp
    rw [polarCoord_target, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) :=
      polarCoord_symm_apply p
    have hmem : (polarCoord.symm p ∈ diskProd) ↔ p ∈ T := by
      rw [hsymm, hT, diskProd]
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo]
      rw [show (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq p.2]]
      constructor
      · intro h
        exact ⟨⟨hp.1, by nlinarith [hp.1]⟩, hp.2⟩
      · intro h
        nlinarith [hp.1, h.1.2]
    by_cases hd : polarCoord.symm p ∈ diskProd
    · rw [Set.indicator_of_mem hd, Set.indicator_of_mem (hmem.1 hd), hF, hsymm, smul_eq_mul]
    · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem (fun h => hd (hmem.2 h)), smul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet heq,
    setIntegral_indicator hTmeas, Set.inter_eq_self_of_subset_right hTS]
  have hK : IsCompact ((Icc (0 : ℝ) 1) ×ˢ (Icc (-π) π)) := isCompact_Icc.prod isCompact_Icc
  have hsub : T ⊆ (Icc (0 : ℝ) 1) ×ˢ (Icc (-π) π) :=
    Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioo_subset_Icc_self
  have hInt : IntegrableOn F T volume :=
    (hFcont.locallyIntegrable.integrableOn_isCompact hK).mono_set hsub
  rw [Measure.volume_eq_prod] at hInt ⊢
  rw [MeasureTheory.setIntegral_prod F hInt]

/-- The unit disk of `Fin 2 → ℝ` and the unit disk of `ℝ × ℝ` carry the same integrals. -/
theorem setIntegral_unitDisk_eq (G : ℝ × ℝ → ℝ) :
    ∫ y in unitDisk, G (y 0, y 1) = ∫ q in diskProd, G q := by
  have h := (MeasureTheory.volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding G diskProd
  rw [← h]
  rfl

/-! ### The product rule -/

/-- The angular factor of a monomial is `2 π`-periodic. -/
theorem periodic_cos_pow_mul_sin_pow (a b : ℕ) :
    Function.Periodic (fun θ : ℝ => Real.cos θ ^ a * Real.sin θ ^ b) (2 * π) := by
  intro θ
  simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The angular integral over `(−π, π)` is the integral over one period from `0`. -/
theorem integral_Ioo_cos_pow_mul_sin_pow (a b : ℕ) :
    ∫ θ in Ioo (-π) π, Real.cos θ ^ a * Real.sin θ ^ b
      = ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ ^ a * Real.sin θ ^ b := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)]
  have h := (periodic_cos_pow_mul_sin_pow a b).intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, show (0 : ℝ) + 2 * π = 2 * π by ring] at h
  exact h

/-- **The disk rule (14.3.1)**: with `(ρ, ω)` the `(n + 1)`-point Gauss–Legendre rule on `[0, 1]`
and `2 n + 1` equispaced angles, the product rule has nodes in the open unit disk, positive weights,
and integrates every polynomial of total degree at most `2 n` over the closed unit disk exactly. -/
theorem exists_diskRule (n : ℕ) :
    ∃ ρ ω : Fin (n + 1) → ℝ, (∀ l, ρ l ∈ Ioo (0 : ℝ) 1) ∧ (∀ l, 0 < ω l) ∧
      Approximation.IsExactOn (volume.restrict unitDisk)
        (fun k : Fin (n + 1) × Fin (2 * n + 1) => 2 * π / (2 * n + 1) * (ω k.1 * ρ k.1))
        (fun k : Fin (n + 1) × Fin (2 * n + 1) =>
          ![ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2),
            ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)])
        (2 * n) := by
  classical
  obtain ⟨ρ, ω, hinj, hωpos, hgauss⟩ :=
    exists_gauss isWeight_unitIntervalMeasure (n + 1)
  refine ⟨ρ, ω, fun l => node_mem_Ioo hinj hωpos hgauss l, hωpos, ?_⟩
  -- the monomial case
  have hmono : ∀ a b : ℕ, a + b ≤ 2 * n →
      ∑ k : Fin (n + 1) × Fin (2 * n + 1),
          (2 * π / (2 * n + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ a
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ b)
        = ∫ y in unitDisk, y 0 ^ a * y 1 ^ b := by
    intro a b hab
    have hrad : ∑ l, ω l * ρ l ^ (a + b + 1) = ∫ r in Ioc (0 : ℝ) 1, r ^ (a + b + 1) := by
      have h := hgauss (X ^ (a + b + 1)) (by
        rw [Polynomial.degree_X_pow]
        exact_mod_cast by omega)
      simpa [unitIntervalMeasure, ← MeasureTheory.integral_Ioc_eq_integral_Ioo] using h
    have hang : (2 * π / (2 * n + 1))
        * ∑ m ∈ Finset.range (2 * n + 1),
            Real.cos (angleNode (2 * n + 1) m) ^ a * Real.sin (angleNode (2 * n + 1) m) ^ b
        = ∫ θ in Ioo (-π) π, Real.cos θ ^ a * Real.sin θ ^ b := by
      rw [integral_Ioo_cos_pow_mul_sin_pow]
      have := trapezoid_eq_integral_cos_pow_mul_sin_pow (N := 2 * n + 1) (a := a) (b := b)
        (by omega)
      simpa using this
    -- the exact integral
    have hG : Continuous (fun q : ℝ × ℝ => q.1 ^ a * q.2 ^ b) := by fun_prop
    rw [setIntegral_unitDisk_eq (fun q => q.1 ^ a * q.2 ^ b),
      setIntegral_diskProd_eq_polar hG]
    have hinner : ∀ r : ℝ, (∫ θ in Ioo (-π) π,
          r * ((r * Real.cos θ) ^ a * (r * Real.sin θ) ^ b))
        = r ^ (a + b + 1) * ∫ θ in Ioo (-π) π, Real.cos θ ^ a * Real.sin θ ^ b := by
      intro r
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
      rw [mul_pow, mul_pow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc fun r _ => hinner r,
      MeasureTheory.integral_mul_const, ← hrad, ← hang]
    rw [Fintype.sum_prod_type]
    have hstep : ∀ x : Fin (n + 1),
        ∑ y : Fin (2 * n + 1), 2 * π / (2 * (n : ℝ) + 1) * (ω x * ρ x)
            * ((ρ x * Real.cos (angleNode (2 * n + 1) y)) ^ a
              * (ρ x * Real.sin (angleNode (2 * n + 1) y)) ^ b)
          = (ω x * ρ x ^ (a + b + 1))
            * (2 * π / (2 * (n : ℝ) + 1) * ∑ m ∈ Finset.range (2 * n + 1),
                Real.cos (angleNode (2 * n + 1) m) ^ a
                  * Real.sin (angleNode (2 * n + 1) m) ^ b) := by
      intro x
      rw [Fin.sum_univ_eq_sum_range (fun m => 2 * π / (2 * (n : ℝ) + 1) * (ω x * ρ x)
        * ((ρ x * Real.cos (angleNode (2 * n + 1) m)) ^ a
          * (ρ x * Real.sin (angleNode (2 * n + 1) m)) ^ b)), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_pow, mul_pow, pow_succ, pow_add]
      ring
    rw [Finset.sum_congr rfl fun x _ => hstep x, ← Finset.sum_mul]
  -- the general case, by linearity over the monomials of `p`
  intro p hp
  have heval : ∀ z : Fin 2 → ℝ, MvPolynomial.eval z p
      = ∑ v ∈ p.support, MvPolynomial.coeff v p * (z 0 ^ v 0 * z 1 ^ v 1) := by
    intro z
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun v _ => by
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun _ => pow_zero _,
        Fin.prod_univ_two]
  have hdeg : ∀ v ∈ p.support, v 0 + v 1 ≤ 2 * n := by
    intro v hv
    have h := MvPolynomial.le_totalDegree hv
    have hs : (v.sum fun _ e => e) = v 0 + v 1 := by
      rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_two]
    omega
  have hint : ∀ v : Fin 2 →₀ ℕ, IntegrableOn
      (fun y : Fin 2 → ℝ => MvPolynomial.coeff v p * (y 0 ^ v 0 * y 1 ^ v 1))
      unitDisk volume :=
    fun v => (Continuous.locallyIntegrable (by fun_prop)).integrableOn_isCompact isCompact_unitDisk
  calc ∑ k : Fin (n + 1) × Fin (2 * n + 1),
        (2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
          * MvPolynomial.eval
              ![ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2),
                ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)] p
      = ∑ k : Fin (n + 1) × Fin (2 * n + 1), ∑ v ∈ p.support, MvPolynomial.coeff v p
          * ((2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ v 0
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ v 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [heval, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
    _ = ∑ v ∈ p.support, ∑ k : Fin (n + 1) × Fin (2 * n + 1), MvPolynomial.coeff v p
          * ((2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ v 0
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ v 1)) := Finset.sum_comm
    _ = ∑ v ∈ p.support, MvPolynomial.coeff v p * ∑ k : Fin (n + 1) × Fin (2 * n + 1),
          (2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ v 0
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ v 1) :=
        Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ v ∈ p.support, MvPolynomial.coeff v p * ∫ y in unitDisk, y 0 ^ v 0 * y 1 ^ v 1 :=
        Finset.sum_congr rfl fun v hv => by rw [hmono _ _ (hdeg v hv)]
    _ = ∫ y in unitDisk, MvPolynomial.eval y p := by
        simp only [heval]
        rw [MeasureTheory.integral_finsetSum _ fun v _ => hint v]
        exact Finset.sum_congr rfl fun v _ => (MeasureTheory.integral_const_mul _ _).symm

end Quadrature
