/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Numlib.Approximation.Hyperinterpolation
import Numlib.Approximation.Quadrature
import Numlib.Approximation.TrapezoidExactness

/-!
# A product quadrature rule on the unit disk

Let $\mathbb{B}_2 = \{(x, y) : x^2 + y^2 \le 1\}$ be the closed unit disk of the plane. The
Gauss–Legendre rule in the radius and the periodic trapezoidal rule in the angle give the product
rule
$$\int_{\mathbb{B}_2} f \approx \frac{2\pi}{2n + 1} \sum_{l=0}^{n} \sum_{m=0}^{2n} \omega_l r_l \,
  f(r_l \cos \theta_m, r_l \sin \theta_m), \qquad \theta_m = \frac{2\pi m}{2n + 1},$$
where $(r_l, \omega_l)$ is the $(n + 1)$-point Gauss–Legendre rule on $[0, 1]$. This is the rule
(14.3.1) of [han2009theoretical]. Its nodes lie in the open disk, its weights are positive, and it
is exact for every polynomial of total degree at most $2n$. This exactness is what
hyperinterpolation of degree $n$ needs. The source claims one degree more; see the implementation
notes.

The proof changes to polar coordinates. A monomial $x^a y^b$ becomes
$r^{a+b+1} \cos^a \theta \sin^b \theta$, and each one-dimensional rule handles one factor. The
Gauss–Legendre rule integrates $r^{a+b+1}$ on $[0, 1]$ exactly because $a + b + 1 \le 2n + 1$. The
trapezoidal rule integrates $\cos^a \theta \sin^b \theta$ on $[0, 2\pi]$ exactly because
$a + b < 2n + 1$ (`Quadrature.trapezoid_eq_integral_cos_pow_mul_sin_pow`).

## Main definitions

* `Quadrature.diskProd` and `Quadrature.unitDisk`: the closed unit disk, as a subset of `ℝ × ℝ` and
  of `Fin 2 → ℝ`.
* `Quadrature.unitIntervalMeasure`: Lebesgue measure on $(0, 1)$, the weight of the radial rule.

## Main results

* `Quadrature.setIntegral_diskProd_eq_polar`: the change of variables to polar coordinates on the
  disk.
* `Quadrature.setIntegral_diskProd_eq_chords`: the integral over the disk as an iterated integral
  over the vertical chords $|s| \le \sqrt{1 - t^2}$.
* `Quadrature.setIntegral_diskProd_rotate`: the integral over the disk is invariant under a rotation
  of the plane.
* `Quadrature.isMvWeight_unitDisk`: Lebesgue measure on the disk is a weight for multivariate
  polynomials.
* `Quadrature.node_mem_Ioo`: the nodes of a rule with positive weights that is exact to degree
  $2m - 1$ on $(0, 1)$ lie in $(0, 1)$.
* `Quadrature.exists_diskRule`: the product rule has nodes in the open disk and positive weights,
  and it is exact for the polynomials of total degree at most $2n$.

## Implementation notes

* After (14.3.1), [han2009theoretical] states that the rule is exact on $\Pi_{2n+1}^2$, the
  polynomials of total degree at most $2n + 1$. This is one degree too many, and
  `Quadrature.exists_diskRule` states exactness on $\Pi_{2n}^2$. The smallest counterexample is
  $n = 1$ and $f = x^3$: the integral is $0$, but the rule gives $\tfrac{2\pi}{3} \bigl(\sum_l
  \omega_l r_l^4\bigr) \tfrac34 \approx 0.3055$. The use of the rule in (14.3.3) of the source needs
  only exactness on $\Pi_{2n}^2$, because it applies the rule to products of two elements of
  $\Pi_n^2$.
* The chord decomposition and the rotation invariance are not used by the quadrature rule. They are
  the geometry of the disk that a computation with ridge polynomials needs.
-/

open Finset MeasureTheory OrthogonalPolynomial Polynomial Set

open scoped Real

namespace Quadrature

/-! ### The radial rule: Gauss–Legendre on $(0, 1)$ -/

/-- Lebesgue measure restricted to $(0, 1)$, the weight of the Gauss–Legendre rule on the unit
interval. -/
noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- Lebesgue measure on $(0, 1)$ is a weight in the sense of `OrthogonalPolynomial.IsWeight`: all
its moments are finite and it is not carried by a finite set. So Gauss quadrature applies to it. -/
theorem isWeight_unitIntervalMeasure : IsWeight unitIntervalMeasure :=
  isWeight_volume_restrict_Ioo zero_lt_one

/-- Let $p$ be a real polynomial with $p \ge 0$ on $(0, 1)$ and $\int_0^1 p = 0$. Then $p = 0$
almost everywhere on $(0, 1)$. -/
theorem ae_eq_zero_of_integral_eq_zero {p : ℝ[X]} (hnn : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ p.eval x)
    (h : ∫ x, p.eval x ∂unitIntervalMeasure = 0) :
    (fun x => p.eval x) =ᵐ[unitIntervalMeasure] 0 := by
  refine (integral_eq_zero_iff_of_nonneg_ae ?_
    (isWeight_unitIntervalMeasure.integrable_eval p)).1 h
  rw [unitIntervalMeasure]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx

/-- Let $\rho_0, \dots, \rho_{m-1}$ be distinct real numbers and
$\omega_0, \dots, \omega_{m-1} > 0$. Suppose that
$$\sum_l \omega_l \, p(\rho_l) = \int_0^1 p(t) \, dt$$
for every real polynomial $p$ of degree less than $2m$. Then $\rho_l \in (0, 1)$ for every $l$.

The rule applied to $t \prod_{j \neq l} (t - \rho_j)^2$ and to
$(1 - t) \prod_{j \neq l} (t - \rho_j)^2$ isolates the node $\rho_l$ and gives the signs of
$\rho_l$ and $1 - \rho_l$. -/
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

/-- The closed unit disk $\{(x, y) : x^2 + y^2 \le 1\}$ of the plane, as a subset of `ℝ × ℝ`. -/
def diskProd : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 ≤ 1}

/-- The closed unit disk $\{y : y_0^2 + y_1^2 \le 1\}$ of the plane, as a subset of `Fin 2 → ℝ`. -/
def unitDisk : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 ≤ 1}

/-- The closed unit disk of `ℝ × ℝ` is measurable. -/
theorem measurableSet_diskProd : MeasurableSet diskProd :=
  measurableSet_le (by fun_prop) measurable_const

/-- The closed unit disk of `Fin 2 → ℝ` is compact, because it is closed and contained in the unit
ball of the sup norm. -/
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

/-- Lebesgue measure on the closed unit disk is a weight for multivariate polynomials in the sense
of `Approximation.IsMvWeight`: every polynomial is square integrable, and no nonzero polynomial
vanishes almost everywhere.

The hyperinterpolation results of `Numlib.Approximation.Hyperinterpolation` then accept the disk
rule. -/
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

/-- **The integral over the unit disk in polar coordinates.** For a continuous
$G \colon \mathbb{R}^2 \to \mathbb{R}$,
$$\int_{\mathbb{B}_2} G = \int_0^1 \int_{-\pi}^{\pi} r \, G(r \cos \theta, r \sin \theta) \,
  d\theta \, dr.$$
-/
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

/-- For every $G \colon \mathbb{R}^2 \to \mathbb{R}$, the integral of $G(y_0, y_1)$ over the disk in
`Fin 2 → ℝ` equals the integral of $G$ over the disk in `ℝ × ℝ`. -/
theorem setIntegral_unitDisk_eq (G : ℝ × ℝ → ℝ) :
    ∫ y in unitDisk, G (y 0, y 1) = ∫ q in diskProd, G q := by
  have h := (MeasureTheory.volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding G diskProd
  rw [← h]
  rfl

/-! ### The chord decomposition, and rotation invariance -/

/-- For $|t| \le 1$, the chord of the closed unit disk at the abscissa $t$ is the segment
$\{s : |s| \le \sqrt{1 - t^2}\}$. -/
theorem preimage_mk_diskProd_of_abs_le {t : ℝ} (ht : |t| ≤ 1) :
    Prod.mk t ⁻¹' diskProd = Icc (-√(1 - t ^ 2)) (√(1 - t ^ 2)) := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have hnn : (0 : ℝ) ≤ √(1 - t ^ 2) := Real.sqrt_nonneg _
  have hsq : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  ext s
  simp only [Set.mem_preimage, diskProd, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro h
    have hs2 : s ^ 2 ≤ √(1 - t ^ 2) ^ 2 := by rw [hsq]; linarith
    have habs : |s| ≤ √(1 - t ^ 2) := by
      have hle := Real.sqrt_le_sqrt hs2
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hnn] at hle
    exact abs_le.1 habs
  · rintro ⟨h1, h2⟩
    nlinarith

/-- For $|t| > 1$, the closed unit disk has no point with the abscissa $t$. -/
theorem preimage_mk_diskProd_of_one_lt {t : ℝ} (ht : 1 < |t|) :
    Prod.mk t ⁻¹' diskProd = ∅ := by
  have ht2 : 1 < t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  ext s
  simp only [Set.mem_preimage, diskProd, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_le]
  nlinarith [sq_nonneg s]

/-- The closed unit disk of `ℝ × ℝ` is compact. -/
theorem isCompact_diskProd : IsCompact diskProd := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset fun q hq => ?_
  have h0 : q.1 ^ 2 ≤ 1 := le_trans (by nlinarith [sq_nonneg q.2]) hq
  have h1 : q.2 ^ 2 ≤ 1 := le_trans (by nlinarith [sq_nonneg q.1]) hq
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact ⟨abs_le_one_iff_mul_self_le_one.2 (by nlinarith),
    abs_le_one_iff_mul_self_le_one.2 (by nlinarith)⟩

/-- **The integral over the unit disk as an iterated integral over vertical chords.** For a
continuous $F \colon \mathbb{R}^2 \to \mathbb{R}$,
$$\int_{\mathbb{B}_2} F = \int_{-1}^{1} \int_{-\sqrt{1 - t^2}}^{\sqrt{1 - t^2}} F(t, s) \, ds \,
  dt.$$
This is also called the Radon, or chord, decomposition.

The proof is Fubini's theorem for the indicator function of the disk, whose section at $t$ is
the chord. -/
theorem setIntegral_diskProd_eq_chords {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    ∫ q in diskProd, F q
      = ∫ t in (-1 : ℝ)..1, ∫ s in (-√(1 - t ^ 2))..√(1 - t ^ 2), F (t, s) := by
  have hInd : Integrable (Set.indicator diskProd F) volume :=
    (hF.locallyIntegrable.integrableOn_isCompact isCompact_diskProd).integrable_indicator
      measurableSet_diskProd
  have hsection : ∀ t : ℝ, ∫ s, Set.indicator diskProd F (t, s)
      = Set.indicator (Icc (-1 : ℝ) 1)
          (fun t => ∫ s in (-√(1 - t ^ 2))..√(1 - t ^ 2), F (t, s)) t := by
    intro t
    have hfun : (fun s => Set.indicator diskProd F (t, s))
        = Set.indicator (Prod.mk t ⁻¹' diskProd) (fun s => F (t, s)) := by
      funext s
      by_cases hs : (t, s) ∈ diskProd
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show s ∈ _ from hs)]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show s ∉ _ from hs)]
    rw [hfun]
    rcases le_or_gt |t| 1 with ht | ht
    · have hmem : t ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.2 (abs_le.1 ht)
      rw [preimage_mk_diskProd_of_abs_le ht, integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
      simp only [Set.indicator_of_mem hmem]
      rw [intervalIntegral.integral_of_le (by linarith [Real.sqrt_nonneg (1 - t ^ 2)])]
    · have hmem : t ∉ Icc (-1 : ℝ) 1 := fun h => absurd (abs_le.2 (Set.mem_Icc.1 h)) (not_le.2 ht)
      rw [preimage_mk_diskProd_of_one_lt ht, Set.indicator_of_notMem hmem, Set.indicator_empty,
        MeasureTheory.integral_zero]
  rw [← integral_indicator measurableSet_diskProd, Measure.volume_eq_prod,
    MeasureTheory.integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  simp_rw [hsection]
  rw [integral_indicator measurableSet_Icc,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The integral over the unit disk is invariant under a rotation of the plane.** For a continuous
$F \colon \mathbb{R}^2 \to \mathbb{R}$ and every angle $\varphi$,
$$\int_{\mathbb{B}_2} F(x \cos \varphi - y \sin \varphi, \; x \sin \varphi + y \cos \varphi) \,
  d(x, y) = \int_{\mathbb{B}_2} F.$$

In polar coordinates a rotation is a translation of the angle. The angular integrand is
$2\pi$-periodic, so its integral over one period does not change. -/
theorem setIntegral_diskProd_rotate {F : ℝ × ℝ → ℝ} (hF : Continuous F) (φ : ℝ) :
    ∫ q in diskProd, F (q.1 * Real.cos φ - q.2 * Real.sin φ, q.1 * Real.sin φ + q.2 * Real.cos φ)
      = ∫ q in diskProd, F q := by
  have hG : Continuous fun q : ℝ × ℝ =>
      F (q.1 * Real.cos φ - q.2 * Real.sin φ, q.1 * Real.sin φ + q.2 * Real.cos φ) := by fun_prop
  rw [setIntegral_diskProd_eq_polar hG, setIntegral_diskProd_eq_polar hF]
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hIoo : ∀ g : ℝ → ℝ, ∫ θ in Ioo (-π) π, g θ = ∫ θ in (-π)..π, g θ := fun g => by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi]
  have hper : Function.Periodic (fun θ : ℝ => r * F (r * Real.cos θ, r * Real.sin θ)) (2 * π) := by
    intro θ; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hshift : ∀ θ : ℝ,
      r * F (r * Real.cos θ * Real.cos φ - r * Real.sin θ * Real.sin φ,
          r * Real.cos θ * Real.sin φ + r * Real.sin θ * Real.cos φ)
        = (fun θ : ℝ => r * F (r * Real.cos θ, r * Real.sin θ)) (θ + φ) := by
    intro θ
    have h1 : r * Real.cos (θ + φ)
        = r * Real.cos θ * Real.cos φ - r * Real.sin θ * Real.sin φ := by
      rw [Real.cos_add]; ring
    have h2 : r * Real.sin (θ + φ)
        = r * Real.cos θ * Real.sin φ + r * Real.sin θ * Real.cos φ := by
      rw [Real.sin_add]; ring
    simp only [h1, h2]
  rw [setIntegral_congr_fun measurableSet_Ioo fun θ _ => hshift θ, hIoo, hIoo,
    intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => r * F (r * Real.cos θ, r * Real.sin θ)) φ]
  have h := hper.intervalIntegral_add_eq (-π + φ) (-π)
  rw [show -π + φ + 2 * π = π + φ by ring, show -π + 2 * π = π by ring] at h
  exact h

/-! ### The product rule -/

/-- For $a, b \in \mathbb{N}$, the function $\theta \mapsto \cos^a \theta \sin^b \theta$ is
$2\pi$-periodic. -/
theorem periodic_cos_pow_mul_sin_pow (a b : ℕ) :
    Function.Periodic (fun θ : ℝ => Real.cos θ ^ a * Real.sin θ ^ b) (2 * π) := by
  intro θ
  simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- For $a, b \in \mathbb{N}$,
$$\int_{(-\pi, \pi)} \cos^a \theta \sin^b \theta \, d\theta = \int_0^{2\pi} \cos^a \theta \sin^b
  \theta \, d\theta.$$
-/
theorem integral_Ioo_cos_pow_mul_sin_pow (a b : ℕ) :
    ∫ θ in Ioo (-π) π, Real.cos θ ^ a * Real.sin θ ^ b
      = ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ ^ a * Real.sin θ ^ b := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)]
  have h := (periodic_cos_pow_mul_sin_pow a b).intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, show (0 : ℝ) + 2 * π = 2 * π by ring] at h
  exact h

/-- **The disk rule (14.3.1)** of [han2009theoretical]. For every $n \in \mathbb{N}$ there are
$\rho_0, \dots, \rho_n \in (0, 1)$ and $\omega_0, \dots, \omega_n > 0$ such that the rule with
the weights and nodes
$$\frac{2\pi}{2n + 1} \omega_l \rho_l, \qquad (\rho_l \cos \theta_m, \rho_l \sin \theta_m),
  \qquad \theta_m = \frac{2\pi m}{2n + 1},$$
for $l = 0, \dots, n$ and $m = 0, \dots, 2n$, integrates every polynomial of total degree at
most $2n$ over the closed unit disk exactly. In particular the nodes lie in the open disk and
the weights are positive.

The source states exactness for total degree $2n + 1$, which is false. A monomial $x^a y^b$ of
odd total degree $d$ has the integral $0$ over the disk. Its angular factor
$\cos^a \theta \sin^b \theta$ is a trigonometric polynomial with frequencies of the parity of
$d$ and modulus at most $d$. The $N = 2n + 1$ equally spaced angles annihilate a frequency $k$
unless $N$ divides $k$. So for $d < N$ the rule also gives $0$. For $d = N$ the two extreme
frequencies $\pm N$ remain, with the total weight $2N \operatorname{Re} c_N \neq 0$ when $a$ is
odd. The smallest case is $n = 1$, $f = x^3$, where the rule gives about $0.3055$.

The proof takes for $(\rho, \omega)$ the $(n + 1)$-point Gauss–Legendre rule on $[0, 1]$. The
exactness is `Approximation.IsExactOn` for Lebesgue measure on `Quadrature.unitDisk`, and the
angles are `Quadrature.angleNode`. -/
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
      = ∑ v ∈ p.support, p.coeff v * (z 0 ^ v 0 * z 1 ^ v 1) := by
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
      (fun y : Fin 2 → ℝ => p.coeff v * (y 0 ^ v 0 * y 1 ^ v 1))
      unitDisk volume :=
    fun v => (Continuous.locallyIntegrable (by fun_prop)).integrableOn_isCompact isCompact_unitDisk
  calc ∑ k : Fin (n + 1) × Fin (2 * n + 1),
        (2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
          * MvPolynomial.eval
              ![ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2),
                ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)] p
      = ∑ k : Fin (n + 1) × Fin (2 * n + 1), ∑ v ∈ p.support, p.coeff v
          * ((2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ v 0
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ v 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [heval, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
    _ = ∑ v ∈ p.support, ∑ k : Fin (n + 1) × Fin (2 * n + 1), p.coeff v
          * ((2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ v 0
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ v 1)) := Finset.sum_comm
    _ = ∑ v ∈ p.support, p.coeff v * ∑ k : Fin (n + 1) × Fin (2 * n + 1),
          (2 * π / (2 * (n : ℝ) + 1) * (ω k.1 * ρ k.1))
            * ((ρ k.1 * Real.cos (angleNode (2 * n + 1) k.2)) ^ v 0
              * (ρ k.1 * Real.sin (angleNode (2 * n + 1) k.2)) ^ v 1) :=
        Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ v ∈ p.support, p.coeff v * ∫ y in unitDisk, y 0 ^ v 0 * y 1 ^ v 1 :=
        Finset.sum_congr rfl fun v hv => by rw [hmono _ _ (hdeg v hv)]
    _ = ∫ y in unitDisk, MvPolynomial.eval y p := by
        simp only [heval]
        rw [MeasureTheory.integral_finsetSum _ fun v _ => hint v]
        exact Finset.sum_congr rfl fun v _ => (MeasureTheory.integral_const_mul _ _).symm

end Quadrature
