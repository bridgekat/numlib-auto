import Mathlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Ring.Inverse

/-!
# Atkinson–Han §2.9: the resolvent operator

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.9: the resolvent set, the spectrum, the
perturbation bound (2.9.2) and the Neumann expansion (2.9.3) of the resolvent about a point of the
resolvent set.

Definition 2.9.1 is Mathlib's `resolventSet`, `spectrum` and `resolvent`, and is not restated: the
book's `R(λ) = (λ I - L)⁻¹` is `resolvent L λ`, defined as `Ring.inverse (algebraMap 𝕜 _ λ - L)` in
the Banach algebra `𝓛(V) = V →L[𝕜] V`. What the surface adds to the qualitative
`spectrum.isOpen_resolventSet` is the *quantitative* content the book uses: the radius
`1 / ‖R(λ₀)‖` of the disc that stays inside the resolvent set, the bound (2.9.2) on
`‖R(λ) - R(λ₀)‖`, and the power series (2.9.3). All three come from the backbone perturbation
theorems of `Numlib/Analysis/Normed/Ring/Inverse`, which is how the book derives them from its
Theorem 2.3.5.

## Main results

* `lemma_2_9_2` — the resolvent set is open, the spectrum is closed, and (2.9.1)–(2.9.2).
* `equation_2_9_3` — the Neumann series `R(λ) = ∑ₖ (-1)^k (λ - λ₀)^k R(λ₀)^{k+1}`.
* `spectrum_subset_closedBall` — the spectrum lies in the closed ball of radius `‖L‖`.

The analyticity of `λ ↦ R(λ)` that the book reads off (2.9.3) is Mathlib's
`spectrum.hasDerivAt_resolvent_const_left`; `equation_2_9_3` records that the series above is its
Taylor expansion at `λ₀`.

## Conventions

`lemma_2_9_2` and `spectrum_subset_closedBall` carry `[Nontrivial V]`, which the book assumes
silently: on the zero space `𝓛(V)` is the zero ring, `‖1‖ = 0`, and the radius `1 / ‖R(λ₀)‖` is
meaningless. `equation_2_9_3` needs no such hypothesis.

## Not formalized here

* §2.9's classification of the spectrum into point, continuous and residual parts — a definition
  with no theorem attached in the book.
* Theorems 2.9.3 and 2.9.4, the multiplicativity of the holomorphic functional calculus and the
  Riesz spectral projection `E(λ₀, L) = (2πi)⁻¹ ∮ (λ - L)⁻¹ dλ`. Both are stated in the book
  without proof, both need contour integrals of operator-valued functions, and Theorem 2.9.4 needs
  the Riesz ascent–descent theory as well.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

namespace AtkinsonHan.Chapter02

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  [Nontrivial V]

/-- **Lemma 2.9.2** with **(2.9.1)** and **(2.9.2)**. The resolvent set of a bounded operator is
open and the spectrum is closed; moreover, if `λ₀ ∈ ρ(L)` and `|λ - λ₀| ‖R(λ₀)‖ < 1` then
`λ ∈ ρ(L)` and `‖R(λ) - R(λ₀)‖ ≤ ‖R(λ₀)‖² |λ - λ₀| / (1 - ‖R(λ₀)‖ |λ - λ₀|)`. -/
theorem lemma_2_9_2 (L : V →L[𝕜] V) :
    IsOpen (resolventSet 𝕜 L) ∧ IsClosed (spectrum 𝕜 L) ∧
      ∀ lam₀ ∈ resolventSet 𝕜 L, ∀ lam : 𝕜,
        ‖resolvent L lam₀‖ * ‖lam - lam₀‖ < 1 →
          lam ∈ resolventSet 𝕜 L ∧
            ‖resolvent L lam - resolvent L lam₀‖ ≤
              ‖resolvent L lam₀‖ ^ 2 * ‖lam - lam₀‖ /
                (1 - ‖resolvent L lam₀‖ * ‖lam - lam₀‖) := by
  refine ⟨spectrum.isOpen_resolventSet L, spectrum.isClosed L, fun lam₀ h₀ lam hlt => ?_⟩
  obtain ⟨x, hxval⟩ := spectrum.mem_resolventSet_iff.mp h₀
  have hxinv : resolvent L lam₀ = ((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V) := by
    rw [show resolvent L lam₀ = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam₀ - L) from rfl,
      ← hxval, Ring.inverse_unit]
  have htnorm : ‖algebraMap 𝕜 (V →L[𝕜] V) (lam - lam₀)‖ = ‖lam - lam₀‖ :=
    norm_algebraMap' (V →L[𝕜] V) _
  have hpos : 0 < ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖ := Units.norm_pos x⁻¹
  rw [hxinv] at hlt ⊢
  have hlt' : ‖algebraMap 𝕜 (V →L[𝕜] V) (lam - lam₀)‖ <
      ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖⁻¹ := by
    rw [htnorm]
    refine lt_of_not_ge fun hc => absurd hlt (not_lt.mpr ?_)
    calc (1 : ℝ) = ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖⁻¹ *
            ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖ := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖ * ‖lam - lam₀‖ := by rw [mul_comm]; gcongr
  have hsum : (x : V →L[𝕜] V) + algebraMap 𝕜 (V →L[𝕜] V) (lam - lam₀)
      = algebraMap 𝕜 (V →L[𝕜] V) lam - L := by
    rw [hxval, map_sub]
    abel
  have hunit : IsUnit (algebraMap 𝕜 (V →L[𝕜] V) lam - L) := by
    rw [← hsum]
    exact Units.isUnit_add_of_norm_lt x _ hlt'
  refine ⟨spectrum.mem_resolventSet_iff.mpr hunit, ?_⟩
  have hbound := Units.norm_inverse_add_sub_le x _ hlt'
  rw [hsum, htnorm] at hbound
  exact hbound

omit [Nontrivial V] in
/-- **(2.9.3).** For `|λ - λ₀| ‖R(λ₀)‖ < 1` the resolvent is the convergent power series
`R(λ) = ∑_{k ≥ 0} (-1)^k (λ - λ₀)^k R(λ₀)^{k+1}`, which is its Taylor expansion at `λ₀`. -/
theorem equation_2_9_3 (L : V →L[𝕜] V) {lam₀ : 𝕜} (h₀ : lam₀ ∈ resolventSet 𝕜 L) (lam : 𝕜)
    (hlt : ‖resolvent L lam₀‖ * ‖lam - lam₀‖ < 1) :
    HasSum (fun k : ℕ =>
        ((-1 : 𝕜) ^ k * (lam - lam₀) ^ k) • resolvent L lam₀ ^ (k + 1)) (resolvent L lam) := by
  set S := resolvent L lam₀ with hS
  set T := -((lam - lam₀) • S) with hT
  have hTnorm : ‖T‖ < 1 := by
    rw [hT, norm_neg, norm_smul]
    calc ‖lam - lam₀‖ * ‖S‖ = ‖S‖ * ‖lam - lam₀‖ := mul_comm _ _
      _ < 1 := hlt
  have hxS : (algebraMap 𝕜 (V →L[𝕜] V) lam₀ - L) * S = 1 :=
    Ring.mul_inverse_cancel _ (spectrum.mem_resolventSet_iff.mp h₀)
  have hfac : algebraMap 𝕜 (V →L[𝕜] V) lam - L = (algebraMap 𝕜 (V →L[𝕜] V) lam₀ - L) * (1 - T) := by
    rw [hT, sub_neg_eq_add, mul_add, mul_one, mul_smul_comm, hxS, ← Algebra.algebraMap_eq_smul_one,
      map_sub]
    abel
  have hone : IsUnit (1 - T) := isUnit_one_sub_of_norm_lt_one hTnorm
  -- The resolvent at `lam` factors as `(1 - T)⁻¹ R(λ₀)`.
  have hres : resolvent L lam = Ring.inverse (1 - T) * S := by
    have hz : IsUnit (algebraMap 𝕜 (V →L[𝕜] V) lam - L) := by
      rw [hfac]
      exact (spectrum.mem_resolventSet_iff.mp h₀).mul hone
    have hzy : (algebraMap 𝕜 (V →L[𝕜] V) lam - L) * (Ring.inverse (1 - T) * S) = 1 := by
      rw [hfac, mul_assoc, ← mul_assoc (1 - T), Ring.mul_inverse_cancel _ hone, one_mul, hxS]
    calc resolvent L lam
        = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam - L) * 1 := by rw [mul_one]; rfl
      _ = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam - L) *
            ((algebraMap 𝕜 (V →L[𝕜] V) lam - L) * (Ring.inverse (1 - T) * S)) := by rw [hzy]
      _ = Ring.inverse (1 - T) * S := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hz, one_mul]
  rw [hres]
  have heq : (fun k : ℕ => ((-1 : 𝕜) ^ k * (lam - lam₀) ^ k) • S ^ (k + 1))
      = fun k : ℕ => T ^ k * S := by
    funext k
    calc ((-1 : 𝕜) ^ k * (lam - lam₀) ^ k) • S ^ (k + 1)
        = ((-1 : 𝕜) * (lam - lam₀)) ^ k • (S ^ k * S) := by rw [mul_pow, pow_succ]
      _ = ((-(lam - lam₀)) ^ k • S ^ k) * S := by rw [neg_one_mul, ← smul_mul_assoc]
      _ = T ^ k * S := by rw [hT, ← neg_smul, smul_pow]
  rw [heq]
  exact (hasSum_geom_series_inverse T hTnorm).mul_right S

/-- The remark before Definition 2.9.1: every `λ` with `‖L‖ < |λ|` lies in the resolvent set, so
the spectrum is contained in the closed ball of radius `‖L‖`. This is why the resolvent is defined
near infinity, which §2.9 and Chapter 6 both use. -/
theorem spectrum_subset_closedBall (L : V →L[𝕜] V) :
    {lam : 𝕜 | ‖L‖ < ‖lam‖} ⊆ resolventSet 𝕜 L ∧
      spectrum 𝕜 L ⊆ Metric.closedBall (0 : 𝕜) ‖L‖ :=
  ⟨fun _ h => spectrum.mem_resolventSet_of_norm_lt h, spectrum.subset_closedBall_norm L⟩

end AtkinsonHan.Chapter02
