import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.Normed.Ring.Inverse

/-!
# Stationary (affine) iterations

`Stationary.step G f x = G x + f`. Convergence for all data iff the spectral radius satisfies
`ρ(G) < 1` (Saad[^saad-iterative] Thm 4.1, in a complex Banach space for `⇒` and in finite
dimension for `⇐`; Kress[^kress] Thm 4.1), the contraction case `‖G‖ < 1` with a priori /
a posteriori bounds (Kress Thm 3.48, Atkinson–Han[^atkinson-han] §5.2.2), and the error
propagation `x_k - x* = G^k (x₀ - x*)`.

The spectral radius is also the *sharp* asymptotic convergence factor: no starting vector decays
faster than `ρ(G)` in the sense of the limsup of `(‖G^k d₀‖/‖d₀‖)^{1/k}`
(`Stationary.limsup_norm_pow_apply_rpow_le_spectralRadius`), and in finite dimension an
eigenvector of a dominant eigenvalue attains it
(`Stationary.exists_limsup_norm_pow_apply_rpow_eq_spectralRadius`).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Filter Topology

namespace Stationary

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- One affine step `x ↦ G x + f`. -/
def step (G : E →L[𝕜] E) (f : E) (x : E) : E := G x + f

/-- Submultiplicativity of the operator norm, including the exponent `0`, where `NormOneClass`
is unavailable because `E` may be trivial. -/
private theorem norm_pow_le_pow_norm (G : E →L[𝕜] E) (k : ℕ) : ‖G ^ k‖ ≤ ‖G‖ ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

variable (G : E →L[𝕜] E) (f : E)

/-- Error propagation: the error after `k` steps is `G^k` applied to the initial error, for any
fixed point `x'` of the step.  Every convergence statement below is read off this identity. -/
theorem step_iterate_sub {x' : E} (hfix : G x' + f = x') (x₀ : E) (k : ℕ) :
    (step G f)^[k] x₀ - x' = (G ^ k) (x₀ - x') := by
  have hf : f - x' = -G x' := by rw [eq_sub_of_add_eq' hfix]; abel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_apply_eq_comp, ← ih, step, map_sub,
      add_sub_assoc, hf, ← sub_eq_add_neg]

/-- Fixed points of the step are solutions of `(1 - G) x = f`. -/
theorem step_fixed_iff (x : E) : step G f x = x ↔ (1 - G) x = f := by
  rw [step, sub_apply, one_apply_eq_self, sub_eq_iff_eq_add, eq_comm, add_comm f]

/-- Contraction case `‖G‖ < 1`: the affine step is a contraction with constant `‖G‖`
(Kress, *Numerical Analysis*, Thm 3.48; Atkinson–Han, *Theoretical Numerical Analysis*,
§5.2.2). -/
theorem contractingWith (hG : ‖G‖ < 1) :
    ContractingWith ⟨‖G‖, norm_nonneg _⟩ (step G f) := by
  refine ⟨by exact_mod_cast hG, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [step, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub]
  exact G.le_opNorm _

/-- The distance to a fixed point is controlled by a single step; the estimate behind both the
a priori and the a posteriori bound. -/
private theorem norm_sub_fixed_le (hG : ‖G‖ < 1) {x' : E} (hfix : G x' + f = x') (x₀ : E) :
    ‖x₀ - x'‖ ≤ ‖step G f x₀ - x₀‖ / (1 - ‖G‖) := by
  have h1 : step G f x₀ - x' = G (x₀ - x') := by
    simpa using step_iterate_sub G f hfix x₀ 1
  have h2 : ‖x₀ - x'‖ ≤ ‖step G f x₀ - x₀‖ + ‖G‖ * ‖x₀ - x'‖ :=
    calc ‖x₀ - x'‖ = ‖x₀ - step G f x₀ + (step G f x₀ - x')‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x₀ - step G f x₀‖ + ‖step G f x₀ - x'‖ := norm_add_le _ _
      _ ≤ ‖step G f x₀ - x₀‖ + ‖G‖ * ‖x₀ - x'‖ := by
          rw [norm_sub_rev, h1]; gcongr; exact G.le_opNorm _
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- A priori bound `‖x_k - x*‖ ≤ ‖G‖^k / (1 - ‖G‖) ‖x₁ - x₀‖` for `‖G‖ < 1`. -/
theorem norm_iterate_sub_le [CompleteSpace E] (hG : ‖G‖ < 1) {x' : E} (hfix : G x' + f = x')
    (x₀ : E) (k : ℕ) :
    ‖(step G f)^[k] x₀ - x'‖ ≤ ‖G‖ ^ k / (1 - ‖G‖) * ‖step G f x₀ - x₀‖ := by
  rw [step_iterate_sub G f hfix]
  calc ‖(G ^ k) (x₀ - x')‖ ≤ ‖G ^ k‖ * ‖x₀ - x'‖ := (G ^ k).le_opNorm _
    _ ≤ ‖G‖ ^ k * (‖step G f x₀ - x₀‖ / (1 - ‖G‖)) := by
        gcongr
        · exact norm_pow_le_pow_norm G k
        · exact norm_sub_fixed_le G f hG hfix x₀
    _ = ‖G‖ ^ k / (1 - ‖G‖) * ‖step G f x₀ - x₀‖ := by ring

/-- A posteriori bound `‖x_k - x*‖ ≤ ‖G‖ / (1 - ‖G‖) ‖x_k - x_{k-1}‖`. -/
theorem norm_iterate_sub_le' [CompleteSpace E] (hG : ‖G‖ < 1) {x' : E} (hfix : G x' + f = x')
    (x₀ : E) (k : ℕ) :
    ‖(step G f)^[k + 1] x₀ - x'‖ ≤
      ‖G‖ / (1 - ‖G‖) * ‖(step G f)^[k + 1] x₀ - (step G f)^[k] x₀‖ := by
  set y := (step G f)^[k] x₀ with hy
  rw [Function.iterate_succ_apply']
  have h1 : step G f y - x' = G (y - x') := by simpa using step_iterate_sub G f hfix y 1
  calc ‖step G f y - x'‖ = ‖G (y - x')‖ := by rw [h1]
    _ ≤ ‖G‖ * ‖y - x'‖ := G.le_opNorm _
    _ ≤ ‖G‖ * (‖step G f y - y‖ / (1 - ‖G‖)) := by
        gcongr
        exact norm_sub_fixed_le G f hG hfix y
    _ = ‖G‖ / (1 - ‖G‖) * ‖step G f y - y‖ := by ring

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On a trivial space every continuous linear operator is `0 = 1`. -/
private theorem subsingleton_clm [Subsingleton F] : Subsingleton (F →L[ℂ] F) :=
  ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩

/-- Neumann: a spectral radius `ρ(G) < 1` makes `1 - G` invertible, so the affine iteration has
the unique fixed point `(1 - G)⁻¹ f`.  The Banach-algebra form
`_root_.isUnit_one_sub_of_spectralRadius_lt_one` assumes `NormOneClass`, which `F →L[ℂ] F`
satisfies only for nontrivial `F`; on a trivial `F` every operator is a unit anyway. -/
theorem isUnit_one_sub_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F)
    (hG : spectralRadius ℂ G < 1) : IsUnit (1 - G) := by
  rcases subsingleton_or_nontrivial F with _ | _
  · have := subsingleton_clm (F := F)
    exact isUnit_of_subsingleton _
  · exact _root_.isUnit_one_sub_of_spectralRadius_lt_one hG

/-- Saad, *Iterative Methods*, Thm 4.1 (⇒), in any complex Banach space: a spectral radius
`ρ(G) < 1` gives convergence for every `f, x₀` to the unique fixed point `(1 - G)⁻¹ f`. -/
theorem tendsto_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F)
    (hG : spectralRadius ℂ G < 1) (f x₀ : F) :
    Tendsto (fun k => (step G f)^[k] x₀) atTop (𝓝 (Ring.inverse (1 - G) f)) := by
  rcases subsingleton_or_nontrivial F with _ | _
  · simp only [fun k => Subsingleton.elim ((step G f)^[k] x₀) (Ring.inverse (1 - G) f)]
    exact tendsto_const_nhds
  · have hu : IsUnit ((1 : F →L[ℂ] F) - G) := isUnit_one_sub_of_spectralRadius_lt_one G hG
    have hfix : G (Ring.inverse (1 - G) f) + f = Ring.inverse (1 - G) f := by
      refine (step_fixed_iff G f _).mpr ?_
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hu, one_apply_eq_self]
    have hpow : Tendsto (fun k => (G : F →L[ℂ] F) ^ k) atTop (𝓝 0) :=
      (spectralRadius_lt_one_iff_tendsto_pow G).mp hG
    rw [← tendsto_sub_nhds_zero_iff]
    simp only [step_iterate_sub G f hfix]
    refine squeeze_zero_norm (fun k => (G ^ k).le_opNorm _) ?_
    simpa using hpow.norm.mul_const ‖x₀ - Ring.inverse (1 - G) f‖

/-- Saad, *Iterative Methods*, Thm 4.1 (⇐), in finite dimension: convergence of `G^k x₀ → 0`
for all `x₀` forces the spectral radius to satisfy `ρ(G) < 1`. -/
theorem spectralRadius_lt_one_of_forall_tendsto [FiniteDimensional ℂ F] (G : F →L[ℂ] F)
    (h : ∀ x₀, Tendsto (fun k => (G ^ k) x₀) atTop (𝓝 0)) : spectralRadius ℂ G < 1 := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  rcases subsingleton_or_nontrivial F with _ | _
  · have := subsingleton_clm (F := F)
    simp [spectralRadius]
  · refine (spectralRadius_lt_one_iff_tendsto_pow G).mpr ?_
    -- In finite dimension, evaluation at a basis is a closed embedding, so pointwise
    -- convergence of `G ^ k` upgrades to convergence in the operator norm.
    set b := Module.finBasis ℂ F with hb
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : (F →L[ℂ] F) →ₗ[ℂ] (Fin (Module.finrank ℂ F) → F),
        ∀ T i, Φ T i = T (b i) :=
      ⟨{ toFun := fun T i => T (b i)
         map_add' := fun T S => by funext i; simp
         map_smul' := fun c T => by funext i; simp }, fun _ _ => rfl⟩
    have hinj : Function.Injective Φ := by
      intro T S hTS
      refine ContinuousLinearMap.coe_injective (b.ext fun i => ?_)
      have hi := congrFun hTS i
      rwa [hΦ, hΦ] at hi
    have hemb : Topology.IsEmbedding Φ :=
      (LinearMap.isClosedEmbedding_of_injective (f := Φ)
        (LinearMap.ker_eq_bot.mpr hinj)).isEmbedding
    rw [hemb.tendsto_nhds_iff, map_zero, tendsto_pi_nhds]
    intro i
    simpa [Function.comp_def, hΦ] using h (b i)

/-- Saad, *Iterative Methods*, Thm 4.1 as an equivalence in finite dimension: the iteration
converges from every `f` and `x₀` iff the spectral radius satisfies `ρ(G) < 1`. -/
theorem forall_tendsto_iff_spectralRadius_lt_one [FiniteDimensional ℂ F] (G : F →L[ℂ] F) :
    (∀ f x₀, ∃ x, Tendsto (fun k => (step G f)^[k] x₀) atTop (𝓝 x)) ↔
      spectralRadius ℂ G < 1 := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  constructor
  · intro hconv
    -- the limit of the iteration is a fixed point, so `1 - G` is onto, hence injective
    have hfixed : ∀ f : F, ∃ x, step G f x = x := by
      intro f
      obtain ⟨x, hx⟩ := hconv f 0
      have hcont : Continuous (step G f) := G.continuous.add continuous_const
      refine ⟨x, tendsto_nhds_unique ?_ (hx.comp (Filter.tendsto_add_atTop_nat 1))⟩
      simpa only [Function.iterate_succ_apply', Function.comp_def] using (hcont.tendsto x).comp hx
    have hsurj : Function.Surjective (((1 : F →L[ℂ] F) - G : F →L[ℂ] F) : F →ₗ[ℂ] F) := fun f =>
      (hfixed f).imp fun x hx => (step_fixed_iff G f x).mp hx
    have hinj : Function.Injective (((1 : F →L[ℂ] F) - G : F →L[ℂ] F) : F →ₗ[ℂ] F) :=
      LinearMap.injective_iff_surjective.mpr hsurj
    refine spectralRadius_lt_one_of_forall_tendsto G fun x₀ => ?_
    obtain ⟨x, hx⟩ := hconv 0 x₀
    have hfix0 : G (0 : F) + (0 : F) = 0 := by simp
    have hiter : ∀ k, (step G (0 : F))^[k] x₀ = (G ^ k) x₀ := fun k => by
      simpa using step_iterate_sub G (0 : F) hfix0 x₀ k
    have hcont : Continuous (step G (0 : F)) := G.continuous.add continuous_const
    have hxfix : step G (0 : F) x = x := by
      refine tendsto_nhds_unique ?_ (hx.comp (Filter.tendsto_add_atTop_nat 1))
      simpa only [Function.iterate_succ_apply', Function.comp_def] using (hcont.tendsto x).comp hx
    have hx0 : x = 0 := hinj (by simpa using (step_fixed_iff G (0 : F) x).mp hxfix)
    simpa only [hiter, hx0] using hx
  · exact fun hG f x₀ => ⟨_, tendsto_of_spectralRadius_lt_one G hG f x₀⟩

/-- Geometric convergence rate: for every `r > ρ(G)`, `‖x_k - x*‖ ≤ C r^k ‖x₀ - x*‖`. -/
theorem exists_norm_iterate_sub_le [CompleteSpace F] (G : F →L[ℂ] F) {r : NNReal}
    (hr : spectralRadius ℂ G < r) (f : F) {x' : F} (hfix : G x' + f = x') :
    ∃ C : ℝ, ∀ x₀ k, ‖(step G f)^[k] x₀ - x'‖ ≤ C * (r : ℝ) ^ k * ‖x₀ - x'‖ := by
  rcases subsingleton_or_nontrivial F with _ | _
  · exact ⟨0, fun x₀ k => by simp [Subsingleton.elim ((step G f)^[k] x₀) x']⟩
  · obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt G hr
    refine ⟨C, fun x₀ k => ?_⟩
    rw [step_iterate_sub G f hfix]
    calc ‖(G ^ k) (x₀ - x')‖ ≤ ‖G ^ k‖ * ‖x₀ - x'‖ := (G ^ k).le_opNorm _
      _ ≤ C * (r : ℝ) ^ k * ‖x₀ - x'‖ := by gcongr; exact hC k

/-- `C ^ (1/k) → 1` for a positive constant `C`, because the exponent tends to `0`.  This is what
turns the geometric bound `‖G^k‖ ≤ C r^k` into the asymptotic rate `r`. -/
private theorem tendsto_const_rpow_one_div {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ => C ^ (1 / k : ℝ)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun k : ℕ => Real.log C * (1 / k : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log C)
  have h1 := (Real.continuous_exp.tendsto 0).comp h0
  rw [Real.exp_zero] at h1
  refine h1.congr fun k => ?_
  rw [Function.comp_apply, ← Real.rpow_def_of_pos hC]

/-- **No starting vector beats the spectral radius.**  The limsup of the `k`-th root of the
relative growth `‖G^k d₀‖ / ‖d₀‖` is at most `ρ(G)`, for every `d₀`: the geometric bound
`‖G^k‖ ≤ C r^k` valid for each `r > ρ(G)` gives `(‖G^k d₀‖/‖d₀‖)^{1/k} ≤ C^{1/k} r → r`.

`Stationary.exists_limsup_norm_pow_apply_rpow_eq_spectralRadius` exhibits a `d₀` attaining the
bound, so `ρ(G)` is the sharp asymptotic convergence factor of the stationary iteration. -/
theorem limsup_norm_pow_apply_rpow_le_spectralRadius [CompleteSpace F] (G : F →L[ℂ] F) (d₀ : F) :
    limsup (fun k : ℕ => (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ)) atTop
      ≤ (spectralRadius ℂ G).toReal := by
  have hnn : ∀ k : ℕ, 0 ≤ (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ) :=
    fun k => Real.rpow_nonneg (by positivity) _
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      fun k : ℕ => (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ) :=
    ⟨0, fun a ha => by
      obtain ⟨k, hk⟩ := (Filter.eventually_map.mp ha).exists
      exact (hnn k).trans hk⟩
  have hρtop : spectralRadius ℂ G ≠ ⊤ := by
    rcases subsingleton_or_nontrivial F with hF | hF
    · have := subsingleton_clm (F := F)
      simp [spectralRadius]
    · exact ((spectrum.spectralRadius_le_nnnorm G).trans_lt ENNReal.coe_lt_top).ne
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hc0 : (0 : ℝ) < c := lt_of_le_of_lt ENNReal.toReal_nonneg hc
  obtain ⟨r, hρr, hrc⟩ : ∃ r : NNReal, spectralRadius ℂ G < r ∧ (r : ENNReal) < ENNReal.ofReal c :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp (by
      rw [← ENNReal.ofReal_toReal hρtop]
      exact (ENNReal.ofReal_lt_ofReal_iff hc0).mpr hc)
  have hrc' : (r : ℝ) < c := by
    simpa using (ENNReal.lt_ofReal_iff_toReal_lt (a := (r : ENNReal)) (by simp)).mp hrc
  obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt G hρr
  have hC1 : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbound : ∀ k : ℕ, 1 ≤ k →
      (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ) ≤ max C 1 ^ (1 / k : ℝ) * r := by
    intro k hk
    have h1 : ‖(G ^ k) d₀‖ / ‖d₀‖ ≤ max C 1 * (r : ℝ) ^ k := by
      rcases eq_or_ne d₀ 0 with rfl | hd
      · simp only [map_zero, norm_zero, zero_div]
        positivity
      · rw [div_le_iff₀ (norm_pos_iff.mpr hd)]
        calc ‖(G ^ k) d₀‖ ≤ ‖G ^ k‖ * ‖d₀‖ := (G ^ k).le_opNorm _
          _ ≤ max C 1 * (r : ℝ) ^ k * ‖d₀‖ := by
              gcongr
              exact (hC k).trans (by gcongr; exact le_max_left _ _)
    calc (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ)
        ≤ (max C 1 * (r : ℝ) ^ k) ^ (1 / k : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = max C 1 ^ (1 / k : ℝ) * ((r : ℝ) ^ k) ^ (1 / k : ℝ) :=
          Real.mul_rpow hC1.le (by positivity)
      _ = max C 1 ^ (1 / k : ℝ) * r := by
          rw [one_div, Real.pow_rpow_inv_natCast r.coe_nonneg (by omega)]
  have hlim : Tendsto (fun k : ℕ => max C 1 ^ (1 / k : ℝ) * (r : ℝ)) atTop (𝓝 ((1 : ℝ) * r)) :=
    (tendsto_const_rpow_one_div hC1).mul_const _
  refine Filter.limsup_le_of_le hcob ?_
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually_lt_const (by rw [one_mul]; exact hrc')] with k hk1 hk2
  exact (hbound k hk1).trans hk2.le

/-- **The sharp convergence factor of a stationary iteration.**  In finite dimension the bound of
`Stationary.limsup_norm_pow_apply_rpow_le_spectralRadius` is attained: an eigenvector of a
dominant eigenvalue is a starting error whose asymptotic decay rate is exactly `ρ(G)`.  Together
the two say that the spectral radius *is* the worst-case asymptotic convergence factor of the
iteration. -/
theorem exists_limsup_norm_pow_apply_rpow_eq_spectralRadius [FiniteDimensional ℂ F] [Nontrivial F]
    (G : F →L[ℂ] F) :
    ∃ d₀ : F, d₀ ≠ 0 ∧
      limsup (fun k : ℕ => (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ)) atTop
        = (spectralRadius ℂ G).toReal := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  obtain ⟨μ, hμ, hμρ⟩ := spectrum.exists_nnnorm_eq_spectralRadius G
  rw [ContinuousLinearMap.spectrum_eq] at hμ
  obtain ⟨d₀, hd, hd0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hd
  have hd' : G d₀ = μ • d₀ := hd
  refine ⟨d₀, hd0, ?_⟩
  have hpow : ∀ k : ℕ, (G ^ k) d₀ = μ ^ k • d₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ' G, mul_apply_eq_comp, ih, map_smul, hd', smul_smul, ← pow_succ]
  have hconst : ∀ᶠ k : ℕ in atTop, (‖(G ^ k) d₀‖ / ‖d₀‖) ^ (1 / k : ℝ) = ‖μ‖ := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [hpow, norm_smul, norm_pow, mul_div_assoc, div_self (norm_ne_zero_iff.mpr hd0), mul_one,
      one_div, Real.pow_rpow_inv_natCast (norm_nonneg μ) (by omega)]
  rw [Filter.limsup_congr (v := fun _ : ℕ => ‖μ‖) hconst, limsup_const, ← hμρ]
  simp

end Complex

end Stationary
