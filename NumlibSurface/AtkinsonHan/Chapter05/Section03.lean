import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Convex.Gateaux
import Numlib.IntegralEquations.Basic

/-!
# Atkinson–Han §5.3: differential calculus for nonlinear operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.3.

The book's Fréchet derivative (Definition 5.3.1) is Mathlib's `HasFDerivAt`; its "interior point"
convention `B(u₀, r) ⊆ K` is `K ∈ 𝓝 u₀`, under which `HasFDerivWithinAt` and `HasFDerivAt`
agree.  The book's Gâteaux derivative (Definition 5.3.2) is `HasGateauxDerivAt` below, defined
from Mathlib's `HasLineDerivAt`; the identification is `HasFDerivAt.hasGateauxDerivAt`.

Contents: uniqueness of the Fréchet derivative (Definition 5.3.1), Proposition 5.3.3
(differentiable ⇒ continuous), Proposition 5.3.4 (Fréchet ⇒ Gâteaux, and the two converses),
Propositions 5.3.5–5.3.7 (sum, product and chain rules), Example 5.3.8 (affine maps),
Example 5.3.10 (the Fréchet derivative of the Urysohn integral operator),
Proposition 5.3.11 (mean value inequality (5.3.7)), Corollary 5.3.12, Proposition 5.3.13 (the
second-order Taylor remainder) together with the Lipschitz-derivative form
`norm_sub_sub_fderiv_le_half_mul_sq` used again in §5.4, and Definition 5.3.14 with
Proposition 5.3.15 on partial derivatives, including formula (5.3.8).  Section §5.3.4 on convex
functionals is Theorems 5.3.17–5.3.19: convexity via the tangent plane inequality and via
monotonicity of the derivative, their strict versions, and the characterization of a minimizer by
the variational inequality (5.3.10) and, over a subspace, the variational equation (5.3.11);
those four are specializations of `Numlib.Analysis.Convex.Gateaux`, which owns the general
statements and their proofs.

Left out, with the reason: Example 5.3.9 (Jacobian), Corollary 5.3.16 (the `C¹` form of
Proposition 5.3.15; a restatement, not used downstream), and the exercises — see
`plans/atkinsonhan-ch5.md` §4.

§5.5 (completely continuous vector fields) is summarized rather than formalized: Theorem 5.5.1
(Brouwer), Example 5.5.2, Definition 5.5.3 (compact and completely continuous nonlinear
operators), Theorem 5.5.4 (Schauder), Proposition 5.5.5 and the rotation properties P1–P5 are all
quoted in the book without proof and have no Mathlib support (Mathlib's `IsCompactOperator` is
for linear maps only, and Brouwer's theorem is available only in dimension one).
-/

open Filter Set Topology

namespace AtkinsonHan.Chapter05

section Frechet

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]

/-- Definition 5.3.1: the Fréchet derivative is unique. -/
theorem fderiv_unique {f : V₁ → V₂} {A B : V₁ →L[ℝ] V₂} {u₀ : V₁} (hA : HasFDerivAt f A u₀)
    (hB : HasFDerivAt f B u₀) : A = B :=
  hA.unique hB

/-- Definition 5.3.1 in the book's little-`o` form (5.3.5):
`f(u₀ + h) = f(u₀) + A h + o(‖h‖)`. -/
theorem hasFDerivAt_iff_isLittleO {f : V₁ → V₂} {A : V₁ →L[ℝ] V₂} {u₀ : V₁} :
    HasFDerivAt f A u₀ ↔ (fun h => f (u₀ + h) - f u₀ - A h) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

/-- The book requires `u₀` to be an interior point of the domain `K`, i.e. `B(u₀, r) ⊆ K`; this is
`K ∈ 𝓝 u₀`, and there the derivative within `K` is the derivative at `u₀`. -/
theorem hasFDerivWithinAt_iff_of_mem_nhds {f : V₁ → V₂} {A : V₁ →L[ℝ] V₂} {K : Set V₁} {u₀ : V₁}
    (hK : K ∈ 𝓝 u₀) : HasFDerivWithinAt f A K u₀ ↔ HasFDerivAt f A u₀ :=
  ⟨fun h => h.hasFDerivAt hK, fun h => h.hasFDerivWithinAt⟩

/-- **Proposition 5.3.3**: a Fréchet differentiable operator is continuous. -/
theorem proposition_5_3_3 {f : V₁ → V₂} {A : V₁ →L[ℝ] V₂} {u₀ : V₁} (hf : HasFDerivAt f A u₀) :
    ContinuousAt f u₀ :=
  hf.continuousAt

/-- **Proposition 5.3.5** (sum rule) for Fréchet derivatives. -/
theorem proposition_5_3_5 {f g : V₁ → V₂} {A B : V₁ →L[ℝ] V₂} {u₀ : V₁} (hf : HasFDerivAt f A u₀)
    (hg : HasFDerivAt g B u₀) (c : ℝ) :
    HasFDerivAt (fun u => f u + c • g u) (A + c • B) u₀ :=
  hf.add (hg.const_smul c)

/-- **Proposition 5.3.6** (product rule): if `b` is a bounded bilinear map then
`B(u) = b(f₁ u, f₂ u)` is differentiable with `B'(u₀) h = b(f₁'(u₀) h, f₂(u₀)) +
b(f₁(u₀), f₂'(u₀) h)`. -/
theorem proposition_5_3_6 {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W]
    [NormedSpace ℝ W] (b : V₁ →L[ℝ] V₂ →L[ℝ] W) {f₁ : V → V₁} {f₂ : V → V₂} {A₁ : V →L[ℝ] V₁}
    {A₂ : V →L[ℝ] V₂} {u₀ : V} (h₁ : HasFDerivAt f₁ A₁ u₀) (h₂ : HasFDerivAt f₂ A₂ u₀) :
    HasFDerivAt (fun u => b (f₁ u) (f₂ u))
      ((b.flip (f₂ u₀)).comp A₁ + (b (f₁ u₀)).comp A₂) u₀ := by
  have h := b.hasFDerivAt_of_bilinear h₁ h₂
  convert h using 1
  ext u
  simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, add_comm]

/-- **Proposition 5.3.7** (chain rule). -/
theorem proposition_5_3_7 {f : V₁ → V₂} {g : V₂ → V₃} {A : V₁ →L[ℝ] V₂} {B : V₂ →L[ℝ] V₃} {u₀ : V₁}
    (hg : HasFDerivAt g B (f u₀)) (hf : HasFDerivAt f A u₀) :
    HasFDerivAt (fun u => g (f u)) (B.comp A) u₀ :=
  hg.comp u₀ hf

/-- **Example 5.3.8**: an affine map `f v = L v + b` has the constant derivative `L`. -/
theorem example_5_3_8 (L : V₁ →L[ℝ] V₂) (b : V₂) (u₀ : V₁) :
    HasFDerivAt (fun v => L v + b) L u₀ :=
  L.hasFDerivAt.add_const b

end Frechet

section Urysohn

open IntegralOperator

/-- **Example 5.3.10**: the Fréchet derivative of the Urysohn integral operator
`u ↦ (x ↦ ∫_a^b k(x, y, u(y)) dy)` on `C[a, b]` is the Fredholm operator with kernel
`∂_u k(x, y, u(y))`. -/
theorem example_5_3_10 {a b : ℝ} (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    (hk : ∀ (x y : Icc a b) (z : ℝ), HasDerivAt (fun t => k (x, y, t)) (kz (x, y, z)) z)
    (u : C(Icc a b, ℝ)) :
    HasFDerivAt (urysohn hab k) (fredholm hab (urysohnDerivKernel kz u)) u :=
  hasFDerivAt_urysohn hab hk u

end Urysohn

section Gateaux

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Definition 5.3.2**: `A ∈ L(V, W)` is the Gâteaux derivative of `f` at `u₀` when
`lim_{t → 0} (f(u₀ + t h) - f(u₀))/t = A h` for every direction `h`.  Each of these limits is
Mathlib's `HasLineDerivAt`. -/
def HasGateauxDerivAt (f : V → W) (A : V →L[ℝ] W) (u₀ : V) : Prop :=
  ∀ h : V, HasLineDerivAt ℝ f (A h) u₀ h

/-- Definition 5.3.2 spelled out as a limit of difference quotients. -/
theorem hasGateauxDerivAt_iff_tendsto {f : V → W} {A : V →L[ℝ] W} {u₀ : V} :
    HasGateauxDerivAt f A u₀ ↔
      ∀ h : V, Tendsto (fun t : ℝ => t⁻¹ • (f (u₀ + t • h) - f u₀)) (𝓝[≠] 0) (𝓝 (A h)) := by
  simp only [HasGateauxDerivAt, hasLineDerivAt_iff_tendsto_slope_zero]

/-- The Gâteaux derivative is unique. -/
theorem HasGateauxDerivAt.unique {f : V → W} {A B : V →L[ℝ] W} {u₀ : V}
    (hA : HasGateauxDerivAt f A u₀) (hB : HasGateauxDerivAt f B u₀) : A = B := by
  ext h
  exact (hA h).unique (hB h)

/-- **Proposition 5.3.4**(i): a Fréchet derivative is a Gâteaux derivative. -/
theorem HasFDerivAt.hasGateauxDerivAt {f : V → W} {A : V →L[ℝ] W} {u₀ : V}
    (hf : HasFDerivAt f A u₀) : HasGateauxDerivAt f A u₀ := fun h => hf.hasLineDerivAt h

/-- **Proposition 5.3.5** (sum rule) for Gâteaux derivatives. -/
theorem HasGateauxDerivAt.add {f g : V → W} {A B : V →L[ℝ] W} {u₀ : V}
    (hf : HasGateauxDerivAt f A u₀) (hg : HasGateauxDerivAt g B u₀) :
    HasGateauxDerivAt (fun u => f u + g u) (A + B) u₀ := fun h =>
  HasDerivAt.add (hf h) (hg h)

/-- Scalar multiples, the other half of Proposition 5.3.5 for Gâteaux derivatives. -/
theorem HasGateauxDerivAt.const_smul {f : V → W} {A : V →L[ℝ] W} {u₀ : V}
    (hf : HasGateauxDerivAt f A u₀) (c : ℝ) :
    HasGateauxDerivAt (fun u => c • f u) (c • A) u₀ := fun h =>
  HasDerivAt.const_smul c (hf h)

/-- **Proposition 5.3.4**(ii): if the difference quotients converge *uniformly* over the unit
sphere of directions, the Gâteaux derivative is a Fréchet derivative. -/
theorem hasFDerivAt_of_hasGateauxDerivAt_uniform {f : V → W} {A : V →L[ℝ] W} {u₀ : V}
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ h : V, ‖h‖ = 1 → ∀ t : ℝ, 0 < t → t < δ →
      ‖t⁻¹ • (f (u₀ + t • h) - f u₀) - A h‖ ≤ ε) :
    HasFDerivAt f A u₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hunif ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : V) hδ] with h hh
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  have hnpos : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hlt : ‖h‖ < δ := by simpa [dist_eq_norm] using hh
  have he : ‖‖h‖⁻¹ • h‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  have hkey := hbound (‖h‖⁻¹ • h) he ‖h‖ hnpos hlt
  have hsm : ‖h‖ • (‖h‖⁻¹ • h) = h := by
    rw [smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul]
  have hexp : f (u₀ + h) - f u₀ - A h
      = ‖h‖ • (‖h‖⁻¹ • (f (u₀ + ‖h‖ • (‖h‖⁻¹ • h)) - f u₀) - A (‖h‖⁻¹ • h)) := by
    rw [hsm, smul_sub, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul, ← map_smul, hsm]
  rw [hexp, norm_smul, norm_norm, hsm]
  calc ‖h‖ * ‖‖h‖⁻¹ • (f (u₀ + h) - f u₀) - A (‖h‖⁻¹ • h)‖ ≤ ‖h‖ * ε := by
        gcongr
        rwa [hsm] at hkey
    _ = ε * ‖h‖ := mul_comm _ _

/-- Definition 5.3.2 gives the derivative of the restriction `s ↦ f (u + s • h)` only at `s = 0`;
a Gâteaux derivative at the point `u + t • h` gives it at `s = t`, by translating the parameter.
This is the form in which the mean value theorem is applied below; it is
`HasLineDerivAt.hasDerivAt_line` applied in the single direction `h`. -/
theorem HasGateauxDerivAt.hasDerivAt_line {f : V → W} {A : V →L[ℝ] W} {u h : V} {t : ℝ}
    (hG : HasGateauxDerivAt f A (u + t • h)) :
    HasDerivAt (fun s : ℝ => f (u + s • h)) (A h) t :=
  (hG h).hasDerivAt_line

/-- **Proposition 5.3.4**(iii): if `f` has a Gâteaux derivative `A u` at every point of a ball
around `u₀` and `u ↦ A u` is continuous at `u₀`, then `A u₀` is the Fréchet derivative of `f` at
`u₀`.  The proof is the book's: apply the mean value inequality to
`s ↦ f (u₀ + s h) - s A(u₀) h` on `[0, 1]`. -/
theorem hasFDerivAt_of_hasGateauxDerivAt_continuousAt {f : V → W} {A : V → V →L[ℝ] W} {u₀ : V}
    {r : ℝ} (hr : 0 < r) (hG : ∀ u ∈ Metric.ball u₀ r, HasGateauxDerivAt f (A u) u)
    (hA : ContinuousAt A u₀) : HasFDerivAt f (A u₀) u₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδA⟩ : ∃ δ > 0, ∀ u : V, ‖u - u₀‖ < δ → ‖A u - A u₀‖ ≤ ε := by
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hA ε hε
    refine ⟨δ, hδ, fun u hu => ?_⟩
    rw [← dist_eq_norm]
    exact (hd (by rwa [dist_eq_norm])).le
  filter_upwards [Metric.ball_mem_nhds (0 : V) (lt_min hδ hr)] with h hh
  have hnorm : ‖h‖ < min δ r := by simpa [dist_eq_norm] using hh
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, ‖(u₀ + t • h) - u₀‖ ≤ ‖h‖ := by
    intro t ht
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg h, ht.2, ht.1]
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, u₀ + t • h ∈ Metric.ball u₀ r := fun t ht => by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (hle t ht) (lt_of_lt_of_le hnorm (min_le_right _ _))
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (u₀ + s • h) - s • A u₀ h) (A (u₀ + t • h) h - A u₀ h) t := by
    intro t ht
    have h1 := (hG _ (hmem t ht)).hasDerivAt_line (t := t)
    have h2 : HasDerivAt (fun s : ℝ => s • A u₀ h) (A u₀ h) t := by
      simpa using (hasDerivAt_id t).smul_const (A u₀ h)
    exact h1.sub h2
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (u₀ + t • h) h - A u₀ h‖ ≤ ε * ‖h‖ := by
    intro t ht
    have hd : ‖A (u₀ + t • h) - A u₀‖ ≤ ε :=
      hδA _ (lt_of_le_of_lt (hle t ht) (lt_of_lt_of_le hnorm (min_le_left _ _)))
    calc ‖A (u₀ + t • h) h - A u₀ h‖ = ‖(A (u₀ + t • h) - A u₀) h‖ := by rw [sub_apply]
      _ ≤ ‖A (u₀ + t • h) - A u₀‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  rw [show f (u₀ + h) - f u₀ - A u₀ h = f (u₀ + h) - A u₀ h - f u₀ from by abel]
  simpa using hmvt

end Gateaux

section MeanValue

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Proposition 5.3.11**, the mean value inequality (5.3.7), with an explicit bound on the
derivative along the segment: `‖F u - F w‖ ≤ C ‖u - w‖`. -/
theorem proposition_5_3_11 {F : V → W} {F' : V → V →L[ℝ] W} {u w : V} {C : ℝ}
    (hF : ∀ z ∈ segment ℝ u w, HasFDerivAt F (F' z) z)
    (hC : ∀ z ∈ segment ℝ u w, ‖F' z‖ ≤ C) : ‖F u - F w‖ ≤ C * ‖u - w‖ :=
  (convex_segment u w).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hF z hz).hasFDerivWithinAt) hC (right_mem_segment ℝ u w)
    (left_mem_segment ℝ u w)

/-- **Proposition 5.3.11** in the book's form (5.3.7), with the supremum of `‖F'‖` over the
segment.  Continuity of `F'` (a hypothesis of the book) makes the supremum finite. -/
theorem proposition_5_3_11_iSup {F : V → W} {F' : V → V →L[ℝ] W} {u w : V}
    (hF : ∀ z ∈ segment ℝ u w, HasFDerivAt F (F' z) z) (hF' : Continuous F') :
    ‖F u - F w‖ ≤ (⨆ θ : Icc (0 : ℝ) 1, ‖F' ((1 - (θ : ℝ)) • u + (θ : ℝ) • w)‖) * ‖u - w‖ := by
  set c : Icc (0 : ℝ) 1 → ℝ := fun θ => ‖F' ((1 - (θ : ℝ)) • u + (θ : ℝ) • w)‖ with hc
  have hcont : Continuous c := by
    fun_prop
  have hbdd : BddAbove (range c) := (isCompact_range hcont).bddAbove
  refine proposition_5_3_11 hF fun z hz => ?_
  rw [segment_eq_image ℝ u w] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  exact le_ciSup hbdd ⟨θ, hθ⟩

/-- **Corollary 5.3.12**: an operator with vanishing derivative on a connected open set is
constant there. -/
theorem corollary_5_3_12 {F : V → W} {K : Set V} (hK : IsOpen K) (hKc : IsPreconnected K)
    (hF : DifferentiableOn ℝ F K) (hF' : K.EqOn (fderiv ℝ F) 0) {u v : V} (hu : u ∈ K)
    (hv : v ∈ K) : F u = F v :=
  hK.is_const_of_fderiv_eq_zero hKc hF hF' hu hv

/-- The `L/2` Taylor estimate for an operator with an `L`-Lipschitz derivative:
`‖F y - F x - F'(x)(y - x)‖ ≤ (L/2) ‖y - x‖²`.  It is the sharp form of Proposition 5.3.13 and
the analytic core of (5.4.5) in §5.4.

This is the backbone's `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le` with the
two-sided Lipschitz hypothesis the book states, specialised at `w = x`. -/
theorem norm_sub_sub_fderiv_le_half_mul_sq {s : Set V} (hs : Convex ℝ s) {F : V → W}
    {F' : V → V →L[ℝ] W} {L : ℝ} (hF : ∀ z ∈ s, HasFDerivAt F (F' z) z)
    (hL : ∀ z ∈ s, ∀ w ∈ s, ‖F' z - F' w‖ ≤ L * ‖z - w‖) {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F y - F x - F' x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 :=
  hs.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hF hx hy fun z hz => hL z hz x hx

/-- **Proposition 5.3.13**: for a twice differentiable `F` with `‖F''‖ ≤ C` on the segment,
`‖F(u₀ + h) - F(u₀) - F'(u₀) h‖ ≤ ½ C ‖h‖²`. -/
theorem proposition_5_3_13 {F : V → W} {F' : V → V →L[ℝ] W} {F'' : V → V →L[ℝ] V →L[ℝ] W} {u₀ h : V}
    {C : ℝ} (hF : ∀ z ∈ segment ℝ u₀ (u₀ + h), HasFDerivAt F (F' z) z)
    (hF' : ∀ z ∈ segment ℝ u₀ (u₀ + h), HasFDerivAt F' (F'' z) z)
    (hC : ∀ z ∈ segment ℝ u₀ (u₀ + h), ‖F'' z‖ ≤ C) :
    ‖F (u₀ + h) - F u₀ - F' u₀ h‖ ≤ C / 2 * ‖h‖ ^ 2 := by
  have hs : Convex ℝ (segment ℝ u₀ (u₀ + h)) := convex_segment _ _
  have hL : ∀ z ∈ segment ℝ u₀ (u₀ + h), ∀ w ∈ segment ℝ u₀ (u₀ + h),
      ‖F' z - F' w‖ ≤ C * ‖z - w‖ := fun z hz w hw =>
    hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun p hp => (hF' p hp).hasFDerivWithinAt) hC hw hz
  have hmain := norm_sub_sub_fderiv_le_half_mul_sq hs hF hL (left_mem_segment ℝ u₀ (u₀ + h))
    (right_mem_segment ℝ u₀ (u₀ + h))
  simpa using hmain

end MeanValue

section Partial

variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Definition 5.3.14** and **Proposition 5.3.15**(⇒): Fréchet differentiability of
`f : U × V → W` gives the partial derivative in the first variable. -/
theorem proposition_5_3_15_fst {f : U × V → W} {A : U × V →L[ℝ] W} {p : U × V}
    (hf : HasFDerivAt f A p) :
    HasFDerivAt (fun u => f (u, p.2)) (A.comp (ContinuousLinearMap.inl ℝ U V)) p.1 :=
  hf.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)

/-- **Definition 5.3.14** and **Proposition 5.3.15**(⇒), second variable. -/
theorem proposition_5_3_15_snd {f : U × V → W} {A : U × V →L[ℝ] W} {p : U × V}
    (hf : HasFDerivAt f A p) :
    HasFDerivAt (fun v => f (p.1, v)) (A.comp (ContinuousLinearMap.inr ℝ U V)) p.2 :=
  hf.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)

/-- **(5.3.8)**: the total derivative is the sum of the two partial derivatives,
`f'(u₀, v₀)(h, k) = f_u(u₀, v₀) h + f_v(u₀, v₀) k`. -/
theorem equation_5_3_8 (A : U × V →L[ℝ] W) (h : U) (k : V) :
    A (h, k) = A.comp (ContinuousLinearMap.inl ℝ U V) h
      + A.comp (ContinuousLinearMap.inr ℝ U V) k := by
  have hsum : ((h, k) : U × V) = (h, 0) + (0, k) := by simp
  rw [hsum, map_add]
  rfl

/-- **Proposition 5.3.15**(⇐): continuous partial derivatives near `(u₀, v₀)` imply Fréchet
differentiability, with derivative the coproduct of the partials (Mathlib's
`hasStrictFDerivAt_uncurry_coprod`). -/
theorem proposition_5_3_15_of_partial {f : U → V → W} {f₁ : U → V → U →L[ℝ] W}
    {f₂ : U → V → V →L[ℝ] W}
    {p : U × V} (df₁ : ∀ᶠ q in 𝓝 p, HasFDerivAt (f · q.2) (↿f₁ q) q.1)
    (df₂ : ∀ᶠ q in 𝓝 p, HasFDerivAt (f q.1 ·) (↿f₂ q) q.2) (cf₁ : ContinuousAt (↿f₁) p)
    (cf₂ : ContinuousAt (↿f₂) p) : HasFDerivAt (↿f) ((↿f₁ p).coprod (↿f₂ p)) p :=
  (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂).hasFDerivAt

end Partial

section Convexity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Set V} {f : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- **Theorem 5.3.17**: for a Gâteaux differentiable `f : V → ℝ` on a convex set `K`, the
following are equivalent: (a) `f` is convex on `K`; (b) `f u + ⟨f'(u), v - u⟩ ≤ f v` for all
`u, v ∈ K`; (c) the derivative is monotone, `⟨f'(v) - f'(u), v - u⟩ ≥ 0`.  The two equivalences
are `convexOn_iff_forall_add_lineDeriv_le` and `convexOn_iff_monotone_lineDeriv`, whose hypothesis
`∀ h, HasLineDerivAt ℝ f (f' u h) u h` is `HasGateauxDerivAt f (f' u) u` by definition. -/
theorem theorem_5_3_17 (hK : Convex ℝ K) (hG : ∀ u ∈ K, HasGateauxDerivAt f (f' u) u) :
    (ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) ∧
      (ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u)) :=
  ⟨convexOn_iff_forall_add_lineDeriv_le hK hG, convexOn_iff_monotone_lineDeriv hK hG⟩

/-- **Theorem 5.3.18**: the strict version of Theorem 5.3.17, from
`strictConvexOn_iff_forall_add_lineDeriv_lt` and `strictConvexOn_iff_forall_lineDeriv_sub_pos`. -/
theorem theorem_5_3_18 (hK : Convex ℝ K) (hG : ∀ u ∈ K, HasGateauxDerivAt f (f' u) u) :
    (StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v) ∧
      (StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (f' v - f' u) (v - u)) :=
  ⟨strictConvexOn_iff_forall_add_lineDeriv_lt hK hG,
    strictConvexOn_iff_forall_lineDeriv_sub_pos hK hG⟩

/-- **Theorem 5.3.19**: for a convex Gâteaux differentiable `f` on a convex set `K`, `u` minimizes
`f` over `K` if and only if it solves the variational inequality (5.3.10),
`⟨f'(u), v - u⟩ ≥ 0` for all `v ∈ K`.  The book states the two existence problems to be
equivalent; `isMinOn_iff_forall_lineDeriv_nonneg` gives this stronger pointwise form.  The book's
separate hypothesis that `K` is convex is `hcvx.1` and is not repeated. -/
theorem theorem_5_3_19 (hG : ∀ u ∈ K, HasGateauxDerivAt f (f' u) u) (hcvx : ConvexOn ℝ K f)
    {u : V} (hu : u ∈ K) : IsMinOn f K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) :=
  isMinOn_iff_forall_lineDeriv_nonneg hcvx hG hu

/-- **Theorem 5.3.19**, formula (5.3.11): when `K` is a subspace the variational inequality
becomes the variational equation `⟨f'(u), v⟩ = 0` for all `v ∈ K`.  This is
`isMinOn_iff_forall_lineDeriv_eq_zero`. -/
theorem theorem_5_3_19_submodule (K : Submodule ℝ V)
    (hG : ∀ u ∈ (K : Set V), HasGateauxDerivAt f (f' u) u) (hcvx : ConvexOn ℝ (K : Set V) f)
    {u : V} (hu : u ∈ K) : IsMinOn f (K : Set V) u ↔ ∀ v ∈ K, f' u v = 0 :=
  isMinOn_iff_forall_lineDeriv_eq_zero hcvx hG hu

end Convexity

end AtkinsonHan.Chapter05
