import Numlib.Variational.Forms
import Numlib.Nonlinear.FixedPoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Lax–Milgram, Babuška–Nečas, and existence theory for variational problems

* `SesqForm.laxMilgram`: a bounded coercive form on a Hilbert space is uniquely solvable,
  `‖u‖ ≤ ‖ℓ‖ / c` (Atkinson–Han[^atkinson-han] Thm 8.3.4; Kress[^kress] Thm 11.13 in operator
  form, Cor 11.16 for forms; Mathlib's `IsCoercive.continuousLinearEquivOfBilin` is the real
  case); proof routes: Riesz + `ContinuousLinearMap.exists_equiv_of_isCoerciveWith`
  (Atkinson–Han's second proof of Thm 8.3.4) or the damped fixed-point iteration (their first
  proof, `contractingWith_damped`).
* `SesqForm.isMinOn_energy_iff`: for Hermitian coercive forms, the solution is the unique
  minimizer of the energy (Atkinson–Han Thm 8.3.3; Saad[^saad-iterative] Prop 5.2 in operator
  form), on subspaces and on closed convex sets (variational inequalities, Atkinson–Han (8.3.3)).
* `SesqForm₂.babuska_necas`: the generalized Lax–Milgram lemma (Atkinson–Han Thm 8.7.1) under the
  inf–sup condition and nondegeneracy, with `‖u‖ ≤ ‖ℓ‖ / α` (8.7.5).
* Existence via a priori estimates (Atkinson–Han Thm 8.2.1–8.2.4): bounded-below operators with
  closed / dense range, including the closed-operator version.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

section BoundedBelow

/-! ### Bounded-below operators

The two workhorses of Atkinson–Han, *Theoretical Numerical Analysis*, §8.2 — a bounded-below
operator has closed range, and if in addition its range is dense then it is bijective — proved
once here and reused by `SesqForm₂.babuska_necas` and by the public statements at the end of the
file. -/

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

private theorem isClosed_range_aux (L : U →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) : IsClosed (LinearMap.range (L : U →ₗ[𝕜] W) : Set W) := by
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) L := by
    refine L.antilipschitz_of_bound fun v => ?_
    rw [Real.coe_toNNReal _ (by positivity), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h v
  rw [LinearMap.coe_range]
  exact hanti.isClosed_range L.uniformContinuous

private theorem injective_aux (L : U →L[𝕜] W) {c : ℝ} (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) :
    Function.Injective L := by
  intro x y hxy
  have hx := h (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at hx
  have hx0 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hx0)

private theorem bijective_aux (L : U →L[𝕜] W) {c : ℝ} (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    (hdense : (LinearMap.range (L : U →ₗ[𝕜] W))ᗮ = ⊥) : Function.Bijective L := by
  refine ⟨injective_aux L hc h, ?_⟩
  have hcs : CompleteSpace (LinearMap.range (L : U →ₗ[𝕜] W)) :=
    (isClosed_range_aux L hc h).completeSpace_coe
  have hrange : LinearMap.range (L : U →ₗ[𝕜] W) = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range (L : U →ₗ[𝕜] W)), hdense,
      Submodule.bot_orthogonal_eq_top]
  intro w
  have hw : w ∈ LinearMap.range (L : U →ₗ[𝕜] W) := by rw [hrange]; trivial
  obtain ⟨y, hy⟩ := hw
  exact ⟨y, hy⟩

end BoundedBelow

namespace SesqForm

variable (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)

/-- The Lax–Milgram operator is invertible; `hEq` shape used throughout. -/
private theorem exists_equiv_toOperator {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) :
    ∃ e : V ≃L[𝕜] V, (∀ u, toOperator a u = e u) ∧ ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / c := by
  obtain ⟨e, he, he'⟩ := ContinuousLinearMap.exists_equiv_of_isCoerciveWith hc
    ((a.isCoerciveWith_iff_toOperator c).mp ha)
  exact ⟨e, fun u => by rw [← he]; rfl, he'⟩

/-- Lax–Milgram (Atkinson–Han, *Theoretical Numerical Analysis*, Thm 8.3.4): a bounded coercive
form is uniquely solvable, that is, for every continuous functional `ℓ` there is exactly one `u`
with `a u v = ℓ v` for all `v`. -/
theorem laxMilgram {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) : ∃! u, ∀ v, a u v = ℓ v := by
  obtain ⟨e, hEq, -⟩ := a.exists_equiv_toOperator hc ha
  refine ⟨e.symm (rieszRep ℓ), ?_, ?_⟩
  · change ∀ v, a (e.symm (rieszRep ℓ)) v = ℓ v
    rw [a.forall_apply_eq_iff_toOperator_eq, hEq, e.apply_symm_apply]
  · intro y hy
    rw [a.forall_apply_eq_iff_toOperator_eq, hEq] at hy
    rw [← hy, e.symm_apply_apply]

/-- The stability estimate `‖u‖ ≤ ‖ℓ‖ / c`. -/
theorem norm_le_of_forall_apply_eq {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) {u : V}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / c := by
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · simp [← h]
  · refine le_of_mul_le_mul_right ?_ h
    calc ‖u‖ * c * ‖u‖ = c * ‖u‖ ^ 2 := by ring
      _ ≤ RCLike.re (a u u) := ha u
      _ = RCLike.re (ℓ u) := by rw [hu]
      _ ≤ ‖ℓ u‖ := RCLike.re_le_norm _
      _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u

/-- Lipschitz dependence on the data: the solution map `ℓ ↦ u` is `1 / c`-Lipschitz
(Atkinson–Han, *Theoretical Numerical Analysis*, (5.1.11), stated there for strongly monotone
maps). -/
theorem norm_sub_le_of_forall_apply_eq {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c)
    {ℓ₁ ℓ₂ : V →L[𝕜] 𝕜} {u₁ u₂ : V} (h₁ : ∀ v, a u₁ v = ℓ₁ v) (h₂ : ∀ v, a u₂ v = ℓ₂ v) :
    ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / c :=
  a.norm_le_of_forall_apply_eq (ℓ₁ - ℓ₂) hc ha fun v => by
    simp [map_sub, h₁, h₂]

/-- The solution operator `ℓ ↦ u` for the variational problem `a u v = ℓ v` (Atkinson–Han,
*Theoretical Numerical Analysis*, problem (8.3.5)) is a continuous *conjugate-linear* equivalence
`V' ≃L⋆ V`.

The statement was corrected from `≃L[𝕜]`/`→L[𝕜]` to `≃L⋆[𝕜]`/`→L⋆[𝕜]`: since `a` is
conjugate-linear in its first slot, `a (μ • u) v = conj μ * a u v`, so the solution map satisfies
`S (μ • ℓ) = conj μ • S ℓ` and is conjugate-linear. Over `ℝ` the two notions coincide. -/
theorem exists_solutionEquiv {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) :
    ∃ S : (V →L[𝕜] 𝕜) ≃L⋆[𝕜] V, (∀ ℓ v, a (S ℓ) v = ℓ v) ∧
      ‖(S : (V →L[𝕜] 𝕜) →L⋆[𝕜] V)‖ ≤ 1 / c := by
  obtain ⟨e, hEq, he'⟩ := a.exists_equiv_toOperator hc ha
  refine ⟨(InnerProductSpace.toDual 𝕜 V).symm.toContinuousLinearEquiv.trans e.symm, ?_, ?_⟩
  · intro ℓ' v
    revert v
    rw [a.forall_apply_eq_iff_toOperator_eq]
    change toOperator a (e.symm (rieszRep ℓ')) = rieszRep ℓ'
    rw [hEq, e.apply_symm_apply]
  · refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one hc.le) fun ℓ' => ?_
    change ‖e.symm (rieszRep ℓ')‖ ≤ 1 / c * ‖ℓ'‖
    calc ‖e.symm (rieszRep ℓ')‖ ≤ ‖(e.symm : V →L[𝕜] V)‖ * ‖rieszRep ℓ'‖ :=
          (e.symm : V →L[𝕜] V).le_opNorm _
      _ = ‖(e.symm : V →L[𝕜] V)‖ * ‖ℓ'‖ := by rw [norm_rieszRep]
      _ ≤ 1 / c * ‖ℓ'‖ := by gcongr

/-- The first of the two proofs of Lax–Milgram in Atkinson–Han, *Theoretical Numerical Analysis*,
Thm 8.3.4: the damped iteration `u ↦ u - θ (A u - f)` is a contraction with factor
`√(1 - 2θc + θ²‖a‖²)` for `0 < θ < 2c / ‖a‖²`, so the Banach fixed-point theorem produces the
solution (see `contractingWith_damped`,
`ContinuousLinearMap.norm_sub_smul_apply_sq_le`). -/
theorem contractingWith_damped_toOperator {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c)
    (ha0 : 0 < ‖a‖) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * c / ‖a‖ ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * ‖a‖ ^ 2)))
      (fun u => u - (θ : 𝕜) • (toOperator a u - rieszRep ℓ)) := by
  have hcoer := (a.isCoerciveWith_iff_toOperator c).mp ha
  have hmono : ∀ x y : V, c * ‖x - y‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (toOperator a x - toOperator a y) (x - y)) := by
    intro x y
    rw [← map_sub]
    exact hcoer (x - y)
  have hlip : LipschitzWith (Real.toNNReal ‖a‖) (toOperator a) := by
    rw [← a.norm_toOperator, ← coe_nnnorm, Real.toNNReal_coe]
    exact (toOperator a).lipschitzWith
  exact contractingWith_damped (𝕜 := 𝕜) hc ha0 hmono hlip (rieszRep ℓ) hθ hθ'

omit [CompleteSpace V] in
/-- Expansion of the energy around a point for a Hermitian form:
`E(u + w) - E(u) = re (a u w) - re (ℓ w) + ½ re (a w w)`. -/
private theorem energy_add_sub_energy (ha : a.IsHermitian) (u w : V) :
    a.energy ℓ (u + w) - a.energy ℓ u
      = RCLike.re (a u w) - RCLike.re (ℓ w) + (1 / 2 : ℝ) * RCLike.re (a w w) := by
  have hsym : RCLike.re (a w u) = RCLike.re (a u w) := by rw [ha w u, RCLike.conj_re]
  simp only [energy, map_add, add_apply]
  rw [hsym]
  ring

omit [CompleteSpace V] in
/-- The energy along the real line through `u` in direction `v`. -/
private theorem energy_smul_sub_energy (ha : a.IsHermitian) (u v : V) (t : ℝ) :
    a.energy ℓ (u + (t : 𝕜) • v) - a.energy ℓ u
      = t * (RCLike.re (a u v) - RCLike.re (ℓ v))
        + (1 / 2 : ℝ) * t ^ 2 * RCLike.re (a v v) := by
  rw [a.energy_add_sub_energy ℓ ha u ((t : 𝕜) • v)]
  simp only [map_smulₛₗ, smul_apply, smul_eq_mul, RCLike.conj_ofReal,
    RingHom.id_apply, RCLike.re_ofReal_mul]
  ring

/-- If a quadratic `t ↦ t δ + ½ t² q` with `q ≥ 0` is nonnegative for every real `t`, then
`δ = 0`. -/
private theorem eq_zero_of_forall_quadratic_nonneg {δ q : ℝ} (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 ≤ t * δ + (1 / 2 : ℝ) * t ^ 2 * q) : δ = 0 := by
  by_contra hδ
  have hq1 : (0 : ℝ) < q + 1 := by linarith
  obtain ⟨s, rfl⟩ : ∃ s : ℝ, δ = s * (q + 1) := ⟨δ / (q + 1), (div_mul_cancel₀ _ hq1.ne').symm⟩
  have hs0 : s ≠ 0 := fun h0 => hδ (by rw [h0, zero_mul])
  have h1 : 0 < s ^ 2 := (sq_nonneg s).lt_of_ne' (pow_ne_zero 2 hs0)
  nlinarith [h (-s), mul_nonneg h1.le hq]

/-- The energy functional is continuous (the quadratic part is a bounded bilinear map). -/
private theorem continuous_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) (ℓ : V →L[ℝ] ℝ) : Continuous (a.energy ℓ) := by
  have h1 : Continuous fun v : V => ((a v : V →L[ℝ] ℝ), v) := a.continuous.prodMk continuous_id
  have h2 : Continuous fun p : (V →L[ℝ] ℝ) × V => p.1 p.2 := isBoundedBilinearMap_apply.continuous
  have hq : Continuous fun v : V => a v v := h2.comp h1
  have hE : a.energy ℓ = fun v : V => (1 / 2 : ℝ) * a v v - ℓ v := by
    funext v
    simp [energy]
  rw [hE]
  exact (continuous_const.mul hq).sub ℓ.continuous

/-- Parallelogram identity for the energy of a symmetric real form:
`E x + E y - 2 E ((x + y) / 2) = ¼ a (x - y) (x - y)`. -/
private theorem energy_parallelogram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) (x y : V) :
    a.energy ℓ x + a.energy ℓ y - 2 * a.energy ℓ ((1 / 2 : ℝ) • (x + y))
      = (1 / 4 : ℝ) * a (x - y) (x - y) := by
  have hsym : a y x = a x y := by simpa using ha y x
  simp only [energy, RCLike.re_to_real, map_smulₛₗ, map_add, map_sub,
    add_apply, sub_apply,
    smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply,
    star_trivial]
  rw [hsym]
  ring

section Energy

variable {a} (ha : a.IsHermitian)
include ha

/-- Atkinson–Han, *Theoretical Numerical Analysis*, Thm 8.3.3 (subspace / whole-space case): for a
Hermitian coercive form, `u` solves `a u v = ℓ v` for all `v ∈ K` iff `u ∈ K` minimizes the energy
on the subspace `K`.  Taking `K = ⊤` recovers the equivalence of the variational problem with
minimizing `E` over the whole space. -/
theorem isMinOn_energy_iff {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (K : Submodule 𝕜 V)
    {u : V} (hu : u ∈ K) : IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v := by
  constructor
  · intro hmin
    -- the real part of the residual vanishes on `K` ...
    have hre : ∀ w ∈ K, RCLike.re (a u w) - RCLike.re (ℓ w) = 0 := by
      intro w hw
      refine eq_zero_of_forall_quadratic_nonneg
        (le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer w)) fun t => ?_
      have hmem : u + (t : 𝕜) • w ∈ K := K.add_mem hu (K.smul_mem _ hw)
      have hle := isMinOn_iff.mp hmin _ hmem
      have heq := a.energy_smul_sub_energy ℓ ha u w t
      linarith
    -- ... and applying it to `conj (a u v - ℓ v) • v` kills the residual itself
    intro v hv
    have hexp : ∀ (w : V) (μ : 𝕜), RCLike.re (a u (μ • w)) - RCLike.re (ℓ (μ • w))
        = RCLike.re (μ * (a u w - ℓ w)) := by
      intro w μ
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul,
        mul_sub, map_sub]
    have hz := hre ((starRingEnd 𝕜) (a u v - ℓ v) • v) (K.smul_mem _ hv)
    rw [hexp, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hz
    rw [← sub_eq_zero]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (a u v - ℓ v)])
  · intro h
    rw [isMinOn_iff]
    intro v hv
    have huv : u + (v - u) = v := by abel
    have heq := a.energy_add_sub_energy ℓ ha u (v - u)
    rw [huv, h _ (K.sub_mem hv hu)] at heq
    have hnn : 0 ≤ RCLike.re (a (v - u) (v - u)) :=
      le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer (v - u))
    linarith

omit ha in
/-- On a nonempty closed convex set `K` (real scalars), the energy minimizer is characterized by
the variational inequality `re (a u (v - u)) ≥ re (ℓ (v - u))` for all `v ∈ K` (Atkinson–Han,
*Theoretical Numerical Analysis*, (8.3.3)).  On a subspace the inequality can be applied to both
`v` and `2u - v`, which is how it collapses to the equality of `isMinOn_energy_iff`. -/
theorem isMinOn_energy_iff_forall_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hK : Convex ℝ K) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u) := by
  constructor
  · intro hmin v hv
    by_contra hlt
    push Not at hlt
    set δ : ℝ := a u (v - u) - ℓ (v - u) with hδdef
    have hδ : δ < 0 := by simp only [hδdef]; linarith
    set q : ℝ := a (v - u) (v - u) with hqdef
    have hq : 0 ≤ q := le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer (v - u))
    set t : ℝ := min 1 (-δ / (q + 1)) with htdef
    have hq1 : (0 : ℝ) < q + 1 := by linarith
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hq1)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htq : t * (q + 1) ≤ -δ := by
      have := min_le_right (1 : ℝ) (-δ / (q + 1))
      rw [← htdef] at this
      calc t * (q + 1) ≤ (-δ / (q + 1)) * (q + 1) := by nlinarith
        _ = -δ := div_mul_cancel₀ _ hq1.ne'
    have hmem : u + t • (v - u) ∈ K := by
      have := hK hu hv (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      module
    have hle := isMinOn_iff.mp hmin _ hmem
    have heq := a.energy_smul_sub_energy ℓ ha u (v - u) t
    simp only [RCLike.ofReal_real_eq_id, id_eq] at heq
    rw [show RCLike.re (a u (v - u)) - RCLike.re (ℓ (v - u)) = δ from rfl,
      show RCLike.re (a (v - u) (v - u)) = q from rfl] at heq
    nlinarith
  · intro h
    rw [isMinOn_iff]
    intro v hv
    have huv : u + (v - u) = v := by abel
    have heq := a.energy_add_sub_energy ℓ ha u (v - u)
    rw [huv] at heq
    have hq : 0 ≤ a (v - u) (v - u) := le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer (v - u))
    have hδ := h v hv
    simp only [RCLike.re_to_real] at heq
    linarith

omit ha in
/-- Existence and uniqueness of the energy minimizer on a nonempty closed convex set
(Atkinson–Han, *Theoretical Numerical Analysis*, Thm 8.3.3, which routes through their Thm 3.3.12
on minimizing a coercive, convex, lower semicontinuous functional; compare Mathlib's
`exists_norm_eq_iInf_of_complete_convex`).  The proof below is instead a direct minimizing-sequence
argument, using the parallelogram identity for the energy to get a Cauchy estimate. -/
theorem existsUnique_isMinOn_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hK : Convex ℝ K) (hKc : IsClosed K)
    (hne : K.Nonempty) : ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u := by
  have hcoer' : ∀ v : V, c * ‖v‖ ^ 2 ≤ a v v := fun v => by simpa using hcoer v
  have henergy : ∀ v : V, a.energy ℓ v = (1 / 2 : ℝ) * a v v - ℓ v := by
    intro v
    simp [SesqForm.energy]
  -- the energy is bounded below on all of `V`
  have hbelow : ∀ v : V, -(‖ℓ‖ ^ 2 / (2 * c)) ≤ a.energy ℓ v := by
    intro v
    have h1 : c * ‖v‖ ^ 2 ≤ a v v := hcoer' v
    have h2 : ℓ v ≤ ‖ℓ‖ * ‖v‖ := le_trans (le_abs_self _) (by simpa using ℓ.le_opNorm v)
    have h3 : c * (c * ‖v‖ ^ 2) ≤ c * (a v v) := mul_le_mul_of_nonneg_left h1 hc.le
    have key : -(‖ℓ‖ ^ 2) ≤ ((1 / 2 : ℝ) * a v v - ℓ v) * (2 * c) := by
      nlinarith [sq_nonneg (c * ‖v‖ - ‖ℓ‖), norm_nonneg v, mul_le_mul_of_nonneg_left h2 hc.le]
    rw [henergy v]
    calc -(‖ℓ‖ ^ 2 / (2 * c)) = -(‖ℓ‖ ^ 2) / (2 * c) := by ring
      _ ≤ (1 / 2 : ℝ) * a v v - ℓ v := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * c)]
          exact key
  set m : ℝ := sInf (a.energy ℓ '' K) with hmdef
  have hSne : (a.energy ℓ '' K).Nonempty := hne.image _
  have hSbdd : BddBelow (a.energy ℓ '' K) :=
    ⟨-(‖ℓ‖ ^ 2 / (2 * c)), by rintro _ ⟨v, -, rfl⟩; exact hbelow v⟩
  have hmle : ∀ v ∈ K, m ≤ a.energy ℓ v := fun v hv => csInf_le hSbdd ⟨v, hv, rfl⟩
  -- a minimizing sequence
  have hex : ∀ n : ℕ, ∃ v, v ∈ K ∧ a.energy ℓ v < m + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hyS, hy⟩ := Real.lt_sInf_add_pos hSne (by positivity : (0:ℝ) < 1 / ((n:ℝ) + 1))
    obtain ⟨v, hv, rfl⟩ := hyS
    exact ⟨v, hv, hy⟩
  choose u hu hlt using hex
  -- the parallelogram identity turns the minimizing property into a Cauchy estimate
  have hpara : ∀ x ∈ K, ∀ y ∈ K,
      c / 4 * ‖x - y‖ ^ 2 ≤ a.energy ℓ x + a.energy ℓ y - 2 * m := by
    intro x hx y hy
    have hmid : (1 / 2 : ℝ) • (x + y) ∈ K := by
      have h := hK hx hy (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num)
      convert h using 1
      module
    have hid := energy_parallelogram ha ℓ x y
    have h1 := hmle _ hmid
    have h2 : c * ‖x - y‖ ^ 2 ≤ a (x - y) (x - y) := hcoer' (x - y)
    linarith
  have hdist : ∀ n N : ℕ, N ≤ n → c / 4 * ‖u n - u N‖ ^ 2 < 2 / ((N : ℝ) + 1) := by
    intro n N hnN
    have h1 := hpara (u n) (hu n) (u N) (hu N)
    have h4 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hnN
      linarith
    have h5 : (2 : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
    linarith [hlt n, hlt N]
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (8 / (c * ε ^ 2))
    refine ⟨N, fun n hn => ?_⟩
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hcε : (0 : ℝ) < c * ε ^ 2 := by positivity
    have h2 : 8 < ((N : ℝ) + 1) * (c * ε ^ 2) := by
      have h6 : 8 / (c * ε ^ 2) < (N : ℝ) + 1 := by linarith
      calc (8 : ℝ) = 8 / (c * ε ^ 2) * (c * ε ^ 2) := by field_simp
        _ < ((N : ℝ) + 1) * (c * ε ^ 2) := by
            exact mul_lt_mul_of_pos_right h6 hcε
    have h3 : 2 / ((N : ℝ) + 1) < c / 4 * ε ^ 2 := by
      rw [div_lt_iff₀ hNpos]
      nlinarith
    have h7 : c / 4 * ‖u n - u N‖ ^ 2 < c / 4 * ε ^ 2 :=
      lt_trans (hdist n N hn) h3
    have h8 : ‖u n - u N‖ ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h7 (by positivity)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u n - u N)]
  obtain ⟨ustar, hustar⟩ := cauchySeq_tendsto_of_complete hcau
  have hmemK : ustar ∈ K := hKc.mem_of_tendsto hustar (Filter.Eventually.of_forall hu)
  have hElim : Filter.Tendsto (fun n => a.energy ℓ (u n)) Filter.atTop
      (nhds (a.energy ℓ ustar)) :=
    ((continuous_energy a ℓ).tendsto ustar).comp hustar
  have hmlim : Filter.Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds m) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_add m
  have hEm : a.energy ℓ ustar = m :=
    le_antisymm (le_of_tendsto_of_tendsto' hElim hmlim fun n => (hlt n).le) (hmle _ hmemK)
  refine ⟨ustar, ⟨hmemK, ?_⟩, ?_⟩
  · rw [isMinOn_iff]
    intro v hv
    rw [hEm]
    exact hmle v hv
  · rintro y ⟨hyK, hymin⟩
    have hEy : a.energy ℓ y = m :=
      le_antisymm (by rw [← hEm]; exact isMinOn_iff.mp hymin _ hmemK) (hmle _ hyK)
    have hp := hpara y hyK ustar hmemK
    rw [hEy, hEm] at hp
    have h1 : ‖y - ustar‖ ^ 2 ≤ 0 := by nlinarith
    have h2 : ‖y - ustar‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))

/-- The energy identity `E(v) - E(u) = ½ ‖v - u‖_a²` at the solution `u`: completing the square
turns minimizing `E` into minimizing the energy-norm distance to `u`, which is why the two
formulations agree.  This is the computation inside the proof of Atkinson–Han, *Theoretical
Numerical Analysis*, Thm 8.3.3, and inside the proof of Saad, *Iterative Methods for Sparse Linear
Systems*, Prop 5.2 in operator form.

A positivity hypothesis `hpos` was added: without it the right-hand side is `0` whenever
`re (a w w) < 0` (take `a = -⟪·,·⟫`, `ℓ = 0`, `u = 0`), while the left-hand side is not. -/
theorem energy_sub_energy_eq (hpos : a.IsCoerciveWith 0) {u : V} (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2 := by
  have huv : u + (v - u) = v := by abel
  have heq := a.energy_add_sub_energy ℓ ha u (v - u)
  rw [huv, hu (v - u)] at heq
  rw [heq, energyNorm, Real.sq_sqrt (by simpa using hpos (v - u))]
  ring

end Energy

end SesqForm

namespace SesqForm₂

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜)

/-- The two-space Riesz operator `B : U →L[𝕜] V` with `⟪B u, v⟫ = a u v`; the composite of `a`
with `InnerProductSpace.toDual.symm`, exactly as `continuousLinearMapOfBilin` in the one-space
case. Both factors are conjugate-linear, so `B` is linear. -/
private noncomputable def toOperator₂ : U →L[𝕜] V :=
  (InnerProductSpace.toDual 𝕜 V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp a

private theorem inner_toOperator₂ (u : U) (v : V) : inner 𝕜 (toOperator₂ a u) v = a u v := by
  simp [toOperator₂]

private theorem norm_toOperator₂_apply (u : U) : ‖toOperator₂ a u‖ = ‖a u‖ :=
  (InnerProductSpace.toDual 𝕜 V).symm.norm_map (a u)

private theorem forall_apply_eq_iff_toOperator₂_eq (u : U) :
    (∀ v, a u v = ℓ v) ↔ toOperator₂ a u = SesqForm.rieszRep ℓ := by
  constructor
  · intro h
    exact ext_inner_right 𝕜 fun v => by
      rw [inner_toOperator₂, SesqForm.inner_rieszRep, h]
  · intro h v
    rw [← inner_toOperator₂, h, SesqForm.inner_rieszRep]

/-- Generalized Lax–Milgram / Babuška–Nečas (Atkinson–Han, *Theoretical Numerical Analysis*,
Thm 8.7.1, a result they attribute to Nečas): under the inf–sup condition and nondegeneracy,
`a u v = ℓ v ∀ v` is uniquely solvable.  The inf–sup condition supplies injectivity and closed
range, nondegeneracy supplies density of the range. -/
theorem babuska_necas {α : ℝ} (hα : 0 < α) (hinf : a.InfSupWith α) (hnd : a.IsNondegenerate) :
    ∃! u, ∀ v, a u v = ℓ v := by
  have hbound : ∀ u : U, α * ‖u‖ ≤ ‖toOperator₂ a u‖ := fun u => by
    rw [norm_toOperator₂_apply]; exact hinf u
  have hperp : (LinearMap.range (toOperator₂ a : U →ₗ[𝕜] V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    obtain ⟨u, hu⟩ := hnd v hv0
    exact hu (by rw [← inner_toOperator₂ a u v]; exact hv _ ⟨u, rfl⟩)
  obtain ⟨hinj, hsurj⟩ := bijective_aux (toOperator₂ a) hα hbound hperp
  obtain ⟨u, hu⟩ := hsurj (SesqForm.rieszRep ℓ)
  refine ⟨u, (forall_apply_eq_iff_toOperator₂_eq a ℓ u).mpr hu, fun y hy => ?_⟩
  exact hinj (((forall_apply_eq_iff_toOperator₂_eq a ℓ y).mp hy).trans hu.symm)

/-- The stability estimate `‖u‖ ≤ ‖ℓ‖ / α` for the two-space problem, with `α` the inf–sup
constant (Atkinson–Han, *Theoretical Numerical Analysis*, (8.7.5)). -/
theorem norm_le_of_infSupWith {α : ℝ} (hα : 0 < α) (hinf : a.InfSupWith α) {u : U}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α := by
  rw [le_div_iff₀ hα, mul_comm]
  calc α * ‖u‖ ≤ ‖a u‖ := hinf u
    _ = ‖ℓ‖ := by rw [ContinuousLinearMap.ext hu]

/-- The inf–sup condition is necessary: if the problem is well posed with `‖u‖ ≤ C ‖ℓ‖` for all
`ℓ`, then `a.InfSupWith (1 / C)`.  This is the converse of Atkinson–Han, *Theoretical Numerical
Analysis*, Thm 8.7.1 (they state only the forward direction, and attribute the theorem to Nečas).

The injectivity hypothesis `hinj` was added: "well posed" in the source statement means *unique*
solvability, and mere existence of some bounded solution is not enough (take `V = 0` and
`U ≠ 0`: every `ℓ` is `0` and `u = 0` is a solution with `‖u‖ ≤ C ‖ℓ‖`, but `‖a u‖ = 0` for all
`u`, so no inf–sup constant exists). -/
theorem infSupWith_of_forall_exists {C : ℝ} (hC : 0 < C) (hinj : ∀ u : U, (∀ v, a u v = 0) → u = 0)
    (h : ∀ ℓ : V →L[𝕜] 𝕜, ∃ u, (∀ v, a u v = ℓ v) ∧ ‖u‖ ≤ C * ‖ℓ‖) :
    a.InfSupWith (1 / C) := by
  intro u₀
  obtain ⟨u, hu, hnorm⟩ := h (a u₀)
  have : u = u₀ := by
    have := hinj (u - u₀) fun v => by
      rw [map_sub, sub_apply, hu, sub_self]
    rwa [sub_eq_zero] at this
  rw [this] at hnorm
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC, mul_comm]
  exact hnorm

end SesqForm₂

section APriori

/-! ### Existence from a priori estimates

Following Atkinson–Han, *Theoretical Numerical Analysis*, §8.2: a lower bound `c ‖v‖ ≤ ‖L v‖`,
which in applications comes from an a priori estimate for the problem being solved, already
delivers injectivity and closed range, and hence solvability once the range is dense. -/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

/-- Atkinson–Han, *Theoretical Numerical Analysis*, Thm 8.2.1 and Thm 8.2.4 (bounded case): a
bounded-below operator `c ‖v‖ ≤ ‖L v‖` has closed range; if moreover its range is dense
(`(range L)ᗮ = ⊥`) it is bijective. -/
theorem ContinuousLinearMap.isClosed_range_of_le_norm (L : V →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) : IsClosed (LinearMap.range (L : V →ₗ[𝕜] W) : Set W) :=
  isClosed_range_aux L hc h

theorem ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot (L : V →L[𝕜] W)
    {c : ℝ} (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    (hdense : (LinearMap.range (L : V →ₗ[𝕜] W))ᗮ = ⊥) : Function.Bijective L :=
  bijective_aux L hc h hdense

/-- Atkinson–Han, *Theoretical Numerical Analysis*, Thm 8.2.4 (closed-operator version): a closed,
bounded-below, densely defined operator `L : V →ₗ.[𝕜] W` has closed range.  Closedness of the graph
replaces continuity: it is what lets the limit of a convergent sequence of images be recognized as
an image. -/
theorem LinearPMap.isClosed_range_of_isClosed_of_le_norm (L : V →ₗ.[𝕜] W) (hL : L.IsClosed)
    {c : ℝ} (hc : 0 < c) (h : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖) :
    _root_.IsClosed (LinearMap.range L.toFun : Set W) := by
  refine IsSeqClosed.isClosed fun u w hu hconv => ?_
  choose v hv using hu
  have hv' : ∀ n, L (v n) = u n := hv
  -- the preimages form a Cauchy sequence, by the lower bound
  have hcauchy : CauchySeq fun n => ((v n : V)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (c * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := h (v m - v n)
    rw [map_sub, hv', hv'] at hd
    rw [dist_eq_norm]
    have h₁ : dist (u m) (u n) < c * ε := hN m hm n hn
    rw [dist_eq_norm] at h₁
    have h₂ : c * ‖(v m : V) - (v n : V)‖ ≤ ‖u m - u n‖ := by
      simpa using hd
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the graph is closed, so `(x, w)` lies on it
  have hgraph : (x, w) ∈ L.graph :=
    hL.mem_of_tendsto (hx.prodMk_nhds hconv) (.of_forall fun n => by
      have hn := L.mem_graph (v n)
      rwa [hv' n] at hn)
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨y, -, hy⟩ := hgraph
  exact ⟨y, hy⟩

/-- The a priori (stability) estimate `‖v‖ ≤ C ‖L v‖` of Atkinson–Han, *Theoretical Numerical
Analysis*, (8.2.2), is equivalent to injectivity with continuous inverse on the range; here the
quantitative form `‖L⁻¹ w‖ ≤ C ‖w‖`. -/
theorem ContinuousLinearMap.norm_le_of_le_norm (L : V →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) {v : V} {w : W} (hv : L v = w) : ‖v‖ ≤ ‖w‖ / c := by
  rw [le_div_iff₀ hc, mul_comm, ← hv]
  exact h v

end APriori
