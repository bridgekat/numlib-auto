import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import NumlibSurface.Brezis.Chapter02.Section01

/-!
# Brezis §2.2: the uniform boundedness principle

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.2, for real Banach spaces `E`, `F` and bounded
operators `𝓛(E, F) = E →L[ℝ] F` with the norm `sup_{‖x‖ ≤ 1} ‖T x‖` (Mathlib's operator norm,
`ContinuousLinearMap.sSup_unitClosedBall_eq_norm`). Theorem 2.2 is Mathlib's `banach_steinhaus`;
Corollary 2.3 (c), Corollary 2.4 and Corollary 2.5 are the backbone
`Numlib/Analysis/Normed/Operator/BanachSteinhaus` (`opNorm_le_liminf_opNorm_of_tendsto`,
`isBounded_of_forall_dual_image_isBounded`, `StrongDual.isBounded_of_forall_eval_isBounded`).
The book assumes `E` and `F` complete throughout; the surface carries both hypotheses for
fidelity although only the completeness of `E` is used.

## Main results

* `opNorm_eq_sSup` — the notation `‖T‖_{𝓛(E,F)} = sup_{‖x‖ ≤ 1} ‖T x‖`.
* `theorem_2_2` — Banach–Steinhaus: a pointwise bounded family of bounded operators is
  uniformly bounded, with the estimate (2).
* `remark_2_3` — pointwise convergence `Tₙ x → T x` does not give `‖Tₙ - T‖ → 0`: the coordinate
  functionals on `ℓ²` converge pointwise to `0` and all have norm `1`.
* `corollary_2_3` — the pointwise limit of a sequence of bounded operators is a bounded operator,
  the norms are bounded, and `‖T‖ ≤ liminf ‖Tₙ‖`.
* `corollary_2_4`, `corollary_2_5` — weakly bounded sets are bounded; weak-∗ bounded sets of
  functionals are bounded.

Remark 2 is discussion; Remark 4 ("weakly bounded ⟺ strongly bounded") is the `iff` form of
Corollary 2.4, `isBounded_iff_forall_dual_image_isBounded`.
-/

open Bornology Filter Metric Topology

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The notation of §2.2.** For `T ∈ 𝓛(E, F)`, `‖T‖_{𝓛(E,F)} = sup_{‖x‖ ≤ 1} ‖T x‖`: the
surface's norm on operators is the book's. -/
theorem opNorm_eq_sSup (T : E →L[ℝ] F) : ‖T‖ = sSup ((fun x => ‖T x‖) '' closedBall 0 1) :=
  T.sSup_unitClosedBall_eq_norm.symm

/-- **Theorem 2.2 (Banach–Steinhaus, uniform boundedness principle).** Let `E`, `F` be Banach
spaces and `(Tᵢ)_{i ∈ I}` a family of bounded operators `E → F` with `sup_i ‖Tᵢ x‖ < ∞` for
every `x`. Then `sup_i ‖Tᵢ‖ < ∞`: there is a constant `c` with `‖Tᵢ x‖ ≤ c ‖x‖` for all `x`
and `i` (2). -/
theorem theorem_2_2 [CompleteSpace E] [CompleteSpace F] {ι : Type*} (T : ι → E →L[ℝ] F)
    (h : ∀ x, ∃ C : ℝ, ∀ i, ‖T i x‖ ≤ C) :
    ∃ c : ℝ, (∀ i, ‖T i‖ ≤ c) ∧ ∀ x i, ‖T i x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc⟩ := banach_steinhaus h
  exact ⟨c, hc, fun x i => (T i).le_of_opNorm_le (hc i) x⟩

/-- **Corollary 2.3.** Let `E`, `F` be Banach spaces and `(Tₙ)` a sequence of bounded
operators `E → F` such that `Tₙ x` converges for every `x`, to a limit denoted `T x`. Then
(a) `sup_n ‖Tₙ‖ < ∞`; (b) `T ∈ 𝓛(E, F)`; (c) `‖T‖ ≤ liminf ‖Tₙ‖`. -/
theorem corollary_2_3 [CompleteSpace E] [CompleteSpace F] (T : ℕ → E →L[ℝ] F)
    (h : ∀ x, ∃ y, Tendsto (fun n => T n x) atTop (𝓝 y)) :
    ∃ L : E →L[ℝ] F, (∃ C : ℝ, ∀ n, ‖T n‖ ≤ C) ∧
      (∀ x, Tendsto (fun n => T n x) atTop (𝓝 (L x))) ∧
      ‖L‖ ≤ liminf (fun n => ‖T n‖) atTop := by
  choose f hf using h
  have hpt : Tendsto (fun n x => T n x) atTop (𝓝 f) := tendsto_pi_nhds.2 hf
  obtain ⟨C, hC⟩ := banach_steinhaus (g := T) fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto _ (hf x))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  let L : E →L[ℝ] F :=
    (linearMapOfTendsto f (fun n => (T n : E →ₗ[ℝ] F)) hpt).mkContinuousOfExistsBound
      ⟨C, fun x => le_of_tendsto (hf x).norm
        (Eventually.of_forall fun n => (T n).le_of_opNorm_le (hC n) x)⟩
  refine ⟨L, ⟨C, hC⟩, fun x => hf x, ?_⟩
  exact ContinuousLinearMap.opNorm_le_liminf_opNorm_of_tendsto (fun x => hf x)
    ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩

/-- **Corollary 2.4.** Let `G` be a Banach space and `B ⊆ G` such that for every `f ∈ G*` the
set `f(B) = {⟨f, x⟩ | x ∈ B}` is bounded in `ℝ`. Then `B` is bounded. -/
theorem corollary_2_4 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : Set G} (h : ∀ f : StrongDual ℝ G, IsBounded (f '' B)) : IsBounded B :=
  isBounded_of_forall_dual_image_isBounded h

/-- **Corollary 2.5.** Let `G` be a Banach space and `B* ⊆ G*` such that for every `x ∈ G` the
set `⟨B*, x⟩ = {⟨f, x⟩ | f ∈ B*}` is bounded in `ℝ`. Then `B*` is bounded. -/
theorem corollary_2_5 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : Set (StrongDual ℝ G)} (h : ∀ x : G, IsBounded ((fun f : StrongDual ℝ G => f x) '' B)) :
    IsBounded B :=
  StrongDual.isBounded_of_forall_eval_isBounded h

/-! ### Remark 3: the coordinate functionals on `ℓ²` -/

/-- The coordinates of a square-summable sequence tend to `0` (used again in chapter 3,
Remark 9). -/
theorem tendsto_coord_zero (x : lp (fun _ : ℕ => ℝ) 2) :
    Tendsto (fun n => x n) atTop (𝓝 0) := by
  have hsum := (lp.memℓp x).summable (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat] at hsum
  have h2 := hsum.tendsto_atTop_zero
  have h := (Real.continuous_rpow_const (q := (2 : ℝ)⁻¹) (by norm_num)).tendsto 0 |>.comp h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (h.congr fun n => Real.rpow_rpow_inv (norm_nonneg _) two_ne_zero).mono_right ?_
  simp

/-- **Remark 3.** In the setting of Theorem 2.2, `Tₙ x → T x` for every `x` does not give
`‖Tₙ - T‖ → 0`: on `ℓ²`, the coordinate functionals `Tₙ x = xₙ` converge pointwise to `T = 0`,
while `‖Tₙ - T‖ = ‖Tₙ‖ = 1` for every `n`. -/
theorem remark_2_3 :
    (∀ x : lp (fun _ : ℕ => ℝ) 2,
      Tendsto (fun n => lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n x) atTop
        (𝓝 ((0 : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] ℝ) x))) ∧
    ¬ Tendsto (fun n => ‖lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n - 0‖) atTop (𝓝 0) := by
  refine ⟨fun x => ?_, fun h => ?_⟩
  · rw [zero_apply]
    exact tendsto_coord_zero x
  have hge : ∀ n, (1 : ℝ) ≤ ‖lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n - 0‖ := fun n => by
    rw [sub_zero]
    have := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).le_opNorm (lp.single 2 n (1 : ℝ))
    rw [lp.norm_single (by norm_num), norm_one, mul_one] at this
    simpa [lp.evalCLM, lp.single_apply_self] using this
  exact absurd (ge_of_tendsto' h hge) (by norm_num)

end Brezis.Chapter02
