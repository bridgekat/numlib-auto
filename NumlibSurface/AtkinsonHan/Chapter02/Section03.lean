import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.IntegralEquations.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Positivity.Finset

/-!
# Atkinson–Han §2.3: the geometric series theorem and its variants

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.3 , proved by specializing
`Numlib.Analysis.Normed.Ring.Inverse` and the Neumann-series API of Mathlib.

The book phrases invertibility as "`L` is a bijection of `V` onto `W` whose inverse is bounded".
Here that is `∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L`, and `L⁻¹` is `e.symm`; the bridge to the
ring-theoretic `IsUnit` used by the backbone is `isUnit_iff_exists_continuousLinearEquiv`.

## Main results

* `theorem_2_3_1` — geometric series theorem, with `(I - L)⁻¹ = ∑ Lⁿ` and (2.3.2).
* `equation_2_3_4`, `equation_2_3_5` — stability of, and partial-sum approximation for, `(I - L)u =
  f`.
* `example_2_3_2` — the second-kind equation `(λI - K)u = f` (abstract part).
* `corollary_2_3_3`, `example_2_3_4` — the variants under `‖Lᵐ‖ < 1`.
* `theorem_2_3_5` — the perturbation theorem, with (2.3.13), (2.3.14), (2.3.15).
* `equation_2_3_16`, `convergence_of_consistent_stable` — consistency plus stability gives
  convergence.
* `example_2_3_2_integral`, `example_2_3_4_volterra` — the concrete halves of the two examples,
  on `C[a, b]`, using the integral operators of `Numlib/IntegralEquations/Basic.lean` and the
  norm formula (2.2.8).

## Not formalized here

Example 2.3.6, a numerical solvability analysis with explicit constants.
-/

open Filter Topology

namespace AtkinsonHan.Chapter02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

section Units

/-- The coercion of `ContinuousLinearEquiv.ofUnit u` is the underlying operator of `u`. -/
private theorem coe_ofUnit (u : (V →L[𝕜] V)ˣ) :
    ((ContinuousLinearEquiv.ofUnit u : V ≃L[𝕜] V) : V →L[𝕜] V) = (u : V →L[𝕜] V) := by
  ext x; rfl

/-- The inverse of `ContinuousLinearEquiv.ofUnit u` computes `Ring.inverse`. -/
private theorem coe_ofUnit_symm (u : (V →L[𝕜] V)ˣ) :
    ((ContinuousLinearEquiv.ofUnit u).symm : V →L[𝕜] V) = Ring.inverse (u : V →L[𝕜] V) := by
  rw [Ring.inverse_unit]
  ext x; rfl

/-- Book-to-backbone bridge for "bijection with a bounded inverse": an operator of a normed space
into itself is a unit of `V →L[𝕜] V` exactly when it is (the coercion of) a continuous linear
equivalence. This is what lets the ring-level results of `Numlib.Analysis.Normed.Ring.Inverse`
prove the statements of Atkinson–Han §2.3. -/
theorem isUnit_iff_exists_continuousLinearEquiv (L : V →L[𝕜] V) :
    IsUnit L ↔ ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = L := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨ContinuousLinearEquiv.ofUnit u, coe_ofUnit u⟩
  · rintro ⟨e, rfl⟩
    exact ⟨ContinuousLinearEquiv.toUnit e, rfl⟩

/-- The form of `isUnit_iff_exists_continuousLinearEquiv` used in proofs: it also identifies the
inverse of the equivalence with `Ring.inverse`, so backbone bounds on `Ring.inverse` transfer. -/
private theorem exists_equiv_of_isUnit {L : V →L[𝕜] V} (h : IsUnit L) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = L ∧ (e.symm : V →L[𝕜] V) = Ring.inverse L := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨ContinuousLinearEquiv.ofUnit u, coe_ofUnit u, coe_ofUnit_symm u⟩

/-- Every operator on a trivial space has norm zero. Used to dispose of the degenerate case in
which `V →L[𝕜] V` is not `NormOneClass`. -/
private theorem norm_eq_zero_of_subsingleton [Subsingleton V] (T : V →L[𝕜] V) : ‖T‖ = 0 := by
  have : T = 0 := by ext x; exact Subsingleton.elim _ _
  rw [this, norm_zero]

end Units

/-! ### Theorem 2.3.1 -/

/-- **Geometric series theorem** (Theorem 2.3.1). If `V` is a Banach space and `L ∈ 𝓛(V)` has
`‖L‖ < 1`, then `I - L` is a bijection of `V` onto `V` with bounded inverse, the inverse is the
sum of the Neumann series `∑ₙ Lⁿ`, and `‖(I - L)⁻¹‖ ≤ 1 / (1 - ‖L‖)`, which is (2.3.2). -/
theorem theorem_2_3_1 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L ∧
      HasSum (fun n : ℕ => L ^ n) (e.symm : V →L[𝕜] V) ∧
      ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / (1 - ‖L‖) := by
  obtain ⟨e, he, hesymm⟩ := exists_equiv_of_isUnit (isUnit_one_sub_of_norm_lt_one hL)
  refine ⟨e, he, ?_, ?_⟩
  · rw [hesymm]
    exact hasSum_geom_series_inverse L hL
  · rw [hesymm, ← (hasSum_geom_series_inverse L hL).tsum_eq, one_div]
    have h1 : ‖(1 : V →L[𝕜] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 := tsum_geometric_le_of_norm_lt_one L hL
    linarith

/-- Stability of `(I - L)u = f` (the remark (2.3.4) after Theorem 2.3.1): the solution depends
Lipschitz-continuously on the data, with constant `1 / (1 - ‖L‖)`. -/
theorem equation_2_3_4 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) {u₁ u₂ f₁ f₂ : V}
    (h₁ : (1 - L) u₁ = f₁) (h₂ : (1 - L) u₂ = f₂) :
    ‖u₁ - u₂‖ ≤ 1 / (1 - ‖L‖) * ‖f₁ - f₂‖ := by
  obtain ⟨e, he, -, hb⟩ := theorem_2_3_1 L hL
  have hu : u₁ - u₂ = (e.symm : V →L[𝕜] V) (f₁ - f₂) := by
    rw [map_sub]
    have k₁ : (e.symm : V →L[𝕜] V) f₁ = u₁ := by
      rw [← h₁, ← he]; exact e.symm_apply_apply u₁
    have k₂ : (e.symm : V →L[𝕜] V) f₂ = u₂ := by
      rw [← h₂, ← he]; exact e.symm_apply_apply u₂
    rw [k₁, k₂]
  rw [hu]
  exact ((e.symm : V →L[𝕜] V).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- Approximation of the solution of `(I - L)u = f` by the partial sums of the Neumann series
(2.3.5): `uₙ = ∑_{j ≤ n} Lʲ f → u`. -/
theorem equation_2_3_5 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) {u f : V}
    (hu : (1 - L) u = f) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), (L ^ j) f) atTop (𝓝 u) := by
  obtain ⟨e, he, hsum, -⟩ := theorem_2_3_1 L hL
  have hu' : (e.symm : V →L[𝕜] V) f = u := by
    rw [← hu, ← he]; exact e.symm_apply_apply u
  have happ : HasSum (fun n : ℕ => (L ^ n) f) u := by
    rw [← hu']
    exact hsum.mapL (ContinuousLinearMap.apply 𝕜 V f)
  exact happ.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-! ### Example 2.3.2 -/

/-- **Second-kind equations** (Example 2.3.2, abstract part). If `‖K‖ < |λ|` then `λI - K` is
invertible with `‖(λI - K)⁻¹‖ ≤ 1 / (|λ| - ‖K‖)`; consequently the solution of `(λI - K)u = f`
satisfies `‖u‖ ≤ ‖f‖ / (|λ| - ‖K‖)`. The concrete part of the example, where `K` is an integral
operator on `C[a, b]` with `‖K‖` given by (2.2.8), needs integral operators, which are not yet
available. -/
theorem example_2_3_2 [CompleteSpace V] (K : V →L[𝕜] V) {lam : 𝕜} (h : ‖K‖ < ‖lam‖) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = lam • (1 : V →L[𝕜] V) - K ∧
      ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / (‖lam‖ - ‖K‖) := by
  have hlampos : 0 < ‖lam‖ := lt_of_le_of_lt (norm_nonneg K) h
  have hlam : lam ≠ 0 := norm_pos_iff.mp hlampos
  have hLnorm : ‖lam⁻¹ • K‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_one₀ hlampos]
    exact h
  obtain ⟨e₀, he₀, -, hb₀⟩ := theorem_2_3_1 (lam⁻¹ • K) hLnorm
  have hcancel : (e₀ : V →L[𝕜] V) * (e₀.symm : V →L[𝕜] V) = 1 := by
    ext x; exact e₀.apply_symm_apply x
  have hcancel' : (e₀.symm : V →L[𝕜] V) * (e₀ : V →L[𝕜] V) = 1 := by
    ext x; exact e₀.symm_apply_apply x
  have hval : lam • (e₀ : V →L[𝕜] V) = lam • (1 : V →L[𝕜] V) - K := by
    rw [he₀, smul_sub, smul_inv_smul₀ hlam]
  refine ⟨ContinuousLinearEquiv.ofUnit
    ⟨lam • (e₀ : V →L[𝕜] V), lam⁻¹ • (e₀.symm : V →L[𝕜] V), ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hcancel, mul_inv_cancel₀ hlam, one_smul]
  · rw [smul_mul_smul_comm, hcancel', inv_mul_cancel₀ hlam, one_smul]
  · rw [coe_ofUnit]
    exact hval
  · rw [coe_ofUnit_symm, Ring.inverse_unit]
    change ‖lam⁻¹ • (e₀.symm : V →L[𝕜] V)‖ ≤ 1 / (‖lam‖ - ‖K‖)
    have hnorm : ‖lam⁻¹ • K‖ = ‖K‖ / ‖lam‖ := by
      rw [norm_smul, norm_inv, div_eq_inv_mul]
    rw [norm_smul, norm_inv]
    rw [hnorm] at hb₀
    have hpos : 0 < 1 - ‖K‖ / ‖lam‖ := by
      have : ‖K‖ / ‖lam‖ < 1 := (div_lt_one hlampos).2 h
      linarith
    have hsplit : 1 - ‖K‖ / ‖lam‖ = (‖lam‖ - ‖K‖) / ‖lam‖ := by
      field_simp
    have hnum : 0 < ‖lam‖ - ‖K‖ := by linarith
    calc ‖lam‖⁻¹ * ‖(e₀.symm : V →L[𝕜] V)‖
        ≤ ‖lam‖⁻¹ * (1 / (1 - ‖K‖ / ‖lam‖)) :=
          mul_le_mul_of_nonneg_left hb₀ (by positivity)
      _ = 1 / (‖lam‖ - ‖K‖) := by
          rw [hsplit, one_div_div]
          field_simp

/-- The solution bound of Example 2.3.2: `(λI - K)u = f` forces `‖u‖ ≤ ‖f‖ / (|λ| - ‖K‖)`. -/
theorem example_2_3_2_bound [CompleteSpace V] (K : V →L[𝕜] V) {lam : 𝕜} (h : ‖K‖ < ‖lam‖)
    {u f : V} (hu : (lam • (1 : V →L[𝕜] V) - K) u = f) : ‖u‖ ≤ ‖f‖ / (‖lam‖ - ‖K‖) := by
  obtain ⟨e, he, hb⟩ := example_2_3_2 K h
  have hu' : (e.symm : V →L[𝕜] V) f = u := by
    rw [← hu, ← he]; exact e.symm_apply_apply u
  rw [← hu', div_eq_inv_mul, ← one_div]
  exact ((e.symm : V →L[𝕜] V).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-! ### Corollary 2.3.3 -/

set_option linter.unusedVariables false in
/-- **Corollary 2.3.3.** If `‖Lᵐ‖ < 1` for some `m ≥ 1` (2.3.10), then `I - L` is still a
bijection with bounded inverse, and `‖(I - L)⁻¹‖ ≤ (∑_{i<m} ‖Lⁱ‖) / (1 - ‖Lᵐ‖)`, which is
(2.3.11). The hypothesis `1 ≤ m` is kept for faithfulness; the backbone does not need it, since
`‖L⁰‖ = ‖1‖ < 1` is impossible in a nontrivial space. -/
theorem corollary_2_3_3 [CompleteSpace V] (L : V →L[𝕜] V) {m : ℕ} (hm : 1 ≤ m) (hL : ‖L ^ m‖ < 1) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L ∧
      ‖(e.symm : V →L[𝕜] V)‖ ≤ (∑ i ∈ Finset.range m, ‖L ^ i‖) / (1 - ‖L ^ m‖) := by
  have hden : 0 < 1 - ‖L ^ m‖ := by linarith
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨ContinuousLinearEquiv.refl 𝕜 V, ?_, ?_⟩
    · ext x; exact Subsingleton.elim _ _
    · rw [norm_eq_zero_of_subsingleton]
      positivity
  · have hnt : Nontrivial V := hV
    obtain ⟨e, he, hesymm⟩ :=
      exists_equiv_of_isUnit (NormedRing.isUnit_one_sub_of_norm_pow_lt_one hL)
    exact ⟨e, he, hesymm ▸ NormedRing.norm_inverse_one_sub_le_of_norm_pow_lt_one hL⟩

/-- **Example 2.3.4** (abstract part). If `‖Lᵏ‖ → 0` — as happens for the Volterra integral
operator, whose iterated kernels give `‖Lᵏ‖ ≤ (MB)ᵏ / k!` — then `I - L` is invertible. The
kernel estimate itself needs integral operators on `C[0, B]`, which are not yet available. -/
theorem example_2_3_4 [CompleteSpace V] (L : V →L[𝕜] V)
    (h : Tendsto (fun k : ℕ => ‖L ^ k‖) atTop (𝓝 0)) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L := by
  obtain ⟨m, hm⟩ := ((h.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop 1)).exists
  obtain ⟨e, he, -⟩ := corollary_2_3_3 L hm.2 hm.1
  exact ⟨e, he⟩

/-! ### Theorem 2.3.5 -/

/-- A continuous linear equivalence transports completeness, so the book's hypothesis "at least
one of `V`, `W` is complete" in Theorem 2.3.5 is symmetric in the two spaces. -/
theorem completeSpace_of_equiv (L : V ≃L[𝕜] W) [CompleteSpace W] : CompleteSpace V :=
  (completeSpace_congr (e := L.toLinearEquiv.toEquiv) L.isUniformEmbedding).2 ‹_›

/-- **Perturbation theorem** (Theorem 2.3.5). Let `L ∈ 𝓛(V, W)` be a bijection with bounded
inverse and let `M ∈ 𝓛(V, W)` satisfy `‖M - L‖ < 1 / ‖L⁻¹‖` (2.3.12). Then `M` is also a
bijection with bounded inverse, and
`‖M⁻¹‖ ≤ ‖L⁻¹‖ / (1 - ‖L⁻¹‖ ‖L - M‖)` (2.3.13),
`‖L⁻¹ - M⁻¹‖ ≤ ‖L⁻¹‖² ‖L - M‖ / (1 - ‖L⁻¹‖ ‖L - M‖)` (2.3.14),
`‖v₁ - v₂‖ ≤ ‖M⁻¹‖ ‖(L - M) v₁‖` whenever `L v₁ = w = M v₂` (2.3.15). -/
theorem theorem_2_3_5 (hc : CompleteSpace V ∨ CompleteSpace W) (L : V ≃L[𝕜] W) (M : V →L[𝕜] W)
    (hM : ‖M - (L : V →L[𝕜] W)‖ < 1 / ‖(L.symm : W →L[𝕜] V)‖) :
    ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = M ∧
      ‖(e.symm : W →L[𝕜] V)‖ ≤
        ‖(L.symm : W →L[𝕜] V)‖ / (1 - ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W) - M‖) ∧
      ‖(L.symm : W →L[𝕜] V) - (e.symm : W →L[𝕜] V)‖ ≤
        ‖(L.symm : W →L[𝕜] V)‖ ^ 2 * ‖(L : V →L[𝕜] W) - M‖ /
          (1 - ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W) - M‖) ∧
      ∀ w : W, ∀ v₁ v₂ : V, L v₁ = w → M v₂ = w →
        ‖v₁ - v₂‖ ≤ ‖(e.symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - M) v₁‖ := by
  have : CompleteSpace V := hc.elim id fun _ => completeSpace_of_equiv L
  have hLpos : 0 < ‖(L.symm : W →L[𝕜] V)‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (L.symm : W →L[𝕜] V)) with h | h
    · rw [← h, div_zero] at hM
      exact absurd hM (not_lt.2 (norm_nonneg _))
    · exact h
  have hkey : ‖(L.symm : W →L[𝕜] V)‖ * ‖M - (L : V →L[𝕜] W)‖ < 1 := by
    rw [mul_comm, ← lt_div_iff₀ hLpos]
    exact hM
  obtain ⟨e, he, hb₁, hb₂⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add L (M - (L : V →L[𝕜] W)) hkey
  have hrev : ‖(L : V →L[𝕜] W) - M‖ = ‖M - (L : V →L[𝕜] W)‖ := norm_sub_rev _ _
  have he' : (e : V →L[𝕜] W) = M := by rw [he]; abel
  refine ⟨e, he', ?_, ?_, ?_⟩
  · rw [hrev]; exact hb₁
  · rw [hrev, norm_sub_rev]; exact hb₂
  · intro w v₁ v₂ hv₁ hv₂
    have hMe : (e : V →L[𝕜] W) v₂ = M v₂ := by rw [he']
    have happ : (L : V →L[𝕜] W) v₁ = e v₂ := by
      simp only [ContinuousLinearEquiv.coe_coe] at hMe ⊢
      rw [hv₁, hMe, hv₂]
    have hb := ContinuousLinearEquiv.norm_sub_le_of_apply_eq (L : V →L[𝕜] W) e happ
    rwa [he'] at hb

/-! ### Consistency, stability and convergence (2.3.16) -/

/-- **(2.3.16), first part.** If `Lₙ → L` in `𝓛(V, W)` and `L` is a bijection with bounded
inverse, then for all large `n` the approximating equation `Lₙ vₙ = w` is uniquely solvable and
the error obeys `‖v - vₙ‖ ≤ ‖Lₙ⁻¹‖ ‖(L - Lₙ) v‖`.

The inverses are produced as a family `eₙ`, which is exactly the data
`convergence_of_consistent_stable` consumes, so the two halves of (2.3.16) compose. -/
theorem equation_2_3_16 (hc : CompleteSpace V ∨ CompleteSpace W) (L : V ≃L[𝕜] W)
    (Ln : ℕ → V →L[𝕜] W)
    (hLn : Tendsto (fun n => ‖(L : V →L[𝕜] W) - Ln n‖) atTop (𝓝 0)) :
    ∃ N : ℕ, ∃ en : ∀ n, N ≤ n → (V ≃L[𝕜] W),
      (∀ n hn, ((en n hn : V ≃L[𝕜] W) : V →L[𝕜] W) = Ln n) ∧
        ∀ n hn, ∀ w : W, ∀ v vn : V, L v = w → Ln n vn = w →
          ‖v - vn‖ ≤ ‖((en n hn).symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - Ln n) v‖ := by
  suffices h : ∃ N : ℕ, ∀ n, N ≤ n → ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = Ln n ∧
      ∀ w : W, ∀ v vn : V, L v = w → Ln n vn = w →
        ‖v - vn‖ ≤ ‖(e.symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - Ln n) v‖ by
    obtain ⟨N, hN⟩ := h
    choose en hen hbound using hN
    exact ⟨N, en, hen, hbound⟩
  rcases eq_or_lt_of_le (norm_nonneg (L.symm : W →L[𝕜] V)) with h | h
  · -- Degenerate case `‖L⁻¹‖ = 0`: both spaces are trivial and every claim is vacuous.
    have hWz : ∀ z : W, z = 0 := fun z => by
      have hb := (L.symm : W →L[𝕜] V).le_opNorm z
      rw [← h, zero_mul] at hb
      simpa using congrArg (⇑L) (norm_le_zero_iff.1 hb)
    have hVz : ∀ z : V, z = 0 := fun z => by
      simpa using congrArg (⇑(L.symm : W →L[𝕜] V)) (hWz (L z))
    refine ⟨0, fun n _ => ⟨L, ?_, fun w v vn _ _ => ?_⟩⟩
    · ext x
      rw [hWz ((L : V →L[𝕜] W) x), hWz (Ln n x)]
    · rw [hVz v, hVz vn, sub_zero, norm_zero]
      positivity
  · have hpos : (0 : ℝ) < 1 / ‖(L.symm : W →L[𝕜] V)‖ := by positivity
    obtain ⟨N, hN⟩ := (hLn.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    have hlt : ‖Ln n - (L : V →L[𝕜] W)‖ < 1 / ‖(L.symm : W →L[𝕜] V)‖ := by
      rw [norm_sub_rev]
      exact hN n hn
    obtain ⟨e, he, -, -, hb⟩ := theorem_2_3_5 hc L (Ln n) hlt
    exact ⟨e, he, hb⟩

/-- **(2.3.16), second part.** Consistency (`‖(L - Lₙ) v‖ → 0`) together with stability (a uniform
bound on `‖Lₙ⁻¹‖`) implies convergence `vₙ → v` of the approximate solutions. The families `eₙ`
and `vₙ` are only defined for `n ≥ N`, as `equation_2_3_16` provides them, and the conclusion is
indexed
accordingly. -/
theorem convergence_of_consistent_stable (hc : CompleteSpace V ∨ CompleteSpace W)
    (L : V ≃L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) (N : ℕ) (en : ∀ n, N ≤ n → (V ≃L[𝕜] W))
    (hen : ∀ n hn, ((en n hn : V ≃L[𝕜] W) : V →L[𝕜] W) = Ln n) {v : V}
    (vn : ∀ n, N ≤ n → V) (hv : ∀ n hn, Ln n (vn n hn) = L v)
    (hcons : Tendsto (fun n => ‖((L : V →L[𝕜] W) - Ln n) v‖) atTop (𝓝 0))
    (hstab : ∃ C : ℝ, ∀ n hn, ‖((en n hn).symm : W →L[𝕜] V)‖ ≤ C) :
    Tendsto (fun k : ℕ => ‖v - vn (k + N) (Nat.le_add_left N k)‖) atTop (𝓝 0) := by
  have : CompleteSpace V := hc.elim id fun _ => completeSpace_of_equiv L
  obtain ⟨C, hC⟩ := hstab
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC N le_rfl)
  have hshift : Tendsto (fun k : ℕ => C * ‖((L : V →L[𝕜] W) - Ln (k + N)) v‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hcons.const_mul C).comp (tendsto_add_atTop_nat N)
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hshift
  set n := k + N with hn'
  have hn : N ≤ n := Nat.le_add_left N k
  have hEq : ((en n hn : V ≃L[𝕜] W) : V →L[𝕜] W) (vn n hn) = Ln n (vn n hn) := by rw [hen n hn]
  have happ : (L : V →L[𝕜] W) v = en n hn (vn n hn) := by
    simp only [ContinuousLinearEquiv.coe_coe] at hEq ⊢
    rw [← hv n hn, hEq]
  have hb := ContinuousLinearEquiv.norm_sub_le_of_apply_eq (L : V →L[𝕜] W) (en n hn) happ
  rw [hen n hn] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (hC n hn) (norm_nonneg _))

/-! ### The integral-operator instances of Examples 2.3.2 and 2.3.4 -/

section IntegralEquations

open Set IntegralOperator

open scoped Nat

/-- Rescaling an invertible operator by a nonzero scalar keeps it invertible. -/
private theorem exists_smul_equiv {lam : 𝕜} (hlam : lam ≠ 0) (e₀ : V ≃L[𝕜] V) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = lam • (e₀ : V →L[𝕜] V) := by
  have hcancel : (e₀ : V →L[𝕜] V) * (e₀.symm : V →L[𝕜] V) = 1 := by
    ext x; exact e₀.apply_symm_apply x
  have hcancel' : (e₀.symm : V →L[𝕜] V) * (e₀ : V →L[𝕜] V) = 1 := by
    ext x; exact e₀.symm_apply_apply x
  refine ⟨ContinuousLinearEquiv.ofUnit
    ⟨lam • (e₀ : V →L[𝕜] V), lam⁻¹ • (e₀.symm : V →L[𝕜] V), ?_, ?_⟩, coe_ofUnit _⟩
  · rw [smul_mul_smul_comm, hcancel, mul_inv_cancel₀ hlam, one_smul]
  · rw [smul_mul_smul_comm, hcancel', inv_mul_cancel₀ hlam, one_smul]

variable {a b : ℝ}

/-- **Example 2.3.2 (ii)**, the concrete instance.  Let `K` be the Fredholm integral operator on
`C[a, b]` with continuous kernel `k`, so that by (2.2.8) its norm is the largest row integral
`max_x ∫ₐᵇ |k(x, y)| dy`.  If that number is smaller than `|λ|`, then `λ u - K u = f` is uniquely
solvable for every `f`, the inverse of `λI - K` is bounded by `1 / (|λ| - ‖K‖)`, and the solution
obeys `‖u‖ ≤ ‖f‖ / (|λ| - ‖K‖)`. -/
theorem example_2_3_2_integral (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) {lam : ℝ}
    (hk : (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) < |lam|) :
    ∃ e : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ),
      (e : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))
          = lam • (1 : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) - fredholm hab k ∧
        ‖(e.symm : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))‖
          ≤ 1 / (|lam| - ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) ∧
        ∀ u f : C(Icc a b, ℝ), lam • u - fredholm hab k u = f →
          ‖u‖ ≤ ‖f‖ / (|lam| - ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) := by
  have hK : ‖fredholm hab k‖ < ‖lam‖ := by
    rw [norm_fredholm hab k, Real.norm_eq_abs]; exact hk
  obtain ⟨e, he, hb⟩ := example_2_3_2 (fredholm hab k) hK
  rw [norm_fredholm hab k, Real.norm_eq_abs] at hb
  refine ⟨e, he, hb, fun u f hu => ?_⟩
  have hu' : (lam • (1 : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) - fredholm hab k) u = f := by
    simpa using hu
  have hbound := example_2_3_2_bound (fredholm hab k) hK hu'
  rwa [norm_fredholm hab k, Real.norm_eq_abs] at hbound

/-- **Example 2.3.4**, the concrete instance.  For the linear Volterra operator `L` on `C[a, b]`
with continuous kernel `k`, the iterated kernels give `‖Lᵐ‖ ≤ (‖k‖ (b - a))ᵐ / m!`, so (2.3.10)
holds for all large `m` and `λI - L` is invertible for every `λ ≠ 0`: a Volterra equation of the
second kind is uniquely solvable however large its kernel. -/
theorem example_2_3_4_volterra (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) {lam : ℝ}
    (hlam : lam ≠ 0) :
    (∀ m : ℕ, ‖volterraCLM hab k ^ m‖ ≤ (‖k‖ * (b - a)) ^ m / m !) ∧
      ∃ e : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ),
        (e : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))
          = lam • (1 : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) - volterraCLM hab k := by
  refine ⟨norm_volterraCLM_pow_le hab k, ?_⟩
  have hbound : ∀ m : ℕ, ‖(lam⁻¹ • volterraCLM hab k) ^ m‖
      ≤ (‖lam⁻¹‖ * (‖k‖ * (b - a))) ^ m / m ! := fun m => by
    calc ‖(lam⁻¹ • volterraCLM hab k) ^ m‖
        = ‖lam⁻¹‖ ^ m * ‖volterraCLM hab k ^ m‖ := by
          rw [smul_pow, norm_smul, norm_pow]
      _ ≤ ‖lam⁻¹‖ ^ m * ((‖k‖ * (b - a)) ^ m / m !) :=
          mul_le_mul_of_nonneg_left (norm_volterraCLM_pow_le hab k m) (by positivity)
      _ = (‖lam⁻¹‖ * (‖k‖ * (b - a))) ^ m / m ! := by rw [← mul_div_assoc, ← mul_pow]
  have htend : Tendsto (fun m : ℕ => ‖(lam⁻¹ • volterraCLM hab k) ^ m‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound
      (FloorSemiring.tendsto_pow_div_factorial_atTop _)
  obtain ⟨e₀, he₀⟩ := example_2_3_4 (lam⁻¹ • volterraCLM hab k) htend
  obtain ⟨e, he⟩ := exists_smul_equiv hlam e₀
  exact ⟨e, by rw [he, he₀, smul_sub, smul_inv_smul₀ hlam]⟩

end IntegralEquations

end AtkinsonHan.Chapter02
