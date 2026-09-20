import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Calculus.DerivativeTest
import Numlib.Analysis.PDE.Elliptic.Dirichlet

/-!
# The maximum principle for second-order elliptic equations

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.7: the
weak maximum principle by Stampacchia's truncation method — Theorem 9.27 (the Dirichlet problem
for `-Δu + u = f` on an arbitrary open set, in both cases `|Ω| < ∞` and `|Ω| = ∞`),
Corollary 9.28, Proposition 9.29 (general elliptic operators with `a₀ ≥ 0`, in the drift-free
case the book proves) and Proposition 9.30 (the Neumann problem), on the spaces
`H^1(Ω) = SobolevEuclidean N 1 2 Ω` and `H^1_0(Ω) = SobolevEuclideanZero N 1 2 Ω` and with the
forms of `Numlib/Analysis/PDE/Elliptic/Dirichlet.lean`.

## The shape of the statements

A weak solution is an element `u` of `H^1(Ω)` with `laplaceForm Ω u φ = load Ω f φ` for every
`φ` of a test space `V` (`H^1_0(Ω)` for the Dirichlet problem, all of `H^1(Ω)` for the Neumann
problem), and "`u ∈ C(Ω̄)`" is a function `ũ : ℝ^N → ℝ`, continuous on `closure Ω`, with
`SobolevMultiIndex.fn u =ᵐ[Ω] ũ`; the boundary values are the values of `ũ` on `frontier Ω`. The
book's `sup_Γ u` and `sup_Ω f` are not formed: a bound `K` with `ũ ≤ K` on `frontier Ω` and
`f ≤ K` almost everywhere on `Ω` is the hypothesis and `ũ ≤ K` on `Ω` the conclusion; lower bounds
are the same statements for `-u`, `-f`, `-K`. Almost-everywhere bounds are upgraded to every
point of the open `Ω` by continuity (`Elliptic.forall_le_of_ae_le_of_continuousOn`).

## The engine

Every proof of the section is the same three steps, and `Elliptic.le_of_forall_truncation_mem`
states them once: (1) a Stampacchia truncation `G` (`IsStampacchiaTruncation`: `C¹`,
`|G'| ≤ M`, `G' ≥ 0`, `G = 0` on `(-∞, 0]`, `G > 0` on `(0, ∞)`; the concrete
`stampacchiaTruncation` is `s ↦ ∫₀ˢ min (max t 0) 1 dt`); (2) `v = G(u − K') ∈ H^1(Ω)`
by the chain rule (Proposition 9.5, `MemSobolevMultiIndex.contDiff_comp`), which the engine
constructs itself in both cases of the proof of Theorem 9.27 — `t ↦ G(t − K') − G(−K')` plus the
constant `G(−K')` when `|Ω| < ∞`, and `t ↦ G(t − K')` directly when `K' ≥ 0`, the case `|Ω| = ∞`
forcing `K ≥ 0` (`Elliptic.nonneg_of_ae_le_of_measure_eq_top`) — and whose admissibility `v ∈ V`
is the hypothesis of the engine; (3) the equation tested with `v` gives
`∑ᵢ ∫ (∂ᵢu)² G'(u − K') + ∫ (u − f) G(u − K') = 0`, and pointwise
`0 ≤ (u − K') G(u − K') ≤ (u − f) G(u − K')` as `f ≤ K < K'`, so `(u − K') G(u − K') = 0` almost
everywhere, so `u ≤ K'`; `K' ↓ K`. Comparing with `(u − f) G(u − K')` rather than subtracting
`K' ∫ G(u − K')` avoids the integrability bookkeeping of footnote 36.

For the Dirichlet problem `v ∈ H^1_0(Ω)` comes from Theorem 9.17 (i) ⇒ (ii), valid on every open
set (`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`), the continuous
representative `G(ũ − K')` vanishing on `frontier Ω`; footnotes 35, 37 and 38 — the assumption
`u ∈ C(Ω̄)` can be dropped for `u ∈ H^1_0(Ω)` — are the `_of_mem_zero` variants, through
`SobolevMultiIndexZero.contDiff_comp_mem`; they are what chapter 10's maximum principle for the
heat equation consumes.

Proposition 9.29 replaces `∫ |∇u|²` by `∫ ∑ a_ij ∂ᵢu ∂ⱼu G'(u) ≥ α ∫ |∇u|² G'(u)` and, the form
having no `∫ uv` term, concludes from `|∇u|² G'(u) = 0` by the auxiliary `H(t) = ∫₀ᵗ √G'(s) ds`
(`stampacchiaTruncationSqrt`): `H(u) ∈ H^1_0(Ω)` has `∇H(u) = 0`, hence `H(u) = 0`
by footnote 39 (`SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero`: the extension by zero of a
`W_0^{1,p}` function with vanishing gradient is a constant `L^p` function on `ℝ^N`, hence zero,
for `N ≥ 1`), hence `u ≤ 0`. The general statement with a drift term `a_i` (Gilbarg–Trudinger,
Theorem 8.1) is quoted without proof by the book and not proved here; the clauses (80)–(81) are
proved in the drift-free case.

Remark 27 is the classical proof, for solutions `ũ ∈ C(Ω̄) ∩ C²(Ω)` on a bounded `Ω`: at an
interior maximum the gradient vanishes and the Hessian is nonpositive, so the equation gives
`ũ(x₀) ≤ f(x₀)`. For the Laplacian this is `Elliptic.le_of_classical_laplacian`
(`IsLocalMax.laplacian_nonpos`); for the general operator `-∑ ∂ⱼ(a_ij ∂ᵢũ) + ∑ b_i ∂ᵢũ + ũ`
with symmetric positive semidefinite `a_ij(x₀)` it is `Elliptic.le_of_classical`, whose
Hessian-trace step `∑ a_ij(x₀) ∂ᵢ∂ⱼũ(x₀) ≤ 0` (`Matrix.PosSemidef.sum_mul_apply_single_nonpos`)
goes through the square root of `a(x₀)` (`CFC.sqrt`) instead of the book's diagonalization.

## References

[brezis2011functional], §9.7: Theorem 9.27, Corollary 9.28, Proposition 9.29, Proposition 9.30,
footnotes 35–39. The book's "proceed as in the proof of Theorem 8.18" refers to Theorem 8.19.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

/-! ### Almost everywhere bounds of continuous functions, and the negation of the data -/

section Aux

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- A function continuous on the open set `Ω` and at most `K` almost everywhere on `Ω` is at most
`K` everywhere on `Ω`: `max ũ K` and the constant `K` are continuous on `Ω` and agree almost
everywhere (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). -/
theorem forall_le_of_ae_le_of_continuousOn {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hc : ContinuousOn ũ Ω) {K : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), ũ x ≤ K) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have e := Measure.eqOn_open_of_ae_eq (μ := volume) (f := fun x ↦ max (ũ x) K) (g := fun _ ↦ K)
    (by filter_upwards [h] with x hx; exact max_eq_right hx) Ω.isOpen
    (continuous_max.comp_continuousOn (hc.prodMk continuousOn_const)) continuousOn_const
  intro x hx
  have : max (ũ x) K = K := e hx
  rw [← this]
  exact le_max_left _ _

/-- The function of `-u` is `-fn u`, almost everywhere on `Ω`. -/
theorem _root_.SobolevMultiIndex.fn_neg (u : SobolevEuclidean N 1 2 Ω) :
    fn (-u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] -fn u :=
  Lp.coeFn_neg (weakDeriv u 0)

/-- The form of `-Δ + 1` is odd in its first argument. -/
theorem laplaceForm_neg_apply (u φ : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω (-u) φ = -laplaceForm Ω u φ := by
  rw [map_neg, neg_apply]

/-- The load of `-f` is the opposite of the load of `f`. -/
theorem load_neg_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (φ : SobolevEuclidean N 1 2 Ω) : load Ω (-f) φ = -load Ω f φ := by
  rw [load_apply_inner, load_apply_inner, inner_neg_left]

/-- The weak equation for `-u`, `-f`, from the one for `u`, `f`. -/
theorem forall_laplaceForm_neg_eq_load_neg (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ V, laplaceForm Ω u φ = load Ω f φ) :
    ∀ φ ∈ V, laplaceForm Ω (-u) φ = load Ω (-f) φ := fun φ hφ ↦ by
  rw [laplaceForm_neg_apply, load_neg_apply, heq φ hφ]

/-- `-f ≤ -K` almost everywhere when `K ≤ f` almost everywhere. -/
theorem ae_neg_le_neg {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), (-f) x ≤ -K := by
  filter_upwards [hf, Lp.coeFn_neg f] with x hx hx'
  rw [hx', Pi.neg_apply]
  linarith

/-- `-K ≤ -f` almost everywhere when `f ≤ K` almost everywhere. -/
theorem ae_neg_ge_neg {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), -K ≤ (-f) x := by
  filter_upwards [hf, Lp.coeFn_neg f] with x hx hx'
  rw [hx', Pi.neg_apply]
  linarith

end Aux

/-! ### Constants and truncations as elements of `H^1(Ω)` -/

section Engine

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **A constant is the function of an element of `H^1(Ω)` when `Ω` has finite measure**, with
vanishing weak gradient. -/
theorem exists_const_of_measure_ne_top (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (K : ℝ) :
    ∃ c : SobolevEuclidean N 1 2 Ω,
      fn c =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun _ ↦ K) ∧
      ∀ i, weakDeriv c (MultiIndexLE.single i) = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    isFiniteMeasure_restrict.2 hΩ
  have hmem : MemSobolev (fun _ : EuclideanSpace ℝ (Fin N) ↦ K) 1 2 Ω volume := by
    refine ⟨memLp_const K, fun m hm ↦ ⟨_, ContDiffOn.hasWeakIteratedFDerivOn (μ := volume)
      (Ω := Ω) (contDiffOn_const (n := 1)) (by exact_mod_cast hm), ?_⟩⟩
    rcases m with _ | m
    · rw [iteratedFDeriv_zero_eq_comp]
      exact memLp_const _
    · rw [iteratedFDeriv_succ_const]
      exact memLp_const _
  obtain ⟨c, hc⟩ := (hmem.memSobolevMultiIndex
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)).exists_sobolevMultiIndex
  refine ⟨c, hc, fun i ↦ ?_⟩
  refine Lp.ext ?_
  have h1 := ((hasWeakIteratedLineDerivOn c (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → _) i)
    ).congr_ae hc (EventuallyEq.refl _ _)
  have h2 : HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
      (fun _ : EuclideanSpace ℝ (Fin N) ↦ K) 0 Ω volume := by
    have := (ContDiffOn.hasWeakIteratedFDerivOn (μ := volume) (Ω := Ω)
      (contDiffOn_const (c := K) (n := 1)) (m := 1) le_rfl).lineDeriv
        ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
    refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
    simp [iteratedFDeriv_succ_const]
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2),
    Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx hx0
  rw [hx0]
  exact hx

/-- **The truncation `G(u − K')` is the function of an element of `H^1(Ω)`** when `Ω` has finite
measure or `0 ≤ K'` ([brezis2011functional] Theorem 9.27, cases (a) and (b) of the proof): in
the second case `t ↦ G(t − K')` vanishes at `0` and Proposition 9.5 applies directly; in the
first, it applies to `t ↦ G(t − K') − G(−K')`, and the constant `G(−K')` lies in `H^1(Ω)`. -/
theorem exists_truncation_elem {G : ℝ → ℝ} {M : ℝ} (hG : IsStampacchiaTruncation G M)
    (u : SobolevEuclidean N 1 2 Ω) {K' : ℝ}
    (h : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ ∨ 0 ≤ K') :
    ∃ v : SobolevEuclidean N 1 2 Ω,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ G (fn u x - K') := by
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (fun x ↦ G (fn u x - K') - G (-K')) 1 2 Ω volume := by
    have := (memSobolevMultiIndex u).contDiff_comp (G := fun t ↦ G (t - K') - G (-K')) one_le_two
      ((hG.contDiff_sub K').sub contDiff_const) (by simp) (M := M) fun t ↦ by
        rw [deriv_sub_const]; exact hG.abs_deriv_sub_le K' t
    exact this
  rcases h with hΩ | hK'
  · obtain ⟨v₁, hv₁⟩ := hmem.exists_sobolevMultiIndex
    obtain ⟨c, hc, -⟩ := exists_const_of_measure_ne_top hΩ (G (-K'))
    refine ⟨v₁ + c, ?_⟩
    filter_upwards [fn_add v₁ c, hv₁, hc] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    ring
  · obtain ⟨v, hv⟩ := hmem.exists_sobolevMultiIndex
    refine ⟨v, hv.trans (Eventually.of_forall fun x ↦ ?_)⟩
    simp [hG.eq_zero_of_nonpos (-K') (by linarith)]

/-- The partial derivatives of an element of `H^1(Ω)` with function `G(u − K')` are
`G'(u − K') ∂ᵢu` almost everywhere on `Ω` (the chain rule, Proposition 9.5). -/
theorem weakDeriv_single_ae_eq_of_fn_ae_eq_truncation {G : ℝ → ℝ} {M : ℝ}
    (hG : IsStampacchiaTruncation G M) {u v : SobolevEuclidean N 1 2 Ω} {K' : ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ G (fn u x - K')) (i : Fin N) :
    (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ deriv G (fn u x - K') * weakDeriv u (MultiIndexLE.single i) x := by
  have := weakDeriv_single_ae_eq_of_fn_ae_eq_comp (u := u) (v := v) (hG.contDiff_sub K')
    (hG.abs_deriv_sub_le K') hv i
  refine this.trans (Eventually.of_forall fun x ↦ ?_)
  simp only [deriv_comp_sub_const]

/-- **`f ≤ K` almost everywhere with `f ∈ L²(Ω)` forces `0 ≤ K` when `|Ω| = ∞`** (the remark
opening case (b) of the proof of [brezis2011functional] Theorem 9.27): otherwise `|f| ≥ |K| > 0`
almost everywhere and `f ∉ L²`. -/
theorem nonneg_of_ae_le_of_measure_eq_top
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) = ⊤)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) : 0 ≤ K := by
  by_contra hK
  push Not at hK
  have hne : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ 0 := by
    intro h
    rw [← Measure.restrict_apply_univ, h] at hΩ
    simp at hΩ
  have h1 : eLpNorm (fun _ ↦ K) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ eLpNorm f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    refine eLpNorm_mono_ae aestronglyMeasurable_const ?_
    filter_upwards [hf] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hK, abs_of_neg (hx.trans_lt hK)]
    linarith
  rw [eLpNorm_const K two_ne_zero hne, Measure.restrict_apply_univ, hΩ,
    ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (by simpa using hK.ne)] at h1
  exact (Lp.eLpNorm_ne_top f) (top_le_iff.1 h1)

/-- **The truncation engine of Stampacchia's method** ([brezis2011functional] §9.7, proof of
Theorem 9.27, both cases at once). Let `Ω ⊆ ℝ^N` be open, `V` a subspace of `H^1(Ω)`,
`u ∈ H^1(Ω)` and `f ∈ L²(Ω)` with `laplaceForm Ω u φ = load Ω f φ` for all `φ ∈ V`, `f ≤ K`
almost everywhere on `Ω`, and suppose that for every `K' > K` and every Stampacchia truncation
`G` the elements of `H^1(Ω)` carrying `G(u − K')` lie in `V`. Then `u ≤ K` almost everywhere on
`Ω`.

Proof: fix `K' > K`; the element `v` with function `G(u − K')` exists
(`Elliptic.exists_truncation_elem`, since `|Ω| < ∞` or `K' > K ≥ 0`, the latter forced by
`|Ω| = ∞`) and lies in `V`; testing the equation with it,
`∑ᵢ ∫ (∂ᵢu)² G'(u − K') + ∫ (u − f) G(u − K') = 0` with a nonnegative first term, so
`∫ (u − f) G(u − K') ≤ 0`; pointwise `0 ≤ (u − K') G(u − K') ≤ (u − f) G(u − K')`, so
`(u − K') G(u − K') = 0` almost everywhere and `u ≤ K'` almost everywhere; let `K' ↓ K`. -/
theorem le_of_forall_truncation_mem (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ V, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K)
    (hV : ∀ K', K < K' → ∀ (G : ℝ → ℝ) (M : ℝ), IsStampacchiaTruncation G M →
      ∀ v : SobolevEuclidean N 1 2 Ω,
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          (fun x ↦ G (fn u x - K')) → v ∈ V) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K := by
  obtain ⟨G, hG, -, -⟩ := exists_stampacchiaTruncation
  have hΩm := Ω.isOpen.measurableSet
  -- for every `K' > K`, `u ≤ K'` almost everywhere
  have key : ∀ K', K < K' →
      ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K' := by
    intro K' hK'
    have hcase : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ ∨ 0 ≤ K' := by
      by_cases hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) = ⊤
      · exact Or.inr ((nonneg_of_ae_le_of_measure_eq_top hΩ f hf).trans hK'.le)
      · exact Or.inl hΩ
    obtain ⟨v, hv⟩ := exists_truncation_elem hG u hcase
    have hvV : v ∈ V := hV K' hK' G _ hG v hv
    have hvm : AEStronglyMeasurable (fun x ↦ G (fn u x - K'))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      (memLp v).aestronglyMeasurable.congr hv
    have hum : AEStronglyMeasurable (fn u)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := (memLp u).aestronglyMeasurable
    -- the equation tested with `v`
    have e := heq v hvV
    rw [laplaceForm_apply_inner, load_apply_inner] at e
    -- the gradient term is nonnegative
    have hgrad : 0 ≤ ∑ i : Fin N, ⟪weakDeriv u (MultiIndexLE.single i),
        weakDeriv v (MultiIndexLE.single i)⟫_ℝ := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      rw [L2.inner_eq_integral_mul]
      refine integral_nonneg_of_ae ?_
      filter_upwards [weakDeriv_single_ae_eq_of_fn_ae_eq_truncation hG hv i] with x hx
      rw [hx, show weakDeriv u (MultiIndexLE.single i) x
          * (deriv G (fn u x - K') * weakDeriv u (MultiIndexLE.single i) x)
          = deriv G (fn u x - K') * (weakDeriv u (MultiIndexLE.single i) x
            * weakDeriv u (MultiIndexLE.single i) x) by ring]
      exact mul_nonneg (hG.deriv_nonneg _) (mul_self_nonneg _)
    have hv' : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        (weakDeriv v 0 : EuclideanSpace ℝ (Fin N) → ℝ) x = G (fn u x - K') := hv
    -- hence `∫ (u − f) G(u − K') ≤ 0`
    have hI : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (fn u x - f x) * G (fn u x - K') ≤ 0 := by
      have h1 : ⟪weakDeriv u 0, weakDeriv v 0⟫_ℝ - ⟪f, weakDeriv v 0⟫_ℝ
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (fn u x - f x) * G (fn u x - K') := by
        rw [← inner_sub_left, L2.inner_eq_integral_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (weakDeriv u 0) f, hv'] with x hx hx'
        rw [hx, Pi.sub_apply, hx']
        rfl
      linarith
    -- the integrand dominates the nonnegative `(u − K') G(u − K')`
    have hint : Integrable (fun x ↦ (fn u x - f x) * G (fn u x - K'))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine (L2.integrable_inner (𝕜 := ℝ) (weakDeriv u 0 - f) (weakDeriv v 0)).congr ?_
      filter_upwards [Lp.coeFn_sub (weakDeriv u 0) f, hv'] with x hx hx'
      simp only [hx, Pi.sub_apply, RCLike.inner_apply, conj_trivial, hx']
      rw [mul_comm]
      rfl
    have hle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        (fn u x - K') * G (fn u x - K') ≤ (fn u x - f x) * G (fn u x - K') := by
      filter_upwards [hf] with x hx
      exact mul_le_mul_of_nonneg_right (sub_le_sub_left (hx.trans hK'.le) _) (hG.nonneg _)
    have hint' : Integrable (fun x ↦ (fn u x - K') * G (fn u x - K'))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine hint.mono' ((hum.sub aestronglyMeasurable_const).mul hvm) ?_
      filter_upwards [hle] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hG.mul_nonneg _)]
      exact hx
    have hzero : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (fn u x - K') * G (fn u x - K') = 0 := by
      refine le_antisymm ((integral_mono_ae hint' hint hle).trans hI) ?_
      exact integral_nonneg fun x ↦ hG.mul_nonneg _
    have := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x ↦ hG.mul_nonneg _)
      hint').1 hzero
    filter_upwards [this] with x hx
    have := hG.mul_eq_zero_iff.1 hx
    linarith
  -- `K' = K + 1/(n+1)` for every `n`
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ n : ℕ, fn u x ≤ K + 1 / ((n : ℝ) + 1) :=
    ae_all_iff.2 fun n ↦ key _ (lt_add_of_pos_right K (by positivity))
  filter_upwards [hall] with x hx
  have ht : Tendsto (fun n : ℕ ↦ K + 1 / ((n : ℝ) + 1)) atTop (𝓝 K) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto ht (Eventually.of_forall hx)

end Engine

/-! ### Theorem 9.27: the maximum principle for the Dirichlet problem -/

section Dirichlet

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **Theorem 9.27 (maximum principle for the Dirichlet problem), upper bound**: for an open
`Ω ⊆ ℝ^N`, `f ∈ L²(Ω)`, `u ∈ H^1(Ω)` with `laplaceForm Ω u φ = load Ω f φ` for all
`φ ∈ H^1_0(Ω)`, and a representative `ũ` of `u` continuous on `closure Ω`: if `ũ ≤ K` on
`frontier Ω` and `f ≤ K` almost everywhere on `Ω`, then `ũ ≤ K` on `Ω`
([brezis2011functional] Theorem 9.27, the upper bound of (70), for both `|Ω| < ∞` and `|Ω| = ∞`).
The engine `Elliptic.le_of_forall_truncation_mem` with `V = H^1_0(Ω)`: `G(ũ − K')` is continuous
on `closure Ω` and vanishes on `frontier Ω`, so its class lies in `H^1_0(Ω)` by Theorem 9.17
(i) ⇒ (ii), which needs no regularity of `Ω`. -/
theorem le_of_le_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have hae := le_of_forall_truncation_mem (SobolevEuclideanZero N 1 2 Ω) heq hf
    fun K' hK' G M hG v hv ↦ ?_
  · refine forall_le_of_ae_le_of_continuousOn (hc.mono subset_closure) ?_
    filter_upwards [hae, hu] with x hx hx'
    rw [← hx']
    exact hx
  · refine SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier ENNReal.ofNat_ne_top
      v (ũ := fun x ↦ G (ũ x - K')) ?_ (hG.contDiff.continuous.comp_continuousOn
        (hc.sub continuousOn_const)) fun x hx ↦ ?_
    · filter_upwards [hv, hu] with x hx hx'
      rw [hx, hx']
    · exact hG.eq_zero_of_nonpos _ (by linarith [hΓ x hx])

/-- **Theorem 9.27, lower bound**: `K ≤ ũ` on `frontier Ω` and `K ≤ f` almost everywhere force
`K ≤ ũ` on `Ω` — the upper bound applied to `-u`, `-f`, `-K`. -/
theorem ge_of_ge_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ x ∈ Ω, K ≤ ũ x := by
  have h := le_of_le_frontier (forall_laplaceForm_neg_eq_load_neg _ heq) (ũ := -ũ)
    ((fn_neg u).trans (hu.neg)) hc.neg (K := -K) (fun x hx ↦ by simpa using hΓ x hx)
    (ae_neg_le_neg hf)
  intro x hx
  simpa using h x hx

/-- **Theorem 9.27, the upper half of (70)**: `ũ ≤ max {K₁, K₂}` on `Ω` when `ũ ≤ K₁` on
`frontier Ω` and `f ≤ K₂` almost everywhere — the book's `u ≤ max {sup_Γ u, sup_Ω f}`. -/
theorem le_max_of_isWeakSolution {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K₁)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K₂) :
    ∀ x ∈ Ω, ũ x ≤ max K₁ K₂ :=
  le_of_le_frontier heq hu hc (fun x hx ↦ (hΓ x hx).trans (le_max_left _ _))
    (hf.mono fun _ hx ↦ hx.trans (le_max_right _ _))

/-- **Theorem 9.27 without the continuity hypothesis, for `u ∈ H^1_0(Ω)`** (footnote 35 of
[brezis2011functional] §9.7): if `u ∈ H^1_0(Ω)` satisfies `laplaceForm Ω u φ = load Ω f φ` for
all `φ ∈ H^1_0(Ω)`, `f ≤ K` almost everywhere on `Ω` and `0 ≤ K`, then `fn u ≤ K` almost
everywhere on `Ω`. The boundary value `0` replaces `sup_Γ u`, which is why `K ≥ 0` is assumed:
`t ↦ G(t − K')` then vanishes at `0` and `SobolevMultiIndexZero.contDiff_comp_mem` places
`G(u − K')` in `H^1_0(Ω)`. Chapter 10's maximum principle for the heat equation consumes this
form. -/
theorem le_of_mem_zero {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K := by
  refine le_of_forall_truncation_mem (SobolevEuclideanZero N 1 2 Ω) heq hf
    fun K' hK' G M hG v hv ↦ ?_
  exact SobolevMultiIndexZero.contDiff_comp_mem ENNReal.ofNat_ne_top hu (hG.contDiff_sub K')
    (hG.eq_zero_of_nonpos _ (by linarith)) (hG.abs_deriv_sub_le K') hv

/-- **Theorem 9.27 without the continuity hypothesis, lower bound**: for `u ∈ H^1_0(Ω)`, `K ≤ 0`
and `K ≤ f` almost everywhere, `K ≤ fn u` almost everywhere on `Ω`. -/
theorem ge_of_mem_zero {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hK : K ≤ 0) (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ fn u x := by
  have h := le_of_mem_zero (neg_mem hu) (forall_laplaceForm_neg_eq_load_neg _ heq) (K := -K)
    (by linarith) (ae_neg_le_neg hf)
  filter_upwards [h, fn_neg u] with x hx hx'
  rw [hx', Pi.neg_apply] at hx
  linarith

/-- **Corollary 9.28, (73)**: under the hypotheses of `Elliptic.le_of_le_frontier`, if `ũ ≥ 0` on
`frontier Ω` and `f ≥ 0` almost everywhere on `Ω`, then `ũ ≥ 0` on `Ω`
([brezis2011functional] Corollary 9.28, first assertion). -/
theorem nonneg_of_nonneg_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, 0 ≤ ũ x :=
  ge_of_ge_frontier heq hu hc hΓ hf

/-- **Corollary 9.28, (74)**: `|ũ| ≤ max {K₁, K₂}` on `Ω` when `|ũ| ≤ K₁` on `frontier Ω` and
`|f| ≤ K₂` almost everywhere on `Ω` — the book's
`‖u‖_{L^∞(Ω)} ≤ max {‖u‖_{L^∞(Γ)}, ‖f‖_{L^∞(Ω)}}` ([brezis2011functional] Corollary 9.28). -/
theorem abs_le_max_of_isWeakSolution {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), |ũ x| ≤ K₁)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |f x| ≤ K₂) :
    ∀ x ∈ Ω, |ũ x| ≤ max K₁ K₂ := by
  intro x hx
  rw [abs_le]
  constructor
  · have := ge_of_ge_frontier heq hu hc (K := -max K₁ K₂)
      (fun y hy ↦ by linarith [(abs_le.1 (hΓ y hy)).1, le_max_left K₁ K₂])
      (hf.mono fun y hy ↦ by linarith [(abs_le.1 hy).1, le_max_right K₁ K₂]) x hx
    exact this
  · exact le_of_le_frontier heq hu hc (fun y hy ↦ (le_abs_self _).trans
      ((hΓ y hy).trans (le_max_left _ _)))
      (hf.mono fun y hy ↦ (le_abs_self _).trans (hy.trans (le_max_right _ _))) x hx

/-- **Corollary 9.28, the case `f = 0`**: `|ũ| ≤ K` on `Ω` when `|ũ| ≤ K` on `frontier Ω` —
"`‖u‖_{L^∞(Ω)} ≤ ‖u‖_{L^∞(Γ)}`" ([brezis2011functional] Corollary 9.28). -/
theorem abs_le_of_load_eq_zero {u : SobolevEuclidean N 1 2 Ω}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω 0 φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hK : 0 ≤ K)
    (hΓ : ∀ x ∈ frontier (Ω : Set _), |ũ x| ≤ K) :
    ∀ x ∈ Ω, |ũ x| ≤ K := by
  have h := abs_le_max_of_isWeakSolution heq hu hc hΓ (K₂ := K) ?_
  · simpa using h
  · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx
    rw [hx, Pi.zero_apply, abs_zero]
    exact hK

/-- **Corollary 9.28, the case `u = 0` on `Γ`**: `|ũ| ≤ K` on `Ω` when `|f| ≤ K` almost everywhere
— "`‖u‖_{L^∞(Ω)} ≤ ‖f‖_{L^∞(Ω)}`" ([brezis2011functional] Corollary 9.28). -/
theorem abs_le_of_eqOn_zero_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : EqOn ũ 0 (frontier Ω)) {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |f x| ≤ K) :
    ∀ x ∈ Ω, |ũ x| ≤ K := by
  have h := abs_le_max_of_isWeakSolution heq hu hc (K₁ := K)
    (fun x hx ↦ by rw [hΓ hx, Pi.zero_apply, abs_zero]; exact hK) hf
  simpa using h

end Dirichlet

/-! ### Proposition 9.30: the maximum principle for the Neumann problem -/

section Neumann

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **Proposition 9.30 (maximum principle for the Neumann problem), upper bound**: for an open
`Ω ⊆ ℝ^N`, `f ∈ L²(Ω)` and `u ∈ H^1(Ω)` with `laplaceForm Ω u φ = load Ω f φ` for all
`φ ∈ H^1(Ω)`, if `f ≤ K` almost everywhere on `Ω` then `fn u ≤ K` almost everywhere on `Ω`
([brezis2011functional] Proposition 9.30, the upper half of (82)): the engine with `V = ⊤`,
where the admissibility of `G(u − K')` is its membership in `H^1(Ω)`. No boundary values enter,
so no continuity of `u` is assumed. -/
theorem le_of_neumann {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K :=
  le_of_forall_truncation_mem ⊤ (fun φ _ ↦ heq φ) hf fun _ _ _ _ _ _ _ ↦ Submodule.mem_top

/-- **Proposition 9.30, lower bound**: `K ≤ f` almost everywhere forces `K ≤ fn u` almost
everywhere on `Ω`, the lower half of (82). -/
theorem ge_of_neumann {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ fn u x := by
  have h := le_of_neumann (u := -u) (f := -f)
    (fun φ ↦ forall_laplaceForm_neg_eq_load_neg ⊤ (fun φ _ ↦ heq φ) φ Submodule.mem_top)
    (ae_neg_le_neg hf)
  filter_upwards [h, fn_neg u] with x hx hx'
  rw [hx', Pi.neg_apply] at hx
  linarith

end Neumann

/-! ### Proposition 9.29: the maximum principle for general elliptic operators (no drift) -/

section General

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

open SobolevMultiIndex

/-- **The core of the proof of Proposition 9.29, (79')**: for `N ≥ 1`, a solution `u ∈ H^1(Ω)`
of the drift-free equation with `a₀ ≥ 0` and `f ≤ 0`, such that the truncations `G(u)`, for every
Stampacchia truncation `G`, lie in `H^1_0(Ω)`, satisfies `u ≤ 0` almost everywhere on `Ω`. -/
theorem nonpos_ae_of_general_zero_drift_of_forall_mem (hN : N ≠ 0)
    (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0)
    (hadm : ∀ (G : ℝ → ℝ) (M : ℝ), IsStampacchiaTruncation G M → ∀ v : SobolevEuclidean N 1 2 Ω,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ G (fn u x)) →
        v ∈ SobolevEuclideanZero N 1 2 Ω) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ 0 := by
  classical
  have hΩm := Ω.isOpen.measurableSet
  have hα : 0 < α := hA.1
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = stampacchiaTruncation := ⟨_, rfl⟩
  have hG : IsStampacchiaTruncation G 1 := hGdef ▸ isStampacchiaTruncation_stampacchiaTruncation
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℝ, H = stampacchiaTruncationSqrt := ⟨_, rfl⟩
  have hH : IsStampacchiaTruncation H 1 := hHdef ▸ isStampacchiaTruncation_stampacchiaTruncationSqrt
  have hHG : ∀ s, deriv H s ^ 2 = deriv G s := fun s ↦ by
    rw [hHdef, hGdef]; exact sq_deriv_stampacchiaTruncationSqrt s
  have hum : AEStronglyMeasurable (fn u) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (memLp u).aestronglyMeasurable
  -- the test function `v = G(u) ∈ H^1_0(Ω)`
  obtain ⟨v, hv⟩ := ((memSobolevMultiIndex u).contDiff_comp one_le_two hG.contDiff hG.zero
    hG.abs_deriv_le).exists_sobolevMultiIndex
  have hvV := hadm G 1 hG v hv
  have hv' : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (weakDeriv v 0 : EuclideanSpace ℝ (Fin N) → ℝ) x = G (fn u x) := hv
  have hvi : ∀ i, (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ deriv G (fn u x) * weakDeriv u (MultiIndexLE.single i) x := fun i ↦
    weakDeriv_single_ae_eq_of_fn_ae_eq_comp hG.contDiff hG.abs_deriv_le hv i
  -- the equation tested with `v`
  have e := heq v hvV
  rw [generalForm_apply_inner, load_apply_inner] at e
  have hmid : ∑ i : Fin N, ⟪mulL Ω ((0 : Fin N → Lp ℝ ⊤ (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N))))) i) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v 0⟫_ℝ = 0 := by
    simp [mulL_zero]
  have hthird : 0 ≤ ⟪mulL Ω a₀ (weakDeriv u 0), weakDeriv v 0⟫_ℝ := by
    rw [inner_mulL_eq_integral]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha₀, hv'] with x hx hx'
    rw [hx', mul_assoc]
    exact mul_nonneg hx (hG.mul_nonneg _)
  have hrhs : ⟪f, weakDeriv v 0⟫_ℝ ≤ 0 := by
    rw [L2.inner_eq_integral_mul]
    refine integral_nonpos_of_ae ?_
    filter_upwards [hf, hv'] with x hx hx'
    rw [hx']
    exact mul_nonpos_of_nonpos_of_nonneg hx (hG.nonneg _)
  -- the principal term dominates `α ∫ |∇u|² G'(u)`
  have hint : ∀ i j, Integrable (fun x ↦ A i j x * weakDeriv u (MultiIndexLE.single i) x
      * weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦
    integrable_mul_mul Ω _ _ _
  have hsq : ∀ i, Integrable (fun x ↦ weakDeriv u (MultiIndexLE.single i) x
      * weakDeriv u (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (L2.integrable_inner (𝕜 := ℝ) (weakDeriv u (MultiIndexLE.single i))
      (weakDeriv u (MultiIndexLE.single i))).congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  have hGm : AEStronglyMeasurable (fun x ↦ deriv G (fn u x))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (hG.contDiff.continuous_deriv le_rfl).comp_aestronglyMeasurable hum
  have hGb : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ‖deriv G (fn u x)‖ ≤ 1 := Eventually.of_forall fun x ↦ hG.abs_deriv_le _
  have hDint : Integrable (fun x ↦ (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
      * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (integrable_finsetSum _ fun i _ ↦ hsq i).mul_bdd hGm hGb
  have hprin : α * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
        * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x)
      ≤ ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv u (MultiIndexLE.single i)),
          weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
    simp only [inner_mulL_eq_integral]
    simp only [← integral_finsetSum _ fun j _ ↦ hint _ j]
    rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j,
      ← integral_const_mul]
    refine integral_mono_ae (hDint.const_mul α)
      (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j) ?_
    filter_upwards [hA.2, ae_all_iff.2 hvi] with x hx hxv
    have h := hx (WithLp.toLp 2 fun i ↦ weakDeriv u (MultiIndexLE.single i) x)
    rw [EuclideanSpace.real_norm_sq_eq] at h
    simp only [hxv]
    have hd : 0 ≤ deriv G (fn u x) := hG.deriv_nonneg _
    calc α * ((∑ i, weakDeriv u (MultiIndexLE.single i) x * weakDeriv u (MultiIndexLE.single i) x)
          * deriv G (fn u x))
        = (α * ∑ i, weakDeriv u (MultiIndexLE.single i) x * weakDeriv u (MultiIndexLE.single i) x)
          * deriv G (fn u x) := by ring
      _ ≤ (∑ i, ∑ j, A i j x * weakDeriv u (MultiIndexLE.single i) x
          * weakDeriv u (MultiIndexLE.single j) x) * deriv G (fn u x) := by
          refine mul_le_mul_of_nonneg_right ?_ hd
          simpa [sq] using h
      _ = ∑ i, ∑ j, A i j x * weakDeriv u (MultiIndexLE.single i) x
          * (deriv G (fn u x) * weakDeriv u (MultiIndexLE.single j) x) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          ring
  -- hence `∫ |∇u|² G'(u) = 0`, so `|∇u|² G'(u) = 0` almost everywhere
  have hzero : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
        * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x) = 0 := by
    have hnn : 0 ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
          * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x) :=
      integral_nonneg fun x ↦ mul_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
        (hG.deriv_nonneg _)
    have hle : α * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
          * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x) ≤ 0 := by
      linarith
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x ↦
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _) (hG.deriv_nonneg _)) hDint).1 hzero
  -- the element `h = H(u) ∈ H^1_0(Ω)` has vanishing gradient
  obtain ⟨h, hh⟩ := ((memSobolevMultiIndex u).contDiff_comp one_le_two hH.contDiff hH.zero
    hH.abs_deriv_le).exists_sobolevMultiIndex
  have hhV := hadm H 1 hH h hh
  have hhi : ∀ i, weakDeriv h (MultiIndexLE.single i) = 0 := fun i ↦ by
    refine Lp.ext ?_
    filter_upwards [weakDeriv_single_ae_eq_of_fn_ae_eq_comp hH.contDiff hH.abs_deriv_le hh i, hae,
      Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx hx' hx0
    rw [hx, hx0, Pi.zero_apply]
    have hi : weakDeriv u (MultiIndexLE.single i) x * weakDeriv u (MultiIndexLE.single i) x
        * deriv G (fn u x) = 0 := by
      have hsum : (∑ j : Fin N, weakDeriv u (MultiIndexLE.single j) x
          * weakDeriv u (MultiIndexLE.single j) x) * deriv G (fn u x) = 0 := hx'
      rw [Finset.sum_mul] at hsum
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
        mul_nonneg (mul_self_nonneg _) (hG.deriv_nonneg _)).1 hsum i (Finset.mem_univ i)
    have : (deriv H (fn u x) * weakDeriv u (MultiIndexLE.single i) x) ^ 2 = 0 := by
      rw [mul_pow, hHG]
      linear_combination hi
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have hh0 : (⟨h, hhV⟩ : SobolevEuclideanZero N 1 2 Ω) = 0 :=
    SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero hN ENNReal.ofNat_ne_top _ hhi
  have hh0' : h = 0 := congrArg Subtype.val hh0
  -- `H(u) = 0` almost everywhere, so `u ≤ 0`
  have hz : fn (0 : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] 0 := fn_zero
  filter_upwards [hh, hz] with x hx hx0
  rw [hh0', hx0, Pi.zero_apply] at hx
  by_contra hpos
  push Not at hpos
  exact (hH.pos_of_pos _ hpos).ne hx

end General

section General

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

open SobolevMultiIndex

/-- The general form is odd in its first argument. -/
theorem generalForm_neg_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u φ : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ (-u) φ = -generalForm Ω A a₁ a₀ u φ := by
  rw [map_neg, neg_apply]

/-- The weak equation for `-u`, `-f`, from the one for `u`, `f` (general form). -/
theorem forall_generalForm_neg_eq_load_neg
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ V, generalForm Ω A a₁ a₀ u φ = load Ω f φ) :
    ∀ φ ∈ V, generalForm Ω A a₁ a₀ (-u) φ = load Ω (-f) φ := fun φ hφ ↦ by
  rw [generalForm_neg_apply, load_neg_apply, heq φ hφ]

/-- **Proposition 9.29, (79'), for continuous solutions**: for `N ≥ 1`, an open `Ω ⊆ ℝ^N`,
`A` uniformly elliptic, `a₀ ∈ L^∞(Ω)` with `a₀ ≥ 0`, `f ∈ L²(Ω)`, `u ∈ H^1(Ω)` with
`generalForm Ω A 0 a₀ u φ = load Ω f φ` for all `φ ∈ H^1_0(Ω)`, and `ũ` a representative of `u`
continuous on `closure Ω`: `ũ ≤ 0` on `frontier Ω` and `f ≤ 0` almost everywhere force `ũ ≤ 0` on
`Ω` ([brezis2011functional] Proposition 9.29, the form (79') its proof establishes). The
truncations `G(ũ)` are continuous on `closure Ω` and vanish on `frontier Ω`, so their classes lie
in `H^1_0(Ω)` by Theorem 9.17 (i) ⇒ (ii), and
`Elliptic.nonpos_ae_of_general_zero_drift_of_forall_mem` applies. -/
theorem nonpos_of_nonpos_frontier_general_zero_drift (hN : N ≠ 0)
    (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ 0 := by
  have hae := nonpos_ae_of_general_zero_drift_of_forall_mem hN hA ha₀ heq hf
    fun G M hG v hv ↦ ?_
  · refine forall_le_of_ae_le_of_continuousOn (hc.mono subset_closure) ?_
    filter_upwards [hae, hu] with x hx hx'
    rw [← hx']
    exact hx
  · refine SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier ENNReal.ofNat_ne_top
      v (ũ := fun x ↦ G (ũ x)) ?_ (hG.contDiff.continuous.comp_continuousOn hc) fun x hx ↦ ?_
    · filter_upwards [hv, hu] with x hx hx'
      rw [hx, hx']
    · exact hG.eq_zero_of_nonpos _ (hΓ x hx)

/-- **Proposition 9.29, (79), in the drift-free case the book proves**: for `N ≥ 1`, an open
`Ω ⊆ ℝ^N`, `A` uniformly elliptic, `a₀ ∈ L^∞(Ω)` with `a₀ ≥ 0`, `f ∈ L²(Ω)`, `u ∈ H^1(Ω)` with
`generalForm Ω A 0 a₀ u φ = load Ω f φ` for all `φ ∈ H^1_0(Ω)`, and `ũ` a representative of `u`
continuous on `closure Ω`: if `ũ ≥ 0` on `frontier Ω` and `f ≥ 0` almost everywhere then `ũ ≥ 0`
on `Ω` ([brezis2011functional] Proposition 9.29, (79), with `a_i = 0`; the general drift term is
quoted from Gilbarg–Trudinger, Theorem 8.1, and not proved here). The (79') form
`Elliptic.nonpos_of_nonpos_frontier_general_zero_drift` applied to `-u`, `-f`. -/
theorem nonneg_of_nonneg_frontier_general_zero_drift (hN : N ≠ 0)
    (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, 0 ≤ ũ x := by
  have h := nonpos_of_nonpos_frontier_general_zero_drift hN hA ha₀
    (forall_generalForm_neg_eq_load_neg A 0 a₀ _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_le_neg hf)
  intro x hx
  simpa using h x hx

/-- **Proposition 9.29, (79'), for `u ∈ H^1_0(Ω)`** (footnote 38 of [brezis2011functional]
§9.7): without a continuous representative, `f ≤ 0` almost everywhere forces `fn u ≤ 0` almost
everywhere on `Ω`; the truncations `G(u)` lie in `H^1_0(Ω)` by
`SobolevMultiIndexZero.contDiff_comp_mem`. -/
theorem nonpos_of_mem_zero_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ 0 :=
  nonpos_ae_of_general_zero_drift_of_forall_mem hN hA ha₀ heq hf fun _ _ hG _ hv ↦
    SobolevMultiIndexZero.contDiff_comp_mem ENNReal.ofNat_ne_top hu hG.contDiff hG.zero
      hG.abs_deriv_le hv

/-- **Proposition 9.29, (79), for `u ∈ H^1_0(Ω)`** (footnote 38 of [brezis2011functional]
§9.7): `f ≥ 0` almost everywhere forces `fn u ≥ 0` almost everywhere on `Ω`. This is the
drift-free instance of Remark 23's second clause: with `f = 0` it gives `u ≥ 0` and `u ≤ 0`, so
the homogeneous kernel of `generalForm Ω A 0 a₀` on `H^1_0(Ω)` is trivial. -/
theorem nonneg_of_mem_zero_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ fn u x := by
  have h := nonpos_of_mem_zero_general_zero_drift hN hA ha₀ (neg_mem hu)
    (forall_generalForm_neg_eq_load_neg A 0 a₀ _ heq) (by simpa using ae_neg_le_neg hf)
  filter_upwards [h, fn_neg u] with x hx hx'
  rw [hx', Pi.neg_apply] at hx
  linarith

/-- Subtracting an element with vanishing gradient does not change the form (41) with
`a₁ = 0`, `a₀ = 0`. -/
theorem generalForm_zero_zero_sub_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {u c : SobolevEuclidean N 1 2 Ω} (hc : ∀ i, weakDeriv c (MultiIndexLE.single i) = 0)
    (φ : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A 0 0 (u - c) φ = generalForm Ω A 0 0 u φ := by
  have e : ∀ i, weakDeriv (u - c) (MultiIndexLE.single i) = weakDeriv u (MultiIndexLE.single i) :=
    fun i ↦ by
      rw [show weakDeriv (u - c) (MultiIndexLE.single i)
        = weakDeriv u (MultiIndexLE.single i) - weakDeriv c (MultiIndexLE.single i) from rfl, hc i,
        sub_zero]
  rw [generalForm_apply_inner, generalForm_apply_inner]
  simp only [e, Pi.zero_apply, mulL_zero, zero_apply, inner_zero_left, Finset.sum_const_zero,
    add_zero]

/-- **Proposition 9.29, (80), drift-free case**: for `N ≥ 1`, `A` uniformly elliptic, `a₀ = 0`
and `Ω` of finite measure (the book's bounded `Ω`), `f ≥ 0` almost everywhere and `ũ ≥ K` on
`frontier Ω` force `ũ ≥ K` on `Ω` — the book's `u ≥ inf_Γ u` ([brezis2011functional]
Proposition 9.29, (80)): the constant `K` lies in `H^1(Ω)` with zero gradient
(`Elliptic.exists_const_of_measure_ne_top`), `u − K` satisfies the same equation because the form
has no zeroth-order term (`Elliptic.generalForm_zero_zero_sub_apply`), and (79) applies to it. -/
theorem ge_of_ge_frontier_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, K ≤ ũ x := by
  obtain ⟨c, hcK, hc0⟩ := exists_const_of_measure_ne_top hΩ K
  have h := nonneg_of_nonneg_frontier_general_zero_drift hN hA (a₀ := 0)
    (by filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx; rw [hx]; exact le_rfl)
    (u := u - c) (fun φ hφ ↦ by rw [generalForm_zero_zero_sub_apply A hc0, heq φ hφ])
    (ũ := fun x ↦ ũ x - K) ?_ (hc.sub continuousOn_const)
    (fun x hx ↦ by linarith [hΓ x hx]) hf
  · intro x hx
    linarith [h x hx]
  · filter_upwards [fn_sub u c, hu, hcK] with x hx hx' hx''
    rw [hx, Pi.sub_apply, hx', hx'']

/-- **Proposition 9.29, (80'), drift-free case**: for `N ≥ 1`, `A` uniformly elliptic, `a₀ = 0`
and `Ω` of finite measure, `f ≤ 0` almost everywhere and `ũ ≤ K` on `frontier Ω` force `ũ ≤ K` on
`Ω` — the book's `u ≤ sup_Γ u` ([brezis2011functional] Proposition 9.29, the proof of (80)). -/
theorem le_of_le_frontier_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have h := ge_of_ge_frontier_general_zero_drift hN hA hΩ
    (forall_generalForm_neg_eq_load_neg A 0 0 _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (K := -K) (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_ge_neg hf)
  intro x hx
  simpa using h x hx

/-- **Proposition 9.29, (81), drift-free case**: for `N ≥ 1`, `A` uniformly elliptic, `a₀ = 0`,
`f = 0` and `Ω` of finite measure, `ũ` lies on `Ω` between any lower and upper bound of `ũ` on
`frontier Ω` — the book's `inf_Γ u ≤ u ≤ sup_Γ u` ([brezis2011functional] Proposition 9.29,
(81)). -/
theorem mem_Icc_of_frontier_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {u : SobolevEuclidean N 1 2 Ω}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 0 u φ = load Ω 0 φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ∈ Icc K₁ K₂) :
    ∀ x ∈ Ω, ũ x ∈ Icc K₁ K₂ := by
  have h0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (0 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) x = 0 :=
    Lp.coeFn_zero ℝ 2 _
  intro x hx
  exact ⟨ge_of_ge_frontier_general_zero_drift hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).1)
      (h0.mono fun y hy ↦ hy.symm.le) x hx,
    le_of_le_frontier_general_zero_drift hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).2)
      (h0.mono fun y hy ↦ hy.le) x hx⟩

end General

/-! ### Remark 27: the classical maximum principle for the Laplacian -/

section Classical

open Laplacian

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Remark 27, the classical proof of Theorem 9.27 for the Laplacian**: for a bounded open
`Ω ⊆ ℝ^N`, a classical solution `ũ` of `-Δũ + ũ = f` on `Ω` — continuous on `closure Ω` and
`C²` on `Ω` — with `ũ ≤ K` on `frontier Ω` and `f ≤ K` on `Ω` satisfies `ũ ≤ K` on `Ω`
([brezis2011functional] Chapter 9, Remark 27). The maximum of `ũ` on the compact `closure Ω` is
attained at some `x₀`; if `x₀ ∈ frontier Ω` there is nothing to prove, and if `x₀ ∈ Ω` then
`Δũ(x₀) ≤ 0` (`IsLocalMax.laplacian_nonpos`), so `ũ(x₀) = f(x₀) + Δũ(x₀) ≤ f(x₀) ≤ K`. -/
theorem le_of_classical_laplacian (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {ũ f : EuclideanSpace ℝ (Fin N) → ℝ} (hc : ContinuousOn ũ (closure Ω))
    (hu : ContDiffOn ℝ 2 ũ Ω) (heq : ∀ x ∈ Ω, -Δ ũ x + ũ x = f x) {K : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))), ũ x ≤ K)
    (hf : ∀ x ∈ Ω, f x ≤ K) : ∀ x ∈ Ω, ũ x ≤ K := by
  intro x hx
  obtain ⟨x₀, hx₀, hmax⟩ := hΩ.isCompact_closure.exists_isMaxOn ⟨x, subset_closure hx⟩ hc
  refine (hmax (subset_closure hx)).trans ?_
  rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hx₀
  rcases hx₀ with hx₀ | hx₀
  · have hloc : IsLocalMax ũ x₀ :=
      hmax.isLocalMax (mem_of_superset (Ω.isOpen.mem_nhds hx₀) subset_closure)
    have hΔ := hloc.laplacian_nonpos (hu.contDiffAt (Ω.isOpen.mem_nhds hx₀))
    have := heq x₀ hx₀
    linarith [hf x₀ hx₀]
  · exact hΓ x₀ hx₀

end Classical

/-! ### Remark 27: the classical maximum principle for a general elliptic operator -/

section ClassicalGeneral

open scoped MatrixOrder ComplexOrder

/-- **The trace of a positive semidefinite matrix against a nonpositive bilinear form is
nonpositive**: if `A` is positive semidefinite and `D` is a bilinear form on `ℝ^N` with
`D v v ≤ 0` for every `v`, then `∑ᵢⱼ A_ij D(e_i, e_j) ≤ 0`. With `A = S S` for the positive
semidefinite square root `S` (`CFC.sqrt`), symmetric, the sum is `∑ₖ D(S e_k, S e_k)`. -/
theorem _root_.Matrix.PosSemidef.sum_mul_apply_single_nonpos {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hD : ∀ v, D v v ≤ 0) :
    ∑ i, ∑ j, A i j * D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ 0 := by
  obtain ⟨S, hS⟩ : ∃ S, S = CFC.sqrt A := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact CFC.sqrt_nonneg A
  have hSS : S * S = A := by rw [hS]; exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hSsymm : ∀ i j, S i j = S j i := fun i j ↦ by
    have h := (Matrix.nonneg_iff_posSemidef.1 hS0).1
    have := congrFun (congrFun h j) i
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w : Fin N → EuclideanSpace ℝ (Fin N),
      ∀ k, w k = ∑ i, S k i • EuclideanSpace.single i (1 : ℝ) := ⟨_, fun _ ↦ rfl⟩
  have key : ∀ k, D (w k) (w k) = ∑ i, ∑ j, S k i * S k j
      * D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun k ↦ by
    simp only [hw, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  calc ∑ i, ∑ j, A i j * D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      = ∑ k, D (w k) (w k) := by
        simp only [key, ← hSS, Matrix.mul_apply, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hSsymm i k]
    _ ≤ 0 := Finset.sum_nonpos fun k _ ↦ hD (w k)

/-- A symmetric matrix of coefficients `a_ij(x)` whose quadratic form is nonnegative is positive
semidefinite. -/
theorem _root_.Matrix.posSemidef_of_of_symm_of_nonneg {N : ℕ} {a : Fin N → Fin N → ℝ}
    (hsymm : ∀ i j, a i j = a j i)
    (hnn : ∀ ξ : EuclideanSpace ℝ (Fin N), 0 ≤ ∑ i, ∑ j, a i j * ξ i * ξ j) :
    (Matrix.of a).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun i j ↦ ?_)
    fun x ↦ ?_
  · simp [hsymm i j]
  · have h := hnn (WithLp.toLp 2 x)
    simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply, Finset.mul_sum]
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Remark 27, the classical maximum principle for a general second-order elliptic operator**
([brezis2011functional] Chapter 9, Remark 27): for a bounded open `Ω ⊆ ℝ^N`, a classical
solution `ũ` of `-∑ᵢⱼ ∂ⱼ(a_ij ∂ᵢũ) + ∑ᵢ b_i ∂ᵢũ + ũ = f` on `Ω` — continuous on `closure Ω` and
`C²` on `Ω`, with `a_ij` differentiable on `Ω`, symmetric and with nonnegative quadratic form
(the ellipticity condition, of which only `∑ a_ij(x) ξ_i ξ_j ≥ 0` is used), and arbitrary `b_i`
— with `ũ ≤ K` on `frontier Ω` and `f ≤ K` on `Ω` satisfies `ũ ≤ K` on `Ω`. The Laplacian is the
case `a_ij = δ_ij`, `b = 0` (`Elliptic.le_of_classical_laplacian`).

Proof: the maximum of `ũ` on the compact `closure Ω` is attained at some `x₀`; if
`x₀ ∈ frontier Ω` there is nothing to prove. If `x₀ ∈ Ω` then `∇ũ(x₀) = 0`
(`IsLocalMax.fderiv_eq_zero`) and the Hessian is nonpositive
(`IsLocalMax.fderiv_fderiv_apply_self_nonpos`), so by the product rule
`∂ⱼ(a_ij ∂ᵢũ)(x₀) = a_ij(x₀) ∂ᵢ∂ⱼũ(x₀)` and the first-order term vanishes; the book's
"`∑ a_ij(x₀) ∂ᵢ∂ⱼũ(x₀) ≤ 0` by a change of coordinates diagonalizing `a_ij(x₀)`" is
`Matrix.PosSemidef.sum_mul_apply_single_nonpos` (through the square root of `a(x₀)` rather than
its diagonalization), whence `ũ(x₀) = f(x₀) + ∑ a_ij(x₀) ∂ᵢ∂ⱼũ(x₀) ≤ f(x₀) ≤ K`. -/
theorem le_of_classical (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {ũ f : EuclideanSpace ℝ (Fin N) → ℝ} (hc : ContinuousOn ũ (closure Ω))
    (hu : ContDiffOn ℝ 2 ũ Ω) {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (ha : ∀ i j, DifferentiableOn ℝ (a i j) Ω) (hsymm : ∀ i j, a i j = a j i)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin N), 0 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (heq : ∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ ũ y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i, b i x * fderiv ℝ ũ x (EuclideanSpace.single i 1)) + ũ x = f x)
    {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))), ũ x ≤ K)
    (hf : ∀ x ∈ Ω, f x ≤ K) : ∀ x ∈ Ω, ũ x ≤ K := by
  intro x hx
  obtain ⟨x₀, hx₀, hmax⟩ := hΩ.isCompact_closure.exists_isMaxOn ⟨x, subset_closure hx⟩ hc
  refine (hmax (subset_closure hx)).trans ?_
  rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hx₀
  rcases hx₀ with hx₀ | hx₀
  · have hnhds := Ω.isOpen.mem_nhds hx₀
    have hloc : IsLocalMax ũ x₀ := hmax.isLocalMax (mem_of_superset hnhds subset_closure)
    have hu2 : ContDiffAt ℝ 2 ũ x₀ := hu.contDiffAt hnhds
    have hgrad : fderiv ℝ ũ x₀ = 0 := hloc.fderiv_eq_zero
    have hD : ∀ v, (fderiv ℝ (fderiv ℝ ũ) x₀).flip v v ≤ 0 := fun v ↦
      hloc.fderiv_fderiv_apply_self_nonpos hu2 v
    -- the product rule at the critical point `x₀`
    have hprod : ∀ i j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ ũ y (EuclideanSpace.single i 1)) x₀
          (EuclideanSpace.single j 1)
        = a i j x₀ * (fderiv ℝ (fderiv ℝ ũ) x₀).flip (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) := by
      intro i j
      have hai : DifferentiableAt ℝ (a i j) x₀ := (ha i j).differentiableAt hnhds
      have hd2 : DifferentiableAt ℝ (fderiv ℝ ũ) x₀ :=
        (hu2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      have hg : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ũ y (EuclideanSpace.single i 1)) x₀ :=
        hd2.clm_apply (differentiableAt_const _)
      rw [fderiv_fun_mul hai hg, fderiv_clm_apply hd2 (differentiableAt_const _)]
      simp [hgrad]
    have hsum := (Matrix.posSemidef_of_of_symm_of_nonneg (fun i j ↦ congrFun (hsymm i j) x₀)
      (hell x₀ hx₀)).sum_mul_apply_single_nonpos _ hD
    simp only [Matrix.of_apply] at hsum
    have h := heq x₀ hx₀
    simp only [hprod, hgrad, zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at h
    linarith [hf x₀ hx₀]
  · exact hΓ x₀ hx₀

end ClassicalGeneral

end Elliptic
