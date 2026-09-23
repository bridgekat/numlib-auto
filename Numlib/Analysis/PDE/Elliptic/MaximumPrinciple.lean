import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Calculus.DerivativeTest
import Numlib.Analysis.PDE.Elliptic.Dirichlet

/-!
# The maximum principle for second-order elliptic equations

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.7: the
weak maximum principle by Stampacchia's truncation method — Theorem 9.27 (the Dirichlet problem
for `-Δu + u = f` on an arbitrary open set, in both cases `|Ω| < ∞` and `|Ω| = ∞`),
Corollary 9.28, Proposition 9.29 (general elliptic operators with `a₀ ≥ 0`, both in the
drift-free case the book proves and, for `N ≥ 3`, with a drift term) and Proposition 9.30 (the
Neumann problem), on the spaces
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
for `N ≥ 1`), hence `u ≤ 0`.

The general statement with a drift term `a_i` is quoted by the book from Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 8.1; that proof is carried out
here for `N ≥ 3` (`Elliptic.nonpos_of_nonpos_frontier_general`,
`Elliptic.nonneg_of_nonneg_frontier_general`), and it is a different argument. For a level
`l ≥ 0` with `sup_Γ u ≤ l` the truncation `v = (u − l)⁺` lies in `H^1_0(Ω)` — it lies in `H^1(Ω)`
by `MemSobolevMultiIndex.posPart_sub_const` (the positive part of Gilbarg–Trudinger's Lemma 7.6
after the affine shift `t ↦ t − l`, which the `C¹` chain rule does cover) and its continuous
representative vanishes on `frontier Ω`. Testing (78) with `v` and dropping the nonnegative
`∫ a₀ u v` and the nonpositive `∫ f v` gives
`α ‖∇v‖₂² ≤ ∑ᵢ ∫ a_i ∂ᵢu v ≤ (∑ᵢ ‖a_i‖_∞) ‖∇v‖₂ ‖1_E v‖₂`, the set `E = {u > l} ∩ {∇u ≠ 0}`
(`Elliptic.levelGradSet`) carrying all of `∇v`; the Sobolev inequality of Remark 20 on an
arbitrary open set together with Hölder on `E` bounds `‖1_E v‖₂ ≤ C ‖∇v‖₂ |E|^{1/N}`, so either
`∇v = 0` — and then `v = 0` and `u ≤ l` — or `|E| ≥ c` for a `c > 0` independent of `l`
(`Elliptic.exists_measure_levelGradSet_ge`). As `l` rises to the least almost-everywhere bound `M`
of `u` the sets `E` decrease to `{u = M} ∩ {∇u ≠ 0}`, a null set because the weak gradient of a
`W^{1,p}` function vanishes almost everywhere on each level set
(`SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq`, Gilbarg–Trudinger's Lemma 7.7, proved
here from the positive parts of `u − M` and `M − u`); hence `M ≤ 0`
(`Elliptic.nonpos_ae_of_forall_le_measure_levelGradSet`). The clauses (80), (80') and (81) follow
for a drift term as they do without one, from (79) applied to `u − K` and `K − u`
(`Elliptic.ge_iInf_frontier_of_nonneg`, `Elliptic.le_iSup_frontier_of_nonpos`,
`Elliptic.mem_Icc_of_frontier_general`); the drift-free forms, valid for every `N ≥ 1`, are kept
under their own names.

Remark 27 is the classical proof, for solutions `ũ ∈ C(Ω̄) ∩ C²(Ω)` on a bounded `Ω`: at an
interior maximum the gradient vanishes and the Hessian is nonpositive, so the equation gives
`ũ(x₀) ≤ f(x₀)`. For the Laplacian this is `Elliptic.le_of_classical_laplacian`
(`IsLocalMax.laplacian_nonpos`); for the general operator `-∑ ∂ⱼ(a_ij ∂ᵢũ) + ∑ b_i ∂ᵢũ + ũ`
with symmetric positive semidefinite `a_ij(x₀)` it is `Elliptic.le_of_classical`, whose
Hessian-trace step `∑ a_ij(x₀) ∂ᵢ∂ⱼũ(x₀) ≤ 0` (`Matrix.PosSemidef.sum_mul_apply_single_nonpos`)
goes through the square root of `a(x₀)` (`CFC.sqrt`) instead of the book's diagonalization.

## Not formalized here

* **Proposition 9.29, (79), (80), (81) with a drift term `a_i ≠ 0` in dimension `N ≤ 2`.** The
  statements are the ones proved in this file, with `3 ≤ N` weakened to `N ≥ 1`: under the
  hypotheses of Proposition 9.29 with `a_i ∈ L^∞(Ω)` arbitrary, `u ≥ 0` on `Γ` and `f ≥ 0` in `Ω`
  give `u ≥ 0` in `Ω`. The only step that fails is the Sobolev inequality
  `‖v‖_{L^{2^*}(Ω)} ≤ C(2, N) ‖∇v‖_{L²(Ω)}` on `W_0^{1,2}(Ω)` (Remark 20 of Chapter 9,
  `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq`), which needs `2 < N`; what the argument
  actually consumes is the Faber–Krahn-type bound
  `‖v‖_{L²(Ω)} ≤ C_N ‖∇v‖_{L²(Ω)} |{v ≠ 0}|^{1/N}` for `v ∈ H^1_0(Ω)` on an arbitrary open `Ω`,
  and only `N ≥ 3` has it in the library. For `N = 2` it would follow from the Sobolev inequality
  at the exponent `q = 3/2 < 2` applied to the extension by zero (`q^* = 6`, and Hölder on
  `{v ≠ 0}` twice), which needs `W_0^{1,2}(Ω) → W_0^{1,3/2}(Ω)` on a set of finite measure and a
  quantitative form of `SobolevEuclideanZero.exists_eLpNorm_fn_le_sum_of_measure_ne_top`
  (Remark 21, whose constant is existential there); for `N = 1` it would need the one-dimensional
  `‖v‖_∞ ≤ ‖v'‖_{L¹}` on `W_0^{1,1}` of an open subset of `ℝ`, which lives in the one-dimensional
  chapter under a different model of `ℝ^1`. Gilbarg and Trudinger state Theorem 8.1 for a bounded
  domain and treat `n = 2` by replacing `2^*` by an arbitrary `q < ∞`; the book gives no proof at
  all. Estimate: ~200 lines for `N = 2` on top of a quantitative Remark 21, and the `N = 1` case
  is a separate bridging exercise.

## References

[brezis2011functional], §9.7: Theorem 9.27, Corollary 9.28, Proposition 9.29, Proposition 9.30,
footnotes 35–39. The book's "proceed as in the proof of Theorem 8.18" refers to Theorem 8.19.
The drift term of Proposition 9.29 follows D. Gilbarg and N. Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Theorem 8.1, with Lemmas 7.6 and 7.7.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology InnerProductSpace

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

/-! ### The truncation `(u − l)⁺` and the level sets of a `W^{1,p}` function

Gilbarg–Trudinger's proof of Theorem 8.1 tests the equation with `v = (u − l)⁺` for a constant
`l ≥ 0`, a Lipschitz but not `C¹` function of `u`. The chain rule of Proposition 9.5 does not
apply to it directly; the positive part of `Numlib/Analysis/Sobolev/Calculus.lean`
(`HasWeakIteratedLineDerivOn.posPart`, the `C¹` approximations
`G_ε(s) = √((max s 0)² + ε²) − ε`) does, after the affine shift `t ↦ t − l`, which the chain rule
does cover. The same two shifts give the vanishing of the weak gradient on a level set
(Gilbarg–Trudinger, Lemma 7.7), which is what makes the set `{u > l} ∩ {∇u ≠ 0}` shrink to a null
set as `l` rises to the essential supremum of `u`. -/

section PosPartSubConst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {y : E}

/-- Subtracting a constant does not change the weak derivative along a direction: the chain rule
`HasWeakIteratedLineDerivOn.contDiff_comp'` for the `C¹` function `t ↦ t − l`, of derivative `1`. -/
theorem _root_.HasWeakIteratedLineDerivOn.sub_const {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (l : ℝ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ u x - l) w Ω μ := by
  have hd : ∀ t : ℝ, deriv (fun s : ℝ ↦ s - l) t = 1 := fun t ↦ by simp
  refine (h.contDiff_comp' (f := fun s : ℝ ↦ s - l) (contDiff_id.sub contDiff_const)
      (M := 1) fun t ↦ by rw [hd]; norm_num).congr_ae (Eventually.of_forall fun x ↦ rfl) ?_
  filter_upwards with x
  rw [hd, one_mul]

/-- Subtracting from a constant negates the weak derivative along a direction: the chain rule for
the `C¹` function `t ↦ l − t`, of derivative `−1`. -/
theorem _root_.HasWeakIteratedLineDerivOn.const_sub {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (l : ℝ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ l - u x) (fun x ↦ -w x) Ω μ := by
  have hd : ∀ t : ℝ, deriv (fun s : ℝ ↦ l - s) t = -1 := fun t ↦ by simp
  refine (h.contDiff_comp' (f := fun s : ℝ ↦ l - s) (contDiff_const.sub contDiff_id)
      (M := 1) fun t ↦ by rw [hd]; norm_num).congr_ae (Eventually.of_forall fun x ↦ rfl) ?_
  filter_upwards with x
  rw [hd, neg_one_mul]

/-- **The shifted positive part of a weakly differentiable function**: if `w` is the weak
derivative of `u` along `y` on `Ω` and `l` is a constant, then `{u > l}.indicator w` is the weak
derivative of `(u − l)⁺ = max (u − l) 0` (`HasWeakIteratedLineDerivOn.posPart` after
`HasWeakIteratedLineDerivOn.sub_const`). -/
theorem _root_.HasWeakIteratedLineDerivOn.posPart_sub_const {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (l : ℝ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ max (u x - l) 0)
      ({x | l < u x}.indicator w) Ω μ := by
  have h2 := (h.sub_const l).posPart
  have hset : {x : E | 0 < u x - l} = {x : E | l < u x} := by
    ext x; simp [sub_pos]
  rwa [hset] at h2

/-- **The weak derivative vanishes almost everywhere on every level set** (Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Lemma 7.7): `u − c` is the difference
`(u − c)⁺ − (c − u)⁺` of two positive parts, whose weak derivatives are `1_{u > c} w` and
`−1_{u < c} w`, so `w = 1_{u > c} w + 1_{u < c} w` almost everywhere and `w` vanishes where
`u = c`. -/
theorem _root_.HasWeakIteratedLineDerivOn.ae_eq_zero_of_eq_const {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (c : ℝ) :
    ∀ᵐ x ∂(μ.restrict (Ω : Set E)), u x = c → w x = 0 := by
  classical
  have h1 := h.posPart_sub_const c
  have h2 := (h.const_sub c).posPart
  have hset : {x : E | 0 < c - u x} = {x : E | u x < c} := by ext x; simp [sub_pos]
  rw [hset] at h2
  have h4 : HasWeakIteratedLineDerivOn ![y] (fun x ↦ u x - c)
      (({x : E | c < u x}.indicator w) - ({x : E | u x < c}.indicator fun x ↦ -w x)) Ω μ := by
    refine (h1.sub h2).congr_ae (Eventually.of_forall fun x ↦ ?_) (EventuallyEq.refl _ _)
    simp only [Pi.sub_apply]
    rcases le_total (u x) c with hx | hx
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have h6 : ∀ᵐ x ∂(μ.restrict (Ω : Set E)),
      w x = ({x : E | c < u x}.indicator w) x - ({x : E | u x < c}.indicator fun x ↦ -w x) x :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (by filter_upwards [(h.sub_const c).ae_eq h4] with x hx using hx)
  filter_upwards [h6] with x hx hxc
  rw [hx, Set.indicator_of_notMem (by simp [hxc]), Set.indicator_of_notMem (by simp [hxc]),
    sub_zero]

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E}

/-- **The shifted positive part of a `W^{1,p}` function lies in `W^{1,p}`**: for
`u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞` and `l ≥ 0`, `(u − l)⁺ = max (u − l) 0 ∈ W^{1,p}(Ω)`, with
`∂_i (u − l)⁺ = {u > l}.indicator (∂_i u)`. The bound `|(u − l)⁺| ≤ |u|` needs `l ≥ 0`, and is
what keeps the truncation in `L^p` on an open set of infinite measure. -/
theorem _root_.MemSobolevMultiIndex.posPart_sub_const {u : E → ℝ} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) {l : ℝ} (hl : 0 ≤ l) :
    MemSobolevMultiIndex b (fun x ↦ max (u x - l) 0) 1 p Ω μ := by
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) := hu.memLp.aestronglyMeasurable
  have hpos : MemLp (fun x ↦ max (u x - l) 0) p (μ.restrict (Ω : Set E)) :=
    hu.memLp.of_le (((continuous_id.sub continuous_const).max
        continuous_const).comp_aestronglyMeasurable hum)
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        rcases le_total (u x) l with hx | hx
        · rw [max_eq_right (by linarith), abs_zero]
          exact abs_nonneg _
        · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]
          exact (by linarith : u x - l ≤ u x).trans (le_abs_self _))
  refine ⟨hpos, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hpos.locallyIntegrableOn hp), hpos⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
    have hw' : HasWeakIteratedLineDerivOn ![b i] u w Ω μ :=
      hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    have hset : {x : E | l < u x} = {x : E | 0 < u x - l} := by ext x; simp [sub_pos]
    refine ⟨_, (hw'.posPart_sub_const l).of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm,
      hwp.of_le ?_ (Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)⟩
    rw [hset]
    exact aestronglyMeasurable_indicator_pos
      ((continuous_id.sub continuous_const).comp_aestronglyMeasurable hum)
      hwp.aestronglyMeasurable

/-- The partial derivative of an element of `W^{1,p}(Ω)` whose function is `(u − l)⁺` is
`{u > l}.indicator (∂_i u)` almost everywhere on `Ω`
(`HasWeakIteratedLineDerivOn.posPart_sub_const` and the uniqueness of the weak derivative). -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart_sub_const
    {u v : SobolevMultiIndex ℝ b 1 p Ω μ} {l : ℝ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ max (SobolevMultiIndex.fn u x - l) 0) (i : ι) :
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ)
      =ᵐ[μ.restrict (Ω : Set E)] {x | l < SobolevMultiIndex.fn u x}.indicator
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) := by
  have h1 := (SobolevMultiIndex.hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).posPart_sub_const l
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    ((h1.congr_ae hv (Filter.EventuallyEq.refl _ _)).ae_eq h2)

/-- The partial derivatives of an element of `W^{1,p}(Ω)` vanish almost everywhere on each level
set `{u = c}` (`HasWeakIteratedLineDerivOn.ae_eq_zero_of_eq_const`). -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq
    (u : SobolevMultiIndex ℝ b 1 p Ω μ) (c : ℝ) (i : ι) :
    ∀ᵐ x ∂(μ.restrict (Ω : Set E)), SobolevMultiIndex.fn u x = c →
      (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : E → ℝ) x = 0 :=
  ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).ae_eq_zero_of_eq_const c

end PosPartSubConst

/-! ### Proposition 9.29 with a drift term: Gilbarg–Trudinger's Theorem 8.1

The book proves (79) only for `a_i = 0` and cites Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 8.1, for the general case.
That proof is the one formalized here, for `N ≥ 3`: for `sup_Γ u ≤ l < sup_Ω u` the truncation
`v = (u − l)⁺` lies in `H^1_0(Ω)`, and testing the equation with it gives
`α ∫ |∇v|² ≤ ∫ ∑ a_i ∂_i u v ≤ (∑ᵢ ‖a_i‖_∞) ‖∇v‖₂ ‖1_E v‖₂`, where `E = {u > l} ∩ {∇u ≠ 0}` carries
the whole of `∇v`. The Sobolev inequality of Remark 20 on an arbitrary open set,
`‖v‖_{2^*} ≤ C ‖∇v‖₂`, and Hölder on `E` turn this into `α ≤ C' |E|^{1/N}`, so `|E| ≥ c > 0` for a
`c` independent of `l`, unless `∇v = 0`, in which case `v = 0` and `u ≤ l`. As `l` rises to the
essential supremum `M` of `u` the sets `E` decrease to `{u = M} ∩ {∇u ≠ 0}`, which is null because
the weak gradient vanishes on level sets; hence `M ≤ 0`.

The restriction `N ≥ 3` is the one the Sobolev inequality `‖v‖_{2^*} ≤ C ‖∇v‖_2` carries: see
`## Not formalized here` at the end of this file. -/

section GeneralDrift

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

open SobolevMultiIndex

/-- **The Sobolev inequality on `H^1_0(Ω)` localized to a set of small measure**, for `N ≥ 3`:
there is `C` with `‖1_s v‖_{L²(Ω)} ≤ C ‖∇v‖_{L²(Ω)} |s|^{1/N}` for every `v ∈ H^1_0(Ω)` and every
measurable `s` of finite measure. Hölder at the exponents `(2, 2^*)` on `s`
(`1/2 = 1/2^* + 1/N`), and Remark 20's `‖v‖_{2^*} ≤ C(2, N) ‖∇v‖_2` on an arbitrary open set
(`SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq`). -/
theorem exists_norm_indicator_bound (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω →
      ∀ s : Set (EuclideanSpace ℝ (Fin N)), MeasurableSet s →
      volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s ≠ ⊤ →
      (eLpNorm (s.indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * gradNorm v
          * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s).toReal ^ ((N : ℝ)⁻¹) := by
  have hN0 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 3 by norm_num) hN0
  have hd : (0 : ℝ) < (2 : ℝ)⁻¹ - (N : ℝ)⁻¹ := by norm_num at h1 ⊢; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = ((2 : ℝ)⁻¹ - (N : ℝ)⁻¹)⁻¹ :=
    ⟨Real.toNNReal _, Real.coe_toNNReal _ (by positivity)⟩
  have hqinv2 : ((q : ℝ))⁻¹ = (2 : ℝ)⁻¹ - (N : ℝ)⁻¹ := by rw [hq, inv_inv]
  have hqinv : ((q : ℝ))⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (N : ℝ)⁻¹ := by rw [hqinv2]; norm_num
  have hqN : (2 : ℝ≥0) < (N : ℝ≥0) := by
    have : (2 : ℕ) < N := by omega
    exact_mod_cast this
  have : Fact ((1 : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevEuclideanZero N 1 2 Ω,
      eLpNorm (fn (v : SobolevEuclidean N 1 2 Ω)) (q : ℝ≥0∞)
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ ENNReal.ofReal (C * gradNorm (v : SobolevEuclidean N 1 2 Ω)) :=
    ⟨(SobolevEuclidean.gnsConst N ((2 : ℝ≥0) : ℝ) : ℝ) * N, by positivity, fun v ↦ by
      simpa [mul_assoc] using
        SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq (p := (2 : ℝ≥0)) (p' := q) hqN hqinv v⟩
  refine ⟨C, hC0, fun v hvmem s hs hfin ↦ ?_⟩
  have hCv := hC ⟨v, hvmem⟩
  have hgrad : 0 ≤ C * gradNorm v := mul_nonneg hC0 (gradNorm_nonneg _)
  have hqval : (2 : ℝ) ≤ (q : ℝ) := by
    rw [hq, le_inv_comm₀ (by norm_num) hd]
    norm_num
  have h2q : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    have h : ((2 : ℝ≥0)) ≤ q := by rwa [← NNReal.coe_le_coe, NNReal.coe_ofNat]
    calc (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := by norm_num
      _ ≤ (q : ℝ≥0∞) := ENNReal.coe_le_coe.2 h
  have hexp : 1 / (2 : ℝ≥0∞).toReal - 1 / ((q : ℝ≥0∞)).toReal = (N : ℝ)⁻¹ := by
    rw [ENNReal.coe_toReal, ENNReal.toReal_ofNat, one_div, one_div, hqinv2]
    ring
  have key : eLpNorm (s.indicator (fn v)) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ENNReal.ofReal (C * gradNorm v)
        * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s) ^ ((N : ℝ)⁻¹) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    have hmeas : AEStronglyMeasurable (fn v)
        ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))).restrict s) :=
      (SobolevMultiIndex.memLp _).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))).restrict s) h2q hmeas
    rw [Measure.restrict_apply_univ, hexp] at hh
    exact hh.trans (mul_le_mul' ((eLpNorm_restrict_le _ _ _ _).trans hCv) le_rfl)
  have hfin2 : ENNReal.ofReal (C * gradNorm v)
      * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s) ^ ((N : ℝ)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin)
  refine (ENNReal.toReal_mono hfin2 key).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hgrad, ← ENNReal.toReal_rpow]

/-- The part of `Ω` where `u` exceeds `l` and the weak gradient of `u` does not vanish. -/
def levelGradSet (u : SobolevEuclidean N 1 2 Ω) (l : ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | l < fn u x} ∩ {x | ∃ i, (weakDeriv u (MultiIndexLE.single i) :
    EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0}

/-- `Elliptic.levelGradSet u l` is measurable: the superlevel set of a strongly measurable
representative of `u`, intersected with the union over `i` of the sets where `∂ᵢu` does not
vanish. -/
theorem measurableSet_levelGradSet (u : SobolevEuclidean N 1 2 Ω) (l : ℝ) :
    MeasurableSet (levelGradSet u l) := by
  refine MeasurableSet.inter (measurableSet_lt measurable_const ?_) ?_
  · exact (Lp.stronglyMeasurable (weakDeriv u 0)).measurable
  · rw [show {x | ∃ i, (weakDeriv u (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0}
      = ⋃ i : Fin N, {x | (weakDeriv u (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0} from by ext x; simp]
    exact MeasurableSet.iUnion fun i ↦
      (Lp.stronglyMeasurable (weakDeriv u (MultiIndexLE.single i))).measurable
        (measurableSet_singleton (0 : ℝ)).compl

/-- Membership in `Elliptic.levelGradSet u l`, unfolded. -/
theorem mem_levelGradSet_iff {u : SobolevEuclidean N 1 2 Ω} {l : ℝ}
    {x : EuclideanSpace ℝ (Fin N)} :
    x ∈ levelGradSet u l ↔ l < fn u x ∧ ∃ i,
      (weakDeriv u (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0 := Iff.rfl

/-- **The energy estimate of Gilbarg–Trudinger's Theorem 8.1** for the truncation
`v = (u − l)⁺ ∈ H^1_0(Ω)`, `l ≥ 0`: testing the equation with `v` and dropping the
(nonnegative) zeroth-order term and the (nonpositive) load gives
`α ‖∇v‖₂² ≤ (∑ᵢ ‖a_i‖_∞) ‖∇v‖₂ ‖1_E v‖₂`, where `E` is the part of `Ω` on which `u > l` and
`∇u ≠ 0` — the only part on which `∇v` does not vanish. -/
theorem gradNorm_sq_le_of_posPart (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0)
    {l : ℝ} (hl : 0 ≤ l) {v : SobolevEuclidean N 1 2 Ω}
    (hvmem : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ max (fn u x - l) 0) :
    α * gradNorm v ^ 2 ≤ (∑ i : Fin N, ‖a₁ i‖) * gradNorm v
      * (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
  classical
  have hEm := measurableSet_levelGradSet u l
  have hgLp : MemLp ((levelGradSet u l).indicator (fn v)) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (SobolevMultiIndex.memLp v).indicator hEm
  have hvi : ∀ i, (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        {x | l < fn u x}.indicator (weakDeriv u (MultiIndexLE.single i)) := fun i ↦
    SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart_sub_const hv i
  have hall := ae_all_iff.2 hvi
  -- the principal part
  have hP : ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v (MultiIndexLE.single j)⟫_ℝ
      = ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv v (MultiIndexLE.single i)),
        weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_mulL_eq_integral, inner_mulL_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hall] with x hx
    by_cases hxl : l < fn u x
    · rw [hx i, Set.indicator_of_mem (show x ∈ {y | l < fn u y} from hxl)]
    · rw [hx j, Set.indicator_of_notMem (show x ∉ {y | l < fn u y} from hxl), mul_zero, mul_zero]
  have hPge : α * gradNorm v ^ 2
      ≤ ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
    rw [hP, gradNorm_eq_sqrt, Real.sq_sqrt (by positivity)]
    exact sum_inner_mulL_ge Ω hA v
  -- the zeroth-order term
  have hZ : 0 ≤ ⟪mulL Ω a₀ (weakDeriv u 0), weakDeriv v 0⟫_ℝ := by
    rw [inner_mulL_eq_integral]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha₀, hv] with x hx hxv
    change 0 ≤ a₀ x * fn u x * fn v x
    rw [hxv]
    rcases le_total (fn u x) l with h | h
    · rw [max_eq_right (by linarith), mul_zero]
    · rw [max_eq_left (by linarith)]
      have : 0 ≤ fn u x := le_trans hl h
      positivity
  -- the load
  have hR : ⟪f, weakDeriv v 0⟫_ℝ ≤ 0 := by
    rw [L2.inner_eq_integral_mul]
    refine integral_nonpos_of_ae ?_
    filter_upwards [hf, hv] with x hx hxv
    change f x * fn v x ≤ 0
    rw [hxv]
    exact mul_nonpos_of_nonpos_of_nonneg hx (le_max_right _ _)
  -- the drift term
  have hgnorm : ‖hgLp.toLp ((levelGradSet u l).indicator (fn v))‖
      = (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hgLp.coeFn_toLp]
  have hDeq : ∀ i, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)), weakDeriv v 0⟫_ℝ
      = ⟪mulL Ω (a₁ i) (weakDeriv v (MultiIndexLE.single i)),
        hgLp.toLp ((levelGradSet u l).indicator (fn v))⟫_ℝ := by
    intro i
    rw [inner_mulL_eq_integral, inner_mulL_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hall, hv, hgLp.coeFn_toLp] with x hx hxv hxg
    simp only [SobolevMultiIndex.weakDeriv_zero]
    rw [hxg]
    by_cases hxl : l < fn u x
    · by_cases hxD : ∃ j, (weakDeriv u (MultiIndexLE.single j) :
          EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0
      · rw [hx i, Set.indicator_of_mem (show x ∈ {y | l < fn u y} from hxl),
          Set.indicator_of_mem (show x ∈ levelGradSet u l from ⟨hxl, hxD⟩)]
      · push Not at hxD
        rw [hx i, Set.indicator_of_mem (show x ∈ {y | l < fn u y} from hxl), hxD i,
          mul_zero, zero_mul, zero_mul]
    · have hnot : x ∉ levelGradSet u l := fun hx' ↦ hxl hx'.1
      rw [hx i, Set.indicator_of_notMem (show x ∉ {y | l < fn u y} from hxl),
        Set.indicator_of_notMem hnot, hxv,
        max_eq_right (by linarith [not_lt.1 hxl]), mul_zero, mul_zero]
  have hDbd : |∑ i : Fin N, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v 0⟫_ℝ|
      ≤ (∑ i : Fin N, ‖a₁ i‖) * gradNorm v
        * (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
    rw [← hgnorm, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [hDeq i]
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (norm_mulL_apply_le Ω _ _).trans
      (mul_le_mul_of_nonneg_left (norm_weakDeriv_single_le_gradNorm v i) (norm_nonneg _))
  -- put the pieces together
  have e := heq v hvmem
  rw [generalForm_apply_inner, load_apply_inner] at e
  have hle : -∑ i : Fin N, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)),
      weakDeriv v 0⟫_ℝ ≤ |∑ i : Fin N, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)),
      weakDeriv v 0⟫_ℝ| := neg_le_abs _
  linarith [hPge, hZ, hR, hDbd, hle]

/-- **The truncation `(u − l)⁺` lies in `H^1_0(Ω)`** when `l ≥ 0` and the continuous
representative `ũ` of `u` is at most `0` on `frontier Ω`: it lies in `H^1(Ω)` by
`MemSobolevMultiIndex.posPart_sub_const` and its continuous representative `(ũ − l)⁺` vanishes on
`frontier Ω`, so Theorem 9.17 (i) ⇒ (ii) applies. -/
theorem exists_posPart_mem_zero {u : SobolevEuclidean N 1 2 Ω}
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hcont : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0)
    {l : ℝ} (hl : 0 ≤ l) :
    ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ max (fn u x - l) 0 := by
  obtain ⟨v, hv⟩ := ((memSobolevMultiIndex u).posPart_sub_const
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hl).exists_sobolevMultiIndex
  refine ⟨v, ?_, hv⟩
  refine SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier ENNReal.ofNat_ne_top
    v (ũ := fun x ↦ max (ũ x - l) 0) ?_ ?_ fun x hx ↦ ?_
  · filter_upwards [hv, hu] with x hx hx'
    rw [hx, hx']
  · exact ((continuous_id.sub continuous_const).max continuous_const).comp_continuousOn hcont
  · exact max_eq_right (by linarith [hΓ x hx])

/-- **The key dichotomy of Gilbarg–Trudinger's Theorem 8.1**: there is a constant `c > 0`,
depending only on `α`, `‖a_i‖_∞`, `N` and the Sobolev constant, such that for every level
`l ≥ 0` either `u ≤ l` almost everywhere on `Ω`, or the set on which `u > l` and `∇u ≠ 0` has
measure at least `c`. The energy estimate `α ‖∇v‖₂² ≤ (∑ᵢ ‖a_i‖_∞) ‖∇v‖₂ ‖1_E v‖₂` for
`v = (u − l)⁺` is combined with `‖1_E v‖₂ ≤ C ‖∇v‖₂ |E|^{1/N}`; when `∇v = 0` the truncation
itself vanishes, because `v ∈ H^1_0(Ω)`. -/
theorem exists_measure_levelGradSet_ge (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hcont : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ l : ℝ, 0 ≤ l →
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l) ∨
        ENNReal.ofReal c
          ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l) := by
  have hN0 : N ≠ 0 := by omega
  have hα : 0 < α := hA.1
  obtain ⟨C, hC0, hC⟩ := exists_norm_indicator_bound (Ω := Ω) hN
  have hΛ : 0 ≤ ∑ i : Fin N, ‖a₁ i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  have hden : 0 < (∑ i : Fin N, ‖a₁ i‖) * C + 1 := by positivity
  refine ⟨(α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)) ^ (N : ℝ), Real.rpow_pos_of_pos (by positivity) _,
    fun l hl ↦ ?_⟩
  obtain ⟨v, hvmem, hv⟩ := exists_posPart_mem_zero hu hcont hΓ hl
  rcases eq_or_lt_of_le (gradNorm_nonneg v) with hG | hG
  · -- the gradient of the truncation vanishes, hence so does the truncation
    left
    have hgi : ∀ i, weakDeriv v (MultiIndexLE.single i) = 0 := fun i ↦ by
      have := norm_weakDeriv_single_le_gradNorm v i
      rw [← hG] at this
      exact norm_le_zero_iff.1 this
    have h0 : (⟨v, hvmem⟩ : SobolevEuclideanZero N 1 2 Ω) = 0 :=
      SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero hN0 ENNReal.ofNat_ne_top _ hgi
    have h0' : v = 0 := congrArg Subtype.val h0
    filter_upwards [hv, show fn (0 : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] 0 from fn_zero] with x hx hx0
    rw [h0', hx0, Pi.zero_apply] at hx
    have := le_max_left (fn u x - l) 0
    rw [← hx] at this
    linarith
  · right
    by_cases hfin : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l) = ⊤
    · rw [hfin]; exact le_top
    have key1 := gradNorm_sq_le_of_posPart hA ha₀ heq hf hl hvmem hv
    have key2 := hC v hvmem (levelGradSet u l) (measurableSet_levelGradSet u l) hfin
    have hXnn : (0 : ℝ) ≤ (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := ENNReal.toReal_nonneg
    have htnn : (0 : ℝ) ≤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
        (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹) := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have h3 : (∑ i : Fin N, ‖a₁ i‖) * gradNorm v
        * (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ ((∑ i : Fin N, ‖a₁ i‖) * C
            * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
              (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹)) * gradNorm v ^ 2 := by
      have := mul_le_mul_of_nonneg_left key2 (mul_nonneg hΛ hG.le)
      nlinarith [this]
    have h4 : α * gradNorm v ^ 2
        ≤ ((∑ i : Fin N, ‖a₁ i‖) * C
            * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
              (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹)) * gradNorm v ^ 2 := by linarith
    have h5 : α ≤ (∑ i : Fin N, ‖a₁ i‖) * C
        * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
          (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹) :=
      le_of_mul_le_mul_right h4 (pow_pos hG 2)
    have h6 : α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)
        ≤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
          (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹) := by
      rw [div_le_iff₀ hden]
      nlinarith [htnn, h5]
    have h7 : (α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)) ^ (N : ℝ)
        ≤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l)).toReal := by
      refine (Real.rpow_le_rpow (by positivity) h6 (by positivity)).trans_eq ?_
      rw [← Real.rpow_mul ENNReal.toReal_nonneg, inv_mul_cancel₀ (by positivity : (N : ℝ) ≠ 0),
        Real.rpow_one]
    calc ENNReal.ofReal ((α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)) ^ (N : ℝ))
        ≤ ENNReal.ofReal ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
            (levelGradSet u l)).toReal) := ENNReal.ofReal_le_ofReal h7
      _ = volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l) :=
          ENNReal.ofReal_toReal hfin


/-- A superlevel set `{u > t}` of an `L²` function has finite measure for `t > 0`
(Chebyshev's inequality). -/
theorem measure_lt_fn_ne_top (u : SobolevEuclidean N 1 2 Ω) {t : ℝ} (ht : 0 < t) :
    volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) {x | t < fn u x} ≠ ⊤ := by
  have hsub : {x | t < fn u x} ⊆ {x | t.toNNReal ≤ ‖fn u x‖₊} := by
    intro x hx
    have hx' : t < fn u x := hx
    have : t ≤ ‖fn u x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    simpa [← NNReal.coe_le_coe, Real.coe_toNNReal t ht.le] using this
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  exact ((SobolevMultiIndex.memLp u).meas_ge_lt_top (by norm_num) ENNReal.ofNat_ne_top
    (by simpa using ht)).ne

/-- The essential supremum of `u` on `Ω` is at most `0` once every level `l ≥ 0` either bounds
`u` almost everywhere or has `|{u > l} ∩ {∇u ≠ 0}| ≥ c` for a fixed `c > 0`: the infimum `M` of
the almost-everywhere bounds is attained, and if it were positive the sets
`{u > M − M/(n+2)} ∩ {∇u ≠ 0}` would all have measure at least `c` while decreasing to
`{u = M} ∩ {∇u ≠ 0}`, a null set because the weak gradient vanishes on level sets
(`SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq`). -/
theorem nonpos_ae_of_forall_le_measure_levelGradSet {u : SobolevEuclidean N 1 2 Ω} {c : ℝ}
    (hc0 : 0 < c)
    (hdich : ∀ l : ℝ, 0 ≤ l →
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l) ∨
        ENNReal.ofReal c
          ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l)) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ 0 := by
  classical
  have hcE : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.2 hc0
  have hmeas : ∀ t : ℝ, MeasurableSet {x | t < fn u x} := fun t ↦
    measurableSet_lt measurable_const (Lp.stronglyMeasurable (weakDeriv u 0)).measurable
  have hsubset : ∀ t : ℝ, levelGradSet u t ⊆ {x | t < fn u x} := fun _ ↦ inter_subset_left
  obtain ⟨L, hLdef⟩ : ∃ L : Set ℝ, L = {l : ℝ | 0 ≤ l ∧
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l} := ⟨_, rfl⟩
  have hLmem : ∀ l : ℝ, l ∈ L ↔ 0 ≤ l ∧
      ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l := by
    rw [hLdef]; exact fun l ↦ Iff.rfl
  -- `L` is nonempty: `u ∈ L²(Ω)`, so `|{u > n}| → 0`
  have hLne : L.Nonempty := by
    have hanti : Antitone fun n : ℕ ↦ {x | ((n : ℝ) + 1) < fn u x} := by
      intro m n hmn x hx
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hx' : (n : ℝ) + 1 < fn u x := hx
      exact show (m : ℝ) + 1 < fn u x from by linarith
    have hempty : ⋂ n : ℕ, {x | ((n : ℝ) + 1) < fn u x} = ∅ := by
      ext x
      simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (fn u x)
      exact ⟨n, fun hcon ↦ absurd (show (n : ℝ) + 1 < fn u x from hcon) (by linarith)⟩
    have htend := tendsto_measure_iInter_atTop
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      (fun n : ℕ ↦ (hmeas ((n : ℝ) + 1)).nullMeasurableSet) hanti
      ⟨0, by simpa using measure_lt_fn_ne_top u (t := ((0 : ℕ) : ℝ) + 1) (by norm_num)⟩
    rw [hempty, measure_empty] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (eventually_lt_nhds hcE)).exists
    refine ⟨(n : ℝ) + 1, (hLmem _).2 ⟨by positivity, ?_⟩⟩
    rcases hdich ((n : ℝ) + 1) (by positivity) with h | h
    · exact h
    · exact absurd (h.trans (measure_mono (hsubset _))) (by simpa using hn.not_ge)
  have hLbdd : BddBelow L := ⟨0, fun a ha ↦ ((hLmem a).1 ha).1⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = sInf L := ⟨_, rfl⟩
  have hMle : ∀ l ∈ L, M ≤ l := fun l hl ↦ hMdef ▸ csInf_le hLbdd hl
  -- the infimum is attained
  have hML : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ M := by
    have hex : ∀ k : ℕ, ∃ a ∈ L, a < M + 1 / ((k : ℝ) + 1) := fun k ↦
      exists_lt_of_csInf_lt hLne (by
        have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        rw [← hMdef]; linarith)
    choose a haL haM using hex
    have htendM : Tendsto (fun k : ℕ ↦ M + 1 / ((k : ℝ) + 1)) atTop (𝓝 M) := by
      have h0 : Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ M) atTop (𝓝 M)).add h0
    filter_upwards [ae_all_iff.2 fun k ↦ ((hLmem _).1 (haL k)).2] with x hx
    exact ge_of_tendsto htendM (Eventually.of_forall fun k ↦ (hx k).trans (haM k).le)
  -- the infimum is `0`
  refine hML.mono fun x hx ↦ hx.trans ?_
  by_contra hMpos
  push Not at hMpos
  have hlpos : ∀ n : ℕ, 0 < M - M / ((n : ℝ) + 2) := fun n ↦ by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : M / ((n : ℝ) + 2) < M := by
      rw [div_lt_iff₀ h2]; nlinarith
    linarith
  have hlt : ∀ n : ℕ, M - M / ((n : ℝ) + 2) < M := fun n ↦ by
    have : (0 : ℝ) < M / ((n : ℝ) + 2) := by positivity
    linarith
  have hmono : Monotone fun n : ℕ ↦ M - M / ((n : ℝ) + 2) := by
    intro m n hmn
    have hm : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have : M / ((n : ℝ) + 2) ≤ M / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hMpos.le (by positivity) hm
    simp only
    linarith
  have hlim : Tendsto (fun n : ℕ ↦ M - M / ((n : ℝ) + 2)) atTop (𝓝 M) := by
    have h1 : Tendsto (fun n : ℕ ↦ M / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa using h2.const_div_atTop M
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ M) atTop (𝓝 M)).sub h1
  have hge : ∀ n : ℕ, ENNReal.ofReal c ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
      (levelGradSet u (M - M / ((n : ℝ) + 2))) := fun n ↦ by
    rcases hdich _ (hlpos n).le with h | h
    · exact absurd (hMle _ ((hLmem _).2 ⟨(hlpos n).le, h⟩)) (not_le.2 (hlt n))
    · exact h
  -- the sets shrink to a null set
  have hlevel : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ i, fn u x = M → (weakDeriv u (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x = 0 :=
    ae_all_iff.2 fun i ↦ SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq u M i
  have hnull : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
      (⋂ n : ℕ, levelGradSet u (M - M / ((n : ℝ) + 2))) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hML, hlevel] with x h1 h2 hmem
    rw [mem_iInter] at hmem
    have hev : ∀ n : ℕ, M - M / ((n : ℝ) + 2) ≤ fn u x := fun n ↦ le_of_lt (hmem n).1
    obtain ⟨i, hi⟩ := (hmem 0).2
    exact hi (h2 i (le_antisymm h1 (le_of_tendsto hlim (Eventually.of_forall hev))))
  have hanti2 : Antitone fun n : ℕ ↦ levelGradSet u (M - M / ((n : ℝ) + 2)) :=
    fun m n hmn x hx ↦ ⟨lt_of_le_of_lt (hmono hmn) hx.1, hx.2⟩
  have htend2 := tendsto_measure_iInter_atTop
    (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (fun n : ℕ ↦ (measurableSet_levelGradSet u _).nullMeasurableSet) hanti2
    ⟨0, ne_top_of_le_ne_top (measure_lt_fn_ne_top u (hlpos 0)) (measure_mono (hsubset _))⟩
  rw [hnull] at htend2
  exact absurd (ge_of_tendsto htend2 (Eventually.of_forall hge)) (by simpa using hcE.ne')


/-- **Proposition 9.29, (79'), as stated — with a drift term** (Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 8.1): for `N ≥ 3`, an open
`Ω ⊆ ℝ^N`, `A` uniformly elliptic, `a₁ ∈ L^∞(Ω)^N` arbitrary, `a₀ ∈ L^∞(Ω)` with `a₀ ≥ 0`,
`f ∈ L²(Ω)`, `u ∈ H^1(Ω)` with `generalForm Ω A a₁ a₀ u φ = load Ω f φ` for all `φ ∈ H^1_0(Ω)`,
and `ũ` a representative of `u` continuous on `closure Ω`: `ũ ≤ 0` on `frontier Ω` and `f ≤ 0`
almost everywhere force `ũ ≤ 0` on `Ω`. -/
theorem nonpos_of_nonpos_frontier_general (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ 0 := by
  obtain ⟨c, hc0, hdich⟩ := exists_measure_levelGradSet_ge hN hA ha₀ heq hf hu hc hΓ
  have hae := nonpos_ae_of_forall_le_measure_levelGradSet hc0 hdich
  refine forall_le_of_ae_le_of_continuousOn (hc.mono subset_closure) ?_
  filter_upwards [hae, hu] with x hx hx'
  rw [← hx']
  exact hx

/-- **Proposition 9.29, (79), as stated — with a drift term** ([brezis2011functional]
Proposition 9.29, (79); Gilbarg and Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Theorem 8.1): for `N ≥ 3`, `A` uniformly elliptic, `a₁ ∈ L^∞(Ω)^N`, `a₀ ∈ L^∞(Ω)` with
`a₀ ≥ 0`, `f ∈ L²(Ω)` and `u ∈ H^1(Ω) ∩ C(Ω̄)` solving the equation (78), `ũ ≥ 0` on `frontier Ω`
and `f ≥ 0` almost everywhere force `ũ ≥ 0` on `Ω`. The (79') form
`Elliptic.nonpos_of_nonpos_frontier_general` applied to `-u`, `-f`. -/
theorem nonneg_of_nonneg_frontier_general (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, 0 ≤ ũ x := by
  have h := nonpos_of_nonpos_frontier_general hN hA ha₀
    (forall_generalForm_neg_eq_load_neg A a₁ a₀ _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_le_neg hf)
  intro x hx
  simpa using h x hx

/-- Subtracting an element with vanishing gradient does not change the form (41) with `a₀ = 0`:
neither the principal part nor the drift term sees the function itself. -/
theorem generalForm_zero_sub_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {u c : SobolevEuclidean N 1 2 Ω} (hc : ∀ i, weakDeriv c (MultiIndexLE.single i) = 0)
    (φ : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ 0 (u - c) φ = generalForm Ω A a₁ 0 u φ := by
  have e : ∀ i, weakDeriv (u - c) (MultiIndexLE.single i) = weakDeriv u (MultiIndexLE.single i) :=
    fun i ↦ by
      rw [show weakDeriv (u - c) (MultiIndexLE.single i)
        = weakDeriv u (MultiIndexLE.single i) - weakDeriv c (MultiIndexLE.single i) from rfl, hc i,
        sub_zero]
  rw [generalForm_apply_inner, generalForm_apply_inner]
  simp only [e, mulL_zero, zero_apply, inner_zero_left, add_zero]

/-- **Proposition 9.29, (80), as stated — with a drift term**: for `N ≥ 3`, `A` uniformly
elliptic, `a₀ = 0` and `Ω` of finite measure (the book's bounded `Ω`), `f ≥ 0` almost everywhere
and `ũ ≥ K` on `frontier Ω` force `ũ ≥ K` on `Ω` — the book's `u ≥ inf_Γ u`
([brezis2011functional] Proposition 9.29, (80)): the constant `K` lies in `H^1(Ω)` with vanishing
gradient (`Elliptic.exists_const_of_measure_ne_top`), `u − K` satisfies the same equation because
the form has no zeroth-order term (`Elliptic.generalForm_zero_sub_apply`), and (79) applies. -/
theorem ge_iInf_frontier_of_nonneg (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, K ≤ ũ x := by
  obtain ⟨cK, hcK, hc0⟩ := exists_const_of_measure_ne_top hΩ K
  have h := nonneg_of_nonneg_frontier_general hN hA (a₀ := 0)
    (by filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx; rw [hx]; exact le_rfl)
    (u := u - cK) (fun φ hφ ↦ by rw [generalForm_zero_sub_apply A a₁ hc0, heq φ hφ])
    (ũ := fun x ↦ ũ x - K) ?_ (hc.sub continuousOn_const)
    (fun x hx ↦ by linarith [hΓ x hx]) hf
  · intro x hx
    linarith [h x hx]
  · filter_upwards [fn_sub u cK, hu, hcK] with x hx hx' hx''
    rw [hx, Pi.sub_apply, hx', hx'']

/-- **Proposition 9.29, (80'), as stated — with a drift term**: for `N ≥ 3`, `A` uniformly
elliptic, `a₀ = 0` and `Ω` of finite measure, `f ≤ 0` almost everywhere and `ũ ≤ K` on
`frontier Ω` force `ũ ≤ K` on `Ω` — the book's `u ≤ sup_Γ u` ([brezis2011functional]
Proposition 9.29, the proof of (80)). -/
theorem le_iSup_frontier_of_nonpos (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have h := ge_iInf_frontier_of_nonneg hN hA hΩ
    (forall_generalForm_neg_eq_load_neg A a₁ 0 _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (K := -K) (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_ge_neg hf)
  intro x hx
  simpa using h x hx

/-- **Proposition 9.29, (81), as stated — with a drift term**: for `N ≥ 3`, `A` uniformly
elliptic, `a₀ = 0`, `f = 0` and `Ω` of finite measure, `ũ` lies on `Ω` between any lower and upper
bound of `ũ` on `frontier Ω` — the book's `inf_Γ u ≤ u ≤ sup_Γ u` ([brezis2011functional]
Proposition 9.29, (81)), from (80) and (80'). -/
theorem mem_Icc_of_frontier_general (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {u : SobolevEuclidean N 1 2 Ω}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ 0 u φ = load Ω 0 φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ∈ Icc K₁ K₂) :
    ∀ x ∈ Ω, ũ x ∈ Icc K₁ K₂ := by
  have h0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (0 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) x = 0 :=
    Lp.coeFn_zero ℝ 2 _
  intro x hx
  exact ⟨ge_iInf_frontier_of_nonneg hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).1)
      (h0.mono fun y hy ↦ hy.symm.le) x hx,
    le_iSup_frontier_of_nonpos hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).2)
      (h0.mono fun y hy ↦ hy.le) x hx⟩


end GeneralDrift

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
