# Surface plan: Atkinson–Han — §2.3–2.5, §3.3–3.7

Source: `theoretical-numerical-analysis-atkinson-han.md` (3rd ed.), §2.3 (l. 3309–3905), §2.4 (3905–4233),
§2.5 (4233–4551), §3.3 (6539–6977), §3.4 (6977–7367), §3.5 (7367–7619, black boxes only), §3.6 (7619–7749),
§3.7 (7749–8077). Backbone references are to `plans/backbone.md` (§1, §2.1.1–2.1.7, §2.2, §5.1, §8.3).

Conventions used below.
* Scalars: the book's `𝕂 ∈ {ℝ, ℂ}` becomes `[RCLike 𝕜]`; "real" hypotheses stated by the book (all of §3.4, Def 2.5.4/Thm 2.5.5,
  Def 3.3.6/Thm 3.3.7, strictly normed spaces) are kept as `ℝ`. Where the book says "real or complex" and the statement
  involves convexity of *sets* (§3.3), Lean needs `Module ℝ V`; we state those over `[NormedSpace ℝ V]` (a complex space
  gets this via `NormedSpace.complexToReal`), and add `[NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]` only where a `𝕜`-subspace and
  a real-convex set occur together (Thm 3.3.15). Verified: `Convex ℝ K` does *not* elaborate under bare `[NormedSpace 𝕜 V]`.
* Inner products: the book's `(u, v)` is linear in the first slot; Mathlib's `⟪u, v⟫` is linear in the second, so
  book `(v, u)` = Mathlib `inner 𝕜 u v`. All surface statements are written in Mathlib's convention with this swap.
* Operators: `𝓛(V, W)` = `V →L[𝕜] W`; "bijection with bounded inverse" = `∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L`;
  `V'` = `StrongDual 𝕜 V`; `Vᗮ` = `Submodule.orthogonal`.
* Naming: `AtkinsonHan.Ch02.thm_2_3_1`, `cor_2_3_3`, `lem_3_4_1`, `prop_3_6_9_a`, `example_3_6_7`, `exercise_3_6_7`,
  `eq_2_3_13` (numbered inequalities); book numbers appear only in the surface, per backbone §1.4.
* "✓" marks statements type-checked (with `sorry`) in `ScratchCh2.lean` / `ScratchCh3.lean` in this directory
  (`lake env lean`, Lean `v4.34.0-rc2`); a few are proved outright there (Thm 2.4.4, 2.5.2, Cor 2.5.6, Thm 2.5.8, Prop 3.6.9(c)).

Proposed files (`Surface/AtkinsonHan/…`, importing only `Numlib`):

| File | Book | Content |
|---|---|---|
| `Ch02/GeometricSeries.lean` | §2.3 | Thm 2.3.1, (2.3.5), Ex 2.3.2 (abstract), Cor 2.3.3, Ex 2.3.4 (abstract), Thm 2.3.5, (2.3.16) |
| `Ch02/Operators.lean` | §2.4 | Thm 2.4.1, Thm 2.4.3, `cond`, (2.4.1), Thm 2.4.4, Thm 2.4.5, quadrature (2.4.3)–(2.4.4), Exer 2.4.3 |
| `Ch02/Functionals.lean` | §2.5 | Thm 2.5.2, Def 2.5.4, Thm 2.5.5, Cor 2.5.6–2.5.7, Thm 2.5.8 |
| `Ch03/BestApprox.lean` | §3.3 | defs, Ex 3.3.5, Thm 3.3.7, Thm 3.3.13, Thm 3.3.15–3.3.16, Ex 3.3.17, Thm 3.3.18, strictly normed, Thm 3.3.21, Exer 3.3.8–3.3.9 |
| `Ch03/InnerProduct.lean` | §3.4 (+§3.5 refs) | Lem 3.4.1, Cor 3.4.2, Thm 3.4.3, `projConvex`, Prop 3.4.4, Thm 3.4.5–3.4.7, (3.4.6), expansion |
| `Ch03/Projections.lean` | §3.6 | Def 3.6.1, Prop 3.6.2, Def 3.6.3, orthogonal projection operators, Ex 3.6.7, Prop 3.6.9, Exer 3.6.1/3.6.7 |
| `Ch03/UniformBounds.lean` | §3.7 | Lebesgue-lemma forms of (3.7.11)/(3.7.14)/(3.7.21), non-convergence lemma; the rest recorded as docstring stubs |

Status counts (66 blocks in §Results, by primary status): direct 31 · needs-equivalence 6 · GAP 7 · surface-only 5 · out-of-scope 17.

---

## Book-specific definitions

Each entry: book formulation → proposed surface definition → Mathlib/backbone counterpart → equivalence lemma.

1. **Bounded inverse / bijection with `M⁻¹ ∈ 𝓛(W,V)`** (used throughout §2.3–2.4).
   Surface: no new def; conclusions are phrased as `∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = M`. Mathlib: `ContinuousLinearEquiv`,
   `ContinuousLinearEquiv.ofBijective`, `ContinuousLinearMap.isUnit_iff_bijective` (V = W), `ContinuousLinearEquiv.unitsEquiv`.
   Equivalence: `isUnit_iff_exists_continuousLinearEquiv (L : V →L[𝕜] V) : IsUnit L ↔ ∃ e : V ≃L[𝕜] V, ↑e = L` (from
   `ContinuousLinearEquiv.unitsEquiv`), so ring-level backbone results (2.1.1, 2.1.2) transfer.

2. **Condition number** `cond(L) ≡ ‖L⁻¹‖‖L‖` (§2.4.2, for `L : V → W`).
   Surface ✓: `noncomputable def cond (L : V ≃L[𝕜] W) : ℝ := ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W)‖`.
   Backbone: 2.1.2 `NormedRing.condNumber (a : R) := ‖a‖ * ‖Ring.inverse a‖` (single space) and
   `ContinuousLinearEquiv.condNumber_eq`. Equivalence ✓: `cond_eq_condNumber (L : V ≃L[𝕜] V) : cond L = NormedRing.condNumber (L : V →L[𝕜] V)`
   (`Ring.inverse` of a unit = `↑L.symm`; `mul_comm`).

3. **Dual space, linear functional** (§2.5): `V' = 𝓛(V, 𝕂)` (bounded functionals only).
   Surface: `abbrev Dual' (V) := StrongDual 𝕜 V` or just use `StrongDual 𝕜 V`. Mathlib: `StrongDual`, completeness
   instance `ContinuousLinearMap.completeSpace`. No equivalence needed.

4. **Sublinear functional** (Def 2.5.4, real vector space `V`, no topology).
   Surface ✓: `def IsSublinear (p : E → ℝ) : Prop := (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ (α : ℝ) v, 0 ≤ α → p (α • v) = α * p v`.
   Mathlib: hypotheses `N_hom : ∀ c > 0, ∀ x, N (c • x) = c * N x`, `N_add` of `exists_extension_of_le_sublinear`.
   Equivalence: `isSublinear_iff : IsSublinear p ↔ (∀ x y, p (x + y) ≤ p x + p y) ∧ ∀ c > 0, ∀ x, p (c • x) = c * p x`
   (⇐: `p 0 = 0` from `p 0 = p (2 • 0) = 2 * p 0`).

5. **Convex set / convex and strictly convex function** (Def 3.3.1–3.3.2), **convex combination** (3.3.1).
   Surface: none; use `Convex ℝ K`, `ConvexOn ℝ K f`, `StrictConvexOn ℝ K f`, `Convex.sum_mem`. Book's Def 3.3.1 quantifies
   `λ ∈ (0,1)`, Mathlib `[0,1]`: trivially equivalent (`convex_iff_openSegment_subset`); no lemma needed.

6. **Closed / weakly closed set; (weakly) sequentially l.s.c.** (Def 3.3.3–3.3.4).
   Surface: `IsClosed K`/`IsSeqClosed K` (equal in metric spaces: `isSeqClosed_iff_isClosed`); l.s.c. as
   `LowerSemicontinuousOn f K` (sequential = topological in metric spaces). Weak notions: define only the sequential
   form used in Ex 3.3.5: `WeakSeqTendsto (v : ℕ → V) (u : V) := ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))`
   (Mathlib `WeakSpace` gives the topological version; `tendsto_iff_forall_dual_apply_tendsto` is only stated for the WOT).
   No backbone counterpart (reflexivity/Mazur are out of scope).

7. **Separated / strictly separated sets** (Def 3.3.6, real normed `V`).
   Surface: `AreSeparated A B := ∃ (ℓ : StrongDual ℝ V) (α : ℝ), ℓ ≠ 0 ∧ (∀ u ∈ A, ℓ u ≤ α) ∧ ∀ v ∈ B, α ≤ ℓ v`; strict with `<`.
   Mathlib counterpart: conclusion shape of `geometric_hahn_banach_compact_closed` (`∃ f u v, (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b`).
   Equivalence lemma: `areStrictlySeparated_iff : (∃ ℓ ≠ 0, ∃ α, …<…) ↔ ∃ f u v, …` (take `α = (u+v)/2`; `f ≠ 0` from nonemptiness of `A`).

8. **Coercive functional over `K`** (Def 3.3.9): `f(v) → ∞ as ‖v‖ → ∞, v ∈ K`.
   Surface: `IsCoerciveFunctionalOn (f : V → ℝ) (K : Set V) : Prop := ∀ M : ℝ, ∃ R, ∀ v ∈ K, R ≤ ‖v‖ → M ≤ f v`
   (equivalently `Tendsto (fun v : K => f v) (comap (‖·‖) atTop) atTop`). No Mathlib/backbone counterpart.
   **Name clash warning**: backbone §2.1.4 uses `LinearMap.IsCoercive` for `re⟪Ax,x⟫ ≥ c‖x‖²` (AH's "strongly monotone"); the surface
   must not reuse `IsCoercive` for Def 3.3.9.

9. **Finite-dimensional subset** (after Thm 3.3.13): subset of a finite-dimensional subspace.
   Surface: hypothesis pair `(S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (hKS : K ⊆ S)`; no def.

10. **Best approximation** (3.3.3): `û ∈ K`, `‖u − û‖ = inf_{v∈K} ‖u − v‖`.
    Backbone 5.1.1: `IsBestApprox (K : Set V) (u v : V) : Prop := v ∈ K ∧ ∀ w ∈ K, ‖u − v‖ ≤ ‖u − w‖`.
    Equivalence ✓ (statement): `isBestApprox_iff_norm_eq_iInf (K) (u v) : IsBestApprox K u v ↔ v ∈ K ∧ ‖u - v‖ = ⨅ w : K, ‖u - w‖`
    (proof: `ciInf_le` with lower bound 0, `le_ciInf`). Also `Metric.infDist_eq_iInf` links to `Metric.infDist` used in 5.1.1.

11. **Strictly normed space** (§3.3.4): `‖u+v‖ = ‖u‖+‖v‖ ∧ u ≠ 0 ⇒ v = λu, λ ≥ 0`.
    Surface ✓: `def IsStrictlyNormed (V) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
      ∀ u v : V, ‖u + v‖ = ‖u‖ + ‖v‖ → u ≠ 0 → ∃ lam : ℝ, 0 ≤ lam ∧ v = lam • u`.
    Mathlib: `StrictConvexSpace ℝ V`. Equivalence ✓ (statement): `isStrictlyNormed_iff_strictConvexSpace : IsStrictlyNormed V ↔ StrictConvexSpace ℝ V`.
    Proof: ⇐ `sameRay_iff_norm_add` + `SameRay.exists_nonneg_left`; ⇒ `StrictConvexSpace.of_norm_add` (hypothesis
    `‖x‖ = ‖y‖ = 1 → ‖x + y‖ = 2 → SameRay ℝ x y`, and `y = lam • x` with `lam ≥ 0` gives `SameRay` via `SameRay.sameRay_nonneg_smul_right`).

12. **`ρₙ(f)`, best uniform approximation from `𝒫ₙ` / `𝕋ₙ`** (Thm 3.3.19–3.3.20, §3.7).
    Surface (only as definitions, phase 3): `polyLE (n) : Submodule ℝ C(Set.Icc a b, ℝ) := (Polynomial.degreeLT ℝ (n+1)).map (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)).toLinearMap`
    (finite-dimensional by `Module.Finite.map`), `ρ n f := ⨅ p : polyLE n, ‖f - p‖`. Mathlib: `polynomialFunctions`, `Polynomial.degreeLT`.
    Trigonometric polynomials `𝕋ₙ` (3.2.13): no Mathlib real-valued object; the complex `span ℂ (fourier '' Icc (-n) n)` on `AddCircle (2π)` is the nearest.

13. **Projection onto a closed convex set `P_K`** (after Thm 3.4.3; nonlinear).
    Surface: `noncomputable def projConvex (K) (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K) : H → H := fun u => (thm_3_4_3 hne hcl hK u).choose`,
    spec `isBestApprox_projConvex`. Backbone: none (5.1.1 only has `IsBestApprox`); Mathlib: none (only the existence theorem).
    Equivalence: for a complete subspace, `projConvex K … u = K.starProjection u` (by uniqueness, Cor 3.4.2 + `starProjection_isBestApprox`).

14. **Orthogonal projection operator `P_K` onto a complete subspace** (Thm 3.4.6–3.4.7).
    Surface: `Submodule.starProjection K` with instance `Submodule.HasOrthogonalProjection.ofCompleteSpace`. Mathlib: same.
    Glue ✓ (statement): `starProjection_isBestApprox (K) [CompleteSpace K] (u) : IsBestApprox (K : Set H) u (K.starProjection u)`
    (from `Submodule.starProjection_minimal` + item 10).

15. **Direct sum `V = V₁ ⊕ V₂`, orthogonal direct sum** (Def 3.6.1).
    Surface ✓: `def IsDirectSum (V₁ V₂ : Submodule 𝕜 V) : Prop := ∀ v, ∃! p : V × V, p.1 ∈ V₁ ∧ p.2 ∈ V₂ ∧ v = p.1 + p.2`;
    orthogonal: `IsDirectSum V₁ V₂ ∧ V₁ ⟂ V₂` (`Submodule.IsOrtho`). Mathlib: `IsCompl V₁ V₂`.
    Equivalence ✓ (statement): `isDirectSum_iff_isCompl : IsDirectSum V₁ V₂ ↔ IsCompl V₁ V₂`
    (⇐ `Submodule.existsUnique_add_of_isCompl`; ⇒ `disjoint_iff`/`codisjoint_iff` from uniqueness/existence of decompositions).

16. **Projection operator on a Banach space** (Def 3.6.3): `P ∈ 𝓛(V)`, `P² = P`; projection space `P(V)`; topological direct sum.
    Surface ✓: `def IsProjectionOperator [CompleteSpace V] (P : V →L[𝕜] V) : Prop := IsIdempotentElem P` (backbone §8.3 choice).
    Mathlib: `IsIdempotentElem`, `LinearMap.IsProj`, `isProj_range_iff_isIdempotentElem`, `Submodule.projection`,
    `IsIdempotentElem.ker_eq_range_one_sub`, `ContinuousLinearMap.IsIdempotentElem.eq_projectionL`. No further equivalence needed
    (definitional); "topological direct sum" = `IsCompl P.range (1 - P).range` with both ranges closed (`IsIdempotentElem.isClosed_range`, used in
    `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean` l. 514; exact namespace to confirm at formalization time).

17. **Orthogonal projection operator** (Def 3.6.3 / (3.6.2), Hilbert `V`): projection with `(Pv, (I−P)w) = 0`.
    Surface ✓: `def IsOrthogonalProjectionOperator (P : H →L[𝕜] H) : Prop := IsIdempotentElem P ∧ ∀ v w, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w) = 0`.
    Mathlib: `LinearMap.IsSymmetricProjection` (`E →ₗ`), `IsStarProjection` (`E →L`), `ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection`.
    Equivalence ✓ (statement): `isOrthogonalProjectionOperator_iff (P) : IsOrthogonalProjectionOperator P ↔ (P : H →ₗ[𝕜] H).IsSymmetricProjection`
    via `IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker` and `IsIdempotentElem.ker_eq_range_one_sub`.

18. **Orthogonal complement** `V₁ᗮ` (§3.6): Mathlib `Submodule.orthogonal`, `Submodule.mem_orthogonal`. No def.

19. **`C_p(2π)`, Hölder classes `C_p^{k,α}(2π)`, `C^k[−1,1]` with Hölder `k`-th derivative** (§3.7, Thm 3.7.1–3.7.2).
    Surface (definitions only): `PeriodicCont := {g : ℝ → ℝ // Continuous g ∧ Function.Periodic g (2 * π)}` with sup norm
    (or `C(AddCircle (2 * π), ℝ)`), `HolderClass (k) (α) (M) (g) := ContDiff ℝ k g ∧ HolderWith M α (iteratedDeriv k g)`;
    on `[−1,1]`: `ContDiffOn ℝ k f (Icc (-1) 1) ∧ HolderOnWith M α (iteratedDerivWithin k f (Icc (-1) 1)) (Icc (-1) 1)`.
    Mathlib: `HolderWith`, `HolderOnWith`, `ContDiff`, `iteratedDeriv`. Book's §1.4.1 `C^{m,β}` uses the same convention.

20. **Fourier projection `𝓕ₙ`, Dirichlet kernel `Dₙ`, Lebesgue constants `Lₙ`, interpolatory projection `𝓘ₙ`, orthonormal polynomials `pₙ`, `P_N`, kernel `K(x,t)`** (§3.7).
    Surface: not defined in this phase (all consumers are out of scope); Mathlib has `fourierCoeff`, `fourierBasis`, `hasSum_fourier_series_L2` on
    `AddCircle` (complex-valued, `L²`), no Dirichlet kernel, no Lebesgue constants, no real trig-polynomial projection on `C_p(2π)`.
    Backbone 3.12 `OrthogonalPolynomials`/5.1.2–5.1.4 (phases 2–3) are the intended homes.

21. **§3.5 black boxes** (only cited, never proved here): Legendre `Lₙ` (3.5.4)–(3.5.6) — not in Mathlib (only `Polynomial.shiftedLegendre`);
    Chebyshev `Tₙ` (3.5.8)–(3.5.9) — `Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.T_add_two`, `Polynomial.Chebyshev.T_real_cos`;
    weighted `L²_w(−1,1)` and Gram–Schmidt orthogonal polynomials — Mathlib `InnerProductSpace.gramSchmidtNormed` on `MeasureTheory.Lp` (not planned).

---

## Results

Status legend: `direct` (Mathlib or an existing backbone item gives it, modulo trivial glue), `needs-equivalence` (goes through a
surface definition + equivalence lemma of the previous section), `GAP` (a backbone/Mathlib item is missing or must change; see the
numbered gap), `surface-only` (short proof that belongs to the surface, no backbone demand), `out-of-scope` (needs machinery not
planned in this phase; reason given).

### §2.3 Geometric series theorem and variants

**Theorem 2.3.1 (geometric series theorem).**
*Book statement.* `V` Banach (𝕂 = ℝ or ℂ), `L ∈ 𝓛(V)`, `‖L‖ < 1`. Then `I − L` is a bijection on `V` with bounded inverse,
`(I − L)⁻¹ = ∑ₙ Lⁿ` (in `𝓛(V)`), and `‖(I − L)⁻¹‖ ≤ 1/(1 − ‖L‖)` (2.3.2).
*Lean surface statement* ✓:
```lean
theorem thm_2_3_1 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L ∧
      HasSum (fun n : ℕ => L ^ n) (e.symm : V →L[𝕜] V) ∧ ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / (1 - ‖L‖)
```
*Backbone/Mathlib.* `Units.oneSub`, `NormedRing.inverse_one_sub`, `hasSum_geom_series_inverse`, `isUnit_one_sub_of_norm_lt_one`
(`Mathlib/Analysis/SpecificLimits/Normed.lean`, instance `HasSummableGeomSeries` from `CompleteSpace (V →L[𝕜] V)`),
`ContinuousLinearEquiv.unitsEquiv`; bound: backbone 2.1.1 `NormedRing.norm_inverse_one_sub_le`, or Mathlib
`tsum_geometric_le_of_norm_lt_one` (`‖∑ xⁿ‖ ≤ ‖1‖ − 1 + (1 − ‖x‖)⁻¹`, which is (2.3.2) once `‖1‖ = 1`, i.e. `[Nontrivial V]`;
the trivial space satisfies (2.3.2) trivially).
*Proof route.* `Units.oneSub L hL` → `unitsEquiv`; `HasSum` from `hasSum_geom_series_inverse`; bound from 2.1.1.
*Status:* direct.

**(2.3.4)–(2.3.5) Stability and partial-sum approximation** (remarks after Thm 2.3.1, stated as results).
*Book.* Under Thm 2.3.1, `(I − L)u = f` has a unique solution, `‖u₁ − u₂‖ ≤ ‖f₁ − f₂‖/(1 − ‖L‖)`, and `uₙ := ∑_{j≤n} Lʲ f → u`.
*Lean.* `theorem eq_2_3_5 … (hu : (1 - L) u = f) : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), (L ^ j) f) atTop (𝓝 u)` and
`theorem stability_2_3_4 … : ‖u₁ - u₂‖ ≤ (1 / (1 - ‖L‖)) * ‖f₁ - f₂‖`.
*Backbone/Mathlib.* `HasSum.tendsto_sum_nat` applied to `(fun n => L ^ n)` composed with evaluation at `f` (`ContinuousLinearMap.apply`), `ContinuousLinearMap.le_opNorm`.
*Status:* direct.

**Example 2.3.2 (second-kind equation `(λI − K)u = f`).**
*Book.* (i) abstract part: if `‖K‖ < |λ|`, `λ ≠ 0`, then `(λI − K)⁻¹` exists and `‖(λI − K)⁻¹‖ ≤ 1/(|λ| − ‖K‖)`, hence
`‖u‖ ≤ ‖f‖/(|λ| − ‖K‖)`; (ii) concrete part: `V = C[a,b]`, `K` the integral operator with continuous kernel, `‖K‖ = max_x ∫|k(x,y)|dy` (2.2.8).
*Lean* ✓ (i): `theorem example_2_3_2 (K : V →L[𝕜] V) {lam : 𝕜} (h : ‖K‖ < ‖lam‖) : ∃ e : V ≃L[𝕜] V, ↑e = lam • (1 : V →L[𝕜] V) - K ∧ ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / (‖lam‖ - ‖K‖)`.
*Proof route.* `λI − K = λ (I − λ⁻¹K)`, Thm 2.3.1 with `‖λ⁻¹K‖ < 1`, `norm_smul`.
*Status:* (i) surface-only; (ii) out-of-scope (integral operators on `C[a,b]` and (2.2.8) are not planned; Mathlib has no such operator).

**Corollary 2.3.3 (`‖Lᵐ‖ < 1`).**
*Book.* `V` Banach, `L ∈ 𝓛(V)`, `m ≥ 1`, `‖Lᵐ‖ < 1` (2.3.10). Then `I − L` bijective with bounded inverse and
`‖(I − L)⁻¹‖ ≤ (∑_{i=0}^{m−1} ‖Lⁱ‖)/(1 − ‖Lᵐ‖)` (2.3.11).
*Lean* ✓: `theorem cor_2_3_3 [CompleteSpace V] (L) {m : ℕ} (hm : 1 ≤ m) (hL : ‖L ^ m‖ < 1) : ∃ e : V ≃L[𝕜] V, ↑e = 1 - L ∧ ‖(e.symm : V →L[𝕜] V)‖ ≤ (∑ i ∈ Finset.range m, ‖L ^ i‖) / (1 - ‖L ^ m‖)`.
*Backbone.* 2.1.1 `NormedRing.isUnit_one_sub_of_norm_pow_lt_one` — but its bound is `(∑ ‖t‖ ^ i)/(1 − ‖tᵐ‖)`, weaker than the book's `∑ ‖tⁱ‖`.
*Proof route.* `(1 − L)(∑_{i<m} Lⁱ) = 1 − Lᵐ` (`geom_sum_mul_neg`/`mul_neg_geom_sum`), Thm 2.3.1 for `Lᵐ`, `norm_sum_le`.
*Status:* GAP (Gap 1: state 2.1.1 with `∑ ‖t ^ i‖`; the `‖t‖ ^ i` form then follows from `norm_pow_le'`).

**Example 2.3.4 (Volterra equation).**
*Book.* `Lv(x) = ∫₀ˣ ℓ(x,y)v(y)dy` on `C[0,B]`; iterated kernels give `‖Lᵏ‖ ≤ (MB)ᵏ/k!`, so (2.3.10) holds for large `m`.
*Lean* (abstract consequence only): `theorem example_2_3_4 [CompleteSpace V] (L) (h : Tendsto (fun k => ‖L ^ k‖) atTop (𝓝 0)) : ∃ e : V ≃L[𝕜] V, ↑e = 1 - L`.
*Proof route.* pick `m` with `‖L ^ m‖ < 1` (`(h.eventually (gt_mem_nhds one_pos)).exists`), Cor 2.3.3.
*Status:* abstract part surface-only; kernel estimate out-of-scope (iterated Volterra kernels, integral operators on `C[0,B]`).

**Theorem 2.3.5 (perturbation theorem), (2.3.12)–(2.3.15).**
*Book.* `V, W` normed, at least one complete; `L ∈ 𝓛(V,W)` with bounded inverse `L⁻¹ : W → V`; `M ∈ 𝓛(V,W)` with
`‖M − L‖ < 1/‖L⁻¹‖` (2.3.12). Then `M` bijective, `M⁻¹ ∈ 𝓛(W,V)`,
`‖M⁻¹‖ ≤ ‖L⁻¹‖/(1 − ‖L⁻¹‖‖L − M‖)` (2.3.13), `‖L⁻¹ − M⁻¹‖ ≤ ‖L⁻¹‖²‖L − M‖/(1 − ‖L⁻¹‖‖L − M‖)` (2.3.14),
and for `Lv₁ = w = Mv₂`: `‖v₁ − v₂‖ ≤ ‖M⁻¹‖‖(L − M)v₁‖` (2.3.15).
*Lean* ✓:
```lean
theorem thm_2_3_5 (hc : CompleteSpace V ∨ CompleteSpace W) (L : V ≃L[𝕜] W) (M : V →L[𝕜] W)
    (hM : ‖M - L‖ < 1 / ‖(L.symm : W →L[𝕜] V)‖) :
    ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = M ∧
      ‖(e.symm : W →L[𝕜] V)‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ / (1 - ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W) - M‖) ∧
      ‖(L.symm : W →L[𝕜] V) - (e.symm : W →L[𝕜] V)‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ ^ 2 * ‖(L : V →L[𝕜] W) - M‖ /
          (1 - ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W) - M‖) ∧
      ∀ w v₁ v₂, L v₁ = w → M v₂ = w → ‖v₁ - v₂‖ ≤ ‖(e.symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - M) v₁‖
```
(`1 / ‖L.symm‖` with `‖L.symm‖ = 0` only in the trivial case, where `1/0 = 0` makes the hypothesis false — harmless.)
*Backbone/Mathlib.* Single-space: 2.1.1 `Units.norm_inverse_add_le` (2.3.13) ✓, `Units.norm_inverse_add_sub_le` (2.3.14) ✓,
Mathlib `Units.ofNearby`, `Units.add`, `NormedRing.inverse_add_norm_diff_first_order` (qualitative). Two-space: Mathlib
`ContinuousLinearEquiv.isOpen`/`.nhds` need `[CompleteSpace V]` (domain) and give no constants; the "`W` complete" case is
`M = [I − (L − M)L⁻¹] L` on `W` and the "`V` complete" case is `M = L[I − L⁻¹(L − M)]` on `V`.
*Proof route.* case split on `hc`; each case: Thm 2.3.1 in `𝓛(W)` resp. `𝓛(V)` with `‖(L−M)L⁻¹‖ ≤ ‖L−M‖‖L⁻¹‖ < 1`; (2.3.14) from
`L⁻¹ − M⁻¹ = M⁻¹(M − L)L⁻¹`; (2.3.15) from `v₁ − v₂ = M⁻¹(M − L)v₁`.
*Status:* GAP (Gap 2: 2.1.1 promises "the `E →L[𝕜] F` two-space version, only one of `V, W` complete" but has no statement;
fix the statement above, including (2.3.15), as the backbone item; the surface then specializes).

**(2.3.16) Consistency + stability ⇒ convergence.**
*Book.* `Lv = w` exact, `Lₙ → L` in `𝓛(V,W)`; for `n` large `Lₙvₙ = w` uniquely solvable and
`‖v − vₙ‖ ≤ ‖Lₙ⁻¹‖‖(L − Lₙ)v‖`; if `‖(L − Lₙ)v‖ → 0` (consistency) and `sup ‖Lₙ⁻¹‖ < ∞` (stability) then `vₙ → v`.
Dual reading: a posteriori bound `‖v − vₙ‖ ≤ ‖M⁻¹‖‖(M − Mₙ)vₙ‖`.
*Lean* ✓ (first part): `theorem eq_2_3_16 (hc) (L : V ≃L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) (hLn : Tendsto (fun n => ‖(L : V →L[𝕜] W) - Ln n‖) atTop (𝓝 0)) : ∃ N, ∃ en : ∀ n ≥ N, V ≃L[𝕜] W, (∀ n hn, (en n hn : V →L[𝕜] W) = Ln n) ∧ ∀ w v (vn : ∀ n ≥ N, V), L v = w → (∀ n hn, Ln n (vn n hn) = w) → ∀ n hn, ‖v - vn n hn‖ ≤ ‖((en n hn).symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - Ln n) v‖`;
second part `convergence_of_consistent_stable`: add `(hcons : Tendsto (fun n => ‖((L : V →L[𝕜] W) - Ln n) v‖) atTop (𝓝 0)) (hstab : ∃ C, ∀ n hn, ‖((en n hn).symm : W →L[𝕜] V)‖ ≤ C)` and conclude `Tendsto (fun n => ‖v - vn n‖) atTop (𝓝 0)` (indexing via `n + N`).
*Proof route.* `hLn` eventually `< 1/‖L.symm‖`; Thm 2.3.5 pointwise in `n`; squeeze.
*Status:* direct (given Thm 2.3.5; 2.1.1 lists this corollary).

**Example 2.3.6** — numerical solvability analysis of (2.3.17) with (2.3.18)–(2.3.21). *Status:* out-of-scope (left out; concrete integral operators, numerical constants).

### §2.4 More results on linear operators

**Theorem 2.4.1 (extension theorem).**
*Book.* `V` normed, `V̂` its completion, `W` Banach, `L ∈ 𝓛(V,W)`. There is a unique `L̂ ∈ 𝓛(V̂,W)` with `L̂v = Lv` on `V` and `‖L̂‖ = ‖L‖`.
*Lean* ✓ (with `V̂ := UniformSpace.Completion V`):
```lean
theorem thm_2_4_1 [CompleteSpace W] (L : V →L[𝕜] W) :
    ∃ Lhat : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, Lhat v = L v) ∧ ‖Lhat‖ = ‖L‖ ∧
      ∀ L' : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, L' v = L v) → L' = Lhat
```
Variant for the book's typical use (extend from a dense subspace `V₀` of a Banach `V`): replace `Completion V` by `V` with `(hV₀ : Dense (V₀ : Set V))`, `L : V₀ →L[𝕜] W`.
*Mathlib.* `ContinuousLinearMap.extend` (`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Extend.lean`) with
`e := UniformSpace.Completion.toComplL`, `UniformSpace.Completion.denseRange_coe`, `isUniformInducing_coe`; `ContinuousLinearMap.extend_eq`;
`ContinuousLinearMap.opNorm_extend_le` with `N = 1` (`UniformSpace.Completion.norm_coe`); `≥` from `L = Lhat.comp toComplL`,
`opNorm_comp_le`, `UniformSpace.Completion.norm_toComplL`; uniqueness `ContinuousLinearMap.ext_on` with `Dense (span (range coe))`.
Also `LinearMap.extendOfNorm`, `opNorm_extendOfNorm_le` (`Mathlib/Analysis/Normed/Operator/Extend.lean`).
*Status:* direct.

**Example 2.4.2** — extension of `D : C¹[0,1] → L²(0,1)` to `H¹(0,1)`. *Status:* out-of-scope (Sobolev spaces).

**Theorem 2.4.3 (open mapping / bounded inverse).**
*Book.* `V, W` Banach, `L ∈ 𝓛(V,W)` bijective ⇒ `L⁻¹ ∈ 𝓛(W,V)`.
*Lean* ✓: `theorem thm_2_4_3 [CompleteSpace V] [CompleteSpace W] (L : V →L[𝕜] W) (hL : Function.Bijective L) : ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L`.
*Mathlib.* `ContinuousLinearEquiv.ofBijective` (`hinj : L.ker = ⊥`, `hsurj : L.range = ⊤`; `LinearMap.ker_eq_bot`, `LinearMap.range_eq_top`),
`coe_ofBijective`; also `ContinuousLinearMap.isOpenMap`, `LinearEquiv.toContinuousLinearEquivOfContinuous`, `ContinuousLinearMap.isUnit_iff_bijective`.
*Status:* direct.

**Stability bound after Thm 2.4.3** (`Lv = w`, `Lv̂ = ŵ` ⇒ `‖v − v̂‖ ≤ ‖L⁻¹‖‖w − ŵ‖`).
*Lean.* `theorem stability_2_4 (L : V ≃L[𝕜] W) (v vhat : V) : ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖`. *Mathlib:* `ContinuousLinearMap.le_opNorm`, `map_sub`. *Status:* direct.

**(2.4.1) Relative error bound and `cond(L) ≥ 1`.**
*Book.* `‖v − v̂‖/‖v‖ ≤ ‖L⁻¹‖‖L‖ · ‖w − ŵ‖/‖w‖`; `cond(L) ≡ ‖L⁻¹‖‖L‖ ≥ 1` (since `‖L⁻¹L‖ = ‖I‖ = 1`).
*Lean* ✓: `theorem eq_2_4_1 (L : V ≃L[𝕜] W) {v vhat : V} (hv : v ≠ 0) : ‖v - vhat‖ / ‖v‖ ≤ cond L * (‖L v - L vhat‖ / ‖L v‖)`;
`theorem one_le_cond [Nontrivial V] (L : V ≃L[𝕜] W) : 1 ≤ cond L`.
*Backbone/Mathlib.* 2.2 `relative_error_le_condNumber_mul_relative_residual` (stated for `A : E ≃L[𝕜] E`, single space) and
2.1.2 `NormedRing.one_le_condNumber`; two-space: Mathlib `ContinuousLinearEquiv.one_le_norm_mul_norm_symm [Nontrivial V]` gives `1 ≤ cond L` directly.
*Proof route.* `‖v − v̂‖ ≤ ‖L⁻¹‖‖w − ŵ‖`, `‖w‖ ≤ ‖L‖‖v‖`, `div_le_div`.
*Status:* `one_le_cond` direct; `eq_2_4_1` GAP (Gap 3: state 2.2's residual bound for `E ≃L[𝕜] F` and define `ContinuousLinearEquiv.condNumber`;
otherwise the surface proves the three-line bound itself, which would duplicate 2.2).

**Ill-posed / well-posed remark** — definitions only; left out (no theorem).

**Theorem 2.4.4 (principle of uniform boundedness).**
*Book.* `V` Banach, `W` normed, `Lₙ ∈ 𝓛(V,W)`, `{Lₙv}` bounded for each `v` ⇒ `sup ‖Lₙ‖ < ∞`.
*Lean* ✓ (proved): `theorem thm_2_4_4 [CompleteSpace V] (Ln : ℕ → V →L[𝕜] W) (h : ∀ v, ∃ C, ∀ n, ‖Ln n v‖ ≤ C) : ∃ C, ∀ n, ‖Ln n‖ ≤ C := banach_steinhaus h`.
*Mathlib.* `banach_steinhaus`, `banach_steinhaus_iSup_nnnorm` (`Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`). *Status:* direct.

**Theorem 2.4.5 (Banach–Steinhaus).**
*Book.* `V` complete, `W` normed, `L, Lₙ ∈ 𝓛(V,W)`, `V₀ ⊂ V` a dense subspace. `Lₙv → Lv ∀v ∈ V` iff (a) `Lₙv → Lv ∀v ∈ V₀` and (b) `sup ‖Lₙ‖ < ∞`.
*Lean* ✓: `theorem thm_2_4_5 [CompleteSpace V] (L) (Ln : ℕ → V →L[𝕜] W) (V₀ : Submodule 𝕜 V) (hV₀ : Dense (V₀ : Set V)) : (∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ↔ (∀ v ∈ V₀, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ∧ ∃ C, ∀ n, ‖Ln n‖ ≤ C`.
*Mathlib.* `⇒`: `banach_steinhaus` + `Metric.isBounded_range_of_tendsto`. `⇐`: no Mathlib lemma found (searched
`Equicontinuity.lean`, `UniformConvergence.lean`, LeanSearch); `ContinuousLinearMap.ofTendstoOfBoundedRange` only builds the limit operator.
*Proof route.* ε/3 argument of the book (`Dense.exists_dist_lt`, `le_opNorm`).
*Status:* GAP (Gap 4: ForMathlib lemma `ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`; the `⇒` half is direct).
Generality note (also in `plans/analysis/atkinson-han.md`): a dense *subset* suffices for `⇐` if one also assumes `L` bounded, which the book does.

**§2.4.4 Convergence of numerical quadratures** ((2.4.3), (2.4.4), criterion, Exercise 2.4.3).
*Book.* `Lv = ∫₀¹ w v`, `w ≥ 0`, `w ∈ L¹(0,1)`; `Lₙv = ∑_{i=0}^n wᵢ⁽ⁿ⁾ v(xᵢ⁽ⁿ⁾)` with `0 ≤ x₀ < … < xₙ ≤ 1`, as functionals on `C[0,1]`:
(i) `‖Lₙ‖ = ∑|wᵢ⁽ⁿ⁾|` (2.4.4; Exercise 2.4.2); (ii) if `Lₙ = L` on `𝒫_{d(n)}` with `d(n) → ∞`, then `Lₙv → Lv ∀v ∈ C[0,1]` iff `sup_n ∑|wᵢ⁽ⁿ⁾| < ∞`;
(iii) (Exercise 2.4.3) under (ii) with `wᵢ⁽ⁿ⁾ ≥ 0`, convergence holds.
*Lean* ✓ (definition and (i)): `noncomputable def quadFunctional {n} (w : Fin (n+1) → ℝ) (x : Fin (n+1) → Set.Icc (0:ℝ) 1) : C(Set.Icc (0:ℝ) 1, ℝ) →L[ℝ] ℝ := ∑ i, w i • ContinuousMap.evalCLM ℝ (x i)`;
`theorem eq_2_4_4 (w) (x) (hx : Function.Injective x) : ‖quadFunctional w x‖ = ∑ i, |w i|`.
(ii): `theorem quadrature_convergence (L : C(Icc 0 1, ℝ) →L[ℝ] ℝ) (w x d) (hd : Tendsto d atTop atTop) (hexact : ∀ n, ∀ p : Polynomial ℝ, p.natDegree ≤ d n → quadFunctional (w n) (x n) (p.toContinuousMapOn _) = L (p.toContinuousMapOn _)) : (∀ v, Tendsto (fun n => quadFunctional (w n) (x n) v) atTop (𝓝 (L v))) ↔ ∃ C, ∀ n, ∑ i, |w n i| ≤ C`
(with `L` any bounded functional; the book's weighted integral is one instance, `∫₀¹ w v` bounded by `‖w‖_{L¹}`).
(iii): add `(hw : ∀ n i, 0 ≤ w n i)` and `0 ≤ d n`; conclude convergence.
*Backbone/Mathlib.* 5.1.4 `Approximation/Quadrature.lean` (phase 3) is the designated home; Mathlib `polynomialFunctions_closure_eq_top`
(density of polynomials in `C(Icc a b, ℝ)`), `ContinuousMap.evalCLM`, `Polynomial.toContinuousMapOn`; Thm 2.4.5 for the criterion.
*Proof route.* (i) `≤` by `norm_sum_le`/`evalCLM` norm ≤ 1; `≥` by evaluating on a continuous `v` with `v(xᵢ) = sign wᵢ`, `‖v‖ ≤ 1`
(piecewise-linear interpolation between distinct nodes — the only real work). (ii) `⇐`: (i)-upper bound + Thm 2.4.5 `⇐` with `V₀ =` polynomial
functions (dense); `⇒`: `banach_steinhaus` + (i). (iii) `∑ wᵢ = Lₙ 1 = L 1` bounded.
*Status:* out-of-scope for this phase (backbone 5.1.4 is phase 3), but (ii)–(iii) need only Gap 4 + Weierstrass; (i) is surface-only once phase 3 starts.

**Exercise 2.4.4** (pointwise limit of bounded operators is bounded, `‖L‖ ≤ liminf ‖Lₙ‖`) — not cited by an in-scope theorem; Mathlib
`ContinuousLinearMap.ofTendstoOfBoundedRange`, `banach_steinhaus`. Left out (see §Left out).

### §2.5 Linear functionals

**Example 2.5.1** (`(Lᵖ)' = Lᵖ'`) — *Status:* out-of-scope (Lᵖ duality; Mathlib has `MeasureTheory.Lp` but no duality theorem in this form).

**Theorem 2.5.2 (Hahn–Banach).**
*Book.* `V₀` subspace of a normed `V` (𝕂 = ℝ or ℂ), `ℓ : V₀ → 𝕂` linear bounded ⇒ ∃ `ℓ̂ ∈ V'` extending `ℓ` with `‖ℓ̂‖ = ‖ℓ‖`.
*Lean* ✓ (proved): `theorem thm_2_5_2 (V₀ : Submodule 𝕜 V) (ℓ : StrongDual 𝕜 V₀) : ∃ ℓhat : StrongDual 𝕜 V, (∀ v : V₀, ℓhat v = ℓ v) ∧ ‖ℓhat‖ = ‖ℓ‖ := exists_extension_norm_eq V₀ ℓ`.
*Mathlib.* `exists_extension_norm_eq` (`Mathlib/Analysis/Normed/Module/HahnBanach.lean`, `[IsRCLikeNormedField 𝕜]`, instance from `RCLike`). *Status:* direct.

**Example 2.5.3** (point evaluation on `L^∞(0,1)` via Hahn–Banach, properties of `ℓ̂_c`) — *Status:* out-of-scope (`L^∞` cosets, measure theory).

**Definition 2.5.4 / Theorem 2.5.5 (generalized Hahn–Banach).**
*Book.* `V` real linear space, `V₀ ⊂ V` subspace, `p : V → ℝ` sublinear, `ℓ : V₀ → ℝ` linear with `ℓ ≤ p` on `V₀` ⇒ `ℓ` extends to `V` with `ℓ ≤ p`.
*Lean* ✓: `theorem thm_2_5_5 {E} [AddCommGroup E] [Module ℝ E] (V₀ : Submodule ℝ E) (p : E → ℝ) (hp : IsSublinear p) (ℓ : V₀ →ₗ[ℝ] ℝ) (hℓ : ∀ v : V₀, ℓ v ≤ p v) : ∃ ℓhat : E →ₗ[ℝ] ℝ, (∀ v : V₀, ℓhat v = ℓ v) ∧ ∀ v, ℓhat v ≤ p v`.
*Mathlib.* `exists_extension_of_le_sublinear (f : E →ₗ.[ℝ] ℝ) (N) (N_hom) (N_add) (hf)` (`Mathlib/Analysis/Convex/Cone/Extension.lean`), packaged through `LinearPMap.mk V₀ ℓ`.
*Proof route.* `isSublinear_iff` (def 4) + `LinearPMap` glue. *Status:* needs-equivalence.
Remark (book): with `p = ‖ℓ‖‖·‖` this yields Thm 2.5.2 (Exercise 2.5.1) — over ℝ only; not formalized separately.

**Corollary 2.5.6 (norming functional).**
*Book.* `V` normed, `0 ≠ v ∈ V` ⇒ ∃ `ℓ_v ∈ V'`, `‖ℓ_v‖ = 1`, `ℓ_v(v) = ‖v‖`.
*Lean* ✓ (proved): `theorem cor_2_5_6 (v : V) (hv : v ≠ 0) : ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ ℓ v = ‖v‖ := exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)`.
*Mathlib.* `exists_dual_vector`, `exists_dual_vector'`, `exists_dual_vector''`. *Status:* direct.

**Corollary 2.5.7, (2.5.4) (norm via the dual).**
*Book.* `‖v‖ = sup{|ℓ(v)| : ℓ ∈ V', ‖ℓ‖ = 1}`.
*Lean* ✓: `theorem cor_2_5_7 (v : V) : ‖v‖ = sSup {r | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖}`.
*Mathlib.* `NormedSpace.inclusionInDoubleDualLi` (`norm_map`), `ContinuousLinearMap.sSup_sphere_eq_norm` applied to
`inclusionInDoubleDual 𝕜 V v : StrongDual 𝕜 (StrongDual 𝕜 V)`; also `NormedSpace.norm_le_dual_bound`.
*Proof route.* rewrite the set as `(fun ℓ => ‖(inclusionInDoubleDual 𝕜 V v) ℓ‖) '' sphere 0 1` (`Set.ext`), then the two lemmas. *Status:* direct.

**Theorem 2.5.8 (Riesz representation).**
*Book.* `V` real or complex Hilbert, `ℓ ∈ V'` ⇒ ∃! `u ∈ V` with `ℓ(v) = (v, u) ∀v` (2.5.5), and `‖ℓ‖ = ‖u‖` (2.5.6).
*Lean* ✓ (proved outright in `ScratchCh2.lean`, `thm_2_5_8'`):
```lean
theorem thm_2_5_8 {H} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (ℓ : StrongDual 𝕜 H) :
    (∃! u : H, ∀ v, ℓ v = inner 𝕜 u v) ∧ ‖ℓ‖ = ‖(InnerProductSpace.toDual 𝕜 H).symm ℓ‖
```
(book's `(v, u)` = `inner 𝕜 u v`; the `∃!`-bundled form `∃! u, (∀ v, ℓ v = inner 𝕜 u v) ∧ ‖ℓ‖ = ‖u‖` also elaborates).
*Mathlib.* `InnerProductSpace.toDual`, `toDual_apply_apply`, `toDual_symm_apply`, `LinearIsometryEquiv.norm_map`. *Status:* direct.
The book's second proof (via Thm 3.3.12 minimization) is not reproduced (Thm 3.3.12 is out of scope).

**Example 2.5.9** (`(L²)' = L²`; Riesz representer of point evaluation in `H¹(a,b)`, (2.5.7)–(2.5.8)) — *Status:* out-of-scope (Sobolev).

### §3.3 Best approximation

**(3.3.1) Convex combinations** — `Convex.sum_mem`. *Status:* direct (no separate surface theorem needed; cite in docstring).

**Example 3.3.5 (the norm is w.l.s.c.).**
*Book.* `vₙ ⇀ v` in a normed space ⇒ `‖v‖ ≤ liminf ‖vₙ‖` (proof via Cor 2.5.6; simpler proof in inner product spaces).
*Lean* ✓: `theorem example_3_3_5 (v : ℕ → V) (u : V) (hweak : ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))) : ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop`.
*Mathlib.* `exists_dual_vector''`, `ContinuousLinearMap.le_opNorm`, `Filter.le_liminf_of_le`/`Tendsto.liminf_eq`.
*Status:* GAP (Gap 9: ForMathlib `norm_le_liminf_norm_of_weak_tendsto`; reused by AH §2.7, §11 and Kress; proof is 5 lines).

**Theorem 3.3.7 (strict separation of a compact and a closed convex set).**
*Book.* `V` real normed, `A, B` nonempty disjoint convex, one compact, the other closed ⇒ strictly separated (Def 3.3.6).
*Lean* ✓: `theorem thm_3_3_7 {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne) (hBne) (hdisj : Disjoint A B) (hAc : IsCompact A) (hBc : IsClosed B) : ∃ (ℓ : StrongDual ℝ E) (α : ℝ), ℓ ≠ 0 ∧ (∀ u ∈ A, ℓ u < α) ∧ ∀ v ∈ B, α < ℓ v`
(plus the symmetric case `A` closed, `B` compact by swapping and negating `ℓ`).
*Mathlib.* `geometric_hahn_banach_compact_closed` (`Mathlib/Analysis/LocallyConvex/Separation.lean`; normed spaces are `LocallyConvexSpace ℝ`), `geometric_hahn_banach_closed_compact`.
*Proof route.* take `α := (u+v)/2`; `ℓ ≠ 0` because `A` nonempty and `ℓ a < u < v < ℓ b`. *Status:* direct (via def 7's equivalence).

**Theorem 3.3.8, Theorem 3.3.10 (existence of minimizers in reflexive spaces; coercive variant).**
*Book.* `V` reflexive Banach, `K` bounded (resp. arbitrary) weakly closed, `f` w.l.s.c. (resp. + coercive) ⇒ `inf_K f` attained.
*Status:* out-of-scope — Mathlib has no reflexivity / weak sequential compactness (Thm 2.7.5); backbone 5.1.1 defers to phase 3.
(Record the statements as docstring stubs only.)

**Theorem 3.3.11 (Mazur lemma)** and its corollaries (Exercise 3.3.6). *Status:* out-of-scope (absent from Mathlib; weak topology).

**Theorem 3.3.12** (reflexive, convex closed `K`, convex l.s.c. `f`, bounded `K` or coercive `f` ⇒ minimizer; unique if strictly convex). *Status:* out-of-scope (reflexivity), except the uniqueness clause, which is Mathlib `StrictConvexOn.eq_of_isMinOn` (direct, reused in Thm 3.3.13).

**Theorem 3.3.13 (finite-dimensional existence of minimizers).**
*Book.* `V` normed, `K` convex, closed, finite-dimensional subset, `f : K → ℝ` convex l.s.c.; (a) `K` bounded or (b) `f` coercive on `K` ⇒ minimizer exists; unique if `f` strictly convex.
*Lean.* `theorem thm_3_3_13 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] (K : Set V) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty) (f : V → ℝ) (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K) (h : Bornology.IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u`
and `theorem thm_3_3_13_unique … (hf : StrictConvexOn ℝ K f) (hu₁ : IsMinOn f K u₁) (hu₂ : IsMinOn f K u₂) (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K) : u₁ = u₂`.
*Mathlib.* `LowerSemicontinuousOn.exists_isMinOn` (lsc on compact attains its minimum), `FiniteDimensional.proper`,
`Submodule.closed_of_finiteDimensional` (`Mathlib/Topology/Algebra/Module/FiniteDimension.lean`), `Metric.isCompact_of_isClosed_isBounded` inside `S`,
`StrictConvexOn.eq_of_isMinOn`. Convexity of `f`/`K` is not needed for existence (the book's proof does not use it either at this rung).
*Proof route.* (a) `K` compact (closed, bounded, in a proper subspace) + lsc; (b) restrict to the sublevel set `{v ∈ K | f v ≤ f v₀}`, closed (lsc) and bounded (coercive).
*Status:* surface-only now; proposed as backbone item in Gap 10 (also serves AH Ch. 11 and Thm 3.4.5).

**Theorem 3.3.14 (existence in reflexive Banach spaces).** *Status:* out-of-scope (reflexivity; the Hilbert instance is Thm 3.4.3).

**Theorem 3.3.15 (existence from a closed convex finite-dimensional subset).**
*Book.* `K ⊂ V` convex, closed, finite-dimensional subset of a normed `V` ⇒ ∀ `u` ∃ `û ∈ K` with `‖u − û‖ = inf_K ‖u − v‖`.
*Lean* ✓: `theorem thm_3_3_15 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] (K : Set V) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty) (u : V) : ∃ uhat, IsBestApprox K u uhat`
(the convexity hypothesis is kept for faithfulness; unused).
*Backbone.* 5.1.1 has only the subspace version `exists_isBestApprox_of_finiteDimensional`.
*Proof route.* `IsCompact.exists_infDist_eq_dist` on `K ∩ closedBall u ‖u − k₀‖` (compact in the proper space `S`), then `Metric.infDist_le_dist_of_mem`.
*Status:* GAP (Gap 5: generalize 5.1.1's existence lemma to closed subsets of finite-dimensional subspaces; 3.3.16 becomes a corollary).

**Theorem 3.3.16 (existence from a finite-dimensional subspace).**
*Lean* ✓: `theorem thm_3_3_16 (K : Submodule 𝕜 V) [FiniteDimensional 𝕜 K] (u : V) : ∃ uhat, IsBestApprox (K : Set V) u uhat`.
*Backbone.* 5.1.1 `exists_isBestApprox_of_finiteDimensional`. *Status:* direct. (Exercise 3.3.7's Heine–Borel proof is the backbone proof.)

**Example 3.3.17 (best polynomial approximation in `C[a,b]` / `Lᵖ(a,b)`).**
*Lean* (sup-norm case): `theorem example_3_3_17 (a b : ℝ) (n : ℕ) (f : C(Set.Icc a b, ℝ)) : ∃ p ∈ polyLE a b n, IsBestApprox (polyLE a b n : Set _) f p`
with `polyLE` from def 12 (`FiniteDimensional` via `Module.Finite.map`).
*Status:* `C[a,b]` case surface-only (instance of 3.3.16); `Lᵖ` case out-of-scope.

**Theorem 3.3.18 (uniqueness under strict convexity of `‖·‖ᵖ`).**
*Book.* `V` normed, `‖·‖ᵖ` strictly convex for some `p ≥ 1`, `K` convex ⇒ best approximations are unique.
*Lean* ✓: `theorem thm_3_3_18 [NormedSpace ℝ V] {p : ℝ} (hp : 1 ≤ p) (hconv : StrictConvexOn ℝ Set.univ (fun v : V => ‖v‖ ^ p)) {K : Set V} (hK : Convex ℝ K) {u v₁ v₂} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) : v₁ = v₂`.
*Backbone/Mathlib.* 5.1.1 `IsBestApprox.unique [StrictConvexSpace ℝ V]`; `StrictConvexSpace.of_norm_combo_lt_one` / `of_norm_add_ne_two`.
*Proof route.* `hconv` ⇒ `StrictConvexSpace ℝ V` (unit vectors `x ≠ y`: `‖(x+y)/2‖ᵖ < 1`), then backbone uniqueness; or the book's
direct midpoint argument (`hK.add_smul_sub_mem`, `hconv.2`).
*Status:* needs-equivalence (Gap 8 lists the small ForMathlib lemma `StrictConvexSpace.of_strictConvexOn_norm_rpow`).

**Exercise 3.3.8 (`‖v‖²` strictly convex in an inner product space)** — cited by Thm 3.3.18's remark and §3.4.
*Lean* ✓: `theorem exercise_3_3_8 {H} [NormedAddCommGroup H] [InnerProductSpace ℝ H] : StrictConvexOn ℝ Set.univ (fun v : H => ‖v‖ ^ 2)`.
*Mathlib.* no direct lemma; `norm_add_sq_real`, `parallelogram_law_with_norm`, `StrictConvexOn` from midpoint strictness (`strictConvexOn_iff_...` not available for
non-continuous general functions, but `norm_sq` is continuous: use `StrictConvexOn.of_slope`? simplest is `LinearOrder.strictConvexOn_of_lt`-style direct computation).
*Status:* surface-only (Gap 8 optionally ForMathlib).

**Theorem 3.3.19 (Chebyshev equioscillation), Theorem 3.3.20 (trigonometric case).** *Status:* out-of-scope (backbone 5.1.2, phase 3: Haar/de la Vallée-Poussin machinery absent).

**Theorem 3.3.21 (uniqueness in strictly normed spaces).**
*Book.* `V` strictly normed, `K` nonempty convex ⇒ at most one best approximation.
*Lean* ✓: `theorem thm_3_3_21 [NormedSpace ℝ V] (hV : IsStrictlyNormed V) {K : Set V} (hne : K.Nonempty) (hK : Convex ℝ K) {u v₁ v₂} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) : v₁ = v₂`.
*Backbone.* 5.1.1 `IsBestApprox.unique [StrictConvexSpace ℝ V]` via def 11's `isStrictlyNormed_iff_strictConvexSpace` (`haveI := ….mp hV`).
*Status:* needs-equivalence.

**Exercise 3.3.9 (inner product spaces are strictly normed)** — cited after Thm 3.3.21 and in §3.4.
*Lean.* `theorem exercise_3_3_9 {H} [NormedAddCommGroup H] [InnerProductSpace ℝ H] : IsStrictlyNormed H`.
*Mathlib.* `InnerProductSpace.toUniformConvexSpace` → `UniformConvexSpace.toStrictConvexSpace` + def 11. *Status:* needs-equivalence.
(The book's `Lᵖ`, `1 < p < ∞`, claim: out-of-scope.)

### §3.4 Best approximation in inner product spaces (real `V` throughout, per the book)

**Lemma 3.4.1, (3.4.1) (variational characterization).**
*Book.* `K` convex in a real inner product space; `û ∈ K` is a best approximation of `u` iff `(u − û, v − û) ≤ 0 ∀ v ∈ K`.
*Lean* ✓: `theorem lem_3_4_1 {K : Set H} (hK : Convex ℝ K) {u uhat : H} (hu : uhat ∈ K) : IsBestApprox K u uhat ↔ ∀ v ∈ K, inner ℝ (u - uhat) (v - uhat) ≤ 0`.
*Mathlib.* `norm_eq_iInf_iff_real_inner_le_zero` (`Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`) + def 10. *Status:* needs-equivalence
(backbone 5.1.1 promises "the `IsBestApprox` glue lemmas"; name it `isBestApprox_iff_real_inner_le_zero`).

**Corollary 3.4.2 (uniqueness in inner product spaces).**
*Lean* ✓: `theorem cor_3_4_2 {K : Set H} (hK : Convex ℝ K) {u v₁ v₂ : H} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) : v₁ = v₂`.
*Proof route.* book's proof from Lem 3.4.1 (add the two inequalities), or backbone `IsBestApprox.unique` with the `StrictConvexSpace` instance of `H`. *Status:* direct.

**Theorem 3.4.3 (projection onto a closed convex set), real Hilbert space.**
*Lean* ✓: `theorem thm_3_4_3 [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K) (u : H) : ∃! uhat, IsBestApprox K u uhat`
(+ characterization by (3.4.1) = Lem 3.4.1).
*Mathlib.* `exists_norm_eq_iInf_of_complete_convex` (`IsComplete K` from `hcl.isComplete`), def 10, Cor 3.4.2. *Status:* direct.
The book's direct parallelogram-law proof is Mathlib's proof.

**Proposition 3.4.4 (`P_K` monotone and non-expansive).**
*Book.* `K` nonempty closed convex in a real Hilbert `V`: `(P_K u − P_K v, u − v) ≥ 0`, `‖P_K u − P_K v‖ ≤ ‖u − v‖`.
*Lean* ✓ (pairs form): `theorem prop_3_4_4 {K : Set H} (hK : Convex ℝ K) {u v uhat vhat : H} (hu : IsBestApprox K u uhat) (hv : IsBestApprox K v vhat) : 0 ≤ inner ℝ (uhat - vhat) (u - v) ∧ ‖uhat - vhat‖ ≤ ‖u - v‖`;
book form via def 13: `prop_3_4_4' [CompleteSpace H] (hne hcl hK) (u v) : 0 ≤ inner ℝ (projConvex K … u - projConvex K … v) (u - v) ∧ ‖projConvex … u - projConvex … v‖ ≤ ‖u - v‖`.
(No completeness needed in the pairs form.)
*Mathlib.* only the subspace case (`Submodule.lipschitzWith_starProjection`); nothing for convex sets.
*Proof route.* Lem 3.4.1 twice, add: `‖û − v̂‖² ≤ ⟪u − v, û − v̂⟫ ≤ ‖u − v‖‖û − v̂‖` (`real_inner_le_norm`).
*Status:* GAP (Gap 6: add `IsBestApprox.inner_sub_sub_nonneg` and `IsBestApprox.norm_sub_le` to 5.1.1).

**Theorem 3.4.5 (finite-dimensional closed convex subset of an inner product space).**
*Lean* ✓: `theorem thm_3_4_5 {K : Set H} (S : Submodule ℝ H) [FiniteDimensional ℝ S] (hKS : K ⊆ S) (hcl : IsClosed K) (hK : Convex ℝ K) (hne : K.Nonempty) (u : H) : ∃! uhat, IsBestApprox K u uhat`.
*Proof route.* Thm 3.3.15 (existence) + Cor 3.4.2. *Status:* GAP (depends on Gap 5 only).

**Theorem 3.4.6 (complete subspace; (3.4.2) orthogonality characterization).**
*Book.* `K` complete subspace of an inner product space ⇒ ∃! best approximation `û`, characterized by `(u − û, v) = 0 ∀ v ∈ K`.
*Lean* ✓ (stated over `RCLike 𝕜`, which contains the book's real case): `theorem thm_3_4_6 (K : Submodule 𝕜 H) [CompleteSpace K] (u : H) : (∃! uhat, IsBestApprox (K : Set H) u uhat) ∧ ∀ uhat ∈ K, IsBestApprox (K : Set H) u uhat ↔ ∀ v ∈ K, inner 𝕜 (u - uhat) v = 0`.
*Mathlib.* `Submodule.exists_norm_eq_iInf_of_complete_subspace`, `Submodule.norm_eq_iInf_iff_inner_eq_zero` (real: `norm_eq_iInf_iff_real_inner_eq_zero`), `Submodule.starProjection_minimal`. *Status:* direct (via def 10).

**Exercise 3.4.8 ((3.4.1) ⟺ (3.4.2) for subspaces)** — cited after Thm 3.4.6.
*Lean.* `theorem exercise_3_4_8 (K : Submodule ℝ H) {u uhat} (hu : uhat ∈ K) : (∀ v ∈ K, inner ℝ (u - uhat) (v - uhat) ≤ 0) ↔ ∀ v ∈ K, inner ℝ (u - uhat) v = 0`.
*Mathlib.* both sides ↔ `‖u − û‖ = ⨅ …` by `norm_eq_iInf_iff_real_inner_le_zero` (with `K.convex`) and `norm_eq_iInf_iff_real_inner_eq_zero`. *Status:* direct.

**Theorem 3.4.7 (orthogonal projection operator), (3.4.3)–(3.4.5).**
*Book.* `K` complete subspace ⇒ `P_K` is linear, self-adjoint `(P_K u, v) = (u, P_K v)`, `‖v‖² = ‖P_K v‖² + ‖v − P_K v‖²`, and `‖P_K‖ = 1`.
*Lean* ✓ (three of four parts closed by name):
```lean
theorem thm_3_4_7 (K : Submodule 𝕜 H) [CompleteSpace K] :
    (∀ u v, inner 𝕜 (K.starProjection u) v = inner 𝕜 u (K.starProjection v)) ∧
      (∀ v, ‖v‖ ^ 2 = ‖K.starProjection v‖ ^ 2 + ‖v - K.starProjection v‖ ^ 2) ∧
      ‖K.starProjection‖ ≤ 1 ∧ (K ≠ ⊥ → ‖K.starProjection‖ = 1)
```
*Mathlib.* linearity is `starProjection : H →L[𝕜] H`; `Submodule.starProjection_isSymmetric`; `Submodule.norm_sq_eq_add_norm_sq_projection` with
`Submodule.starProjection_orthogonal_val` (`Kᗮ.starProjection v = v − K.starProjection v`); `Submodule.starProjection_norm_le`, `Submodule.norm_starProjection (hK : K ≠ ⊥)`.
*Status:* direct. **Book imprecision:** (3.4.5) `‖P_K‖ = 1` fails for `K = {0}`; the surface states `≤ 1` and `= 1` under `K ≠ ⊥` (recorded in the docstring).

**(3.4.6) Least-squares approximation from `span{φ₁,…,φₙ}` and the expansion `u = ∑ (u, φᵢ) φᵢ`.**
*Lean* ✓: `theorem eq_3_4_6 [DecidableEq H] {ι} {φ : ι → H} (hφ : Orthonormal 𝕜 φ) (s : Finset ι) (u : H) : (Submodule.span 𝕜 (s.image φ : Set H)).starProjection u = ∑ i ∈ s, inner 𝕜 (φ i) u • φ i`;
`theorem expansion_3_4 {ι} (b : HilbertBasis ι 𝕜 H) (u : H) : HasSum (fun i => inner 𝕜 (b i) u • b i) u` (proved: `simpa [b.repr_apply_apply] using b.hasSum_repr u`).
*Mathlib.* `OrthonormalBasis.span`, `OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum`, `OrthonormalBasis.starProjection_eq_sum_rankOne`, `HilbertBasis.hasSum_repr`, `HilbertBasis.repr_apply_apply`.
The book's intermediate identity `f(b) = ‖u‖² − ∑|(u,φᵢ)|² + ∑|bᵢ − (u,φᵢ)|²` is `Orthonormal.sum_inner_products_le`-style bookkeeping; optional. *Status:* direct.

**Example 3.4.8 (Legendre least squares, Parseval), Example 3.4.9 (Fourier series in `L²(0,2π)`).** *Status:* out-of-scope (`L²` function spaces; Mathlib's `fourierBasis`/`hasSum_fourier_series_L2` covers the complex `L²` Fourier case if wanted later).

### §3.5 Orthogonal polynomials — black boxes only (see def 21). No results planned; (3.5.2) `P_N u = ∑ ξₙ pₙ` is an instance of (3.4.6). *Status:* out-of-scope (weighted `L²`, backbone 3.12 phase 2–3).

### §3.6 Projection operators

**Definition 3.6.1 / Proposition 3.6.2 (direct sums ↔ idempotents).**
*Book.* `V = V₁ ⊕ V₂` iff ∃ linear `P` with `P² = P`, `v₁ = Pv`, `v₂ = (I − P)v`, `V₁ = P(V)`, `V₂ = (I − P)(V)`.
*Lean* ✓: `theorem prop_3_6_2 (V₁ V₂ : Submodule 𝕜 V) : IsDirectSum V₁ V₂ ↔ ∃ P : V →ₗ[𝕜] V, P ∘ₗ P = P ∧ LinearMap.range P = V₁ ∧ LinearMap.range (LinearMap.id - P) = V₂`
(the decomposition clause `v₁ = Pv, v₂ = (I − P)v` follows from uniqueness; add it to the `∃` if desired).
*Mathlib.* `isDirectSum_iff_isCompl` (def 15), `Submodule.projection`, `Submodule.isIdempotentElem_projection`, `Submodule.range_projection`, `Submodule.ker_projection`,
`IsIdempotentElem.isProj_range`, `LinearMap.IsProj.isCompl`, `IsIdempotentElem.ker_eq_range_one_sub`. *Status:* needs-equivalence.

**Definition 3.6.3** — see defs 16–17 (no theorem). "Easy to see" (3.6.2) equivalence: `isOrthogonalProjectionOperator_iff` (def 17), needs-equivalence.

**Example 3.6.4** (`ℝ²`) — left out (trivial). **Example 3.6.5 (Lagrange interpolation projection), Example 3.6.6 (piecewise linear interpolation)** — *Status:* out-of-scope
(backbone 5.1.3 phase 3; Mathlib `Lagrange.interpolate` exists but the operator on `C[a,b]` and its projection property are not planned). **Example 3.6.8 (Fourier projection)** — out-of-scope.

**Example 3.6.7 (orthonormal-basis formula defines an orthogonal projection).**
*Lean* ✓: `theorem example_3_6_7 [CompleteSpace H] {n : ℕ} {u : Fin n → H} (hu : Orthonormal 𝕜 u) : IsOrthogonalProjectionOperator (∑ i, InnerProductSpace.rankOne 𝕜 (u i) (u i))`.
*Mathlib.* `OrthonormalBasis.starProjection_eq_sum_rankOne` with `OrthonormalBasis.span`, `Submodule.isSymmetricProjection_starProjection`. *Status:* direct (via def 17).

**Proposition 3.6.9 (orthogonal projection), Hilbert `V`, closed subspace `V₁`.**
(a) *Book.* `P` orthogonal projection iff self-adjoint projection.
*Lean* ✓: `theorem prop_3_6_9_a [CompleteSpace H] (P : H →L[𝕜] H) (hP : IsIdempotentElem P) : (∀ v w, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w) = 0) ↔ (P : H →ₗ[𝕜] H).IsSymmetric`.
*Mathlib.* `IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`, `IsIdempotentElem.ker_eq_range_one_sub`; `ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection`. *Status:* direct.
(b) *Book.* each orthogonal projection is continuous, `‖P‖ ≤ 1`, `‖P‖ = 1` for `P ≠ 0`.
*Lean* ✓: `theorem prop_3_6_9_b (P) (hP : IsOrthogonalProjectionOperator P) : ‖P‖ ≤ 1 ∧ (P ≠ 0 → ‖P‖ = 1)` (continuity is built into `H →L[𝕜] H`; for the
`E →ₗ` reading, `LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range` supplies continuity).
*Mathlib.* `LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range`, `Submodule.starProjection_norm_le`, `Submodule.norm_starProjection`. *Status:* direct.
(c) *Book.* `V = V₁ ⊕ V₁ᗮ`. *Lean* ✓ (proved): `theorem prop_3_6_9_c (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) : IsCompl V₁ V₁ᗮ` via `h.completeSpace_coe` and `Submodule.isCompl_orthogonal`. *Status:* direct.
(d) *Book.* exactly one orthogonal projection onto `V₁`; `‖v − Pv‖ = inf_{w∈V₁} ‖v − w‖`; `I − P` is the orthogonal projection onto `V₁ᗮ`.
*Lean* ✓: `theorem prop_3_6_9_d (V₁) (h : IsClosed (V₁ : Set H)) : (∃! P : H →L[𝕜] H, IsOrthogonalProjectionOperator P ∧ P.range = V₁) ∧ ∀ P, IsOrthogonalProjectionOperator P → P.range = V₁ → (∀ v, ‖v - P v‖ = ⨅ w : V₁, ‖v - w‖) ∧ IsOrthogonalProjectionOperator ((1 : H →L[𝕜] H) - P) ∧ ((1 : H →L[𝕜] H) - P).range = V₁ᗮ`.
*Mathlib.* `LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range` (uniqueness), `Submodule.starProjection_minimal`, `Submodule.starProjection_orthogonal_val`, `IsIdempotentElem.one_sub`, `IsIdempotentElem.ker_eq_range_one_sub`. *Status:* direct.
(e) *Book.* `P(V)` closed, `V = P(V) ⊕ (I − P)(V)` orthogonal.
*Lean* ✓: `theorem prop_3_6_9_e (P) (hP : IsOrthogonalProjectionOperator P) : IsClosed (P.range : Set H) ∧ IsCompl P.range ((1 : H →L[𝕜] H) - P).range ∧ ((1 : H →L[𝕜] H) - P).range = P.rangeᗮ`.
*Mathlib.* `IsIdempotentElem.isClosed_range` (bounded idempotent, namespace to confirm), `ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range`, `Submodule.isCompl_orthogonal`, `LinearMap.IsSymmetric.orthogonal_range`. *Status:* direct.

**Exercise 3.6.1 (`I − P` is a projection; range/kernel swap)** — used implicitly by 3.6.9(d). *Mathlib.* `IsIdempotentElem.one_sub`, `IsIdempotentElem.ker_eq_range`, `IsIdempotentElem.ker_eq_range_one_sub`. *Status:* direct.

**Exercise 3.6.7 (`‖P‖ ≥ 1` for a nonzero bounded projection; `= 1` for orthogonal projections).**
*Lean* ✓: `theorem exercise_3_6_7 [CompleteSpace V] (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (h0 : P ≠ 0) : 1 ≤ ‖P‖` (second clause = 3.6.9(b)).
*Backbone.* 5.1.1 lists "`‖P‖ ≥ 1` for a nonzero projection". *Proof route.* `‖P‖ = ‖P * P‖ ≤ ‖P‖ * ‖P‖`, `norm_pos_iff`. *Status:* direct (backbone item, sketch only — no Lean statement given there; trivial).

### §3.7 Uniform error bounds

**(3.7.1)–(3.7.2) transfer `f(cos θ)` / even trigonometric best approximation; Theorem 3.7.1, Theorem 3.7.2 (Jackson).**
*Book.* `g ∈ C_p^{k,α}(2π)` ⇒ `‖g − qₙ‖_∞ ≤ c^{k+1} M_k / n^{k+α}`, `c = 1 + π²/2`; polynomial version with `d_k`.
*Lean* (statement sketch only, using def 19): `theorem thm_3_7_1 (g) (hg : HolderClass k α M g) (n : ℕ) (hn : 1 ≤ n) : ρ_trig n g ≤ (1 + π ^ 2 / 2) ^ (k + 1) * M / n ^ (k + α)`.
*Status:* out-of-scope (backbone §8.3 marks Thm 3.7.1–3.7.3 as phase 3 / Mathlib gap; no trigonometric polynomial machinery).

**(3.7.5)** `‖f − 𝓕ₙf‖₂ ≤ √(2π)‖f − 𝓕ₙf‖_∞` — out-of-scope (`L²`; trivial once `𝓕ₙ` exists).

**(3.7.6)–(3.7.8) Dirichlet kernel representation and closed form; (3.7.9) `‖𝓕ₙ‖ ≤ Lₙ` (and `= Lₙ` via (2.2.8)); (3.7.10) `Lₙ = (4/π²) log n + O(1)`.**
*Status:* out-of-scope (needs `𝓕ₙ` on `C_p(2π)`, integral-operator norm formula (2.2.8), Zygmund's asymptotics). The closed form (3.7.8) is an elementary trig identity that could be surface-only in phase 3.

**Non-convergence of `𝓕ₙf` for some `f ∈ C_p(2π)`** (paragraph after (3.7.10)).
*Book.* `{‖𝓕ₙ‖}` unbounded + `𝓕ₙ = I` on `𝕋ₙ` + density of trig polynomials ⇒ ∃ `f` with `𝓕ₙf ↛ f` uniformly (Banach–Steinhaus).
*Lean* ✓ (abstract form): `theorem exists_not_tendsto_of_not_bddAbove [CompleteSpace V] (P : ℕ → V →L[𝕜] V) (h : ¬ BddAbove (Set.range fun n => ‖P n‖)) : ∃ f : V, ¬ Tendsto (fun n => P n f) atTop (𝓝 f)`.
*Mathlib.* contrapositive of `banach_steinhaus` + `Metric.isBounded_range_of_tendsto`. *Status:* direct (abstract); the concrete Fourier instance is out-of-scope.

**(3.7.11), (3.7.14), (3.7.21) (Lebesgue lemma + Jackson).**
*Book.* For a bounded projection `𝓕ₙ` onto `𝕋ₙ` and the best approximation `qₙ`: `‖f − 𝓕ₙf‖_∞ ≤ (1 + ‖𝓕ₙ‖)‖f − qₙ‖_∞`, hence `≤ (1 + ‖𝓕ₙ‖) c^{k+1} M_k/n^{k+α}`; same for `P_N` on `C[−1,1]` (3.7.14) and `𝓘ₙ` (3.7.21).
*Lean* ✓ (abstract Lebesgue lemma): `theorem lebesgue_lemma (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u q : V) (hq : q ∈ P.range) : ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖`;
corollary with `IsBestApprox P.range u q`: `‖u - P u‖ ≤ (1 + ‖P‖) * ⨅ w : P.range, ‖u - w‖`.
*Backbone.* 5.1.1 `norm_sub_projection_le (P) (hP : IsIdempotentElem P) (u) : ‖u - P u‖ ≤ (1 + ‖P‖) * Metric.infDist u (LinearMap.range P)`.
*Proof route.* `u − Pu = (u − q) − P(u − q)` for `q = Pq`. *Status:* Lebesgue part direct (Gap 7 asks for the pointwise-`q` form as the primary backbone statement); Jackson part out-of-scope.

**(3.7.12), (3.7.22)** `‖f − 𝓕ₙf‖_∞ ≤ c_k log n / n^{k+α}` — out-of-scope (needs (3.7.10)/(3.7.20) + Jackson).

**(3.7.13)–(3.7.17) `P_N` on `L²_w`, kernel `K(x,t)`, `‖P_N‖ = max_x ∫|K(x,t)|dt`** — out-of-scope (weighted `L²`, (2.2.8)).

**Theorem 3.7.3 (Christoffel–Darboux identity).**
*Book.* orthonormal `pₙ` w.r.t. weight `w ≥ 0`: `∑_{n≤N} pₙ(x)pₙ(t) = (p_{N+1}(x)p_N(t) − p_N(x)p_{N+1}(t))/(a_N(x − t))`, `a_N = A_{N+1}/A_N`; confluent form at `x = t`.
*Status:* out-of-scope (backbone 3.12 `OrthogonalPolynomials`, phase 2–3). Note for that plan: the identity is purely algebraic from the three-term recurrence
(Exercises 3.5.5–3.5.6) and could be stated for any sequence of polynomials satisfying `p_{n+1} = (aₙx + bₙ)pₙ + cₙp_{n−1}` with `cₙ = −aₙ/a_{n−1}`.

**Example 3.7.4 (Chebyshev kernel, `‖P_N‖ = (4/π²) log N + O(1)`)** — out-of-scope.

**§3.7.3 (3.7.19) trigonometric Lagrange formula, (3.7.20) `‖𝓘ₙ‖ ≤ 1 + (2/π) log n`** — out-of-scope (trigonometric interpolation, Rivlin's bound).

---

## Gaps and requests to the backbone

1. **2.1.1, Cor 2.3.3 bound.** `NormedRing.isUnit_one_sub_of_norm_pow_lt_one` is planned with `(∑ i ∈ range m, ‖t‖ ^ i)/(1 − ‖t ^ m‖)`; the book's (2.3.11) has
   `∑ ‖t ^ i‖` (sharper). Please state the `‖t ^ i‖` form (proof unchanged: `(1 − t)(∑_{i<m} tⁱ) = 1 − tᵐ`, `norm_sum_le`); the `‖t‖ ^ i` form is a corollary via `norm_pow_le'`.
2. **2.1.1, two-space perturbation theorem.** The plan mentions "the `E →L[𝕜] F` two-space version of AH 2.3.5 (only one of `V, W` complete)" without a statement.
   Proposed backbone statement = `thm_2_3_5` above (hypothesis `CompleteSpace V ∨ CompleteSpace W`, conclusions (2.3.13)–(2.3.15)), e.g.
   `ContinuousLinearEquiv.exists_of_norm_sub_lt`; also a `def ContinuousLinearEquiv.ofNearby` (data version) if the Krylov/Newton layers want it. Kress Thm 3.48 and Saad §1.13 use the same statement.
3. **2.2 / 2.1.2, condition number of an equivalence between two spaces.** `relative_error_le_condNumber_mul_relative_residual` is stated for `A : E ≃L[𝕜] E`; AH (2.4.1) and Kress Def 5.2 are `V → W`.
   Please state it for `A : E ≃L[𝕜] F` with `def ContinuousLinearEquiv.condNumber (e : E ≃L[𝕜] F) : ℝ := ‖(e : E →L[𝕜] F)‖ * ‖(e.symm : F →L[𝕜] E)‖`, the lemma
   `ContinuousLinearEquiv.condNumber_eq_condNumber (e : E ≃L[𝕜] E) : e.condNumber = NormedRing.condNumber (e : E →L[𝕜] E)` (already sketched as `condNumber_eq`),
   and `one_le_condNumber [Nontrivial E]` from Mathlib `ContinuousLinearEquiv.one_le_norm_mul_norm_symm`.
4. **New ForMathlib item `ForMathlib/Operator/BanachSteinhaus.lean`.** (i) `ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded
   [CompleteSpace V]? (no: not needed) {L : V →L[𝕜] W} {Ln : ℕ → V →L[𝕜] W} {s : Set V} (hs : Dense s) (hb : ∃ C, ∀ n, ‖Ln n‖ ≤ C) (h : ∀ v ∈ s, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) : ∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))`
   (ε/3; no completeness needed; works for any filter, not just `atTop`); (ii) the iff of Thm 2.4.5 (`[CompleteSpace V]`, dense subspace);
   (iii) `exists_not_tendsto_of_not_bddAbove` (contrapositive of `banach_steinhaus`). Serves AH 2.4.5, §2.4.4, §3.7.1, Kress Thm 9.10 (Szegő), backbone 5.1.4. Not found in Mathlib (`Equicontinuity.lean`, LeanSearch).
5. **5.1.1, existence of best approximations.** Generalize `exists_isBestApprox_of_finiteDimensional` to
   `exists_isBestApprox_of_isClosed_of_subset_finiteDimensional (K : Set V) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hK : IsClosed K) (hne : K.Nonempty) (u) : ∃ v, IsBestApprox K u v`
   (Thm 3.3.15; proof `IsCompact.exists_infDist_eq_dist` on `K ∩ closedBall u ‖u − k₀‖`, `FiniteDimensional.proper`, `Submodule.closed_of_finiteDimensional`); the subspace version is the special case `K = S`. Needed by Thm 3.4.5 too.
6. **5.1.1, Hilbert-space glue for `IsBestApprox`** (the plan promises "the `IsBestApprox` glue lemmas"; concrete list):
   `isBestApprox_iff_norm_eq_iInf` (def 10), `isBestApprox_iff_real_inner_le_zero` (Lem 3.4.1, from `norm_eq_iInf_iff_real_inner_le_zero`),
   `isBestApprox_iff_inner_eq_zero` (Thm 3.4.6, subspaces, `RCLike`), `IsBestApprox.unique_of_innerProductSpace` (Cor 3.4.2),
   `exists_isBestApprox_of_isClosed_convex [CompleteSpace H]` (Thm 3.4.3), `starProjection_isBestApprox`, and Prop 3.4.4 in pairs form:
   `IsBestApprox.inner_sub_sub_nonneg (hK : Convex ℝ K) (hu : IsBestApprox K u û) (hv : IsBestApprox K v v̂) : 0 ≤ ⟪û − v̂, u − v⟫_ℝ` and
   `IsBestApprox.norm_sub_le … : ‖û − v̂‖ ≤ ‖u − v‖`. Optionally a chooser `Convex.bestApprox` (AH's `P_K`, used again in AH Ch. 11 variational inequalities).
7. **5.1.1, Lebesgue lemma.** State the pointwise form `norm_sub_projection_le_of_mem (hP : IsIdempotentElem P) (hq : q ∈ LinearMap.range P) : ‖u − P u‖ ≤ (1 + ‖P‖) * ‖u − q‖`
   as the primary lemma (AH (3.7.11)/(3.7.14)/(3.7.21) all use it with `q` = best approximation), with the `Metric.infDist` version and `‖u − Pu‖ ≤ ‖1 − P‖‖u − q‖` as corollaries.
   Also give the Lean statement of "`‖P‖ ≥ 1` for a nonzero projection" (Exercise 3.6.7): `IsIdempotentElem.one_le_norm (hP : IsIdempotentElem P) (h0 : P ≠ 0) : 1 ≤ ‖P‖` (any normed ring, `‖P‖ = ‖P*P‖ ≤ ‖P‖²`).
8. **ForMathlib (strict convexity).** `StrictConvexSpace.of_strictConvexOn_norm_rpow (hp : 1 ≤ p) (h : StrictConvexOn ℝ univ (fun v => ‖v‖ ^ p)) : StrictConvexSpace ℝ V` (Thm 3.3.18) and
   `strictConvexOn_norm_sq [InnerProductSpace ℝ H] : StrictConvexOn ℝ univ (fun v => ‖v‖ ^ 2)` (Exercise 3.3.8). Small; could also live in the surface (`surface-only`), but they are Mathlib-shaped.
   The equivalence `IsStrictlyNormed V ↔ StrictConvexSpace ℝ V` stays in the surface (book-specific vocabulary).
9. **ForMathlib (weak l.s.c. of the norm).** `norm_le_liminf_norm_of_weak_tendsto (h : ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) l (𝓝 (ℓ u))) : ‖u‖ ≤ liminf (fun n => ‖v n‖) l`
   (Example 3.3.5; via `exists_dual_vector''`). Reused by AH §2.7 (Exercise 2.7.2), §3.3, §11, Kress. Consider a `WeakSeqTendsto` predicate or Mathlib's `WeakSpace` topology as the hypothesis form.
10. **Optional new module `Numlib/Variational/Minimization.lean`.** Existence/uniqueness of minimizers of l.s.c. functionals on closed subsets of finite-dimensional subspaces
    (bounded set or coercive functional; uniqueness under `StrictConvexOn`) = Thm 3.3.13, from `LowerSemicontinuousOn.exists_isMinOn` and `StrictConvexOn.eq_of_isMinOn`.
    Needed later by AH Ch. 11 (variational inequalities) and the finite-dimensional Galerkin theory; for now Thm 3.3.13 is surface-only.
11. **5.1.4 (phase 3) quadrature.** When it starts: (2.4.4) `‖∑ wᵢ • evalCLM xᵢ‖ = ∑|wᵢ|` for distinct nodes (needs a norm-1 continuous function with prescribed signs at the nodes),
    and the convergence criterion of §2.4.4 from Gap 4 + `polynomialFunctions_closure_eq_top`. Definition `quadFunctional` above type-checks and can be moved there.
12. **Naming.** Backbone `LinearMap.IsCoercive` (§2.1.4) vs the book's coercive *functional* (Def 3.3.9): the surface will use `IsCoerciveFunctionalOn`; please avoid `IsCoercive` for real-valued functionals in the backbone.
   Also: `IsBestApprox` should stay on `SeminormedAddCommGroup` (as planned) so that `Metric.infDist_eq_iInf` glue works without `NormedSpace`.

## Left out

* Example 2.3.6, Exercises 2.3.1–2.3.11 (except the abstract content of Exercise 2.3.4/2.3.7, which are instances of Thm 2.3.1) — numerical examples; not cited by in-scope theorems.
* Operator-valued functions `e^L`, `sin L`, `arctan L` (§2.3 remark) — Mathlib has only `NormedSpace.exp`; no theorem in the book.
* Example 2.4.2, Example 2.5.1, Example 2.5.3, Example 2.5.9, Example 3.4.8, Example 3.4.9, Example 3.6.8, Example 3.7.4 — Sobolev/`Lᵖ`/`L²` function spaces not planned.
* Example 3.6.4 (`ℝ²` picture) — trivial; Examples 3.6.5–3.6.6 — interpolation operators (backbone 5.1.3, phase 3).
* Exercise 2.4.4 (limit of pointwise-convergent bounded operators) — not cited; Mathlib `ContinuousLinearMap.ofTendstoOfBoundedRange` covers it.
* Exercises 2.4.5–2.4.7, 2.5.3–2.5.6, 3.3.1–3.3.5, 3.4.1–3.4.7, 3.4.10–3.4.12, 3.5.*, 3.6.2–3.6.6, 3.6.8–3.6.9, 3.7.* — not cited by in-scope theorems (3.4.7/3.4.9/3.6.6 are the proofs of Prop 3.4.4/Thm 3.4.7/Prop 3.6.9, covered by those blocks).
* Weak closedness / w.l.s.c. as general definitions, Theorems 3.3.8, 3.3.10–3.3.12, 3.3.14, Mazur (3.3.11) — reflexivity and weak sequential compactness are absent from Mathlib (backbone 5.1.1: phase 3).
* Theorems 3.3.19–3.3.20 (equioscillation) — backbone 5.1.2, phase 3.
* All of §3.5 except as cited black boxes; §3.7 Jackson theorems, Dirichlet kernel, Lebesgue constants, Christoffel–Darboux, interpolatory projections — phase 3 (backbone 3.12, 5.1.2–5.1.4); only the abstract Lebesgue lemma and the Banach–Steinhaus non-convergence lemma are kept.
* (2.2.8)-based norm identities (`‖K‖ = max_x ∫|k(x,y)|dy`) used by Ex 2.3.2, (3.7.9), (3.7.17) — integral operators on `C[a,b]` not planned.
* The `Lᵖ` (`1 < p < ∞`) strict-convexity claims after Thm 3.3.18/3.3.21 (Clarkson) — not in Mathlib.

## OCR uncertainties

* §2.3, Example 2.3.2: (2.3.8) writes `|K(x,y)|` (capital) for the kernel `k(x,y)`; treated as `k`.
* §2.3, Example 2.3.6: numerical constants (`1 − cos 1 ≈ 0.4597`, `cos 1 − 1/2 ≈ 0.0403`, `λ₀ ≈ −0.0881`) and the quadratic for `λ₀` were not verified (left out anyway).
* §2.3.1 text: "irregardless" (book typo, not OCR).
* §2.4.4: `L_n` defined on `C[0,1]` with `0 ≤ x₀ < … < xₙ ≤ 1`; the OCR of (2.4.2) vs (2.4.3) is consistent. `d(n)` degree of precision as read.
* §3.3.4, strictly normed: read as "`‖u+v‖ = ‖u‖+‖v‖` and `u ≠ 0` implies `v = λu` for some non-negative scalar `λ`" (consistent with the proof of Thm 3.3.21).
* §3.4, Theorem 3.4.7 (3.4.5) "`‖P_K‖ = 1`" — book imprecision (fails for `K = {0}`), not OCR; surface states `≤ 1` and `= 1` for `K ≠ ⊥`.
* §3.6, Proposition 3.6.9 header "Let `P : V → V₁`" as read; (b) "continuous" is redundant with Def 3.6.3 (which already assumes `P ∈ 𝓛(V)`), so (b) is formalized for `P : H →L[𝕜] H` with the `E →ₗ` reading noted.
* §3.7, (3.7.8): the OCR says "For `t ∉ {2jπ}`" while the formula is in `θ` (book/OCR variable mismatch).
* §3.7.1: "`‖𝓕ₙ‖ = 1` when `𝓕ₙ` is viewed as an operator from `L^(−π,π)` to itself" — garbled; should be `L²(−π,π)`.
* §3.7.2, Example 3.7.4: "`‖P_N‖ = (4/π²) log n + O(1), n ≥ 1`" uses `n` for `N` (book typo).
* §3.7, Theorem 3.7.2: the constant `d_k` condition `d_k ≥ n^{k+α}/(n(n−1)⋯(n−k+1)(n−k)^α)`, `n > k`, as read.
* Figure references (Fig. 2.1, 3.3, 3.4) carry no mathematical content and were ignored.
