# Surface plan: Atkinson–Han — Chapter 5

Atkinson & Han, *Theoretical Numerical Analysis* (3rd ed.), Ch. 5 "Nonlinear Equations and Their
Solution by Iteration": §5.1 Banach fixed point, §5.2 applications (scalar, linear systems, integral
equations, ODEs in Banach spaces), §5.3 differential calculus of operators, §5.4 Newton (local +
Kantorovich), §5.5 completely continuous vector fields (summary only), §5.6 CG for operator equations.

Generality as in the book: §5.1–5.2 on a Banach space `V` (scalar field irrelevant; we state over
`[NormedSpace ℝ V]`, generalising to `RCLike 𝕜` is free), Thm 5.1.4 and §5.6 on a **real** Hilbert
space (the book says so explicitly in §5.6; Thm 5.1.4 says "Hilbert space" with a real inner product
`(·,·)`), §5.3 on normed spaces (Prop 5.3.11/5.3.13 say "real Banach"), §5.4 on Banach spaces `U, W`.
The surface imports only `Numlib`; every backbone declaration is cited with its module under `Numlib/`.

Classification of each book item. `direct`: proof is a direct use of Mathlib or of a `Numlib`
declaration (named). `needs-equivalence`: same, modulo a surface lemma identifying the book's
definition with the Mathlib/backbone notion (the lemma is named in §1). `surface-only`: provable in
the surface file from Mathlib with moderate work, no backbone item warranted. `deferred`: needs a
backbone item scheduled for a later phase (`plans/backbone.md` §7; the item is listed in §3).
`out-of-scope`: not planned (reason given).

Proposed files (`Surface/AtkinsonHan/Ch05/`, namespace `AtkinsonHan.Ch05`, one section per file):

| File | Book | Backbone modules used |
|---|---|---|
| `FixedPoint.lean` | Def 5.1.2, Thm 5.1.3 (5.1.4)–(5.1.6), Ex 5.1.2, Thm 5.1.4 (5.1.8)–(5.1.11) | `Numlib/Nonlinear/FixedPoint.lean`; `Numlib/Analysis/InnerProductSpace/Coercive.lean` (linear case); Mathlib `ContractingWith` |
| `LinearIteration.lean` | Thm 5.2.1 + derivative criterion; §5.2.2 (5.2.4)–(5.2.6), relations 1–3, Jacobi/GS/SOR | `Numlib/Nonlinear/FixedPoint.lean` (derivative criterion); `Numlib/LinearSolve/Stationary/{Basic,Splitting}.lean`; `Numlib/Matrix/{Hessenberg,Complexify}.lean`; `Numlib/Analysis/Normed/Algebra/SpectralRadius.lean`; Mathlib MVT |
| `IntegralEquations.lean` (phase 3) | §5.2.3 (5.2.7)–(5.2.9), Thm 5.2.2–5.2.3, §5.2.4 Thm 5.2.4 | Mathlib `IsPicardLindelof`, `ODE_solution_unique_of_mem_Icc`; the `C[a,b]` integral-operator toolkit (§3 item 1) |
| `Calculus.lean` | Def 5.3.1–5.3.2, Prop 5.3.3–5.3.7, Ex 5.3.8, Prop 5.3.11–5.3.13, Def 5.3.14–Cor 5.3.16, Thm 5.3.17–5.3.19 | Mathlib `HasFDerivAt`, `HasLineDerivAt`, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, `FDeriv/Partial.lean` |
| `Newton.lean` | (5.4.2), Thm 5.4.1 (5.4.3)–(5.4.5), Thm 5.4.2, (5.4.7) | `Numlib/Nonlinear/Newton.lean`; `Numlib/Analysis/Normed/Ring/Inverse.lean` |
| `ConjugateGradient.lean` | (5.6.2)–(5.6.6), (5.6.10), Thm 5.6.1; Thm 5.6.2 with (5.6.12)–(5.6.21) as a surface-only variant | `Numlib/Krylov/{Subspace,Iterate,CG}.lean`; `Numlib/Krylov/Convergence/{Polynomial,CG}.lean`; `Numlib/LinearSolve/Projection/{Basic,Optimality,OneDimensional}.lean`; `Numlib/InnerProductSpace/{Coercive,Energy}.lean`; `Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean` |

§5.5 gets no file (a module docstring in `Calculus.lean` records the summary). `IntegralEquations.lean`
belongs to phase 3 (`plans/backbone.md` §7, §8.3); its Mathlib-only parts (existence and uniqueness
in Thm 5.2.4) can be stated earlier.

## 1. Book-specific definitions

### D1. Contractive / non-expansive / Lipschitz (Def 5.1.2)
*Book.* `T : K ⊂ V → V`; contractive with constant `α ∈ [0,1)`: `‖T u − T v‖ ≤ α ‖u − v‖ ∀ u v ∈ K`;
non-expansive: `α = 1`; Lipschitz: some `L ≥ 0`. Implications contractive ⇒ non-expansive ⇒ Lipschitz
⇒ continuous.
*Lean.*
```lean
def ContractiveOn (T : V → V) (K : Set V) (α : ℝ) : Prop :=
  0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ α * ‖u - v‖
def NonExpansiveOn (T : V → V) (K : Set V) : Prop := ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ ‖u - v‖
def LipschitzOn (T : V → V) (K : Set V) : Prop := ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ L * ‖u - v‖
```
*Counterpart.* Mathlib `LipschitzOnWith (K : ℝ≥0) T s`, `ContractingWith K f` (= `K < 1 ∧ LipschitzWith K f`,
`Mathlib/Topology/MetricSpace/Contracting.lean`). The backbone's subset versions of the fixed-point
theorem (`exists_unique_fixedPoint_of_mapsTo`, `dist_iterate_le_of_mapsTo`,
`Numlib/Nonlinear/FixedPoint.lean`) take the contraction hypothesis unbundled, as
`0 ≤ K`, `K < 1`, `∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y` — `ContractiveOn` up to `dist_eq_norm`.
*Equivalence lemmas.* `ContractiveOn.dist_le (h : ContractiveOn T K α) : ∀ u ∈ K, ∀ v ∈ K, dist (T u) (T v) ≤ α * dist u v`
(`dist_eq_norm`); `contractiveOn_iff (hα : 0 ≤ α) : ContractiveOn T K α ↔ α < 1 ∧ LipschitzOnWith ⟨α, hα⟩ T K`
(`lipschitzOnWith_iff_norm_sub_le`); `ContractiveOn.contractingWith_restrict (h) (hT : MapsTo T K K) :
ContractingWith ⟨α, h.1⟩ (hT.restrict T K K)` (contraction of the restricted self-map of the subtype `↥K`);
`lipschitzOn_iff : LipschitzOn T K ↔ ∃ L : ℝ≥0, LipschitzOnWith L T K`; `ContractiveOn.nonExpansiveOn`,
`NonExpansiveOn.lipschitzOn`, `LipschitzOn.continuousOn` (`LipschitzOnWith.continuousOn`).

### D2. Fixed-point iteration (5.1.1)
*Book.* `u_{n+1} = T(u_n)`, `u_0 ∈ K`, requires `T(K) ⊂ K` (5.1.2). *Lean.* `T^[n] u₀` (`Nat.iterate`),
invariance `Set.MapsTo T K K` (then `Set.MapsTo.iterate`). No new definition.

### D3. Strongly monotone, Lipschitz operator (5.1.8)–(5.1.9)
*Book.* `(T v₁ − T v₂, v₁ − v₂) ≥ c₁ ‖v₁ − v₂‖²`, `‖T v₁ − T v₂‖ ≤ c₂ ‖v₁ − v₂‖`, real Hilbert space.
*Lean.* `def StronglyMonotoneWith (T : V → V) (c₁ : ℝ) : Prop := ∀ v₁ v₂, c₁ * ‖v₁ - v₂‖ ^ 2 ≤ inner ℝ (T v₁ - T v₂) (v₁ - v₂)`;
Lipschitz as `∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖` (= `LipschitzWith` up to `ℝ≥0`).
*Counterpart.* Backbone `zarantonello` (`Numlib/Nonlinear/FixedPoint.lean`) takes the hypotheses as
`hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y))` and
`hlip : LipschitzWith (Real.toNNReal L) T`; the linear case is `LinearMap.IsCoerciveWith A c`
(`Numlib/Analysis/InnerProductSpace/Coercive.lean`).
*Equivalence.* `stronglyMonotoneWith_iff : StronglyMonotoneWith T c ↔ ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner ℝ (T x - T y) (x - y))`
(`RCLike.re_to_real`); `stronglyMonotoneWith_iff_isCoerciveWith (A : V →L[ℝ] V) : StronglyMonotoneWith A c ↔ (A : V →ₗ[ℝ] V).IsCoerciveWith c`
(`map_sub`); `lipschitzWith_toNNReal_iff (hc : 0 ≤ c₂) : (∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖) ↔ LipschitzWith (Real.toNNReal c₂) T`
(`LipschitzWith.of_dist_le_mul`, `Real.coe_toNNReal`).

### D4. Matrix splitting and iteration matrix (§5.2.2)
*Book.* `A = N − M`, `N` nonsingular; iteration `N x_n = M x_{n−1} + b`, i.e. `x_n = N⁻¹M x_{n−1} + N⁻¹b`;
iteration matrix `N⁻¹M`; spectral radius `r_σ(A) = max |λ_i(A)|`; operator norm (5.2.6).
*Lean.* `structure BookSplitting (A : Matrix m m ℝ) where (N M : Matrix m m ℝ) (eq : A = N - M) (hN : IsUnit N)`;
`iterMatrix s := s.N⁻¹ * s.M`; `iterStep s b x := s.N⁻¹ * s.M *ᵥ x + s.N⁻¹ *ᵥ b`;
`rσ (A : Matrix m m ℝ) : ℝ≥0∞ := Matrix.complexSpectralRadius A` (`= spectralRadius ℂ (A.map Complex.ofReal)`
by definition).
*Counterpart.* Backbone `Stationary.Splitting a` (`Numlib/LinearSolve/Stationary/Splitting.lean`, any ring):
fields `m`, `isUnit : IsUnit m`, with `n := m - a` and `iterationOperator := 1 - Ring.inverse m * a`
(`= Ring.inverse m * n` by `Splitting.iterationOperator_eq`) — **note the naming swap**: backbone
`a = m − n` with `IsUnit m` versus the book's `A = N − M` with `N` nonsingular. `Stationary.step G f x = G x + f`
(`Numlib/LinearSolve/Stationary/Basic.lean`, `G : E →L[𝕜] E`). Spectral radius of real matrices:
`Matrix.complexify A = A.map Complex.ofReal` and `Matrix.complexSpectralRadius A = spectralRadius ℂ (complexify A)`
(`Numlib/LinearAlgebra/Matrix/Complexify.lean`, with `complexify_pow`, `tendsto_pow_iff_complexSpectralRadius_lt_one`).
Operator norm (5.2.6): Mathlib `ContinuousLinearMap.opNorm` via `Matrix.toLin'`; the ∞-norm instance
`Matrix.Norms.Operator` (`linfty_opNorm_*`).
*Equivalence.* `BookSplitting.toSplitting (s) : Stationary.Splitting A := ⟨s.N, s.hN⟩`;
`toSplitting_n : s.toSplitting.n = s.M` (from `s.eq`);
`toSplitting_iterationOperator : s.toSplitting.iterationOperator = s.N⁻¹ * s.M`
(`Splitting.iterationOperator_eq`, `Matrix.nonsing_inv_eq_ringInverse`);
`iterStep_eq_stationary_step : iterStep s b = Stationary.step (toLin' (s.N⁻¹ * s.M)) (s.N⁻¹ *ᵥ b)`.

### D5. Integral operators on `C[a,b]` (§5.2.3–5.2.4)
*Book.* Linear Fredholm `u ↦ (1/λ)∫ₐᵇ k(x,y)u(y)dy + f/λ` (5.2.9); Urysohn `T u (x) = μ ∫ₐᵇ k(x,y,u(y)) dy + f(x)`
(5.2.10)/(5.2.13); Volterra `T u (t) = ∫ₐᵗ k(t,s,u(s)) ds + f(t)` (5.2.15)/(5.2.16); Picard
`T u (t) = z + ∫_{t₀}^t f(s,u(s)) ds` (5.2.19)/(5.2.20); Bielecki norm `|||v||| = max e^{−βt}|v(t)|`.
*Lean.* Carrier `C(Set.Icc a b, ℝ)` (sup norm, complete: `ContinuousMap` normed-space instances on a compact
domain); bare-function form
`urysohnFun (hab : a ≤ b) (μ) (k : ℝ → ℝ → ℝ → ℝ) (f u : C(Icc a b, ℝ)) : Icc a b → ℝ := fun x => μ * ∫ y in a..b, k x y (u (Set.projIcc a b hab y)) + f x`,
bundled to `C(Icc a b, ℝ)` with `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
(`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`; needs `k` continuous). Same shape for
Volterra (`∫ y in a..x`, use `..._of_continuous` with `s x = x`) and Picard (values in `V`).
Bielecki norm: type synonym `Bielecki (β : ℝ) (X)` of `C(Icc a b, V)` with `‖v‖ = ⨆ t, exp (−β t) ‖v t‖`.
*Counterpart.* None in Mathlib or the backbone; the bundled operators, their Lipschitz bounds and the
Bielecki norm form the phase-3 integral-operator toolkit (`plans/backbone.md` §7, §8.3; §3 item 1).
Mathlib's `IsPicardLindelof.FunSpace` (`Mathlib/Analysis/ODE/PicardLindelof.lean`) is an internal
instance of the same construction (iterate-contraction, `exists_contractingWith_iterate_next`).

### D6. Fréchet derivative (Def 5.3.1), higher derivatives
*Book.* `f : K ⊂ V → W`, `u₀` interior (closed ball `B(u₀,r) ⊂ K`), `A ∈ L(V,W)` with
`f(u₀+h) = f(u₀) + Ah + o(‖h‖)`; `f' : K₀ → L(V,W)`; `f'' = (f')' : K₀ → L(V, L(V,W)) ≅ L(V×V, W)`.
*Lean.* Mathlib `HasFDerivAt f A u₀` with `A : V →L[ℝ] W`; on `K`: `HasFDerivWithinAt f A K u₀`, and the
book's interior-point convention is `K ∈ 𝓝 u₀` (`Metric.closedBall_mem_nhds`). `f''`: `HasFDerivAt f' (f'' u) u`
with `f'' u : V →L[ℝ] V →L[ℝ] W` (curried form; bilinear view via `ContinuousLinearMap.flip`/`uncurry`;
Mathlib's `iteratedFDeriv ℝ 2` is the multilinear form).
*Equivalence.* `hasFDerivAt_iff_isLittleO_nhds_zero` (little-o form, literally (5.3.5));
`hasFDerivWithinAt_of_mem_nhds`/`HasFDerivWithinAt.hasFDerivAt (h) (hs : K ∈ 𝓝 u₀)` (interior point ⇒ the
within/at notions coincide); uniqueness `HasFDerivAt.unique`.

### D7. Gâteaux derivative (Def 5.3.2)
*Book.* `A ∈ L(V,W)` with `lim_{t→0} (f(u₀+th) − f(u₀))/t = A h` for every `h` (the Gâteaux derivative is
required to be bounded linear).
*Lean.* `def HasGateauxDerivAt (f : V → W) (A : V →L[ℝ] W) (u₀ : V) : Prop := ∀ h : V, HasLineDerivAt ℝ f (A h) u₀ h`.
*Counterpart.* Mathlib `HasLineDerivAt 𝕜 f f' x v` (`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`; no
bundled Gâteaux notion). *Equivalence.* `HasFDerivAt.hasGateauxDerivAt := fun h => hf.hasLineDerivAt h`;
uniqueness `HasGateauxDerivAt.unique` from `HasLineDerivAt.unique` + `ContinuousLinearMap.ext`;
`hasGateauxDerivAt_iff_tendsto : … ↔ ∀ h, Tendsto (fun t => t⁻¹ • (f (u₀ + t • h) - f u₀)) (𝓝[≠] 0) (𝓝 (A h))`
(`hasLineDerivAt_iff_tendsto_slope_zero`).

### D8. Partial derivatives (Def 5.3.14)
*Book.* `f : U × V → W`; `f_u(u₀,v₀)` = derivative of `u ↦ f(u,v₀)` at `u₀`, similarly `f_v`.
*Lean.* `HasFDerivAt (fun u => f u v₀) (fu) u₀`, `HasFDerivAt (fun v => f u₀ v) (fv) v₀` (curried `f : U → V → W`).
*Counterpart.* Mathlib `Mathlib/Analysis/Calculus/FDeriv/Partial.lean` (`hasStrictFDerivAt_uncurry_coprod`),
`hasFDerivAt_prodMk_left/right`, `ContinuousLinearMap.coprod`. Formula (5.3.8) is `(fu.coprod fv) (h, k) = fu h + fv k`.

### D9. Convex functional and its Gâteaux derivative pairing (§5.3.4)
*Book.* `f : K → ℝ` on a convex `K`, `⟨f'(u), v⟩` with `f'(u) ∈ V'`. *Lean.* `ConvexOn ℝ K f`,
`StrictConvexOn ℝ K f`; `f' : V → V →L[ℝ] ℝ`, pairing = application `f' u v`; minimiser `IsMinOn f K u`.
*Counterpart.* Mathlib `ConvexOn`, `IsMinOn`; the derivative characterisations are only in 1D
(`Mathlib/Analysis/Convex/Deriv.lean`: `MonotoneOn.convexOn_of_deriv`, `ConvexOn.slope_mono`); the
normed-space versions are surface lemmas (Thm 5.3.17–5.3.19).

### D10. Newton iteration (5.4.2)
*Book.* `u_{n+1} = u_n − [F'(u_n)]⁻¹ F(u_n)`, `F : U → W` Fréchet differentiable, `U, W` Banach.
*Lean.* The book's iteration is the backbone's `Newton.step`/`Newton.iterate` (`Numlib/Nonlinear/Newton.lean`):
```lean
noncomputable def Newton.step (Fn : E → F) (F' : E → E →L[𝕜] F) (x : E) : E := x - (F' x).inverse (Fn x)
noncomputable def Newton.iterate (Fn : E → F) (F' : E → E →L[𝕜] F) (x₀ : E) (k : ℕ) : E := (step Fn F')^[k] x₀
```
using Mathlib `ContinuousLinearMap.inverse` (`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean`;
`= e.symm` on invertible maps by `ContinuousLinearMap.inverse_equiv`, `= 0` otherwise). The surface uses
them directly with `𝕜 = ℝ`, `E = U`, `F = W` (no book-specific definition); `Newton.iterate_succ` is (5.4.2)
and `Newton.step_eq_self_of_eq_zero` says that roots are fixed points. "Well-defined" =
`∀ n, ∃ e : U ≃L[ℝ] W, ↑e = F' (Newton.iterate F F' u₀ n)`.
Surface lemma `newtonStep_sub_eq (he : ↑e = F' u) : (F' u) (Newton.step F F' u - u) = -F u` (the form
`F'(x_n) δ_n = −F(x_n)` of (5.4.7)/(5.4.9)).

### D11. Conjugate gradient iteration (5.6.2)
*Book.* Real Hilbert space `V`, `A` bounded self-adjoint positive definite; `r₀ = f − A u₀`, `s₀ = r₀`;
`α_k = ‖r_k‖²/(A s_k, s_k)`, `u_{k+1} = u_k + α_k s_k`, `r_{k+1} = f − A u_{k+1}`, `β_k = ‖r_{k+1}‖²/‖r_k‖²`,
`s_{k+1} = r_{k+1} + β_k s_k`.
*Lean.*
```lean
structure CGState (V : Type*) where (u r s : V)
noncomputable def cgStep (A : V →L[ℝ] V) (f : V) (st : CGState V) : CGState V :=
  let α := ‖st.r‖ ^ 2 / inner ℝ (A st.s) st.s
  let u' := st.u + α • st.s
  let r' := f - A u'
  let β := ‖r'‖ ^ 2 / ‖st.r‖ ^ 2
  ⟨u', r', r' + β • st.s⟩
noncomputable def cg (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) : CGState V := (cgStep A f)^[k] ⟨u₀, f - A u₀, f - A u₀⟩
```
(Lean's `x / 0 = 0` makes the recurrences total; after breakdown `r_k = 0` both `α_k` and `β_k` are `0`
and the iterate is frozen — same convention as the backbone.)
*Counterpart.* Backbone `CG.State`, `CG.step`, `CG.init`, `CG.iterate A b x₀ k`, `CG.alpha`, `CG.beta`
(`Numlib/Krylov/CG.lean`, `A : E →ₗ[𝕜] E`): `α = ⟪r, r⟫ / ⟪A p, p⟫` (`𝕜`-valued) and `r' = r − α A p` (`CG.step_r`).
*Equivalence.* `cg_eq_CG_iterate : cg A f u₀ k = ⟨(CG.iterate ↑A f u₀ k).x, (CG.iterate ↑A f u₀ k).r, (CG.iterate ↑A f u₀ k).p⟩`
— by induction on `k` with `CG.iterate_succ`, `CG.residual_eq` (the book's explicit `r_{k+1} = f − A u_{k+1}`
versus the backbone's `r_k − α_k A p_k`) and `real_inner_self_eq_norm_sq` for `⟪r,r⟫ = ‖r‖²`.

### D12. `A`-inner product and `A`-norm (§5.6)
*Book.* `(v,u)_A = (Av, u)`, `‖v‖_A = √(v,v)_A`. *Lean.* `innerA A v u := inner ℝ (A v) u`,
`normA A v := Real.sqrt (innerA A v v)`.
*Counterpart.* Backbone `energyInner (A : E →ₗ[𝕜] E) x y = inner 𝕜 (A x) y`, `energyNorm A x = √(re ⟪A x, x⟫)`
(`Numlib/Analysis/InnerProductSpace/Energy.lean`, scoped notation `⟪x, y⟫_[A]`, `‖x‖_[A]` in `Energy`).
*Equivalence.* `innerA_eq : innerA A v u = energyInner (A : V →ₗ[ℝ] V) v u` (`rfl`),
`normA_eq : normA A v = energyNorm (A : V →ₗ[ℝ] V) v` (`RCLike.re_to_real`).

### D13. Bounded self-adjoint positive definite operator; (5.6.3)
*Book.* `A ∈ L(V)` self-adjoint (`(Au,v) = (u,Av)`, real Hilbert space), positive definite in the sense that
Thm 5.1.4 applies, i.e. `(Av,v) ≥ c₁‖v‖²` (the book's (5.6.8) confirms: "positive definite iff `δ = inf(1−λ_j) > 0`");
(5.6.3): `√m ‖v‖ ≤ ‖v‖_A ≤ √M ‖v‖`, `m, M > 0`.
*Lean.* `IsSelfAdjoint (A : V →L[ℝ] V)` (Mathlib, needs `[CompleteSpace V]`), hypothesis
`hbound : ∀ v, √m * ‖v‖ ≤ normA A v ∧ normA A v ≤ √M * ‖v‖`.
*Counterpart.* Backbone `LinearMap.IsSymmetricBoundedBy A m M` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`:
fields `isSymmetric`, `le_re_inner : m ‖x‖² ≤ re ⟪A x, x⟫`, `re_inner_le`), the hypothesis of every
Chebyshev-type bound; `LinearMap.IsSymmetricCoercive` via `IsSymmetricBoundedBy.isSymmetricCoercive (hm : 0 < m)`,
`LinearMap.IsCoerciveWith A m` via `IsSymmetricBoundedBy.isCoerciveWith`.
*Equivalence.* `isSelfAdjoint_iff_isSymmetric : IsSelfAdjoint A ↔ (A : V →ₗ[ℝ] V).IsSymmetric`
(Mathlib `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, `Adjoint.lean`);
`bound_iff : (∀ v, √m ‖v‖ ≤ ‖v‖_A ∧ ‖v‖_A ≤ √M ‖v‖) ↔ (∀ v, m ‖v‖² ≤ ⟪A v, v⟫ ∧ ⟪A v, v⟫ ≤ M ‖v‖²)`
(`Real.sqrt_le_sqrt`, `Real.sqrt_le_left`, `pow_le_pow_left`); hence
`isSymmetricBoundedBy_iff : IsSelfAdjoint A ∧ (∀ v, √m ‖v‖ ≤ ‖v‖_A ∧ ‖v‖_A ≤ √M ‖v‖) ↔ (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy m M`
(`RCLike.re_to_real`).

### D14. Compact / completely continuous nonlinear operators (Def 5.5.3) — summary only
Mathlib has `IsCompactOperator` for linear maps; the nonlinear notion, Brouwer/Schauder and the rotation are out
of scope (no Mathlib support; `Brouwer` does not occur in Mathlib outside order theory).

## 2. Results

Numbered results in book order. Each block: **Book statement** / **Lean surface statement** (sketch) /
**Backbone/Mathlib item** / **Proof route** / **Classification**.

### §5.1 The Banach fixed-point theorem

**Ex 5.1.1** (affine map on ℝ).
Book: `T x = a x + b`; `x_n = x₀ + n b` if `a = 1`, `x_n = aⁿ x₀ + (1 − aⁿ)/(1 − a) b` if `a ≠ 1`; for `a ≠ 1`
the iteration converges iff `|a| < 1`.
Lean: `theorem ex_5_1_1 (a b x₀ : ℝ) (h : a ≠ 1) : (fun x => a * x + b)^[n] x₀ = a ^ n * x₀ + (1 - a ^ n) / (1 - a) * b`
and `(∀ x₀, ∃ x, Tendsto (fun n => (fun x => a*x+b)^[n] x₀) atTop (𝓝 x)) ↔ |a| < 1`.
Mathlib: `tendsto_pow_atTop_nhds_zero_iff`, `geom_sum_eq`. Route: induction + geometric series.
Classification: `surface-only` (trivial; optional).

**Def 5.1.2 implications** (contractive ⇒ non-expansive ⇒ Lipschitz ⇒ continuous).
Lean: `ContractiveOn.nonExpansiveOn`, `NonExpansiveOn.lipschitzOn`, `LipschitzOn.continuousOn`.
Mathlib: `LipschitzOnWith.continuousOn`. Classification: `direct`.

**Thm 5.1.3 (Banach fixed-point theorem)**.
Book: `K` nonempty closed in a Banach space `V`, `T : K → K` contractive with constant `α ∈ [0,1)`. (1) ∃! `u ∈ K`,
`u = T u`. (2) for any `u₀ ∈ K`, `u_n → u`, and
(5.1.4) `‖u_n − u‖ ≤ αⁿ/(1−α) ‖u₀ − u₁‖`, (5.1.5) `‖u_n − u‖ ≤ α/(1−α) ‖u_{n−1} − u_n‖`, (5.1.6) `‖u_n − u‖ ≤ α ‖u_{n−1} − u‖`.
Lean:
```lean
theorem thm_5_1_3 [CompleteSpace V] {K : Set V} (hK : IsClosed K) (hne : K.Nonempty)
    {T : V → V} (hT : Set.MapsTo T K K) {α : ℝ} (hα : ContractiveOn T K α) :
    (∃! u, u ∈ K ∧ T u = u) ∧
    ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
      (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧                       -- (5.1.4)
      (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧           -- (5.1.5)
      (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖)                                 -- (5.1.6)
```
Backbone (`Numlib/Nonlinear/FixedPoint.lean`):
`exists_unique_fixedPoint_of_mapsTo (hs : IsClosed s) (hne : s.Nonempty) (hmaps : Set.MapsTo f s s) (hK0 : 0 ≤ K) (hK : K < 1) (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) : ∃! x, x ∈ s ∧ f x = x`
— (1); `dist_iterate_le_of_mapsTo (hs) (hmaps) (hK0) (hK) (hf) (hx' : x' ∈ s) (hfix : f x' = x') (hx₀ : x₀ ∈ s) (n) : dist (f^[n] x₀) x' ≤ K ^ n / (1 - K) * dist (f x₀) x₀`
— (5.1.4) (`dist_comm` for the book's `‖u₀ − u₁‖`). Whole-space forms in Mathlib: `ContractingWith.fixedPoint`,
`fixedPoint_isFixedPt`, `fixedPoint_unique`, `tendsto_iterate_fixedPoint`, `apriori_dist_iterate_fixedPoint_le`,
`aposteriori_dist_iterate_fixedPoint_le`, and the backbone's `ContractingWith.dist_iterate_succ_fixedPoint_le` ((5.1.6)).
Route: `hα.dist_le` (D1) feeds both backbone lemmas. (5.1.6): `T^[n] u₀ ∈ K` (`Set.MapsTo.iterate`) and
`T u = u`, so `hα` gives it in one line. (5.1.5): `‖u_{n+1} − u‖ ≤ ‖u_{n+1} − u_{n+2}‖ + ‖u_{n+2} − u‖ ≤ α ‖u_n − u_{n+1}‖ + α ‖u_{n+1} − u‖`,
then `(1 − α) ‖u_{n+1} − u‖ ≤ α ‖u_n − u_{n+1}‖`. Convergence: (5.1.4) with `tendsto_pow_atTop_nhds_zero_of_lt_one`
and `squeeze_zero`.
Classification: `direct` ((1), (2), (5.1.4)); `surface-only` ((5.1.5), (5.1.6): the short inequalities above).
The book's unusual `n = 0` case of (5.1.5)/(5.1.6) is avoided by indexing with `n + 1` (the book states them
for `n ≥ 1`).

**Ex 5.1.2** (`Tᵐ` contractive; cited by Thm 5.2.3).
Book: `K` nonempty closed, `T : K → K` continuous, `Tᵐ` a contraction for some `m ≥ 1` ⇒ `T` has a unique fixed
point in `K` and `u_{n+1} = T u_n` converges.
Lean: `theorem ex_5_1_2 … (hc : ContinuousOn T K) {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : ContractiveOn (T^[m]) K α) : (∃! u, u ∈ K ∧ T u = u) ∧ ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u)`.
Backbone (`Numlib/Nonlinear/FixedPoint.lean`, whole space):
`exists_unique_fixedPoint_of_iterate_contractingWith [Nonempty α] [CompleteSpace α] (hT : Continuous T) (hm : 0 < m) (hK : ContractingWith K T^[m]) : ∃! x, T x = x`
(`[Nonempty α]` is needed: the empty metric space is complete and every self-map of it is a
contraction, so unique existence fails there; on the subtype `↥K` it comes from the book's "`K`
nonempty") and `tendsto_iterate_of_iterate_contractingWith [CompleteSpace α] (hT) (hm) (hK) (x) : ∃ x', T x' = x' ∧ Tendsto (fun n => T^[n] x) atTop (𝓝 x')`
(nonemptiness is supplied there by the point `x`; the `m` subsequences
`T^[k m + j] u₀ = (T^[m])^[k] (T^[j] u₀)` converge to the `T^[m]`-fixed point, glued by
`Nat.mod_add_div`; continuity of `T` is not needed for the conclusion but is kept for faithfulness).
Route: work on the subtype `↥K` (complete by `IsClosed.completeSpace_coe`) with the restricted map
`hT.restrict T K K` (`hc.restrict` continuous), `(hT.restrict T K K)^[m] = (hT.iterate m).restrict …`
(`Set.MapsTo.iterate_restrict`) and D1's `contractingWith_restrict` applied to `T^[m]`; map the fixed point
and the limit back with `Subtype.val` (`continuous_subtype_val`).
Classification: `needs-equivalence` (subtype transfer via D1).

**Thm 5.1.4** (strongly monotone + Lipschitz ⇒ bijective; real Hilbert space).
Book: `V` Hilbert, `T : V → V` with (5.1.8) `(T v₁ − T v₂, v₁ − v₂) ≥ c₁‖v₁ − v₂‖²` and (5.1.9)
`‖T v₁ − T v₂‖ ≤ c₂‖v₁ − v₂‖`, `c₁, c₂ > 0`. Then ∀ `b`, ∃! `u` with `T u = b` (5.1.10), and (5.1.11)
`‖u₁ − u₂‖ ≤ (1/c₁)‖b₁ − b₂‖` when `T u_i = b_i`.
Lean:
```lean
theorem thm_5_1_4 {T : V → V} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hmono : StronglyMonotoneWith T c₁) (hlip : ∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖) :
    (∀ b, ∃! u, T u = b) ∧ ∀ u₁ u₂ b₁ b₂, T u₁ = b₁ → T u₂ = b₂ → ‖u₁ - u₂‖ ≤ (1 / c₁) * ‖b₁ - b₂‖
```
Backbone (`Numlib/Nonlinear/FixedPoint.lean`): `zarantonello (hc : 0 < c) (hmono) (hlip : LipschitzWith (Real.toNNReal L) T) (b) : ∃! x, T x = b`
— (5.1.10); `norm_sub_le_of_strongly_monotone (hc) (hmono) (h₁ : T x₁ = b₁) (h₂ : T x₂ = b₂) : ‖x₁ - x₂‖ ≤ ‖b₁ - b₂‖ / c`
— (5.1.11); the proof's damped map `x ↦ x − θ (T x − b)` contracts with factor `√(1 − 2θc + θ²L²)` for
`0 < θ < 2c/L²` (`contractingWith_damped`; then Thm 5.1.3 with `K = V`). Linear special case:
`ContinuousLinearMap.exists_equiv_of_isCoerciveWith` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`).
Route: D3's `stronglyMonotoneWith_iff` and `lipschitzWith_toNNReal_iff`; `(1/c₁) ‖b₁ − b₂‖ = ‖b₁ − b₂‖ / c₁`.
Classification: `needs-equivalence` (D3). The book's proof swaps the constants — see §5.

### §5.2 Applications to iterative methods

**Thm 5.2.1** (scalar contraction on `[a,b]`).
Book: `T : [a,b] → [a,b]` contractive with `α ∈ [0,1)`: unique fixed point, convergence, the three bounds.
Lean (`thm_5_2_1`): Thm 5.1.3 with `V = ℝ`, `K = Icc a b`, `|·|` for `‖·‖`.
Mathlib: `isClosed_Icc`, `Set.nonempty_Icc`. Classification: `direct` (specialisation of `thm_5_1_3`).

**Thm 5.2.1, derivative criterion** ("`sup_{[a,b]} |T'| < 1` ⇒ contractive with that constant").
Lean: `thm_5_2_1_deriv (hT : ∀ x ∈ Icc a b, HasDerivWithinAt T (T' x) (Icc a b) x) (hα : ∀ x ∈ Icc a b, |T' x| ≤ α) (h1 : α < 1) : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |T x - T y| ≤ α * |x - y|`.
Backbone: `lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex ℝ s) (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hT' : ∀ x ∈ s, ‖T' x‖₊ ≤ q) : LipschitzOnWith q T s`
(`Numlib/Nonlinear/FixedPoint.lean`), applied with `T' x := (1 : ℝ →L[ℝ] ℝ).smulRight (T' x)`
(`hasDerivWithinAt_iff_hasFDerivWithinAt`, `ContinuousLinearMap.norm_smulRight_apply`); or Mathlib
`Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` (`MeanValue.lean`) directly, with `convex_Icc`.
Classification: `direct`.

**§5.2.2 (a)** error equation (5.2.5) `x − x_n = (N⁻¹M)ⁿ (x − x₀)`.
Lean: `theorem eq_5_2_5 (s : BookSplitting A) (hx : A *ᵥ x = b) (x₀) (n) : x - (iterStep s b)^[n] x₀ = (s.N⁻¹ * s.M) ^ n *ᵥ (x - x₀)`.
Backbone: `Stationary.step_iterate_sub (hfix : G x' + f = x') (x₀) (k) : (step G f)^[k] x₀ - x' = (G ^ k) (x₀ - x')`
(`Numlib/LinearSolve/Stationary/Basic.lean`) through D4's `iterStep_eq_stationary_step` and `Matrix.toLin'_pow`;
otherwise a five-line induction. Classification: `needs-equivalence` (D4).

**§5.2.2 (b)** "converges if `‖N⁻¹M‖ < 1`" (any induced norm).
Lean: `theorem tendsto_of_opNorm_lt_one (hG : ‖toLin' (s.N⁻¹ * s.M)‖ < 1) (hx : A *ᵥ x = b) (x₀) : Tendsto (fun n => (iterStep s b)^[n] x₀) atTop (𝓝 x)`.
Backbone: `Stationary.contractingWith (hG : ‖G‖ < 1) : ContractingWith ⟨‖G‖, _⟩ (step G f)` with the a priori /
a posteriori bounds `Stationary.norm_iterate_sub_le`, `norm_iterate_sub_le'` and the fixed-point
identification `Stationary.step_fixed_iff` (`Numlib/LinearSolve/Stationary/Basic.lean`); convergence by
`ContractingWith.tendsto_iterate_fixedPoint`. Alternatively `thm_5_1_3` with `K = univ`.
Classification: `needs-equivalence` (D4).

**§5.2.2 (c)** "`Aⁿ → 0` iff `r_σ(A) < 1`" (square matrices).
Backbone: `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one (A : Matrix n n ℝ) : Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ complexSpectralRadius A < 1`
(`Numlib/LinearAlgebra/Matrix/Complexify.lean`) — literally the book's statement with `rσ = complexSpectralRadius` (D4).
For complex Banach algebras: `spectralRadius_lt_one_iff_tendsto_pow` (`Numlib/Analysis/Normed/Algebra/SpectralRadius.lean`).
Classification: `direct`.

**§5.2.2 (d)** "converges for every `x₀` iff `(N⁻¹M)ⁿ → 0`", hence iff `r_σ(N⁻¹M) < 1`.
Lean: `(∀ x₀, Tendsto … (𝓝 x)) ↔ Tendsto (fun n => (s.N⁻¹ * s.M) ^ n) atTop (𝓝 0)`; from (5.2.5) (⇐ direct; ⇒ apply to
`x₀ = x − e_i` and use `Matrix.mulVec`-basis vectors / `Pi.tendsto_iff`), then (c). Classification: `surface-only`
(finite-dimensional argument; the complex operator form is `Stationary.forall_tendsto_iff_spectralRadius_lt_one`,
`Numlib/LinearSolve/Stationary/Basic.lean`).

**§5.2.2 relation 1** `r_σ(A) ≤ ‖A‖` for any operator norm.
Mathlib: `spectrum.spectralRadius_le_nnnorm` (`Mathlib/Analysis/Normed/Algebra/Spectrum.lean`) for the
Banach-algebra norm; real matrices: `Matrix.complexSpectralRadius_le_of_norm` (`Numlib/LinearAlgebra/Matrix/Complexify.lean`,
under `[NormedRing (Matrix n n ℝ)]`, `[NormOneClass (Matrix n n ℝ)]` and `[NormedAlgebra ℝ (Matrix n n ℝ)]`;
submultiplicativity with `‖1‖ = 1` alone does not give `ℝ`-homogeneity and the bound then fails, but
every scoped matrix norm carries all three).
Classification: `direct` (for the norm instance in scope), `surface-only` for "any" induced norm (quantify over a
`NormedAlgebra ℂ (Matrix n n ℂ)` instance — awkward; state for the three Mathlib norms).

**§5.2.2 relation 2** (`∀ ε ∃` operator norm with `‖A‖ ≤ r_σ + ε`; `r_σ = inf` over operator norms).
Classification: `out-of-scope` (no Mathlib support; the backbone replaces it by Gelfand, `plans/backbone.md` §2.3.1).

**§5.2.2 relation 3** Gelfand `r_σ(A) = lim ‖Aⁿ‖^{1/n}` for any matrix norm.
Mathlib: `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (ℂ, Banach-algebra norm). Real matrices:
`Matrix.complexify_pow` (`Numlib/LinearAlgebra/Matrix/Complexify.lean`) and `‖complexify B‖ = ‖B‖` for the norm instance in
scope (entrywise for the three Mathlib norms), then the complex formula.
Classification: `direct` (complex matrices, algebra norm); `surface-only` (real matrices; the "any matrix norm"
generality via norm equivalence, `LinearEquiv.toContinuousLinearEquiv` constants).

**§5.2.2 Jacobi / Gauss–Seidel / SOR** (definitions `A = D + L + U`, `N = D`, `N = D + L`, `N = D/ω + L`).
Lean: `Matrix.diagPart`, `strictLower`, `strictUpper` (`Numlib/LinearAlgebra/Matrix/Hessenberg.lean`, `[LinearOrder n]`;
`A = D + L + U` is `diagPart_add_strictLower_add_strictUpper`), the three `BookSplitting`s and the componentwise
formulas as `Matrix.mulVec` lemmas.
Backbone: `Matrix.jacobiSplitting A h`, `gaussSeidelSplitting A h`, `sorSplitting A h hω`
(`Numlib/LinearSolve/Stationary/Splitting.lean`, `h : IsUnit (diagPart A)`), whose `m` fields are exactly the
book's `N`. Equivalence: `(jacobi A h).toSplitting = Matrix.jacobiSplitting A h` etc. by `Stationary.Splitting.ext`.
Classification: `needs-equivalence` (definitions only; no theorem in the book here).

**§5.2.3 linear Fredholm equation** (5.2.7)–(5.2.9): contractivity constant `α = (1/|λ|) max_x ∫ₐᵇ |k(x,y)| dy`,
condition (5.2.8) `α < 1`.
Lean: `fredholmFun`/`fredholmOp` on `C(Icc a b, ℝ)`; `lemma lipschitz_fredholmOp : ‖T u − T v‖ ≤ α ‖u − v‖`.
Route: `intervalIntegral.norm_integral_le_of_norm_le_const` pointwise then `ContinuousMap.norm_le`.
Classification: `deferred` (phase 3, `C[a,b]` integral-operator toolkit — §3 item 1).

**Thm 5.2.2 (Urysohn equation)**.
Book: `f ∈ C[a,b]`, `k ∈ C([a,b]²×ℝ)` (5.2.11), uniform Lipschitz in the third argument with constant `M` (5.2.12),
`|μ| M (b − a) < 1` ⇒ unique solution `u ∈ C[a,b]` of (5.2.10), approximated by (5.2.13).
Lean (`thm_5_2_2`, operator supplied as a bundled map agreeing with `urysohnFun`):
`(∃! u, T u = u) ∧ ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u)`.
Route: `thm_5_1_3` with `K = univ`; Lipschitz bound `‖T u − T v‖ ≤ |μ| M (b−a) ‖u − v‖` from
`intervalIntegral.norm_integral_le_of_norm_le_const` and `ContinuousMap.norm_coe_le_norm`.
Classification: `deferred` (phase 3: bundling `T` into `C(Icc a b, ℝ)` and its Lipschitz bound are the
toolkit's first lemmas — §3 item 1).

**Thm 5.2.3 (nonlinear Volterra equation)**.
Book: `k` continuous on `{a ≤ s ≤ t ≤ b} × ℝ`, `f ∈ C[a,b]`, Lipschitz in `u` with constant `M` (no smallness) ⇒ unique
solution in `C[a,b]`, iteration (5.2.16) converges for every `u₀`.
Lean: same shape as `thm_5_2_2` with `volterraFun hab k f u x := ∫ y in a..x, k x y (u (projIcc y)) + f x` and no `μ`-hypothesis.
Route (book Approach 1): `|Tᵐu(t) − Tᵐv(t)| ≤ (M(t−a))ᵐ/m! ‖u−v‖_∞` by induction (`intervalIntegral.integral_mono`,
`integral_pow`), so `T^[m]` contracts for large `m` (`Real.tendsto_pow_div_factorial_atTop`), then Ex 5.1.2 — the
backbone's `tendsto_iterate_of_iterate_contractingWith` is the engine. Approach 2 (Bielecki):
`ContractingWith (M/β) T` on the type synonym `Bielecki β C(Icc a b, ℝ)`. Mathlib's
`IsPicardLindelof.FunSpace.dist_iterate_next_apply_le` proves exactly the factorial estimate for the Picard
operator and is the template.
Classification: `deferred` (phase 3: the factorial estimate / Bielecki norm of the toolkit — §3 item 1).

**Thm 5.2.4 (generalized Picard–Lindelöf)**.
Book: `V` Banach, `Q_b = {(t,u) : |t − t₀| ≤ a, ‖u − z‖ ≤ b}`, `f : Q_b → V` continuous, Lipschitz in `u` with constant
`L`, `M = max_{Q_b} ‖f‖`, `a₀ = min(a, b/M)`. Then (5.2.18) has a unique `C¹` solution on `[t₀ − a₀, t₀ + a₀]`;
the Picard iteration (5.2.20) converges for any `u₀` with `‖z − u₀‖ < b`; with `α = 1 − e^{−L a₀}` the weighted error
`max_{|t−t₀|≤a₀} ‖u_n(t) − u(t)‖ e^{−L|t−t₀|}` satisfies the three bounds (5.1.4)–(5.1.6) in the weighted norm.
Lean (existence/uniqueness part, `thm_5_2_4_exists_unique`):
```lean
theorem thm_5_2_4_exists_unique {t₀ a b L M : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) {z : V} {f : ℝ → V → V}
    (hcont : ContinuousOn (Function.uncurry f) (Icc (t₀ - a) (t₀ + a) ×ˢ Metric.closedBall z b))
    (hlip : ∀ t ∈ Icc (t₀ - a) (t₀ + a), LipschitzOnWith (Real.toNNReal L) (f t) (Metric.closedBall z b))
    (hbound : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ∀ u ∈ Metric.closedBall z b, ‖f t u‖ ≤ M) :
    let a₀ := min a (b / M)
    ∃! u : ℝ → V, ContDiffOn ℝ 1 u (Icc (t₀ - a₀) (t₀ + a₀)) ∧ u t₀ = z ∧
      ∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀), HasDerivWithinAt u (f t (u t)) (Icc (t₀ - a₀) (t₀ + a₀)) t
```
(uniqueness among functions on `Icc`; state as `EqOn` on the interval if `∃!` over all of `ℝ → V` is too strong).
Mathlib: `IsPicardLindelof f t₀ x₀ a r L K` (fields `lipschitzOnWith`, `continuousOn`, `norm_le`, `mul_max_le : L * max (tmax − t₀) (t₀ − tmin) ≤ a − r`)
with `x₀ := z`, `a := b`, `r := 0`, `L := M`, `K := L`, `tmin/tmax := t₀ ∓ a₀` (then `M a₀ ≤ b`);
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` (existence), `contDiffOn_enat_Icc_of_hasDerivWithinAt`
(`C¹`), `ODE_solution_unique_of_mem_Icc` (uniqueness; Gronwall `norm_le_gronwallBound_of_norm_deriv_right_le`).
Mathlib's `IsPicardLindelof` is stated for any complete real normed space, so the book's generalised theorem is
literally Mathlib's.
Picard-iteration convergence and the three weighted bounds: not exposed by Mathlib (its proof goes through
`FunSpace.next` with iterate-contraction, not the Bielecki norm) — needs the `Bielecki`-norm type synonym on
`C(Icc (t₀−a₀) (t₀+a₀), V)`, the contraction `|||T u − T v||| ≤ (1 − e^{−L a₀}) |||u − v|||` and Thm 5.1.3 on the closed
ball `{u : ‖u(t) − z‖ ≤ b}`.
Classification: `direct` (existence, uniqueness, `C¹`); `deferred` (iteration + weighted bounds — phase 3, §3 item 1).

### §5.3 Differential calculus for nonlinear operators

**Def 5.3.1, uniqueness of the Fréchet derivative.** Mathlib `HasFDerivAt.unique`. Classification: `direct`.

**Prop 5.3.3** (Fréchet differentiable ⇒ continuous). `HasFDerivAt.continuousAt`. Classification: `direct`.

**Prop 5.3.4** (Fréchet ⇒ Gâteaux; converse under uniform limit or continuity of the Gâteaux derivative).
Lean: (i) `HasFDerivAt.hasGateauxDerivAt` (`HasFDerivAt.hasLineDerivAt`).
(ii) `hasFDerivAt_of_hasGateauxDerivAt_uniform (hG : HasGateauxDerivAt f A u₀) (hunif : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ = 1 → ∀ t, 0 < |t| → |t| < δ → ‖t⁻¹ • (f (u₀ + t • h) - f u₀) - A h‖ ≤ ε) : HasFDerivAt f A u₀`
— unfold `hasFDerivAt_iff_isLittleO_nhds_zero`, write `h = ‖h‖ • (‖h‖⁻¹ • h)`.
(iii) `hasFDerivAt_of_hasGateauxDerivAt_continuousAt (hG : ∀ᶠ u in 𝓝 u₀, HasGateauxDerivAt f (A u) u) (hA : ContinuousAt A u₀) : HasFDerivAt f (A u₀) u₀`
— standard: apply `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` to `t ↦ f (u₀ + t • h) − t • A u₀ h` on `[0,1]`
(line derivative `A (u₀ + t h) h − A u₀ h`, bounded by `sup ‖A(u₀+th) − A u₀‖ ‖h‖ = o(1)‖h‖`).
Mathlib has neither (ii) nor (iii). Classification: `direct` (i); `surface-only` (ii), (iii). A `HasGateauxDerivAt`
API is a candidate for the backbone once a second consumer (Kress Ch. 6, AH Ch. 11) is formalized — §3.

**Prop 5.3.5 (sum rule)** for Fréchet and Gâteaux derivatives.
Mathlib: `HasFDerivAt.add`, `HasFDerivAt.const_smul` (`FDeriv/Add.lean`); Gâteaux: unfold `HasLineDerivAt` (= `HasDerivAt` of
`t ↦ f (x + t • v)` at `0`) and use `HasDerivAt.add`, `HasDerivAt.const_smul`. Classification: `direct` (Fréchet);
`surface-only` (Gâteaux, one-liners).

**Prop 5.3.6 (product rule)** `B(u) = b(f₁ u, f₂ u)`, `b` bounded bilinear.
Mathlib: `IsBoundedBilinearMap.hasFDerivAt` + `HasFDerivAt.comp` + `HasFDerivAt.prodMk`, or the packaged
`ContinuousLinearMap.hasFDerivAt_of_bilinear` (`FDeriv/Bilinear.lean`, `b : V₁ →L[ℝ] V₂ →L[ℝ] W`); derivative
`h ↦ b (f₁' h) (f₂ u₀) + b (f₁ u₀) (f₂' h)`. Gâteaux case: `HasFDerivAt.comp_hasDerivAt` along the line.
Classification: `direct` (Fréchet; state `b` as `IsBoundedBilinearMap ℝ b` with equivalence to the curried CLM via
`IsBoundedBilinearMap.toContinuousLinearMap`); `surface-only` (Gâteaux).

**Prop 5.3.7 (chain rule)**. `HasFDerivAt.comp` (`FDeriv/Comp.lean`); Gâteaux∘Fréchet: `HasFDerivAt.comp_hasDerivAt`
on `t ↦ f (u₀ + t • h)`. Interior-point hypotheses are the `K ∈ 𝓝 u₀`, `L ∈ 𝓝 (f u₀)` reductions of D6.
Classification: `direct`.

**Ex 5.3.8** (affine `f v = L v + b` has `f' ≡ L`). `(L.hasFDerivAt).add_const b`. Classification: `direct`.

**Ex 5.3.9** (Jacobian). Classification: `out-of-scope` (see §4; Mathlib `hasFDerivAt_pi''`, `LinearMap.toMatrix'` give it under
`C¹` hypotheses the book does not state).

**Ex 5.3.10** (Fréchet derivative of the Urysohn operator). Classification: `out-of-scope` (an example; would need the
phase-3 integral-operator toolkit and differentiation under the integral sign, Mathlib
`hasFDerivAt_integral_of_dominated_of_fderiv_le`).

**Prop 5.3.11 (mean value inequality)**.
Book: `U, V` real Banach, `K` open, `F` differentiable on `K` with `F'` continuous, segment `[u,w] ⊂ K` ⇒
(5.3.7) `‖F u − F w‖ ≤ sup_{θ∈[0,1]} ‖F'((1−θ)u + θw)‖ ‖u − w‖`.
Lean (`prop_5_3_11`): `‖F u - F w‖ ≤ (⨆ θ : Icc (0:ℝ) 1, ‖F' ((1 - θ) • u + θ • w)‖) * ‖u - w‖`.
Mathlib: `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` with `s := segment ℝ u w` (`convex_segment`), bound `C := ⨆ …`
(`le_ciSup` needs `BddAbove`, from continuity of `F'` on the compact segment: `isCompact_segment`, `IsCompact.bddAbove_image`);
`segment_eq_image_lineMap`. Completeness and continuity of `F'` are only used to make the `sup` finite.
Classification: `direct`.

**Cor 5.3.12** (`F' ≡ 0` on a connected open set ⇒ `F` constant).
Mathlib: `IsOpen.is_const_of_fderiv_eq_zero (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s) (hf' : s.EqOn (fderiv 𝕜 f) 0) : f x = f y`
(`MeanValue.lean`; book "connected" = `IsPreconnected` for open sets). Classification: `direct`.

**Prop 5.3.13 (Taylor remainder)**.
Book: `F` twice continuously differentiable on open `K`, segment `[u₀, u₀+h] ⊂ K` ⇒
`‖F(u₀+h) − F(u₀) − F'(u₀)h‖ ≤ ½ sup_{θ} ‖F''(u₀+θh)‖ ‖h‖²`.
Lean (`prop_5_3_13`, `F'' : V → V →L[ℝ] V →L[ℝ] W`).
Route: `φ(t) := F(u₀ + t h) − F u₀ − t • F' u₀ h` on `[0,1]`, `φ'(t) = (F'(u₀+th) − F' u₀) h`, `‖φ'(t)‖ ≤ C t ‖h‖²` by the
MVT for `F'` on the sub-segment (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` applied to `F'`), then
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` (`MeanValue.lean`) with boundary `B t = C ‖h‖² t²/2`.
Alternative: `taylor_mean_remainder_bound` (`Taylor.lean`) on `t ↦ F(u₀ + t h)` with `n = 1` (needs `ContDiffOn ℝ 2`
of the composite and the identification of `iteratedDerivWithin 2`). Not in Mathlib in this form.
Classification: `surface-only`. The Lipschitz-`F'` form of the same estimate,
`‖F y − F x − F' x (y − x)‖ ≤ (L/2) ‖y − x‖²`, is the core of the backbone's `Newton.norm_step_sub_le` ((5.4.5)
below); the surface states it once as `norm_sub_sub_fderiv_le_half_mul_sq` and uses it for both.

**Prop 5.3.15** (Fréchet ⇒ partials, formula (5.3.8); continuous partials near `(u₀,v₀)` ⇒ Fréchet).
Lean: (⇒) `HasFDerivAt (fun u => f u v₀) (f'.comp (ContinuousLinearMap.inl ℝ U V)) u₀` from `HasFDerivAt.comp` with
`hasFDerivAt_prodMk_left`; formula `f' (h,k) = f' (h,0) + f' (0,k)` by linearity.
(⇐) Mathlib `hasStrictFDerivAt_uncurry_coprod` (`FDeriv/Partial.lean`; hypotheses: partials exist eventually near
`u` and are continuous at `u`) then `.hasFDerivAt`. Classification: `direct`.

**Cor 5.3.16** (`f` is `C¹` near `(u₀,v₀)` iff `f_u, f_v` continuous near it). Route: Prop 5.3.15 both ways +
continuity of `coprod`/`comp inl` in the operator norm (`Continuous.clm_comp`;
`coprod f g = f.comp (fst ℝ U V) + g.comp (snd ℝ U V)`). Classification: `surface-only`.

**Thm 5.3.17** (Gâteaux-differentiable `f : K → ℝ`, `K` convex: convex ⇔ (b) `f v ≥ f u + ⟨f' u, v − u⟩` ⇔ (c) monotone gradient).
Lean (`thm_5_3_17`): `(ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) ∧ (ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u))`.
Route: (a)⇒(b): `ConvexOn.slope_mono` on the 1D restriction `t ↦ f (u + t • (v − u))` (`ConvexOn.comp_affineMap`) +
`HasLineDerivAt.tendsto_slope_zero_right`; (b)⇒(a), (b)⇒(c) algebra; (c)⇒(b): `exists_hasDerivAt_eq_slope`
(`Deriv/MeanValue.lean`) for `φ(t) = f(u + t(v−u))` on `(0,1)`. Mathlib only has the 1D versions
(`MonotoneOn.convexOn_of_deriv`). Classification: `surface-only` (not needed by §5.4/§5.6, but by AH Ch 8, 11;
candidate for the backbone — §3).

**Thm 5.3.18** (strict version). Classification: `surface-only` (same file as 5.3.17; `StrictConvexOn`).

**Thm 5.3.19** (minimiser ⇔ variational inequality (5.3.10); subspace case (5.3.11)).
Lean (`thm_5_3_19`): `IsMinOn f K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u)` given convexity; plus
`(K : Submodule) : IsMinOn f K u ↔ ∀ v ∈ K, f' u v = 0`. Route: (⇒) one-sided slope limit
(`HasLineDerivAt.tendsto_slope_zero_right`, `ge_of_tendsto`); (⇐) Thm 5.3.17 (b). Classification: `surface-only` (given 5.3.17).

### §5.4 Newton's method

**(5.4.2) Newton iteration** — D10; `Newton.iterate_succ : iterate F F' u₀ (k + 1) = step F F' (iterate F F' u₀ k)`,
`newtonStep_sub_eq`. Classification: `direct`.

**Thm 5.4.1 (local convergence)**.
Book: `U, W` Banach, `F : U → W` Fréchet differentiable, `F u* = 0`, `[F'(u*)]⁻¹ ∈ L(W,U)`, `F'` Lipschitz with constant
`L > 0` on a neighbourhood `N(u*)`. Then ∃ `δ > 0`: if `‖u₀ − u*‖ ≤ δ` the Newton sequence is well defined and converges to
`u*`, and for some `M` with `Mδ < 1`: (5.4.3) `‖u_{n+1} − u*‖ ≤ M ‖u_n − u*‖²`, (5.4.4) `‖u_n − u*‖ ≤ (Mδ)^{2ⁿ}/M`.
Lean (`0 < M` added so that (5.4.4) is meaningful — harmless, `M = c₀L/2 > 0`; the neighbourhood `N(u*)` is
`Metric.ball ustar r`):
```lean
theorem thm_5_4_1 [CompleteSpace U] [CompleteSpace W] {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U}
    (hroot : F ustar = 0) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' ustar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ u ∈ Metric.ball ustar r, HasFDerivAt F (F' u) u)
    (hL : ∀ u ∈ Metric.ball ustar r, ∀ v ∈ Metric.ball ustar r, ‖F' u - F' v‖ ≤ L * ‖u - v‖) :
    ∃ δ > 0, ∃ M > 0, M * δ < 1 ∧ ∀ u₀, ‖u₀ - ustar‖ ≤ δ →
      (∀ n, ∃ e : U ≃L[ℝ] W, (e : U →L[ℝ] W) = F' (Newton.iterate F F' u₀ n)) ∧
      Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) ∧
      (∀ n, ‖Newton.iterate F F' u₀ (n + 1) - ustar‖ ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2) ∧  -- (5.4.3)
      (∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤ (M * δ) ^ (2 ^ n) / M)                             -- (5.4.4)
```
Backbone (`Numlib/Nonlinear/Newton.lean`, same hypotheses `hstar`, `e`, `he`, `hr`, `hF`, `hL`; its
quadratic-convergence section also carries `[IsRCLikeNormedField 𝕜]` and `[NormedSpace ℝ E]`,
because the estimates go through the mean value inequality and are false over a general
nontrivially normed field — both are automatic at the surface's `𝕜 = ℝ`, `E = U`):
`Newton.exists_ball_norm_step_sub_le : ∃ δ > 0, ∃ C : ℝ, ∀ x ∈ Metric.ball xstar δ, ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2`
and `Newton.tendsto_iterate : ∃ δ > 0, ∀ x₀ ∈ Metric.ball xstar δ, Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar)`.
Route: take `M := max C 1` and shrink `δ` so that `M δ < 1`; then `‖u − u*‖ ≤ δ ⇒ ‖T u − u*‖ ≤ M δ ‖u − u*‖ < δ`,
so the iterates stay in the ball and (5.4.3) holds along the sequence; (5.4.4) by induction
(`‖u_{n+1} − u*‖ ≤ M ((Mδ)^{2ⁿ}/M)² = (Mδ)^{2^{n+1}}/M`). Well-definedness (and the uniform bound `c₀` on
`‖F'(u)⁻¹‖` used by (5.4.5)): `ContinuousLinearEquiv.exists_symm_norm_le_of_add`
(`Numlib/Analysis/Normed/Ring/Inverse.lean`, AH Thm 2.3.5) applied to `F' u = F' u* + (F' u − F' u*)` with
`‖F' u − F' u*‖ ≤ Lδ < ‖F'(u*)⁻¹‖⁻¹`.
Classification: `direct` (well-definedness, convergence, (5.4.3)); `surface-only` ((5.4.4) induction).

**(5.4.5)** `‖T u − T u*‖ ≤ (c₀ L/2) ‖u − u*‖²` for `T u = u − F'(u)⁻¹ F u`, `u ∈ N(u*)`, `‖F'(u)⁻¹‖ ≤ c₀`.
Lean: `theorem eq_5_4_5 (hroot : F ustar = 0) (hF) (hL) (hu : u ∈ Metric.ball ustar r) (e : U ≃L[ℝ] W) (he : ↑e = F' u) (hc₀ : ‖(e.symm : W →L[ℝ] U)‖ ≤ c₀) : ‖Newton.step F F' u - ustar‖ ≤ c₀ * L / 2 * ‖u - ustar‖ ^ 2`.
Backbone: `Newton.norm_step_sub_le (hstar) (hF) (hL) (hx : x ∈ Metric.ball xstar r) (e) (he : ↑e = F' x) : ‖step Fn F' x - xstar‖ ≤ L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2`
(`Numlib/Nonlinear/Newton.lean`) — the exact constant, via `T u − u* = F'(u)⁻¹ [F u* − F u − F'(u)(u* − u)]` and
the `L/2` Taylor bound (`image_norm_le_of_norm_deriv_right_le_deriv_boundary`, see Prop 5.3.13).
Route: `mul_le_mul_of_nonneg_right` with `hc₀`. Classification: `direct`.

**Thm 5.4.2 (Kantorovich)**.
Book: (a) `F : D(F) ⊂ U → W` differentiable on an open convex `D(F)`, `‖F'(u) − F'(v)‖ ≤ L‖u − v‖` on `D(F)`; (b) `[F'(u₀)]⁻¹`
exists, bounded, `h = abL ≤ ½` with `a ≥ ‖F'(u₀)⁻¹‖`, `b ≥ ‖F'(u₀)⁻¹F(u₀)‖`, `t* = (1 − √(1−2h))/(aL)`, `t** = (1 + √(1−2h))/(aL)`;
(c) `B̄(u₁, r) ⊂ D(F)`, `r = t* − b`. Then ∃ solution `u* ∈ B̄(u₁, r)`, unique in `B̄(u₀, t**) ∩ D(F)`, `u_n → u*`, and
`‖u_n − u*‖ ≤ (1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)`.
Lean (all constants written out; `0 < a`, `0 < L` added so that `t*` is meaningful — with `L = 0` the book's `t*`
is `0/0`; the domain is taken as `Metric.closedBall u₀ r` with `t* ≤ r`):
```lean
theorem thm_5_4_2 [CompleteSpace U] [CompleteSpace W] {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U}
    {r a b L : ℝ} (ha : 0 < a) (hL : 0 < L) (hb : 0 ≤ b)
    (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ Metric.closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) :
    ∃ ustar ∈ Metric.closedBall u₀ ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L)),
      F ustar = 0 ∧ Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) ∧
      (∀ n, Newton.iterate F F' u₀ n ∈ Metric.closedBall u₀ r) ∧
      (0 < a * b * L → ∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤
        (2 * (a * b * L)) ^ (2 ^ n) * b / (2 ^ n * (a * b * L)))
```
Backbone: `Newton.kantorovich` (`Numlib/Nonlinear/Newton.lean`) with `β = a`, `η = b`, `h = β L η`,
`t* = (1 − √(1−2h))/(βL) ≤ r` — the statement above up to the order of the factors in `a * b * L`.
Classification: `direct`.
The book's finer form is a `deferred` refinement (phase 2, `plans/backbone.md` §7 "5.3.2 Kantorovich"; §3 item 2):
existence localised to `B̄(u₁, t* − b) ⊂ B̄(u₀, t*)` under the weaker domain hypothesis `B̄(u₁, t* − b) ⊂ D(F)`;
uniqueness in `B̄(u₀, t**) ∩ D(F)`; and the sharper bound `(1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)` — the backbone's
`(2h)^{2ⁿ} b/(2ⁿ h) = (2h)^{2ⁿ}/(2ⁿ aL)` is weaker since `1 − √(1−2h) ≤ 2h`; the two agree at `h = ½`, where both
degenerate to the linear rate `2⁻ⁿ/(aL)`.

**(5.4.7) Newton for nonlinear systems in ℝᵈ** and the form `F'(x_n) δ_n = −F(x_n)`, `x_{n+1} = x_n + δ_n`.
Lean: instantiate `Newton.iterate` with `U = W = EuclideanSpace ℝ (Fin d)`; `newtonStep_sub_eq`. Classification: `direct`.

**(5.4.8)–(5.4.12)** (Newton for the Urysohn equation on `C[0,1]`, the modified Newton (5.4.11), and the BVP `u'' = f(t,u)`
in `C²₀[0,1]`). Classification: `out-of-scope` (function-space calculus on top of the phase-3 toolkit; the modified
Newton convergence is Ex 5.4.5, an exercise — see §4).

### §5.5 Completely continuous vector fields (summary)

Thm 5.5.1 (Brouwer), Ex 5.5.2 (Kakutani-type map without fixed point on the unit ball of an infinite-dimensional Hilbert
space), Def 5.5.3 (compact / completely continuous nonlinear operators), Thm 5.5.4 (Schauder), Prop 5.5.5 (`T'(v₀)` compact),
and the rotation/index properties P1–P5 are all quoted without proof from Krasnoselskii/Berger/Zeidler; none is in
Mathlib (Brouwer: only the 1D `exists_mem_Icc_isFixedPt`; compact operators: `IsCompactOperator` and the Fredholm
alternative `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` — linear only). Classification: `out-of-scope` (all).

### §5.6 Conjugate gradient method for operator equations

**Setting: `Au = f` uniquely solvable, `A⁻¹` bounded** (book: by Thm 5.1.4).
Lean: `theorem existsUnique_solution (hA : IsSelfAdjoint A) (hbound) (f) : ∃! u, A u = f` and `‖A⁻¹‖ ≤ 1/m`.
Backbone: `ContinuousLinearMap.exists_equiv_of_isCoerciveWith (hc : 0 < c) (hA : (A : V →ₗ[ℝ] V).IsCoerciveWith c) : ∃ e : V ≃L[ℝ] V, ↑e = A ∧ ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 / c`
(`Numlib/Analysis/InnerProductSpace/Coercive.lean`) with `c := m`, via D13's `isSymmetricBoundedBy_iff` and
`IsSymmetricBoundedBy.isCoerciveWith`. Classification: `needs-equivalence` (D13).

**(5.6.2) CG recurrences** — D11; equivalence `cg_eq_CG_iterate` with backbone `CG.iterate` (`Numlib/Krylov/CG.lean`).
Classification: `needs-equivalence` (D11).

**Thm 5.6.1** (linear convergence; Patterson).
Book: `A` bounded self-adjoint with (5.6.3) `√m‖v‖ ≤ ‖v‖_A ≤ √M‖v‖`, `m, M > 0`. Then `u_k → u*` and
(5.6.4) `‖u* − u_{k+1}‖_A ≤ (M−m)/(M+m) ‖u* − u_k‖_A`.
Lean:
```lean
theorem thm_5_6_1 {A : V →L[ℝ] V} (hA : IsSelfAdjoint A) {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    {f u₀ ustar : V} (hstar : A ustar = f) :
    Tendsto (fun k => (cg A f u₀ k).u) atTop (𝓝 ustar) ∧
    ∀ k, normA A (ustar - (cg A f u₀ (k + 1)).u) ≤ (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u)
```
Backbone (via D11 and D13, `hA' : (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy m M`, `hA'.isSymmetricCoercive hm`):
`CG.isGalerkinIterate (k) : IsGalerkinIterate A f u₀ k (CG.iterate A f u₀ k).x` and
`CG.iterate_sub_mem (k) : (CG.iterate A f u₀ k).x - u₀ ∈ Krylov.subspace A r₀ k` (`Numlib/Krylov/CG.lean`);
`Krylov.residual_mem_subspace_succ` (`Numlib/Krylov/Iterate.lean`: `r_k ∈ 𝒦_{k+1}`), `Krylov.subspace_mono`
(`Numlib/Krylov/Subspace.lean`); `IsGalerkin.energyNorm_le (hA) (hx) (hstar) (hy : y - x₀ ∈ K)`
(`Numlib/LinearSolve/Projection/Optimality.lean`);
`Projection.energyNorm_steepestDescentStep_le (hl : 0 < lmin) (hA : A.IsSymmetricBoundedBy lmin lmax) (hstar) (x) : energyNorm A (xstar - steepestDescentStep A b x) ≤ (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x)`
(`Numlib/LinearSolve/Projection/OneDimensional.lean`, any inner product space).
Route for (5.6.4): `u_{k+1}` is the Galerkin iterate on `u₀ + 𝒦_{k+1}(A, r₀)`; the steepest-descent point
`u_k + α r_k` lies in `u₀ + 𝒦_{k+1}` (`u_k − u₀ ∈ 𝒦_k`, `r_k ∈ 𝒦_{k+1}`, `subspace_mono`), so `IsGalerkin.energyNorm_le`
gives `‖e_{k+1}‖_A ≤ ‖u* − SD(u_k)‖_A ≤ (M − m)/(M + m) ‖e_k‖_A`. (Equivalently: the degree-1 polynomial bound
`LinearMap.IsSymmetricBoundedBy.energyNorm_aeval_map_apply_le` (`Numlib/Krylov/Convergence/Polynomial.lean`) with
`p = 1 − 2X/(M+m)` on `e_k`, whose sup over `[m, M]` is `(M−m)/(M+m)`.) Convergence: (5.6.4) iterated,
`(M−m)/(M+m) < 1`, and `√m ‖·‖ ≤ ‖·‖_A` (`LinearMap.IsCoerciveWith.norm_le_energyNorm`,
`Numlib/Analysis/InnerProductSpace/Energy.lean`).
Difficult-proof note (backbone side, not repeated in the surface): the Hilbert-space bounds are proved by compressing
`A` to the finite-dimensional Krylov space generated by the *error* `x* − x₀` (`compression.aeval_apply_of_forall_pow_mem`,
`compression.isSymmetricBoundedBy`, `compression.energyNorm_apply` in `Numlib/Analysis/InnerProductSpace/Projection/Compression.lean` and
`Numlib/Krylov/Convergence/Polynomial.lean`), not by the residual: with generator `r₀` the compressed problem's
solution `A_K⁻¹ r₀` differs from `e₀ ∉ K`, and the compressed bound controls the wrong quantity.
Classification: `needs-equivalence` (D11, D13).

**(5.6.5)** `‖u* − u_k‖_A ≤ 2 ((√M − √m)/(√M + √m))^k ‖u* − u₀‖_A` (Patterson; quoted).
Lean (`eq_5_6_5`, under `m < M`). Backbone: `Krylov.IsGalerkinIterate.energyNorm_error_le (hl : 0 < lmin) (hll : lmin < lmax) (hA : A.IsSymmetricBoundedBy lmin lmax) (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) : energyNorm A (xstar - x) ≤ 2 * ((√(lmax / lmin) - 1) / (√(lmax / lmin) + 1)) ^ m * energyNorm A (xstar - x₀)`
(`Numlib/Krylov/Convergence/CG.lean`, any inner product space; the sharp Chebyshev form
`energyNorm_error_le_div_eval_T` alongside; ingredient `Polynomial.Chebyshev.one_div_eval_T_le_two_mul_pow`,
`Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean`) with `CG.isGalerkinIterate`.
Route: `(√(M/m) − 1)/(√(M/m) + 1) = (√M − √m)/(√M + √m)` (`Real.sqrt_div`, `div_sub_one`, `div_add_one`,
`div_div_div_cancel_right`). The backbone assumes `m < M`; for `m = M`, `A = m • 1` and CG is exact after one step.
Classification: `needs-equivalence` (D11, D13; ratio identity).

**(5.6.6)** `(√M − √m)/(√M + √m) ≤ (M − m)/(M + m)` (Ex 5.6.1).
Lean (`eq_5_6_6 (hm : 0 < m) (hmM : m ≤ M)`). Backbone: `Krylov.sqrt_ratio_le_ratio (hκ : 1 ≤ κ) : (√κ - 1) / (√κ + 1) ≤ (κ - 1) / (κ + 1)`
(`Numlib/Krylov/Convergence/CG.lean`) with `κ = M/m`; or directly: with `s = √m`, `t = √M`,
`(t−s)(t²+s²) ≤ (t+s)(t²−s²)` ⇔ `0 ≤ 2st`; `div_le_div_iff`,
`nlinarith [Real.sq_sqrt hm.le, Real.sq_sqrt (hm.le.trans hmM), Real.sqrt_nonneg m, Real.sqrt_nonneg M]`.
Classification: `direct`.

**(5.6.7)–(5.6.9)** (eigen-decomposition of the compact self-adjoint `K`, `λ_j → 0`, `δ = inf(1−λ_j) > 0 ⇔ A` positive definite,
`Δ = sup(1−λ_j)`, `‖A‖ = Δ`, `‖A⁻¹‖ = 1/δ`).
Classification: `out-of-scope` — relies on AH Thm 2.8.15/2.8.12 (spectral theorem for compact self-adjoint operators), absent from
Mathlib (only `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` (finite-dimensional) and the Fredholm alternative). (5.6.9)
becomes `surface-only` if the eigenbasis is taken as a hypothesis (see Thm 5.6.2 variant).

**(5.6.10)** `‖u* − u_{k+1}‖_A ≤ (Δ−δ)/(Δ+δ) ‖u* − u_k‖_A` for `A = I − K`.
Route: (5.6.4) with `(m, M) = (δ, Δ)`; the bounds `δ‖v‖² ≤ (Av,v) ≤ Δ‖v‖²` from Parseval in the eigenbasis
(`HilbertBasis.hasSum_repr`/`tsum` of `(1−λ_j)|(v,φ_j)|²`). Classification: `needs-equivalence` (from (5.6.4), under the
eigenbasis hypothesis).

**Thm 5.6.2 (Winther, superlinear convergence)**.
Book: `K` compact self-adjoint, `A = I − K` self-adjoint positive definite ⇒ `‖u* − u_k‖ ≤ c_k^k ‖u* − u₀‖` with
`c_k = (Δ/δ)^{3/(2k)} (2/k) Σ_{j≤k} |λ_j|/(1−λ_j) → 0` (5.6.21).
Faithful statement: `deferred` (phase 2, `plans/backbone.md` §3.10 and §8.3; needs the compact self-adjoint spectral
theorem, absent from Mathlib — §3 item 3). Surface-only variant (recommended if wanted): hypotheses
`(φ : HilbertBasis ℕ ℝ V) (λ : ℕ → ℝ) (hK : ∀ j, K (φ j) = λ j • φ j) (hanti : Antitone fun j => |λ j|) (hlim : Tendsto λ atTop (𝓝 0)) (hδ : 0 < δ) (hδ' : ∀ j, δ ≤ 1 − λ j) (hΔ : ∀ j, 1 − λ j ≤ Δ)`,
conclusion (5.6.11) with `c_k` as in (5.6.21). Proof steps:
- **(5.6.12)** `u_k = u₀ + P̃_{k−1}(A) r₀` (Ex 5.6.2): `CG.iterate_sub_mem` (`Numlib/Krylov/CG.lean`) +
  `Krylov.mem_subspace_iff_exists_aeval` (`Numlib/Krylov/Subspace.lean`). Classification: `needs-equivalence`.
- **(5.6.13)–(5.6.14)** optimality among `y_k = u₀ + P_{k−1}(K) r₀`: `IsGalerkin.energyNorm_le` +
  `Krylov.aeval_apply_mem_subspace` + `CG.isGalerkinIterate` + rewriting `P(K) = P̂(A)` (`Polynomial.aeval` of
  `1 − A`, `Polynomial.comp`). Classification: `needs-equivalence`.
- **(5.6.15)** `Q_k(λ) = ∏_{j≤k} (λ−λ_j)/(1−λ_j)`, `Q_k(1) = 1`, `Q_k = 1 − (1−λ)P_{k−1}`: `Polynomial` algebra
  (`Polynomial.X_sub_C_dvd_sub_C_eval` factorisation of `Q_k − 1` at `1`). Classification: `surface-only`.
- **(5.6.16)** `‖u* − u_k‖ ≤ (1/δ)√(Δ/δ) ‖r̃_k‖`: `LinearMap.IsCoerciveWith.norm_le_energyNorm`
  (`Numlib/Analysis/InnerProductSpace/Energy.lean`), the upper bound `‖v‖_A ≤ √Δ ‖v‖` (one line from
  `IsSymmetricBoundedBy.re_inner_le` and `Real.sqrt_le_sqrt`), `‖A⁻¹‖ ≤ 1/δ` from `exists_equiv_of_isCoerciveWith`.
  Classification: `direct`.
- **(5.6.17)** `r̃_k = Q_k(A) r₀`: `Krylov.exists_residual_poly (hx : x - x₀ ∈ Krylov.subspace A r₀ m) : ∃ p, p.degree ≤ m ∧ p.eval 0 = 1 ∧ b - A x = aeval A p (b - A x₀)`
  (`Numlib/Krylov/Iterate.lean`) and `Polynomial.aeval` algebra for the specific `Q_k`. Classification: `surface-only`.
- **(5.6.18)–(5.6.19)** `‖r̃_k‖ ≤ α_k ‖r₀‖`, `α_k = sup_{j>k} |Q_k(λ_j)| ≤ ∏_{j≤k} 2|λ_j|/(1−λ_j)`: `Module.End.aeval_apply_of_hasEigenvector`
  (`Q_k(A) φ_j = Q_k(λ_j) φ_j`), `HilbertBasis.repr` + Parseval, the product estimate from `hanti`. Classification: `surface-only`.
- **(5.6.20)** `(2/k) Σ_{j≤k} |λ_j|/(1−λ_j) → 0` (Ex 5.6.3): Mathlib `Filter.Tendsto.cesaro` (`SpecificAsymptotics.lean`)
  applied to `j ↦ |λ_j|/(1−λ_j) → 0` (`hlim`, `hδ`), with the AM–GM step `(∏ b_j)^{1/k} ≤ (1/k)Σ b_j`
  (`Real.geom_mean_le_arith_mean_weighted`). Classification: `direct` (Cesàro), `surface-only` (AM–GM assembly).
- **(5.6.21)/(5.6.11)** assembly. Classification: `surface-only`.

**Thm 5.6.3** (rates of `τ_ℓ` for Hilbert–Schmidt kernels (5.6.24) and `C^p` symmetric kernels (5.6.25)).
Classification: `out-of-scope` (integral operators on `L²(a,b)`, `Σλ_j² = ‖K‖²_HS`, Fenyö–Stolle eigenvalue asymptotics).

**Closing remark of §5.6** (`u_k − u₀ ∈ 𝒦(A)`; `‖u* − u_k‖_A = min_{y ∈ u₀ + 𝒦_k} ‖u* − y‖_A`).
Backbone: `IsGalerkin.iff_energyNorm_min` (`Numlib/LinearSolve/Projection/Optimality.lean`) or the polynomial
form `Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf` (`Numlib/Krylov/Iterate.lean`) + `CG.isGalerkinIterate`.
Classification: `needs-equivalence` (D11, D13).

## 3. Deferred backbone items

1. **`C[a,b]` integral-operator toolkit** — phase 3 (`plans/backbone.md` §7 "AH 5.2.3–5.2.4 (Bielecki norms,
   Picard–Lindelöf)", §8.3). Proposed `Numlib/IntegralEquations/Basic.lean`: bundled Fredholm/Urysohn/Volterra
   operators `C(Icc a b, ℝ) → C(Icc a b, ℝ)` (continuity from
   `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`), Lipschitz bounds (`|μ|·M·(b−a)`;
   Fredholm `α = max_x ∫|k|/|λ|`), the Volterra factorial estimate `|Tᵐu(t) − Tᵐv(t)| ≤ (M(t−a))ᵐ/m! ‖u−v‖_∞`, and a
   `Bielecki β` type synonym with norm equivalence and the contraction `M/β`. With these, Thm 5.2.2 is Thm 5.1.3 on
   `C(Icc a b, ℝ)`, Thm 5.2.3 is `tendsto_iterate_of_iterate_contractingWith` + the factorial bound, and the
   iteration part of Thm 5.2.4 is Thm 5.1.3 on the closed ball in `Bielecki L`. Consumers beyond this chapter:
   AH Ch. 12, Kress Ch. 10–12.
2. **Newton–Kantorovich in Atkinson–Han's form** — phase 2 (`plans/backbone.md` §7 "5.3.2 Kantorovich"): refine
   `Newton.kantorovich` with existence in `B̄(u₁, t* − b)` under the domain hypothesis `B̄(u₁, t* − b) ⊂ D(F)`,
   uniqueness in `B̄(u₀, t**)` with `t** = (1 + √(1−2h))/(aL)`, and the sharp a priori bound
   `‖u_n − u*‖ ≤ (1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)` (majorant-sequence argument; Ortega–Rheinboldt §12.6, Zeidler).
3. **Winther's theorem (Thm 5.6.2)** — phase 2 (`plans/backbone.md` §3.10, §8.3): blocked by the spectral theorem
   for compact self-adjoint operators (AH Thm 2.8.15; absent from Mathlib). The surface-only variant above takes the
   eigenbasis as a hypothesis and needs only `Krylov.exists_residual_poly` and `CG.iterate_sub_mem`.

Surface items that a later backbone phase may absorb (no phase assigned; each becomes worthwhile with a second
consumer): a Gâteaux-derivative API (`HasGateauxDerivAt`, Prop 5.3.4 (iii); Kress Ch. 6, AH Ch. 11); convexity
via directional derivatives (Thm 5.3.17–5.3.19: `ConvexOn.of_forall_le_add_lineDeriv`,
`convexOn_iff_monotone_lineDeriv`, `isMinOn_iff_forall_lineDeriv_nonneg`; AH Ch. 8, 11 and any optimisation
source); the `L/2` Taylor lemma `norm_sub_sub_fderiv_le_half_mul_sq` (Prop 5.3.13, (5.4.5)); the upper energy-norm
bound `‖v‖_A ≤ √M ‖v‖` for `IsSymmetricBoundedBy` (a one-liner; the form version is
`SesqForm.energyNorm_le_sqrt_mul_norm` in `Numlib/Variational/Forms.lean`).

## 4. Left out

- Ex 5.1.1 (kept optional), Ex 5.1.3, Ex 5.1.4 (not cited by theorems; Ex 5.1.4 is the local version of the
  fixed-point theorem mentioned in `plans/backbone.md` §5.3.1).
- §5.2.1 remarks on `T x = x − c₀ f(x)` and Newton's scalar form (motivation only).
- §5.2.2 componentwise Jacobi/GS/SOR formulas and the optimal-`ω` discussion; Ex 5.2.2 (diagonal dominance —
  backbone `Numlib/LinearSolve/Stationary/DiagDominant.lean`), Ex 5.2.3 (Richardson; `0 < θ < 2/λ_max`).
- Ex 5.2.4–5.2.11 (error bounds for the integral-equation iterations; systems of Volterra equations; second-order
  IVP) and Ex 5.2.12–5.2.13 (Gronwall — Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le`,
  `dist_le_of_approx_trajectories_ODE` cover them).
- Hammerstein and Nekrasov equations (5.2.14) (no theorem).
- Ex 5.3.1–5.3.17 (counterexamples, Jacobian, norm differentiability, Hessian criterion in ℝᵈ, `f(v) = ½(Av,v)`,
  energy functional — the last two reappear in Ch 8/9 and belong to the variational surface).
- Ex 5.3.9 (Jacobian), Ex 5.3.10 (Urysohn derivative), the paragraph on "maps of several variables" after Cor 5.3.16.
- §5.4.2 applications except (5.4.7): integral equation (5.4.8)–(5.4.12), modified Newton (5.4.11) = Ex 5.4.5
  (linear convergence of the chord method via the fixed-point theorem; an exercise), the BVP in `C²₀[0,1]`;
  Ex 5.4.1–5.4.4.
- §5.5 entirely (Brouwer, Kakutani-type example, Schauder, Prop 5.5.5, rotation P1–P5): quoted results, no Mathlib support.
- (5.6.7)–(5.6.9) as theorems about compact operators, Thm 5.6.2 in its faithful form, Thm 5.6.3, (5.6.22)–(5.6.26),
  Ex 5.6.1–5.6.3 as standalone exercises (they appear inside the corresponding results above).

## 5. Remarks on the book's statements

- **Thm 5.1.4 proof** (book erratum): `‖T_θ v₁ − T_θ v₂‖² ≤ (1 − 2c₂θ + c₁²θ²)‖v₁ − v₂‖²` and `θ ∈ (0, 2c₂/c₁²)`
  should read `1 − 2c₁θ + c₂²θ²` and `θ ∈ (0, 2c₁/c₂²)`; the theorem statement is unaffected, and the backbone's
  `contractingWith_damped` carries the corrected factor `√(1 − 2θc + θ²L²)`.
- **(5.6.3)** is read as `√m ‖v‖ ≤ ‖v‖_A ≤ √M ‖v‖`, i.e. `m‖v‖² ≤ (Av,v) ≤ M‖v‖²` — the form consistent with
  (5.6.9)–(5.6.10) (`m = δ`, `M = Δ`) and with Saad Thm 6.29; it is `LinearMap.IsSymmetricBoundedBy A m M` (D13).
- **Thm 5.2.4**: `Q_b = {(t,u) ∈ ℝ × V | |t − t₀| ≤ a, ‖u − z‖ ≤ b}`; "for any initial value `u₀` for which
  `‖z − u₀‖ < b`" is read as a constant initial function (any continuous `u₀` with `sup_t ‖u₀(t) − z‖ ≤ b` works in
  the proof); the weight `e^{−L|t−t₀|}` and `α = 1 − e^{−L a₀}` are the Bielecki computation with `β = L`.
- **Thm 5.4.2**: `h = abL ≤ 1/2`, `t* = (1 − (1−2h)^{1/2})/(aL)`, error bound `[1 − (1−2h)^{1/2}]^{2ⁿ}/(2ⁿ aL)` — the
  standard Zeidler/Kantorovich statement (for `h = ½` it degenerates to the linear rate `2⁻ⁿ/(aL)`).
- **Def 5.3.1 convention**: "interior point" via the *closed* ball `{‖u − u₀‖ ≤ r} ⊂ K` — equivalent to `K ∈ 𝓝 u₀`.
- **Thm 5.3.19**: "there exists `u ∈ K` such that (5.3.9) iff there exists `u ∈ K` such that (5.3.10)" — the proof
  shows the stronger pointwise equivalence for a fixed `u`; the surface states the pointwise form.
