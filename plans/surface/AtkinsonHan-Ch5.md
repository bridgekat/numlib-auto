# Surface plan: Atkinson–Han — Chapter 5

Atkinson & Han, *Theoretical Numerical Analysis* (3rd ed.), Ch. 5 "Nonlinear Equations and Their
Solution by Iteration": §5.1 Banach fixed point, §5.2 applications (scalar, linear systems, integral
equations, ODEs in Banach spaces), §5.3 differential calculus of operators, §5.4 Newton (local +
Kantorovich), §5.5 completely continuous vector fields (summary only), §5.6 CG for operator equations.

Generality as in the book: §5.1–5.2 on a Banach space `V` (scalar field irrelevant; we state over
`[NormedSpace ℝ V]`, generalising to `RCLike 𝕜` is free), Thm 5.1.4 and §5.6 on a **real** Hilbert
space (the book says so explicitly in §5.6; Thm 5.1.4 says "Hilbert space" with a real inner product
`(·,·)`), §5.3 on normed spaces (Prop 5.3.11/5.3.13 say "real Banach"), §5.4 on Banach spaces `U, W`.
Every Lean sketch below marked ✓ elaborated with `sorry` against Mathlib `v4.34.0-rc2`
(`Scratch1.lean`, `Scratch2.lean` in this directory). The surface imports only `Numlib`; where a
backbone item is still only planned (not in the current skeleton) the status says so.

Status legend. `direct`: proof is a direct use of Mathlib or of a declaration already in the `Numlib`
skeleton. `needs-equivalence`: same, modulo a surface lemma identifying the book's definition with the
Mathlib/backbone notion (or a backbone item that is planned and routine). `GAP`: needs a backbone
item that is neither in Mathlib nor in the current skeleton — listed in §4. `surface-only`: provable
in the surface file from Mathlib with moderate work, no backbone item warranted. `out-of-scope`: not
planned (reason given).

Proposed files (`Surface/AtkinsonHan/Ch05/`, namespace `AtkinsonHan.Ch05`, one section per file):

| File | Book | Backbone modules used |
|---|---|---|
| `FixedPoint.lean` | Def 5.1.2, Thm 5.1.3 (5.1.4)–(5.1.6), Ex 5.1.2, Thm 5.1.4 (5.1.8)–(5.1.11) | Mathlib `ContractingWith`; §5.3.1 (`Nonlinear/FixedPoint.lean`, planned); `ForMathlib/InnerProductSpace/Coercive.lean` (linear case) |
| `LinearIteration.lean` | Thm 5.2.1 + derivative criterion; §5.2.2 (5.2.4)–(5.2.6), relations 1–3, Jacobi/GS/SOR | Mathlib MVT; §2.3.1–2.3.2 (planned); `ForMathlib/Algebra/SpectralRadius.lean` |
| `IntegralEquations.lean` | §5.2.3 (5.2.7)–(5.2.9), Thm 5.2.2–5.2.3, §5.2.4 Thm 5.2.4 | Mathlib `IsPicardLindelof`, `ODE_solution_unique_of_mem_Icc`; `C[a,b]` toolkit (phase 3, §4 item 7) |
| `Calculus.lean` | Def 5.3.1–5.3.2, Prop 5.3.3–5.3.7, Ex 5.3.8, Prop 5.3.11–5.3.13, Def 5.3.14–Cor 5.3.16, Thm 5.3.17–5.3.19 | Mathlib `HasFDerivAt`, `HasLineDerivAt`, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, `FDeriv/Partial.lean`; §4 items 4–5 |
| `Newton.lean` | (5.4.2), Thm 5.4.1 (5.4.3)–(5.4.5), Thm 5.4.2, (5.4.7) | §5.3.2 (`Nonlinear/Newton.lean`, planned); `ForMathlib/NormedRing/Inverse.lean` |
| `ConjugateGradient.lean` | (5.6.2)–(5.6.6), (5.6.10), Thm 5.6.1; Thm 5.6.2 with (5.6.12)–(5.6.21) as a surface-only variant | `Krylov/Subspace.lean` ✓, `LinearSolve/Projection/{Basic,Optimality}.lean` ✓, `ForMathlib/InnerProductSpace/{Coercive,Energy,Compression}.lean` ✓, `ForMathlib/Polynomial/ChebyshevMinimax.lean` ✓; §3.7 `Krylov/CG.lean`, §3.9–3.10 (planned; Hilbert-space upgrade requested in §4 item 1) |

§5.5 gets no file (a module docstring in `Calculus.lean` records the summary).

## Book-specific definitions

### D1. Contractive / non-expansive / Lipschitz (Def 5.1.2)
*Book.* `T : K ⊂ V → V`; contractive with constant `α ∈ [0,1)`: `‖T u − T v‖ ≤ α ‖u − v‖ ∀ u v ∈ K`;
non-expansive: `α = 1`; Lipschitz: some `L ≥ 0`. Implications contractive ⇒ non-expansive ⇒ Lipschitz
⇒ continuous.
*Lean.* ✓
```lean
def ContractiveOn (T : V → V) (K : Set V) (α : ℝ) : Prop :=
  0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ α * ‖u - v‖
def NonExpansiveOn (T : V → V) (K : Set V) : Prop := ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ ‖u - v‖
def LipschitzOn (T : V → V) (K : Set V) : Prop := ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ L * ‖u - v‖
```
*Counterpart.* Mathlib `LipschitzOnWith (K : ℝ≥0) T s`, `ContractingWith K f` (= `K < 1 ∧ LipschitzWith K f`,
`Mathlib/Topology/MetricSpace/Contracting.lean`).
*Equivalence lemmas.* `contractiveOn_iff (hα : 0 ≤ α) : ContractiveOn T K α ↔ α < 1 ∧ LipschitzOnWith ⟨α, hα⟩ T K`
(`lipschitzOnWith_iff_norm_sub_le`); `ContractiveOn.contractingWith_restrict (h) (hT : MapsTo T K K) :
ContractingWith ⟨α, h.1⟩ (hT.restrict T K K)` (contraction of the restricted self-map of the subtype `↥K`);
`lipschitzOn_iff : LipschitzOn T K ↔ ∃ L : ℝ≥0, LipschitzOnWith L T K`; `ContractiveOn.nonExpansiveOn`,
`NonExpansiveOn.lipschitzOn`, `LipschitzOn.continuousOn` (`LipschitzOnWith.continuousOn`).

### D2. Fixed-point iteration (5.1.1)
*Book.* `u_{n+1} = T(u_n)`, `u_0 ∈ K`, requires `T(K) ⊂ K` (5.1.2). *Lean.* `T^[n] u₀` (`Nat.iterate`),
invariance `Set.MapsTo T K K` (then `Set.MapsTo.iterate`). No new definition.

### D3. Strongly monotone, Lipschitz operator (5.1.8)–(5.1.9)
*Book.* `(T v₁ − T v₂, v₁ − v₂) ≥ c₁ ‖v₁ − v₂‖²`, `‖T v₁ − T v₂‖ ≤ c₂ ‖v₁ − v₂‖`, real Hilbert space.
*Lean.* ✓ `def StronglyMonotoneWith (T : V → V) (c₁ : ℝ) : Prop := ∀ v₁ v₂, c₁ * ‖v₁ - v₂‖ ^ 2 ≤ inner ℝ (T v₁ - T v₂) (v₁ - v₂)`;
Lipschitz as `∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖` (= `LipschitzWith` up to `ℝ≥0`).
*Counterpart.* Backbone `LinearMap.IsCoerciveWith A c` (`Coercive.lean`, ✓ in skeleton) for the linear case;
the nonlinear notion is the hypothesis of backbone `zarantonello` (§5.3.1, planned).
*Equivalence.* `stronglyMonotoneWith_iff_isCoerciveWith (A : V →L[ℝ] V) : StronglyMonotoneWith A c ↔ (A : V →ₗ[ℝ] V).IsCoerciveWith c`
(`map_sub`, `RCLike.re_to_real`); `lipschitzWith_iff : (∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖) ↔ LipschitzWith ⟨c₂, _⟩ T`.

### D4. Matrix splitting and iteration matrix (§5.2.2)
*Book.* `A = N − M`, `N` nonsingular; iteration `N x_n = M x_{n−1} + b`, i.e. `x_n = N⁻¹M x_{n−1} + N⁻¹b`;
iteration matrix `N⁻¹M`; spectral radius `r_σ(A) = max |λ_i(A)|`; operator norm (5.2.6).
*Lean.* `structure BookSplitting (A : Matrix m m ℝ) where (N M : Matrix m m ℝ) (eq : A = N - M) (hN : IsUnit N)`;
`iterMatrix s := s.N⁻¹ * s.M`; `iterStep s b x := s.N⁻¹ * s.M *ᵥ x + s.N⁻¹ *ᵥ b`;
`rσ (A : Matrix m m ℝ) : ℝ≥0∞ := spectralRadius ℂ (A.map (algebraMap ℝ ℂ))`.
*Counterpart.* Backbone `Matrix.Splitting A` (§2.3.2, planned) — **note the naming swap**: backbone
`A = M − N` with `IsUnit M`; `Stationary.step G f x = G x + f` (§2.3.1, planned); spectral radius
`spectralRadius ℂ` for complex matrices (`ForMathlib/Algebra/SpectralRadius.lean` ✓); real matrices via
`Matrix.map Complex.ofReal` (§2.1.11, planned). Operator norm (5.2.6): Mathlib `ContinuousLinearMap.opNorm`
via `Matrix.toLin'`; the ∞-norm instance `Matrix.Norms.Operator` (`linfty_opNorm_*`).
*Equivalence.* `BookSplitting.toSplitting : Matrix.Splitting A` with `M := s.N`, `N := s.M`;
`iterStep_eq_stationary_step : iterStep s b = Stationary.step (toLin' (s.N⁻¹ * s.M)) (s.N⁻¹ *ᵥ b)`.

### D5. Integral operators on `C[a,b]` (§5.2.3–5.2.4)
*Book.* Linear Fredholm `u ↦ (1/λ)∫ₐᵇ k(x,y)u(y)dy + f/λ` (5.2.9); Urysohn `T u (x) = μ ∫ₐᵇ k(x,y,u(y)) dy + f(x)`
(5.2.10)/(5.2.13); Volterra `T u (t) = ∫ₐᵗ k(t,s,u(s)) ds + f(t)` (5.2.15)/(5.2.16); Picard
`T u (t) = z + ∫_{t₀}^t f(s,u(s)) ds` (5.2.19)/(5.2.20); Bielecki norm `|||v||| = max e^{−βt}|v(t)|`.
*Lean.* Carrier `C(Set.Icc a b, ℝ)` (sup norm, complete: `ContinuousMap` normed-space instances on a compact
domain); bare-function form ✓
`urysohnFun (hab : a ≤ b) (μ) (k : ℝ → ℝ → ℝ → ℝ) (f u : C(Icc a b, ℝ)) : Icc a b → ℝ := fun x => μ * ∫ y in a..b, k x y (u (Set.projIcc a b hab y)) + f x`,
bundled to `C(Icc a b, ℝ)` with `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
(`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:604`; needs `k` continuous). Same shape for
Volterra (`∫ y in a..x`, use `..._of_continuous` with `s x = x`) and Picard (values in `V`).
Bielecki norm: type synonym `Bielecki (β : ℝ) (X)` of `C(Icc a b, V)` with `‖v‖ = ⨆ t, exp (−β t) ‖v t‖`.
*Counterpart.* None in Mathlib/backbone (phase 3 in backbone §8.3; §4 item 7). Mathlib's
`IsPicardLindelof.FunSpace` (`Mathlib/Analysis/ODE/PicardLindelof.lean`) is an internal instance of the
same construction (iterate-contraction, `exists_contractingWith_iterate_next`).

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
*Lean.* ✓ `def HasGateauxDerivAt (f : V → W) (A : V →L[ℝ] W) (u₀ : V) : Prop := ∀ h : V, HasLineDerivAt ℝ f (A h) u₀ h`.
*Counterpart.* Mathlib `HasLineDerivAt 𝕜 f f' x v` (`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`; no
bundled Gâteaux notion). *Equivalence.* `HasFDerivAt.hasGateauxDerivAt := fun h => hf.hasLineDerivAt h` ✓;
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
(`Mathlib/Analysis/Convex/Deriv.lean`: `MonotoneOn.convexOn_of_deriv`, `ConvexOn.slope_mono`) — §4 item 5.

### D10. Newton iteration (5.4.2)
*Book.* `u_{n+1} = u_n − [F'(u_n)]⁻¹ F(u_n)`, `F : U → W` Fréchet differentiable, `U, W` Banach.
*Lean.* ✓
```lean
noncomputable def newtonStep (F : U → W) (F' : U → U →L[ℝ] W) (u : U) : U := u - (F' u).inverse (F u)
noncomputable def newtonSeq (F : U → W) (F' : U → U →L[ℝ] W) (u₀ : U) (n : ℕ) : U := (newtonStep F F')^[n] u₀
```
using Mathlib `ContinuousLinearMap.inverse` (`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean`;
`= e.symm` on invertible maps by `ContinuousLinearMap.inverse_equiv`, `= 0` otherwise). "Well-defined" =
`∀ n, ∃ e : U ≃L[ℝ] W, ↑e = F' (newtonSeq F F' u₀ n)`.
*Counterpart.* Backbone §5.3.2 `newtonStep f Df x := x - (Df x) (f x)` with a supplied `Df : E → F ≃L[𝕜] E`
(planned). *Equivalence.* `newtonStep_eq_backbone (hDf : ∀ u, (Df u : U →L[ℝ] W) = F' u) : newtonStep F F' = Newton.newtonStep F Df`
by `inverse_equiv`. Recommendation in §4 item 3: make the `inverse`-based form the backbone one.
Also `newtonStep_sub_eq (he : ↑e = F' u) : (F' u) (newtonStep F F' u - u) = -F u` (the form `F'(x_n) δ_n = −F(x_n)` of (5.4.7)/(5.4.9)).

### D11. Conjugate gradient iteration (5.6.2)
*Book.* Real Hilbert space `V`, `A` bounded self-adjoint positive definite; `r₀ = f − A u₀`, `s₀ = r₀`;
`α_k = ‖r_k‖²/(A s_k, s_k)`, `u_{k+1} = u_k + α_k s_k`, `r_{k+1} = f − A u_{k+1}`, `β_k = ‖r_{k+1}‖²/‖r_k‖²`,
`s_{k+1} = r_{k+1} + β_k s_k`.
*Lean.* ✓
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
*Counterpart.* Backbone `CG.State`, `CG.step`, `CG.iterate A b x₀ k` (§3.7 `Krylov/CG.lean`, planned, `A : E →ₗ[𝕜] E`).
*Equivalence.* `cg_eq_CG_iterate : cg A f u₀ k = ⟨(CG.iterate ↑A f u₀ k).x, (CG.iterate ↑A f u₀ k).r, (CG.iterate ↑A f u₀ k).p⟩`
— by induction on `k`, using `CG.residual_eq` (backbone) for the book's explicit `r_{k+1} = f − A u_{k+1}`
versus the backbone's (presumably) `r_k − α_k A p_k`, and `RCLike.re_to_real`/`inner_self_eq_norm_sq` for
`⟪r,r⟫ = ‖r‖²` if the backbone divides by `𝕜`-valued inner products.

### D12. `A`-inner product and `A`-norm (§5.6)
*Book.* `(v,u)_A = (Av, u)`, `‖v‖_A = √(v,v)_A`. *Lean.* ✓ `innerA A v u := inner ℝ (A v) u`,
`normA A v := Real.sqrt (innerA A v v)`.
*Counterpart.* Backbone `energyInner (A : E →ₗ[𝕜] E) x y = inner 𝕜 (A x) y`, `energyNorm A x = √(re ⟪A x, x⟫)`
(`Energy.lean` ✓, scoped notation `⟪x, y⟫_[A]`, `‖x‖_[A]`).
*Equivalence.* `innerA_eq : innerA A v u = energyInner (A : V →ₗ[ℝ] V) v u` (`rfl`),
`normA_eq : normA A v = energyNorm (A : V →ₗ[ℝ] V) v` (`RCLike.re_to_real`).

### D13. Bounded self-adjoint positive definite operator; (5.6.3)
*Book.* `A ∈ L(V)` self-adjoint (`(Au,v) = (u,Av)`, real Hilbert space), positive definite in the sense that
Thm 5.1.4 applies, i.e. `(Av,v) ≥ c₁‖v‖²` (the book's (5.6.8) confirms: "positive definite iff `δ = inf(1−λ_j) > 0`");
(5.6.3): `√m ‖v‖ ≤ ‖v‖_A ≤ √M ‖v‖`, `m, M > 0`.
*Lean.* `IsSelfAdjoint (A : V →L[ℝ] V)` (Mathlib, needs `[CompleteSpace V]`), hypothesis
`hbound : ∀ v, √m * ‖v‖ ≤ normA A v ∧ normA A v ≤ √M * ‖v‖` ✓.
*Counterpart.* Backbone `LinearMap.IsSymmetric`, `LinearMap.IsCoerciveWith A m`, `LinearMap.IsSymmetricCoercive A`
(`Coercive.lean` ✓). *Equivalence.* `isSelfAdjoint_iff_isSymmetric : IsSelfAdjoint A ↔ (A : V →ₗ[ℝ] V).IsSymmetric`
(Mathlib `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, `Adjoint.lean`);
`bound_iff : (∀ v, √m ‖v‖ ≤ ‖v‖_A ∧ ‖v‖_A ≤ √M ‖v‖) ↔ (A.IsCoerciveWith m ∧ ∀ v, re ⟪A v, v⟫ ≤ M ‖v‖²)`
(`Real.sqrt_le_sqrt`, `Real.sqrt_le_left`, `pow_le_pow_left`); hence `IsSymmetricCoercive` from `hA` and `hbound`.

### D14. Compact / completely continuous nonlinear operators (Def 5.5.3) — summary only
Mathlib has `IsCompactOperator` for linear maps; the nonlinear notion, Brouwer/Schauder and the rotation are out
of scope (no Mathlib support; `Brouwer` does not occur in Mathlib outside order theory).

## Results

Numbered results in book order. Each block: **Book statement** / **Lean surface statement** (sketch) /
**Backbone/Mathlib item** / **Proof route** / **Status**.

### §5.1 The Banach fixed-point theorem

**Ex 5.1.1** (affine map on ℝ).
Book: `T x = a x + b`; `x_n = x₀ + n b` if `a = 1`, `x_n = aⁿ x₀ + (1 − aⁿ)/(1 − a) b` if `a ≠ 1`; for `a ≠ 1`
the iteration converges iff `|a| < 1`.
Lean: `theorem ex_5_1_1 (a b x₀ : ℝ) (h : a ≠ 1) : (fun x => a * x + b)^[n] x₀ = a ^ n * x₀ + (1 - a ^ n) / (1 - a) * b`
and `(∀ x₀, ∃ x, Tendsto (fun n => (fun x => a*x+b)^[n] x₀) atTop (𝓝 x)) ↔ |a| < 1`.
Mathlib: `tendsto_pow_atTop_nhds_zero_iff`, `geom_sum_eq`. Route: induction + geometric series.
Status: `surface-only` (trivial; optional).

**Def 5.1.2 implications** (contractive ⇒ non-expansive ⇒ Lipschitz ⇒ continuous).
Lean: `ContractiveOn.nonExpansiveOn`, `NonExpansiveOn.lipschitzOn`, `LipschitzOn.continuousOn`.
Mathlib: `LipschitzOnWith.continuousOn`. Status: `direct`.

**Thm 5.1.3 (Banach fixed-point theorem)**.
Book: `K` nonempty closed in a Banach space `V`, `T : K → K` contractive with constant `α ∈ [0,1)`. (1) ∃! `u ∈ K`,
`u = T u`. (2) for any `u₀ ∈ K`, `u_n → u`, and
(5.1.4) `‖u_n − u‖ ≤ αⁿ/(1−α) ‖u₀ − u₁‖`, (5.1.5) `‖u_n − u‖ ≤ α/(1−α) ‖u_{n−1} − u_n‖`, (5.1.6) `‖u_n − u‖ ≤ α ‖u_{n−1} − u‖`.
Lean ✓ (`Scratch1.lean`):
```lean
theorem thm_5_1_3 [CompleteSpace V] {K : Set V} (hK : IsClosed K) (hne : K.Nonempty)
    {T : V → V} (hT : Set.MapsTo T K K) {α : ℝ} (hα : ContractiveOn T K α) :
    (∃! u, u ∈ K ∧ T u = u) ∧
    ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
      (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧                       -- (5.1.4)
      (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧           -- (5.1.5)
      (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖)                                 -- (5.1.6)
```
Mathlib: work on the subtype `↥K` (complete by `IsClosed.completeSpace_coe`) with
`ContractingWith.fixedPoint`, `fixedPoint_isFixedPt`, `fixedPoint_unique`/`fixedPoint_unique'`,
`tendsto_iterate_fixedPoint`, `apriori_dist_iterate_fixedPoint_le` (= (5.1.4)),
`aposteriori_dist_iterate_fixedPoint_le` (`dist (f^[n] x) u ≤ dist (f^[n] x) (f^[n+1] x)/(1−K)`),
`dist_le_mul` (= (5.1.6)). Alternatively the `efixedPoint'` API (`exists_fixedPoint'`, `efixedPoint_mem'`,
`tendsto_iterate_efixedPoint'`, `apriori_edist_iterate_efixedPoint_le'`, `edist_efixedPoint_le'`) in `edist` form
— backbone §5.3.1 plans the `dist`-form glue `ContractingWith.dist_iterate_fixedPoint_le_of_mapsTo`.
Route: (5.1.5) = `aposteriori…` at `n+1` chained with `dist_le_mul` (`‖u_{n+1} − u_{n+2}‖ ≤ α ‖u_n − u_{n+1}‖`).
Status: `direct` ((1), (2), (5.1.4), (5.1.6)); `direct` ((5.1.5), two-line combination). The book's unusual
`n = 0` case of (5.1.5)/(5.1.6) is avoided by indexing with `n + 1` (the book states them for `n ≥ 1`).

**Ex 5.1.2** (`Tᵐ` contractive; cited by Thm 5.2.3).
Book: `K` nonempty closed, `T : K → K` continuous, `Tᵐ` a contraction for some `m ≥ 1` ⇒ `T` has a unique fixed
point in `K` and `u_{n+1} = T u_n` converges.
Lean ✓: `theorem ex_5_1_2 … (hc : ContinuousOn T K) {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : ContractiveOn (T^[m]) K α) : (∃! u, u ∈ K ∧ T u = u) ∧ ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u)`.
Mathlib: `ContractingWith.isFixedPt_fixedPoint_iterate` (existence), `fixedPoint_unique'` applied to `T^[m]`
(uniqueness, since a fixed point of `T` is one of `T^[m]`). Convergence of the whole sequence: the `m`
subsequences `T^[k m + j] u₀ = (T^[m])^[k] (T^[j] u₀) → u` (`tendsto_iterate_fixedPoint`), then
`Filter.tendsto_atTop` residue-class glue (`Nat.mod_add_div`) — backbone §5.3.1 `exists_unique_fixedPoint_of_iterate_contracting`
(planned). Remark: continuity of `T` is not needed (the limit is the `T^[m]`-fixed point, which is the `T`-fixed
point by uniqueness); keep the hypothesis for faithfulness.
Status: `direct` (existence, uniqueness); `GAP` (convergence: backbone §5.3.1 item planned, not in skeleton — §4 item 2).

**Thm 5.1.4** (strongly monotone + Lipschitz ⇒ bijective; real Hilbert space).
Book: `V` Hilbert, `T : V → V` with (5.1.8) `(T v₁ − T v₂, v₁ − v₂) ≥ c₁‖v₁ − v₂‖²` and (5.1.9)
`‖T v₁ − T v₂‖ ≤ c₂‖v₁ − v₂‖`, `c₁, c₂ > 0`. Then ∀ `b`, ∃! `u` with `T u = b` (5.1.10), and (5.1.11)
`‖u₁ − u₂‖ ≤ (1/c₁)‖b₁ − b₂‖` when `T u_i = b_i`.
Lean ✓:
```lean
theorem thm_5_1_4 {T : V → V} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hmono : StronglyMonotoneWith T c₁) (hlip : ∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖) :
    (∀ b, ∃! u, T u = b) ∧ ∀ u₁ u₂ b₁ b₂, T u₁ = b₁ → T u₂ = b₂ → ‖u₁ - u₂‖ ≤ (1 / c₁) * ‖b₁ - b₂‖
```
Backbone: §5.3.1 `zarantonello` (planned): contraction of `T_θ v = v − θ (T v − b)` with factor
`√(1 − 2θc₁ + θ²c₂²) < 1` for `θ ∈ (0, 2c₁/c₂²)`, then Thm 5.1.3 with `K = V`. Linear special case already in
skeleton: `ContinuousLinearMap.exists_equiv_of_isCoerciveWith` (`Coercive.lean`).
Route: (5.1.11) directly from (5.1.8) + `real_inner_le_norm` (surface, 3 lines).
Status: `GAP` (existence/uniqueness: backbone `zarantonello` planned, not in skeleton — §4 item 2);
`direct` ((5.1.11)). Book erratum in the proof (constants swapped) — see §6.

### §5.2 Applications to iterative methods

**Thm 5.2.1** (scalar contraction on `[a,b]`).
Book: `T : [a,b] → [a,b]` contractive with `α ∈ [0,1)`: unique fixed point, convergence, the three bounds.
Lean ✓ (`Scratch2.lean` `thm_5_2_1`): Thm 5.1.3 with `V = ℝ`, `K = Icc a b`, `|·|` for `‖·‖`.
Mathlib: `isClosed_Icc`, `Set.nonempty_Icc`. Status: `direct` (specialisation of `thm_5_1_3`).

**Thm 5.2.1, derivative criterion** ("`sup_{[a,b]} |T'| < 1` ⇒ contractive with that constant").
Lean ✓ `thm_5_2_1_deriv (hT : ∀ x ∈ Icc a b, HasDerivWithinAt T (T' x) (Icc a b) x) (hα : ∀ x ∈ Icc a b, |T' x| ≤ α) (h1 : α < 1) : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |T x - T y| ≤ α * |x - y|`.
Mathlib: `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` / `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`
(`MeanValue.lean:704`), `convex_Icc`. Status: `direct`.

**§5.2.2 (a)** error equation (5.2.5) `x − x_n = (N⁻¹M)ⁿ (x − x₀)`.
Lean: `theorem eq_5_2_5 (s : BookSplitting A) (hx : A *ᵥ x = b) (x₀) (n) : x - (iterStep s b)^[n] x₀ = (s.N⁻¹ * s.M) ^ n *ᵥ (x - x₀)`.
Backbone: `Stationary.step_iterate_sub` (§2.3.1, planned) through D4's equivalence; otherwise a five-line
induction. Status: `needs-equivalence`.

**§5.2.2 (b)** "converges if `‖N⁻¹M‖ < 1`" (any induced norm).
Lean: `theorem tendsto_of_opNorm_lt_one (hG : ‖toLin' (s.N⁻¹ * s.M)‖ < 1) (hx : A *ᵥ x = b) (x₀) : Tendsto (fun n => (iterStep s b)^[n] x₀) atTop (𝓝 x)`.
Mathlib: `ContractingWith` for `x ↦ G x + c` (`ContinuousLinearMap.lipschitz`, `LipschitzWith.add_const`) +
Thm 5.1.3, or backbone `Stationary.contractingWith` (§2.3.1, planned). Status: `direct` (via `thm_5_1_3`).

**§5.2.2 (c)** "`Aⁿ → 0` iff `r_σ(A) < 1`" (square matrices).
Backbone: `spectralRadius_lt_one_iff_tendsto_pow` (`ForMathlib/Algebra/SpectralRadius.lean` ✓, complex Banach
algebra) — direct for `Matrix n n ℂ`; for real matrices needs the complexification bridge `Matrix.map Complex.ofReal`
(§2.1.11, planned: `spectralRadius (A.map ofReal)`, `(A.map ofReal)^n = (A^n).map ofReal`, `tendsto` transfer).
Status: `direct` (complex); `GAP` (real matrices, §4 item 6).

**§5.2.2 (d)** "converges for every `x₀` iff `(N⁻¹M)ⁿ → 0`", hence iff `r_σ(N⁻¹M) < 1`.
Lean: `(∀ x₀, Tendsto … (𝓝 x)) ↔ Tendsto (fun n => (s.N⁻¹ * s.M) ^ n) atTop (𝓝 0)`; from (5.2.5) (⇐ direct; ⇒ apply to
`x₀ = x − e_i` and use `Matrix.mulVec`-basis vectors / `Pi.tendsto_iff`). Status: `surface-only` (finite-dimensional
argument; the ⇒ direction is the finite-dimensional statement `Stationary.spectralRadius_lt_one_of_forall_tendsto` of §2.3.1).

**§5.2.2 relation 1** `r_σ(A) ≤ ‖A‖` for any operator norm.
Mathlib: `spectrum.spectralRadius_le_nnnorm` (`Mathlib/Analysis/Normed/Algebra/Spectrum.lean:227`) for the Banach-algebra
norm; other induced norms via `Matrix.Norms.*` instances or the equivalence-of-norms instance in scope.
Status: `direct` (for the norm instance in scope), `surface-only` for "any" induced norm (quantify over a
`NormedAlgebra ℂ (Matrix n n ℂ)` instance — awkward; state for the three Mathlib norms).

**§5.2.2 relation 2** (`∀ ε ∃` operator norm with `‖A‖ ≤ r_σ + ε`; `r_σ = inf` over operator norms).
Status: `out-of-scope` (no Mathlib support; backbone §2.3.1 explicitly replaces it by Gelfand).

**§5.2.2 relation 3** Gelfand `r_σ(A) = lim ‖Aⁿ‖^{1/n}` for any matrix norm.
Mathlib: `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (ℂ, Banach-algebra norm).
Status: `direct` (complex matrices, algebra norm); `GAP` (real matrices via §2.1.11); the "any matrix norm"
generality is `surface-only` via norm equivalence (`LinearEquiv.toContinuousLinearEquiv` constants).

**§5.2.2 Jacobi / Gauss–Seidel / SOR** (definitions `A = D + L + U`, `N = D`, `N = D + L`, `N = D/ω + L`).
Lean: `Matrix.diagPart`, strict lower/upper parts as `Matrix.of fun i j => if j < i then A i j else 0` (needs
`[LinearOrder n]`), the three `BookSplitting`s and the componentwise formulas as `Matrix.mulVec` lemmas.
Backbone: §2.3.2 constructors (planned). Status: `needs-equivalence` (definitions only; no theorem in the book here).

**§5.2.3 linear Fredholm equation** (5.2.7)–(5.2.9): contractivity constant `α = (1/|λ|) max_x ∫ₐᵇ |k(x,y)| dy`,
condition (5.2.8) `α < 1`.
Lean: `fredholmFun`/`fredholmOp` on `C(Icc a b, ℝ)`; `lemma lipschitz_fredholmOp : ‖T u − T v‖ ≤ α ‖u − v‖`.
Route: `intervalIntegral.norm_integral_le_of_norm_le_const` pointwise then `ContinuousMap.norm_le`.
Status: `GAP` (needs the `C[a,b]` integral-operator toolkit — §4 item 7; backbone §8.3 "phase 3").

**Thm 5.2.2 (Urysohn equation)**.
Book: `f ∈ C[a,b]`, `k ∈ C([a,b]²×ℝ)` (5.2.11), uniform Lipschitz in the third argument with constant `M` (5.2.12),
`|μ| M (b − a) < 1` ⇒ unique solution `u ∈ C[a,b]` of (5.2.10), approximated by (5.2.13).
Lean ✓ (`Scratch2.lean` `thm_5_2_2`, operator supplied as a bundled map agreeing with `urysohnFun`):
`(∃! u, T u = u) ∧ ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u)`.
Route: `thm_5_1_3` with `K = univ`; Lipschitz bound `‖T u − T v‖ ≤ |μ| M (b−a) ‖u − v‖` from
`intervalIntegral.norm_integral_le_of_norm_le_const` and `ContinuousMap.norm_coe_le_norm`.
Status: `surface-only` (moderate; the only non-trivial step is bundling `T` into `C(Icc a b, ℝ)` — covered by
§4 item 7 if the toolkit is built).

**Thm 5.2.3 (nonlinear Volterra equation)**.
Book: `k` continuous on `{a ≤ s ≤ t ≤ b} × ℝ`, `f ∈ C[a,b]`, Lipschitz in `u` with constant `M` (no smallness) ⇒ unique
solution in `C[a,b]`, iteration (5.2.16) converges for every `u₀`.
Lean: same shape as `thm_5_2_2` with `volterraFun hab k f u x := ∫ y in a..x, k x y (u (projIcc y)) + f x` and no `μ`-hypothesis.
Route (book Approach 1): `|Tᵐu(t) − Tᵐv(t)| ≤ (M(t−a))ᵐ/m! ‖u−v‖_∞` by induction (`intervalIntegral.integral_mono`,
`integral_pow`), so `T^[m]` contracts for large `m` (`FloorSemiring`/`Real.tendsto_pow_div_factorial_atTop`), then Ex 5.1.2.
Approach 2 (Bielecki): `ContractingWith (M/β) T` on the type synonym `Bielecki β C(Icc a b, ℝ)`.
Status: `GAP` (Ex 5.1.2 convergence in §5.3.1 + toolkit §4 item 7; Mathlib's `IsPicardLindelof.FunSpace.dist_iterate_next_apply_le`
proves exactly the factorial estimate for the Picard operator and is the template).

**Thm 5.2.4 (generalized Picard–Lindelöf)**.
Book: `V` Banach, `Q_b = {(t,u) : |t − t₀| ≤ a, ‖u − z‖ ≤ b}`, `f : Q_b → V` continuous, Lipschitz in `u` with constant
`L`, `M = max_{Q_b} ‖f‖`, `a₀ = min(a, b/M)`. Then (5.2.18) has a unique `C¹` solution on `[t₀ − a₀, t₀ + a₀]`;
the Picard iteration (5.2.20) converges for any `u₀` with `‖z − u₀‖ < b`; with `α = 1 − e^{−L a₀}` the weighted error
`max_{|t−t₀|≤a₀} ‖u_n(t) − u(t)‖ e^{−L|t−t₀|}` satisfies the three bounds (5.1.4)–(5.1.6) in the weighted norm.
Lean ✓ (existence/uniqueness part, `Scratch2.lean` `thm_5_2_4_exists_unique`):
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
with `x₀ := z`, `a := b`, `r := 0`, `L := M`, `K := L`, `tmin/tmax := t₀ ∓ a₀` (then `M a₀ ≤ b` ✓);
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` (existence), `contDiffOn_enat_Icc_of_hasDerivWithinAt`
(`C¹`), `ODE_solution_unique_of_mem_Icc` (uniqueness; Gronwall `norm_le_gronwallBound_of_norm_deriv_right_le`).
Note Mathlib's `IsPicardLindelof` is stated for any complete `NormedSpace ℝ E` — the backbone §5.3.1 remark "in finite
dimension" is inaccurate; the book's generalised theorem is literally Mathlib's.
Picard-iteration convergence and the three weighted bounds: not exposed by Mathlib (its proof goes through
`FunSpace.next` with iterate-contraction, not the Bielecki norm) — needs the `Bielecki`-norm type synonym on
`C(Icc (t₀−a₀) (t₀+a₀), V)`, the contraction `|||T u − T v||| ≤ (1 − e^{−L a₀}) |||u − v|||` and Thm 5.1.3 on the closed
ball `{u : ‖u(t) − z‖ ≤ b}`.
Status: `direct` (existence, uniqueness, `C¹`); `GAP` (iteration + weighted bounds — §4 item 7).

### §5.3 Differential calculus for nonlinear operators

**Def 5.3.1, uniqueness of the Fréchet derivative.** Mathlib `HasFDerivAt.unique`. Status: `direct`.

**Prop 5.3.3** (Fréchet differentiable ⇒ continuous). `HasFDerivAt.continuousAt`. Status: `direct`.

**Prop 5.3.4** (Fréchet ⇒ Gâteaux; converse under uniform limit or continuity of the Gâteaux derivative).
Lean: (i) `HasFDerivAt.hasGateauxDerivAt` ✓ (`HasFDerivAt.hasLineDerivAt`).
(ii) `hasFDerivAt_of_hasGateauxDerivAt_uniform (hG : HasGateauxDerivAt f A u₀) (hunif : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ = 1 → ∀ t, 0 < |t| → |t| < δ → ‖t⁻¹ • (f (u₀ + t • h) - f u₀) - A h‖ ≤ ε) : HasFDerivAt f A u₀`
— unfold `hasFDerivAt_iff_isLittleO_nhds_zero`, write `h = ‖h‖ • (‖h‖⁻¹ • h)`.
(iii) `hasFDerivAt_of_hasGateauxDerivAt_continuousAt (hG : ∀ᶠ u in 𝓝 u₀, HasGateauxDerivAt f (A u) u) (hA : ContinuousAt A u₀) : HasFDerivAt f (A u₀) u₀`
— standard: apply `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` to `t ↦ f (u₀ + t • h) − t • A u₀ h` on `[0,1]`
(line derivative `A (u₀ + t h) h − A u₀ h`, bounded by `sup ‖A(u₀+th) − A u₀‖ ‖h‖ = o(1)‖h‖`).
Mathlib has neither (ii) nor (iii). Status: `direct` (i); `surface-only` (ii); `GAP` (iii — §4 item 4; also Kress Thm 6.x).

**Prop 5.3.5 (sum rule)** for Fréchet and Gâteaux derivatives.
Mathlib: `HasFDerivAt.add`, `HasFDerivAt.const_smul` (`FDeriv/Add.lean`); Gâteaux: unfold `HasLineDerivAt` (= `HasDerivAt` of
`t ↦ f (x + t • v)` at `0`) and use `HasDerivAt.add`, `HasDerivAt.const_smul`. Status: `direct` (Fréchet); `surface-only` (Gâteaux, one-liners).

**Prop 5.3.6 (product rule)** `B(u) = b(f₁ u, f₂ u)`, `b` bounded bilinear.
Mathlib: `IsBoundedBilinearMap.hasFDerivAt` + `HasFDerivAt.comp` + `HasFDerivAt.prodMk`, or the packaged
`ContinuousLinearMap.hasFDerivAt_of_bilinear` (`FDeriv/Bilinear.lean:120`, `b : V₁ →L[ℝ] V₂ →L[ℝ] W`); derivative
`h ↦ b (f₁' h) (f₂ u₀) + b (f₁ u₀) (f₂' h)`. Gâteaux case: `HasFDerivAt.comp_hasDerivAt` along the line.
Status: `direct` (Fréchet; state `b` as `IsBoundedBilinearMap ℝ b` with equivalence to the curried CLM via
`IsBoundedBilinearMap.toContinuousLinearMap`); `surface-only` (Gâteaux).

**Prop 5.3.7 (chain rule)**. `HasFDerivAt.comp` (`FDeriv/Comp.lean:105`); Gâteaux∘Fréchet: `HasFDerivAt.comp_hasDerivAt`
on `t ↦ f (u₀ + t • h)`. Interior-point hypotheses are the `K ∈ 𝓝 u₀`, `L ∈ 𝓝 (f u₀)` reductions of D6.
Status: `direct`.

**Ex 5.3.8** (affine `f v = L v + b` has `f' ≡ L`). `(L.hasFDerivAt).add_const b`. Status: `direct`.

**Ex 5.3.9** (Jacobian). Status: `out-of-scope` (see §5; Mathlib `hasFDerivAt_pi''`, `LinearMap.toMatrix'` give it under
`C¹` hypotheses the book does not state).

**Ex 5.3.10** (Fréchet derivative of the Urysohn operator). Status: `out-of-scope` (phase 3, `C[a,b]` toolkit + differentiation
under the integral: Mathlib `hasFDerivAt_integral_of_dominated_of_fderiv_le`).

**Prop 5.3.11 (mean value inequality)**.
Book: `U, V` real Banach, `K` open, `F` differentiable on `K` with `F'` continuous, segment `[u,w] ⊂ K` ⇒
(5.3.7) `‖F u − F w‖ ≤ sup_{θ∈[0,1]} ‖F'((1−θ)u + θw)‖ ‖u − w‖`.
Lean ✓ (`Scratch1.lean` `prop_5_3_11`): `‖F u - F w‖ ≤ (⨆ θ : Icc (0:ℝ) 1, ‖F' ((1 - θ) • u + θ • w)‖) * ‖u - w‖`.
Mathlib: `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` with `s := segment ℝ u w` (`convex_segment`), bound `C := ⨆ …`
(`le_ciSup` needs `BddAbove`, from continuity of `F'` on the compact segment: `isCompact_segment`, `IsCompact.bddAbove_image`);
`segment_eq_image_lineMap`. Completeness and continuity of `F'` are only used to make the `sup` finite.
Status: `direct`.

**Cor 5.3.12** (`F' ≡ 0` on a connected open set ⇒ `F` constant).
Mathlib: `IsOpen.is_const_of_fderiv_eq_zero (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s) (hf' : s.EqOn (fderiv 𝕜 f) 0) : f x = f y`
(`MeanValue.lean:618`; book "connected" = `IsPreconnected` for open sets). Status: `direct`.

**Prop 5.3.13 (Taylor remainder)**.
Book: `F` twice continuously differentiable on open `K`, segment `[u₀, u₀+h] ⊂ K` ⇒
`‖F(u₀+h) − F(u₀) − F'(u₀)h‖ ≤ ½ sup_{θ} ‖F''(u₀+θh)‖ ‖h‖²`.
Lean ✓ (`Scratch2.lean` `prop_5_3_13`, `F'' : V → V →L[ℝ] V →L[ℝ] W`).
Route: `φ(t) := F(u₀ + t h) − F u₀ − t • F' u₀ h` on `[0,1]`, `φ'(t) = (F'(u₀+th) − F' u₀) h`, `‖φ'(t)‖ ≤ C t ‖h‖²` by the
MVT for `F'` on the sub-segment (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` applied to `F'`), then
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` (`MeanValue.lean:299`) with boundary `B t = C ‖h‖² t²/2`.
Alternative: `taylor_mean_remainder_bound` (`Taylor.lean:390`) on `t ↦ F(u₀ + t h)` with `n = 1` (needs `ContDiffOn ℝ 2`
of the composite and the identification of `iteratedDerivWithin 2`). Not in Mathlib in this form.
Status: `surface-only`, but the same lemma with a Lipschitz `F'` is exactly (5.4.5) — request it in the backbone (§4 item 3).

**Prop 5.3.15** (Fréchet ⇒ partials, formula (5.3.8); continuous partials near `(u₀,v₀)` ⇒ Fréchet).
Lean: (⇒) `HasFDerivAt (fun u => f u v₀) (f'.comp (ContinuousLinearMap.inl ℝ U V)) u₀` from `HasFDerivAt.comp` with
`hasFDerivAt_prodMk_left`; formula `f' (h,k) = f' (h,0) + f' (0,k)` by linearity.
(⇐) Mathlib `hasStrictFDerivAt_uncurry_coprod` (`FDeriv/Partial.lean:56`; hypotheses: partials exist eventually near
`u` and are continuous at `u`) then `.hasFDerivAt`. Status: `direct`.

**Cor 5.3.16** (`f` is `C¹` near `(u₀,v₀)` iff `f_u, f_v` continuous near it). Route: Prop 5.3.15 both ways +
continuity of `coprod`/`comp inl` (`ContinuousLinearMap.coprodL`?, else `Continuous.clm_comp`). Status: `surface-only`.

**Thm 5.3.17** (Gâteaux-differentiable `f : K → ℝ`, `K` convex: convex ⇔ (b) `f v ≥ f u + ⟨f' u, v − u⟩` ⇔ (c) monotone gradient).
Lean ✓ (`Scratch2.lean` `thm_5_3_17`): `(ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) ∧ (ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u))`.
Route: (a)⇒(b): `ConvexOn.slope_mono` on the 1D restriction `t ↦ f (u + t • (v − u))` (`ConvexOn.comp_affineMap`) +
`HasLineDerivAt.tendsto_slope_zero_right`; (b)⇒(a), (b)⇒(c) algebra; (c)⇒(b): `exists_hasDerivAt_eq_slope`
(`Deriv/MeanValue.lean:122`) for `φ(t) = f(u + t(v−u))` on `(0,1)`. Mathlib only has the 1D versions
(`MonotoneOn.convexOn_of_deriv`). Status: `GAP` (§4 item 5; not needed by §5.4/§5.6 but by AH Ch 8, 11).

**Thm 5.3.18** (strict version). Status: `GAP` (same file as 5.3.17; `StrictConvexOn`).

**Thm 5.3.19** (minimiser ⇔ variational inequality (5.3.10); subspace case (5.3.11)).
Lean ✓ (`thm_5_3_19`): `IsMinOn f K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u)` given convexity; plus
`(K : Submodule) : IsMinOn f K u ↔ ∀ v ∈ K, f' u v = 0`. Route: (⇒) one-sided slope limit
(`HasLineDerivAt.tendsto_slope_zero_right`, `ge_of_tendsto`); (⇐) Thm 5.3.17 (b). Status: `surface-only` (given 5.3.17).

### §5.4 Newton's method

**(5.4.2) Newton iteration** — D10; `newtonSeq_succ : newtonSeq F F' u₀ (n+1) = newtonStep F F' (newtonSeq F F' u₀ n)`,
`newtonStep_sub_eq`. Status: `direct`.

**Thm 5.4.1 (local convergence)**.
Book: `U, W` Banach, `F : U → W` Fréchet differentiable, `F u* = 0`, `[F'(u*)]⁻¹ ∈ L(W,U)`, `F'` Lipschitz with constant
`L > 0` on a neighbourhood `N(u*)`. Then ∃ `δ > 0`: if `‖u₀ − u*‖ ≤ δ` the Newton sequence is well defined and converges to
`u*`, and for some `M` with `Mδ < 1`: (5.4.3) `‖u_{n+1} − u*‖ ≤ M ‖u_n − u*‖²`, (5.4.4) `‖u_n − u*‖ ≤ (Mδ)^{2ⁿ}/M`.
Lean ✓ (`Scratch1.lean` `thm_5_4_1`; `∃ δ > 0, ∃ M > 0, M * δ < 1 ∧ ∀ u₀, ‖u₀ - ustar‖ ≤ δ → (well-defined) ∧ Tendsto … ∧ (5.4.3) ∧ (5.4.4)`;
`0 < M` added so that (5.4.4) is meaningful — harmless, `M = c₀L/2 > 0`).
Backbone: §5.3.2 `newton_local_quadratic` (planned; stated with `Metric.ball` and a supplied `Df`). Proof route (book):
`c₀ = sup_{B̄(u*,δ)} ‖F'(u)⁻¹‖ < ∞` from `ContinuousLinearEquiv.exists_symm_norm_le_of_add` (`Inverse.lean` ✓, AH 2.3.5)
applied to `F' u = F' u* + (F' u − F' u*)` with `‖F' u − F' u*‖ ≤ Lδ < ‖F'(u*)⁻¹‖⁻¹`; then (5.4.5) and the induction.
Status: `GAP` (backbone item planned, not in skeleton — §4 item 3).

**(5.4.5)** `‖T u − T u*‖ ≤ (c₀ L/2) ‖u − u*‖²` for `T u = u − F'(u)⁻¹ F u`, `u ∈ N(u*)`, `‖F'(u)⁻¹‖ ≤ c₀`.
Lean: `theorem eq_5_4_5 (hlipseg : ∀ z ∈ segment ℝ u ustar, ‖F' z - F' u‖ ≤ L * ‖z - u‖) (he : ↑e = F' u) (hc₀ : ‖(e.symm : W →L[ℝ] U)‖ ≤ c₀) (hroot : F ustar = 0) : ‖newtonStep F F' u - ustar‖ ≤ c₀ * L / 2 * ‖u - ustar‖ ^ 2`.
Route: `T u − u* = F'(u)⁻¹ [F u* − F u − F'(u)(u* − u)]`, and the exact-constant Taylor bound
`‖F y − F x − F' x (y − x)‖ ≤ (L/2)‖y − x‖²` via `image_norm_le_of_norm_deriv_right_le_deriv_boundary` (see Prop 5.3.13).
Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` gives only constant `L` (backbone §5.3.2 plans to use it, which
loses the `½`). Status: `GAP` (request the `½` lemma, §4 item 3).

**Thm 5.4.2 (Kantorovich)**.
Book: (a) `F : D(F) ⊂ U → W` differentiable on an open convex `D(F)`, `‖F'(u) − F'(v)‖ ≤ L‖u − v‖` on `D(F)`; (b) `[F'(u₀)]⁻¹`
exists, bounded, `h = abL ≤ ½` with `a ≥ ‖F'(u₀)⁻¹‖`, `b ≥ ‖F'(u₀)⁻¹F(u₀)‖`, `t* = (1 − √(1−2h))/(aL)`, `t** = (1 + √(1−2h))/(aL)`;
(c) `B̄(u₁, r) ⊂ D(F)`, `r = t* − b`. Then ∃ solution `u* ∈ B̄(u₁, r)`, unique in `B̄(u₀, t**) ∩ D(F)`, `u_n → u*`, and
`‖u_n − u*‖ ≤ (1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)`.
Lean ✓ (`Scratch1.lean` `thm_5_4_2`, all constants written out; add `0 < a`, `0 < L` if the formulas are to be
meaningful — with `L = 0` the book's `t*` is `0/0`).
Backbone: §5.3.2 `newton_kantorovich` (planned for phase 2, Kress's simpler variant first; majorant-sequence proof,
Ortega–Rheinboldt §12.6 / Zeidler). Status: `GAP` (§4 item 3).

**(5.4.7) Newton for nonlinear systems in ℝᵈ** and the form `F'(x_n) δ_n = −F(x_n)`, `x_{n+1} = x_n + δ_n`.
Lean: instantiate `newtonSeq` with `U = W = EuclideanSpace ℝ (Fin d)`; `newtonStep_sub_eq`. Status: `direct`.

**(5.4.8)–(5.4.12)** (Newton for the Urysohn equation on `C[0,1]`, the modified Newton (5.4.11), and the BVP `u'' = f(t,u)`
in `C²₀[0,1]`). Status: `out-of-scope` (function-space calculus, phase 3; the modified Newton convergence is Ex 5.4.5, an
exercise — see §5).

### §5.5 Completely continuous vector fields (summary)

Thm 5.5.1 (Brouwer), Ex 5.5.2 (Kakutani-type map without fixed point on the unit ball of an infinite-dimensional Hilbert
space), Def 5.5.3 (compact / completely continuous nonlinear operators), Thm 5.5.4 (Schauder), Prop 5.5.5 (`T'(v₀)` compact),
and the rotation/index properties P1–P5 are all quoted without proof from Krasnoselskii/Berger/Zeidler; none is in
Mathlib (Brouwer: only the 1D `exists_mem_Icc_isFixedPt`; compact operators: `IsCompactOperator` and the Fredholm
alternative `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` — linear only). Status: `out-of-scope` (all).

### §5.6 Conjugate gradient method for operator equations

**Setting: `Au = f` uniquely solvable, `A⁻¹` bounded** (book: by Thm 5.1.4).
Lean: `theorem existsUnique_solution (hA : IsSelfAdjoint A) (hbound) (f) : ∃! u, A u = f` and `‖A⁻¹‖ ≤ 1/m`.
Backbone: `ContinuousLinearMap.exists_equiv_of_isCoerciveWith` (`Coercive.lean` ✓) with `c := m` via D13.
Status: `direct` (`needs-equivalence` through D13's `bound_iff`).

**(5.6.2) CG recurrences** — D11; equivalence `cg_eq_CG_iterate` with backbone `CG.iterate` (§3.7, planned).
Status: `needs-equivalence` (backbone `Krylov/CG.lean` not yet in skeleton).

**Thm 5.6.1** (linear convergence; Patterson).
Book: `A` bounded self-adjoint with (5.6.3) `√m‖v‖ ≤ ‖v‖_A ≤ √M‖v‖`, `m, M > 0`. Then `u_k → u*` and
(5.6.4) `‖u* − u_{k+1}‖_A ≤ (M−m)/(M+m) ‖u* − u_k‖_A`.
Lean ✓ (`Scratch1.lean` `thm_5_6_1`):
```lean
theorem thm_5_6_1 {A : V →L[ℝ] V} (hA : IsSelfAdjoint A) {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    {f u₀ ustar : V} (hstar : A ustar = f) :
    Tendsto (fun k => (cg A f u₀ k).u) atTop (𝓝 ustar) ∧
    ∀ k, normA A (ustar - (cg A f u₀ (k + 1)).u) ≤ (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u)
```
Route for (5.6.4): `u_{k+1}` is the Galerkin iterate on `u₀ + 𝒦_{k+1}(A, r₀)` (backbone `CG.isGalerkinIterate`, §3.7);
`u_k + α r_k ∈ u₀ + 𝒦_{k+1}` for every `α` (`u_k − u₀ ∈ 𝒦_k`, `r_k ∈ 𝒦_{k+1}`, `Krylov.subspace_mono` ✓), so by
`IsGalerkin.energyNorm_le` (`Optimality.lean` ✓) `‖e_{k+1}‖_A ≤ ‖(1 − αA) e_k‖_A`; with `α = 2/(M+m)` the degree-1
polynomial bound on the two-dimensional compression `K = span{e_k, A e_k}` (§4 item 1) gives
`max_{λ∈[m,M]} |1 − αλ| = (M−m)/(M+m)`. (Equivalently: the backbone steepest-descent bound
`Projection.energyNorm_steepestDescentStep_le` (`OneDimensional.lean` ✓, `[FiniteDimensional]`) lifted by the same
compression trick, since CG's `u_{k+1}` beats the SD step from `u_k`.) Convergence: (5.6.4) iterated, `(M−m)/(M+m) < 1`,
and `√m ‖·‖ ≤ ‖·‖_A`. Status: `GAP` (needs §3.7 + the Hilbert-space polynomial bound — §4 item 1).

**(5.6.5)** `‖u* − u_k‖_A ≤ 2 ((√M − √m)/(√M + √m))^k ‖u* − u₀‖_A` (Patterson; quoted).
Lean ✓ (`eq_5_6_5`). Backbone: §3.10 `Krylov.IsGalerkinIterate.energyNorm_error_le` (planned, `[FiniteDimensional ℝ E]`,
eigenvalue hypotheses) + `ForMathlib/Polynomial/ChebyshevMinimax.lean` ✓ (`one_div_eval_T_le_sSup_abs_eval_of_eval_zero`,
`one_div_eval_T_le_two_mul_pow`). Route: the compression trick with generator `e₀ = u* − u₀` — worked out in §4 item 1.
Status: `GAP` (§4 item 1).

**(5.6.6)** `(√M − √m)/(√M + √m) ≤ (M − m)/(M + m)` (Ex 5.6.1).
Lean ✓ (`eq_5_6_6 (hm : 0 < m) (hmM : m ≤ M)`). Route: with `s = √m`, `t = √M`, `(t−s)(t²+s²) ≤ (t+s)(t²−s²)` ⇔ `0 ≤ 2st`;
`div_le_div_iff`, `nlinarith [Real.sq_sqrt hm.le, Real.sq_sqrt (hm.le.trans hmM), Real.sqrt_nonneg m, Real.sqrt_nonneg M]`.
Status: `direct`.

**(5.6.7)–(5.6.9)** (eigen-decomposition of the compact self-adjoint `K`, `λ_j → 0`, `δ = inf(1−λ_j) > 0 ⇔ A` positive definite,
`Δ = sup(1−λ_j)`, `‖A‖ = Δ`, `‖A⁻¹‖ = 1/δ`).
Status: `out-of-scope` — relies on AH Thm 2.8.15/2.8.12 (spectral theorem for compact self-adjoint operators), absent from Mathlib
(only `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` (finite-dimensional) and the Fredholm alternative). (5.6.9) becomes
`surface-only` if the eigenbasis is taken as a hypothesis (see Thm 5.6.2 variant).

**(5.6.10)** `‖u* − u_{k+1}‖_A ≤ (Δ−δ)/(Δ+δ) ‖u* − u_k‖_A` for `A = I − K`.
Route: (5.6.4) with `(m, M) = (δ, Δ)`; the bounds `δ‖v‖² ≤ (Av,v) ≤ Δ‖v‖²` from Parseval in the eigenbasis
(`HilbertBasis.hasSum_repr`/`tsum` of `(1−λ_j)|(v,φ_j)|²`). Status: `needs-equivalence` (from (5.6.4), under the eigenbasis hypothesis).

**Thm 5.6.2 (Winther, superlinear convergence)**.
Book: `K` compact self-adjoint, `A = I − K` self-adjoint positive definite ⇒ `‖u* − u_k‖ ≤ c_k^k ‖u* − u₀‖` with
`c_k = (Δ/δ)^{3/(2k)} (2/k) Σ_{j≤k} |λ_j|/(1−λ_j) → 0` (5.6.21).
Faithful statement: `out-of-scope` (compact spectral theorem). Surface-only variant (recommended if wanted): hypotheses
`(φ : HilbertBasis ℕ ℝ V) (λ : ℕ → ℝ) (hK : ∀ j, K (φ j) = λ j • φ j) (hanti : Antitone fun j => |λ j|) (hlim : Tendsto λ atTop (𝓝 0)) (hδ : 0 < δ) (hδ' : ∀ j, δ ≤ 1 − λ j) (hΔ : ∀ j, 1 − λ j ≤ Δ)`,
conclusion (5.6.11) with `c_k` as in (5.6.21). Proof steps:
- **(5.6.12)** `u_k = u₀ + P̃_{k−1}(A) r₀` (Ex 5.6.2): backbone `CG` span property `u_k − u₀ ∈ 𝒦_k(A, r₀)` (§3.7, planned) +
  `Krylov.mem_subspace_iff_exists_aeval` (`Subspace.lean` ✓). Status: `needs-equivalence`.
- **(5.6.13)–(5.6.14)** optimality among `y_k = u₀ + P_{k−1}(K) r₀`: `IsGalerkin.energyNorm_le` ✓ + `Krylov.aeval_apply_mem_subspace` ✓
  + `CG.isGalerkinIterate` (§3.7) + rewriting `P(K) = P̂(A)` (`Polynomial.aeval` of `1 − A`, `Polynomial.comp`). Status: `needs-equivalence`.
- **(5.6.15)** `Q_k(λ) = ∏_{j≤k} (λ−λ_j)/(1−λ_j)`, `Q_k(1) = 1`, `Q_k = 1 − (1−λ)P_{k−1}`: `Polynomial` algebra
  (`Polynomial.X_sub_C_dvd`-style factorisation of `Q_k − 1` at `1`). Status: `surface-only`.
- **(5.6.16)** `‖u* − u_k‖ ≤ (1/δ)√(Δ/δ) ‖r̃_k‖`: `IsCoerciveWith.norm_le_energyNorm` ✓, `IsSymmetricCoercive.energyNorm_le_norm` ✓
  (with `‖A‖ ≤ Δ`), `‖A⁻¹‖ ≤ 1/δ` from `exists_equiv_of_isCoerciveWith` ✓. Status: `direct`.
- **(5.6.17)** `r̃_k = Q_k(A) r₀`: `Polynomial.aeval` algebra. Status: `surface-only`.
- **(5.6.18)–(5.6.19)** `‖r̃_k‖ ≤ α_k ‖r₀‖`, `α_k = sup_{j>k} |Q_k(λ_j)| ≤ ∏_{j≤k} 2|λ_j|/(1−λ_j)`: `Module.End.aeval_apply_of_hasEigenvector`
  (`Q_k(A) φ_j = Q_k(λ_j) φ_j`), `HilbertBasis.repr` + Parseval, the product estimate from `hanti`. Status: `surface-only`.
- **(5.6.20)** `(2/k) Σ_{j≤k} |λ_j|/(1−λ_j) → 0` (Ex 5.6.3): Mathlib `Filter.Tendsto.cesaro` (`SpecificAsymptotics.lean:189`)
  applied to `j ↦ |λ_j|/(1−λ_j) → 0` (`hlim`, `hδ`), with the AM–GM step `(∏ b_j)^{1/k} ≤ (1/k)Σ b_j`
  (`Real.inner_le_nnorm_mul_nnnorm`? — use `Real.geom_mean_le_arith_mean_weighted`). Status: `direct` (Cesàro), `surface-only` (AM–GM assembly).
- **(5.6.21)/(5.6.11)** assembly. Status: `surface-only`.

**Thm 5.6.3** (rates of `τ_ℓ` for Hilbert–Schmidt kernels (5.6.24) and `C^p` symmetric kernels (5.6.25)).
Status: `out-of-scope` (integral operators on `L²(a,b)`, `Σλ_j² = ‖K‖²_HS`, Fenyö–Stolle eigenvalue asymptotics).

**Closing remark of §5.6** (`u_k − u₀ ∈ 𝒦(A)`; `‖u* − u_k‖_A = min_{y ∈ u₀ + 𝒦_k} ‖u* − y‖_A`).
Backbone: `IsGalerkin.iff_energyNorm_min` (`Optimality.lean` ✓) + `CG.isGalerkinIterate` (§3.7). Status: `needs-equivalence`.

**Status tally** (60 status labels over the blocks above, sub-statuses counted separately): `direct` 27, `needs-equivalence` 8, `GAP` 15, `surface-only` 14,
`out-of-scope` 7 (§5.5 counted as one block).

## Gaps and requests to the backbone

1. **Hilbert-space CG bounds (Thm 5.6.1, (5.6.4), (5.6.5)) — the "compression trick" of backbone §5.2.3, evaluated.**
   The backbone's §3.9/§3.10 statements (`LinearMap.IsSymmetric.norm_aeval_apply_le`, `Krylov.IsGalerkinIterate.energyNorm_error_le`)
   carry `[FiniteDimensional 𝕜 E]` and spectral hypotheses; the book's Thm 5.6.1 is on an arbitrary (separable) real Hilbert
   space with only the quadratic-form bounds (5.6.3). The trick works, **but only if the compression is taken on the Krylov
   space generated by the error, not by the residual**:
   *Setting.* `A : E →ₗ[𝕜] E` symmetric with `m‖v‖² ≤ re⟪Av,v⟫ ≤ M‖v‖²`, `A x* = b`, `e₀ := x* − x₀`, `r₀ = A e₀`,
   `x` a Galerkin iterate on `x₀ + 𝒦_k(A, r₀)`. Put `K := 𝒦_{k+1}(A, e₀)` (finite-dimensional, so `K.HasOrthogonalProjection`) and
   `A_K := compression A K` (`Compression.lean` ✓).
   *Step 1 (polynomial form of the error).* `y − x₀ ∈ 𝒦_k(A, r₀)` iff `y − x₀ = s(A) r₀ = s(A) A e₀` with `deg s < k`
   (`Krylov.mem_subspace_iff_exists_aeval` ✓), so `x* − y = q(A) e₀` with `q := 1 − X·s`, `q(0) = 1`, `deg q ≤ k`; conversely every
   such `q` arises. `IsGalerkin.energyNorm_le` ✓ gives `‖x* − x‖_A ≤ ‖q(A) e₀‖_A` for all admissible `q`.
   *Step 2 (transport to `K`).* For `deg q ≤ k`, `q(A) e₀ = q(A_K) ⟨e₀,_⟩` — this is the planned §2.1.6 lemma
   `aeval_compression_krylov` (Saad Prop 6.3: `A_K^j e₀ = A^j e₀` for `j ≤ k` because `A^j e₀ ∈ K`); and
   `‖w‖_{A_K} = ‖w‖_A` for `w ∈ K` by `compression.inner_apply` ✓. Hence `‖q(A) e₀‖_A = ‖q(A_K) e₀‖_{A_K}`.
   *Step 3 (spectrum of `A_K`).* `A_K` is symmetric (`compression.isSymmetric` ✓) and satisfies the same two-sided bounds
   (`inner_apply` ✓), so by `IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue` ✓ and an upper-bound twin
   (**new**: `IsSymmetric.re_hasEigenvalue_le_of_forall_re_inner_le`) all eigenvalues of `A_K` lie in `[m, M]`.
   *Step 4.* Apply the finite-dimensional bound `IsSymmetricCoercive.energyNorm_aeval_apply_le` (§3.9) on `K`:
   `‖q(A_K) e₀‖_{A_K} ≤ max_{[m,M]} |q| · ‖e₀‖_{A_K} = max_{[m,M]}|q| · ‖e₀‖_A`, then Chebyshev min–max
   (`ChebyshevMinimax.lean` ✓) for (5.6.5), and `q(λ) = 1 − 2λ/(M+m)` for (5.6.4) (applied to `e_k` with `K = 𝒦_2(A, e_k)`).
   *What is wrong with generator `r₀`.* With `K = 𝒦_{k+1}(A, r₀)` the CG iterates of `A` and of `A_K` coincide, but the
   compressed problem's exact solution `A_K⁻¹ r₀` differs from `e₀ ∉ K`, so the compressed Chebyshev bound bounds the wrong
   quantity (one only gets `‖x* − x‖_A² = ‖e₀‖_A² − ‖A_K⁻¹ r₀‖²_{A_K} + …`, which is circular). Please state in
   `Convergence/CG.lean` that the trick is applied to `𝒦_{k+1}(A, x* − x₀)`.
   *Requested theorems* (all L1 + the L3 lemma on `K`, no completeness, no CFC):
   ```lean
   theorem compression.aeval_apply_of_mem_krylov {v : E} {m : ℕ} (hK : K = Krylov.subspace A v m) {p : 𝕜[X]} (hp : p.degree < m)
       (hv : v ∈ K) : (aeval (compression A K) p ⟨v, hv⟩ : E) = aeval A p v
   theorem compression.energyNorm_apply (w : K) : energyNorm (compression A K) w = energyNorm A (w : E)
   theorem LinearMap.IsSymmetric.re_hasEigenvalue_le_of_forall_re_inner_le (hA : A.IsSymmetric) {M : ℝ}
       (h : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ M * ‖x‖ ^ 2) {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) : RCLike.re μ ≤ M
   /-- Hilbert-space Chebyshev bound (AH (5.6.5), Saad Thm 6.29 without finite dimension). -/
   theorem IsGalerkin.energyNorm_error_le_of_forall_inner_le (hA : A.IsSymmetric) {m M : ℝ} (hm : 0 < m)
       (hlow : A.IsCoerciveWith m) (hup : ∀ v, RCLike.re (inner 𝕜 (A v) v) ≤ M * ‖v‖ ^ 2)
       (hx : IsGalerkin A b x₀ (Krylov.subspace A (b - A x₀) k) x) (hstar : A xstar = b) :
       energyNorm A (xstar - x) ≤ 2 * ((√M - √m) / (√M + √m)) ^ k * energyNorm A (xstar - x₀)
   /-- One-step bound (AH (5.6.4)): any Galerkin iterate on a space containing `x_k + span{r_k}`. -/
   theorem IsGalerkin.energyNorm_error_le_of_le_span … : energyNorm A (xstar - x') ≤ (M - m)/(M + m) * energyNorm A (xstar - x)
   ```
   plus `CG.isGalerkinIterate`, `CG.sub_mem_subspace` (`x_k − x₀ ∈ 𝒦_k`), `CG.residual_mem_subspace` (`r_k ∈ 𝒦_{k+1}`) in §3.7.
   The alternative via Mathlib's CFC (`cfc_mono`, `norm_cfc_le`, `ContinuousLinearMap.IsPositive.spectrumRestricts` in
   `InnerProductSpace/StarOrder.lean`) needs a CFC instance on `V →L[ℝ] V` for the real scalar field (present for
   `H →L[𝕜] H` with `RCLike 𝕜` per `StarOrder.lean`, to be double-checked) and an `energyNorm`–`A^{1/2}` bridge; the compression
   route is shorter and stays at L1/L3.

2. **`Nonlinear/FixedPoint.lean` (§5.3.1) — needed now by the surface, not in the skeleton.**
   (a) `dist`-form glue for `ContractingWith.efixedPoint'` (or the subtype route) packaged as one lemma giving (5.1.4)–(5.1.6);
   (b) `tendsto_iterate_of_iterate_contractingWith (hf : ContractingWith K f^[m]) (hm : 0 < m) (x) : Tendsto (fun n => f^[n] x) atTop (𝓝 (hf.fixedPoint _))`
   — residue-class argument; note continuity of `f` is not needed; together with `isFixedPt_fixedPoint_iterate` this is Ex 5.1.2
   and the engine of Thm 5.2.3 and of Mathlib's own Picard–Lindelöf proof;
   (c) `zarantonello` as planned, with the explicit factor `√(1 − 2θc₁ + θ²c₂²)` (the book's constants in the proof are swapped — see §6)
   and the corollary `‖u₁ − u₂‖ ≤ ‖b₁ − b₂‖/c₁`; the linear case should be derived from `exists_equiv_of_isCoerciveWith`
   or vice versa (the surface will prove `stronglyMonotoneWith_iff_isCoerciveWith`).

3. **`Nonlinear/Newton.lean` (§5.3.2).** (a) Define `newtonStep F F' u := u − (F' u).inverse (F u)` with `ContinuousLinearMap.inverse`
   (total, matches the book, no supplied `Df`; add `newtonStep_eq_of_equiv`). (b) Thm 5.4.1 with `0 < M` and both (5.4.3), (5.4.4).
   (c) The exact-constant Taylor bound
   `norm_sub_sub_fderiv_le_half_mul_sq (hlip : ∀ z ∈ segment ℝ x y, ‖F' z − F' x‖ ≤ L * ‖z − x‖) : ‖F y − F x − F' x (y − x)‖ ≤ L / 2 * ‖y − x‖ ^ 2`
   via `image_norm_le_of_norm_deriv_right_le_deriv_boundary` — this is (5.4.5) and Prop 5.3.13 in one; the planned use of
   `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` yields `L`, not `L/2`, so the surface could not state (5.4.5) faithfully.
   (d) Kantorovich (Thm 5.4.2) in AH's form (phase 2 as planned) with explicit `t*, t**` and the `2⁻ⁿ`-error bound; hypotheses `0 < a`, `0 < L`.

4. **`Nonlinear/Calculus.lean` (new, small).** `HasGateauxDerivAt` (D7) and Prop 5.3.4 (iii)
   `hasFDerivAt_of_hasGateauxDerivAt_continuousAt`; Prop 5.3.13 (`½ sup‖F''‖‖h‖²`, from 3(c) + MVT for `F'`). Also used by Kress Ch 6
   and AH Ch 11.

5. **Convexity via Gâteaux derivatives (Thm 5.3.17–5.3.19)** — Mathlib gap in general normed spaces (1D only in
   `Analysis/Convex/Deriv.lean`). Not needed by §5.4/§5.6, but AH Ch 8.8/Ch 11 and any optimisation source will need it: propose
   `Nonlinear/Convex.lean` with `ConvexOn.of_forall_le_add_lineDeriv`, `ConvexOn.forall_le_add_lineDeriv`,
   `convexOn_iff_monotone_lineDeriv`, `isMinOn_iff_forall_lineDeriv_nonneg`.

6. **§5.2.2 bridge.** (a) `Matrix.Splitting` (§2.3.2) — please note the naming/sign difference with AH (`A = N − M`, `N` invertible);
   the surface adds `BookSplitting.toSplitting`. (b) Real-matrix complexification (§2.1.11): `spectralRadius ℂ (A.map ofReal)`,
   `map_pow`, and `tendsto_pow_iff` transfer, so that `(N⁻¹M)ⁿ → 0 ⇔ r_σ < 1` holds for `Matrix n n ℝ`.
   (c) Optional: Gelfand for a general matrix norm via norm equivalence.

7. **`C[a,b]` integral-operator toolkit (phase 3, but it is the only obstacle to Thm 5.2.2–5.2.4 and to the whole of AH Ch 12 / Kress Ch 10–12).**
   Propose `Numlib/IntegralEquations/Basic.lean`: bundled Fredholm/Urysohn/Volterra operators `C(Icc a b, ℝ) → C(Icc a b, ℝ)`
   (continuity from `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`), Lipschitz bounds
   (`|μ|·M·(b−a)`; Fredholm `α = max_x ∫|k|/|λ|`), the Volterra factorial estimate, and a `Bielecki β` type synonym with norm
   equivalence and the contraction `M/β`. With these, Thm 5.2.2 is `direct`, Thm 5.2.3 is item 2(b) + factorial bound, and the
   iteration part of Thm 5.2.4 is Thm 5.1.3 on the closed ball in `Bielecki L`.

8. **Winther (Thm 5.6.2).** Blocked by the compact self-adjoint spectral theorem (Mathlib gap; AH Thm 2.8.15) — phase 2+ as
   planned. The `Krylov/Iterate.lean` residual-polynomial lemma (`b − A x = q(A)(b − A x₀)`, `q(0)=1`, `deg q ≤ k`, prototyped in
   `plans/prototypes/Proto1.lean`) and `CG.sub_mem_subspace` are the only backbone pieces the surface-only variant needs.

9. **Minor.** `IsSymmetricCoercive.energyNorm_le_norm` gives `√‖A‖`; a version with an arbitrary upper bound `M` on the quadratic
   form (`energyNorm_le_sqrt_mul_norm_of_forall_re_inner_le`) matches (5.6.3)/(5.6.16) directly. `Krylov.subspace` needs a
   `FiniteDimensional` instance for `Submodule.HasOrthogonalProjection` (span of a finite image — presumably `Finset`/`Set.Iio`
   finiteness; please provide `instance : FiniteDimensional 𝕜 (Krylov.subspace A v m)`).

## Left out

- Ex 5.1.1 (kept optional), Ex 5.1.3, Ex 5.1.4 (not cited by theorems; Ex 5.1.4 is the local version mentioned in backbone §5.3.1).
- §5.2.1 remarks on `T x = x − c₀ f(x)` and Newton's scalar form (motivation only).
- §5.2.2 componentwise Jacobi/GS/SOR formulas and the optimal-`ω` discussion; Ex 5.2.2 (diagonal dominance — backbone §2.3.3), Ex 5.2.3 (Richardson; `0 < θ < 2/λ_max`).
- Ex 5.2.4–5.2.11 (error bounds for the integral-equation iterations; systems of Volterra equations; second-order IVP) and Ex 5.2.12–5.2.13
  (Gronwall — Mathlib `norm_le_gronwallBound_of_norm_deriv_right_le`, `dist_le_of_approx_trajectories_ODE` already cover them).
- Hammerstein and Nekrasov equations (5.2.14) (no theorem).
- Ex 5.3.1–5.3.17 (counterexamples, Jacobian, norm differentiability, Hessian criterion in ℝᵈ, `f(v) = ½(Av,v)`, energy functional — the
  last two reappear in Ch 8/9 and belong to the variational surface).
- Ex 5.3.9 (Jacobian), Ex 5.3.10 (Urysohn derivative), the paragraph on "maps of several variables" after Cor 5.3.16.
- §5.4.2 applications except (5.4.7): integral equation (5.4.8)–(5.4.12) (has an OCR/typo issue anyway), modified Newton (5.4.11) = Ex 5.4.5
  (backbone §5.3.2 lists a chord-Newton lemma; add to the surface when it exists), the BVP in `C²₀[0,1]`; Ex 5.4.1–5.4.4.
- §5.5 entirely (Brouwer, Kakutani-type example, Schauder, Prop 5.5.5, rotation P1–P5): quoted results, no Mathlib support.
- (5.6.7)–(5.6.9) as theorems about compact operators, Thm 5.6.2 in its faithful form, Thm 5.6.3, (5.6.22)–(5.6.26), Ex 5.6.1–5.6.3 as
  standalone exercises (they appear inside the corresponding results above).

## OCR uncertainties

- **Thm 5.1.4 proof** (book erratum, not OCR): `‖T_θ v₁ − T_θ v₂‖² ≤ (1 − 2c₂θ + c₁²θ²)‖v₁ − v₂‖²` and `θ ∈ (0, 2c₂/c₁²)` should read
  `1 − 2c₁θ + c₂²θ²` and `θ ∈ (0, 2c₁/c₂²)`; the theorem statement is unaffected.
- **(5.6.3)**: the OCR reads `√m ‖v‖ ≤ ‖v‖_A ≤ √M ‖v‖`; `plans/analysis/atkinson-han.md` recorded `m‖v‖ ≤ ‖v‖_A ≤ M‖v‖` and flagged an
  inconsistency with (5.6.9)–(5.6.10). The OCR form is the consistent one (`m‖v‖² ≤ (Av,v) ≤ M‖v‖²`, matching `m = δ`, `M = Δ` and
  Saad Thm 6.29); the surface uses it.
- **(5.4.10), (5.4.12)**: right-hand sides `−u_n(t) + ∫ k(t,s,u_n(s)) u_n(s) ds` carry a spurious factor `u_n(s)` (should be `∫ k(t,s,u_n(s)) ds`,
  i.e. `−F(u_n)`); left out anyway.
- **(5.6.17)** and the line before it use `b` and `y₀` for `f` and `u₀`; read as `f`, `u₀`.
- **Thm 5.2.4**: `Q_b ≡ {(t,u) ∈ ℝ × V | |t − t₀| ≤ a, ‖u − z‖ ≤ b}` (bars garbled); "for any initial value `u₀` for which `‖z − u₀‖ < b`"
  is read as a constant initial function (any continuous `u₀` with `sup_t ‖u₀(t) − z‖ ≤ b` works in the proof); the weight `e^{−L|t−t₀|}`
  and `α = 1 − e^{−L a₀}` are consistent with the Bielecki computation (`β = L`).
- **Thm 5.4.2**: `h = abL ≤ 1/2`, `t* = (1 − (1−2h)^{1/2})/(aL)`, error bound `[1 − (1−2h)^{1/2}]^{2ⁿ}/(2ⁿ aL)` — matches the standard
  Zeidler/Kantorovich statement (for `h = ½` it degenerates to the linear rate `2⁻ⁿ/(aL)`); the analysis file marked the exact form
  "[uncertain]"; the OCR is clean here.
- **Def 5.3.1 convention**: "interior point" via the *closed* ball `{‖u − u₀‖ ≤ r} ⊂ K` — equivalent to `K ∈ 𝓝 u₀`.
- **Prop 5.3.11** statement/proof: `sup_{0≤θ≤1}‖F'((1−θ)u+θw)‖` vs the proof's `g(t) = T(F(tu + (1−t)w))` — consistent.
- **Thm 5.3.19**: "there exists `u ∈ K` such that (5.3.9) iff there exists `u ∈ K` such that (5.3.10)" — the proof shows the stronger
  pointwise equivalence for a fixed `u`; the surface states the pointwise form.
- **Ex 5.2.9**: "`u ∈ ℝ`" should be `ℝᵈ`; irrelevant.
- **(5.5.2)** hypotheses `k > 1`, `0 < t ≤ √(k²−1)`: clean; irrelevant (left out).
