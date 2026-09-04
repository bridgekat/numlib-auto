# Surface plan: Atkinson–Han — §8.2, 8.3, 8.7, Chapter 9

Scope: Atkinson & Han, *Theoretical Numerical Analysis* (3rd ed.), §8.2 (existence/uniqueness for
operator equations), §8.3 (Lax–Milgram), §8.7 (generalized Lax–Milgram), Chapter 9 (Galerkin,
Petrov–Galerkin, generalized Galerkin/Strang, variational CG). §8.1, §8.4–8.6, §8.8 are recorded
only as one-liners (all need Sobolev spaces; see §5). The book works throughout with **real** Hilbert
spaces, real bilinear forms `a : V × V → ℝ`, `ℓ ∈ V'`, finite-dimensional `V_N`, and the sup in the
inf–sup conditions is taken *without* absolute values (a sign-symmetry lemma is needed once).

The surface represents the book's "bilinear form" as `LinearMap.BilinForm ℝ V` (= `V →ₗ[ℝ] V →ₗ[ℝ] ℝ`)
with unbundled predicates (`IsBoundedWith M`, `IsEllipticWith α`, `LinearMap.IsSymm`); the bundled
`V →L[ℝ] V →L[ℝ] ℝ` is obtained by `LinearMap.mkContinuous₂`. Key finding (checked by compiling
`Scratch.lean` in this directory, Lean `v4.34.0-rc2`): over `ℝ` a bounded bilinear
`V →L[ℝ] V →L[ℝ] ℝ` is accepted *definitionally* where the backbone's sesquilinear
`V →L⋆[ℝ] V →L[ℝ] ℝ` is expected, so the `RCLike` backbone specialises to the real surface without a
conversion function; only `RCLike.re`/`conj` wrappers need `simp` lemmas (§4, G1). All statements in
§3 were written against the local Mathlib (`.lake/packages/mathlib`); the representative ones were
type-checked with `sorry` proofs ("checked" below).

Proposed files (library `AtkinsonHan`, `srcDir = "Surface"`, importing only `Numlib`; two files added
to the list in backbone.md §8.3):

| File | Content |
|---|---|
| `Surface/AtkinsonHan/Ch08/Existence.lean` | §8.2: closed operators, Thm 8.2.1, 8.2.4, Ex 8.2.5, Hilbert case of 8.2.7, Thm 8.2.8 |
| `Surface/AtkinsonHan/Ch08/BilinearForms.lean` | §8.3 start: `BilinForm` predicates, `toCLM`/`ofCLM`, Thm 8.3.1 and the dictionary, `toOperator`, energy norm |
| `Surface/AtkinsonHan/Ch08/LaxMilgram.lean` | Thm 8.3.2, 8.3.3, 8.3.4 (both proofs' ingredients), Ex 8.3.1 |
| `Surface/AtkinsonHan/Ch08/GeneralizedLaxMilgram.lean` | Thm 8.7.1, (8.7.5), Ex 8.7.1, inf–sup ↔ operator-norm lemmas |
| `Surface/AtkinsonHan/Ch09/Galerkin.lean` | §9.1: Galerkin problem, stiffness matrix (9.1.5), Ex 9.1.1–9.1.2, Ritz, Céa, Cor 9.1.4 |
| `Surface/AtkinsonHan/Ch09/PetrovGalerkin.lean` | §9.2: Petrov–Galerkin problem, discrete inf–sup, Thm 9.2.1, Rem 9.2.2, Cor 9.2.3, (9.2.13)–(9.2.14) |
| `Surface/AtkinsonHan/Ch09/Strang.lean` | §9.3: generalized Galerkin problem, Thm 9.3.1, Ex 9.3.1 |
| `Surface/AtkinsonHan/Ch09/CG.lean` | §9.4: `A`, `f`, Algorithm 1 = backbone `CG.iterate`, convergence via Thm 5.6.1, energy derivative |

Naming: namespace `AtkinsonHan`, book numbers in names (`AtkinsonHan.Ch08.thm_8_2_4`,
`AtkinsonHan.Ch09.prop_9_1_3`, …) as in backbone.md §1.4; definitions get descriptive names.

Common preamble (all files): `variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]`
(+ `[CompleteSpace V]` = "Hilbert"), `ℓ : StrongDual ℝ V` (`= V →L[ℝ] ℝ`), `open InnerProductSpace`.

## Book-specific definitions

### D1. Closed operator (Def 8.2.2)
* Book: `T : D(T) ⊂ V → W` (Banach spaces) is closed if `v_n ∈ D(T)`, `v_n → v`, `T v_n → w` imply
  `v ∈ D(T)` and `T v = w`.
* Lean: partial linear operators are `LinearPMap ℝ V W` (`V →ₗ.[ℝ] W`, fields `domain`, `toFun`);
  the book's `D(L)` is `L.domain`, `R(L)` is `LinearMap.range L.toFun`.
* Mathlib counterpart: `LinearPMap.IsClosed` (`IsClosed (f.graph : Set (E × F))`,
  `Mathlib/Topology/Algebra/Module/LinearPMap.lean`).
* Equivalence lemma `LinearPMap.isClosed_iff_seq` (checked):
  ```lean
  theorem isClosed_iff_seq (T : V →ₗ.[ℝ] W) :
      T.IsClosed ↔ ∀ (v : ℕ → T.domain) (x : V) (w : W),
        Tendsto (fun n => (v n : V)) atTop (𝓝 x) → Tendsto (fun n => T (v n)) atTop (𝓝 w) →
          ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = w
  ```
  Proof: `isSeqClosed_iff_isClosed` (metric ⇒ sequential space) + `LinearPMap.mem_graph_iff`.
  "Continuous ⇒ closed": for `f : V →L[ℝ] W`, `(f.toLinearMap.toPMap ⊤).IsClosed` — graph is the
  preimage of the diagonal (`isClosed_diagonal.preimage`); small surface lemma.

### D2. Stability estimate (8.2.2)
* Book: `‖L v‖_W ≥ c ‖v‖_V` for all `v ∈ D(L)`, `c > 0`.
* Lean: `∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖` (for `L : V →ₗ.[ℝ] W`), or `∀ v, c * ‖v‖ ≤ ‖L v‖`
  for `L : V →L[ℝ] W`.
* Mathlib: `AntilipschitzWith (c⁻¹).toNNReal ⇑L`; bridges `AntilipschitzWith.of_le_mul_dist`,
  `AntilipschitzWith.le_mul_dist`, `ContinuousLinearMap.antilipschitz_of_bound`,
  `ContinuousLinearMap.bound_of_antilipschitz`.
* Equivalence lemma `stabilityEstimate_iff_antilipschitz (hc : 0 < c) :
  (∀ v, c * ‖v‖ ≤ ‖L v‖) ↔ AntilipschitzWith ⟨c⁻¹, _⟩ L` (linear maps: `dist = ‖·‖`).

### D3. Annihilators and the dual operator (§8.2, Banach setting)
* Book: `L* : D(L*) ⊂ W' → V'`, `⟨L* w*, v⟩ = ⟨w*, L v⟩` for densely defined `L`;
  `N(L)^⊥ ⊂ V'`, `N(L*)^⊥ ⊂ W` (annihilator / pre-annihilator).
* Mathlib: algebraic `LinearMap.dualMap`, `Submodule.dualAnnihilator`, `Submodule.dualCoannihilator`
  (`Module.Dual`, not `StrongDual`); Hilbert adjoints `ContinuousLinearMap.adjoint` (bounded) and
  `LinearPMap.adjoint` (densely defined; `LinearPMap.adjoint_isClosed`). No continuous Banach
  `dualMap` for unbounded operators was found in the local checkout.
* Surface: **not defined** (only used by Thm 8.2.7, which is out of scope, §5). The Hilbert
  specialisation uses `T†` and `Submodule.orthogonal` instead of annihilators.

### D4. Bilinear forms and their properties (§8.3)
* Book: `a : V × V → ℝ` bilinear; bounded (`|a(u,v)| ≤ M‖u‖‖v‖`), positive (`a(v,v) ≥ 0`),
  strictly positive (`a(v,v) > 0`, `v ≠ 0`), strongly positive / `V`-elliptic
  (`a(v,v) ≥ α‖v‖²`, `α > 0`), symmetric (`a(u,v) = a(v,u)`).
* Lean (`Ch08/BilinearForms.lean`; checked):
  ```lean
  abbrev BilinForm (V) [AddCommGroup V] [Module ℝ V] := LinearMap.BilinForm ℝ V   -- V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  namespace BilinForm
  def IsBoundedWith (a : BilinForm V) (M : ℝ) : Prop := ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖
  def IsBounded (a) : Prop := ∃ M > 0, a.IsBoundedWith M
  def IsPositive (a) : Prop := ∀ v, 0 ≤ a v v
  def IsStrictlyPositive (a) : Prop := ∀ v, v ≠ 0 → 0 < a v v
  def IsEllipticWith (a) (α : ℝ) : Prop := ∀ v, α * ‖v‖ ^ 2 ≤ a v v      -- "strongly positive"
  def IsElliptic (a) : Prop := ∃ α > 0, a.IsEllipticWith α
  -- symmetric: Mathlib `LinearMap.IsSymm a` (structure; `LinearMap.isSymm_def`)
  noncomputable def toCLM (a) {M} (hM : a.IsBoundedWith M) : V →L[ℝ] V →L[ℝ] ℝ :=
    LinearMap.mkContinuous₂ a M (fun u v => by simpa [Real.norm_eq_abs] using hM u v)
  theorem toCLM_apply : a.toCLM hM u v = a u v := rfl
  theorem norm_toCLM_le (hM0 : 0 ≤ M) (hM) : ‖a.toCLM hM‖ ≤ M   -- `LinearMap.mkContinuous₂_norm_le`
  ```
* Mathlib / backbone counterparts and equivalence lemmas:
  * bounded ↔ `IsBoundedBilinearMap ℝ (fun p : V × V => a p.1 p.2)` (`isBounded_iff_isBoundedBilinearMap`;
    ⇐ from `IsBoundedBilinearMap.bound`, ⇒ the four linearity fields come from `a`) and ↔
    `∃ B : V →L[ℝ] V →L[ℝ] ℝ, ∀ u v, B u v = a u v` (`toCLM`; norm bounds
    `ContinuousLinearMap.le_opNorm₂`, `LinearMap.mkContinuous₂_norm_le`).
  * `V`-elliptic ↔ Mathlib `IsCoercive (a.toCLM hM)` (`∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`,
    `Mathlib/Analysis/Normed/Operator/NormedSpace.lean`): `isElliptic_iff_isCoercive`, proof by
    `sq`/`mul_assoc` (checked inside `laxMilgram` below).
  * `IsEllipticWith α` ↔ backbone `SesqForm.IsCoerciveWith (a.toCLM hM) α` (backbone.md §5.2.1;
    `re` on `ℝ` is the identity, `RCLike.re_to_real`): `isEllipticWith_iff_isCoerciveWith`, by `simp`.
  * `IsEllipticWith α` ↔ `LinearMap.IsCoercive (toOperator a hM)` (backbone §2.1.4, via `inner_toOperator`).
  * `LinearMap.IsSymm a` ↔ `∀ u v, a u v = a v u` (`simp [LinearMap.isSymm_def]`, checked) ↔ backbone
    `SesqForm.IsHermitian (a.toCLM hM)` (`RCLike.conj_to_real`) ↔ `(toOperator a hM : V →ₗ[ℝ] V).IsSymmetric`
    ↔ `IsSelfAdjoint (toOperator a hM)` (`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`).
  * `IsSymm ∧ IsElliptic` ↔ `LinearMap.IsSymmetricCoercive (toOperator a hM)` (backbone §2.1.4).
  * positive: Mathlib `LinearMap.IsPositive` *includes* symmetry, so the book's "positive" is only
    `∀ v, 0 ≤ ⟪A v, v⟫`; no backbone counterpart needed. Strictly positive ↔ elliptic in finite
    dimension (`LinearMap.isCoercive_iff_pos`, backbone §2.1.4).

### D5. Operator ↔ form, `A : V → V'` (8.3.1) and `A : V → V` (9.4.5)
* Book: `⟨A u, v⟩ = a(u,v)` with `A ∈ L(V, V')` (§8.3, `V` a real Banach space); in §9.4 the Riesz
  representative `A : V → V`, `(A u, v) = a(u,v)`, and `f ∈ V` with `(f, v) = ℓ(v)`.
* Lean: `V →L[ℝ] StrongDual ℝ V` **is** `V →L[ℝ] V →L[ℝ] ℝ` (`StrongDual ℝ V` unfolds to
  `V →L[ℝ] ℝ`), so `A ↦ a` is
  ```lean
  noncomputable def ofCLM (A : V →L[ℝ] StrongDual ℝ V) : BilinForm V :=
    (ContinuousLinearMap.coeLM ℝ).comp (A : V →ₗ[ℝ] StrongDual ℝ V)
  theorem ofCLM_apply : ofCLM A u v = A u v := rfl
  theorem isBoundedWith_opNorm (A) : (ofCLM A).IsBoundedWith ‖A‖      -- `le_opNorm₂`
  ```
  and `a ↦ A` is `toCLM` (D4). The §9.4 operator (checked):
  ```lean
  noncomputable def toOperator (a : BilinForm V) {M} (hM : a.IsBoundedWith M) : V →L[ℝ] V :=
    InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) (a.toCLM hM)
  theorem inner_toOperator : ⟪toOperator a hM u, v⟫_ℝ = a u v   -- `continuousLinearMapOfBilin_apply`
  noncomputable def rieszRep (ℓ : StrongDual ℝ V) : V := (toDual ℝ V).symm ℓ   -- `f`
  ```
  `‖rieszRep ℓ‖ = ‖ℓ‖` is `LinearIsometryEquiv.norm_map`.
* Backbone counterpart: `SesqForm.toOperator` (§5.2.1) — **it is exactly Mathlib's
  `InnerProductSpace.continuousLinearMapOfBilin`**; request that the backbone make it an `abbrev`
  of it (G5). Equivalence: `toOperator a hM = SesqForm.toOperator (a.toCLM hM)` (`rfl` after that).

### D6. Energy functional, energy inner product and energy norm (Thm 8.3.3, (9.1.7), §9.4)
* Book: `E(v) = ½ a(v,v) − ℓ(v)`; `(u,v)_a = a(u,v)`, `‖v‖_a = √a(v,v)`, equivalent to `‖·‖`:
  `c₁‖v‖ ≤ ‖v‖_a ≤ c₂‖v‖`.
* Lean:
  ```lean
  noncomputable def energy (a : BilinForm V) (ℓ : StrongDual ℝ V) (v : V) : ℝ := (1/2 : ℝ) * a v v - ℓ v
  noncomputable def energyNorm (a : BilinForm V) (v : V) : ℝ := Real.sqrt (a v v)
  ```
* Backbone: `energyInner`, `energyNorm A x = √(re ⟪A x, x⟫)`, `WithEnergy A hA` (§2.1.5);
  `SesqForm.isMinOn_energy_iff` (§5.2.1, energy written `½ re (a v v) − re (ℓ v)`).
* Equivalence lemmas: `energyNorm_eq : energyNorm a v = _root_.energyNorm (toOperator a hM) v`
  (`inner_toOperator`, `re_to_real`); `energy_eq : energy a ℓ v = ½ re (a.toCLM hM v v) − re (ℓ v)` (`simp`);
  `sqrt_alpha_mul_norm_le_energyNorm`, `energyNorm_le_sqrt_M_mul_norm` (`c₁ = √α`, `c₂ = √M`; backbone
  `le_energyNorm`/`energyNorm_le`).

### D7. Galerkin problem (9.1.4), stiffness matrix and load vector (9.1.5)
* Book: `u_N ∈ V_N`, `a(u_N, v) = ℓ(v) ∀ v ∈ V_N`, `V_N ⊂ V` an `N`-dimensional subspace;
  `A = (a(φ_j, φ_i)) ∈ ℝ^{N×N}`, `b = (ℓ(φ_i))`, `u_N = Σ ξ_j φ_j`.
* Lean (checked):
  ```lean
  def GalerkinProblem (a : BilinForm V) (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V) (uN : V) : Prop :=
    uN ∈ VN ∧ ∀ v ∈ VN, a uN v = ℓ v
  def stiffnessMatrix (a : BilinForm V) {N} (φ : Fin N → V) : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun i j => a (φ j) (φ i)
  def loadVector (ℓ : StrongDual ℝ V) {N} (φ : Fin N → V) : Fin N → ℝ := fun i => ℓ (φ i)
  ```
  `V_N` "`N`-dimensional" is `[FiniteDimensional ℝ VN]` (+ `Module.finrank ℝ VN = N` only where `N`
  matters, i.e. in §9.2).
* Backbone: `IsGalerkinSolution (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) ℓ K u` (§5.2.3); operator form
  `IsGalerkin (toOperator a) (rieszRep ℓ) 0 VN u` (§2.4.1).
* Equivalence: `galerkinProblem_iff : GalerkinProblem a ℓ VN u ↔ IsGalerkinSolution (a.toCLM hM) ℓ VN u`
  (`Iff.rfl` up to `toCLM_apply`); then the backbone bridge `isGalerkinSolution_iff_isGalerkin`.

### D8. Petrov–Galerkin problem (9.2.5)
* Book: `U, V` real Hilbert, `a : U × V → ℝ`, `U_N ⊂ U`, `V_N ⊂ V`, `dim U_N = dim V_N = N`;
  `u_N ∈ U_N`, `a(u_N, v_N) = ℓ(v_N) ∀ v_N ∈ V_N`.
* Lean (checked): `a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ`,
  ```lean
  def PetrovGalerkinProblem (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ℓ : StrongDual ℝ V) (UN : Submodule ℝ U)
      (VN : Submodule ℝ V) (uN : U) : Prop := uN ∈ UN ∧ ∀ v ∈ VN, a uN v = ℓ v
  ```
  with `[FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN)`.
* Backbone: `IsPetrovGalerkinSolution … (K L : Submodule 𝕜 V)` (§5.2.3) is **single-space** — see G3.
  Equivalence (after G3): `petrovGalerkinProblem_iff : … ↔ IsPetrovGalerkinSolution (a.toCLM₂ hM) ℓ UN VN u`
  (`toCLM₂` = `LinearMap.mkContinuous₂` for the two-space form).

### D9. Discrete inf–sup constant `α_N` (9.2.6), inf–sup condition (9.2.13)–(9.2.14)
* Book: `sup_{0≠v_N∈V_N} a(u_N,v_N)/‖v_N‖_V ≥ α_N ‖u_N‖_U ∀ u_N ∈ U_N`; uniform version with `α_0`;
  equivalently `inf_{0≠u_N} sup_{0≠v_N} a(u_N,v_N)/(‖u_N‖‖v_N‖) ≥ α_0`.
* Lean (checked; the sup is a real `iSup` over the subtype `{v : VN // v ≠ 0}`, bounded above by
  `M ‖u_N‖` thanks to (9.2.2), so `Real.iSup` is meaningful):
  ```lean
  def DiscreteInfSup (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (UN : Submodule ℝ U) (VN : Submodule ℝ V) (αN : ℝ) : Prop :=
    ∀ uN ∈ UN, αN * ‖uN‖ ≤ ⨆ vN : {v : VN // v ≠ 0}, a uN vN / ‖(vN : V)‖
  def InfSupCondition (a) (UN : ℕ → Submodule ℝ U) (VN : ℕ → Submodule ℝ V) (α₀ : ℝ) : Prop :=
    ∀ N, DiscreteInfSup a (UN N) (VN N) α₀                                   -- (9.2.13)
  noncomputable def infSupValue (a) (UN) (VN) : ℝ :=                          -- the quantity in (9.2.14)
    ⨅ uN : {u : UN // u ≠ 0}, ⨆ vN : {v : VN // v ≠ 0}, a uN vN / (‖(uN : U)‖ * ‖(vN : V)‖)
  ```
  The same shape (with `V` in place of `VN`) is the continuous condition (8.7.2)/(9.2.3).
* Backbone: `babuska_necas` hypothesis `∀ u, α * ‖u‖ ≤ ⨆ v ≠ 0, ‖a u v‖ / ‖v‖` (§5.2.2); the
  natural operator form is `∀ u, α * ‖u‖ ≤ ‖a u‖` (norm of the functional `a u : V →L[𝕜] 𝕜`); G3
  asks for the latter.
* Equivalence lemmas: `iSup_div_eq_iSup_abs_div` (sign symmetry `v ↦ -v`);
  `iSup_div_norm_eq_opNorm (hM) : (⨆ v : {v // v ≠ 0}, |a u v| / ‖v‖) = ‖a.toCLM hM u‖`
  (from `ContinuousLinearMap.sSup_unit_ball_eq_norm`, `Mathlib/Analysis/Normed/Operator/NNNorm.lean`,
  or directly from `opNorm_le_bound`/`le_opNorm`); `discreteInfSup_iff_norm_le`.

### D10. The `N`-dependent norm and `V + V_N` (§9.3)
* Book: `‖·‖_N`, `a_N`, `ℓ_N` defined on `V + V_N = {v + v_N}`; `V_N ⊄ V` allowed.
* Lean: a normed space `W` *is* `V + V_N` equipped with `‖·‖_N` (one `W` per fixed `N`; the
  theorem is stated for one `N` at a time, so no family/type-synonym machinery is needed):
  `{W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
  (VN : Submodule ℝ W) [FiniteDimensional ℝ VN] (u : W)`. The generalized Galerkin problem (9.3.1):
  `GeneralizedGalerkinProblem aN ℓN VN uN : Prop := uN ∈ VN ∧ ∀ v ∈ VN, aN uN v = ℓN v`
  (the same shape as D7 on `W`). The surface wrapper adds the book's `V` (Hilbert), an injection
  `ι : V →ₗ[ℝ] W` and the exact solution `u : V` of (9.1.1); the proof never uses them (G4).
* Backbone: §5.2.3 "First Strang lemma … `V + V_N` setting, type synonym per `N`" (phase 2) — G4
  proposes the abstract-`W` statement above instead.

### D11. The conjugate gradient algorithm (§9.4, Algorithm 1)
* Book: `r_k ∈ V` with `(r_k, v) = ℓ(v) − a(u_k, v)`; `s_0 = r_0`;
  `α_k = ‖r_k‖²/a(s_k,s_k)`, `u_{k+1} = u_k + α_k s_k`, `β_k = ‖r_{k+1}‖²/‖r_k‖²`, `s_{k+1} = r_{k+1} + β_k s_k`.
* Lean (checked with a local `CGState`; reuse the backbone's `CG.State` (fields `x r p`) instead):
  ```lean
  noncomputable def residual (a) (hM) (ℓ) (u : V) : V := (toDual ℝ V).symm (ℓ - a.toCLM hM u)
  theorem inner_residual : ⟪residual a hM ℓ u, v⟫_ℝ = ℓ v - a u v      -- `inner_sub_left`, `toDual_symm_apply`
  noncomputable def cgStep (a) (hM) (ℓ) (st : CG.State V) : CG.State V :=
    let αk := ‖st.r‖ ^ 2 / a st.p st.p
    let u' := st.x + αk • st.p
    let r' := residual a hM ℓ u'
    ⟨u', r', r' + (‖r'‖ ^ 2 / ‖st.r‖ ^ 2) • st.p⟩
  noncomputable def cgIterate (a) (hM) (ℓ) (u₀ : V) (k : ℕ) : CG.State V :=
    (cgStep a hM ℓ)^[k] ⟨u₀, residual a hM ℓ u₀, residual a hM ℓ u₀⟩
  ```
  (Lean's `x/0 = 0` makes the stalled iteration `r_k = 0` fixed at the solution, matching the
  stopping criterion.)
* Backbone: `CG.State`, `CG.step`, `CG.iterate A b x₀ k`, `CG.residual_eq` (§3.7).
* Equivalence: `cgIterate_eq : cgIterate a hM ℓ u₀ k = CG.iterate (toOperator a hM) (rieszRep ℓ) u₀ k`
  by induction on `k`, using `residual_eq : residual a hM ℓ u = rieszRep ℓ - toOperator a hM u`
  (`map_sub`, definition of `continuousLinearMapOfBilin`), `inner_toOperator` for `a s s = ⟪A s, s⟫`,
  and `CG.residual_eq` if the backbone updates `r` recursively (G5).

## Results

Status legend: `direct` = Mathlib/backbone theorem applies as is; `needs-equivalence` = specialisation
through the D-lemmas above; `GAP` = backbone item missing or not yet in the planned shape;
`surface-only` = short self-contained proof; `out-of-scope` = not formalisable with the current
backbone/Mathlib (reason given).

### §8.2 General existence and uniqueness

**Thm 8.2.1.** `V, W` Hilbert, `L : D(L) ⊂ V → W` linear: `R(L) = W` iff `R(L)` is closed and `R(L)^⊥ = {0}`.
* Lean (checked): `theorem thm_8_2_1 [CompleteSpace W] (L : V →ₗ.[ℝ] W) : LinearMap.range L.toFun = ⊤ ↔
  IsClosed (LinearMap.range L.toFun : Set W) ∧ (LinearMap.range L.toFun)ᗮ = ⊥` (only `W` complete is
  used; `V` needs no completeness or inner product).
* Mathlib: `Submodule.topologicalClosure_eq_top_iff` (`K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥`,
  `[CompleteSpace E]`), `IsClosed.submodule_topologicalClosure_eq`, `isClosed_univ`,
  `Submodule.top_orthogonal_eq_bot`.
* Proof route: `→`: `⊤` is closed and `⊤ᗮ = ⊥`. `←`: closed ⇒ `topologicalClosure = range`, apply the
  iff. (The book separates by Hahn–Banach; the orthogonal-projection proof is what Mathlib has.)
* Status: **direct**.

**Def 8.2.2 / remark "continuous ⇒ closed".** See D1. Status: **needs-equivalence** (`isClosed_iff_seq`),
continuity ⇒ closed **surface-only**.

**(8.2.2) stability estimate.** See D2. Status: **needs-equivalence** (antilipschitz).

**Thm 8.2.4.** `V, W` Hilbert, `L : D(L) ⊂ V → W` linear closed, (8.2.2) with `c > 0`, `R(L)^⊥ = {0}`.
Then for each `f ∈ W` the equation `L u = f` has a unique solution `u ∈ D(L)`.
* Lean (checked): `theorem thm_8_2_4 [CompleteSpace V] [CompleteSpace W] (L : V →ₗ.[ℝ] W)
  (hL : L.IsClosed) {c} (hc : 0 < c) (hstab : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖)
  (horth : (LinearMap.range L.toFun)ᗮ = ⊥) (f : W) : ∃! u : L.domain, L u = f`.
* Backbone: §5.2.2 `bijective_of_antilipschitz_of_orthogonal_range_eq_bot` is stated for
  **bounded** `L : V →L[𝕜] W` only.
* Proof route (for the backbone `LinearPMap` version, G2): the graph `G = L.graph` is closed hence
  complete (`IsClosed.completeSpace_coe`); `Prod.snd : G → W` is antilipschitz with constant
  `max 1 c⁻¹` (`‖(v, L v)‖ = max ‖v‖ ‖L v‖ ≤ max 1 c⁻¹ · ‖L v‖`), so `AntilipschitzWith.isClosed_range`
  gives `R(L)` closed; then `thm_8_2_1`; uniqueness from (8.2.2).
* Status: **GAP** (needs the closed-operator version; the bounded corollary is then `needs-equivalence`).

**Remark after 8.2.4 (continuity replaces closedness).** `L : V →L[ℝ] W`, stability, `(range L)ᗮ = ⊥`
⇒ `Function.Bijective L`. Backbone §5.2.2 item; Mathlib pieces `AntilipschitzWith.isClosed_range`
(`L.uniformContinuous`), `topologicalClosure_eq_top_iff`. Status: **needs-equivalence** (D2).

**Ex 8.2.5.** `V` Hilbert, `L ∈ L(V, V')` strongly monotone (`⟨L v, v⟩ ≥ c‖v‖²`) ⇒ (8.2.2) with the
same `c`, `R(L)^⊥ = {0}` (in the duality sense), hence `L u = f` uniquely solvable for all `f ∈ V'`.
* Lean (checked): `theorem ex_8_2_5 [CompleteSpace V] (L : V →L[ℝ] StrongDual ℝ V) {c} (hc : 0 < c)
  (hmono : ∀ v, c * ‖v‖ ^ 2 ≤ L v v) : (∀ v, c * ‖v‖ ≤ ‖L v‖) ∧ (∀ v, (∀ w, L w v = 0) → v = 0) ∧
  Function.Bijective L`.
* Mathlib: `IsCoercive.bounded_below` (`C * ‖v‖ ≤ ‖B♯ v‖`, and `‖B♯ v‖ = ‖B v‖` by
  `LinearIsometryEquiv.norm_map`), `IsCoercive.continuousLinearEquivOfBilin` (bijective `B♯`;
  transport to `B = toDual ∘ B♯` by `toDual` bijective).
* Status: **direct**.

**Thm 8.2.7 (closed range theorem).** `V, W` Banach, `L` densely defined closed: (a) `R(L)` closed ⇔
(b) `R(L) = N(L*)^⊥` ⇔ (c) `R(L*)` closed ⇔ (d) `R(L*) = N(L)^⊥`; abstract Fredholm alternative.
* Status: **out-of-scope** in the stated generality (Banach dual of an unbounded operator; not in
  Mathlib, see D3). Hilbert-space, bounded specialisation is **direct**: for `T : V →L[ℝ] W`,
  `T.rangeᗮ = T†.ker` (`ContinuousLinearMap.orthogonal_range`) and
  `Submodule.orthogonal_orthogonal_eq_closure` give `IsClosed (range T) → range T = (ker T†)ᗮ`, i.e.
  `f ∈ range T ↔ ∀ w, T† w = 0 → ⟪w, f⟫ = 0` — record as `thm_8_2_7_hilbert` with a docstring.

**Thm 8.2.8.** `T : D(T) ⊂ V → W` (nonlinear), `w ∈ W`: at most one solution of `T u = w` if
(a) `‖T u − T v‖ ≥ c‖u − v‖` on `D(T)` (`c > 0`), or (b) `‖(T u − u) − (T v − v)‖ < ‖u − v‖` for `u ≠ v`
(here `W = V`).
* Lean (checked for (a)): `theorem thm_8_2_8a (D : Set V) (T : V → W) {c} (hc : 0 < c)
  (hstab : ∀ u ∈ D, ∀ v ∈ D, c * ‖u - v‖ ≤ ‖T u - T v‖) (w : W) :
  ∀ u₁ ∈ D, ∀ u₂ ∈ D, T u₁ = w → T u₂ = w → u₁ = u₂`; (b) analogous with `T : V → V`.
  Remark: linear case (a) = (8.2.2) — `Iff.rfl` after `map_sub`.
* Mathlib: `AntilipschitzWith.injective`/`Set.InjOn`; (b) is a two-line contradiction.
* Status: **surface-only**.

### §8.3 The Lax–Milgram Lemma

**Remark (before 8.3.1): `a` continuous iff `∃ M > 0, |a(u,v)| ≤ M‖u‖‖v‖`.**
* Lean: `theorem continuous_iff_isBounded (a : BilinForm V) :
  Continuous (fun p : V × V => a p.1 p.2) ↔ a.IsBounded`.
* Mathlib: ⇐ `IsBoundedBilinearMap.continuous`; ⇒ needs the standard "continuous at `0` ⇒ bounded on
  a ball ⇒ bound `δ⁻²`" argument (not found as a bilinear lemma).
* Status: **surface-only** (small; optional).

**Thm 8.3.1.** `V` real Banach: one-to-one correspondence `A ∈ L(V, V')` ↔ continuous bilinear
`a : V × V → ℝ` via `⟨A u, v⟩ = a(u, v)`; `|a(u,v)| ≤ ‖A‖‖u‖‖v‖` and `‖A‖ ≤ M`.
* Lean (`[NormedSpace ℝ V]`, no completeness):
  ```lean
  noncomputable def thm_8_3_1 : (V →L[ℝ] StrongDual ℝ V) ≃ {a : BilinForm V // a.IsBounded}   -- ofCLM / toCLM
  theorem isBoundedWith_opNorm (A) : (ofCLM A).IsBoundedWith ‖A‖
  theorem norm_toCLM_le (a) (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖a.toCLM hM‖ ≤ M
  theorem ofCLM_toCLM : ofCLM (a.toCLM hM) = a ; theorem toCLM_ofCLM : (ofCLM A).toCLM _ = A
  ```
* Mathlib: `LinearMap.mkContinuous₂`, `mkContinuous₂_apply`, `mkContinuous₂_norm_le`,
  `ContinuousLinearMap.le_opNorm₂`, `ContinuousLinearMap.coeLM`; extensionality `ContinuousLinearMap.ext`.
* Status: **direct** (the equivalence is bookkeeping; `IsBounded` must carry `M > 0`, which the
  book assumes).

**Dictionary after 8.3.1 (Hilbert `V`; five bullets).** `a` bounded / positive / strictly positive /
strongly positive (`V`-elliptic) / symmetric ⇔ the same for `A` (`⟨A v, v⟩ …`).
* Lean: with `a := ofCLM A` each bullet is `Iff.rfl` except the first: `isBoundedWith_ofCLM_iff :
  (ofCLM A).IsBoundedWith M ↔ ∀ v, ‖A v‖ ≤ M * ‖v‖` (`opNorm_le_bound`/`le_opNorm`),
  `isPositive_ofCLM_iff`, `isStrictlyPositive_ofCLM_iff`, `isEllipticWith_ofCLM_iff`, `isSymm_ofCLM_iff`.
  Through Riesz (`toOperator`) they become the backbone predicates (D4 bullets).
* Backbone: §2.1.4 `LinearMap.IsCoercive`, `IsSymmetricCoercive`; §5.2.1 `SesqForm.IsCoerciveWith`,
  `IsHermitian`, `isCoerciveWith_iff`.
* Status: **needs-equivalence**.

**Thm 8.3.2.** `K ⊂ V` nonempty closed convex, `V` Hilbert, `ℓ ∈ V'`, `E(v) = ½‖v‖² − ℓ(v)`: ∃! `u ∈ K`
with `E(u) = inf_K E`; `u` is characterised by `u ∈ K, (u, v − u) ≥ ℓ(v − u) ∀ v ∈ K`; if `K` is a
subspace, by `u ∈ K, (u, v) = ℓ(v) ∀ v ∈ K`.
* Lean (checked):
  ```lean
  theorem thm_8_3_2 [CompleteSpace V] {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K)
      (ℓ : StrongDual ℝ V) :
      (∃! u, u ∈ K ∧ IsMinOn (fun v => (1/2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u) ∧
      (∀ u ∈ K, IsMinOn (fun v => (1/2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ)
  theorem thm_8_3_2_subspace … (K : Submodule ℝ V) (hK : IsClosed (K : Set V)) (hu : u ∈ K) :
      IsMinOn … K u ↔ ∀ v ∈ K, ⟪u, v⟫_ℝ = ℓ v
  ```
  (`IsMinOn` ⇔ `E u = ⨅ v : K, E v` for `u ∈ K`: helper `isMinOn_iff_eq_ciInf`.)
* Mathlib: with `z := (toDual ℝ V).symm ℓ`, `E v = ½‖v − z‖² − ½‖z‖²` (`toDual_symm_apply`,
  `norm_sub_sq_real`), so minimisers of `E` on `K` are the projections of `z`:
  `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`,
  `norm_eq_iInf_iff_real_inner_eq_zero`; uniqueness from strict convexity / `Submodule.starProjection`.
* Backbone: §5.2.1 `SesqForm.isMinOn_energy_iff` with `a := innerSL ℝ` (G6).
* Status: **needs-equivalence** (or **direct** via the completing-the-square route above).

**Thm 8.3.3.** `K` nonempty closed convex, `a` bilinear symmetric bounded `V`-elliptic, `ℓ ∈ V'`,
`E(v) = ½a(v,v) − ℓ(v)`: ∃! `u ∈ K` with (8.3.2) `E(u) = inf_K E`, which is the unique solution of
(8.3.3) `u ∈ K, a(u, v − u) ≥ ℓ(v − u) ∀ v ∈ K`, and of (8.3.4) `u ∈ K, a(u, v) = ℓ(v) ∀ v ∈ K` when `K`
is a subspace.
* Lean: as 8.3.2 with `energy a ℓ` and `a u (v - u)` / `a u v`; hypotheses `(hM : a.IsBoundedWith M)
  (hα : 0 < α) (ha : a.IsEllipticWith α) (hs : a.IsSymm)`.
* Backbone: §5.2.1 `SesqForm.isMinOn_energy_iff` (closed convex `K`, Hermitian coercive), §2.1.5
  `WithEnergy` (the book's proof: `(·,·)_a` is an inner product with equivalent norm; apply 8.3.2 in
  `WithEnergy`; `K` stays closed/convex under the norm equivalence). Proof-ingredient lemmas
  (un-numbered in the book): `sqrt_alpha_mul_norm_le_energyNorm`, `energyNorm_le_sqrt_M_mul_norm`
  (`c₁ = √α ≤ c₂ = √M`) and "`ℓ` continuous for `‖·‖` iff for `‖·‖_a`" (norm equivalence; trivial).
* Status: **needs-equivalence**.

**Thm 8.3.4 (Lax–Milgram), (8.3.5).** `V` Hilbert, `a` bounded `V`-elliptic bilinear, `ℓ ∈ V'`: unique
solution of (8.3.5) `u ∈ V, a(u, v) = ℓ(v) ∀ v ∈ V`.
* Lean (checked, including the coercivity bridge):
  ```lean
  theorem laxMilgram [CompleteSpace V] (a : BilinForm V) {M α : ℝ} (hM : a.IsBoundedWith M) (hα : 0 < α)
      (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v
  ```
  Bonus (from Ex 8.3.1 / (8.7.5)): `laxMilgram_norm_le : ‖u‖ ≤ ‖ℓ‖ / α`.
* Mathlib: `IsCoercive (a.toCLM hM)` from `ha`; `u := coercive.continuousLinearEquivOfBilin.symm
  ((toDual ℝ V).symm ℓ)` and `continuousLinearEquivOfBilin_apply`, `unique_continuousLinearEquivOfBilin`,
  `toDual_symm_apply`. Backbone alternative: `laxMilgram` (§5.2.2) applied to `a.toCLM hM`
  (accepted as `V →L⋆[ℝ] …` by defeq) with `isEllipticWith_iff_isCoerciveWith`.
* Status: **direct** (Mathlib) / **needs-equivalence** (backbone).

**Proof #1 ingredient (contraction of `P_θ`).** For `θ ∈ (0, 2α/M²)`:
`‖(I − θ𝒥A)w‖² ≤ (1 − 2θα + θ²M²)‖w‖²`, hence `P_θ` is a contraction and Banach's fixed point
theorem gives the solution.
* Lean: `theorem norm_id_sub_smul_toOperator_sq_le (hM) (ha) (θ : ℝ) (w : V) :
  ‖w - θ • toOperator a hM w‖ ^ 2 ≤ (1 - 2 * θ * α + θ ^ 2 * M ^ 2) * ‖w‖ ^ 2`;
  `contractingWith_pTheta (hθ : θ ∈ Set.Ioo 0 (2*α/M^2)) : ContractingWith _ (fun u => u - θ • (toOperator a hM u - rieszRep ℓ))`.
* Backbone: this is the linear case of the proof of AH Thm 5.1.4 (§5.3.1 / §2.1.4
  `ContinuousLinearMap.IsCoercive.exists_inverse`); Mathlib `ContractingWith.fixedPoint`,
  `norm_sub_sq_real`, `real_inner_smul_right`.
* Status: **surface-only** unless the backbone exposes the contraction lemma (G1(v)).

**Proof #2 ingredient.** `L = 𝒥A` has closed range (`‖L w‖ ≥ α‖w‖`) and `R(L)^⊥ = {0}`; conclude by
Thm 8.2.1. Mathlib: `IsCoercive.isClosed_range`, `IsCoercive.range_eq_top` (`B♯ = 𝒥A`).
Status: **direct**.

**Ex 8.3.1.** Deduce Lax–Milgram from Thm 5.1.4 (`T : V → V` strongly monotone and Lipschitz ⇒
`T u = b` uniquely solvable).
* Lean: `theorem ex_8_3_1 … : ∃! u, ∀ v, a u v = ℓ v` proved by applying the surface `Ch05.thm_5_1_4`
  (backbone §5.3.1 / §2.1.4 `exists_inverse`) to `T := toOperator a hM`, `c₁ = α`
  (`inner_toOperator`, `ha`), `c₂ = M` (`‖toOperator a hM‖ ≤ M`), `b := rieszRep ℓ`; then (9.4.7)⟺(9.4.4).
* Status: **needs-equivalence** (imports `Ch05/FixedPoint.lean` within the same library).

### §8.7 Generalized Lax–Milgram Lemma

**Thm 8.7.1 (Nečas), (8.7.1)–(8.7.5).** `U, V` real Hilbert, `a : U × V → ℝ` bilinear, `ℓ ∈ V'`,
`M, α > 0` with (8.7.1) `|a(u,v)| ≤ M‖u‖_U‖v‖_V`; (8.7.2) `sup_{0≠v∈V} a(u,v)/‖v‖_V ≥ α‖u‖_U ∀ u ∈ U`;
(8.7.3) `sup_{u∈U} a(u,v) > 0 ∀ 0 ≠ v ∈ V`. Then (8.7.4) `u ∈ U, a(u,v) = ℓ(v) ∀ v ∈ V` has a unique
solution and (8.7.5) `‖u‖_U ≤ ‖ℓ‖_{V'}/α`.
* Lean (checked; (8.7.3) is formalised as `∃ u, 0 < a u v`, since as a real `iSup` the unbounded
  linear sup would be junk):
  ```lean
  theorem thm_8_7_1 [CompleteSpace U] [CompleteSpace V] (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ℓ : StrongDual ℝ V)
      {M α : ℝ} (hM : 0 < M) (hα : 0 < α)
      (h871 : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖)
      (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖)
      (h873 : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
      (∃! u, ∀ v, a u v = ℓ v) ∧ ∀ u, (∀ v, a u v = ℓ v) → ‖u‖ ≤ ‖ℓ‖ / α
  ```
* Backbone: `babuska_necas` (§5.2.2, phase 2; already two-space `a : U →L⋆[𝕜] V →L[𝕜] 𝕜`); the
  estimate (8.7.5) is not in the plan — add `babuska_necas_norm_le` (G3).
* Proof route (book): `A : U →L V`, `A u := (toDual ℝ V).symm (a.toCLM₂ u)`; (8.7.2) ⇒ `α‖u‖ ≤ ‖A u‖`
  (D9 lemmas) ⇒ injective and, with `CompleteSpace U`, `AntilipschitzWith.isClosed_range`; (8.7.3)
  ⇒ `(range A)ᗮ = ⊥`; `Submodule.topologicalClosure_eq_top_iff` (`CompleteSpace V`) ⇒ `range A = ⊤`;
  solve `A u = (toDual ℝ V).symm ℓ`; (8.7.5): `α‖u‖ ≤ ‖A u‖ = ‖ℓ‖` (`LinearIsometryEquiv.norm_map`).
* Status: **needs-equivalence** (through D9), backbone item **phase 2**.

**(8.7.2) ↔ operator form.** `discreteInfSup_iff_norm_le`-type lemma on `U`/`V`:
`(∀ u, α‖u‖ ≤ ⨆ v ≠ 0, a u v / ‖v‖) ↔ ∀ u, α‖u‖ ≤ ‖a.toCLM₂ hM u‖` (uses sign symmetry and
`ContinuousLinearMap.sSup_unit_ball_eq_norm` or `opNorm_le_bound`/`le_opNorm`). Status:
**needs-equivalence** (the one genuinely fiddly `Real.iSup` lemma in this plan).

**Ex 8.7.1.** Thm 8.7.1 generalises Lax–Milgram: with `U = V` and `a` `V`-elliptic (constant `α`),
(8.7.2) holds with the same `α` (take `v = u`) and (8.7.3) holds (take `u = v`).
* Lean: `theorem IsEllipticWith.infSup (ha : a.IsEllipticWith α) (hα : 0 < α) (hM) : ∀ u, α * ‖u‖ ≤ ⨆ v : {v // v ≠ 0}, a u v / ‖v‖`
  (needs `le_ciSup` with the bound from (8.7.1)); `theorem IsEllipticWith.exists_pos (ha) (hα) : ∀ v ≠ 0, ∃ u, 0 < a u v`;
  `theorem ex_8_7_1 : … := thm_8_7_1 …`.
* Status: **needs-equivalence** (trivial).

### §9.1 The Galerkin method

**(9.1.1) well-posedness.** Under (9.1.2) (`M`) and (9.1.3) (`c₀`), (9.1.1) has a unique solution — this
is `laxMilgram`. Status: **direct**.

**(9.1.4) well-posedness on `V_N`.** `V_N ⊂ V` finite-dimensional ⇒ unique Galerkin solution.
* Lean: `theorem existsUnique_galerkinProblem [CompleteSpace V] … (VN : Submodule ℝ V) [FiniteDimensional ℝ VN] :
  ∃! uN, GalerkinProblem a ℓ VN uN`.
* Backbone: `existsUnique_isGalerkinSolution [CompleteSpace K]` (§5.2.3) + `FiniteDimensional.complete`
  (Mathlib) via D7. (Alternative: Mathlib Lax–Milgram on the subtype with `LinearMap.domRestrict₁₂`.)
* Status: **needs-equivalence**.

**(9.1.5) linear system.** For a basis `{φ_i}` of `V_N`, (9.1.4) ⇔ `A ξ = b` with the stiffness matrix
`A = (a(φ_j, φ_i))` and load vector `b = (ℓ(φ_i))`, `u_N = Σ ξ_j φ_j`.
* Lean: `theorem galerkinProblem_iff_mulVec (φ : Basis (Fin N) ℝ VN) (ξ : Fin N → ℝ) :
  GalerkinProblem a ℓ VN (∑ j, ξ j • (φ j : V)) ↔ (stiffnessMatrix a (fun i => (φ i : V))).mulVec ξ = loadVector ℓ (fun i => (φ i : V))`.
* Backbone: none at form level; §2.4.1 `isPetrovGalerkin_iff_toMatrix` is the operator analogue
  (Saad (5.7)). Proof: reduce `∀ v ∈ VN` to basis vectors (`Basis.mem_span`/`Submodule.span_le`,
  `Finset.sum` linearity), `Matrix.mulVec`, `Matrix.of_apply`.
* Status: **GAP** (small; request a form-level version in §5.2.3, G7).

**Ex 9.1.2.** `a` symmetric ⇒ `A` symmetric; `a` `V`-elliptic ⇒ `A` positive definite.
* Lean: `theorem stiffnessMatrix_isSymm (hs : a.IsSymm) : (stiffnessMatrix a φ).IsSymm`;
  `theorem stiffnessMatrix_pos_of_isElliptic (hφ : LinearIndependent ℝ φ) (ha) (hα) :
  ∀ ξ ≠ 0, 0 < ξ ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ`; corollary with both hypotheses:
  `(stiffnessMatrix a φ).PosDef` (Mathlib `Matrix.PosDef` requires `IsHermitian`, so the book's
  "positive definite" without symmetry is the `⬝ᵥ` statement).
* Backbone: §2.1.4 `Matrix.posDef_iff_isSymmetricCoercive`, `LinearMap.isCoercive_iff_pos`.
* Status: **needs-equivalence**.

**(9.1.6)–(9.1.8), Ex 9.1.1 (Ritz).** `a` symmetric: (9.1.1) ⇔ `E(u) = inf_V E`; (9.1.4) ⇔
`E(u_N) = inf_{V_N} E`; the two discrete problems are equivalent.
* Lean: `theorem galerkinProblem_iff_isMinOn (hs : a.IsSymm) (hM) (hα) (ha) (VN) [FiniteDimensional ℝ VN] (uN) :
  GalerkinProblem a ℓ VN uN ↔ uN ∈ VN ∧ IsMinOn (energy a ℓ) VN uN`; `VN = ⊤` gives (9.1.6).
* Backbone: Thm 8.3.3 subspace case (§5.2.1 `isMinOn_energy_iff`) with `Submodule.closed_of_finiteDimensional`.
* Status: **needs-equivalence**.

**Prop 9.1.3 (Céa), (9.1.11)–(9.1.12).** `V_N ⊂ V` a subspace, `a` bounded (`M`) `V`-elliptic (`c₀`),
`u` the solution of (9.1.1), `u_N` of (9.1.4): (9.1.12) `a(u − u_N, v) = 0 ∀ v ∈ V_N`, and
(9.1.11) `‖u − u_N‖ ≤ c inf_{v∈V_N} ‖u − v‖` with `c = M/c₀`.
* Lean (checked):
  ```lean
  theorem galerkin_orthogonality (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) :
      ∀ v ∈ VN, a (u - uN) v = 0                                                       -- (9.1.12)
  theorem prop_9_1_3 [CompleteSpace V] (a) {M c₀} (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
      (ha : a.IsEllipticWith c₀) (ℓ) (VN : Submodule ℝ V) {u uN} (hu : ∀ v, a u v = ℓ v)
      (huN : GalerkinProblem a ℓ VN uN) : ‖u - uN‖ ≤ M / c₀ * ⨅ v : VN, ‖u - v‖              -- (9.1.11)
  ```
  (`VN` need not be finite-dimensional; `CompleteSpace V` is only needed if one insists that `u`
  exists — it can be dropped from the inequality.)
* Backbone: `cea` (§5.2.3, `‖a‖ / c * ⨅ v : K, ‖u - v‖`) + `norm_toCLM_le` (`‖a.toCLM hM‖ ≤ M`) and
  `⨅ ≥ 0` (`Real.iInf_nonneg`), `div_le_div_of_nonneg_right`.
* Status: **needs-equivalence**.

**Céa, symmetric case (un-numbered).** `‖u − u_N‖_a = inf_{v∈V_N} ‖u − v‖_a`; `u_N` is the
`a`-orthogonal projection of `u` onto `V_N` (and `‖u − u_N‖ ≤ √(M/c₀) inf ‖u − v‖`).
* Lean: `theorem energyNorm_sub_eq_iInf (hs : a.IsSymm) … [FiniteDimensional ℝ VN] :
  energyNorm a (u - uN) = ⨅ v : VN, energyNorm a (u - v)`;
  `theorem galerkin_eq_energyProjection : uN = WithEnergy.equiv.symm ((VN.map WithEnergy.equiv).starProjection (WithEnergy.equiv u))`.
* Backbone: `cea_hermitian` (§5.2.3), `IsGalerkin.error_eq` (§2.4.2), `WithEnergy` +
  `Submodule.starProjection_minimal` (§2.1.5), `energyNorm_eq` (D6).
* Status: **needs-equivalence**.

**Cor 9.1.4, (9.1.13)–(9.1.14).** `V_1 ⊂ V_2 ⊂ ⋯` finite-dimensional with `closure(⋃ V_n) = V` ⇒
`‖u − u_n‖ → 0`.
* Lean (checked):
  ```lean
  theorem cor_9_1_4 [CompleteSpace V] (a) {M c₀} (hM) (hc₀) (ha) (ℓ) (VN : ℕ → Submodule ℝ V)
      [∀ n, FiniteDimensional ℝ (VN n)] (hmono : Monotone VN) (hdense : Dense (⋃ n, (VN n : Set V)))
      {u} (hu : ∀ v, a u v = ℓ v) (uN : ℕ → V) (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
      Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0)
  ```
  (`closure (⋃ V_n) = V` is `Dense`; `Monotone VN` is needed for "pick `v_n ∈ V_n` with `v_n → u`".)
* Backbone: `tendsto_galerkin_of_dense_iUnion` (§5.2.3); shared density lemma requested in G7.
* Status: **needs-equivalence**.

### §9.2 The Petrov–Galerkin method

**(9.2.1) well-posedness under (9.2.2)–(9.2.4).** = `thm_8_7_1`. Status: **needs-equivalence**.

**Thm 9.2.1 (Babuška), (9.2.6)–(9.2.9).** `U_N ⊂ U`, `V_N ⊂ V`, `dim U_N = dim V_N = N`, discrete inf–sup
(9.2.6) with `α_N > 0` ⇒ (9.2.5) has a unique solution, (9.2.8) `a(u − u_N, v_N) = 0 ∀ v_N ∈ V_N`,
(9.2.9) triangle inequality, and (9.2.7) `‖u − u_N‖_U ≤ (1 + M/α_N) inf_{w_N∈U_N} ‖u − w_N‖_U`.
* Lean (checked):
  ```lean
  theorem thm_9_2_1 (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ℓ) {M αN : ℝ} (h922 : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖)
      (UN : Submodule ℝ U) (VN : Submodule ℝ V) [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN]
      (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
      (hinfsup : DiscreteInfSup a UN VN αN) {u : U} (hu : ∀ v, a u v = ℓ v) :
      (∃! uN, PetrovGalerkinProblem a ℓ UN VN uN) ∧
      ∀ uN, PetrovGalerkinProblem a ℓ UN VN uN → ‖u - uN‖ ≤ (1 + M / αN) * ⨅ wN : UN, ‖u - wN‖
  ```
  plus `petrovGalerkin_orthogonality` (9.2.8). Note: completeness of `U, V` and (9.2.3)–(9.2.4) are
  *not* used (only through the existence of `u`); the faithful surface statement may keep them as
  unused hypotheses or, better, omit them with a docstring.
* Backbone: Babuška in §5.2.3 (phase 2) — must be two-space and must contain the finite-dimensional
  solvability step: `T : UN →ₗ[ℝ] Module.Dual ℝ VN`, `T u := (a u ·)|VN`, injective by (9.2.6),
  `Subspace.dual_finrank_eq` + `hdim` + `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`
  ⇒ surjective; error bound as in the book (3 lines, D9 lemma for `α_N‖u_N − w_N‖ ≤ sup …`).
* Status: **GAP** (backbone phase 2 + two-space shape, G3).

**Rem 9.2.2, (9.2.10) and Kato's lemma.** `‖u − u_N‖_U ≤ (M/α_N) inf_{w_N∈U_N} ‖u − w_N‖_U`
(Xu–Zikatanov); ingredient: `H` Hilbert, `0 ≠ P = P² ≠ I` bounded ⇒ `‖P‖ = ‖I − P‖`, applied to
`P_N u := u_N`.
* Lean (checked): `theorem kato {H} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : H →L[ℝ] H) (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : ‖P‖ = ‖1 - P‖`;
  `theorem rem_9_2_2 … : ‖u - uN‖ ≤ M / αN * ⨅ wN : UN, ‖u - wN‖` (needs `u ↦ u_N` to be a bounded
  idempotent `P_N : U →L[ℝ] U` — build it from `thm_9_2_1`'s `∃!` with `Classical.choose`, linear by
  uniqueness, bounded by `‖P_N u‖ ≤ (M/α_N)‖u‖`).
* Backbone: §2.1.7 Kato (phase 2; proof reference: D. Szyld, "The many proofs of an identity on the
  norm of oblique projections", Numer. Algorithms 42 (2006)), §5.2.3 sharpening (phase 2).
* Status: **GAP** (phase 2).

**Cor 9.2.3, (9.2.11)–(9.2.12).** `α_N ≥ α_0 > 0` uniformly, `U_{N_1} ⊂ U_{N_2} ⊂ ⋯` with dense union
⇒ `‖u − u_{N_i}‖_U → 0`.
* Lean: as `cor_9_1_4` with `UN VN : ℕ → Submodule`, `hdim : ∀ i, finrank (UN i) = finrank (VN i)`,
  `hinfsup : ∀ i, DiscreteInfSup a (UN i) (VN i) (αN i)`, `hα : ∀ i, α₀ ≤ αN i`, `Monotone UN`,
  `Dense (⋃ i, (UN i : Set U))`; conclusion `Tendsto (fun i => ‖u - uN i‖) atTop (𝓝 0)`.
* Backbone: `thm_9_2_1` + the shared density lemma (G7).
* Status: **needs-equivalence** (once Thm 9.2.1 exists).

**Remark after Cor 9.2.3.** Convergence already if `max{1, α_N⁻¹} inf_{w_N} ‖u − w_N‖ → 0`.
Lean: from (9.2.7), `1 + M/αN ≤ (1 + M) * max 1 αN⁻¹`. Status: **surface-only**.

**(9.2.13) ⇔ (9.2.14) (inf–sup / Babuška–Brezzi condition).** `InfSupCondition a UN VN α₀ ↔
∀ N, α₀ ≤ infSupValue a (UN N) (VN N)` (with `UN N ≠ ⊥`, `VN N ≠ ⊥` to avoid `Real.iInf`/`iSup` junk;
lower bound `0` for the `ciInf` from sign symmetry).
* Status: **surface-only** (low priority; only the definitional link, no theorem depends on (9.2.14)).

### §9.3 Generalized Galerkin method

**Thm 9.3.1 (first Strang lemma), (9.3.1)–(9.3.2).** `‖·‖_N`, `a_N`, `ℓ_N` on `V + V_N`; constants
`M, α₀, c₀ > 0` with `|a_N(w, v_N)| ≤ M‖w‖_N‖v_N‖_N`, `a_N(v_N, v_N) ≥ α₀‖v_N‖_N²`,
`|ℓ_N(v_N)| ≤ c₀‖v_N‖_N` ⇒ (9.3.1) has a unique solution and
`‖u − u_N‖_N ≤ (1 + M/α₀) inf_{w_N∈V_N} ‖u − w_N‖_N + (1/α₀) sup_{v_N∈V_N} |a_N(u,v_N) − ℓ_N(v_N)|/‖v_N‖_N`.
* Lean (checked; abstract `W`, D10):
  ```lean
  theorem thm_9_3_1 {W} [NormedAddCommGroup W] [NormedSpace ℝ W] (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
      (VN : Submodule ℝ W) [FiniteDimensional ℝ VN] {M α₀ c₀ : ℝ} (hα₀ : 0 < α₀)
      (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖) (hcoer : ∀ v ∈ VN, α₀ * ‖v‖ ^ 2 ≤ aN v v)
      (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W) :
      (∃! uN, uN ∈ VN ∧ ∀ v ∈ VN, aN uN v = ℓN v) ∧
      ∀ uN, uN ∈ VN → (∀ v ∈ VN, aN uN v = ℓN v) →
        ‖u - uN‖ ≤ (1 + M / α₀) * (⨅ w : VN, ‖u - w‖) +
          1 / α₀ * ⨆ v : {v : VN // v ≠ 0}, |aN u v - ℓN v| / ‖(v : W)‖
  ```
  Surface wrapper `thm_9_3_1'` adds the book's data: `V` Hilbert, `a, ℓ` on `V`, `ι : V →ₗ[ℝ] W`
  injective, `u : V` solving (9.1.1), conclusion for `ι u` — a one-line instance of the above.
* Backbone: §5.2.3 "First Strang lemma" (phase 2); G4 recommends the abstract form. Proof: unique
  solvability by injectivity (`a_N(v,v) ≥ α₀‖v‖² > 0` for `v ≠ 0`) + finite dimension
  (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` on `VN →ₗ Module.Dual ℝ VN`); the
  estimate is the book's four-line computation (`le_ciSup` with bound `M‖u‖ + c₀`).
* Status: **GAP** (phase 2; statement ready).

**Ex 9.3.1.** Conforming case (`V_N ⊂ V`, `a_N = a`, `ℓ_N = ℓ`): the consistency term vanishes and
(9.3.2) becomes `‖u − u_N‖ ≤ (1 + M/α₀) inf ‖u − v‖` (an inequality of the form (9.1.11)).
* Lean: `theorem ex_9_3_1 (W := V) … (hu : ∀ v, a u v = ℓ v) : ‖u - uN‖ ≤ (1 + M / c₀) * ⨅ v : VN, ‖u - v‖`
  (sup term `= 0` by `hu`; `Real.iSup` of the zero function).
* Status: **needs-equivalence** (trivial).

### §9.4 Conjugate gradient method: variational formulation

**(9.4.1)–(9.4.3) ⇒ properties of `A`, `f` from (9.4.5)–(9.4.6).** `A` exists (Riesz), `‖A‖ ≤ M`,
`(A u, v) = (u, A v)` (self-adjoint), `(A v, v) ≥ α‖v‖²`; `‖f‖ = ‖ℓ‖`.
* Lean: `norm_toOperator_le : ‖toOperator a hM‖ ≤ M`; `isSelfAdjoint_toOperator (hs : a.IsSymm) :
  IsSelfAdjoint (toOperator a hM)`; `isCoercive_toOperator (ha) : (toOperator a hM : V →ₗ[ℝ] V).IsCoercive`;
  `norm_rieszRep : ‖rieszRep ℓ‖ = ‖ℓ‖`.
* Mathlib/backbone: `continuousLinearMapOfBilin_apply`, `LinearIsometryEquiv.norm_map`,
  `ContinuousLinearMap.opNorm_le_bound`, `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`;
  backbone §5.2.1 `inner_toOperator`, `norm_toOperator`, `isCoerciveWith_iff`; §2.1.4.
* Status: **direct** / **needs-equivalence**.

**(9.4.7) ⇔ (9.4.4).** `A u = f ↔ ∀ v, a(u,v) = ℓ(v)`.
* Lean: `theorem toOperator_eq_rieszRep_iff : toOperator a hM u = rieszRep ℓ ↔ ∀ v, a u v = ℓ v`
  (`ext_inner_right ℝ`, `inner_toOperator`, `toDual_symm_apply`). Backbone bridge
  `isGalerkinSolution_iff_isGalerkin` with `K = ⊤`.
* Status: **direct**.

**Algorithm 1 = backbone CG.** See D11: `cgIterate_eq`.
* Consequences transported from §3.7/§2.4.2: `CG.isGalerkinIterate` (`u_k` is the Galerkin solution on
  `u_0 + 𝒦_k(A, r_0)`), residual orthogonality, `A`-conjugacy of `s_k`, energy-error monotonicity, and
  `isGalerkin_iff_isMinOn_quadratic` (`u_k` minimises `E` over `u_0 + 𝒦_k`).
* Status: **needs-equivalence**.

**"Convergence of Algorithm 1 follows from Theorem 5.6.1."** With `m = α`, `M = M` in (5.6.3)
(`√α‖v‖ ≤ ‖v‖_a ≤ √M‖v‖`): `u_k → u` and (5.6.4) `‖u − u_{k+1}‖_a ≤ (M − α)/(M + α) ‖u − u_k‖_a`,
(5.6.5) `‖u − u_k‖_a ≤ 2((√M − √α)/(√M + √α))^k ‖u − u_0‖_a`.
* Lean: `theorem cg_converges … : Tendsto (fun k => (cgIterate a hM ℓ u₀ k).x) atTop (𝓝 u)`,
  `theorem cg_energy_rate … : energyNorm a (u - (cgIterate a hM ℓ u₀ (k+1)).x) ≤ (M - α) / (M + α) * energyNorm a (u - (cgIterate a hM ℓ u₀ k).x)`,
  `theorem cg_energy_bound … : energyNorm a (u - (cgIterate a hM ℓ u₀ k).x) ≤ 2 * ((√M - √α)/(√M + √α)) ^ k * energyNorm a (u - u₀)`.
* Backbone: `Ch05/ConjugateGradient.lean` (Thm 5.6.1) built on §3.10 with the compression trick
  (§5.2.3 note) for (5.6.5); for the one-step bound (5.6.4) the same trick works on the
  2-dimensional space `S = span{e_k, A e_k}` (`e_k := u − u_k`): CG optimality gives
  `‖e_{k+1}‖_a ≤ ‖(I − tA)e_k‖_a` for every `t` (`u_k + t r_k ∈ u_0 + 𝒦_{k+1}`), and
  `(I − tA)e_k = (I − tA_S)e_k` with `A_S` the compression (§2.1.6) whose spectrum lies in `[α, M]`
  (Rayleigh bounds, §4.2), so the L3 bound `‖I − tA_S‖_{A_S} ≤ (M − α)/(M + α)` at `t = 2/(M + α)` applies.
* Status: **GAP** (phase 2 backbone; surface statements ready to transport via `cgIterate_eq`).

**Energy functional and its Gâteaux derivative (§9.4).** `⟨E'(u), v⟩ = a(u,v) − ℓ(v)`; hence
`(r_k, v) = −⟨E'(u_k), v⟩`, and (9.4.4) ⇔ `E(u) = inf_V E`.
* Lean (checked statement): `theorem hasFDerivAt_energy (hM) (hs : a.IsSymm) (ℓ) (u) :
  HasFDerivAt (fun v => (1/2 : ℝ) * a v v - ℓ v) (a.toCLM hM u - ℓ) u` (Fréchet ⇒ Gâteaux);
  `theorem residual_eq_neg_rieszRep_fderiv : residual a hM ℓ u = -(toDual ℝ V).symm (a.toCLM hM u - ℓ)`;
  `energy_isMinOn_iff` = (9.1.6) case of Thm 8.3.3.
* Mathlib: `IsBoundedBilinearMap.hasFDerivAt` (`Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean`)
  composed with `hasFDerivAt_id.prodMk hasFDerivAt_id`, symmetry to merge the two terms,
  `ContinuousLinearMap.hasFDerivAt`.
* Status: **surface-only** (derivative) / **needs-equivalence** (minimisation).

**Algorithm 2 (nonlinear CG) and its convergence (`J` coercive `C¹`, `J'` Lipschitz and strongly
monotone on bounded sets, [92]).** Status: **out-of-scope** (quoted without proof; see §5).

## Gaps and requests to the backbone

1. **`RCLike` backbone vs. real surface — verdict: workable, small friction.** Checked: over `ℝ`, a
   `B : V →L[ℝ] V →L[ℝ] ℝ` is accepted where `V →L⋆[ℝ] V →L[ℝ] ℝ` is expected (`example (B : V →L[ℝ] V →L[ℝ] ℝ) :
   V →L⋆[ℝ] V →L[ℝ] ℝ := B` elaborates; Mathlib's own `LaxMilgram.lean` relies on the same defeq with
   `continuousLinearMapOfBilin (𝕜 := ℝ)`). So no `ofReal` conversion is needed. Remaining friction and
   fixes: (i) `RCLike.re`/`conj` in backbone statements — provide `@[simp]` real specialisations
   `SesqForm.isCoerciveWith_real_iff : a.IsCoerciveWith c ↔ ∀ v, c * ‖v‖ ^ 2 ≤ a v v` (for `𝕜 = ℝ`),
   `SesqForm.isHermitian_real_iff : a.IsHermitian ↔ ∀ u v, a u v = a v u`, and state the energy as
   `½ re (a v v) − re (ℓ v)` so that `simp [RCLike.re_to_real]` closes the real case; (ii) the book's
   forms are unbundled (`LinearMap.BilinForm ℝ V` + `IsBoundedWith M`), bundled on the surface by
   `LinearMap.mkContinuous₂` (`toCLM`, D4) — fine, no backbone change; (iii) every backbone bound
   stated with `‖a‖` (e.g. `cea : ‖a‖ / c * ⨅ …`) is transferred through `mkContinuous₂_norm_le`
   and monotonicity in `M`; it would be more convenient (and no less general) to state such bounds
   with an explicit `M` and hypothesis `hM : ∀ u v, ‖a u v‖ ≤ M * ‖u‖ * ‖v‖` (or `‖a‖ ≤ M`), mirroring
   how `IsCoerciveWith c` already carries `c`; (iv) Mathlib's `IsCoercive` uses `C * ‖u‖ * ‖u‖`,
   backbone `c * ‖v‖ ^ 2` — one `sq`/`mul_assoc` lemma `isCoerciveWith_iff_isCoercive` in the backbone;
   (v) expose the contraction estimate `‖w − θ A w‖² ≤ (1 − 2θc + θ²‖A‖²)‖w‖²` used in the proof of
   `ContinuousLinearMap.IsCoercive.exists_inverse` (§2.1.4) as a named lemma (AH proof #1 of 8.3.4,
   AH 5.1.4, Richardson iteration §2.3).
2. **Closed-operator version of Thm 8.2.4.** §5.2.2's `bijective_of_antilipschitz_of_orthogonal_range_eq_bot`
   is for bounded `L`; the book's theorem is for `L : V →ₗ.[ℝ] W` with `L.IsClosed`. Add
   `LinearPMap.isClosed_range_of_isClosed_of_le_norm [CompleteSpace V] (hL : L.IsClosed) (hc : 0 < c)
   (h : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖) : IsClosed (LinearMap.range L.toFun : Set W)` (proof via the
   closed graph and `AntilipschitzWith.isClosed_range` for `Prod.snd` on the graph, as in §3), derive
   the bijectivity statement, and keep the bounded version as a corollary (`LinearMap.toPMap`).
   Also add the sequential characterisation `LinearPMap.isClosed_iff_seq` (D1) to `ForMathlib`.
3. **Two-space Petrov–Galerkin and inf–sup shape.** `IsPetrovGalerkinSolution` (§5.2.3) must take
   `a : U →L⋆[𝕜] V →L[𝕜] 𝕜`, `K ≤ U`, `L ≤ V`; Babuška (Thm 9.2.1) needs `Module.finrank 𝕜 K = Module.finrank 𝕜 L`
   and the injective-⇒-surjective step (`Subspace.dual_finrank_eq`,
   `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`); its error bound uses only boundedness
   and the discrete inf–sup (no completeness, no continuous inf–sup). For `babuska_necas` and the
   discrete inf–sup, state the hypothesis as `∀ u, α * ‖u‖ ≤ ‖a u‖` (operator norm of the functional
   `a u : V →L[𝕜] 𝕜`) rather than an `iSup`; the surface converts the book's `sup a(u,v)/‖v‖` with
   one lemma (D9). Add the estimate `‖u‖ ≤ ‖ℓ‖ / α` (8.7.5) as `babuska_necas_norm_le`.
4. **§9.3 `V + V_N`: the plan's proposal fits, and can be simplified.** Thm 9.3.1 is a statement about
   a single finite-dimensional subspace `V_N` of a normed space `W` carrying `‖·‖_N`, an element `u ∈ W`,
   a bilinear `a_N` bounded on `W × V_N` and coercive on `V_N`, and a functional `ℓ_N` bounded on `V_N`.
   Neither the Hilbert space `V`, nor `a`, `ℓ`, nor the fact that `u` solves (9.1.1) enters the proof,
   and unique solvability needs only finite dimension (not Lax–Milgram). Recommend the backbone state
   `strang_first` on `[NormedAddCommGroup W] [NormedSpace 𝕜 W]` with unbundled `aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜`
   (it need not be bounded on all of `W × W`) — no type-synonym family, one `W` per `N`; the surface
   wrapper supplies `V`, `ι : V →ₗ[ℝ] W`, and `u`. Uniformity of `M, α₀, c₀` in `N` is only a
   convention of the book and does not affect the statement.
5. **§9.4 CG from §3.7 via `SesqForm.toOperator` — yes.** `SesqForm.toOperator` coincides with Mathlib's
   `InnerProductSpace.continuousLinearMapOfBilin` (`continuousLinearMapOfBilin_apply` is `inner_toOperator`);
   make it an `abbrev` (or drop it). Requests: (a) fix the residual convention in `CG.step`
   (`r' := r − α • A p`, Hestenes–Stiefel) and keep `CG.residual_eq`, so that the surface equivalence
   `cgIterate_eq` (D11) is a plain induction; (b) let the surface reuse `CG.State`; (c) the
   Hilbert-space rates (5.6.4)/(5.6.5) are phase 2 (§3.10 + compression trick); note that (5.6.4)
   needs the trick only on the 2-dimensional space `span{e_k, A e_k}` (§3, last block), which avoids
   any functional calculus; (d) a lemma that `CG.iterate` is stationary once `r_k = 0` (Lean's `x / 0 = 0`).
6. **`SesqForm.isMinOn_energy_iff` (§5.2.1) scope.** It should cover: existence and uniqueness of the
   minimiser on a nonempty closed convex `K` (`∃!`), the variational inequality (8.3.3), the subspace
   case (8.3.4), and the pure inner-product case (Thm 8.3.2, `a = innerSL`), plus the explicit norm
   equivalence `√c ‖v‖ ≤ ‖v‖_a ≤ √‖A‖ ‖v‖` in §2.1.5. The cleanest route is Mathlib's convex projection
   (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`) in `WithEnergy`
   (real part of the energy inner product for `𝕜 ≠ ℝ`, `InnerProductSpace.rclikeToReal`).
7. **Small shared lemmas** (used by two or more surface items and by Kress): (a)
   `tendsto_dist_of_monotone_dense (hmono : Monotone K) (hdense : Dense (⋃ n, (K n : Set V))) (u) :
   Tendsto (fun n => ⨅ v : K n, ‖u - v‖) atTop (𝓝 0)` and the quasi-optimality corollary (Cor 9.1.4,
   Cor 9.2.3); (b) form-level stiffness-matrix equivalence `IsGalerkinSolution a ℓ K (∑ ξ j • φ j) ↔
   (Matrix.of fun i j => a (φ j) (φ i)).mulVec ξ = fun i => ℓ (φ i)` for a basis `φ` of `K` ((9.1.5),
   Kress §11); (c) `isMinOn_iff_eq_ciInf` (`IsMinOn f K u ↔ f u = ⨅ v : K, f v` for `u ∈ K`, `f`
   bounded below on `K`); (d) note that Mathlib's `Matrix.PosDef`/`LinearMap.IsPositive` include
   symmetry while AH's "positive"/"positive definite" do not — provide the non-symmetric forms.
8. **Kato's lemma and Xu–Zikatanov (§2.1.7, §5.2.3, phase 2).** Rem 9.2.2 depends on both; statement
   `IsIdempotentElem P → P ≠ 0 → P ≠ 1 → ‖P‖ = ‖1 - P‖` on a Hilbert space over `RCLike 𝕜` (Szyld 2006
   for proofs; the shortest uses `‖P x‖ = ‖P (x − y)‖` for `y ∈ ker P` and the adjoint).
9. **Closed range theorem (Thm 8.2.7).** Out of scope; would need Banach adjoints of densely defined
   closed operators (absent from Mathlib). Do not plan it; the Hilbert bounded case is Mathlib
   (`ContinuousLinearMap.orthogonal_range`).
10. **Real-only aspects of the book** that the `RCLike` backbone must specialise cleanly: sups of
    `a(u,v)/‖v‖` without absolute value (sign symmetry lemma on the surface), `V`-ellipticity without
    `re`, symmetric (not Hermitian) forms. Nothing in §8.2–8.3, 8.7, Ch. 9 requires complex scalars.

## Left out

* §8.1 model problem (8.1.1)–(8.1.4), Ex 8.2.3, Ex 8.2.6, Ex 8.3.5, Ex 8.7.2, Examples 9.1.1–9.1.2,
  Table 9.1, Ex 9.1.3: need `H¹₀(Ω)`, `H⁻¹(Ω)`, `L²`, weak derivatives, Green's kernels — no Sobolev
  spaces in Mathlib.
* §8.4 (weak formulations with Dirichlet/Neumann/mixed/Robin conditions, general second-order elliptic
  operators, Lemma 8.4.1 quotient Poincaré inequality): Sobolev spaces, traces, Poincaré/Friedrichs.
* §8.5 (linearized elasticity, Thm 8.5.1): Korn's inequality and tensor-valued Sobolev spaces.
* §8.6 (mixed and dual formulations, Def 8.6.1, Prop 8.6.2, Thm 8.6.3 Ekeland–Temam saddle points,
  Brezzi framework (8.6.21)–(8.6.22)): convex analysis in reflexive Banach spaces, `H(div)`.
* §8.8 (Lemmas 8.8.1–8.8.4, Thm 8.8.5, `p`-Laplacian-type problem): `W^{1,p}₀`, reflexivity, Gâteaux
  derivatives of integral functionals, Thm 3.3.12/5.3.19.
* Thm 8.2.7 in its Banach generality (closed range theorem) — no Banach dual of unbounded operators.
* Ex 8.2.1 (finite-dimensional exercise), Ex 9.1.4 (Galerkin as an existence proof via weak
  compactness — needs weak sequential compactness of bounded sets, not cited by any theorem).
* Algorithm 2 (nonlinear CG for strictly convex `J`) and its convergence claim from [92]: no proof in
  the book; the line search `α_k` is an argmin that need not exist in general.
* Thm 5.6.1/5.6.2 themselves belong to `Ch05/ConjugateGradient.lean` (Winther's superlinear rate is
  phase 2); §9.4 only transports them.

## OCR uncertainties

* Line 15691 (Thm 8.2.1): "`L : D(L) ⊂ V → Wa` linear operator" — OCR merged "W" and "a"; the
  statement is unaffected.
* Thm 8.2.4 proof: "`‖v_n − v_m‖ ≤ c ‖f_n − f_m‖`" should read `c⁻¹` (book typo, not OCR).
* Thm 8.3.1 dictionary bullet 1: "`a(u,v) ≤ M‖u‖‖v‖`" without absolute value — book shorthand;
  formalised with `|·|`.
* (8.7.3), (9.2.4): "`sup_{u∈U} a(u,v) > 0`" — as printed; the sup of a nonzero linear functional is
  `+∞`, so it is formalised as `∃ u, 0 < a u v` (equivalently `∃ u, a u v ≠ 0`).
* Thm 9.2.1 proof (line ≈17893): "for any `w_N ∈ V_N`" should be `w_N ∈ U_N` (book typo).
* (9.3.2): the sup is over `v_N ∈ V_N` without `v_N ≠ 0` (book); formalised over `v_N ≠ 0`.
* §9.1 (line ≈17720): "the simpll choice" — OCR typo, irrelevant.
* Cor 9.1.4 indexes subspaces `V_n`, §9.1 text `V_{N_i}`, Cor 9.2.3 `U_{N_i}`; all formalised as
  `ℕ`-indexed monotone families.
* Thm 8.2.1's proof cites Thm 3.3.7 (Hahn–Banach separation); the Lean proof uses orthogonal
  projections instead — the statement is identical.
* Scratch check: `Scratch.lean` in this directory elaborates all displayed statements marked
  "checked" (with `sorry` proofs); nothing in the book text itself was ambiguous enough to change a
  statement.
