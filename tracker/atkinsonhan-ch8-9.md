<!--
The per-result Lean statements quoted below are historical wherever the result exists: the tracker
plan (the TOML group files beside this document) is the authority on which declarations exist, and
the source is the authority on what they say. Where the two disagree, this document is wrong.

What is worth reading here is the book alignment: which numbered result maps to which declaration,
how each book-specific definition relates to the backbone, what was deferred and why, and what was
deliberately left out.
-->

# Surface plan: Atkinson–Han — §8.2, 8.3, 8.7, Chapter 9

Scope: Atkinson & Han, *Theoretical Numerical Analysis* (3rd ed.), §8.2 (existence/uniqueness for
operator equations), §8.3 (Lax–Milgram), §8.7 (generalized Lax–Milgram), Chapter 9 (Galerkin,
Petrov–Galerkin, generalized Galerkin/Strang, variational CG). §8.1, §8.4–8.6 and §8.8 need
Sobolev spaces and appear only in §6. The book works throughout with **real** Hilbert spaces, real
bilinear forms `a : V × V → ℝ`, `ℓ ∈ V'`, finite-dimensional `V_N`, and the sup in the inf–sup
conditions is taken *without* absolute values (a sign-symmetry lemma is needed once).

## 1. Representation, files and conventions

The surface represents the book's "bilinear form" as `LinearMap.BilinForm ℝ V`
(= `V →ₗ[ℝ] V →ₗ[ℝ] ℝ`) with unbundled predicates (`IsBoundedWith M`, `IsEllipticWith α`,
`LinearMap.IsSymm`); the bundled `V →L[ℝ] V →L[ℝ] ℝ` is obtained by `LinearMap.mkContinuous₂`.
Over `ℝ` a bounded bilinear `V →L[ℝ] V →L[ℝ] ℝ` is accepted *definitionally* where the backbone's
`SesqForm ℝ V` (= `V →L⋆[ℝ] V →L[ℝ] ℝ`, `Numlib/Variational/Forms.lean`) is expected — the same
defeq that Mathlib's `LaxMilgram.lean` relies on with `continuousLinearMapOfBilin (𝕜 := ℝ)` — so
the `RCLike` backbone specialises to the real surface without any conversion function. The only
friction is the `RCLike.re`/`starRingEnd` decoration of backbone statements; it is removed by the
backbone's real specialisations `SesqForm.isCoerciveWith_real_iff`, `SesqForm.isHermitian_real_iff`
and by `simp [RCLike.re_to_real, RCLike.conj_to_real]` (the backbone energy is written
`½ re (a v v) − re (ℓ v)` so that this `simp` call closes the real case). The real-only aspects of
the book — sups of `a(u,v)/‖v‖` without absolute value, `V`-ellipticity without `re`, symmetric
rather than Hermitian forms — are handled once, in D4 and D9; nothing in §8.2–8.3, 8.7, Ch. 9
requires complex scalars.

Files (library `AtkinsonHan`, `srcDir = "Surface"`, importing only `Numlib`; this refines the
`Ch08`/`Ch09` rows of `plans/backbone.md` §8.3):

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
`AtkinsonHan.Ch09.prop_9_1_3`, …) as in `plans/backbone.md` §1.4; definitions get descriptive names.

Common preamble (all files): `variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]`
(+ `[CompleteSpace V]` = "Hilbert"), `ℓ : StrongDual ℝ V` (`= V →L[ℝ] ℝ`), `open InnerProductSpace`.

Classification used in §3 for each book item: `direct` (a Mathlib or backbone theorem applies as
is; it is named), `needs-equivalence` (specialisation through the bridging lemmas of §2; the
lemmas are named), `surface-only` (short self-contained proof from Mathlib), `deferred` (needs a
backbone item of a later phase; item and phase named, collected in §5), `out-of-scope` (reason
given; collected in §6).

## 2. Book-specific definitions

### D1. Closed operator (Def 8.2.2)
* Book: `T : D(T) ⊂ V → W` (Banach spaces) is closed if `v_n ∈ D(T)`, `v_n → v`, `T v_n → w` imply
  `v ∈ D(T)` and `T v = w`.
* Lean: partial linear operators are `LinearPMap ℝ V W` (`V →ₗ.[ℝ] W`, fields `domain`, `toFun`);
  the book's `D(L)` is `L.domain`, `R(L)` is `LinearMap.range L.toFun`.
* Mathlib counterpart: `LinearPMap.IsClosed` (`IsClosed (f.graph : Set (E × F))`,
  `Mathlib/Topology/Algebra/Module/LinearPMap.lean`). The backbone's closed-operator theorem
  (`LinearPMap.isClosed_range_of_isClosed_of_le_norm`, `Numlib/Variational/LaxMilgram.lean`) takes
  `L.IsClosed` directly, so the sequential form below is only the book-facing equivalence.
* Equivalence lemma `LinearPMap.isClosed_iff_seq` (surface):
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
  for `L : V →L[ℝ] W`. The backbone states its §8.2 theorems with exactly these hypotheses
  (`ContinuousLinearMap.isClosed_range_of_le_norm`, `ContinuousLinearMap.norm_le_of_le_norm`,
  `LinearPMap.isClosed_range_of_isClosed_of_le_norm` in `Numlib/Variational/LaxMilgram.lean`), so
  no bridge is needed towards the backbone.
* Mathlib: `AntilipschitzWith (c⁻¹).toNNReal ⇑L`; bridges `AntilipschitzWith.of_le_mul_dist`,
  `AntilipschitzWith.le_mul_dist`, `ContinuousLinearMap.antilipschitz_of_bound`,
  `ContinuousLinearMap.bound_of_antilipschitz`.
* Equivalence lemma (for Mathlib's antilipschitz lemmas) `stabilityEstimate_iff_antilipschitz
  (hc : 0 < c) : (∀ v, c * ‖v‖ ≤ ‖L v‖) ↔ AntilipschitzWith ⟨c⁻¹, _⟩ L` (linear maps:
  `dist = ‖·‖`).

### D3. Annihilators and the dual operator (§8.2, Banach setting)
* Book: `L* : D(L*) ⊂ W' → V'`, `⟨L* w*, v⟩ = ⟨w*, L v⟩` for densely defined `L`;
  `N(L)^⊥ ⊂ V'`, `N(L*)^⊥ ⊂ W` (annihilator / pre-annihilator).
* Mathlib: algebraic `LinearMap.dualMap`, `Submodule.dualAnnihilator`, `Submodule.dualCoannihilator`
  (`Module.Dual`, not `StrongDual`); Hilbert adjoints `ContinuousLinearMap.adjoint` (bounded) and
  `LinearPMap.adjoint` (densely defined; `LinearPMap.adjoint_isClosed`). Mathlib has no continuous
  Banach `dualMap` for unbounded operators.
* Surface: **not defined** (only used by Thm 8.2.7, which is out of scope, §6). The Hilbert
  specialisation uses `T†` and `Submodule.orthogonal` instead of annihilators.

### D4. Bilinear forms and their properties (§8.3)
* Book: `a : V × V → ℝ` bilinear; bounded (`|a(u,v)| ≤ M‖u‖‖v‖`), positive (`a(v,v) ≥ 0`),
  strictly positive (`a(v,v) > 0`, `v ≠ 0`), strongly positive / `V`-elliptic
  (`a(v,v) ≥ α‖v‖²`, `α > 0`), symmetric (`a(u,v) = a(v,u)`).
* Lean (`Ch08/BilinearForms.lean`):
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
* Mathlib / backbone counterparts and equivalence lemmas (backbone predicates in
  `Numlib/Variational/Forms.lean` and `Numlib/Analysis/InnerProductSpace/Coercive.lean`, `plans/backbone.md`
  §5.2.1 and §2.1.4):
  * bounded ↔ `IsBoundedBilinearMap ℝ (fun p : V × V => a p.1 p.2)`
    (`isBounded_iff_isBoundedBilinearMap`; ⇐ from `IsBoundedBilinearMap.bound`, ⇒ the four
    linearity fields come from `a`) and ↔ `∃ B : V →L[ℝ] V →L[ℝ] ℝ, ∀ u v, B u v = a u v` (`toCLM`;
    norm bounds `ContinuousLinearMap.le_opNorm₂`, `LinearMap.mkContinuous₂_norm_le`). The backbone's
    `SesqForm.IsBoundedWith M` is `∀ u v, ‖a u v‖ ≤ M * ‖u‖ * ‖v‖`, so
    `isBoundedWith_iff_toCLM : a.IsBoundedWith M ↔ (a.toCLM hM').IsBoundedWith M` is
    `Real.norm_eq_abs`; `SesqForm.isBoundedWith_opNorm` and `SesqForm.opNorm_le_of_isBoundedWith`
    relate `M` to `‖a.toCLM hM‖`.
  * `V`-elliptic ↔ Mathlib `IsCoercive (a.toCLM hM)` (`∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`,
    `Mathlib/Analysis/Normed/Operator/NormedSpace.lean`): `isElliptic_iff_isCoercive`, proof by
    `sq`/`mul_assoc`.
  * `IsEllipticWith α` ↔ `SesqForm.IsCoerciveWith (a.toCLM hM) α`:
    `isEllipticWith_iff_isCoerciveWith`, which is `SesqForm.isCoerciveWith_real_iff` read through
    `toCLM_apply`.
  * `IsEllipticWith α` ↔ `(toOperator a hM : V →ₗ[ℝ] V).IsCoerciveWith α`
    (`LinearMap.IsCoerciveWith`, §2.1.4): `SesqForm.isCoerciveWith_iff_toOperator`.
  * `LinearMap.IsSymm a` ↔ `∀ u v, a u v = a v u` (`simp [LinearMap.isSymm_def]`) ↔
    `SesqForm.IsHermitian (a.toCLM hM)` (`SesqForm.isHermitian_real_iff`) ↔
    `(toOperator a hM : V →ₗ[ℝ] V).IsSymmetric` (`SesqForm.isHermitian_iff_toOperator_isSymmetric`)
    ↔ `IsSelfAdjoint (toOperator a hM)` (`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`).
  * `IsSymm ∧ IsElliptic` ↔ `LinearMap.IsSymmetricCoercive (toOperator a hM)` (§2.1.4).
  * positive: Mathlib `LinearMap.IsPositive` *includes* symmetry, so the book's "positive" is only
    `∀ v, 0 ≤ ⟪A v, v⟫`; no backbone counterpart needed. Strictly positive ↔ elliptic in finite
    dimension (`LinearMap.isCoercive_iff_forall_pos`, §2.1.4).

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
  and `a ↦ A` is `toCLM` (D4). The §9.4 operator and right-hand side are the backbone's:
  ```lean
  noncomputable abbrev toOperator (a : BilinForm V) {M} (hM : a.IsBoundedWith M) : V →L[ℝ] V :=
    SesqForm.toOperator (a.toCLM hM)      -- = InnerProductSpace.continuousLinearMapOfBilin _
  theorem inner_toOperator : ⟪toOperator a hM u, v⟫_ℝ = a u v   -- `SesqForm.inner_toOperator`
  -- `f` is `SesqForm.rieszRep ℓ` (= `(toDual ℝ V).symm ℓ`), used directly
  ```
  `⟪rieszRep ℓ, v⟫ = ℓ v` and `‖rieszRep ℓ‖ = ‖ℓ‖` are `SesqForm.inner_rieszRep`,
  `SesqForm.norm_rieszRep`.
* Backbone: `SesqForm.toOperator` (`Numlib/Variational/Forms.lean`) is an `abbrev` of Mathlib's
  `InnerProductSpace.continuousLinearMapOfBilin`, so every backbone `toOperator` lemma applies to
  the surface `toOperator a hM` by `rfl`. The backbone's `SesqForm.ofOperator`,
  `toOperator_ofOperator`, `ofOperator_toOperator` are the §9.4 correspondence `A ↔ a` on the
  Hilbert space; `SesqForm.forall_apply_eq_iff_toOperator_eq` is (9.4.7) ⇔ (9.4.4).

### D6. Energy functional, energy inner product and energy norm (Thm 8.3.3, (9.1.7), §9.4)
* Book: `E(v) = ½ a(v,v) − ℓ(v)`; `(u,v)_a = a(u,v)`, `‖v‖_a = √a(v,v)`, equivalent to `‖·‖`:
  `c₁‖v‖ ≤ ‖v‖_a ≤ c₂‖v‖`.
* Lean:
  ```lean
  noncomputable def energy (a : BilinForm V) (ℓ : StrongDual ℝ V) (v : V) : ℝ := (1/2 : ℝ) * a v v - ℓ v
  noncomputable def energyNorm (a : BilinForm V) (v : V) : ℝ := Real.sqrt (a v v)
  ```
* Backbone: `SesqForm.energy a ℓ v = ½ re (a v v) − re (ℓ v)`, `SesqForm.energyNorm a v =
  √(re (a v v))`, `SesqForm.energyNorm_eq_energyNorm_toOperator`,
  `SesqForm.sqrt_mul_norm_le_energyNorm (hc : 0 ≤ c) (h : a.IsCoerciveWith c)`,
  `SesqForm.energyNorm_le_sqrt_mul_norm (h : a.IsBoundedWith M)` (`Numlib/Variational/Forms.lean`);
  operator-level `energyInner`, `energyNorm A x = √(re ⟪A x, x⟫)`, `WithEnergy A hA`,
  `LinearMap.IsCoerciveWith.norm_le_energyNorm` (`Numlib/Analysis/InnerProductSpace/Energy.lean`, §2.1.5).
* Equivalence lemmas: `energy_eq : energy a ℓ v = (a.toCLM hM).energy ℓ v` (`simp [SesqForm.energy]`
  with `RCLike.re_to_real`); `energyNorm_eq : energyNorm a v = (a.toCLM hM).energyNorm v` and
  `= _root_.energyNorm (toOperator a hM : V →ₗ[ℝ] V) v` (`energyNorm_eq_energyNorm_toOperator`);
  `sqrt_alpha_mul_norm_le_energyNorm`, `energyNorm_le_sqrt_M_mul_norm` (`c₁ = √α`, `c₂ = √M`) are
  the two backbone norm-equivalence lemmas read through `energyNorm_eq`.

### D7. Galerkin problem (9.1.4), stiffness matrix and load vector (9.1.5)
* Book: `u_N ∈ V_N`, `a(u_N, v) = ℓ(v) ∀ v ∈ V_N`, `V_N ⊂ V` an `N`-dimensional subspace;
  `A = (a(φ_j, φ_i)) ∈ ℝ^{N×N}`, `b = (ℓ(φ_i))`, `u_N = Σ ξ_j φ_j`.
* Lean:
  ```lean
  def GalerkinProblem (a : BilinForm V) (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V) (uN : V) : Prop :=
    uN ∈ VN ∧ ∀ v ∈ VN, a uN v = ℓ v
  def stiffnessMatrix (a : BilinForm V) {N} (φ : Fin N → V) : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun i j => a (φ j) (φ i)
  def loadVector (ℓ : StrongDual ℝ V) {N} (φ : Fin N → V) : Fin N → ℝ := fun i => ℓ (φ i)
  ```
  `V_N` "`N`-dimensional" is `[FiniteDimensional ℝ VN]` (+ `Module.finrank ℝ VN = N` only where `N`
  matters, i.e. in §9.2).
* Backbone: `IsGalerkinSolution (a : SesqForm 𝕜 V) ℓ K u := u ∈ K ∧ ∀ v ∈ K, a u v = ℓ v`
  (`Numlib/Variational/Galerkin.lean`, §5.2.3); `IsGalerkinSolution.iff_isGalerkin` bridges to the
  operator specification `IsGalerkin (toOperator a) (rieszRep ℓ) 0 K u`
  (`Numlib/LinearSolve/Projection/Basic.lean`, §2.4.1); `IsGalerkinSolution.iff_mulVec` is the
  stiffness-matrix system for a basis `φ : Module.Basis ι 𝕜 K`.
* Equivalence: `galerkinProblem_iff : GalerkinProblem a ℓ VN u ↔ IsGalerkinSolution (a.toCLM hM) ℓ VN u`
  (`Iff.rfl` up to `toCLM_apply`); then the backbone bridge `iff_isGalerkin`.

### D8. Petrov–Galerkin problem (9.2.5)
* Book: `U, V` real Hilbert, `a : U × V → ℝ`, `U_N ⊂ U`, `V_N ⊂ V`, `dim U_N = dim V_N = N`;
  `u_N ∈ U_N`, `a(u_N, v_N) = ℓ(v_N) ∀ v_N ∈ V_N`.
* Lean: `a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ`,
  ```lean
  def PetrovGalerkinProblem (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ℓ : StrongDual ℝ V) (UN : Submodule ℝ U)
      (VN : Submodule ℝ V) (uN : U) : Prop := uN ∈ UN ∧ ∀ v ∈ VN, a uN v = ℓ v
  ```
  with `[FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN)`.
* Backbone: two-space forms `SesqForm₂ 𝕜 U V` (= `U →L⋆[𝕜] V →L[𝕜] 𝕜`,
  `Numlib/Variational/Forms.lean`) and
  `IsPetrovGalerkinSolution (a : SesqForm₂ 𝕜 U V) ℓ (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) u`
  (`Numlib/Variational/Galerkin.lean`); `isGalerkinSolution_iff_isPetrovGalerkinSolution` is the
  one-space case `U = V`, `K = L`.
* Equivalence: `petrovGalerkinProblem_iff : … ↔ IsPetrovGalerkinSolution (a.toCLM₂ hM) ℓ UN VN u`
  (`toCLM₂` = `LinearMap.mkContinuous₂` for the two-space form; `Iff.rfl` up to `toCLM₂_apply`).

### D9. Discrete inf–sup constant `α_N` (9.2.6), inf–sup condition (9.2.13)–(9.2.14)
* Book: `sup_{0≠v_N∈V_N} a(u_N,v_N)/‖v_N‖_V ≥ α_N ‖u_N‖_U ∀ u_N ∈ U_N`; uniform version with `α_0`;
  equivalently `inf_{0≠u_N} sup_{0≠v_N} a(u_N,v_N)/(‖u_N‖‖v_N‖) ≥ α_0`.
* Lean (the sup is a real `iSup` over the subtype `{v : VN // v ≠ 0}`, bounded above by `M ‖u_N‖`
  thanks to (9.2.2), so `Real.iSup` is meaningful):
  ```lean
  def DiscreteInfSup (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (UN : Submodule ℝ U) (VN : Submodule ℝ V) (αN : ℝ) : Prop :=
    ∀ uN ∈ UN, αN * ‖uN‖ ≤ ⨆ vN : {v : VN // v ≠ 0}, a uN vN / ‖(vN : V)‖
  def InfSupCondition (a) (UN : ℕ → Submodule ℝ U) (VN : ℕ → Submodule ℝ V) (α₀ : ℝ) : Prop :=
    ∀ N, DiscreteInfSup a (UN N) (VN N) α₀                                   -- (9.2.13)
  noncomputable def infSupValue (a) (UN) (VN) : ℝ :=                          -- the quantity in (9.2.14)
    ⨅ uN : {u : UN // u ≠ 0}, ⨆ vN : {v : VN // v ≠ 0}, a uN vN / (‖(uN : U)‖ * ‖(vN : V)‖)
  ```
  The same shape (with `V` in place of `VN`) is the continuous condition (8.7.2)/(9.2.3).
* Backbone (operator-norm form, `Numlib/Variational/Forms.lean` and `Galerkin.lean`):
  `SesqForm₂.InfSupWith a α := ∀ u, α * ‖u‖ ≤ ‖a u‖` (norm of the functional `a u : V →L[𝕜] 𝕜`),
  `SesqForm₂.IsNondegenerate a := ∀ v, v ≠ 0 → ∃ u, a u v ≠ 0` ((8.7.3)/(9.2.4)),
  `SesqForm₂.iSup_norm_div_eq_norm : (⨆ v : {v : V // v ≠ 0}, ‖a u v‖ / ‖v‖) = ‖a u‖`, and the
  discrete condition `IsPetrovGalerkinSolution.DiscreteInfSup a K L α :=
  ∀ w ∈ K, α * ‖w‖ ≤ ‖(a w).comp L.subtypeL‖` (norm of the functional restricted to `L`).
* Equivalence lemmas: `iSup_div_eq_iSup_abs_div` (sign symmetry `v ↦ -v`);
  `iSup_abs_div_eq_opNorm (f : V →L[ℝ] ℝ) : (⨆ v : {v : V // v ≠ 0}, |f v| / ‖v‖) = ‖f‖` (from
  `ContinuousLinearMap.sSup_unit_ball_eq_norm`, `Mathlib/Analysis/Normed/Operator/NNNorm.lean`, or
  directly from `opNorm_le_bound`/`le_opNorm`; the backbone's `iSup_norm_div_eq_norm` is its
  instance `f := a u`, and the surface applies it also to `f := (a.toCLM₂ hM w).comp VN.subtypeL`);
  hence `infSup_iff_infSupWith : (∀ u, α * ‖u‖ ≤ ⨆ …) ↔ (a.toCLM₂ hM).InfSupWith α` and
  `discreteInfSup_iff : DiscreteInfSup a UN VN αN ↔
  IsPetrovGalerkinSolution.DiscreteInfSup (a.toCLM₂ hM) UN VN αN`; (8.7.3) as `∃ u, 0 < a u v` is
  `IsNondegenerate` by the same sign flip.

### D10. The `N`-dependent norm and `V + V_N` (§9.3)
* Book: `‖·‖_N`, `a_N`, `ℓ_N` defined on `V + V_N = {v + v_N}`; `V_N ⊄ V` allowed.
* Lean: a normed space `W` *is* `V + V_N` equipped with `‖·‖_N` (one `W` per fixed `N`; the
  theorem is stated for one `N` at a time, so no family/type-synonym machinery is needed):
  `{W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
  (VN : Submodule ℝ W) [FiniteDimensional ℝ VN] (u : W)`.
* Backbone: exactly this setting — `IsGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
  (ℓN : W →ₗ[𝕜] 𝕜) (K : Submodule 𝕜 W) (uN : W) := uN ∈ K ∧ ∀ v ∈ K, aN uN v = ℓN v` on
  `[NormedAddCommGroup W] [NormedSpace 𝕜 W]` (`Numlib/Variational/Galerkin.lean`, section
  `Strang`; `aN` need not be bounded on all of `W × W`). The surface's `GeneralizedGalerkinProblem`
  is this definition at `𝕜 = ℝ` (an `abbrev`). The surface wrapper adds the book's `V` (Hilbert),
  an injection `ι : V →ₗ[ℝ] W` and the exact solution `u : V` of (9.1.1); the proof never uses them.

### D11. The conjugate gradient algorithm (§9.4, Algorithm 1)
* Book: `r_k ∈ V` with `(r_k, v) = ℓ(v) − a(u_k, v)`; `s_0 = r_0`;
  `α_k = ‖r_k‖²/a(s_k,s_k)`, `u_{k+1} = u_k + α_k s_k`, `β_k = ‖r_{k+1}‖²/‖r_k‖²`, `s_{k+1} = r_{k+1} + β_k s_k`.
* Lean (on the backbone's `CG.State V`, fields `x r p`):
  ```lean
  noncomputable def residual (a) (hM) (ℓ) (u : V) : V := SesqForm.rieszRep (ℓ - a.toCLM hM u)
  theorem inner_residual : ⟪residual a hM ℓ u, v⟫_ℝ = ℓ v - a u v      -- `inner_rieszRep`, `sub_apply`
  noncomputable def cgStep (a) (hM) (ℓ) (st : CG.State V) : CG.State V :=
    let αk := ‖st.r‖ ^ 2 / a st.p st.p
    let u' := st.x + αk • st.p
    let r' := residual a hM ℓ u'
    ⟨u', r', r' + (‖r'‖ ^ 2 / ‖st.r‖ ^ 2) • st.p⟩
  noncomputable def cgIterate (a) (hM) (ℓ) (u₀ : V) (k : ℕ) : CG.State V :=
    (cgStep a hM ℓ)^[k] ⟨u₀, residual a hM ℓ u₀, residual a hM ℓ u₀⟩
  ```
  (Lean's `x/0 = 0` makes the stalled iteration `r_k = 0` fixed at the solution, matching the
  stopping criterion; the backbone's `CG.iterate_eq_of_residual_eq_zero` is the same fact.)
* Backbone (`Numlib/Krylov/CG.lean`, §3.7): `CG.State`, `CG.alpha A s = ⟪r, r⟫ / ⟪A p, p⟫`,
  `CG.step` (residual updated recursively, `CG.step_r : (step A s).r = s.r - alpha A s • A s.p`),
  `CG.init`, `CG.iterate A b x₀ k`, `CG.residual_eq : (iterate A b x₀ k).r = b - A (iterate …).x`.
* Equivalence: `cgIterate_eq : cgIterate a hM ℓ u₀ k = CG.iterate (toOperator a hM) (rieszRep ℓ) u₀ k`
  by induction on `k`: `residual_eq' : residual a hM ℓ u = rieszRep ℓ - toOperator a hM u`
  (`map_sub`, `SesqForm.forall_apply_eq_iff_toOperator_eq`), `inner_toOperator` for
  `a s s = ⟪A s, s⟫` (so `αk = CG.alpha A st` via `real_inner_self_eq_norm_sq`), and
  `CG.residual_eq`/`CG.step_r` to identify the recomputed residual with the recursive one.

## 3. Results

### §8.2 General existence and uniqueness

**Thm 8.2.1.** `V, W` Hilbert, `L : D(L) ⊂ V → W` linear: `R(L) = W` iff `R(L)` is closed and `R(L)^⊥ = {0}`.
* Lean: `theorem thm_8_2_1 [CompleteSpace W] (L : V →ₗ.[ℝ] W) : LinearMap.range L.toFun = ⊤ ↔
  IsClosed (LinearMap.range L.toFun : Set W) ∧ (LinearMap.range L.toFun)ᗮ = ⊥` (only `W` complete is
  used; `V` needs no completeness or inner product).
* Mathlib: `Submodule.topologicalClosure_eq_top_iff` (`K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥`,
  `[CompleteSpace E]`), `IsClosed.submodule_topologicalClosure_eq`, `isClosed_univ`,
  `Submodule.top_orthogonal_eq_bot`.
* Proof route: `→`: `⊤` is closed and `⊤ᗮ = ⊥`. `←`: closed ⇒ `topologicalClosure = range`, apply the
  iff. (The book separates by Hahn–Banach; the orthogonal-projection proof is what Mathlib has.)
* Classification: **direct**.

**Def 8.2.2 / remark "continuous ⇒ closed".** See D1. Classification: **needs-equivalence**
(`isClosed_iff_seq`), continuity ⇒ closed **surface-only**.

**(8.2.2) stability estimate.** See D2. Classification: **needs-equivalence** (antilipschitz, for
Mathlib's lemmas only).

**Thm 8.2.4.** `V, W` Hilbert, `L : D(L) ⊂ V → W` linear closed, (8.2.2) with `c > 0`, `R(L)^⊥ = {0}`.
Then for each `f ∈ W` the equation `L u = f` has a unique solution `u ∈ D(L)`.
* Lean: `theorem thm_8_2_4 [CompleteSpace V] [CompleteSpace W] (L : V →ₗ.[ℝ] W)
  (hL : L.IsClosed) {c} (hc : 0 < c) (hstab : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖)
  (horth : (LinearMap.range L.toFun)ᗮ = ⊥) (f : W) : ∃! u : L.domain, L u = f`.
* Backbone: `LinearPMap.isClosed_range_of_isClosed_of_le_norm (L : V →ₗ.[𝕜] W) (hL : L.IsClosed)
  (hc : 0 < c) (h : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖) :
  IsClosed (LinearMap.range L.toFun : Set W)` (`Numlib/Variational/LaxMilgram.lean`, section
  `APriori`; `V`, `W` complete). Its proof: the graph `G = L.graph` is closed hence complete
  (`IsClosed.completeSpace_coe`); `Prod.snd : G → W` is antilipschitz with constant `max 1 c⁻¹`
  (`‖(v, L v)‖ = max ‖v‖ ‖L v‖ ≤ max 1 c⁻¹ · ‖L v‖`), so `AntilipschitzWith.isClosed_range` gives
  `R(L)` closed.
* Surface proof: closed range + `horth` ⇒ `thm_8_2_1` ⇒ `R(L) = ⊤`; uniqueness from `hstab`.
* Classification: **needs-equivalence** (closed range from the backbone, assembled with
  `thm_8_2_1`).

**Remark after 8.2.4 (continuity replaces closedness).** `L : V →L[ℝ] W`, stability, `(range L)ᗮ = ⊥`
⇒ `Function.Bijective L`.
* Backbone: `ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot (L : V →L[𝕜] W)
  (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) (hdense : (LinearMap.range (L : V →ₗ[𝕜] W))ᗮ = ⊥)`,
  with `ContinuousLinearMap.isClosed_range_of_le_norm` and `ContinuousLinearMap.norm_le_of_le_norm`
  (the quantitative inverse bound `‖v‖ ≤ ‖w‖ / c`) alongside (`Numlib/Variational/LaxMilgram.lean`).
* Classification: **direct**.

**Ex 8.2.5.** `V` Hilbert, `L ∈ L(V, V')` strongly monotone (`⟨L v, v⟩ ≥ c‖v‖²`) ⇒ (8.2.2) with the
same `c`, `R(L)^⊥ = {0}` (in the duality sense), hence `L u = f` uniquely solvable for all `f ∈ V'`.
* Lean: `theorem ex_8_2_5 [CompleteSpace V] (L : V →L[ℝ] StrongDual ℝ V) {c} (hc : 0 < c)
  (hmono : ∀ v, c * ‖v‖ ^ 2 ≤ L v v) : (∀ v, c * ‖v‖ ≤ ‖L v‖) ∧ (∀ v, (∀ w, L w v = 0) → v = 0) ∧
  Function.Bijective L`.
* Backbone: `L` is a `SesqForm ℝ V` by defeq and `hmono` is `L.IsCoerciveWith c`
  (`SesqForm.isCoerciveWith_real_iff`); (8.2.2) with the same `c` is
  `SesqForm.IsCoerciveWith.norm_le_norm_apply`; bijectivity from `SesqForm.exists_solutionEquiv`
  (the solution operator `V' ≃L⋆[𝕜] V`, conjugate-linear in general and plainly linear over `ℝ`) or
  `SesqForm.laxMilgram`.
* Mathlib alternative: `IsCoercive.bounded_below` (`C * ‖v‖ ≤ ‖B♯ v‖`, and `‖B♯ v‖ = ‖B v‖` by
  `LinearIsometryEquiv.norm_map`), `IsCoercive.continuousLinearEquivOfBilin` (bijective `B♯`;
  transport to `B = toDual ∘ B♯` by `toDual` bijective).
* Classification: **direct**.

**Thm 8.2.7 (closed range theorem).** `V, W` Banach, `L` densely defined closed: (a) `R(L)` closed ⇔
(b) `R(L) = N(L*)^⊥` ⇔ (c) `R(L*)` closed ⇔ (d) `R(L*) = N(L)^⊥`; abstract Fredholm alternative.
* Classification: **out-of-scope** in the stated generality (Banach dual of an unbounded operator;
  not in Mathlib, see D3 and §6). The Hilbert-space, bounded specialisation is **direct**: for
  `T : V →L[ℝ] W`, `T.rangeᗮ = T†.ker` (`ContinuousLinearMap.orthogonal_range`) and
  `Submodule.orthogonal_orthogonal_eq_closure` give `IsClosed (range T) → range T = (ker T†)ᗮ`,
  i.e. `f ∈ range T ↔ ∀ w, T† w = 0 → ⟪w, f⟫ = 0` — record as `thm_8_2_7_hilbert` with a docstring.

**Thm 8.2.8.** `T : D(T) ⊂ V → W` (nonlinear), `w ∈ W`: at most one solution of `T u = w` if
(a) `‖T u − T v‖ ≥ c‖u − v‖` on `D(T)` (`c > 0`), or (b) `‖(T u − u) − (T v − v)‖ < ‖u − v‖` for `u ≠ v`
(here `W = V`).
* Lean: `theorem thm_8_2_8a (D : Set V) (T : V → W) {c} (hc : 0 < c)
  (hstab : ∀ u ∈ D, ∀ v ∈ D, c * ‖u - v‖ ≤ ‖T u - T v‖) (w : W) :
  ∀ u₁ ∈ D, ∀ u₂ ∈ D, T u₁ = w → T u₂ = w → u₁ = u₂`; (b) analogous with `T : V → V`.
  Remark: linear case (a) = (8.2.2) — `Iff.rfl` after `map_sub`.
* Mathlib: `AntilipschitzWith.injective`/`Set.InjOn`; (b) is a two-line contradiction.
* Classification: **surface-only**.

### §8.3 The Lax–Milgram Lemma

**Remark (before 8.3.1): `a` continuous iff `∃ M > 0, |a(u,v)| ≤ M‖u‖‖v‖`.**
* Lean: `theorem continuous_iff_isBounded (a : BilinForm V) :
  Continuous (fun p : V × V => a p.1 p.2) ↔ a.IsBounded`.
* Mathlib: ⇐ `IsBoundedBilinearMap.continuous`; ⇒ needs the standard "continuous at `0` ⇒ bounded on
  a ball ⇒ bound `δ⁻²`" argument (no bilinear lemma for it in Mathlib).
* Classification: **surface-only** (small; optional).

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
  On the Hilbert space the same bounds are `SesqForm.isBoundedWith_opNorm` and
  `SesqForm.opNorm_le_of_isBoundedWith`.
* Classification: **direct** (the equivalence is bookkeeping; `IsBounded` must carry `M > 0`, which
  the book assumes).

**Dictionary after 8.3.1 (Hilbert `V`; five bullets).** `a` bounded / positive / strictly positive /
strongly positive (`V`-elliptic) / symmetric ⇔ the same for `A` (`⟨A v, v⟩ …`).
* Lean: with `a := ofCLM A` each bullet is `Iff.rfl` except the first: `isBoundedWith_ofCLM_iff :
  (ofCLM A).IsBoundedWith M ↔ ∀ v, ‖A v‖ ≤ M * ‖v‖` (`opNorm_le_bound`/`le_opNorm`),
  `isPositive_ofCLM_iff`, `isStrictlyPositive_ofCLM_iff`, `isEllipticWith_ofCLM_iff`, `isSymm_ofCLM_iff`.
  Through Riesz (`toOperator`) they become the backbone predicates (D4 bullets).
* Backbone: `LinearMap.IsCoercive`, `IsSymmetricCoercive` (§2.1.4); `SesqForm.IsCoerciveWith`,
  `IsHermitian`, `isCoerciveWith_iff_toOperator`, `isHermitian_iff_toOperator_isSymmetric` (§5.2.1).
* Classification: **needs-equivalence**.

**Thm 8.3.2.** `K ⊂ V` nonempty closed convex, `V` Hilbert, `ℓ ∈ V'`, `E(v) = ½‖v‖² − ℓ(v)`: ∃! `u ∈ K`
with `E(u) = inf_K E`; `u` is characterised by `u ∈ K, (u, v − u) ≥ ℓ(v − u) ∀ v ∈ K`; if `K` is a
subspace, by `u ∈ K, (u, v) = ℓ(v) ∀ v ∈ K`.
* Lean:
  ```lean
  theorem thm_8_3_2 [CompleteSpace V] {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K)
      (ℓ : StrongDual ℝ V) :
      (∃! u, u ∈ K ∧ IsMinOn (fun v => (1/2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u) ∧
      (∀ u ∈ K, IsMinOn (fun v => (1/2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ)
  theorem thm_8_3_2_subspace … (K : Submodule ℝ V) (hK : IsClosed (K : Set V)) (hu : u ∈ K) :
      IsMinOn … K u ↔ ∀ v ∈ K, ⟪u, v⟫_ℝ = ℓ v
  ```
  (`IsMinOn` ⇔ `E u = ⨅ v : K, E v` for `u ∈ K`: surface helper `isMinOn_iff_eq_ciInf` for `f`
  bounded below on `K`.)
* Backbone: the three energy theorems of `Numlib/Variational/LaxMilgram.lean` at `a := innerSL ℝ`
  (`SesqForm.innerSL_isCoerciveWith` with `c = 1`, `SesqForm.innerSL_isHermitian`):
  `SesqForm.existsUnique_isMinOn_energy` (∃! on nonempty closed convex `K`),
  `SesqForm.isMinOn_energy_iff_forall_le` (the variational inequality),
  `SesqForm.isMinOn_energy_iff` (subspace case; closedness of `K` is not needed there).
  `(innerSL ℝ).energy ℓ v = ½‖v‖² − ℓ v` by `real_inner_self_eq_norm_sq`.
* Mathlib alternative: with `z := (toDual ℝ V).symm ℓ`, `E v = ½‖v − z‖² − ½‖z‖²`
  (`toDual_symm_apply`, `norm_sub_sq_real`), so minimisers of `E` on `K` are the projections of `z`:
  `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`,
  `norm_eq_iInf_iff_real_inner_eq_zero`; uniqueness from strict convexity / `Submodule.starProjection`.
* Classification: **needs-equivalence** (or **direct** via the completing-the-square route).

**Thm 8.3.3.** `K` nonempty closed convex, `a` bilinear symmetric bounded `V`-elliptic, `ℓ ∈ V'`,
`E(v) = ½a(v,v) − ℓ(v)`: ∃! `u ∈ K` with (8.3.2) `E(u) = inf_K E`, which is the unique solution of
(8.3.3) `u ∈ K, a(u, v − u) ≥ ℓ(v − u) ∀ v ∈ K`, and of (8.3.4) `u ∈ K, a(u, v) = ℓ(v) ∀ v ∈ K` when `K`
is a subspace.
* Lean: as 8.3.2 with `energy a ℓ` and `a u (v - u)` / `a u v`; hypotheses `(hM : a.IsBoundedWith M)
  (hα : 0 < α) (ha : a.IsEllipticWith α) (hs : a.IsSymm)`.
* Backbone: `SesqForm.existsUnique_isMinOn_energy`, `isMinOn_energy_iff_forall_le`,
  `isMinOn_energy_iff` with `a.toCLM hM`; their hypotheses `(ha : a.IsHermitian) (hc : 0 < c)
  (hcoer : a.IsCoerciveWith c) (hK : Convex ℝ K) (hKc : IsClosed K) (hne : K.Nonempty)` are the
  book's through D4 and D6 (`energy_eq`). The backbone proof is the book's: `(·,·)_a` is an inner
  product with equivalent norm (`WithEnergy`, §2.1.5; `sqrt_mul_norm_le_energyNorm`,
  `energyNorm_le_sqrt_mul_norm` are `c₁ = √α ≤ c₂ = √M`), `K` stays closed/convex, and Thm 8.3.2 /
  Mathlib's `exists_norm_eq_iInf_of_complete_convex` applies there. "`ℓ` continuous for `‖·‖` iff
  for `‖·‖_a`" is the norm equivalence (trivial).
* Classification: **needs-equivalence**.

**Thm 8.3.4 (Lax–Milgram), (8.3.5).** `V` Hilbert, `a` bounded `V`-elliptic bilinear, `ℓ ∈ V'`: unique
solution of (8.3.5) `u ∈ V, a(u, v) = ℓ(v) ∀ v ∈ V`.
* Lean:
  ```lean
  theorem laxMilgram [CompleteSpace V] (a : BilinForm V) {M α : ℝ} (hM : a.IsBoundedWith M) (hα : 0 < α)
      (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v
  ```
  Bonus (from Ex 8.3.1 / (8.7.5)): `laxMilgram_norm_le : ‖u‖ ≤ ‖ℓ‖ / α`.
* Backbone (`Numlib/Variational/LaxMilgram.lean`): `SesqForm.laxMilgram (hc : 0 < c)
  (ha : a.IsCoerciveWith c) : ∃! u, ∀ v, a u v = ℓ v` applied to `a.toCLM hM` (accepted as
  `SesqForm ℝ V` by defeq) with `isEllipticWith_iff_isCoerciveWith`;
  `SesqForm.norm_le_of_forall_apply_eq` is the bound `‖u‖ ≤ ‖ℓ‖ / c`,
  `SesqForm.norm_sub_le_of_forall_apply_eq` the Lipschitz dependence on `ℓ`, and
  `SesqForm.exists_solutionEquiv` the solution operator as `(V →L[𝕜] 𝕜) ≃L⋆[𝕜] V` with norm `≤ 1/c`
  — conjugate-linear, because a sesquilinear form is conjugate-linear in its first slot; over the
  surface's `𝕜 = ℝ` the star is the identity and this is the ordinary `(V →L[ℝ] ℝ) ≃L[ℝ] V`.
* Mathlib alternative: `IsCoercive (a.toCLM hM)` from `ha`; `u := coercive.continuousLinearEquivOfBilin.symm
  ((toDual ℝ V).symm ℓ)` and `continuousLinearEquivOfBilin_apply`, `unique_continuousLinearEquivOfBilin`,
  `toDual_symm_apply`.
* Classification: **needs-equivalence** (backbone) / **direct** (Mathlib).

**Proof #1 ingredient (contraction of `P_θ`).** For `θ ∈ (0, 2α/M²)`:
`‖(I − θ𝒥A)w‖² ≤ (1 − 2θα + θ²M²)‖w‖²`, hence `P_θ` is a contraction and Banach's fixed point
theorem gives the solution.
* Lean: `theorem norm_id_sub_smul_toOperator_sq_le (hM) (ha) (θ : ℝ) (w : V) :
  ‖w - θ • toOperator a hM w‖ ^ 2 ≤ (1 - 2 * θ * α + θ ^ 2 * M ^ 2) * ‖w‖ ^ 2`;
  `contractingWith_pTheta (hθ : θ ∈ Set.Ioo 0 (2*α/M^2)) : ContractingWith _ (fun u => u - θ • (toOperator a hM u - rieszRep ℓ))`.
* Backbone: `ContinuousLinearMap.norm_sub_smul_apply_sq_le (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c)
  (hθ : 0 ≤ θ) (x) : ‖x - (θ : 𝕜) • A x‖ ^ 2 ≤ (1 - 2 * θ * c + θ ^ 2 * ‖A‖ ^ 2) * ‖x‖ ^ 2`
  (`Numlib/Analysis/InnerProductSpace/Coercive.lean`, §2.1.4) and
  `SesqForm.contractingWith_damped_toOperator (hc) (ha : a.IsCoerciveWith c) (ha0 : 0 < ‖a‖)
  (hθ : 0 < θ) (hθ' : θ < 2 * c / ‖a‖ ^ 2)` (`Numlib/Variational/LaxMilgram.lean`), both with `‖a‖`
  in place of `M`; the book's `M`-form follows from `‖a.toCLM hM‖ ≤ M` and monotonicity of the
  factor, or directly from `contractingWith_damped` (`Numlib/Nonlinear/FixedPoint.lean`, §5.3.1)
  with `T := toOperator a hM`, `L := M` (`hlip` from `‖toOperator a hM‖ ≤ M`, `hmono` from
  ellipticity and `inner_toOperator`). Then Mathlib's `ContractingWith.fixedPoint`.
* Classification: **needs-equivalence**.

**Proof #2 ingredient.** `L = 𝒥A` has closed range (`‖L w‖ ≥ α‖w‖`) and `R(L)^⊥ = {0}`; conclude by
Thm 8.2.1. Mathlib: `IsCoercive.isClosed_range`, `IsCoercive.range_eq_top` (`B♯ = 𝒥A`); backbone:
`SesqForm.IsCoerciveWith.norm_le_norm_apply` + `ContinuousLinearMap.isClosed_range_of_le_norm`.
Classification: **direct**.

**Ex 8.3.1.** Deduce Lax–Milgram from Thm 5.1.4 (`T : V → V` strongly monotone and Lipschitz ⇒
`T u = b` uniquely solvable).
* Lean: `theorem ex_8_3_1 … : ∃! u, ∀ v, a u v = ℓ v` proved by applying the surface `Ch05.thm_5_1_4`
  (`plans/surface/AtkinsonHan-Ch5.md`; backbone `zarantonello`, `Numlib/Nonlinear/FixedPoint.lean`)
  to `T := toOperator a hM`, `c₁ = α` (`inner_toOperator`, `ha`), `c₂ = M` (`‖toOperator a hM‖ ≤ M`),
  `b := rieszRep ℓ`; then (9.4.7)⟺(9.4.4) (`SesqForm.forall_apply_eq_iff_toOperator_eq`).
* Classification: **needs-equivalence** (imports `Ch05/FixedPoint.lean` within the same library).

### §8.7 Generalized Lax–Milgram Lemma

**Thm 8.7.1 (Nečas), (8.7.1)–(8.7.5).** `U, V` real Hilbert, `a : U × V → ℝ` bilinear, `ℓ ∈ V'`,
`M, α > 0` with (8.7.1) `|a(u,v)| ≤ M‖u‖_U‖v‖_V`; (8.7.2) `sup_{0≠v∈V} a(u,v)/‖v‖_V ≥ α‖u‖_U ∀ u ∈ U`;
(8.7.3) `sup_{u∈U} a(u,v) > 0 ∀ 0 ≠ v ∈ V`. Then (8.7.4) `u ∈ U, a(u,v) = ℓ(v) ∀ v ∈ V` has a unique
solution and (8.7.5) `‖u‖_U ≤ ‖ℓ‖_{V'}/α`.
* Lean ((8.7.3) is formalised as `∃ u, 0 < a u v`, since as a real `iSup` the unbounded linear sup
  would be junk):
  ```lean
  theorem thm_8_7_1 [CompleteSpace U] [CompleteSpace V] (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ℓ : StrongDual ℝ V)
      {M α : ℝ} (hM : 0 < M) (hα : 0 < α)
      (h871 : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖)
      (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖)
      (h873 : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
      (∃! u, ∀ v, a u v = ℓ v) ∧ ∀ u, (∀ v, a u v = ℓ v) → ‖u‖ ≤ ‖ℓ‖ / α
  ```
* Backbone (`Numlib/Variational/LaxMilgram.lean`, §5.2.2): `SesqForm₂.babuska_necas
  (hα : 0 < α) (hinf : a.InfSupWith α) (hnd : a.IsNondegenerate) : ∃! u, ∀ v, a u v = ℓ v` and
  `SesqForm₂.norm_le_of_infSupWith … (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α` (8.7.5), for
  `a : SesqForm₂ 𝕜 U V` with `U`, `V` complete;
  `SesqForm₂.infSupWith_of_forall_exists (hC : 0 < C) (hinj : ∀ u, (∀ v, a u v = 0) → u = 0)
  (h : ∀ ℓ, ∃ u, (∀ v, a u v = ℓ v) ∧ ‖u‖ ≤ C * ‖ℓ‖) : a.InfSupWith (1 / C)` is the
  converse (well-posedness with `‖u‖ ≤ C‖ℓ‖` forces `InfSupWith (1 / C)`), not stated in the book.
  The left-hand nondegeneracy `hinj` is needed: solvability with a norm bound says nothing about
  vectors the form does not see.
  Backbone proof (the book's): `A : U →L V`, `A u := rieszRep (a u)`; `InfSupWith α` is
  `α‖u‖ ≤ ‖A u‖` ⇒ injective and, with `CompleteSpace U`, closed range
  (`ContinuousLinearMap.isClosed_range_of_le_norm`); nondegeneracy ⇒ `(range A)ᗮ = ⊥`;
  `Submodule.topologicalClosure_eq_top_iff` (`CompleteSpace V`) ⇒ `range A = ⊤`; solve
  `A u = rieszRep ℓ`; (8.7.5): `α‖u‖ ≤ ‖A u‖ = ‖ℓ‖` (`norm_rieszRep`).
* Classification: **needs-equivalence** (through D9: `infSup_iff_infSupWith` and the sign flip
  for (8.7.3)).

**(8.7.2) ↔ operator form.** `(∀ u, α‖u‖ ≤ ⨆ v ≠ 0, a u v / ‖v‖) ↔ (a.toCLM₂ hM).InfSupWith α`
(`infSup_iff_infSupWith`, D9: sign symmetry, then `SesqForm₂.iSup_norm_div_eq_norm`).
Classification: **needs-equivalence** (the one genuinely fiddly `Real.iSup` lemma in this plan is
`iSup_abs_div_eq_opNorm`, shared with the discrete condition).

**Ex 8.7.1.** Thm 8.7.1 generalises Lax–Milgram: with `U = V` and `a` `V`-elliptic (constant `α`),
(8.7.2) holds with the same `α` (take `v = u`) and (8.7.3) holds (take `u = v`).
* Lean: `theorem IsEllipticWith.infSup (ha : a.IsEllipticWith α) (hα : 0 < α) (hM) :
  ∀ u, α * ‖u‖ ≤ ⨆ v : {v // v ≠ 0}, a u v / ‖v‖` (needs `le_ciSup` with the bound from (8.7.1));
  `theorem IsEllipticWith.exists_pos (ha) (hα) : ∀ v ≠ 0, ∃ u, 0 < a u v`;
  `theorem ex_8_7_1 : … := thm_8_7_1 …`.
* Backbone: `SesqForm.IsCoerciveWith.infSupWith (h : a.IsCoerciveWith c) :
  SesqForm₂.InfSupWith (a : SesqForm₂ 𝕜 V V) c` (`Numlib/Variational/Forms.lean`) is the
  operator-norm form of the first claim.
* Classification: **needs-equivalence** (trivial).

### §9.1 The Galerkin method

**(9.1.1) well-posedness.** Under (9.1.2) (`M`) and (9.1.3) (`c₀`), (9.1.1) has a unique solution — this
is `laxMilgram`. Classification: **direct** (`SesqForm.laxMilgram`).

**(9.1.4) well-posedness on `V_N`.** `V_N ⊂ V` finite-dimensional ⇒ unique Galerkin solution.
* Lean: `theorem existsUnique_galerkinProblem [CompleteSpace V] … (VN : Submodule ℝ V) [FiniteDimensional ℝ VN] :
  ∃! uN, GalerkinProblem a ℓ VN uN`.
* Backbone: `IsGalerkinSolution.existsUnique (hc : 0 < c) (ha : a.IsCoerciveWith c)
  [CompleteSpace K]` (`Numlib/Variational/Galerkin.lean`) + `FiniteDimensional.complete` (Mathlib)
  via D7. (Alternative: Mathlib Lax–Milgram on the subtype with `LinearMap.domRestrict₁₂`.)
* Classification: **needs-equivalence**.

**(9.1.5) linear system.** For a basis `{φ_i}` of `V_N`, (9.1.4) ⇔ `A ξ = b` with the stiffness matrix
`A = (a(φ_j, φ_i))` and load vector `b = (ℓ(φ_i))`, `u_N = Σ ξ_j φ_j`.
* Lean: `theorem galerkinProblem_iff_mulVec (φ : Basis (Fin N) ℝ VN) (ξ : Fin N → ℝ) :
  GalerkinProblem a ℓ VN (∑ j, ξ j • (φ j : V)) ↔ (stiffnessMatrix a (fun i => (φ i : V))).mulVec ξ = loadVector ℓ (fun i => (φ i : V))`.
* Backbone: `IsGalerkinSolution.iff_mulVec (φ : Module.Basis ι 𝕜 K) (ξ : ι → 𝕜) :
  IsGalerkinSolution a ℓ K (∑ j, ξ j • (φ j : V)) ↔
  (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) = fun i => ℓ (φ i)`
  (`Numlib/Variational/Galerkin.lean`); the `star ξ` is forced by the form being conjugate-linear in
  its first slot, and over the surface's `𝕜 = ℝ` it is `ξ` itself, so the statement above is the
  book's `A ξ = b` verbatim. `stiffnessMatrix`/`loadVector` unfold to its matrix and
  vector (`ι = Fin N`). The operator analogue is `isPetrovGalerkin_iff_mulVec` (§2.4.1, Saad (5.7)).
* Classification: **needs-equivalence**.

**Ex 9.1.2.** `a` symmetric ⇒ `A` symmetric; `a` `V`-elliptic ⇒ `A` positive definite.
* Lean: `theorem stiffnessMatrix_isSymm (hs : a.IsSymm) : (stiffnessMatrix a φ).IsSymm`;
  `theorem stiffnessMatrix_pos_of_isElliptic (hφ : LinearIndependent ℝ φ) (ha) (hα) :
  ∀ ξ ≠ 0, 0 < ξ ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ`; corollary with both hypotheses:
  `(stiffnessMatrix a φ).PosDef` (Mathlib `Matrix.PosDef` requires `IsHermitian`, so the book's
  "positive definite" without symmetry is the `⬝ᵥ` statement).
* Backbone: `Matrix.posDef_iff_isSymmetricCoercive`, `LinearMap.isCoercive_iff_forall_pos` (§2.1.4).
* Classification: **needs-equivalence**.

**(9.1.6)–(9.1.8), Ex 9.1.1 (Ritz).** `a` symmetric: (9.1.1) ⇔ `E(u) = inf_V E`; (9.1.4) ⇔
`E(u_N) = inf_{V_N} E`; the two discrete problems are equivalent.
* Lean: `theorem galerkinProblem_iff_isMinOn (hs : a.IsSymm) (hM) (hα) (ha) (VN) [FiniteDimensional ℝ VN] (uN) :
  GalerkinProblem a ℓ VN uN ↔ uN ∈ VN ∧ IsMinOn (energy a ℓ) VN uN`; `VN = ⊤` gives (9.1.6).
* Backbone: `SesqForm.isMinOn_energy_iff (ha : a.IsHermitian) (hc) (hcoer) (K : Submodule 𝕜 V)
  (hu : u ∈ K) : IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v`
  (`Numlib/Variational/LaxMilgram.lean`; no finite dimension or closedness needed); the energy
  identity `E(v) − E(u) = ½‖v − u‖_a²` at the solution is
  `SesqForm.energy_sub_energy_eq (hpos : a.IsCoerciveWith 0) (hu : ∀ v, a u v = ℓ v) (v)`. The
  positivity hypothesis is not decorative: `a.energyNorm` is a square root, which Lean sends to `0`
  on negative arguments, so the identity fails for indefinite forms; here it comes free from
  `V`-ellipticity (`IsCoerciveWith.mono` with `0 ≤ c₀`).
* Classification: **needs-equivalence**.

**Prop 9.1.3 (Céa), (9.1.11)–(9.1.12).** `V_N ⊂ V` a subspace, `a` bounded (`M`) `V`-elliptic (`c₀`),
`u` the solution of (9.1.1), `u_N` of (9.1.4): (9.1.12) `a(u − u_N, v) = 0 ∀ v ∈ V_N`, and
(9.1.11) `‖u − u_N‖ ≤ c inf_{v∈V_N} ‖u − v‖` with `c = M/c₀`.
* Lean:
  ```lean
  theorem galerkin_orthogonality (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) :
      ∀ v ∈ VN, a (u - uN) v = 0                                                       -- (9.1.12)
  theorem prop_9_1_3 [CompleteSpace V] (a) {M c₀} (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
      (ha : a.IsEllipticWith c₀) (ℓ) (VN : Submodule ℝ V) {u uN} (hu : ∀ v, a u v = ℓ v)
      (huN : GalerkinProblem a ℓ VN uN) : ‖u - uN‖ ≤ M / c₀ * ⨅ v : VN, ‖u - v‖              -- (9.1.11)
  ```
  (`VN` need not be finite-dimensional; `CompleteSpace V` is only needed if one insists that `u`
  exists — it can be dropped from the inequality.)
* Backbone (`Numlib/Variational/Galerkin.lean`, namespace `IsGalerkinSolution`): `apply_sub_eq_zero`
  (Galerkin orthogonality), `norm_sub_le (hc) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
  (hN) (hstar) (hv : v ∈ K) : ‖ustar - u‖ ≤ M / c * ‖ustar - v‖` (pointwise, explicit `M`) and
  `norm_sub_le_infDist … : ‖ustar - u‖ ≤ M / c * Metric.infDist ustar (K : Set V)`; the book's
  `⨅ v : VN, ‖u - v‖` is `Metric.infDist` by `Metric.infDist_eq_iInf` and `dist_eq_norm`.
* Classification: **needs-equivalence**.

**Céa, symmetric case (un-numbered).** `‖u − u_N‖_a = inf_{v∈V_N} ‖u − v‖_a`; `u_N` is the
`a`-orthogonal projection of `u` onto `V_N` (and `‖u − u_N‖ ≤ √(M/c₀) inf ‖u − v‖`).
* Lean: `theorem energyNorm_sub_eq_iInf (hs : a.IsSymm) … [FiniteDimensional ℝ VN] :
  energyNorm a (u - uN) = ⨅ v : VN, energyNorm a (u - v)`;
  `theorem galerkin_eq_energyProjection : uN = WithEnergy.equiv.symm ((VN.map WithEnergy.equiv).starProjection (WithEnergy.equiv u))`.
* Backbone: `IsGalerkinSolution.energyNorm_sub_le (ha : a.IsHermitian) (hpos : a.IsCoerciveWith 0)
  (hN) (hstar) (hv : v ∈ K) : a.energyNorm (ustar - u) ≤ a.energyNorm (ustar - v)`
  (pointwise best approximation; the `⨅` form by `le_ciInf`/`ciInf_le`; `hpos` for the same
  square-root reason as in (9.1.6)–(9.1.8) — without it the claim fails already for
  `V = ℝ²`, `a = diag(1, −1)`, `K = span (1, 2)`, and `V`-ellipticity supplies it),
  `IsGalerkinSolution.norm_sub_le_sqrt` (`√(M / c)`); the projection
  statement through `IsGalerkinSolution.iff_isGalerkin` and `IsGalerkin.error_eq_starProjection`
  (`Numlib/LinearSolve/Projection/Optimality.lean`, §2.4.2) in `WithEnergy` (§2.1.5), with
  `energyNorm_eq` (D6).
* Classification: **needs-equivalence**.

**Cor 9.1.4, (9.1.13)–(9.1.14).** `V_1 ⊂ V_2 ⊂ ⋯` finite-dimensional with `closure(⋃ V_n) = V` ⇒
`‖u − u_n‖ → 0`.
* Lean:
  ```lean
  theorem cor_9_1_4 [CompleteSpace V] (a) {M c₀} (hM) (hc₀) (ha) (ℓ) (VN : ℕ → Submodule ℝ V)
      [∀ n, FiniteDimensional ℝ (VN n)] (hmono : Monotone VN) (hdense : Dense (⋃ n, (VN n : Set V)))
      {u} (hu : ∀ v, a u v = ℓ v) (uN : ℕ → V) (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
      Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0)
  ```
  (`closure (⋃ V_n) = V` is `Dense`; `Monotone VN` is needed for "pick `v_n ∈ V_n` with `v_n → u`".)
* Backbone: `IsGalerkinSolution.tendsto (hc) (hM) (ha) (hmono : Monotone K)
  (hdense : Dense (⋃ n, (K n : Set V))) (hN : ∀ n, IsGalerkinSolution a ℓ (K n) (uN n)) (hstar) :
  Tendsto uN atTop (𝓝 ustar)` (`Numlib/Variational/Galerkin.lean`; finite dimension not needed),
  built on the shared `tendsto_infDist_of_monotone_dense`; the book's form by
  `tendsto_iff_norm_sub_tendsto_zero`.
* Classification: **needs-equivalence**.

### §9.2 The Petrov–Galerkin method

**(9.2.1) well-posedness under (9.2.2)–(9.2.4).** = `thm_8_7_1`.
Classification: **needs-equivalence**.

**Thm 9.2.1 (Babuška), (9.2.6)–(9.2.9).** `U_N ⊂ U`, `V_N ⊂ V`, `dim U_N = dim V_N = N`, discrete inf–sup
(9.2.6) with `α_N > 0` ⇒ (9.2.5) has a unique solution, (9.2.8) `a(u − u_N, v_N) = 0 ∀ v_N ∈ V_N`,
(9.2.9) triangle inequality, and (9.2.7) `‖u − u_N‖_U ≤ (1 + M/α_N) inf_{w_N∈U_N} ‖u − w_N‖_U`.
* Lean:
  ```lean
  theorem thm_9_2_1 (a : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ℓ) {M αN : ℝ} (h922 : ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖)
      (UN : Submodule ℝ U) (VN : Submodule ℝ V) [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN]
      (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
      (hinfsup : DiscreteInfSup a UN VN αN) {u : U} (hu : ∀ v, a u v = ℓ v) :
      (∃! uN, PetrovGalerkinProblem a ℓ UN VN uN) ∧
      ∀ uN, PetrovGalerkinProblem a ℓ UN VN uN → ‖u - uN‖ ≤ (1 + M / αN) * ⨅ wN : UN, ‖u - wN‖
  ```
  plus `petrovGalerkin_orthogonality` (9.2.8), a one-line surface lemma. Note: completeness of
  `U, V` and (9.2.3)–(9.2.4) are *not* used (only through the existence of `u`); the faithful
  surface statement may keep them as unused hypotheses or, better, omit them with a docstring.
* Backbone (`Numlib/Variational/Galerkin.lean`, namespace `IsPetrovGalerkinSolution`):
  `existsUnique [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
  (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) (hα : 0 < α)
  (hinf : DiscreteInfSup a K L α)` and
  `norm_sub_le (hdim) (hα) (hM0 : 0 ≤ M) (hM : ∀ w v, ‖a w v‖ ≤ M * ‖w‖ * ‖v‖) (hinf) (hN) (hstar)
  (hw : w ∈ K) : ‖ustar - u‖ ≤ (1 + M / α) * ‖ustar - w‖` (pointwise; `⨅` form by `le_ciInf`;
  `hM0` is needed because a boundedness hypothesis quantified over a subspace is vacuous when the
  subspace is trivial and so does not force its own constant nonnegative — with `K = L = 0`,
  `a = 0`, `M = −1` the conclusion would read `‖ustar‖ ≤ 0`; at the surface `M` comes from (9.2.2)
  and is nonnegative),
  through D8 and D9. Backbone proof of solvability: `T : K →ₗ[𝕜] Module.Dual 𝕜 L`,
  `T w := (a w ·)|L`, injective by the discrete inf–sup, `Subspace.dual_finrank_eq` + `hdim` +
  `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ⇒ surjective; the error bound is the
  book's three lines (`α ‖u_N − w_N‖ ≤ ‖(a (u_N − w_N)).comp L.subtypeL‖ ≤ M ‖u − w_N‖`).
* Classification: **needs-equivalence**.

**Rem 9.2.2, (9.2.10) and Kato's lemma.** `‖u − u_N‖_U ≤ (M/α_N) inf_{w_N∈U_N} ‖u − w_N‖_U`
(Xu–Zikatanov); ingredient: `H` Hilbert, `0 ≠ P = P² ≠ I` bounded ⇒ `‖P‖ = ‖I − P‖`, applied to
`P_N u := u_N`.
* Lean: `theorem kato {H} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : H →L[ℝ] H) (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : ‖P‖ = ‖1 - P‖`;
  `theorem rem_9_2_2 … : ‖u - uN‖ ≤ M / αN * ⨅ wN : UN, ‖u - wN‖` (needs `u ↦ u_N` to be a bounded
  idempotent `P_N : U →L[ℝ] U` — build it from `thm_9_2_1`'s `∃!` with `Classical.choose`, linear by
  uniqueness, bounded by `‖P_N u‖ ≤ (M/α_N)‖u‖`; then `‖u − u_N‖ = ‖(1 − P_N)(u − w_N)‖ ≤
  ‖P_N‖ ‖u − w_N‖`).
* Backbone: Kato's lemma is `ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq
  (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : ‖1 - P‖ = ‖P‖`
  (`Numlib/Analysis/InnerProductSpace/Projection/ObliqueProjection.lean`, §2.1.7; proof reference D. Szyld, "The many
  proofs of an identity on the norm of oblique projections", Numer. Algorithms 42 (2006)). The
  Xu–Zikatanov sharpening of Babuška's bound to `M/α_N` is the phase-2 item of
  `plans/backbone.md` §5.2.3 (see §5 below).
* Classification: `kato` **direct**; `rem_9_2_2` **deferred** (backbone §5.2.3 Xu–Zikatanov
  sharpening, phase 2).

**Cor 9.2.3, (9.2.11)–(9.2.12).** `α_N ≥ α_0 > 0` uniformly, `U_{N_1} ⊂ U_{N_2} ⊂ ⋯` with dense union
⇒ `‖u − u_{N_i}‖_U → 0`.
* Lean: as `cor_9_1_4` with `UN VN : ℕ → Submodule`, `hdim : ∀ i, finrank (UN i) = finrank (VN i)`,
  `hinfsup : ∀ i, DiscreteInfSup a (UN i) (VN i) (αN i)`, `hα : ∀ i, α₀ ≤ αN i`, `Monotone UN`,
  `Dense (⋃ i, (UN i : Set U))`; conclusion `Tendsto (fun i => ‖u - uN i‖) atTop (𝓝 0)`.
* Backbone: `IsPetrovGalerkinSolution.tendsto` (uniform constant `α`, hypotheses `hdim`, `hα`,
  `hM0 : 0 ≤ M`, `hM`, `hinf : ∀ n, DiscreteInfSup a (K n) (L n) α`, `hmono`, `hdense`, `hN`,
  `hstar`; conclusion
  `Tendsto uN atTop (𝓝 ustar)`), `tendsto_infDist_of_monotone_dense`. The book's varying `α_N ≥ α₀`
  reduces to the uniform form by monotonicity of `DiscreteInfSup` in `α` (surface lemma
  `DiscreteInfSup.mono`).
* Classification: **needs-equivalence**.

**Remark after Cor 9.2.3.** Convergence holds as soon as `max{1, α_N⁻¹} inf_{w_N} ‖u − w_N‖ → 0`.
Lean: from (9.2.7), `1 + M/αN ≤ (1 + M) * max 1 αN⁻¹`. Classification: **surface-only**.

**(9.2.13) ⇔ (9.2.14) (inf–sup / Babuška–Brezzi condition).** `InfSupCondition a UN VN α₀ ↔
∀ N, α₀ ≤ infSupValue a (UN N) (VN N)` (with `UN N ≠ ⊥`, `VN N ≠ ⊥` to avoid `Real.iInf`/`iSup` junk;
lower bound `0` for the `ciInf` from sign symmetry).
* Classification: **surface-only** (low priority; only the definitional link, no theorem depends on
  (9.2.14)).

### §9.3 Generalized Galerkin method

**Thm 9.3.1 (first Strang lemma), (9.3.1)–(9.3.2).** `‖·‖_N`, `a_N`, `ℓ_N` on `V + V_N`; constants
`M, α₀, c₀ > 0` with `|a_N(w, v_N)| ≤ M‖w‖_N‖v_N‖_N`, `a_N(v_N, v_N) ≥ α₀‖v_N‖_N²`,
`|ℓ_N(v_N)| ≤ c₀‖v_N‖_N` ⇒ (9.3.1) has a unique solution and
`‖u − u_N‖_N ≤ (1 + M/α₀) inf_{w_N∈V_N} ‖u − w_N‖_N + (1/α₀) sup_{v_N∈V_N} |a_N(u,v_N) − ℓ_N(v_N)|/‖v_N‖_N`.
* Lean (abstract `W`, D10):
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
* Backbone (`Numlib/Variational/Galerkin.lean`, section `Strang`):
  `existsUnique_isGeneralizedGalerkinSolution aN ℓN K [FiniteDimensional 𝕜 K] (hc : 0 < c)
  (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v))` (unique solvability by injectivity and
  finite dimension, `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` on
  `K →ₗ Module.Dual 𝕜 K`; no Lax–Milgram) and `strang_first (hc) (hM0 : 0 ≤ M) (hM : ∀ w, ∀ v ∈ K,
  ‖aN w v‖ ≤ M * ‖w‖ * ‖v‖) (hcoer) (hN : IsGeneralizedGalerkinSolution aN ℓN K uN) (u : W)
  (hδ0 : 0 ≤ δ) (hδ : ∀ w ∈ K, ‖aN u w - ℓN w‖ ≤ δ * ‖w‖) (hv : v ∈ K) :
  ‖u - uN‖ ≤ (1 + M / c) * ‖u - v‖ + δ / c` (pointwise, with an explicit consistency bound `δ`;
  both `hM0` and `hδ0` are required for the reason given under Thm 9.2.1 — bounds quantified over a
  subspace are vacuous on the trivial subspace — and both hold for the surface's constants, `δ`
  being a supremum of absolute values).
  Bridge: take `δ := ⨆ v : {v : VN // v ≠ 0}, |aN u v - ℓN v| / ‖v‖`, bounded above by `M‖u‖ + c₀`
  (this is the only use of `hℓ`), so `le_ciSup` gives `hδ`; the `⨅` by `le_ciInf`. The estimate
  itself is the book's four-line computation.
* Classification: **needs-equivalence**.

**Ex 9.3.1.** Conforming case (`V_N ⊂ V`, `a_N = a`, `ℓ_N = ℓ`): the consistency term vanishes and
(9.3.2) becomes `‖u − u_N‖ ≤ (1 + M/α₀) inf ‖u − v‖` (an inequality of the form (9.1.11)).
* Lean: `theorem ex_9_3_1 (W := V) … (hu : ∀ v, a u v = ℓ v) : ‖u - uN‖ ≤ (1 + M / c₀) * ⨅ v : VN, ‖u - v‖`
  (sup term `= 0` by `hu`; `strang_first` with `δ = 0`).
* Classification: **needs-equivalence** (trivial).

### §9.4 Conjugate gradient method: variational formulation

**(9.4.1)–(9.4.3) ⇒ properties of `A`, `f` from (9.4.5)–(9.4.6).** `A` exists (Riesz), `‖A‖ ≤ M`,
`(A u, v) = (u, A v)` (self-adjoint), `(A v, v) ≥ α‖v‖²`; `‖f‖ = ‖ℓ‖`.
* Lean: `norm_toOperator_le : ‖toOperator a hM‖ ≤ M`; `isSelfAdjoint_toOperator (hs : a.IsSymm) :
  IsSelfAdjoint (toOperator a hM)`; `isCoercive_toOperator (ha) : (toOperator a hM : V →ₗ[ℝ] V).IsCoercive`;
  `norm_rieszRep : ‖rieszRep ℓ‖ = ‖ℓ‖`.
* Backbone (`Numlib/Variational/Forms.lean`): `SesqForm.norm_toOperator : ‖toOperator a‖ = ‖a‖` with
  `opNorm_le_of_isBoundedWith`; `isHermitian_iff_toOperator_isSymmetric` with Mathlib's
  `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`; `isCoerciveWith_iff_toOperator`;
  `SesqForm.norm_rieszRep`.
* Classification: **direct** / **needs-equivalence** (through D4).

**(9.4.7) ⇔ (9.4.4).** `A u = f ↔ ∀ v, a(u,v) = ℓ(v)`.
* Lean: `theorem toOperator_eq_rieszRep_iff : toOperator a hM u = rieszRep ℓ ↔ ∀ v, a u v = ℓ v`,
  which is `SesqForm.forall_apply_eq_iff_toOperator_eq` read backwards;
  `IsGalerkinSolution.iff_isGalerkin` with `K = ⊤` is the same statement in Galerkin form.
* Classification: **direct**.

**Algorithm 1 = backbone CG.** See D11: `cgIterate_eq`.
* Consequences transported from `Numlib/Krylov/CG.lean` (§3.7) and
  `Numlib/LinearSolve/Projection/Optimality.lean` (§2.4.2): `CG.isGalerkinIterate` (`u_k` is the
  Galerkin solution on `u_0 + 𝒦_k(A, r_0)`), `CG.inner_residual_eq_zero` (residual orthogonality),
  `CG.inner_apply_direction_eq_zero` (`A`-conjugacy of `s_k`), `CG.energyNorm_error_antitone`,
  and `IsGalerkin.iff_energyNorm_min` / `IsGalerkin.quadratic_le` (`u_k` minimises `E` over
  `u_0 + 𝒦_k`).
* Classification: **needs-equivalence**.

**"Convergence of Algorithm 1 follows from Theorem 5.6.1."** With `m = α`, `M = M` in (5.6.3)
(`√α‖v‖ ≤ ‖v‖_a ≤ √M‖v‖`): `u_k → u` and (5.6.4) `‖u − u_{k+1}‖_a ≤ (M − α)/(M + α) ‖u − u_k‖_a`,
(5.6.5) `‖u − u_k‖_a ≤ 2((√M − √α)/(√M + √α))^k ‖u − u_0‖_a`.
* Lean: `theorem cg_converges … : Tendsto (fun k => (cgIterate a hM ℓ u₀ k).x) atTop (𝓝 u)`,
  `theorem cg_energy_rate … : energyNorm a (u - (cgIterate a hM ℓ u₀ (k+1)).x) ≤ (M - α) / (M + α) * energyNorm a (u - (cgIterate a hM ℓ u₀ k).x)`,
  `theorem cg_energy_bound … : energyNorm a (u - (cgIterate a hM ℓ u₀ k).x) ≤ 2 * ((√M - √α)/(√M + √α)) ^ k * energyNorm a (u - u₀)`.
* Route: transport Thm 5.6.1 from `Ch05/ConjugateGradient.lean`
  (`plans/surface/AtkinsonHan-Ch5.md`) via `cgIterate_eq`, `energyNorm_eq` (D6) and
  `(toOperator a hM : V →ₗ[ℝ] V).IsSymmetricBoundedBy α M` (from symmetry, ellipticity and `hM`
  through `inner_toOperator`). The backbone supplies (5.6.5) in any inner product space as
  `Krylov.IsGalerkinIterate.energyNorm_error_le` (`Numlib/Krylov/Convergence/CG.lean`, §3.10,
  hypothesis `LinearMap.IsSymmetricBoundedBy lmin lmax`; proved through the compression of `A` to
  the Krylov space, §2.1.6) together with `CG.isGalerkinIterate`; the one-step bound (5.6.4)
  follows from `IsGalerkin.energyNorm_le` (§2.4.2; `u_k + t r_k ∈ u_0 + 𝒦_{k+1}` for every `t`)
  and the polynomial bound `LinearMap.IsSymmetricBoundedBy.energyNorm_aeval_map_apply_le`
  (`Numlib/Krylov/Convergence/Polynomial.lean`, §3.9) with `p = 1 − 2X/(M + α)`, whose sup over
  `[α, M]` is `(M − α)/(M + α)`. Convergence: (5.6.5), `(√M − √α)/(√M + √α) < 1`, and
  `√α ‖v‖ ≤ ‖v‖_a` (`sqrt_mul_norm_le_energyNorm`).
* Classification: **needs-equivalence**.

**Energy functional and its Gâteaux derivative (§9.4).** `⟨E'(u), v⟩ = a(u,v) − ℓ(v)`; hence
`(r_k, v) = −⟨E'(u_k), v⟩`, and (9.4.4) ⇔ `E(u) = inf_V E`.
* Lean: `theorem hasFDerivAt_energy (hM) (hs : a.IsSymm) (ℓ) (u) :
  HasFDerivAt (fun v => (1/2 : ℝ) * a v v - ℓ v) (a.toCLM hM u - ℓ) u` (Fréchet ⇒ Gâteaux);
  `theorem residual_eq_neg_rieszRep_fderiv : residual a hM ℓ u = -SesqForm.rieszRep (a.toCLM hM u - ℓ)`;
  `energy_isMinOn_iff` = (9.1.6) case of Thm 8.3.3 (`SesqForm.isMinOn_energy_iff` with `K = ⊤`).
* Mathlib: `IsBoundedBilinearMap.hasFDerivAt` (`Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean`)
  composed with `hasFDerivAt_id.prodMk hasFDerivAt_id`, symmetry to merge the two terms,
  `ContinuousLinearMap.hasFDerivAt`.
* Classification: **surface-only** (derivative) / **needs-equivalence** (minimisation).

**Algorithm 2 (nonlinear CG) and its convergence (`J` coercive `C¹`, `J'` Lipschitz and strongly
monotone on bounded sets, [92]).** Classification: **out-of-scope** (quoted without proof; see §6).

## 4. Backbone dependencies

All backbone declarations used above, by module (section numbers refer to `plans/backbone.md`):

| Module | Declarations |
|---|---|
| `Numlib/Variational/Forms.lean` (§5.2.1) | `SesqForm`, `IsBoundedWith`, `IsCoerciveWith`, `IsHermitian`, `isBoundedWith_opNorm`, `opNorm_le_of_isBoundedWith`, `IsCoerciveWith.norm_le_norm_apply`, `isCoerciveWith_real_iff`, `isHermitian_real_iff`, `innerSL_isCoerciveWith`, `innerSL_isHermitian`, `toOperator`, `inner_toOperator`, `rieszRep`, `inner_rieszRep`, `norm_rieszRep`, `ofOperator`, `isCoerciveWith_iff_toOperator`, `isHermitian_iff_toOperator_isSymmetric`, `norm_toOperator`, `forall_apply_eq_iff_toOperator_eq`, `energy`, `energyNorm`, `energyNorm_eq_energyNorm_toOperator`, `sqrt_mul_norm_le_energyNorm`, `energyNorm_le_sqrt_mul_norm`; `SesqForm₂`, `InfSupWith`, `IsNondegenerate`, `iSup_norm_div_eq_norm`, `SesqForm.IsCoerciveWith.infSupWith` |
| `Numlib/Variational/LaxMilgram.lean` (§5.2.2) | `SesqForm.laxMilgram`, `norm_le_of_forall_apply_eq`, `norm_sub_le_of_forall_apply_eq`, `exists_solutionEquiv`, `contractingWith_damped_toOperator`, `isMinOn_energy_iff`, `isMinOn_energy_iff_forall_le`, `existsUnique_isMinOn_energy`, `energy_sub_energy_eq`; `SesqForm₂.babuska_necas`, `norm_le_of_infSupWith`, `infSupWith_of_forall_exists`; `ContinuousLinearMap.isClosed_range_of_le_norm`, `bijective_of_le_norm_of_orthogonal_range_eq_bot`, `norm_le_of_le_norm`, `LinearPMap.isClosed_range_of_isClosed_of_le_norm` |
| `Numlib/Variational/Galerkin.lean` (§5.2.3) | `IsGalerkinSolution` with `iff_isGalerkin`, `existsUnique`, `apply_sub_eq_zero`, `norm_sub_le`, `norm_sub_le_infDist`, `energyNorm_sub_le`, `norm_sub_le_sqrt`, `iff_mulVec`, `tendsto`; `tendsto_infDist_of_monotone_dense`; `IsPetrovGalerkinSolution` with `DiscreteInfSup`, `existsUnique`, `norm_sub_le`, `tendsto`; `isGalerkinSolution_iff_isPetrovGalerkinSolution`; `IsGeneralizedGalerkinSolution`, `strang_first`, `existsUnique_isGeneralizedGalerkinSolution` |
| `Numlib/Analysis/InnerProductSpace/Coercive.lean` (§2.1.4) | `LinearMap.IsCoerciveWith`, `IsCoercive`, `IsSymmetricCoercive`, `IsSymmetricBoundedBy`, `isCoercive_iff_forall_pos`, `ContinuousLinearMap.norm_sub_smul_apply_sq_le`, `Matrix.posDef_iff_isSymmetricCoercive` |
| `Numlib/Analysis/InnerProductSpace/Energy.lean` (§2.1.5) | `energyInner`, `energyNorm`, `WithEnergy`, `LinearMap.IsCoerciveWith.norm_le_energyNorm` |
| `Numlib/Analysis/InnerProductSpace/Projection/ObliqueProjection.lean` (§2.1.7) | `ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq` (Kato) |
| `Numlib/Nonlinear/FixedPoint.lean` (§5.3.1) | `zarantonello`, `contractingWith_damped` |
| `Numlib/LinearSolve/Projection/Basic.lean`, `Optimality.lean` (§2.4.1–2.4.2) | `IsGalerkin`, `isPetrovGalerkin_iff_mulVec`, `IsGalerkin.energyNorm_le`, `iff_energyNorm_min`, `quadratic_le`, `error_eq_starProjection` |
| `Numlib/Krylov/CG.lean` (§3.7) | `CG.State`, `alpha`, `step`, `step_r`, `init`, `iterate`, `residual_eq`, `iterate_eq_of_residual_eq_zero`, `isGalerkinIterate`, `inner_residual_eq_zero`, `inner_apply_direction_eq_zero`, `energyNorm_error_antitone` |
| `Numlib/Krylov/Convergence/Polynomial.lean`, `CG.lean` (§3.9–3.10) | `LinearMap.IsSymmetricBoundedBy.energyNorm_aeval_map_apply_le`, `Krylov.IsGalerkinIterate.energyNorm_error_le` |

Surface bridging lemmas (all in §2): `isClosed_iff_seq`, `stabilityEstimate_iff_antilipschitz`,
`isBoundedWith_iff_toCLM`, `isElliptic_iff_isCoercive`, `isEllipticWith_iff_isCoerciveWith`,
`energy_eq`, `energyNorm_eq`, `galerkinProblem_iff`, `petrovGalerkinProblem_iff`,
`iSup_div_eq_iSup_abs_div`, `iSup_abs_div_eq_opNorm`, `infSup_iff_infSupWith`, `discreteInfSup_iff`,
`DiscreteInfSup.mono`, `cgIterate_eq`, and the helper `isMinOn_iff_eq_ciInf`.

## 5. Deferred backbone items

* **Xu–Zikatanov sharpening of Babuška's bound** (Rem 9.2.2, (9.2.10)): `‖u − u_N‖ ≤ (M/α_N)
  inf_{w_N ∈ U_N} ‖u − w_N‖`, obtained from Kato's lemma applied to the Petrov–Galerkin projector
  `P_N : u ↦ u_N` (bounded idempotent with `‖P_N‖ ≤ M/α_N`, `range = U_N`); `plans/backbone.md`
  §5.2.3, phase 2 (§7). Kato's lemma itself is in `Numlib/Analysis/InnerProductSpace/Projection/ObliqueProjection.lean`;
  the deferred part is the projector construction and the sharpened Galerkin estimate.

## 6. Left out

Out of scope for lack of Sobolev spaces in Mathlib (no phase of `plans/backbone.md` §7 schedules
them):
* §8.1 model problem (8.1.1)–(8.1.4), Ex 8.2.3, Ex 8.2.6, Ex 8.3.5, Ex 8.7.2, Examples 9.1.1–9.1.2,
  Table 9.1, Ex 9.1.3: need `H¹₀(Ω)`, `H⁻¹(Ω)`, `L²`, weak derivatives, Green's kernels.
* §8.4 (weak formulations with Dirichlet/Neumann/mixed/Robin conditions, general second-order elliptic
  operators, Lemma 8.4.1 quotient Poincaré inequality): Sobolev spaces, traces, Poincaré/Friedrichs.
* §8.5 (linearized elasticity, Thm 8.5.1): Korn's inequality and tensor-valued Sobolev spaces.
* §8.6 (mixed and dual formulations, Def 8.6.1, Prop 8.6.2, Thm 8.6.3 Ekeland–Temam saddle points,
  Brezzi framework (8.6.21)–(8.6.22)): convex analysis in reflexive Banach spaces, `H(div)`.
* §8.8 (Lemmas 8.8.1–8.8.4, Thm 8.8.5, `p`-Laplacian-type problem): `W^{1,p}₀`, reflexivity, Gâteaux
  derivatives of integral functionals, Thm 3.3.12/5.3.19.

Out of scope for other reasons:
* Thm 8.2.7 in its Banach generality (closed range theorem): Mathlib has no Banach dual of
  unbounded densely defined operators (D3); the Hilbert bounded case is recorded as
  `thm_8_2_7_hilbert` (§3).
* Ex 8.2.1 (finite-dimensional exercise), Ex 9.1.4 (Galerkin as an existence proof via weak
  compactness — needs weak sequential compactness of bounded sets, not cited by any theorem).
* Algorithm 2 (nonlinear CG for strictly convex `J`) and its convergence claim from [92]: no proof in
  the book; the line search `α_k` is an argmin that need not exist in general.

Placed elsewhere:
* Thm 5.6.1/5.6.2 themselves belong to `Ch05/ConjugateGradient.lean`
  (`plans/surface/AtkinsonHan-Ch5.md`; Winther's superlinear rate 5.6.2 is a later phase); §9.4
  only transports them through `cgIterate_eq`.

## 7. Reading notes on the book text

* Thm 8.2.4 proof: "`‖v_n − v_m‖ ≤ c ‖f_n − f_m‖`" should read `c⁻¹` (book typo).
* Thm 8.3.1 dictionary bullet 1: "`a(u,v) ≤ M‖u‖‖v‖`" without absolute value — book shorthand;
  formalised with `|·|`.
* (8.7.3), (9.2.4): "`sup_{u∈U} a(u,v) > 0`" — as printed; the sup of a nonzero linear functional is
  `+∞`, so it is formalised as `∃ u, 0 < a u v` (equivalently `∃ u, a u v ≠ 0`, the backbone's
  `SesqForm₂.IsNondegenerate`).
* Thm 9.2.1 proof: "for any `w_N ∈ V_N`" should be `w_N ∈ U_N` (book typo).
* (9.3.2): the sup is over `v_N ∈ V_N` without `v_N ≠ 0` (book); formalised over `v_N ≠ 0`.
* Cor 9.1.4 indexes subspaces `V_n`, §9.1 text `V_{N_i}`, Cor 9.2.3 `U_{N_i}`; all formalised as
  `ℕ`-indexed monotone families.
* Thm 8.2.1's proof cites Thm 3.3.7 (Hahn–Banach separation); the Lean proof uses orthogonal
  projections instead — the statement is identical.
