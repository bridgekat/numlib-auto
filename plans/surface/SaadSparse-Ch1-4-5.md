# Surface plan: Saad, Iterative Methods — §1.11–1.13, §4.1–4.2, Ch. 5

Surface library `SaadSparse` (Lake lib, `srcDir = "Surface"`, imports only `Numlib`) for the second
edition of Saad, *Iterative Methods for Sparse Linear Systems*, sections §1.11 (positive-definite
matrices), §1.12 (projectors), §1.13 (linear systems, conditioning), §4.1 (Jacobi/GS/SOR/SSOR,
block variants), §4.2 (convergence: Thm 4.1–4.16) and Ch. 5 (projection methods, Prop 5.1–Thm 5.10,
§5.4). Statements are kept in the book's generality — real `n × n` matrices in Ch. 4–5 and §1.11
(Thm 1.35 complex), complex in §1.12, `RCLike 𝕜` in §1.13 — with the book's own definitions
(Saad's non-symmetric "positive definite", projectors given by bases `V, W`, the splitting
`A = D − E − F`, matrix `p`-norms). Every proof is a specialization of a backbone item (a
declaration under `Numlib/`, cited with its module; design rationale in `plans/backbone.md`, cited
by section number) through an equivalence lemma for the book-specific definition. §1 lists the
definitions and their equivalences, §2 the results, §3 the backbone items deferred to later phases,
§4 what is left out, §5 how ambiguous book statements are read.

Conventions (shared file `Surface/SaadSparse/Basic.lean`):
* `n : ℕ`; vectors of ℝⁿ/ℂⁿ are `EuclideanSpace 𝕜 (Fin n)` (Mathlib's ℝⁿ with the Euclidean norm),
  abbreviated `E𝕜 n`; matrices `Matrix (Fin n) (Fin n) 𝕜`; the action `A x` is `toEuclideanLin A x`
  (local notation `A ⬝ x`); componentwise statements use `Fin n → 𝕜`, `A *ᵥ x`, `x ⬝ᵥ y`, and the
  glue `toEuclideanLin A x = WithLp.toLp 2 (A *ᵥ x.ofLp)` (`rfl`). The backbone's own glue is
  `Numlib/Matrix/ToEuclideanLin.lean` (`toEuclideanLin_mul/pow/conjTranspose`,
  `hasEigenvalue_toEuclideanLin_iff`, `toEuclideanLin_apply_eq_sum`,
  `l2_opNorm_eq_norm_toEuclideanLin`).
* Saad's inner product `(x, y) = Σ x_i ȳ_i` is `inner 𝕜 y x` (Mathlib's is conjugate-linear in the
  first slot); over ℝ they coincide, and every complex statement below is written so that only
  `re`, `‖·‖` or `⟪·,·⟫ = 0` matters.
* `λ_min(H)`, `λ_max(H)` for Hermitian `H` are `Finset.univ.inf'/sup' _ hH.eigenvalues`
  (`Matrix.IsHermitian.eigenvalues`), so `[Nonempty (Fin n)]` (`n ≥ 1`) appears where the book
  uses them. They are the `lmin`, `lmax` of the backbone's quadratic-form hypothesis
  `LinearMap.IsSymmetricBoundedBy` through `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`
  (`Numlib/Matrix/ToEuclideanLin.lean`; its hypothesis `∀ i, eigenvalues i ∈ Icc lmin lmax` is
  trivial for the extremes).
* Real matrices as complex ones: `Matrix.complexify` and `Matrix.complexSpectralRadius`
  (`Numlib/Matrix/Complexify.lean`); `Basic.lean` adds the glue `complexify_sub`,
  `complexify_diagPart/strictLower/strictUpper/inv` (`Matrix.map` of a ring hom) and
  `norm_complexify_mulVec : ‖complexify A *ᵥ (ofReal ∘ x)‖ = ‖A *ᵥ x‖`.
* Names: `SaadSparse.Ch01.thm_1_34`, `SaadSparse.Ch05.prop_5_3`, `eq_1_76`, …, plus descriptive
  aliases; docstrings carry the book statement verbatim.

Proposed files:

| File | Book |
|---|---|
| `Surface/SaadSparse/Basic.lean` | conventions, notation, glue lemmas (`toEuclideanLin`, `dotProduct`, `complexify`) |
| `Surface/SaadSparse/Ch01/PositiveDefinite.lean` | §1.11: (1.48)–(1.57), Thm 1.34, Thm 1.35 |
| `Surface/SaadSparse/Ch01/Projectors.lean` | §1.12: (1.58)–(1.72), Lemma 1.36, Prop 1.37, Thm 1.38, Cor 1.39 |
| `Surface/SaadSparse/Ch01/LinearSystems.lean` | §1.13: existence cases, (1.74)–(1.76), `κ`, `κ_p`, residual–error relation, Example 1.5 |
| `Surface/SaadSparse/Ch04/Splittings.lean` | §4.1: (4.2)–(4.27), Alg 4.1–4.2 as functions |
| `Surface/SaadSparse/Ch04/Convergence.lean` | §4.2–4.2.2: (4.29)–(4.30), Thm 4.1, Cor 4.2, convergence factors, Ex 4.1, Def 4.3, Thm 4.4 |
| `Surface/SaadSparse/Ch04/DiagDominant.lean` | §4.2.3: Def 4.5, Thm 4.6–4.9, Cor 4.8 |
| `Surface/SaadSparse/Ch04/SPD.lean` | §4.2.4–4.2.5: Thm 4.10, Def 4.11–4.13, Prop 4.12–4.15, Thm 4.16, (4.47) |
| `Surface/SaadSparse/Ch05/Projection.lean` | §5.1–5.2: (5.2)–(5.11), Prop 5.1–5.6, Thm 5.7 |
| `Surface/SaadSparse/Ch05/OneDimensional.lean` | §5.3: (5.12)–(5.21), Alg 5.2–5.4, Lemma 5.8, Thm 5.9–5.10 |
| `Surface/SaadSparse/Ch05/Additive.lean` | §5.4: (5.22)–(5.23), Alg 5.5–5.6 |

## 1. Book-specific definitions

Each entry: book formulation; proposed Lean surface definition; backbone counterpart (module under
`Numlib/`, or `plans/backbone.md` section for phase-2 material); equivalence lemma.

**D1. Positive definite / positive real (1.48).** Real `A` with `(Au, u) > 0 ∀ u ∈ ℝⁿ, u ≠ 0`
(no symmetry). SPD = symmetric + (1.48); HPD = Hermitian + `(Au,u) > 0` on ℂⁿ.
```lean
def Matrix.IsPositiveReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u : Fin n → ℝ, u ≠ 0 → 0 < (A *ᵥ u) ⬝ᵥ u
abbrev Matrix.IsSPD (A : Matrix (Fin n) (Fin n) ℝ) : Prop := A.IsSymm ∧ A.IsPositiveReal
```
Backbone: `LinearMap.IsCoercive`, `LinearMap.IsCoerciveWith`, `LinearMap.IsSymmetricCoercive`,
`Matrix.posDef_iff_isSymmetricCoercive` (`Numlib/InnerProductSpace/Coercive.lean`); Mathlib
`Matrix.PosDef`. Equivalences: `isPositiveReal_iff_isCoercive : A.IsPositiveReal ↔
(toEuclideanLin A).IsCoercive` (via `LinearMap.isCoercive_iff_forall_pos` and the glue
`inner ℝ x (A ⬝ x) = (A *ᵥ x) ⬝ᵥ x`); `isSPD_iff_posDef : A.IsSPD ↔ A.PosDef` (Mathlib
`posDef_iff_dotProduct_mulVec`, `star` trivial on ℝ); `isHPD_iff_posDef` for the complex Hermitian
case (`re (star u ⬝ᵥ A *ᵥ u) > 0` ↔ Mathlib's `ComplexOrder` positivity).

**D2. Hermitian and skew-Hermitian parts (1.49)–(1.51).** `H = (A + Aᴴ)/2`, `S = (A − Aᴴ)/(2i)`,
`A = H + iS`.
```lean
def Matrix.hermitianPart (A : Matrix (Fin n) (Fin n) 𝕜) := (2⁻¹ : 𝕜) • (A + Aᴴ)
noncomputable def Matrix.skewPart (A : Matrix (Fin n) (Fin n) ℂ) := (2 * Complex.I)⁻¹ • (A - Aᴴ)
```
(`skewPart` only over ℂ: over ℝ `1/(2i)` is junk; the skew-Hermitian part `(A − Aᴴ)/2` is defined
over `𝕜`.) Backbone/Mathlib: `selfAdjointPart 𝕜`, `skewAdjointPart 𝕜` (`Mathlib/Algebra/Star/Module`)
with `⅟2`; the operator form `(2⁻¹ : 𝕜) • (A + adjoint A)` of
`ContinuousLinearMap.re_inner_hermitianPart_apply` and `isCoerciveWith_iff_hermitianPart`
(`Numlib/InnerProductSpace/Coercive.lean`), reached through `Matrix.toEuclideanLin_conjTranspose`
(`Numlib/Matrix/ToEuclideanLin.lean`). Equivalence:
`hermitianPart_eq_selfAdjointPart : A.hermitianPart = (selfAdjointPart 𝕜 A : Matrix _ _ 𝕜)`;
`toEuclideanLin_hermitianPart : toEuclideanLin A.hermitianPart = (2⁻¹ : 𝕜) • (toEuclideanLin A +
adjoint (toEuclideanLin A))`; `hermitianPart_isHermitian`, `skewPart_isHermitian`,
`eq_hermitianPart_add_I_smul_skewPart` (1.49). The surface `λ_min (hermitianPart_isHermitian A)` is
the `lmin` of `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin` applied to `H`, and the best
coercivity constant of `A` (`ContinuousLinearMap.isCoerciveWith_iff_hermitianPart`).

**D3. Energy (`B`-) inner product (1.57), `B`-self-adjointness.** For SPD/HPD `B`,
`(x, y)_B := (Bx, y)`; "`A` is Hermitian w.r.t. `(·,·)_B`" iff `(Ax, y)_B = (x, Ay)_B ∀ x y`.
```lean
def Matrix.energyInner (B : Matrix (Fin n) (Fin n) 𝕜) (x y : E𝕜 n) : 𝕜 := inner 𝕜 y (B ⬝ x)
def Matrix.IsSelfAdjointWrt (B A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ x y, B.energyInner (A ⬝ x) y = B.energyInner x (A ⬝ y)
```
Backbone: `energyInner`, `energyNorm`, `WithEnergy A hA` with its `InnerProductSpace` instance
`WithEnergy.instInnerProductSpace`, `WithEnergy.equiv`, `inner_equiv`, `norm_equiv`
(`Numlib/InnerProductSpace/Energy.lean`). Equivalence:
`energyInner_eq : B.energyInner x y = starRingEnd 𝕜 (energyInner (toEuclideanLin B) x y)` (equal
over ℝ); "(1.57) is a proper inner product" is the `InnerProductSpace 𝕜 (WithEnergy _ hB)` instance,
transported through `Matrix.posDef_iff_isSymmetricCoercive`.

**D4. Projector, range and null space (§1.12.1).** A projector is an idempotent linear map of ℂⁿ.
```lean
abbrev Matrix.IsProjector (P : Matrix (Fin n) (Fin n) ℂ) : Prop := IsIdempotentElem P   -- P * P = P
-- Ran P := LinearMap.range (toEuclideanLin P), Null P := LinearMap.ker (toEuclideanLin P)
```
Backbone/Mathlib: `IsIdempotentElem`, `LinearMap.IsProj`, `IsIdempotentElem.isCompl`,
`IsIdempotentElem.eq_projection`, `Submodule.projection` (`Mathlib/LinearAlgebra/Projection`).
Equivalence: `isProjector_iff_isIdempotentElem_toEuclideanLin` (`toEuclideanLin` is an algebra
equivalence, `Matrix.toEuclideanCLM`).

**D5. Projector onto `M` orthogonal to `L` (1.59)–(1.60).** `u = Px` iff `u ∈ M` and `x − u ⟂ L`.
```lean
def IsProjOnto (M L : Submodule 𝕜 (E𝕜 n)) (x u : E𝕜 n) : Prop := u ∈ M ∧ x - u ∈ Lᗮ
/-- The projector onto `M` orthogonal to `L` (the unique idempotent with range `M`, kernel `Lᗮ`). -/
noncomputable def obliqueProjection (M L : Submodule 𝕜 (E𝕜 n)) (hd : finrank 𝕜 M = finrank 𝕜 L)
    (h : M ⊓ Lᗮ = ⊥) : E𝕜 n →ₗ[𝕜] E𝕜 n :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot hd h).exists.choose
```
Backbone (`Numlib/InnerProductSpace/ObliqueProjection.lean`):
`LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot (hdim) (hKL : K ⊓ Lᗮ = ⊥) :
∃! P, IsIdempotentElem P ∧ range P = K ∧ ker P = Lᗮ` (finite-dimensional `K, L` of equal
dimension), the characterization `LinearMap.IsIdempotentElem.apply_eq_iff (hP) (hr : range P = K)
(hk : ker P = Lᗮ) (x y) : P x = y ↔ y ∈ K ∧ x - y ∈ Lᗮ`, and uniqueness
`IsIdempotentElem.ext_of_range_eq_of_ker_eq`. Equivalence: `isProjOnto_iff_eq_obliqueProjection :
IsProjOnto M L x u ↔ u = obliqueProjection M L hd h x` is `apply_eq_iff` for the chosen projector
(`obliqueProjection_spec`). Orthogonal projector = the case `L = M`:
`IsProjOnto M M x u ↔ u = M.starProjection x` (Mathlib `eq_starProjection_of_mem_orthogonal`).

**D6. Bases and matrix representation (1.63)–(1.66).** `V = [v₁,…,v_m]` basis of `M`,
`W` basis of `L`; biorthogonal iff `WᴴV = I`; `P = VWᴴ` (1.65), in general `P = V(WᴴV)⁻¹Wᴴ` (1.66).
```lean
/-- The columns of `V` as vectors of `E𝕜 n`. -/
def Matrix.cols (V : Matrix (Fin n) (Fin m) 𝕜) : Fin m → E𝕜 n := fun j => WithLp.toLp 2 (Vᵀ j)
structure Matrix.IsBasisOf (V : Matrix (Fin n) (Fin m) 𝕜) (M : Submodule 𝕜 (E𝕜 n)) : Prop where
  linearIndependent : LinearIndependent 𝕜 V.cols
  span_eq : Submodule.span 𝕜 (Set.range V.cols) = M
def IsBiorthogonal (V W : Matrix (Fin n) (Fin m) 𝕜) : Prop := Wᴴ * V = 1
noncomputable def obliqueProj (V W : Matrix (Fin n) (Fin m) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  V * (Wᴴ * V)⁻¹ * Wᴴ
```
`hV.toBasis : Module.Basis (Fin m) 𝕜 M` (`Basis.mk`) is how bases reach backbone statements
phrased with `Module.Basis`. Backbone (`Numlib/InnerProductSpace/ObliqueProjection.lean`): the
cross-Gram matrix `LinearMap.crossGram 𝕜 V W : Matrix ι ι 𝕜` (entries `⟪W i, V j⟫`) and the
projector from families `LinearMap.obliqueProjectionOfBases 𝕜 V W : E →ₗ[𝕜] E`
(`x ↦ Σ_j ((crossGram 𝕜 V W)⁻¹ *ᵥ (fun i => ⟪W i, x⟫)) j • V j`), with, under
`hVW : IsUnit (crossGram 𝕜 V W)`: `obliqueProjectionOfBases_isIdempotentElem`,
`range_obliqueProjectionOfBases` (`= span (range V)`), `ker_obliqueProjectionOfBases`
(`= (span (range W))ᗮ`), `sub_obliqueProjectionOfBases_apply_mem_orthogonal`; and
`obliqueProjectionOfBases_self_eq_starProjection (hV : Orthonormal 𝕜 V)`. Equivalences:
`crossGram_cols : crossGram 𝕜 V.cols W.cols = Wᴴ * V` (entrywise, `EuclideanSpace.inner_eq_star_dotProduct`);
`toEuclideanLin_obliqueProj : toEuclideanLin (obliqueProj V W) = obliqueProjectionOfBases 𝕜 V.cols W.cols`
(both sides are `x ↦ Σ_j ((Wᴴ V)⁻¹ (Wᴴ x))_j • v_j`, by `Matrix.toEuclideanLin_apply_eq_sum`);
`isUnit_conjTranspose_mul_iff (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) : IsUnit (Wᴴ * V) ↔
∀ v ∈ M, v ∈ Lᗮ → v = 0` (surface: `Wᴴ *ᵥ z = 0 ↔ z ∈ Lᗮ` and `y ↦ V y` is injective with
image `M`); hence `toEuclideanLin (obliqueProj V W) = obliqueProjection M L hd h` by
`IsIdempotentElem.ext_of_range_eq_of_ker_eq`. Orthonormal case: `Vᴴ * V = 1 ↔ Orthonormal 𝕜 V.cols`
(`orthonormal_iff_ite`), `obliqueProj V V = V * Vᴴ`, and
`toEuclideanLin (V * Vᴴ) = M.starProjection` (`obliqueProjectionOfBases_self_eq_starProjection`).

**D7. Orthogonal projector (1.67).** `Null P = (Ran P)ᗮ`; equivalently `Px ∈ M ∧ (I − P)x ⟂ M`.
```lean
def Matrix.IsOrthogonalProjector (P : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  IsIdempotentElem P ∧ LinearMap.ker (toEuclideanLin P) = (LinearMap.range (toEuclideanLin P))ᗮ
```
Backbone/Mathlib: `Submodule.starProjection`, `LinearMap.IsSymmetricProjection`,
`IsIdempotentElem.isSymmetric_iff_orthogonal_range` (`Mathlib/Analysis/InnerProductSpace/Symmetric`).
Equivalence: `isOrthogonalProjector_iff_eq_starProjection : P.IsOrthogonalProjector ↔
toEuclideanLin P = (range (toEuclideanLin P)).starProjection` and
`↔ (toEuclideanLin P).IsSymmetricProjection`.

**D8. Condition number, matrix `p`-norms (§1.13.2).** `κ(A) = ‖A‖‖A⁻¹‖` w.r.t. a matrix norm;
`κ_p(A) = ‖A‖_p ‖A⁻¹‖_p` for the norms induced by the vector `p`-norms.
```lean
/-- `‖A‖_p`: operator norm of `x ↦ A x` on `PiLp p (fun _ : Fin n => 𝕜)`. -/
noncomputable def Matrix.lpOpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (toLpLin p p A)‖
noncomputable def Matrix.condNumberLp (p) [Fact (1 ≤ p)] (A) : ℝ := lpOpNorm p A * lpOpNorm p A⁻¹
```
Backbone: `NormedRing.condNumber` (`‖a‖ ‖Ring.inverse a‖`, scoped notation `κ`),
`ContinuousLinearEquiv.condNumber_eq` (`Numlib/Analysis/NormedRing/CondNumber.lean`), scoped
`Matrix.Norms.L2Operator` (`κ₂`) and `Matrix.Norms.Operator` (`κ_∞`); the perturbation bounds of
`Numlib/LinearSolve/Perturbation.lean` on `E ≃L[𝕜] E`. Mathlib `Matrix.toLpLin p q`,
`Matrix.toLpLinAlgEquiv` (`Mathlib/Analysis/Normed/Lp/Matrix`). Equivalences:
`lpOpNorm_two : lpOpNorm 2 A = ‖A‖` (scoped `L2Operator`; `Matrix.l2_opNorm_def`),
`lpOpNorm_top : lpOpNorm ⊤ A = ‖A‖` (scoped `Operator`; `linfty_opNorm_eq_opNorm`),
`lpOpNorm_one_eq_transpose : lpOpNorm 1 A = lpOpNorm ⊤ Aᵀ` (surface),
`toLpEquiv (hA : IsUnit A) : PiLp p _ ≃L[𝕜] PiLp p _` (the equivalence with
`(toLpEquiv hA : _ →L _) = toContinuousLinearMap (toLpLin p p A)`), and
`condNumberLp_eq_condNumber : condNumberLp p A = NormedRing.condNumber (toContinuousLinearMap (toLpLin p p A))`
(`Matrix.nonsing_inv_eq_ringInverse`, `ContinuousLinearEquiv.condNumber_eq`).

**D9. The splitting `A = D − E − F` (4.2) and the point relaxations (4.4)–(4.9).** `D` diagonal,
`−E` strict lower, `−F` strict upper part; diagonal entries nonzero.
```lean
def D (A : Matrix (Fin n) (Fin n) ℝ) := Matrix.diagPart A      -- `Numlib/Matrix/Hessenberg.lean`
def E (A) := -Matrix.strictLower A
def F (A) := -Matrix.strictUpper A
/-- (4.4) componentwise Jacobi step. -/
def jacobiStep (A) (b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i
/-- (4.8); the componentwise form (4.7) is a theorem about it (it is recursive in `i`). -/
noncomputable def gsStep (A) (b x) : Fin n → ℝ := (D A - E A)⁻¹ *ᵥ (F A *ᵥ x + b)
noncomputable def backwardGsStep (A) (b x) := (D A - F A)⁻¹ *ᵥ (E A *ᵥ x + b)             -- (4.9)
noncomputable def symmetricGsStep (A) (b) := backwardGsStep A b ∘ gsStep A b
```
Backbone: `Matrix.diagPart/strictLower/strictUpper` and
`Matrix.diagPart_sub_neg_strictLower_sub_neg_strictUpper : D − (−L) − (−U) = A`
(`Numlib/Matrix/Hessenberg.lean`); `Matrix.isUnit_diagPart_iff : IsUnit (diagPart A) ↔ ∀ i, A i i ≠ 0`,
`Matrix.jacobiSplitting A h`, `gaussSeidelSplitting A h`, `backwardGaussSeidelSplitting A h`
(all with `h : IsUnit (diagPart A)`; `m = D`, `D + strictLower = D − E`, `D + strictUpper = D − F`),
`jacobiSplitting_iterationOperator`, `gaussSeidelSplitting_n`
(`Numlib/LinearSolve/Stationary/Splitting.lean`); `Stationary.step G f x = G x + f`
(`Numlib/LinearSolve/Stationary/Basic.lean`). Equivalences (with `Splitting.step` of D10):
`jacobiStep_eq (h) : jacobiStep A b = (jacobiSplitting A h).step b` (as maps on `Fin n → ℝ`, i.e.
(4.4) = (4.5)); `gsStep_eq : gsStep A b = (gaussSeidelSplitting A h).step b`;
`backwardGsStep_eq : backwardGsStep A b = (backwardGaussSeidelSplitting A h).step b`;
`decomp : A = D A - E A - F A` (4.2) is `diagPart_sub_neg_strictLower_sub_neg_strictUpper`.

**D10. General splitting and iteration matrix (4.10)–(4.11), (4.18)–(4.23).** `A = M − N`, `M`
nonsingular; `x_{k+1} = M⁻¹N x_k + M⁻¹ b`; `G = M⁻¹N = I − M⁻¹A`, `f = M⁻¹b`; `M` is the
preconditioner, `M⁻¹Ax = M⁻¹b` the preconditioned system.
```lean
/-- `Stationary.Splitting A` has fields `m`, `isUnit`; `n := m - A`,
`iterationOperator := 1 - Ring.inverse m * A` are derived. -/
abbrev Splitting (A : Matrix (Fin n) (Fin n) ℝ) := Stationary.Splitting A
def affineStep (G : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) := G *ᵥ x + f   -- (4.18)/(4.28)
noncomputable def Splitting.step (s : Splitting A) (b) : (Fin n → ℝ) → (Fin n → ℝ) :=
  affineStep s.iterationOperator (s.m⁻¹ *ᵥ b)                                    -- (4.22)
```
Backbone: `Stationary.Splitting`, `Splitting.n`, `m_sub_n`, `iterationOperator`,
`iterationOperator_eq : G = Ring.inverse m * n`, `one_sub_iterationOperator : 1 − G = Ring.inverse m * A`,
`eq_iterationOperator_mul_add_iff` (consistency in ring form)
(`Numlib/LinearSolve/Stationary/Splitting.lean`); `Stationary.step`, `step_iterate_sub`,
`step_fixed_iff` (`Stationary/Basic.lean`). Equivalences:
`affineStep_eq_step : affineStep G f = Stationary.step (LinearMap.toContinuousLinearMap (Matrix.toLin' G)) f`
on `Fin n → ℝ` (`Matrix.toLin'_apply`; this is how every `Stationary.*` statement reaches the
surface, with `(toLin' G)^k = toLin' (G^k)`); `Matrix.nonsing_inv_eq_ringInverse` for `Ring.inverse`;
`G_JA`, `G_GS` (4.19)–(4.20) are `(jacobiSplitting A h).iterationOperator`,
`(gaussSeidelSplitting A h).iterationOperator` by `one_sub_iterationOperator`.

**D11. SOR and SSOR (4.12)–(4.14), (4.26)–(4.27).** `ωA = (D − ωE) − (ωF + (1−ω)D)`;
SOR: `(D − ωE)x_{k+1} = [ωF + (1−ω)D]x_k + ωb`; relaxation form `ξ_i^{(k+1)} = ω ξ_i^{GS} + (1−ω)ξ_i^{(k)}`;
SSOR = SOR sweep then backward SOR sweep, `G_ω`, `f_ω` (4.13)–(4.14),
`f_ω = ω(2−ω)(D − ωF)⁻¹D(D − ωE)⁻¹b`; `M_SOR = ω⁻¹(D − ωE)`, `M_SSOR = (ω(2−ω))⁻¹(D − ωE)D⁻¹(D − ωF)`.
```lean
noncomputable def sorStep (A) (ω : ℝ) (b x) :=
  (D A - ω • E A)⁻¹ *ᵥ ((ω • F A + (1 - ω) • D A) *ᵥ x + ω • b)
noncomputable def backwardSorStep (A) (ω) (b x) :=
  (D A - ω • F A)⁻¹ *ᵥ ((ω • E A + (1 - ω) • D A) *ᵥ x + ω • b)
noncomputable def ssorStep (A) (ω) (b) := backwardSorStep A ω b ∘ sorStep A ω b
noncomputable def G_ssor (A) (ω) :=
  (D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ * (ω • F A + (1 - ω) • D A)
noncomputable def f_ssor (A) (ω) (b) :=
  ω • (D A - ω • F A)⁻¹ *ᵥ ((1 + (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹) *ᵥ b)
noncomputable def M_sor (A) (ω) := ω⁻¹ • (D A - ω • E A)
noncomputable def M_ssor (A) (ω) := (ω * (2 - ω))⁻¹ • (D A - ω • E A) * (D A)⁻¹ * (D A - ω • F A)
/-- Backward SOR as a splitting: the structure has only `m` and `isUnit`, so any unit `M` gives
one (`n := M − A`). -/
noncomputable def backwardSorSplitting (A) (h : IsUnit (diagPart A)) (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • diagPart A + strictUpper A, _⟩
```
Backbone (`Numlib/LinearSolve/Stationary/Splitting.lean`): `Matrix.sorSplitting A h hω`
(`m = ω⁻¹ • diagPart A + strictLower A`, i.e. `ω⁻¹(D − ωE)`; `hω : ω ≠ 0`),
`sorSplitting_iterationOperator : G = (D + ω strictLower)⁻¹ ((1−ω) D − ω strictUpper)`,
`sorSplitting_one : sorSplitting A h one_ne_zero = gaussSeidelSplitting A h`, and
`Matrix.ssorSplitting A h hω hω2` (`hω2 : ω ≠ 2`) whose `m` is exactly (4.27).
Equivalences: `sorStep_eq : sorStep A ω b = (sorSplitting A h hω).step b`
(`sorSplitting_iterationOperator`); `M_sor_eq : M_sor A ω = (sorSplitting A h hω).m` (`rfl` after
unfolding `E`); `ssorStep_eq_affine : ssorStep A ω b x = G_ssor A ω *ᵥ x + f_ssor A ω b`;
`M_ssor_eq : M_ssor A ω = (ssorSplitting A h hω hω2).m` (`rfl`);
`ssorSplitting_iterationOperator : (ssorSplitting A h hω hω2).iterationOperator = G_ssor A ω` —
the product form (4.13) is surface matrix algebra from `iterationOperator = 1 − m⁻¹ A` and
`Matrix.mul_nonsing_inv`; hence `ssorStep_eq : ssorStep A ω b = (ssorSplitting A h hω hω2).step b`.

**D12. Block splitting (4.15)–(4.17), general block Jacobi/GS (Alg 4.1–4.2).** Partition
`{1..n} = S₁ ∪ … ∪ S_p` (possibly overlapping), `V_i = [e_{m_i(1)}, …]`, `W_i` weighted columns with
`W_iᵀV_i = I`, `A_ij = W_iᵀ A V_j`, `ξ_i = W_iᵀ x`; block Jacobi update (4.17)
`ξ_i^{(k+1)} = ξ_i^{(k)} + A_ii⁻¹ W_iᵀ(b − A x_k)`.
```lean
structure BlockPartition (n : ℕ) where
  p : ℕ
  size : Fin p → ℕ
  idx : ∀ i, Fin (size i) → Fin n           -- `m_i(1..n_i)`, injective per block
  weight : ∀ i, Fin (size i) → ℝ            -- `η_{m_i(j)}`, chosen so that `W_iᵀ V_i = 1`
  cover : ∀ k, ∃ i j, idx i j = k
def BlockPartition.V (P) (i) : Matrix (Fin n) (Fin (P.size i)) ℝ := fun k j => if P.idx i j = k then 1 else 0
def BlockPartition.W (P) (i) := fun k j => if P.idx i j = k then P.weight i j else 0
noncomputable def blockJacobiStep (P) (A) (b x : Fin n → ℝ) : Fin n → ℝ :=
  x + ∑ i, P.V i *ᵥ ((P.W i)ᵀ * A * P.V i)⁻¹ *ᵥ ((P.W i)ᵀ *ᵥ (b - A *ᵥ x))          -- Alg 4.1
noncomputable def blockGsSweep (P) (A) (b) : (Fin n → ℝ) → (Fin n → ℝ) :=
  Fin.foldl-style composition of the `p` single-block corrections in order       -- Alg 4.2
```
Backbone: none in phase 1; block splittings and Alg 4.1–4.2 are phase 2 via `plans/backbone.md`
§2.4.4 (`Projection/Additive.lean`, §3 item 6). The definitions are `surface-only`; the
equivalence `blockJacobiStep = additiveProjectionStep` with `K_i = span (V_i)`, `L_i = span (W_i)`
is `deferred`. The non-overlapping identity "(4.17) is `x_{k+1} = D⁻¹(E+F)x_k + D⁻¹b` with block
`D, E, F`" is a surface-only rewrite.

**D13. Spectral radius of a real matrix; convergence factor and rate (§4.2.1).**
`ρ(G)`; specific factor `ρ = lim (‖d_k‖/‖d₀‖)^{1/k}`, rate `τ = −ln ρ`; general factor
`φ = lim (max_{x₀} ‖d_k‖/‖d₀‖)^{1/k}`.
```lean
-- `ρ(G)` is `Matrix.complexSpectralRadius G = spectralRadius ℂ (complexify G)` (no surface copy)
noncomputable def specificFactor (G) (d₀ : E n) : ℝ :=
  limsup (fun k => (‖(G^k) ⬝ d₀‖ / ‖d₀‖) ^ (1/k : ℝ)) atTop
noncomputable def generalFactor (G) : ℝ :=
  limsup (fun k => (⨆ d₀ : {d // d ≠ 0}, ‖(G^k) ⬝ d₀‖ / ‖d₀‖) ^ (1/k : ℝ)) atTop
```
Backbone: `Matrix.complexify`, `complexSpectralRadius`, `tendsto_pow_iff_complexSpectralRadius_lt_one`,
`mem_spectrum_complexify_iff` (`Numlib/Matrix/Complexify.lean`);
`exists_norm_pow_le_of_spectralRadius_lt` (`Numlib/Analysis/SpectralRadius.lean`); Mathlib's
Gelfand formula `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` on `Matrix n n ℂ`
under the scoped `L2Operator` normed-algebra instance. Equivalence:
`iSup_norm_div_eq_opNorm : ⨆ d₀ ≠ 0, ‖G^k d₀‖/‖d₀‖ = ‖G^k‖₂` (Mathlib `opNorm` characterization).
The book defines the factors as limits; the surface uses `limsup` and proves the limit exists in
the general case (Gelfand). See R-4.13.

**D14. Regular splitting (Def 4.3), M-matrix (Def 1.30).**
```lean
structure Matrix.IsRegularSplitting (A M N : Matrix (Fin n) (Fin n) ℝ) : Prop where
  eq : A = M - N
  isUnit : IsUnit M
  inv_nonneg : ∀ i j, 0 ≤ M⁻¹ i j
  nonneg : ∀ i j, 0 ≤ N i j
structure Matrix.IsMMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  diag_pos : ∀ i, 0 < A i i
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  isUnit : IsUnit A
  inv_nonneg : ∀ i j, 0 ≤ A⁻¹ i j
```
Backbone: none in phase 1 — `plans/backbone.md` §2.3.4 (`Stationary/RegularSplitting.lean`,
phase 2) and §2.1.12 (entrywise order, phase 2); see §3 item 3, which asks §2.3.4 to adopt these
two definitions verbatim (the surface spells out `∀ i j, 0 ≤ …` to avoid Mathlib's Loewner `≤` on
`Matrix`). Equivalence: `isRegularSplitting_iff` with the bundle §2.3.4 introduces.

**D15. Diagonal dominance (Def 4.5), irreducibility.** Weakly / strictly / irreducibly
diagonally dominant. As printed, Def 4.5 sums over the *row* index `i` with `j` fixed
(`|a_jj| ≥ Σ_{i≠j} |a_ij|`, i.e. column sums), while Thm 4.6/4.9 proofs use row sums (see §5);
the surface provides both and states Thm 4.9 for both.
```lean
-- strict dominance: the backbone's `Matrix.IsStrictDiagDominant` (row) and
-- `Matrix.IsStrictColDiagDominant` are used directly
def IsRowDiagDominant (A : Matrix (Fin n) (Fin n) 𝕜) : Prop := ∀ i, ∑ j ∈ univ.erase i, ‖A i j‖ ≤ ‖A i i‖
def IsColDiagDominant (A) : Prop := IsRowDiagDominant Aᵀ
/-- Saad's irreducibility (adjacency graph strongly connected), for arbitrary matrices. -/
def IsIrreducible (A : Matrix (Fin n) (Fin n) 𝕜) : Prop := Matrix.IsIrreducible (A.map fun a => ‖a‖)
def IsIrreduciblyRowDiagDominant (A) : Prop :=
  IsIrreducible A ∧ IsRowDiagDominant A ∧ ∃ i, ∑ j ∈ univ.erase i, ‖A i j‖ < ‖A i i‖
```
Backbone: `Matrix.IsStrictDiagDominant` (row), `Matrix.IsStrictColDiagDominant`,
`IsStrictColDiagDominant.transpose_iff : Aᵀ.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant`,
`IsStrictDiagDominant.diag_ne_zero/isUnit_diagPart/isUnit` (`Numlib/LinearSolve/Stationary/DiagDominant.lean`);
Mathlib `Matrix.IsIrreducible`, `Matrix.toQuiver` (`Mathlib/LinearAlgebra/Matrix/Irreducible/Defs`;
nonnegative matrices only — hence the `A.map ‖·‖` trick: `toQuiver` has an arrow `i ⟶ j` iff
`0 < ‖A i j‖` iff `A i j ≠ 0`). The irreducible variants have no backbone counterpart in phase 1
(§3 item 4).

**D16. Property A (Def 4.11), consistent ordering (Def 4.13), T-matrices, `B(α)`.**
```lean
def HasPropertyA (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ c : Fin n → Bool, ∀ i j, i ≠ j → A i j ≠ 0 → c i ≠ c j
/-- Def 4.13: labels `c` (the partition `S₁, …, S_p`) with adjacent `i, j` in consecutive sets,
`c j = c i + 1` if `j > i`, `c j = c i − 1` if `j < i`. -/
def IsConsistentlyOrdered (A) : Prop :=
  ∃ c : Fin n → ℤ, ∀ i j, i ≠ j → (A i j ≠ 0 ∨ A j i ≠ 0) → c j = c i + (if i < j then 1 else -1)
/-- T-matrix (Example 4.2): block tridiagonal w.r.t. consecutive index blocks, diagonal blocks diagonal. -/
def IsTMatrix (A) : Prop := ∃ (p : ℕ) (c : Fin n → Fin p), Monotone c ∧
  ∀ i j, A i j ≠ 0 → (c i = c j → i = j) ∧ ((c i : ℕ) ≤ c j + 1 ∧ (c j : ℕ) ≤ c i + 1)
def Bα (B : Matrix (Fin n) (Fin n) ℂ) (α : ℂ) := α • strictLower B + α⁻¹ • strictUpper B   -- Prop 4.12/4.15
```
Backbone: none in phase 1 — Young's SOR theory (Prop 4.12–Thm 4.16, Kress Def 4.13–Cor 4.16) is
`plans/backbone.md` §2.3.5 (phase 2), and §8.1 marks these definitions surface-only. §3 item 5
asks §2.3.5 to reuse them verbatim; the equivalence is then `Iff.rfl`.

**D17. Projection step (5.2)/(5.3), (5.5)–(5.6); matrix form (5.7); Alg 5.1.** "Find
`x̃ ∈ x₀ + K` with `b − Ax̃ ⟂ L`", `K, L` `m`-dimensional subspaces of ℝⁿ; orthogonal (`L = K`) vs
oblique; with bases `V, W`: `x̃ = x₀ + V(WᵀAV)⁻¹Wᵀr₀`, `r₀ = b − Ax₀`.
```lean
def IsProjectionApprox (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (K L : Submodule ℝ (E n))
    (x : E n) : Prop :=
  x - x₀ ∈ K ∧ ∀ w ∈ L, inner ℝ w (b - A ⬝ x) = 0                                    -- (5.5)–(5.6)
noncomputable def projStep (A) (b) (V W : Matrix (Fin n) (Fin m) ℝ) (x : E n) : E n :=
  x + toEuclideanLin (V * (Wᵀ * A * V)⁻¹ * Wᵀ) (b - A ⬝ x)                          -- (5.7)/Alg 5.1
```
Backbone (`Numlib/LinearSolve/Projection/Basic.lean`): `IsPetrovGalerkin A b x₀ K L x` (fields
`mem : x − x₀ ∈ K`, `orth : b − A x ∈ Lᗮ`), `IsGalerkin`, `IsMinRes`, `IsMinError xstar x₀ K x`
(explicit target), and the bases form `isPetrovGalerkin_iff_mulVec (V : Module.Basis ι 𝕜 K)
(W : Module.Basis ι 𝕜 L) (y) : IsPetrovGalerkin A b x₀ K L (x₀ + Σ_j y j • V j) ↔
(of fun i j => ⟪W i, A (V j)⟫) *ᵥ y = fun i => ⟪W i, b − A x₀⟫`. Equivalence:
`isProjectionApprox_iff : IsProjectionApprox A b x₀ K L x ↔ IsPetrovGalerkin (toEuclideanLin A) b x₀ K L x`
(`Submodule.mem_orthogonal'`); the dimension hypothesis `finrank K = m = finrank L` is carried by
`IsBasisOf` (D6) when bases are present.

**D18. `P_K`, `Q_K^L`, `A_m` (§5.2.3).** `P_K` orthogonal projector onto `K`, `Q_K^L` projector
onto `K` orthogonal to `L`, `A_m = Q_K^L A P_K`.
```lean
abbrev P_K (K) := K.starProjection                                          -- Mathlib
abbrev Q (K L) (hd : finrank K = finrank L) (h : K ⊓ Lᗮ = ⊥) := obliqueProjection K L hd h   -- D5
noncomputable def A_m (A) (K L) … : E n →ₗ[ℝ] E n := Q K L hd h ∘ₗ toEuclideanLin A ∘ₗ K.starProjection
```
Equivalence: D5 (`IsProjOnto K L x (Q x)`), D7.

**D19. One-dimensional processes (5.12), Alg 5.2–5.4; `E(x)`, `R(x)`.** `K = span{v}`,
`L = span{w}`, `x ← x + αv`, `α = (r, w)/(Av, w)`. SD: `v = w = r`; MR: `v = r, w = Ar`;
RNSD: `v = Aᵀr, w = Av`. `E(x) = (A(x* − x), x* − x)^{1/2}`, `R(x) = ‖b − Ax‖₂`.
```lean
noncomputable def step1 (A) (b) (v w x : E n) : E n :=
  x + (inner ℝ w (b - A ⬝ x) / inner ℝ w (A ⬝ v)) • v                                 -- (5.12)
noncomputable def sdStep (A) (b) (x) := step1 A b (b - A ⬝ x) (b - A ⬝ x) x
noncomputable def mrStep (A) (b) (x) := step1 A b (b - A ⬝ x) (A ⬝ (b - A ⬝ x)) x
noncomputable def rnsdStep (A) (b) (x) := step1 A b (Aᵀ ⬝ (b - A ⬝ x)) (A ⬝ (Aᵀ ⬝ (b - A ⬝ x))) x
/-- Alg 5.2 literally: state `(x, r, p)` with the recursive residual update. -/
structure SDState (n) where (x r p : E n)
noncomputable def sdAlgStep (A) (s : SDState n) : SDState n :=
  let α := inner ℝ s.r s.r / inner ℝ s.p s.r; let r' := s.r - α • s.p; ⟨s.x + α • s.r, r', A ⬝ r'⟩
-- likewise `mrAlgStep` (Alg 5.3: `α = (p, r)/(p, p)`), `rnsdAlgStep` (Alg 5.4)
noncomputable def E_A (A) (xstar x : E n) : ℝ := Real.sqrt (inner ℝ (A ⬝ (xstar - x)) (xstar - x))
noncomputable def R_A (A) (b) (x : E n) : ℝ := ‖b - A ⬝ x‖
```
Backbone (`Numlib/LinearSolve/Projection/OneDimensional.lean`): `Projection.step1 A b v w x =
x + (⟪w, b − A x⟫ / ⟪w, A v⟫) • v`, `steepestDescentStep`, `minResStep`, `residualNormSDStep`
(the last on `A : E →L[𝕜] E`, complete `E`); `energyNorm` (`Numlib/InnerProductSpace/Energy.lean`).
Equivalences: `step1_eq : step1 A b v w x = Projection.step1 (toEuclideanLin A) b v w x` (`rfl`),
`sdStep_eq`, `mrStep_eq` (`rfl`), `rnsdStep_eq : rnsdStep A b x = Projection.residualNormSDStep
(toEuclideanCLM A) b x` (`Matrix.toEuclideanLin_conjTranspose` and
`Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`; `Aᵀ = Aᴴ` over ℝ),
`E_A_eq_energyNorm : E_A A xstar x = energyNorm (toEuclideanLin A) (xstar - x)`,
`sdAlg_x_eq : (sdAlgStep A)^[k] ⟨x₀, r₀, A r₀⟩ = ⟨(sdStep A b)^[k] x₀, b − A x_k, A r_k⟩`
(surface-only bookkeeping, same pattern as the backbone's `CG.residual_eq`).

**D20. Additive and multiplicative projection procedures (5.22)–(5.23), Alg 5.5–5.6.** Systems
`V_i` (`n × n_i`, distinct spans), `A_i = V_iᵀAV_i`, `y_i = A_i⁻¹V_iᵀ(b − Ax_k)`,
`x_{k+1} = x_k + Σ ω_i V_i y_i`; `P_i = AV_i(V_iᵀAV_i)⁻¹V_iᵀ`; least-squares option `L_i = AK_i`.
```lean
structure ProjFamily (n : ℕ) where (p : ℕ) (size : Fin p → ℕ) (V : ∀ i, Matrix (Fin n) (Fin (size i)) ℝ)
noncomputable def additiveStep (𝒱 : ProjFamily n) (ω : Fin 𝒱.p → ℝ) (A) (b) (x : E n) : E n :=
  x + ∑ i, ω i • toEuclideanLin (𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ) (b - A ⬝ x)   -- Alg 5.5 with ω_i
noncomputable def P_i (𝒱) (A) (i) : Matrix (Fin n) (Fin n) ℝ := A * 𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ
  -- = obliqueProj (A * V i) (V i)  (D6)
noncomputable def multiplicativeSweep (𝒱) (A) (b) : E n → E n := composition over `i` of `projStep A b (V i) (V i)`   -- Alg 5.6
```
Backbone: `plans/backbone.md` §2.4.4 (`Projection/Additive.lean`, phase 2): residual
`r_{k+1} = (1 − Σ P_i) r_k` with `P_i` the projector onto `A K_i` orthogonal to `K_i` (§3 item 6).
Available now: `P_i = obliqueProj (A * V_i) V_i` (`rfl`) and
`toEuclideanLin (P_i) = obliqueProjectionOfBases ℝ (A * V_i).cols (V_i).cols` (D6); the equivalence
`additiveStep = additiveProjectionStep` is `deferred`.

## 2. Results

Fields: **Book** (faithful statement with exact hypotheses) · **Lean** (sketch) · **Backbone** ·
**Route** · **Class**: `direct` (a backbone/Mathlib theorem applies as stated),
`needs-equivalence` (through one of the §1 equivalence lemmas), `surface-only` (proved in the
surface from Mathlib), `deferred` (needs a §3 backbone item), `out-of-scope`.

### §1.11 Positive-definite matrices (`Ch01/PositiveDefinite.lean`)

**R-1.1 (1.49)–(1.52) Hermitian/skew decomposition.** Book: any square (real or complex) `A`
equals `H + iS` with `H = (A+Aᴴ)/2`, `S = (A−Aᴴ)/(2i)` both Hermitian, `iS` skew-Hermitian; for real
`A` and real `u`, `(Au, u) = (Hu, u)`.
Lean: `hermitianPart_isHermitian`, `skewPart_isHermitian`, `eq_hermitianPart_add_I_smul_skewPart`,
`mulVec_dotProduct_eq_hermitianPart (A : Matrix _ _ ℝ) (u) : (A *ᵥ u) ⬝ᵥ u = (A.hermitianPart *ᵥ u) ⬝ᵥ u`.
Backbone: Mathlib `selfAdjointPart`; the operator identity
`ContinuousLinearMap.re_inner_hermitianPart_apply` (`Numlib/InnerProductSpace/Coercive.lean`).
Route: `conjTranspose` algebra. Class: `surface-only` (definitional algebra; acceptable).

**R-1.2 Theorem 1.34.** Book: `A` real positive definite ⇒ `A` nonsingular and
`∃ α > 0, (Au, u) ≥ α ‖u‖₂² ∀ u ∈ ℝⁿ`; the proof takes `α = λ_min(H)`.
Lean: `thm_1_34 (hA : A.IsPositiveReal) : IsUnit A ∧ ∃ α > 0, ∀ u, α * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u`;
`thm_1_34' [Nonempty (Fin n)] (hA) (u) : lambdaMin (hermitianPart_isHermitian A) * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u`.
Backbone: `LinearMap.isCoercive_iff_forall_pos`, `LinearMap.IsCoercive.injective`
(`Numlib/InnerProductSpace/Coercive.lean`); `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`
(`Numlib/Matrix/ToEuclideanLin.lean`) applied to `hermitianPart A` with `lmin = λ_min(H)`, whose
field `le_re_inner` is the bound. Route: D1 equivalence gives coercivity, injective ⇒ `IsUnit`
(`Matrix.mulVec_injective_iff_isUnit`); the constant via R-1.1 and the quadratic-form bound for
the Hermitian `H`. Class: `needs-equivalence`.

**R-1.3 Theorem 1.35 (Bendixson).** Book: any square complex `A`, `H`, `S` as above: every
eigenvalue `λ` of `A` satisfies `λ_min(H) ≤ Re λ ≤ λ_max(H)` and `λ_min(S) ≤ Im λ ≤ λ_max(S)`.
Lean: `thm_1_35 [Nonempty (Fin n)] (A : Matrix _ _ ℂ) (hμ : μ ∈ spectrum ℂ A) : lambdaMin hH ≤ μ.re ∧ μ.re ≤ lambdaMax hH ∧ lambdaMin hS ≤ μ.im ∧ μ.im ≤ lambdaMax hS`.
Backbone: `re_hasEigenvalue_mem_Icc_of_symmetricPart {A H} (hH : H.IsSymmetricBoundedBy lmin lmax)
(hHA : ∀ x, re ⟪H x, x⟫ = re ⟪A x, x⟫) (hμ : HasEigenvalue A μ) : re μ ∈ Icc lmin lmax`
(`Numlib/Eigen/Perturbation.lean`). Route: `H := toEuclideanLin (hermitianPart A)` with
`Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`, `hHA` from R-1.1 (or
`ContinuousLinearMap.re_inner_hermitianPart_apply` and `toEuclideanLin_conjTranspose`),
`Matrix.hasEigenvalue_toEuclideanLin_iff` for `μ ∈ spectrum ℂ A`. The imaginary part is the same
statement for `(-Complex.I) • A`, whose Hermitian part is `skewPart A`
(`hermitianPart_neg_I_smul`, surface) and whose eigenvalues are `-i μ` (`re (-i μ) = im μ`).
Class: `needs-equivalence`.

**R-1.4 (1.57) the `B`-inner product.** Book: `B` SPD (HPD) ⇒ `(x, y)_B = (Bx, y)` is an inner
product on ℂⁿ (Saad §1.4 axioms). Lean: `energyInner_conj_symm`, `energyInner_add_left/smul_left`,
`energyInner_self_nonneg`, `energyInner_self_eq_zero_iff` for `hB : B.PosDef`; alternatively an
`InnerProductSpace.Core` instance. Backbone: `WithEnergy.core`, `WithEnergy.instInnerProductSpace`
(`Numlib/InnerProductSpace/Energy.lean`). Route: D3 equivalence +
`Matrix.posDef_iff_isSymmetricCoercive`. Class: `needs-equivalence`.

**R-1.5 `B`-self-adjoint examples.** Book: `A = B⁻¹C`, `A = CB` (`C` Hermitian, `B` HPD) are
Hermitian w.r.t. `(·,·)_B` (text remark; Exercise 18). Lean: `isSelfAdjointWrt_inv_mul`,
`isSelfAdjointWrt_mul`. Class: `surface-only` (two-line matrix algebra), optional.

### §1.12 Projection operators (`Ch01/Projectors.lean`)

**R-1.6 Projector basics (1.58).** Book: `P` projector ⇒ `I − P` projector, `Null P = Ran (I−P)`,
`Null P ∩ Ran P = {0}`, `ℂⁿ = Null P ⊕ Ran P`; conversely each direct-sum pair `(M, S)` defines a
unique projector with `Ran = M`, `Null = S`; `rank P = m ⇒ dim Ran(I−P) = n − m`.
Lean: `isProjector_one_sub`, `ker_eq_range_one_sub`, `isCompl_ker_range : IsCompl (ker P) (range P)`,
`existsUnique_projector (h : IsCompl M S) : ∃! P, IsIdempotentElem P ∧ range P = M ∧ ker P = S`,
`finrank_ker_eq`. Backbone/Mathlib: `IsIdempotentElem.isCompl`, `Submodule.projection`,
`IsIdempotentElem.eq_projection`, `LinearMap.finrank_range_add_finrank_ker`; uniqueness is
`LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq` (`Numlib/InnerProductSpace/ObliqueProjection.lean`).
Route: transport through `toEuclideanLin`. Class: `direct`.

**R-1.7 Lemma 1.36.** Book: `M, L ⊂ ℂⁿ` of the same dimension `m`: (i) no nonzero vector of `M`
is orthogonal to `L` ⟺ (ii) for every `x` there is a unique `u` with `u ∈ M`, `x − u ⟂ L`.
Lean: `lemma_1_36 (hdim : finrank 𝕜 M = finrank 𝕜 L) : (∀ v ∈ M, v ∈ Lᗮ → v = 0) ↔ ∀ x, ∃! u, IsProjOnto M L x u`.
Backbone: `LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot` and
`IsIdempotentElem.apply_eq_iff` (`Numlib/InnerProductSpace/ObliqueProjection.lean`). Route: (i) ⟺
`M ⊓ Lᗮ = ⊥`; (⇒) the unique `u` is `P x` for the backbone's projector; (⇐) for
`x ∈ M ⊓ Lᗮ` both `u = x` and `u = 0` qualify, so `x = 0` (three lines). Class: `direct` (⇒),
`surface-only` (⇐).

**R-1.8 (1.62).** Book: with `M ∩ Lᗮ = {0}`, the projector `P` onto `M` orthogonal to `L` has
`Ran P = M`, `Null P = Lᗮ`, and `Px = 0 ⟺ x ⟂ L`. Lean: `range_obliqueProjection`,
`ker_obliqueProjection`, `obliqueProjection_eq_zero_iff : Q x = 0 ↔ x ∈ Lᗮ`. Backbone: the range and
kernel of the chosen projector (D5, `obliqueProjection_spec`) and `IsIdempotentElem.apply_eq_iff`
with `y = 0`. Class: `direct`.

**R-1.9 Matrix representations (1.64)–(1.66).** Book: bases `V` of `M`, `W` of `L`; `Px = Vy`
with `Wᴴ(x − Vy) = 0` (1.64); biorthogonal ⇒ `P = VWᴴ` (1.65); in general `P = V(WᴴV)⁻¹Wᴴ` (1.66);
if no vector of `M` is orthogonal to `L` then `WᴴV` is nonsingular.
Lean: `obliqueProj_isProjOnto (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) (h : IsUnit (Wᴴ * V)) (x) : IsProjOnto M L x (toEuclideanLin (obliqueProj V W) x)`;
`obliqueProj_of_biorthogonal : Wᴴ * V = 1 → obliqueProj V W = V * Wᴴ`;
`isUnit_conjTranspose_mul_of_inf_eq_bot : (∀ v ∈ M, v ∈ Lᗮ → v = 0) → IsUnit (Wᴴ * V)` (the
converse too); `isProjOnto_iff_conjTranspose_mul_eq (hV) : IsProjOnto M L x (V ⬝ y) ↔ Wᴴ *ᵥ (x − V *ᵥ y) = 0` (1.64).
Backbone: `LinearMap.obliqueProjectionOfBases`, `crossGram`, `range_obliqueProjectionOfBases`,
`sub_obliqueProjectionOfBases_apply_mem_orthogonal` (`Numlib/InnerProductSpace/ObliqueProjection.lean`),
through D6's `toEuclideanLin_obliqueProj` and `crossGram_cols`. Route: `y ↦ V y` is injective with
image `M`; `Wᴴ z = 0 ↔ z ∈ Lᗮ` (columns of `W` span `L`). Class: `needs-equivalence` (D6).

**R-1.10 Adjoint projector (1.68)–(1.70).** Book: `Pᴴ` is a projector; `Null Pᴴ = (Ran P)ᗮ`,
`Null P = (Ran Pᴴ)ᗮ`. Lean: `isIdempotentElem_conjTranspose`, `ker_conjTranspose_eq_orthogonal_range`,
`ker_eq_orthogonal_range_conjTranspose`. Backbone/Mathlib: `LinearMap.orthogonal_range`
(`T.rangeᗮ = T.adjoint.ker`), `Matrix.toEuclideanLin_conjTranspose` (`Numlib/Matrix/ToEuclideanLin.lean`:
the adjoint of `toEuclideanLin A` is `toEuclideanLin Aᴴ`). Class: `direct`.

**R-1.11 Proposition 1.37.** Book: a projector is orthogonal iff it is Hermitian.
Lean: `prop_1_37 (hP : IsIdempotentElem P) : (ker (toEuclideanLin P) = (range (toEuclideanLin P))ᗮ) ↔ P.IsHermitian`.
Backbone/Mathlib: `IsIdempotentElem.isSymmetric_iff_orthogonal_range`;
`Matrix.isHermitian_iff_isSymmetric` (`toEuclideanLin`). Class: `direct`.

**R-1.12 `P = VVᴴ` and its non-uniqueness.** Book: `V` `n × m` with orthonormal columns
spanning `M` ⇒ `P = VVᴴ` is the orthogonal projector onto `M`; two orthonormal bases `V₁, V₂` of
`M` give `V₁V₁ᴴ = V₂V₂ᴴ`. Lean: `isOrthogonalProjector_mul_conjTranspose (hV : Vᴴ * V = 1) (hV' : V.IsBasisOf M) : (V * Vᴴ).IsOrthogonalProjector ∧ range … = M`,
`mul_conjTranspose_eq_of_isBasisOf : V₁ * V₁ᴴ = V₂ * V₂ᴴ`. Backbone:
`LinearMap.obliqueProjectionOfBases_self_eq_starProjection (hV : Orthonormal 𝕜 V)`
(`Numlib/InnerProductSpace/ObliqueProjection.lean`) through D6 (`Vᴴ * V = 1 ↔ Orthonormal 𝕜 V.cols`,
`obliqueProj V V = V * Vᴴ`); both sides of the non-uniqueness are `M.starProjection`. Class:
`needs-equivalence` (D6, D7).

**R-1.13 Properties of orthogonal projectors (§1.12.4).** Book: `‖x‖₂² = ‖Px‖₂² + ‖(I−P)x‖₂²`,
`‖Px‖₂ ≤ ‖x‖₂`, `‖P‖₂ = 1`, eigenvalues of an orthogonal projector are `0` or `1` (range vectors
for `1`, null-space vectors for `0`). Lean: `norm_sq_eq_add (hP : P.IsOrthogonalProjector)`,
`norm_apply_le`, `l2_opNorm_eq_one (hP) (h0 : P ≠ 0)` (scoped `Matrix.Norms.L2Operator`),
`spectrum_subset_pair (hP : IsIdempotentElem P) : spectrum ℂ P ⊆ {0, 1}`, `mem_range_iff_eigen_one`.
Backbone/Mathlib: `Submodule.norm_sq_eq_add_norm_sq_starProjection`, `starProjection_norm_le`;
`ContinuousLinearMap.IsIdempotentElem.norm_eq_one_iff_isSymmetric (hP) (h0 : P ≠ 0)`
(`Numlib/InnerProductSpace/ObliqueProjection.lean`) with `Matrix.l2_opNorm_eq_norm_toEuclideanLin`
for `‖P‖₂ = 1`. Route: `starProjection` API; `‖P‖₂ = 1` needs `P ≠ 0` (book says "for any
orthogonal projector"; `P = 0` is a counterexample — see §5). Class: `direct` for the norm facts,
`surface-only` for the eigenvalue facts (idempotent ⇒ `μ² = μ`).

**R-1.14 Theorem 1.38.** Book: `P` the orthogonal projector onto `M`, `x ∈ ℂⁿ`:
`min_{y ∈ M} ‖x − y‖₂ = ‖x − Px‖₂`. Lean: `thm_1_38 (M) (x) : IsLeast ((fun y => ‖x - y‖) '' (M : Set _)) ‖x - M.starProjection x‖`.
Backbone/Mathlib: `Submodule.starProjection_minimal` (as `⨅`), `starProjection_apply_mem`.
Class: `direct`.

**R-1.15 Corollary 1.39.** Book: `M`, `x` given: `min_{y ∈ M} ‖x − y‖₂ = ‖x − y*‖₂` iff
`y* ∈ M` and `x − y* ⟂ M`. Lean: `cor_1_39 (M) (x y) : IsLeast ((fun y => ‖x - y‖) '' M) ‖x - y‖ ↔ y ∈ M ∧ x - y ∈ Mᗮ`
(`IsLeast` includes membership, which is how the book's "min over `y ∈ M`" is read — see §5).
Backbone/Mathlib: `Submodule.norm_eq_iInf_iff_inner_eq_zero (hv : v ∈ K)`. Class: `direct`.

### §1.13 Basic concepts in linear systems (`Ch01/LinearSystems.lean`)

**R-1.16 Existence (§1.13.1, Cases 1–3).** Book: `A` nonsingular ⇒ unique solution `x = A⁻¹b`;
`A` singular and `b ∈ Ran A` ⇒ infinitely many solutions (`x₀ + Null A`); `b ∉ Ran A` ⇒ none.
Lean: `existsUnique_of_isUnit (hA : IsUnit A) : ∃! x, A *ᵥ x = b` (and `= A⁻¹ *ᵥ b`),
`solutions_eq_vadd_ker (hb : ∃ x₀, A *ᵥ x₀ = b) : {x | A *ᵥ x = b} = x₀ +ᵥ ker (mulVecLin A)`,
`infinite_solutions_of_not_isUnit (hA : ¬ IsUnit A) (hb) : Set.Infinite {x | A *ᵥ x = b}`,
`not_exists_of_not_mem_range`. Backbone/Mathlib: `Matrix.mulVec_injective_iff_isUnit`,
`Matrix.mulVec_surjective_iff_isUnit`. Class: `surface-only` (elementary linear algebra, not
numerical-analysis content; acceptable).

**R-1.17 Perturbed system (1.74)–(1.75).** Book: `A` nonsingular, any `E`: `A + εE` nonsingular
for `ε` small (Exercise 37); `(A + εE)x(ε) = b + εe`, `δ(ε) = x(ε) − x = ε(A+εE)⁻¹(e − Ex)`; `x(ε)` is
differentiable at `0` with `x'(0) = A⁻¹(e − Ex)`.
Lean: `isUnit_add_smul_of_small (hA : IsUnit A) (E) : ∀ᶠ ε in 𝓝 (0:𝕜), IsUnit (A + ε • E)`;
`delta_eq (hA) (hε : IsUnit (A + ε • E)) (hx : A *ᵥ x = b) : (A + ε • E)⁻¹ *ᵥ (b + ε • e) - x = ε • (A + ε • E)⁻¹ *ᵥ (e - E *ᵥ x)`;
`hasDerivAt_perturbed_solution (hA) (hx) : HasDerivAt (fun ε : ℝ => (A + ε • E)⁻¹ *ᵥ (b + ε • e)) (A⁻¹ *ᵥ (e - E *ᵥ x)) 0`
(matrices over ℝ; `𝕜` version with `HasDerivAt` over `𝕜`). Backbone: `Units.isUnit_add_of_norm_lt`,
`Units.norm_inverse_add_le` (`Numlib/Analysis/NormedRing/Inverse.lean`; the eventual invertibility,
under the scoped `Matrix.Norms.Operator` normed-ring structure); Mathlib `hasFDerivAt_ringInverse`
(`Matrix.nonsing_inv_eq_ringInverse`). Route: algebra for `δ(ε)`; chain rule for the derivative.
Class: `surface-only` (Mathlib calculus; the derivative of the solution map is a candidate for
`Numlib/LinearSolve/Perturbation.lean`, §3 item 7).

**R-1.18 (1.76) relative perturbation bound.** Book: with `‖·‖` a vector norm and its induced
matrix norm, `‖x(ε) − x‖/‖x‖ ≤ ε ‖A⁻¹‖ (‖e‖/‖x‖ + ‖E‖) + o(ε)`, hence (using `‖b‖ ≤ ‖A‖‖x‖`)
`‖x(ε) − x‖/‖x‖ ≤ ε κ(A)(‖e‖/‖b‖ + ‖E‖/‖A‖) + o(ε)`, `κ(A) = ‖A‖‖A⁻¹‖`.
Lean (for each `p`, via D8, with `x ≠ 0`, `b ≠ 0`, `IsUnit A`):
```lean
theorem eq_1_76_exact (hε : |ε| * lpOpNorm p A⁻¹ * lpOpNorm p E < 1) :
    ‖x ε - x‖_p / ‖x‖_p ≤ condNumberLp p A / (1 - |ε| * lpOpNorm p A⁻¹ * lpOpNorm p E) *
      (|ε| * (lpOpNorm p E / lpOpNorm p A + ‖e‖_p / ‖b‖_p))
theorem eq_1_76 : ∃ g : ℝ → ℝ, g =o[𝓝 0] (fun ε => ε) ∧ ∀ᶠ ε in 𝓝 0,
    ‖x ε - x‖_p / ‖x‖_p ≤ |ε| * condNumberLp p A * (‖e‖_p / ‖b‖_p + lpOpNorm p E / lpOpNorm p A) + g ε
```
(`x ε := (A + ε • E)⁻¹ *ᵥ (b + ε • e)`; `‖·‖_p` the `PiLp p` norm). Backbone:
`relative_error_le_condNumber (A : E ≃L[𝕜] E) (ΔA) (hx) (hy) (hsmall : ‖A⁻¹‖ * ‖ΔA‖ < 1) (hx0) (hb)`
and `exists_perturbed_solution` (`Numlib/LinearSolve/Perturbation.lean`, any complete normed space);
`NormedRing.condNumber`. Route: instantiate `E := PiLp p (fun _ : Fin n => 𝕜)` with D8's
`toLpEquiv hA`, `ΔA = ε • E`, `Δb = ε • e`; `κ/(1 − t) = κ + κt/(1−t)` gives `g ε = O(ε²)`; the
first (`‖A⁻¹‖`) form is the same specialization before using `‖b‖ ≤ ‖A‖‖x‖`. Class:
`needs-equivalence` (D8; the `o(ε)` corollary is surface algebra, see §3 item 7).

**R-1.19 Properties of `κ`.** Book: `κ` is scaling invariant; `κ(αI) = 1` for the standard
norms while `det(αI) = αⁿ`; `κ_p(A)` labelled by the norm. Lean: `condNumberLp_smul (hc : c ≠ 0) : condNumberLp p (c • A) = condNumberLp p A`,
`condNumberLp_smul_one (hc) : condNumberLp p (c • 1) = 1`, `one_le_condNumberLp (hA : IsUnit A)`,
`det_smul_one : det (c • (1 : Matrix (Fin n) (Fin n) 𝕜)) = c ^ n`. Backbone:
`NormedRing.condNumber_smul`, `one_le_condNumber` (`Numlib/Analysis/NormedRing/CondNumber.lean`).
Class: `direct` (via D8), `det` fact Mathlib `det_smul`.

**R-1.20 Example 1.5.** Book: `A_n = I + α e₁ eₙᵀ`, `A_n⁻¹ = I − α e₁ eₙᵀ`,
`‖A_n‖_∞ = ‖A_n⁻¹‖_∞ = 1 + |α|`, `κ_∞(A_n) = (1 + |α|)²` (for `n ≥ 2`), all eigenvalues `1`.
Lean: `example_1_5 (hn : 2 ≤ n) : condNumberLp ⊤ (1 + α • vecMulVec (Pi.single 0 1) (Pi.single (Fin.last _) 1)) = (1 + |α|) ^ 2`
plus `spectrum ℂ A_n = {1}`. Backbone: `plans/backbone.md` §2.1.2 assigns this example to the
surface. Route: `linfty_opNorm_def` (row sums), `charpoly` of a unipotent matrix. Class:
`surface-only` (explicit computation; optional).

**R-1.21 Residual–error relation.** Book: `x` the solution, `x̃` any approximation, `r = b − Ax̃`:
`‖x − x̃‖/‖x‖ ≤ κ(A) ‖r‖/‖b‖`. Lean: `relative_error_le (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0) (xt) : ‖x - xt‖_p / ‖x‖_p ≤ condNumberLp p A * (‖b - A *ᵥ xt‖_p / ‖b‖_p)`.
Backbone: `relative_error_le_condNumber_mul_relative_residual (A : E ≃L[𝕜] E) (hx) (hb)`
(`Numlib/LinearSolve/Perturbation.lean`). Class: `direct` (via D8).

### §4.1 Jacobi, Gauss–Seidel and SOR (`Ch04/Splittings.lean`)

**R-4.1 (4.3)–(4.5) Jacobi.** Book: annihilating the `i`-th residual component gives (4.4)
`ξ_i^{(k+1)} = (β_i − Σ_{j≠i} a_ij ξ_j^{(k)})/a_ii`, i.e. (4.5) `x_{k+1} = D⁻¹(E+F)x_k + D⁻¹b`.
Lean: `jacobiStep_residual (h : ∀ i, A i i ≠ 0) : (b - A *ᵥ jacobiStep A b x) i = 0` — careful: (4.3)
is `(b − A x_{k+1})_i = 0` *with the other components frozen*, i.e. `jacobiStep` is characterized by
`∀ i, A i i * (jacobiStep A b x) i + ∑ j ≠ i, A i j * x j = b i`; `jacobiStep_eq_vec (h) : jacobiStep A b x = (D A)⁻¹ *ᵥ ((E A + F A) *ᵥ x) + (D A)⁻¹ *ᵥ b`.
Backbone: `Matrix.jacobiSplitting`, `jacobiSplitting_iterationOperator` (`= −D⁻¹(strictLower + strictUpper)`,
i.e. `D⁻¹(E+F)`), `isUnit_diagPart_iff` (`Numlib/LinearSolve/Stationary/Splitting.lean`) via D9.
Class: `needs-equivalence` (D9; the componentwise formula is surface algebra).

**R-4.2 (4.6)–(4.8) Gauss–Seidel.** Book: (4.6) with updated components, (4.7) componentwise,
`b + Ex_{k+1} − Dx_{k+1} + Fx_k = 0`, (4.8) `x_{k+1} = (D−E)⁻¹Fx_k + (D−E)⁻¹b`.
Lean: `gsStep_spec (h) : (D A - E A) *ᵥ gsStep A b x = F A *ᵥ x + b` (4.6 in vector form),
`gsStep_apply (h) (i) : gsStep A b x i = (-(∑ j ∈ Iio i, A i j * gsStep A b x j) - ∑ j ∈ Ioi i, A i j * x j + b i) / A i i` (4.7),
`gsStep_eq_vec : gsStep A b x = (D A - E A)⁻¹ *ᵥ (F A *ᵥ x) + (D A - E A)⁻¹ *ᵥ b` (4.8).
Backbone: `Matrix.gaussSeidelSplitting`, `gaussSeidelSplitting_n`,
`Matrix.isUnit_diagPart_add_strictLower` (`IsUnit (D − E)`; `Splitting.lean`). Route: (4.7) is the
forward substitution identity for the lower triangular `D − E`. Class: `needs-equivalence` (D9) for
(4.8); `surface-only` for (4.7).

**R-4.3 (4.9) backward and symmetric GS.** Book: `(D − F)x_{k+1} = Ex_k + b`, coordinate order
`n, …, 1`; symmetric GS = forward then backward sweep. Lean: `backwardGsStep_spec`,
`backwardGsStep_apply` (reverse-order recursion), `symmetricGsStep_eq`. Backbone:
`Matrix.backwardGaussSeidelSplitting A h` (`m = diagPart A + strictUpper A = D − F`),
`isUnit_diagPart_add_strictUpper` (`Splitting.lean`). Class: `needs-equivalence` (D9).

**R-4.4 (4.10)–(4.11), (4.18)–(4.23) splitting form.** Book: Jacobi and GS are
`Mx_{k+1} = Nx_k + b = (M − A)x_k + b` with `M = D`, `D − E`, `D − F`; any splitting with `M`
nonsingular gives `x_{k+1} = M⁻¹Nx_k + M⁻¹b`, `G = M⁻¹N = I − M⁻¹A`, `f = M⁻¹b`;
`G_JA = I − D⁻¹A`, `G_GS = I − (D−E)⁻¹A`; the iteration solves `(I − G)x = f`, i.e. the
preconditioned system `M⁻¹Ax = M⁻¹b` (same solution as `Ax = b`).
Lean: `jacobiStep_eq`, `gsStep_eq`, `backwardGsStep_eq` (D9),
`Splitting.iterationOperator_eq_one_sub : s.iterationOperator = 1 - s.m⁻¹ * A`,
`G_JA_eq : (jacobiSplitting A h).iterationOperator = 1 - (D A)⁻¹ * A`, `G_GS_eq`,
`fixedPoint_iff : x = G *ᵥ x + f ↔ s.m⁻¹ *ᵥ (A *ᵥ x) = s.m⁻¹ *ᵥ b`,
`preconditioned_iff (hM : IsUnit M) : M⁻¹ *ᵥ (A *ᵥ x) = M⁻¹ *ᵥ b ↔ A *ᵥ x = b`.
Backbone: `Stationary.Splitting.iterationOperator_eq`, `one_sub_iterationOperator`, `m_sub_n`,
`eq_iterationOperator_mul_add_iff` (ring form; `Splitting.lean`), `Stationary.step_fixed_iff`
(`Stationary/Basic.lean`). Class: `direct` for the ring identities
(`Matrix.nonsing_inv_eq_ringInverse`), `surface-only` for their `mulVec` forms.

**R-4.5 (4.12) SOR and its relaxation form.** Book: SOR from the splitting
`ωA = (D − ωE) − (ωF + (1−ω)D)`; equals the relaxation sequence
`ξ_i^{(k+1)} = ω ξ_i^{GS} + (1−ω) ξ_i^{(k)}` (`ξ_i^{GS}` the right side of (4.7) evaluated with the
already-updated components); backward SOR analogously.
Lean: `sorStep_spec (h) : (D A - ω • E A) *ᵥ sorStep A ω b x = (ω • F A + (1 - ω) • D A) *ᵥ x + ω • b`,
`sorStep_apply (h) (i) : sorStep A ω b x i = ω * ((-(∑ j ∈ Iio i, A i j * sorStep A ω b x j) - ∑ j ∈ Ioi i, A i j * x j + b i) / A i i) + (1 - ω) * x i`,
`sorStep_one : sorStep A 1 b = gsStep A b`, `omega_smul_decomp : ω • A = (D A - ω • E A) - (ω • F A + (1 - ω) • D A)`.
Backbone: `Matrix.sorSplitting`, `sorSplitting_iterationOperator`, `sorSplitting_one`
(`Splitting.lean`) via D11. Class: `needs-equivalence` for the splitting form, `surface-only` for
the componentwise identity.

**R-4.6 (4.13)–(4.14) SSOR.** Book: SSOR step = SOR step followed by backward SOR step;
`x_{k+1} = G_ω x_k + f_ω` with `G_ω`, `f_ω` as in (4.13)–(4.14), and
`f_ω = ω(2−ω)(D − ωF)⁻¹D(D − ωE)⁻¹b` (using `[ωE + (1−ω)D](D − ωE)⁻¹ = −I + (2−ω)D(D − ωE)⁻¹`).
Lean: `ssorStep_eq_affine (h) : ssorStep A ω b x = G_ssor A ω *ᵥ x + f_ssor A ω b`,
`f_ssor_eq (h) : f_ssor A ω b = (ω * (2 - ω)) • (D A - ω • F A)⁻¹ *ᵥ (D A *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b))`,
`aux_identity : (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ = -1 + (2 - ω) • D A * (D A - ω • E A)⁻¹`.
Backbone: `Matrix.ssorSplitting` (`Splitting.lean`). Route: matrix algebra with
`Matrix.mul_nonsing_inv`. Class: `surface-only` (book-specific closed forms; acceptable) plus
`needs-equivalence` for `ssorStep = (ssorSplitting A h hω hω2).step b` (D11).

**R-4.7 §4.1.1 block relaxation, (4.16)–(4.17), Alg 4.1–4.2.** Book: with a block partition,
block Jacobi is `A_ii ξ_i^{(k+1)} = ((E+F)x_k)_i + β_i`, i.e. the same vector equation with block
`D, E, F`; with `V_i`, `W_i` (`W_iᵀV_i = I`) the Jacobi component is (4.17); `V_iW_iᵀ` is a
projector onto `K_i = span(V_i)`; `x = Σ V_i ξ_i`.
Lean: `V_W_biorthogonal (P) (h : weights chosen) : (P.W i)ᵀ * P.V i = 1`,
`isProjector_V_mul_Wᵀ`, `sum_V_mulVec_Wᵀ (P : partition, no overlap) : ∑ i, P.V i *ᵥ ((P.W i)ᵀ *ᵥ x) = x`,
`blockJacobiStep_eq_of_partition : blockJacobiStep P A b x = (blockD)⁻¹ *ᵥ ((blockE + blockF) *ᵥ x) + (blockD)⁻¹ *ᵥ b`,
`blockJacobiStep_component (4.17)`. Backbone: `plans/backbone.md` §2.4.4 (phase 2). Class:
`surface-only` for the definitions and identities (definitional); `deferred` (§3 item 6) for the
equivalence with the additive projection step.

**R-4.8 (4.24)–(4.27) preconditioners.** Book: `M_JA = D`, `M_GS = D − E`, `M_SOR = ω⁻¹(D − ωE)`,
`M_SSOR = (ω(2−ω))⁻¹(D − ωE)D⁻¹(D − ωF)`, and the SSOR iteration is the fixed-point iteration of
`M_SSOR⁻¹Ax = M_SSOR⁻¹b`, i.e. `G_ω = I − M_SSOR⁻¹A` (implicit in the text).
Lean: `M_JA_eq : (jacobiSplitting A h).m = D A` (`rfl`), `M_GS_eq`, `M_sor_eq` (D11),
`M_ssor_eq : M_ssor A ω = (ssorSplitting A h hω hω2).m` (`rfl`),
`G_ssor_eq_one_sub (h) (hω : ω ≠ 0) (hω2 : ω ≠ 2) : G_ssor A ω = 1 - (M_ssor A ω)⁻¹ * A`
(= D11's `ssorSplitting_iterationOperator`), `f_ssor_eq_inv_mulVec : f_ssor A ω b = (M_ssor A ω)⁻¹ *ᵥ b`.
Backbone: `Matrix.ssorSplitting` (its `m` is (4.27) verbatim), `Splitting.iterationOperator`
(`Splitting.lean`). Class: `needs-equivalence` (D11); the product form (4.13) is surface algebra.

### §4.2 Convergence (`Ch04/Convergence.lean`, `DiagDominant.lean`, `SPD.lean`)

**R-4.9 (4.29) the limit solves the system.** Book: if `x_{k+1} = Gx_k + f` converges, the limit
satisfies `x = Gx + f`; for `G = M⁻¹N`, `f = M⁻¹b` this is `Mx = Nx + b`, i.e. `Ax = b`.
Lean: `tendsto_affineStep_fixed (h : Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) : x = G *ᵥ x + f`,
`fixed_iff_solves (s : Splitting A) : x = s.step b x ↔ A *ᵥ x = b`. Backbone:
`Stationary.step_fixed_iff` (`Stationary/Basic.lean`), `Splitting.eq_iterationOperator_mul_add_iff`
(`Splitting.lean`); continuity of `affineStep`. Class: `direct` / `surface-only` (uniqueness of
limits).

**R-4.10 (4.30) error recursion.** Book: `I − G` nonsingular ⇒ solution `x*` of (4.29) and
`x_{k+1} − x* = G(x_k − x*) = … = G^{k+1}(x₀ − x*)`; also `x_{k+1} − x_k = G^k(f − (I−G)x₀)`.
Lean: `affineStep_iterate_sub (hx : G *ᵥ x' + f = x') : (affineStep G f)^[k] x₀ - x' = (G ^ k) *ᵥ (x₀ - x')`,
`affineStep_iterate_succ_sub : (affineStep G f)^[k+1] x₀ - (affineStep G f)^[k] x₀ = (G ^ k) *ᵥ (f - (1 - G) *ᵥ x₀)`.
Backbone: `Stationary.step_iterate_sub (hfix : G x' + f = x') (x₀) (k)` (`Stationary/Basic.lean`)
through D10's `affineStep_eq_step`. Class: `direct`; the second identity `surface-only`.

**R-4.11 Theorem 4.1.** Book: `G` square (real) with `ρ(G) < 1` ⇒ `I − G` nonsingular and (4.28)
converges for any `f` and `x₀`; conversely, if (4.28) converges for any `f` and `x₀` then `ρ(G) < 1`.
Lean:
```lean
theorem thm_4_1_mp (hG : Matrix.complexSpectralRadius G < 1) : IsUnit (1 - G) ∧
    ∀ f x₀, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f))
theorem thm_4_1_mpr (h : ∀ f x₀, ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) :
    Matrix.complexSpectralRadius G < 1
```
Backbone: `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one : Tendsto (G ^ k) (𝓝 0) ↔
complexSpectralRadius G < 1`, `isUnit_complexify_iff`, `complexify_one` (`Numlib/Matrix/Complexify.lean`);
`isUnit_one_sub_of_spectralRadius_lt_one` (`Numlib/Analysis/SpectralRadius.lean`); the operator
forms `Stationary.tendsto_of_spectralRadius_lt_one`, `spectralRadius_lt_one_of_forall_tendsto`,
`forall_tendsto_iff_spectralRadius_lt_one` (`Stationary/Basic.lean`, `F →L[ℂ] F`) are the same
theorem for complex vectors. Route (⇒): `IsUnit (1 − complexify G)` from
`isUnit_one_sub_of_spectralRadius_lt_one`, transported by `isUnit_complexify_iff` and
`complexify_sub`; then R-4.10 with `x* = (1−G)⁻¹f` and `Gᵏ(x₀ − x*) → 0` from
`tendsto_pow_iff_complexSpectralRadius_lt_one` (`mulVec` is continuous). (⇐): `x₀ = 0`, `f = v`
gives `x_{k+1} − x_k = Gᵏ v → 0` for all `v` (R-4.10), hence `Gᵏ → 0` entrywise, then
`tendsto_pow_iff_complexSpectralRadius_lt_one`. Class: `needs-equivalence` (real/complex glue of
`Basic.lean`).

**R-4.12 Corollary 4.2.** Book: `‖G‖ < 1` for *some matrix norm* (Saad §1.5: a norm on
`ℂ^{n×n}` that is consistent, `‖AB‖ ≤ ‖A‖‖B‖`) ⇒ `I − G` nonsingular and (4.28) converges for any
`x₀` (and `f`). Lean: `cor_4_2 (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ)) (hG : N G < 1) : IsUnit (1 - G) ∧ ∀ f x₀, Tendsto … (𝓝 ((1 - G)⁻¹ *ᵥ f))`;
instances `cor_4_2_lp (p) (hG : lpOpNorm p G < 1)` and the scoped `‖G‖ < 1` forms for `p = 2, ∞`.
Backbone: `Stationary.contractingWith (‖G‖ < 1)` (`Stationary/Basic.lean`);
`spectralRadius_lt_one_of_norm_lt_one` (`Numlib/Analysis/SpectralRadius.lean`) for the scoped
complex normed-algebra instances. Route for `lpOpNorm p`: `lpOpNorm p (G^k) ≤ (lpOpNorm p G)^k → 0`
⇒ `Gᵏx → 0` ⇒ R-4.11 (⇐)+(⇒). Route for an arbitrary `AlgebraNorm`: needs "all norms on the
finite-dimensional space `Matrix` are equivalent" to get `Gᵏ → 0` from `N(Gᵏ) ≤ N(G)ᵏ`. Class:
`direct` for `lpOpNorm p`; `deferred` (§3 item 2) for a general consistent norm.

**R-4.13 Convergence factor and rate (§4.2.1).** Book: `d_k = Gᵏd₀`; specific factor
`ρ = lim (‖d_k‖/‖d₀‖)^{1/k}` equals `ρ(G)` (derived with the Jordan form under "one dominant
eigenvalue"); `τ = −ln ρ`; general factor `φ = lim (max_{d₀} ‖Gᵏd₀‖/‖d₀‖)^{1/k} = lim ‖Gᵏ‖^{1/k} = ρ(G)`.
Lean: `limsup_specific_le : limsup (fun k => (‖(G^k) ⬝ d₀‖/‖d₀‖)^(1/k:ℝ)) atTop ≤ (complexSpectralRadius G).toReal`;
`iSup_eq_opNorm : (⨆ d₀ : {d // d ≠ 0}, ‖(G^k) ⬝ d₀‖/‖d₀‖) = ‖G^k‖₂`;
`tendsto_generalFactor : Tendsto (fun k => ‖G^k‖₂ ^ (1/k:ℝ)) atTop (𝓝 (complexSpectralRadius G).toReal)` (Gelfand);
`exists_specific_eq : ∃ d₀ ≠ 0, limsup … = ρ(G)`. Backbone: `exists_norm_pow_le_of_spectralRadius_lt`
(`Numlib/Analysis/SpectralRadius.lean`) on `complexify G` under the scoped `L2Operator` norm, with
the vector glue `norm_complexify_mulVec` (`Basic.lean`), gives `limsup_specific_le`; Mathlib's
Gelfand formula gives `tendsto_generalFactor` once `‖complexify (G^k)‖₂ = ‖G^k‖₂` is available
(§3 item 1), and `exists_specific_eq` needs the eigenvector argument of the same item. The book's
claim that the *specific* limit exists and equals `ρ(G)` for the generic `d₀` (Jordan asymptotics
`‖d_k‖ ≈ C |λ|^{k−p+1} C(k, p−1)`) is heuristic ("≈") and needs the Jordan form: left out (§4).
Class: `direct` (`limsup_specific_le`), `needs-equivalence` (`iSup_eq_opNorm`, Mathlib `opNorm`),
`deferred` (§3 item 1) for the Gelfand limit and its attainment.

**R-4.14 Example 4.1 (Richardson).** Book: `x_{k+1} = x_k + α(b − Ax_k)`, `G_α = I − αA`; if all
eigenvalues of `A` are real with `λ_min ≤ λ_i ≤ λ_max`: eigenvalues of `G_α` lie in
`[1 − αλ_max, 1 − αλ_min]`; if `λ_min < 0 < λ_max` the method diverges for some `x₀` for every
`α`; if `λ_min > 0` it converges iff `0 < α < 2/λ_max`; `ρ(G_α) = max{|1 − αλ_min|, |1 − αλ_max|}`,
`α_opt = 2/(λ_min + λ_max)`, `ρ_opt = (λ_max − λ_min)/(λ_max + λ_min)`.
Lean: `richardsonStep A α b x := x + α • (b - A *ᵥ x)`,
`richardsonStep_eq : richardsonStep A α b = (Stationary.Splitting.richardson A hα).step b`,
`spectrum_one_sub_smul : spectrum ℂ (1 - α • A) = (fun μ => 1 - α * μ) '' spectrum ℂ A`,
`spectralRadius_richardson (hreal : spectrum ℂ A ⊆ range ofReal) (hmin hmax : attained extremes) : ρ(G_α) = max |1 − αλ_min| |1 − αλ_max|`,
`richardson_converges_iff (hpos : 0 < λ_min) : ρ(G_α) < 1 ↔ 0 < α ∧ α < 2/λ_max`,
`richardson_opt : IsLeast/argmin … = 2/(λ_min+λ_max)`, `ρ_opt` value. Backbone:
`Stationary.Splitting.richardson a hα` (`m = α⁻¹ • 1`), `richardson_iterationOperator : G = 1 − α • a`
(`Splitting.lean`); the optimal-parameter analysis is `plans/backbone.md` §2.3.5 (phase 2,
"Richardson with optimal parameter (Saad Ex 4.1, AH Ex 5.2.3)"). Route: spectral mapping for
affine polynomials (Mathlib `spectrum.sub_singleton`/`smul`), elementary real optimization.
Class: `direct` for the step form; `deferred` (§3 item 5) for the spectral analysis, optional as
`surface-only` meanwhile.

**R-4.15 Definition 4.3 / Theorem 4.4 (regular splittings).** Book: `M, N` regular splitting of
`A` (`M` nonsingular, `M⁻¹ ≥ 0`, `N ≥ 0`): `ρ(M⁻¹N) < 1` iff `A` nonsingular and `A⁻¹ ≥ 0`;
consequently the iteration (4.34) converges whenever `A` is an M-matrix.
Lean: `thm_4_4 (h : A.IsRegularSplitting M N) : complexSpectralRadius (M⁻¹ * N) < 1 ↔ IsUnit A ∧ ∀ i j, 0 ≤ A⁻¹ i j`;
`converges_of_isMMatrix (hA : A.IsMMatrix) (h : A.IsRegularSplitting M N) : ∀ b x₀, Tendsto (iterates of M⁻¹N x + M⁻¹b) atTop (𝓝 (A⁻¹ *ᵥ b))`.
Backbone: `plans/backbone.md` §2.3.4 (phase 2; Thm 1.29 and the weak Perron theorem), §2.1.12;
R-4.11. Class: `deferred` (§3 item 3). The M-matrix corollary is `direct` from Thm 4.4 + R-4.11
(only Def 1.30 is used, not Thm 1.31–1.32).

**R-4.16 `|λ_i| ≤ ‖A‖`.** Book: for any matrix norm, every eigenvalue satisfies `|λ| ≤ ‖A‖`
(text before Thm 4.6). Lean: `norm_le_lpOpNorm_of_mem_spectrum (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ ≤ lpOpNorm p A`;
general `AlgebraNorm` version. Backbone/Mathlib: `spectrum.norm_le_norm_of_mem` /
`spectrum.spectralRadius_le_nnnorm` on `PiLp p _ →L[ℂ] PiLp p _`, with
`spectrum_toLpLin : spectrum ℂ (toContinuousLinearMap (toLpLin p p A)) = spectrum ℂ A`
(surface; `Matrix.toLpLinAlgEquiv`, `AlgEquiv.spectrum_eq`). The backbone's
`Matrix.complexSpectralRadius_le_of_norm` is stated under `NormMulClass` (a *multiplicative* norm,
`‖AB‖ = ‖A‖‖B‖`), which no operator norm on `Matrix (Fin n) (Fin n) ℝ` with `n ≥ 2` satisfies, so
it is not used here. Class: `direct` for every `lpOpNorm p` (via `complexify` for real `A`),
`deferred` (§3 item 2) for a general consistent norm.

**R-4.17 Theorem 4.6 (Gershgorin).** Book: every eigenvalue `λ` of `A` lies in some closed disc
`|λ − a_ii| ≤ ρ_i = Σ_{j≠i} |a_ij|`; the column-sum version holds too (transpose). Lean:
`thm_4_6 (A : Matrix _ _ ℂ) (hμ : μ ∈ spectrum ℂ A) : ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ univ.erase i, ‖A i j‖`;
`thm_4_6_col`. Backbone/Mathlib: `eigenvalue_mem_ball` (on `HasEigenvalue (toLin' A)`),
`Module.End.hasEigenvalue_iff_mem_spectrum`, `Matrix.spectrum_toLin'`, `charpoly_transpose`; the
union form `Matrix.spectrum_subset_iUnion_closedBall` (`Numlib/Eigen/Perturbation.lean`).
Class: `direct`.

**R-4.18 Theorem 4.7.** Book: `A` irreducible, eigenvalue `λ` on the boundary of the union of the
`n` Gershgorin discs ⇒ `λ` lies on the boundary of every disc, `|λ − a_ii| = ρ_i ∀ i`.
Lean: `thm_4_7 (hA : IsIrreducible A) (hμ : μ ∈ spectrum ℂ A) (hb : μ ∈ frontier (⋃ i, closedBall (A i i) (ρ i))) : ∀ i, ‖μ - A i i‖ = ρ i`.
Backbone: `plans/backbone.md` §2.3.3 (irreducible dominance is phase 2). Route: the book's path
argument along the strongly connected quiver of `A.map ‖·‖` (`Matrix.isIrreducible_iff_exists_pow_pos`
or the `IsSStronglyConnected` paths). Class: `deferred` (§3 item 4).

**R-4.19 Corollary 4.8.** Book: strictly diagonally dominant or irreducibly diagonally dominant ⇒
nonsingular. Lean: `cor_4_8_strict (h : A.IsStrictDiagDominant) : IsUnit A` (+ column form),
`cor_4_8_irred (h : IsIrreduciblyRowDiagDominant A) : IsUnit A`. Backbone:
`Matrix.IsStrictDiagDominant.isUnit`, `IsStrictColDiagDominant.transpose_iff`
(`Numlib/LinearSolve/Stationary/DiagDominant.lean`); Mathlib `det_ne_zero_of_sum_row_lt_diag`,
`det_ne_zero_of_sum_col_lt_diag`. Class: `direct` (strict), `deferred` (§3 item 4; irreducible, via
R-4.18).

**R-4.20 Theorem 4.9.** Book: `A` strictly diagonally dominant or irreducibly diagonally dominant
⇒ the Jacobi and Gauss–Seidel iterations converge for any `x₀`.
Lean: `thm_4_9_jacobi (h : A.IsStrictDiagDominant ∨ IsIrreduciblyRowDiagDominant A) (b x₀) : Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))`,
`thm_4_9_gs` likewise; column-dominance versions (`Matrix.IsStrictColDiagDominant`) as separate
theorems (see §5 on Def 4.5). Backbone: `Matrix.jacobi_spectralRadius_lt_one`,
`gaussSeidel_spectralRadius_lt_one`, `jacobi_spectralRadius_lt_one_of_col` (over ℂ;
`DiagDominant.lean`), `linfty_opNorm_jacobi_iterMatrix`; `Matrix.complexify` and the glue
`complexify_diagPart/strictLower/strictUpper/inv` (`Basic.lean`); R-4.11. Route:
`complexSpectralRadius (jacobiSplitting A h).iterationOperator = spectralRadius ℂ (jacobiSplitting (complexify A) h').iterationOperator`
and `(complexify A).IsStrictDiagDominant ↔ A.IsStrictDiagDominant` (`Complex.norm_real`), then
R-4.11 (⇒) with `x* = A⁻¹b`. Class: `needs-equivalence` (strict row; strict column for Jacobi),
`deferred` (§3 item 4) for Gauss–Seidel under column dominance and for the irreducible variants.

**R-4.21 Theorem 4.10.** Book: `A` symmetric with positive diagonal, `0 < ω < 2`: SOR converges for
any `x₀` iff `A` is positive definite. (As printed, "converges" must mean convergence to the
solution for every right-hand side, equivalently `ρ(G_ω) < 1`: for singular positive
semidefinite `A` and `b = 0` the iterates converge for every `x₀` — see §5.)
Lean: `thm_4_10 (hs : A.IsSymm) (hd : ∀ i, 0 < A i i) (hω : 0 < ω) (hω2 : ω < 2) : complexSpectralRadius (sorSplitting A h hω').iterationOperator < 1 ↔ A.IsPositiveReal`
(`h : IsUnit (diagPart A)` from `hd`, `hω' : ω ≠ 0` from `hω`) and, via R-4.11,
`(∀ f x₀, ∃ x, Tendsto …) ↔ A.PosDef`. Backbone: `plans/backbone.md` §2.3.5
(phase 2) Householder–John / Ostrowski–Reich (`A` symmetric coercive, `M + Mᴴ − A` coercive ⇒
`ρ(M⁻¹N) < 1`) gives (⇐) with `M = ω⁻¹D − E`, `M + Mᵀ − A = (2/ω − 1)D`; the converse (⇒) is
§3 item 5. Class: `deferred`.

**R-4.22 Proposition 4.12.** Book: `B = [[0, B₁₂],[B₂₁, 0]]`, `L`, `U` its strict lower/upper
parts: (1) `μ` eigenvalue ⇒ `−μ` eigenvalue; (2) the eigenvalues of `B(α) = αL + α⁻¹U` (`α ≠ 0`)
are independent of `α`. Lean (index type `Fin n₁ ⊕ Fin n₂`, `B := fromBlocks 0 B₁₂ B₂₁ 0`):
`prop_4_12_neg (hμ : μ ∈ spectrum ℂ B) : -μ ∈ spectrum ℂ B`,
`prop_4_12_alpha (hα : α ≠ 0) : spectrum ℂ (α • fromBlocks 0 0 B₂₁ 0 + α⁻¹ • fromBlocks 0 B₁₂ 0 0) = spectrum ℂ B`.
Backbone: §2.3.5 (phase 2) may absorb it. Route: similarity by `fromBlocks 1 0 0 (α • 1)`
(`spectrum` invariant under conjugation, `Matrix.charpoly_units_conj`). Class: `surface-only`
(similarity argument).

**R-4.23 Definition 4.11/4.13 facts.** Book: Property A ⟺ can be symmetrically permuted to the
block form (4.42) with diagonal `D₁, D₂`; consistently ordered ⇒ Property A; T-matrices are
consistently ordered; Property A is invariant under symmetric permutations; Property A ⟺ some
symmetric permutation is consistently ordered. Lean: `hasPropertyA_iff_reindex : HasPropertyA A ↔ ∃ (σ : Equiv.Perm (Fin n)) (k : ℕ), ∀ i j, (A.reindex σ σ) i j ≠ 0 → i ≠ j → ((i : ℕ) < k ↔ ¬ ((j : ℕ) < k))`,
`hasPropertyA_of_isConsistentlyOrdered`, `isConsistentlyOrdered_of_isTMatrix`,
`hasPropertyA_reindex`, `hasPropertyA_iff_exists_reindex_isConsistentlyOrdered`. Backbone: none
(`plans/backbone.md` §8.1: surface-only). Class: `surface-only` (combinatorics of labels; the last
item is harder and optional).

**R-4.24 Proposition 4.14.** Book: `A` consistently ordered ⇒ there is a permutation `P` with
`PᵀAP` a T-matrix and `(PᵀAP)_L = PᵀA_LP`, `(PᵀAP)_U = PᵀA_UP`.
Lean: `prop_4_14 (h : IsConsistentlyOrdered A) : ∃ σ : Equiv.Perm (Fin n), IsTMatrix (A.reindex σ σ) ∧ strictLower (A.reindex σ σ) = (strictLower A).reindex σ σ ∧ strictUpper … `.
Backbone: §2.3.5 (phase 2). Route: sort indices by label, stably (order-preserving within a label
class). Class: `deferred` (§3 item 5).

**R-4.25 Proposition 4.15.** Book: `B` the Jacobi matrix of a consistently ordered `A`, `L, U`
its strict lower/upper parts: eigenvalues of `αL + α⁻¹U` (`α ≠ 0`) do not depend on `α`.
Lean: `prop_4_15 (h : IsConsistentlyOrdered A) (hd : ∀ i, A i i ≠ 0) (hα : α ≠ 0) : spectrum ℂ (Bα (complexify (jacobiSplitting A h').iterationOperator) α) = spectrum ℂ (complexify (jacobiSplitting A h').iterationOperator)`.
Backbone: §2.3.5 (phase 2). Route: R-4.24 then similarity by `diag(α^{c i})`. Class: `deferred`
(§3 item 5).

**R-4.26 Theorem 4.16.** Book: `A` consistently ordered, `a_ii ≠ 0`, `ω ≠ 0`; `M_SOR` here denotes
the SOR *iteration matrix* `(I − ωL)⁻¹(ωU + (1−ω)I)` with `L = D⁻¹E`, `U = D⁻¹F`, `B = L + U`
Jacobi: if `λ ≠ 0` is an eigenvalue of `M_SOR` and `(λ + ω − 1)² = λω²μ²` then `μ` is an eigenvalue
of `B`; conversely `μ ∈ σ(B)` and (4.46) ⇒ `λ ∈ σ(M_SOR)`.
Lean: `thm_4_16_mp (h) (hd) (hω : ω ≠ 0) (hλ : λ ≠ 0) (hλG : λ ∈ spectrum ℂ G_ω) (hμ : (λ + ω - 1)^2 = λ * ω^2 * μ^2) : μ ∈ spectrum ℂ B`,
`thm_4_16_mpr (h) (hd) (hω) (hμB : μ ∈ spectrum ℂ B) (hλ : (λ + ω - 1)^2 = λ * ω^2 * μ^2) : λ ∈ spectrum ℂ G_ω`
(`G_ω := complexify (sorSplitting A h' hω).iterationOperator`,
`B := complexify (jacobiSplitting A h').iterationOperator`).
Backbone: §2.3.5 (phase 2). Route: determinant identity `det((λ+ω−1)I − ω(λL + U)) = 0` and R-4.25
with `α = λ^{1/2}` (complex square root). Class: `deferred` (§3 item 5).

**R-4.27 (4.47) optimal `ω`.** Book: "this theorem allows us to compute an optimal `ω`, which can be
shown to be `ω_opt = 2/(1 + √(1 − ρ(B)²))`" (Young; needs `B` with real eigenvalues and
`ρ(B) < 1`). Lean: `omega_opt (h) (hd) (hreal : spectrum ℂ B ⊆ range ofReal) (hρ : ρ(B) < 1) : IsMinOn (fun ω => ρ(G_ω).toReal) (Ioo 0 2) (2 / (1 + √(1 − ρ(B)²)))` and `ρ(G_{ω_opt}) = ω_opt − 1`.
Backbone: §2.3.5 (phase 2; "`ω_opt`, `ρ_GS = ρ_J²`"). Class: `deferred` (§3 item 5; lowest
priority).

### §5.1 Basic definitions (`Ch05/Projection.lean`)

**R-5.1 (5.3)–(5.7) reformulations and matrix representation.** Book: (5.3) ⟺ (5.5)–(5.6)
with `δ = x̃ − x₀`, `r₀ = b − Ax₀`; with bases `V` of `K`, `W` of `L`, `x̃ = x₀ + Vy` satisfies the
Petrov–Galerkin condition iff `WᵀAVy = Wᵀr₀`; if `WᵀAV` is nonsingular, `x̃ = x₀ + V(WᵀAV)⁻¹Wᵀr₀`
(5.7); Algorithm 5.1 computes exactly this.
Lean: `isProjectionApprox_iff_isPetrovGalerkin` (D17), `isProjectionApprox_add_iff (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) (y) : IsProjectionApprox A b x₀ K L (x₀ + V ⬝ y) ↔ (Wᵀ * A * V) *ᵥ y = Wᵀ *ᵥ (b - A ⬝ x₀)`,
`isProjectionApprox_iff_eq_projStep (hV hW) (h : IsUnit (Wᵀ * A * V)) : IsProjectionApprox A b x₀ K L x ↔ x = projStep A b V W x₀`,
`projStep_isProjectionApprox`. Backbone: `IsPetrovGalerkin`,
`isPetrovGalerkin_iff_mulVec (V : Module.Basis ι 𝕜 K) (W : Module.Basis ι 𝕜 L) (y)`,
`IsPetrovGalerkin.eq_of_forall` (`Numlib/LinearSolve/Projection/Basic.lean`);
`Matrix.toEuclideanLin_apply_eq_sum` (`Numlib/Matrix/ToEuclideanLin.lean`). Route: instantiate the
bases form with `hV.toBasis`, `hW.toBasis`; its matrix `(⟪W i, A (V j)⟫)` is `Wᵀ A V` and
`Σ_j y j • V j = V ⬝ y` by `toEuclideanLin_apply_eq_sum`; when `Wᵀ A V` is a unit the system has the
unique solution `y = (WᵀAV)⁻¹ Wᵀ r₀`. Class: `needs-equivalence` (D6/D17).

**R-5.2 Example 5.1.** Book: an elementary Gauss–Seidel step (4.6) is a projection step with
`K = L = span{e_i}`. Lean: `gsComponentUpdate A b x i = step1 A b (e i) (e i) x` where the left side
changes only component `i` to annihilate `(b − Ax)_i`. Class: `surface-only` (definitional;
optional).

**R-5.3 Nonsingularity of `WᵀAV`.** Book: "`WᵀAV` is nonsingular iff no vector of the subspace
`AK` is orthogonal to `L`" (read as: `Au ⟂ L` for `u ∈ K` forces `u = 0`; the literal reading
"no nonzero vector of `AK` is orthogonal to `L`" fails for `A = 0` — see §5). Lean:
`isUnit_iff_forall (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) : IsUnit (Wᵀ * A * V) ↔ ∀ u ∈ K, u ≠ 0 → A ⬝ u ∉ Lᗮ`;
also `↔ ∀ b x₀, ∃! x, IsProjectionApprox A b x₀ K L x`. Backbone: the nondegeneracy hypothesis
`hKL : ∀ z ∈ K, A z ∈ Lᗮ → z = 0` of `IsPetrovGalerkin.eq_of_forall`
(`Numlib/LinearSolve/Projection/Basic.lean`) is exactly this reading; `existsUnique_isGalerkin_of_isCoercive`,
`existsUnique_isMinRes_of_injOn` are its two instances. Route: `Wᵀ A V y = 0 ↔ A (V y) ∈ Lᗮ`
(columns of `W` span `L`), `y ↦ V y` injective; the `∃!` form: existence from `projStep`
(R-5.1), uniqueness from `eq_of_forall`; conversely uniqueness for `b = A x₀` forces
`K ⊓ A⁻¹(Lᗮ) = ⊥`. Class: `needs-equivalence` (D6) / `surface-only` for the `∃!` form.

**R-5.4 Proposition 5.1.** Book: (i) `A` positive definite (Saad's sense) and `L = K`, or (ii) `A`
nonsingular and `L = AK` ⇒ `B = WᵀAV` is nonsingular for any bases `V` of `K`, `W` of `L`.
Lean: `prop_5_1_i (hA : A.IsPositiveReal) (hV : V.IsBasisOf K) (hW : W.IsBasisOf K) : IsUnit (Wᵀ * A * V)`,
`prop_5_1_ii (hA : IsUnit A) (hV : V.IsBasisOf K) (hW : W.IsBasisOf (K.map (toEuclideanLin A))) : IsUnit (Wᵀ * A * V)`.
Backbone: `existsUnique_isGalerkin_of_isCoercive (hA : A.IsCoercive)`,
`existsUnique_isMinRes_of_injOn` (`Projection/Basic.lean`), `LinearMap.IsCoercive.inner_self_pos`
(`Numlib/InnerProductSpace/Coercive.lean`). Route: R-5.3: (i) `u ∈ K`, `u ≠ 0` ⇒ `(Au, u) > 0` ⇒
`Au ∉ Kᗮ`; (ii) `Au ≠ 0`, `Au ∈ AK = L` ⇒ `Au ∉ Lᗮ`. Class: `needs-equivalence` (via R-5.3; the
book's own proof through `VᵀAV` positive definite / `(AV)ᵀAV` full rank is R-5.5).

**R-5.5 Projected matrix remarks.** Book: `A` symmetric, `L = K`, same basis ⇒ `B = VᵀAV`
symmetric; `A` SPD ⇒ `B` SPD; (in the proof of Prop 5.1) `A` positive definite ⇒ `VᵀAV` positive
definite; `A` nonsingular ⇒ `AV` full rank ⇒ `(AV)ᵀAV` nonsingular.
Lean: `isSymm_conjTranspose_mul_mul`, `posDef_transpose_mul_mul (hA : A.PosDef) (hV : LinearIndependent …)`,
`isPositiveReal_transpose_mul_mul`, `isUnit_transpose_mul_self_of_injective`. Backbone/Mathlib:
`Matrix.PosDef.conjTranspose_mul_mul_same (hA : A.PosDef) (hB : Function.Injective B.mulVec)`,
`Matrix.PosDef.conjTranspose_mul_self (A) (hA : Function.Injective A.mulVec)`
(`Mathlib/LinearAlgebra/Matrix/PosDef`). Class: `direct` (Mathlib) / `surface-only` for the
`IsPositiveReal` variant.

### §5.2 General theory

**R-5.6 Proposition 5.2.** Book: `A` SPD, `L = K`: `x̃` is the result of the orthogonal projection
method onto `K` with starting vector `x₀` iff it minimizes `E(x) = (A(x* − x), x* − x)^{1/2}` over
`x₀ + K`. Lean: `prop_5_2 (hA : A.PosDef) (hstar : A ⬝ xstar = b) : IsProjectionApprox A b x₀ K K x ↔ (x - x₀ ∈ K ∧ IsMinOn (E_A A xstar) {y | y - x₀ ∈ K} x)`.
Backbone: `IsGalerkin.iff_energyNorm_min (hA : A.IsSymmetricCoercive) (hstar) [FiniteDimensional 𝕜 K]`
(both directions; `Numlib/LinearSolve/Projection/Optimality.lean`). Route: D1/D17/D19
equivalences (`Matrix.posDef_iff_isSymmetricCoercive`, `E_A_eq_energyNorm`). Class:
`needs-equivalence`.

**R-5.7 Proposition 5.3.** Book: `A` an arbitrary square matrix, `L = AK`: `x̃` is the result of the
oblique projection method onto `K` orthogonally to `L` with starting vector `x₀` iff it minimizes
`R(x) = ‖b − Ax‖₂` over `x₀ + K` (`A` need not be nonsingular). Lean:
`prop_5_3 : IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x ↔ (x - x₀ ∈ K ∧ IsMinOn (R_A A b) {y | y - x₀ ∈ K} x)`.
Backbone: `IsMinRes.iff_isPetrovGalerkin [FiniteDimensional 𝕜 K]` (`Projection/Basic.lean`).
Class: `direct`.

**R-5.8 Proposition 5.4 and `‖r̃‖₂ ≤ ‖r₀‖₂`.** Book: `L = AK`: `r̃ = b − Ax̃ = (I − P)r₀` with `P` the
orthogonal projector onto `AK`; hence `‖r̃‖₂ ≤ ‖r₀‖₂`. Lean:
`prop_5_4 (hx : IsProjectionApprox A b x₀ K (K.map A') x) : b - A ⬝ x = (b - A ⬝ x₀) - (K.map A').starProjection (b - A ⬝ x₀)`,
`norm_residual_le_of_prop_5_4 : ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ x₀‖`. Backbone: `IsMinRes.residual_eq`,
`IsMinRes.norm_residual_le_norm_residual_zero` (`Projection/Basic.lean`) with R-5.7. Class:
`direct`.

**R-5.9 Proposition 5.5 and `‖d̃‖_A ≤ ‖d₀‖_A`.** Book: `A` SPD, orthogonal projection onto `K`:
`d̃ = x* − x̃ = (I − P_A)d₀`, `P_A` the projector onto `K` orthogonal w.r.t. the `A`-inner product
(`δ = x̃ − x₀` is the `A`-orthogonal projection of `d₀` onto `K`); hence `‖d̃‖_A ≤ ‖d₀‖_A`.
Lean: `prop_5_5_char (hA : A.PosDef) (hstar) (hx : IsProjectionApprox A b x₀ K K x) : (x - x₀) ∈ K ∧ ∀ w ∈ K, A.energyInner (xstar - x) w = 0`
(the (1.59)–(1.60) characterization in the `A`-inner product; this is the Galerkin condition
rewritten), `prop_5_5 : WithEnergy.equiv A' hA' (xstar - x) = (WithEnergy.submoduleMap A' hA' K)ᗮ.starProjection (WithEnergy.equiv A' hA' (xstar - x₀))`,
`energyNorm_le : E_A A xstar x ≤ E_A A xstar x₀`. Backbone: `IsGalerkin.energyInner_error_eq_zero`,
`IsGalerkin.error_eq_starProjection`, `IsGalerkin.energyNorm_le` (with `y = x₀`;
`Numlib/LinearSolve/Projection/Optimality.lean`); `WithEnergy.equiv`, `WithEnergy.submoduleMap`
(`Numlib/InnerProductSpace/Energy.lean`). Class: `needs-equivalence` (D3).

**R-5.10 §5.2.3 reformulation `A_m x̃ = Q b`.** Book: with `x₀ = 0` and `Q = Q_K^L` defined
(`K ∩ Lᗮ = {0}`), (5.5)–(5.6) ⟺ `x̃ ∈ K ∧ Q(b − Ax̃) = 0` ⟺ `x̃ ∈ K ∧ A_m x̃ = Qb`, `A_m = QAP_K`.
Lean: `isProjectionApprox_zero_iff_Q (hd) (h : K ⊓ Lᗮ = ⊥) : IsProjectionApprox A b 0 K L x ↔ x ∈ K ∧ Q K L hd h (b - A ⬝ x) = 0`,
`… ↔ x ∈ K ∧ A_m A K L hd h x = Q K L hd h b`. Backbone: `LinearMap.IsIdempotentElem.apply_eq_iff`
with `y = 0` (`Q x = 0 ↔ x ∈ Lᗮ`, R-1.8; `Numlib/InnerProductSpace/ObliqueProjection.lean`),
Mathlib `starProjection_eq_self_iff`. Class: `direct`.

**R-5.11 Proposition 5.6 (and its `x₀ ≠ 0` extension).** Book: `K` invariant under `A`, `x₀ = 0`,
`b ∈ K` ⇒ the approximate solution of any (oblique or orthogonal) projection method onto `K` is
exact; for `x₀ ≠ 0` the assumption is `r₀ = b − Ax₀ ∈ K`. The proof uses `Q_K^L`, so the implicit
hypothesis `K ∩ Lᗮ = {0}` is needed (see §5). Lean:
`prop_5_6 (hK : K ∈ Module.End.invtSubmodule (toEuclideanLin A)) (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) (hb : b - A ⬝ x₀ ∈ K) (hx : IsProjectionApprox A b x₀ K L x) : A ⬝ x = b`
(the book's case is `x₀ = 0`). Backbone: `IsPetrovGalerkin.eq_of_invt (hx) (hK) (hr) (hKL)`
(`Projection/Basic.lean`, the same hypotheses). Class: `direct`.

**R-5.12 Distance to `K`.** Book: for `x̃ ∈ K`, `‖x̃ − x*‖₂ ≥ ‖(I − P_K)x*‖₂` (the sine of the angle
between `x*` and `K` times `‖x*‖₂`). Lean: `norm_sub_ge_of_mem (hx : x ∈ K) : ‖(1 - K.starProjection) xstar‖ ≤ ‖x - xstar‖`.
Backbone/Mathlib: `starProjection_minimal`. Class: `direct`.

**R-5.13 Theorem 5.7.** Book: `γ = ‖Q_K^L A (I − P_K)‖₂`, `b ∈ K`, `x₀ = 0`: the exact solution
`x*` satisfies `‖b − A_m x*‖₂ ≤ γ ‖(I − P_K)x*‖₂`. Lean:
`thm_5_7 (hd) (h : K ⊓ Lᗮ = ⊥) (hb : b ∈ K) (hstar : A ⬝ xstar = b) : ‖b - A_m A K L hd h xstar‖ ≤ ‖(Q ∘L A' ∘L (1 - K.starProjection) : E n →L[ℝ] E n)‖ * ‖(1 - K.starProjection) xstar‖`.
Backbone: none needed — `Q b = b` for `b ∈ K` (`IsIdempotentElem.apply_eq_iff`) gives
`b − A_m x* = Q A (x* − P_K x*) = (Q A (1 − P_K)) x*`, then `‖T x‖ ≤ ‖T‖ ‖x‖`
(`ContinuousLinearMap.le_opNorm`). Class: `surface-only` (two lines).

**R-5.14 Matrix interpretation of Thm 5.7.** Book: `L = K`, `V` orthonormal basis, `W = V`:
`b = VVᵀb` and (5.11) reads `‖Vᵀb − (VᵀAV)Vᵀx*‖₂ ≤ γ ‖(I − P_K)x*‖₂` (since
`‖V(Vᵀb − (VᵀAV)Vᵀx*)‖₂ = ‖Vᵀb − (VᵀAV)Vᵀx*‖₂`). Lean: `thm_5_7_matrix (hV : Vᵀ * V = 1) (hV' : V.IsBasisOf K) (hb : b ∈ K) (hstar) : ‖Vᵀ *ᵥ b - (Vᵀ * A * V) *ᵥ (Vᵀ *ᵥ xstar)‖ ≤ γ * ‖(1 - K.starProjection) xstar‖`.
Backbone: R-1.12 (`VVᵀ = P_K`), `compression.toMatrix_orthonormalBasis`
(`Numlib/InnerProductSpace/Compression.lean`: `VᵀAV` is the matrix of
`compression (toEuclideanLin A) K` in the orthonormal basis `V.cols`), `‖V y‖ = ‖y‖` for isometric
`V`. Class: `needs-equivalence`.

### §5.3 One-dimensional projection processes (`Ch05/OneDimensional.lean`)

**R-5.15 (5.12).** Book: `K = span{v}`, `L = span{w}`: the new approximation is `x + αv` with
`α = (r, w)/(Av, w)`. Lean: `step1_isProjectionApprox (h : inner ℝ w (A ⬝ v) ≠ 0) : IsProjectionApprox A b x (span {v}) (span {w}) (step1 A b v w x)`
and `isProjectionApprox_span_singleton_iff (h) : IsProjectionApprox A b x (span {v}) (span {w}) x' ↔ x' = step1 A b v w x`.
Backbone: `Projection.step1_isPetrovGalerkin (v w x) (h : ⟪w, A v⟫ ≠ 0)`
(`Numlib/LinearSolve/Projection/OneDimensional.lean`); the `iff` from
`IsPetrovGalerkin.eq_of_forall` (`hKL` for `span {v}`, `span {w}` is `⟪w, A v⟫ ≠ 0`). Class:
`direct` (D19's `step1_eq` is `rfl`).

**R-5.16 Algorithm 5.2 and its line-minimization property.** Book: SD (`A` SPD): `v = w = r`;
Alg 5.2 with the recursive residual `r ← r − αp`, `p = Ar`; each step minimizes
`f(x) = ‖x − x*‖_A²` over `x + αd` with `d = −∇f = 2r` (negative gradient direction).
Lean: `sdAlg_spec (k) : ((sdAlgStep A)^[k] ⟨x₀, b - A ⬝ x₀, A ⬝ (b - A ⬝ x₀)⟩).x = (sdStep A b)^[k] x₀ ∧ ….r = b - A ⬝ (…) ∧ ….p = A ⬝ (….r)`,
`sdStep_isMinOn (hA : A.PosDef) (hstar) : IsMinOn (fun x' => E_A A xstar x' ^ 2) {x + α • r | α : ℝ} (sdStep A b x)`,
`gradient_energy (hA : A.IsSymm) : HasGradientAt (fun x => E_A A xstar x ^ 2) (2 • (A ⬝ (x - xstar))) x` (optional).
Backbone: `Projection.steepestDescentStep`, `steepestDescentStep_isGalerkin (x) (hA : A.IsCoercive)`
(`OneDimensional.lean`), R-5.6 with `K = span{r}`. Class: `surface-only` (bookkeeping, same
pattern as the backbone's `CG.residual_eq`) + `direct` (minimization via Prop 5.2).

**R-5.17 Lemma 5.8 (Kantorovich).** Book: `B` real SPD, `λ_max, λ_min` its extreme eigenvalues:
`(Bx,x)(B⁻¹x,x)/(x,x)² ≤ (λ_max + λ_min)²/(4λ_maxλ_min)` for all `x ≠ 0`. Lean:
`lemma_5_8 [Nonempty (Fin n)] (hB : B.PosDef) (hx : x ≠ 0) : ((B *ᵥ x) ⬝ᵥ x) * ((B⁻¹ *ᵥ x) ⬝ᵥ x) / (x ⬝ᵥ x) ^ 2 ≤ (lambdaMax hB.1 + lambdaMin hB.1) ^ 2 / (4 * lambdaMax hB.1 * lambdaMin hB.1)`.
Backbone: `Projection.kantorovich_inequality (hl : 0 < lmin) (hA : A.IsSymmetricBoundedBy lmin lmax)
(x) (hy : A y = x) : re ⟪A x, x⟫ * re ⟪y, x⟫ ≤ (lmax + lmin)² / (4 lmax lmin) * ‖x‖⁴`
(`Numlib/LinearSolve/Projection/OneDimensional.lean`, inverse-free). Route:
`hA` from `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hB.1` with the extreme
eigenvalues (`Numlib/Matrix/ToEuclideanLin.lean`), `0 < λ_min` from `Matrix.PosDef.eigenvalues_pos`,
`y := B⁻¹ *ᵥ x` with `hy` from `Matrix.mul_nonsing_inv`; divide by `(x ⬝ᵥ x)² = ‖x‖⁴`. No inverse
glue is needed. Class: `needs-equivalence`.

**R-5.18 Theorem 5.9.** Book: `A` SPD: the `A`-norms of the errors `d_k = x* − x_k` of Alg 5.2
satisfy `‖d_{k+1}‖_A ≤ ((λ_max − λ_min)/(λ_max + λ_min)) ‖d_k‖_A`, and Alg 5.2 converges for any
`x₀`. Lean: `thm_5_9 [Nonempty (Fin n)] (hA : A.PosDef) (hstar : A ⬝ xstar = b) (k) : E_A A xstar ((sdStep A b)^[k+1] x₀) ≤ (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) * E_A A xstar ((sdStep A b)^[k] x₀)`;
`thm_5_9_tendsto : Tendsto (fun k => (sdStep A b)^[k] x₀) atTop (𝓝 xstar)`. Backbone:
`Projection.energyNorm_steepestDescentStep_le (hl : 0 < lmin) (hA : IsSymmetricBoundedBy lmin lmax) (hstar) (x)`
(`OneDimensional.lean`); `LinearMap.IsCoerciveWith.norm_le_energyNorm` (`√c ‖x‖ ≤ ‖x‖_A`,
`Numlib/InnerProductSpace/Energy.lean`) for the convergence. Route: contraction factor `< 1`
(since `λ_min > 0`), geometric decay `E_A(x_k) ≤ ρ^k E_A(x₀)`, then `‖x* − x_k‖ ≤ E_A(x_k)/√λ_min`
(surface `Tendsto` corollary, `tendsto_pow_atTop_nhds_zero_of_lt_one`). Class:
`needs-equivalence`.

**R-5.19 Algorithm 5.3 and its minimization property.** Book: MR (`A` positive definite,
`A + Aᵀ` SPD): `v = r`, `w = Ar`, `α = (Ar, r)/(Ar, Ar)`; Alg 5.3 (`α = (p, r)/(p, p)`, `p = Ar`);
each step minimizes `f(x) = ‖b − Ax‖₂²` in the direction `r`. Lean: `mrAlg_spec`,
`mrStep_isMinOn : IsMinOn (fun x' => R_A A b x' ^ 2) {x + α • r | α} (mrStep A b x)` (via R-5.7 with
`K = span{r}`). Backbone: `Projection.minResStep`, `minResStep_isMinRes (x) (hA : A.IsCoercive)`
(`OneDimensional.lean`). Class: `surface-only` + `direct`.

**R-5.20 Theorem 5.10.** Book: `A` real positive definite, `μ = λ_min((A + Aᵀ)/2)`, `σ = ‖A‖₂`:
the residuals of Alg 5.3 satisfy `‖r_{k+1}‖₂ ≤ (1 − μ²/σ²)^{1/2} ‖r_k‖₂`, and Alg 5.3 converges for
any `x₀`. Lean (scoped `Matrix.Norms.L2Operator`):
`thm_5_10 [Nonempty (Fin n)] (hA : A.IsPositiveReal) (k) : ‖b - A ⬝ ((mrStep A b)^[k+1] x₀)‖ ≤ Real.sqrt (1 - lambdaMin (hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) * ‖b - A ⬝ ((mrStep A b)^[k] x₀)‖`;
`thm_5_10_tendsto : Tendsto (fun k => (mrStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ ⬝ b))`. Backbone:
`Projection.norm_residual_minResStep_le {A : E →L[𝕜] E} (hc : 0 < c) (hA : IsCoerciveWith c) (b x)`
(`OneDimensional.lean`; `‖r'‖ ≤ √(1 − c²/‖A‖²) ‖r‖`), R-1.2 (`c = μ`, i.e. `IsCoerciveWith μ`
from `thm_1_34'`), `Matrix.l2_opNorm_eq_norm_toEuclideanLin` (`Numlib/Matrix/ToEuclideanLin.lean`),
`Matrix.toEuclideanCLM`. Route: `0 < μ ≤ σ` so the factor is `< 1`; `r_k → 0` and
`x_k = A⁻¹(b − r_k)`. Class: `needs-equivalence`.

**R-5.21 (5.16)–(5.18), (5.20) and the `sin ∠` form.** Book: `‖r_{k+1}‖₂² = ‖r_k‖₂²(1 − (Ar,r)/(r,r) · (Ar,r)/(Ar,Ar))`
(5.18); `‖r_{k+1}‖₂² ≤ (1 − μ(A)μ(A⁻¹))‖r_k‖₂²` with `μ(B) = λ_min((B + Bᵀ)/2)` (5.20), using
`(Ax,x)/(Ax,Ax) ≥ λ_min((A⁻¹ + A⁻ᵀ)/2) > 0` ("`A⁻¹` is also positive definite");
`‖r_{k+1}‖₂² = ‖r_k‖₂² sin²∠_k`, `cos∠_k = (Ar_k, r_k)/(‖Ar_k‖₂‖r_k‖₂)`; the convergence factor is
bounded by `ρ = max_{x≠0} sin∠(x, Ax) < 1`.
Lean: `norm_sq_mrStep (hr : A ⬝ r ≠ 0) : ‖b - A ⬝ mrStep A b x‖^2 = ‖r‖^2 * (1 - inner (A ⬝ r) r / inner r r * (inner (A ⬝ r) r / inner (A ⬝ r) (A ⬝ r)))`,
`isPositiveReal_inv (hA : A.IsPositiveReal) : A⁻¹.IsPositiveReal`,
`eq_5_20 : ‖r_{k+1}‖^2 ≤ (1 - lambdaMin (hermitianPart_isHermitian A) * lambdaMin (hermitianPart_isHermitian A⁻¹)) * ‖r_k‖^2`,
`norm_sq_mrStep_eq_sin_sq`, `norm_mrStep_le_sup_sin (hA) : ‖r_{k+1}‖ ≤ ρ * ‖r_k‖ ∧ ρ < 1` with
`ρ := ⨆ x : {x // x ≠ 0}, Real.sin (InnerProductGeometry.angle x (A ⬝ x))` (compactness of the unit
sphere for `ρ < 1`). Backbone: only the bound (5.15) (`norm_residual_minResStep_le`, and the
damped-Richardson estimate `ContinuousLinearMap.norm_sub_smul_apply_sq_le` in
`Numlib/InnerProductSpace/Coercive.lean` behind it); the exact identity (5.18) and (5.20) are
two-line inner-product identities. Class: `surface-only` (§3 item 7 notes (5.18) as a candidate
for `OneDimensional.lean`).

**R-5.22 Algorithm 5.4 (RNSD) and its convergence.** Book: `v = Aᵀr`, `w = Av`, `α = ‖v‖₂²/‖Av‖₂²`
(5.21); Alg 5.4 with the recursive residual; each step minimizes `f(x) = ‖b − Ax‖₂²` along
`−∇f = 2Aᵀr`; the method is SD applied to the normal equations `AᵀAx = Aᵀb`, and since `AᵀA` is
SPD for nonsingular `A`, it converges whenever `A` is nonsingular (by Thm 5.9).
Lean: `rnsdAlg_spec`, `rnsdStep_eq_sdStep_normal : rnsdStep A b x = sdStep (Aᵀ * A) (Aᵀ ⬝ b) x`,
`rnsdStep_isMinOn : IsMinOn (fun x' => R_A A b x' ^ 2) {x + α • (Aᵀ ⬝ r) | α} (rnsdStep A b x)`,
`posDef_transpose_mul_self (hA : IsUnit A) : (Aᵀ * A).PosDef`,
`thm_rnsd (hA : IsUnit A) : ‖r_{k+1}‖ ≤ (λ_max(AᵀA) − λ_min(AᵀA))/(λ_max + λ_min) * ‖r_k‖ ∧ Tendsto x_k (𝓝 (A⁻¹ ⬝ b))`
(the `AᵀA`-norm of the error is the residual norm). Backbone: `Projection.residualNormSDStep`
(`OneDimensional.lean`; SD on the normal equations is a one-line corollary), R-5.18, Mathlib
`Matrix.PosDef.conjTranspose_mul_self`. Class: `direct` (via R-5.18) + `surface-only` (algebraic
identities).

### §5.4 Additive and multiplicative processes (`Ch05/Additive.lean`)

**R-5.23 Block relaxations are projection processes.** Book: each inner step of Alg 4.1/4.2 is an
orthogonal projection process over `K_i = span(V_i)`; (4.17) is exactly (5.7) with `W = V = V_i`.
Lean: `blockCorrection_eq_projStep : x + V_i *ᵥ (V_iᵀ A V_i)⁻¹ *ᵥ (V_iᵀ *ᵥ (b − A x)) = projStep A b (V_i) (V_i) x`
(no overlap, `η = 1`). Class: `surface-only` (definitional).

**R-5.24 (5.22)–(5.23) residual of the additive procedure.** Book: `r_{k+1} = (I − Σ_i P_i) r_k`
with `P_i = AV_i(V_iᵀAV_i)⁻¹V_iᵀ`; with parameters `ω_i`, `r_{k+1} = (I − Σ ω_i P_i) r_k`; each `P_i`
is the projector onto `span(AV_i)` orthogonal to `span(V_i)`.
Lean: `residual_additiveStep (h : ∀ i, IsUnit ((V i)ᵀ * A * V i)) : b - A ⬝ additiveStep 𝒱 ω A b x = (1 - ∑ i, ω i • toEuclideanLin (P_i 𝒱 A i)) (b - A ⬝ x)`,
`P_i_isProjOnto (hV : (V i).IsBasisOf K_i) (h) : ∀ z, IsProjOnto (K_i.map A') K_i z (P_i ⬝ z)`.
Backbone: `plans/backbone.md` §2.4.4 (phase 2) for the abstract residual formula; D6/R-1.9 now
(`P_i = obliqueProj (A * V i) (V i)`, `range_obliqueProjectionOfBases`,
`sub_obliqueProjectionOfBases_apply_mem_orthogonal`; `IsBasisOf (A * V i) (K_i.map A')` follows
from `IsUnit (V_iᵀAV_i)`). Class: `surface-only` for the identity (one line of algebra),
`deferred` (§3 item 6) for the equivalence with §2.4.4.

**R-5.25 Least-squares option and exactness.** Book: with `L_i = AK_i`, `P_i = AV_i((AV_i)ᵀAV_i)⁻¹(AV_i)ᵀ`
is the orthogonal projector onto `AK_i`, `r_{k+1} = (I − ΣP_i)r_k`; if the `AV_i` are mutually
orthogonal and the total rank of the `P_i` is `n`, then `I − ΣP_i = 0` and the exact solution is
obtained in one outer step; the maximal reduction occurs when the `V_i` are `A`-orthogonal.
Lean: `obliqueProj_self_isOrthogonalProjector (hV : V.IsBasisOf M) : (obliqueProj V V).IsOrthogonalProjector ∧ range … = M`,
`sum_starProjection_eq_one (horth : ∀ i ≠ j, (A V_i)ᵀ (A V_j) = 0) (hrank : ∑ i, rank (A V_i) = n) : ∑ i, (K_i.map A').starProjection = 1`.
Backbone/Mathlib: D7; `OrthogonalFamily`/`DirectSum.IsInternal` for the sum. Class: `surface-only`
(the sum lemma is a candidate for §2.4.4, §3 item 6).

**R-5.26 Algorithm 5.6.** Book: multiplicative procedure = successive projection steps on
`K_1, …, K_p`; it is the analogue of block Gauss–Seidel. Lean: `multiplicativeSweep_eq_blockGs`
(when `V_i` are identity columns). Class: `surface-only` (definitional).

## 3. Deferred backbone items

Backbone items this chapter needs that are scheduled for later phases (`plans/backbone.md` §7),
with the exact statements the surface will specialize. Everything else in §2 is available in the
phase-1 modules under `Numlib/`.

1. **Real-matrix Gelfand transport (`Numlib/Matrix/Complexify.lean`, phase 2).**
   `l2_opNorm_complexify : ‖complexify A‖ = ‖A‖` under the scoped `Matrix.Norms.L2Operator`
   norms (and the `Operator`/Frobenius analogues), so that Mathlib's Gelfand formula on
   `Matrix n n ℂ` yields `Tendsto (fun k => ‖G^k‖₂ ^ (1/k)) atTop (𝓝 ρ(G))` for real `G`
   (R-4.13 `tendsto_generalFactor`), and the attainment `∃ d₀ ≠ 0, limsup (‖Gᵏd₀‖/‖d₀‖)^{1/k} = ρ(G)`
   (real and imaginary parts of a dominant complex eigenvector). Proof of the norm identity:
   `≥` by real vectors; `≤` by `‖A(x + iy)‖² = ‖Ax‖² + ‖Ay‖² ≤ ‖A‖² (‖x‖² + ‖y‖²)`. An alternative
   that avoids norm identities: "Gelfand's limit does not depend on the norm" (`C^{1/k} → 1` for
   equivalent norms).
2. **Arbitrary consistent matrix norms (`Numlib/Analysis/SpectralRadius.lean`, phase 2).** Saad's
   Cor 4.2 and the remark `|λ| ≤ ‖A‖` quantify over *any* matrix norm (Saad §1.5: a vector norm on
   `ℂ^{n×n}` with `‖AB‖ ≤ ‖A‖‖B‖`), i.e. an `AlgebraNorm ℝ (Matrix n n ℝ)` /
   `AlgebraNorm ℂ (Matrix n n ℂ)` (Mathlib `Mathlib/Analysis/Normed/Unbundled/AlgebraNorm`).
   Statement: `spectralRadius_le_algebraNorm (N : AlgebraNorm ℂ A) [FiniteDimensional ℂ A] (a) :
   spectralRadius ℂ a ≤ N a` (proof: `ρ(a)ᵏ ≤ ‖aᵏ‖_std ≤ C·N(aᵏ) ≤ C·N(a)ᵏ`, `C^{1/k} → 1`, using
   that every seminorm on a finite-dimensional space is bounded by the standard norm) with the
   real-matrix corollary `N G < 1 → Tendsto (G^k) (𝓝 0)`. Until then Cor 4.2 and R-4.16 are
   stated for the induced `p`-norms (`lpOpNorm p`). Note that `Matrix.complexSpectralRadius_le_of_norm`
   assumes `NormMulClass` (multiplicative norms) and therefore does not cover operator norms.
3. **Regular splittings and M-matrices (`Stationary/RegularSplitting.lean`, `Matrix/Order.lean`;
   `plans/backbone.md` §2.3.4, §2.1.12, phase 2).** Thm 4.4 exactly as
   `IsRegularSplitting A M N → (complexSpectralRadius (M⁻¹ * N) < 1 ↔ IsUnit A ∧ ∀ i j, 0 ≤ A⁻¹ i j)`
   with the entrywise order spelled out (or with the §2.1.12 order plus an unfolding lemma), via
   Thm 1.29 and the weak Perron theorem; the M-matrix definition should follow Saad Def 1.30
   verbatim (D14).
4. **Irreducibility and column dominance (`Stationary/DiagDominant.lean`; §2.3.3, phase 2).**
   (a) Saad's irreducibility applies to arbitrary matrices; Mathlib's `Matrix.IsIrreducible`
   requires nonnegative entries. Adopt `Matrix.IsIrreducible (A.map ‖·‖)` (D15) as the backbone
   definition so that Thm 4.7, Cor 4.8 (irreducible part) and Thm 4.9 (irreducible part) can be
   stated. (b) Gauss–Seidel convergence under strict *column* dominance (Def 4.5 as printed uses
   column sums, §5), via the Cor 4.8 argument applied to `N − λM` for `|λ| ≥ 1` — this argument
   also proves the irreducible case, so it may be the cheapest uniform proof. (Jacobi under column
   dominance is `Matrix.jacobi_spectralRadius_lt_one_of_col`.)
5. **SPD and SOR theory (`Stationary/SPD.lean`; §2.3.5, phase 2).** (a) Richardson with the
   optimal parameter (Ex 4.1, R-4.14). (b) Thm 4.10 in both directions: Householder–John /
   Ostrowski–Reich (`M + Mᴴ − A` coercive ⇒ `ρ(M⁻¹N) < 1`) and the converse — `A` symmetric,
   `Q := M + Mᵀ − A` positive definite, `ρ(M⁻¹N) < 1` ⇒ `A` positive definite (proof: the identity
   `e_kᵀAe_k − e_{k+1}ᵀAe_{k+1} = (e_k − e_{k+1})ᵀQ(e_k − e_{k+1}) ≥ 0` with `e_k → 0` forces
   `e₀ᵀAe₀ ≥ 0`, and `= 0` with `e₀ ≠ 0` would force `e₁ = e₀`, contradicting `e_k → 0`).
   (c) Young's theory, stated over ℂ after `complexify` and reusing the D16 definitions verbatim:
   Prop 4.12 (block anti-diagonal: spectrum symmetric under negation; `spectrum (αL + α⁻¹U) =
   spectrum B`), Prop 4.14 (order-preserving permutation to a T-matrix), Prop 4.15
   (`α`-independence for consistently ordered `A`), Thm 4.16 (the relation `(λ + ω − 1)² = λω²μ²`
   both ways, with `λ ≠ 0` in the forward direction), and (4.47) under the hypotheses "Jacobi
   eigenvalues real, `ρ(B) < 1`" with the value `ρ(G_{ω_opt}) = ω_opt − 1`. Kress Def 4.13–Cor 4.16
   uses the same objects, so these are shared.
6. **Additive and multiplicative projection (`Projection/Additive.lean`; §2.4.4, phase 2).** The
   residual identity with weights `ω_i` (Saad (5.23)), the family given by matrices `V_i` as in D20
   (so that `P_i = obliqueProj (A V_i) V_i` is `rfl`), the least-squares variant, the lemma
   "orthogonal projectors onto mutually orthogonal subspaces of total dimension `n` sum to `1`"
   (R-5.25), and block Jacobi/GS (Alg 4.1–4.2, D12, R-4.7) as instances.
7. **Optional candidates (no phase assigned; surface-only meanwhile).** First-order perturbation in
   `Numlib/LinearSolve/Perturbation.lean`: the `IsLittleO` form of (1.76) derived once from
   `relative_error_le_condNumber`, and differentiability of `ε ↦ (A + εE)⁻¹(b + εe)` at `0` with
   derivative `A⁻¹(e − Ex)` (R-1.17; Kress Thm 5.3 and Higham Ch. 7 state the same). Exact one-step
   identities in `Projection/OneDimensional.lean`: `‖r'‖² = ‖r‖²(1 − ⟪Ar,r⟫²/(‖r‖²‖Ar‖²))` for
   the MR step (5.18) and `‖d'‖_A² = ‖d‖_A²(1 − ⟪r,r⟫²/(⟪Ar,r⟫⟪A⁻¹r,r⟫))` for the SD step (R-5.21),
   plus the generic "per-step contraction with factor `< 1` ⇒ `Tendsto` to the solution" corollary
   used three times here (Thm 5.9, Thm 5.10, RNSD).

## 4. Left out

Algorithms without theorems, examples, exercises (with the reason), and the Chapter 1 black boxes.

* Figures 1.1–1.2, 4.1–4.5, 5.1–5.4: illustrations.
* Example 1.3 (`A = [[1, 1],[10⁴, 1]]` eigenvalue rectangle), Example 1.4 (2×2 existence cases):
  numerical examples; Example 1.5 is kept as optional R-1.20 because `plans/backbone.md` §2.1.2
  assigns it to the surface.
* Example 5.2 (`A = [[0, I],[I, I]]`, `WᵀAV` singular although `A` is nonsingular): a
  counterexample; could be a one-line `surface-only` sanity check, not required.
* §1.13.2 the sentence "for large matrices the determinant is almost never a good indication":
  discussion.
* §4.1 mesh/line-relaxation blocking (Figures 4.2–4.3, mesh 2.5 partitions): PDE-specific
  bookkeeping, no statement.
* §4.1.2 the two procedures for computing `w = M⁻¹Av` and the sparsity discussion: algorithmic
  remarks.
* §4.2.1 specific convergence factor via the Jordan form (the asymptotics
  `‖d_k‖ ≈ C|λ|^{k−p+1}C(k,p−1)` and "`ρ = ρ(G)`" for a specific `d₀`): heuristic (`≈`), depends on
  the Jordan form which the backbone deliberately avoids; the rigorous parts are R-4.13.
* §4.2.5 the SOR-with-adaptive-`ω` procedure after (4.47): algorithm without a theorem.
* Algorithms 4.1–4.2, 5.1, 5.5–5.6 are formalized only as functions (D12, D17, D20); Algorithms
  5.2–5.4 as functions plus the residual-bookkeeping lemmas needed by Thm 5.9/5.10.
* All exercises (P-1.1–P-1.37, P-5.1–P-5.17). Cited by the selected text: P-1.15 (real
  `(Au,u)` on ℂⁿ forces Hermitian — remark in §1.11, not used), P-1.17 (PD ⟺ Hermitian part PD —
  this is R-1.1/R-1.2), P-1.18 (`B`-self-adjoint examples — optional R-1.5), P-1.30
  (`V₁V₁ᴴ = V₂V₂ᴴ` — R-1.12), P-1.37 (`A + εE` nonsingular for small `ε` — R-1.17), P-1.10
  (Gelfand — Mathlib, `Numlib/Analysis/SpectralRadius.lean`), P-5.1 (Exercise 1 referenced in
  Example 5.1), P-5.15 (referenced after (5.23)). None is a theorem prerequisite beyond what the
  results in §2 state.
* The `B`-inner-product remark "sometimes an HPD `B` makes `A` Hermitian" (R-1.5): kept optional.

Chapter 1 black boxes cited by the selected sections (where the backbone provides them):

| Cited fact | Used by | Provided by |
|---|---|---|
| Thm 1.10 (`Aᵏ → 0 ⟺ ρ(A) < 1`), Thm 1.11 (Neumann series, `I − A` nonsingular), Thm 1.12 / P-1.10 (Gelfand `lim ‖Aᵏ‖^{1/k} = ρ`) | Thm 4.1, Cor 4.2, §4.2.1 convergence factors | `spectralRadius_lt_one_iff_tendsto_pow`, `summable_pow_iff_spectralRadius_lt_one`, `isUnit_one_sub_of_spectralRadius_lt_one` (`Numlib/Analysis/SpectralRadius.lean`); `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` (`Numlib/Matrix/Complexify.lean`) for real matrices; Gelfand via Mathlib (§3 item 1 for real matrices) |
| `ρ(A) ≤ ‖A‖` for any matrix norm (§1.5/§1.8.4) | Cor 4.2, `|λ| ≤ ‖A‖` | Mathlib `spectrum.spectralRadius_le_nnnorm` for the induced `p`-norms; general consistent norms: §3 item 2 |
| Jordan canonical form (Thm 1.8) | §4.2.1 specific convergence factor | not provided (deliberately, `plans/backbone.md` §1.1); left out |
| Schur form (Thm 1.9) | not cited in the selected sections | not in Mathlib; a phase-3 backbone item |
| Normal matrices / spectral theorem for Hermitian matrices (Thm 1.14, 1.19–1.20: "unitarily similar to a real diagonal matrix") | Lemma 5.8 proof, Thm 1.34/1.35 proofs | Mathlib `Matrix.IsHermitian.spectral_theorem`, `eigenvalues`, `eigenvectorBasis` |
| Min–max / Rayleigh-quotient bounds (Thm 1.21, (1.40)) | Thm 1.34 (`α = λ_min(H)`), Thm 1.35, Thm 5.10 | `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin` (`Numlib/Matrix/ToEuclideanLin.lean`), `LinearMap.IsSymmetricBoundedBy.rayleigh_mem_Icc` (`Numlib/InnerProductSpace/Coercive.lean`); Mathlib `hasEigenvalue_iInf/iSup_of_finiteDimensional` |
| Perron–Frobenius (Thm 1.25), Thm 1.29 (`B ≥ 0`: `ρ(B) < 1 ⟺ (I−B)⁻¹ ≥ 0`) | Thm 4.4 | `plans/backbone.md` §2.3.4 phase 2 (weak Perron; §3 item 3) |
| M-matrices (Def 1.30; Thm 1.31–1.33 not needed) | remark after Thm 4.4 | D14 (definition only) |
| Irreducibility (§1.10 / §3 adjacency graph) | Def 4.5, Thm 4.7, Cor 4.8, Thm 4.9 | Mathlib `Matrix.IsIrreducible` via `A.map ‖·‖` (§3 item 4) |
| (1.13.1) existence theory | §1.13 | Mathlib |
| Exercise 37 (`A + εE` invertible for small `ε`) | §1.13.2 | `Units.isUnit_add_of_norm_lt` (`Numlib/Analysis/NormedRing/Inverse.lean`) |

## 5. Readings of the book's statements

Places where the printed statement is ambiguous, or false as literally read, and how the surface
states it.

1. **Definition 4.5.** As printed, all three dominance conditions read
   `|a_jj| ≥ Σ_{i=1, i≠j}^{n} |a_ij|, j = 1,…,n` — the sum runs over the *row* index `i` with the
   column `j` fixed (column sums). The proofs of Thm 4.6 (4.37)–(4.38) and Thm 4.9 use row sums
   `Σ_{j≠i} |a_ij|`, and Cor 4.8's proof again writes the column form; the second edition is known
   to have this index swap. The surface provides both conventions (D15) and states Cor 4.8/Thm 4.9
   for both; Thm 4.6 is stated in row form with a column corollary.
2. **Theorem 4.16.** The book reuses `M_SOR` for the SOR *iteration matrix*
   `(D − ωE)⁻¹(ωF + (1−ω)D)`, whereas (4.26) uses `M_SOR` for the preconditioner
   `ω⁻¹(D − ωE)`; the surface names them `(sorSplitting A h hω).iterationOperator` vs `M_sor`.
3. **Orthogonal projector norm (§1.12.4).** "`‖P‖₂ = 1` for any orthogonal projector" needs
   `P ≠ 0` (`P = 0` is an orthogonal projector onto `{0}`); stated with `P ≠ 0` (R-1.13), as in the
   backbone's `ContinuousLinearMap.IsIdempotentElem.norm_eq_one_iff_isSymmetric`.
4. **Corollary 1.39.** "`min_{y∈M} ‖x − y‖₂ = ‖x − y*‖₂` iff `y* ∈ M` and `x − y* ⟂ M`" is read with
   `y*` ranging over `M` (a `y* ∉ M` at the same distance would break the literal "iff"); the
   surface uses `IsLeast` over `M`, which includes membership (R-1.15).
5. **§5.1.2 "`WᵀAV` is nonsingular iff no vector of `AK` is orthogonal to `L`".** Literally false
   for `A = 0` (`AK = {0}`); read as "`u ∈ K`, `u ≠ 0` ⇒ `Au ∉ Lᗮ`" (R-5.3), which is the
   backbone's nondegeneracy hypothesis `∀ z ∈ K, A z ∈ Lᗮ → z = 0`.
6. **Proposition 5.6.** The proof presupposes that `Q_K^L` exists (`K ∩ Lᗮ = {0}`); without it the
   statement fails, so the hypothesis is added (R-5.11), exactly as in the backbone's
   `IsPetrovGalerkin.eq_of_invt`. Its proof also says "`x̃` is a nonzero vector in `K`", which is
   not needed.
7. **Theorem 4.10.** "SOR converges for any `x₀`" must be read as `ρ(G_ω) < 1` / convergence to the
   solution for every right-hand side: for singular positive semidefinite symmetric `A` with
   positive diagonal (e.g. the all-ones `2×2` matrix, `ω = 1`, `b = 0`) the iterates converge for
   every `x₀` although `A` is not positive definite (R-4.21).
8. **Prop 5.1 proof** cites "see Chapter 1" for "`A` positive definite ⇒ `VᵀAV` positive definite";
   no numbered statement there covers the non-symmetric case — R-5.5 supplies it.
