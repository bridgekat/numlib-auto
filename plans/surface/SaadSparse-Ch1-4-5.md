# Surface plan: Saad, Iterative Methods — §1.11–1.13, §4.1–4.2, Ch. 5

Surface library `SaadSparse` (Lake lib, `srcDir = "Surface"`, imports only `Numlib`) for the second
edition of Saad, *Iterative Methods for Sparse Linear Systems*, sections §1.11 (positive-definite
matrices), §1.12 (projectors), §1.13 (linear systems, conditioning), §4.1 (Jacobi/GS/SOR/SSOR,
block variants), §4.2 (convergence: Thm 4.1–4.16) and Ch. 5 (projection methods, Prop 5.1–Thm 5.10,
§5.4). Statements are kept in the book's generality — real `n × n` matrices in Ch. 4–5 and §1.11
(Thm 1.35 complex), complex in §1.12, `RCLike 𝕜` in §1.13 — with the book's own definitions
(Saad's non-symmetric "positive definite", projectors given by bases `V, W`, the splitting
`A = D − E − F`, matrix `p`-norms). Every proof is meant to be a specialization of a backbone item
(`plans/backbone.md`, cited by section number) through an equivalence lemma for the book-specific
definition; §4 lists what the backbone does not yet provide. Written from the high-quality OCR text;
a handful of statements were type-checked with `sorry` (`Scratch1.lean` next to this file; all
elaborate, one `def` needs `noncomputable`).

Conventions (shared file `Surface/SaadSparse/Basic.lean`):
* `n : ℕ`; vectors of ℝⁿ/ℂⁿ are `EuclideanSpace 𝕜 (Fin n)` (Mathlib's ℝⁿ with the Euclidean norm),
  abbreviated `E𝕜 n`; matrices `Matrix (Fin n) (Fin n) 𝕜`; the action `A x` is `toEuclideanLin A x`
  (local notation `A ⬝ x`); componentwise statements use `Fin n → 𝕜`, `A *ᵥ x`, `x ⬝ᵥ y`, and the
  glue `toEuclideanLin A x = WithLp.toLp 2 (A *ᵥ x.ofLp)` (`rfl`, checked).
* Saad's inner product `(x, y) = Σ x_i ȳ_i` is `inner 𝕜 y x` (Mathlib's is conjugate-linear in the
  first slot); over ℝ they coincide, and every complex statement below is written so that only
  `re`, `‖·‖` or `⟪·,·⟫ = 0` matters.
* `λ_min(H)`, `λ_max(H)` for Hermitian `H` are `Finset.univ.inf'/sup' _ hH.eigenvalues`
  (`Matrix.IsHermitian.eigenvalues`), so `[Nonempty (Fin n)]` (`n ≥ 1`) appears where the book
  uses them.
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

## Book-specific definitions

Each entry: book formulation; proposed Lean surface definition; backbone counterpart
(`backbone.md` §); equivalence lemma.

**D1. Positive definite / positive real (1.48).** Real `A` with `(Au, u) > 0 ∀ u ∈ ℝⁿ, u ≠ 0`
(no symmetry). SPD = symmetric + (1.48); HPD = Hermitian + `(Au,u) > 0` on ℂⁿ.
```lean
def Matrix.IsPositiveReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u : Fin n → ℝ, u ≠ 0 → 0 < (A *ᵥ u) ⬝ᵥ u
abbrev Matrix.IsSPD (A : Matrix (Fin n) (Fin n) ℝ) : Prop := A.IsSymm ∧ A.IsPositiveReal
```
Backbone: 2.1.4 `LinearMap.IsCoercive`, `LinearMap.IsSymmetricCoercive`, Mathlib `Matrix.PosDef`.
Equivalences: `isPositiveReal_iff_isCoercive : A.IsPositiveReal ↔ (toEuclideanLin A).IsCoercive`
(via 2.1.4 `LinearMap.isCoercive_iff_pos` and the glue `inner (A ⬝ x) x = (A *ᵥ x) ⬝ᵥ x`);
`isSPD_iff_posDef : A.IsSPD ↔ A.PosDef` (Mathlib `posDef_iff_dotProduct_mulVec`, `star` trivial on ℝ);
`isHPD_iff_posDef` for the complex Hermitian case (`re (star u ⬝ᵥ A *ᵥ u) > 0` ↔ Mathlib's
`ComplexOrder` positivity); `posDef_iff_isSymmetricCoercive` is 2.1.4.

**D2. Hermitian and skew-Hermitian parts (1.49)–(1.51).** `H = (A + Aᴴ)/2`, `S = (A − Aᴴ)/(2i)`,
`A = H + iS`.
```lean
def Matrix.hermitianPart (A : Matrix (Fin n) (Fin n) 𝕜) := (2⁻¹ : 𝕜) • (A + Aᴴ)
noncomputable def Matrix.skewPart (A : Matrix (Fin n) (Fin n) ℂ) := (2 * Complex.I)⁻¹ • (A - Aᴴ)
```
(`skewPart` only over ℂ: over ℝ `1/(2i)` is junk; the skew-Hermitian part `(A − Aᴴ)/2` is defined
over `𝕜`.) Backbone/Mathlib: `selfAdjointPart 𝕜`, `skewAdjointPart 𝕜` (`Mathlib/Algebra/Star/Module`)
with `⅟2`. Equivalence: `hermitianPart_eq_selfAdjointPart : A.hermitianPart = (selfAdjointPart 𝕜 A : Matrix _ _ 𝕜)`;
`hermitianPart_isHermitian`, `skewPart_isHermitian`, `eq_hermitianPart_add_I_smul_skewPart` (1.49).
The surface `λ_min (hermitianPart_isHermitian A)` is the `c` of 2.1.4
`IsSymmetricCoercive.coercive_const_eq_iInf_eigenvalues` / 4.1 Rayleigh bounds.

**D3. Energy (`B`-) inner product (1.57), `B`-self-adjointness.** For SPD/HPD `B`,
`(x, y)_B := (Bx, y)`; "`A` is Hermitian w.r.t. `(·,·)_B`" iff `(Ax, y)_B = (x, Ay)_B ∀ x y`.
```lean
def Matrix.energyInner (B : Matrix (Fin n) (Fin n) 𝕜) (x y : E𝕜 n) : 𝕜 := inner 𝕜 y (B ⬝ x)
def Matrix.IsSelfAdjointWrt (B A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ x y, B.energyInner (A ⬝ x) y = B.energyInner x (A ⬝ y)
```
Backbone: 2.1.5 `energyInner`, `energyNorm`, `WithEnergy A hA` (`InnerProductSpace` instance).
Equivalence: `energyInner_eq : B.energyInner x y = starRingEnd 𝕜 (energyInner (toEuclideanLin B) x y)`
(equal over ℝ); "(1.57) is a proper inner product" is the `InnerProductSpace 𝕜 (WithEnergy _ hB)`
instance, transported through `posDef_iff_isSymmetricCoercive`.

**D4. Projector, range and null space (§1.12.1).** A projector is an idempotent linear map of ℂⁿ.
```lean
abbrev Matrix.IsProjector (P : Matrix (Fin n) (Fin n) ℂ) : Prop := IsIdempotentElem P   -- P * P = P
-- Ran P := LinearMap.range (toEuclideanLin P), Null P := LinearMap.ker (toEuclideanLin P)
```
Backbone/Mathlib: `IsIdempotentElem`, `LinearMap.IsProj`, `IsIdempotentElem.isCompl`,
`IsIdempotentElem.eq_projection`, `Submodule.projection`. Equivalence: `isProjector_iff_isIdempotentElem_toEuclideanLin`
(`toEuclideanLin` is an algebra equivalence, `Matrix.toEuclideanCLM`).

**D5. Projector onto `M` orthogonal to `L` (1.59)–(1.60).** `u = Px` iff `u ∈ M` and `x − u ⟂ L`.
```lean
def IsProjOnto (M L : Submodule 𝕜 (E𝕜 n)) (x u : E𝕜 n) : Prop := u ∈ M ∧ x - u ∈ Lᗮ
```
Backbone: 2.1.7 `obliqueProjection K L : E →ₗ[𝕜] E` (range `K`, kernel `Lᗮ`, defined for
finite-dimensional `K, L` of equal dimension with `K ⊓ Lᗮ = ⊥`) and its characterization
`P x ∈ K ∧ x − P x ∈ Lᗮ`. Equivalence: `isProjOnto_iff_eq_obliqueProjection :
IsProjOnto M L x u ↔ u = obliqueProjection M L x` under `M ⊓ Lᗮ = ⊥`, `finrank M = finrank L`.
Orthogonal projector = the case `L = M`: `IsProjOnto M M x u ↔ u = M.starProjection x`
(Mathlib `eq_starProjection_of_mem_orthogonal`).

**D6. Bases and matrix representation (1.63)–(1.66).** `V = [v₁,…,v_m]` basis of `M`,
`W` basis of `L`; biorthogonal iff `WᴴV = I`; `P = VWᴴ` (1.65), in general `P = V(WᴴV)⁻¹Wᴴ` (1.66).
```lean
structure Matrix.IsBasisOf (V : Matrix (Fin n) (Fin m) 𝕜) (M : Submodule 𝕜 (E𝕜 n)) : Prop where
  linearIndependent : LinearIndependent 𝕜 fun j => (WithLp.toLp 2 (Vᵀ j) : E𝕜 n)   -- columns
  span_eq : Submodule.span 𝕜 (Set.range fun j => (WithLp.toLp 2 (Vᵀ j) : E𝕜 n)) = M
def IsBiorthogonal (V W : Matrix (Fin n) (Fin m) 𝕜) : Prop := Wᴴ * V = 1
noncomputable def obliqueProj (V W : Matrix (Fin n) (Fin m) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  V * (Wᴴ * V)⁻¹ * Wᴴ
```
Backbone: 2.1.7 `obliqueProjection`; the "matrix representation with bases" lemma requested in §4
(needed by 2.4.1 (5.7) as well). Equivalence: `toEuclideanLin_obliqueProj :
hV.IsBasisOf M → hW.IsBasisOf L → IsUnit (Wᴴ * V) → toEuclideanLin (obliqueProj V W) = obliqueProjection M L`,
and `isUnit_conjTranspose_mul_iff : IsUnit (Wᴴ * V) ↔ ∀ v ∈ M, v ∈ Lᗮ → v = 0` (with `Matrix.IsBasisOf`
on both sides; the same matrix `Fin m` on both). Orthonormal case: `Vᴴ * V = 1` (`V` "unitary
`n × m`"), `obliqueProj V V = V * Vᴴ`.

**D7. Orthogonal projector (1.67).** `Null P = (Ran P)ᗮ`; equivalently `Px ∈ M ∧ (I − P)x ⟂ M`.
```lean
def Matrix.IsOrthogonalProjector (P : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  IsIdempotentElem P ∧ LinearMap.ker (toEuclideanLin P) = (LinearMap.range (toEuclideanLin P))ᗮ
```
Backbone/Mathlib: `Submodule.starProjection`, `LinearMap.IsSymmetricProjection`,
`IsIdempotentElem.isSymmetric_iff_orthogonal_range`. Equivalence:
`isOrthogonalProjector_iff_eq_starProjection : P.IsOrthogonalProjector ↔ toEuclideanLin P = (range (toEuclideanLin P)).starProjection`
and `↔ (toEuclideanLin P).IsSymmetricProjection`.

**D8. Condition number, matrix `p`-norms (§1.13.2).** `κ(A) = ‖A‖‖A⁻¹‖` w.r.t. a matrix norm;
`κ_p(A) = ‖A‖_p ‖A⁻¹‖_p` for the norms induced by the vector `p`-norms.
```lean
/-- `‖A‖_p`: operator norm of `x ↦ A x` on `PiLp p (fun _ : Fin n => 𝕜)`. (checked) -/
noncomputable def Matrix.lpOpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (toLpLin p p A)‖
noncomputable def Matrix.condNumberLp (p) [Fact (1 ≤ p)] (A) : ℝ := lpOpNorm p A * lpOpNorm p A⁻¹
```
Backbone: 2.1.2 `NormedRing.condNumber` (`‖a‖ ‖Ring.inverse a‖`), scoped `Matrix.Norms.L2Operator`
(`κ₂`) and `Matrix.Norms.Operator` (`κ_∞`); 2.2 perturbation bounds on `E ≃L[𝕜] E`.
Equivalences: `lpOpNorm_two : lpOpNorm 2 A = ‖A‖` (scoped `L2Operator`; `Matrix.l2_opNorm_def`),
`lpOpNorm_top : lpOpNorm ⊤ A = ‖A‖` (scoped `Operator`; `linfty_opNorm_eq_opNorm`),
`lpOpNorm_one_eq_transpose : lpOpNorm 1 A = lpOpNorm ⊤ Aᵀ` (surface), and
`condNumberLp_eq_condNumber : condNumberLp p A = NormedRing.condNumber (toContinuousLinearMap (toLpLin p p A))`
(`Matrix.nonsing_inv_eq_ringInverse`, `ContinuousLinearEquiv.condNumber_eq`).

**D9. The splitting `A = D − E − F` (4.2) and the point relaxations (4.4)–(4.9).** `D` diagonal,
`−E` strict lower, `−F` strict upper part; diagonal entries nonzero.
```lean
def D (A : Matrix (Fin n) (Fin n) ℝ) := Matrix.diagPart A            -- backbone 2.3.2 ✓
def E (A) := -Matrix.strictLower A
def F (A) := -Matrix.strictUpper A
/-- (4.4) componentwise Jacobi step. -/
def jacobiStep (A) (b x : Fin n → ℝ) : Fin n → ℝ := fun i => (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i
/-- (4.8); the componentwise form (4.7) is a theorem about it (it is recursive in `i`). -/
noncomputable def gsStep (A) (b x) : Fin n → ℝ := (D A - E A)⁻¹ *ᵥ (F A *ᵥ x + b)
noncomputable def backwardGsStep (A) (b x) := (D A - F A)⁻¹ *ᵥ (E A *ᵥ x + b)             -- (4.9)
noncomputable def symmetricGsStep (A) (b) := backwardGsStep A b ∘ gsStep A b
```
Backbone: 2.3.2 `Matrix.diagPart/strictLower/strictUpper` (✓), `Matrix.jacobiSplitting`,
`gaussSeidelSplitting`, `Ring.Splitting.iterMatrix`, 2.3.1 `Stationary.step G f x = G x + f`.
Equivalences: `jacobiStep_eq : jacobiStep A b = Stationary.step (jacobiSplitting A h).iterMatrix ((D A)⁻¹ *ᵥ b)`
(as maps on `Fin n → ℝ`, i.e. (4.4) = (4.5)); `gsStep_eq` with `gaussSeidelSplitting`;
`backwardGsStep_eq` (request: a `backwardGaussSeidelSplitting`, or the general constructor from any
unit `M` with `N := M − A`); `decomp : A = D A - E A - F A` (4.2).

**D10. General splitting and iteration matrix (4.10)–(4.11), (4.18)–(4.23).** `A = M − N`, `M`
nonsingular; `x_{k+1} = M⁻¹N x_k + M⁻¹ b`; `G = M⁻¹N = I − M⁻¹A`, `f = M⁻¹b`; `M` is the
preconditioner, `M⁻¹Ax = M⁻¹b` the preconditioned system.
```lean
abbrev Splitting (A : Matrix (Fin n) (Fin n) ℝ) := Ring.Splitting A        -- backbone 2.3.2, fields m n eq isUnit
def affineStep (G : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) := G *ᵥ x + f   -- (4.18)/(4.28) (checked)
noncomputable def Splitting.step (s : Splitting A) (b) : (Fin n → ℝ) → (Fin n → ℝ) :=
  affineStep s.iterMatrix (s.m⁻¹ *ᵥ b)                                         -- (4.22)
```
Backbone: 2.3.2 `Ring.Splitting`, `iterMatrix`, `iterMatrix_eq : G = 1 − m⁻¹ a`, consistency lemma;
2.3.1 `Stationary.step`. Equivalence: `affineStep G f = Stationary.step (toEuclideanCLM …)` is
definitional up to the `EuclideanSpace` synonym; `G_JA`, `G_GS` (4.19)–(4.20) are
`(jacobiSplitting A h).iterMatrix`, `(gaussSeidelSplitting A h).iterMatrix` by `iterMatrix_eq`.

**D11. SOR and SSOR (4.12)–(4.14), (4.26)–(4.27).** `ωA = (D − ωE) − (ωF + (1−ω)D)`;
SOR: `(D − ωE)x_{k+1} = [ωF + (1−ω)D]x_k + ωb`; relaxation form `ξ_i^{(k+1)} = ω ξ_i^{GS} + (1−ω)ξ_i^{(k)}`;
SSOR = SOR sweep then backward SOR sweep, `G_ω`, `f_ω` (4.13)–(4.14),
`f_ω = ω(2−ω)(D − ωF)⁻¹D(D − ωE)⁻¹b`; `M_SOR = ω⁻¹(D − ωE)`, `M_SSOR = (ω(2−ω))⁻¹(D − ωE)D⁻¹(D − ωF)`.
```lean
noncomputable def sorStep (A) (ω : ℝ) (b x) := (D A - ω • E A)⁻¹ *ᵥ ((ω • F A + (1 - ω) • D A) *ᵥ x + ω • b)
noncomputable def backwardSorStep (A) (ω) (b x) := (D A - ω • F A)⁻¹ *ᵥ ((ω • E A + (1 - ω) • D A) *ᵥ x + ω • b)
noncomputable def ssorStep (A) (ω) (b) := backwardSorStep A ω b ∘ sorStep A ω b
noncomputable def G_ssor (A) (ω) := (D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ * (ω • F A + (1 - ω) • D A)
noncomputable def f_ssor (A) (ω) (b) := ω • (D A - ω • F A)⁻¹ *ᵥ ((1 + (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹) *ᵥ b)
noncomputable def M_sor (A) (ω) := ω⁻¹ • (D A - ω • E A)
noncomputable def M_ssor (A) (ω) := (ω * (2 - ω))⁻¹ • (D A - ω • E A) * (D A)⁻¹ * (D A - ω • F A)
```
Backbone: 2.3.2 `Matrix.sorSplitting ω` (`m = ω⁻¹(D − ωE)`), `ssorSplitting ω`.
Equivalences: `sorStep_eq : sorStep A ω b = (sorSplitting A ω h).step b` (`ω ≠ 0`);
`M_sor_eq : M_sor A ω = (sorSplitting A ω h).m`; `ssorStep_eq_affine : ssorStep A ω b x = G_ssor A ω *ᵥ x + f_ssor A ω b`;
`ssorStep_eq : ssorStep A ω b = (ssorSplitting A ω h).step b` and
`M_ssor_eq : M_ssor A ω = (ssorSplitting A ω h).m` (`ω ≠ 0, 2`) — this needs the backbone to prove
`ssorSplitting.iterMatrix = G_ssor` (request G6).

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
Backbone: 2.3.2 says block splittings and Alg 4.1–4.2 are phase 2 via 2.4.4 `Projection/Additive`.
Equivalence (once 2.4.4 exists): `blockJacobiStep = additiveProjectionStep` with
`K_i = span (V_i)`, `L_i = span (W_i)`; the non-overlapping identity "`(4.17)` is
`x_{k+1} = D⁻¹(E+F)x_k + D⁻¹b` with block `D, E, F`" is a surface-only rewrite.

**D13. Spectral radius of a real matrix; convergence factor and rate (§4.2.1).**
`ρ(G)`; specific factor `ρ = lim (‖d_k‖/‖d₀‖)^{1/k}`, rate `τ = −ln ρ`; general factor
`φ = lim (max_{x₀} ‖d_k‖/‖d₀‖)^{1/k}`.
```lean
noncomputable def spectralRadiusReal (G : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (G.map (algebraMap ℝ ℂ))                        -- (checked); = backbone 2.1.11 `Matrix.spectralRadius`
noncomputable def specificFactor (G) (d₀ : E n) : ℝ := limsup (fun k => (‖(G^k) ⬝ d₀‖ / ‖d₀‖) ^ (1/k : ℝ)) atTop
noncomputable def generalFactor (G) : ℝ := limsup (fun k => (⨆ d₀ : {d // d ≠ 0}, ‖(G^k) ⬝ d₀‖ / ‖d₀‖) ^ (1/k : ℝ)) atTop
```
Backbone: 2.1.11 `Matrix.spectralRadius` (complexification), 2.1.3 Gelfand, 2.3.1 "convergence
factor is the spectral radius". Equivalence: `spectralRadiusReal = Matrix.spectralRadius` (rfl);
`iSup_norm_div_eq_opNorm : ⨆ d₀ ≠ 0, ‖G^k d₀‖/‖d₀‖ = ‖G^k‖₂` (Mathlib `opNorm` characterization).
The book defines the factors as limits; the surface uses `limsup` and proves the limit exists in
the general case (Gelfand). See R-4.5.

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
(both checked.) Backbone: 2.3.4 `Stationary/RegularSplitting.lean` (phase 2), 2.1.12 entrywise
order (phase 2). Equivalence: `isRegularSplitting_iff` with whatever bundle 2.3.4 introduces (the
surface deliberately spells out `∀ i j, 0 ≤ …` to avoid Mathlib's Loewner `≤` on `Matrix`).

**D15. Diagonal dominance (Def 4.5), irreducibility.** Weakly / strictly / irreducibly
diagonally dominant. As printed, Def 4.5 sums over the *row* index `i` with `j` fixed
(`|a_jj| ≥ Σ_{i≠j} |a_ij|`, i.e. column sums), while Thm 4.6/4.9 proofs use row sums (see §6);
the surface provides both and states Thm 4.9 for both.
```lean
def IsRowDiagDominant (A : Matrix (Fin n) (Fin n) 𝕜) : Prop := ∀ i, ∑ j ∈ univ.erase i, ‖A i j‖ ≤ ‖A i i‖
def IsStrictRowDiagDominant (A) : Prop := ∀ i, ∑ j ∈ univ.erase i, ‖A i j‖ < ‖A i i‖      -- (checked)
def IsColDiagDominant / IsStrictColDiagDominant  -- `Aᵀ` versions
/-- Saad's irreducibility (adjacency graph strongly connected), for arbitrary matrices. -/
def IsIrreducible (A : Matrix (Fin n) (Fin n) 𝕜) : Prop := Matrix.IsIrreducible (A.map fun a => ‖a‖)   -- (checked)
def IsIrreduciblyRowDiagDominant (A) : Prop :=
  IsIrreducible A ∧ IsRowDiagDominant A ∧ ∃ i, ∑ j ∈ univ.erase i, ‖A i j‖ < ‖A i i‖
```
Backbone: 2.3.3 `Matrix.IsStrictDiagDominant` (row ✓, "column variant"), Mathlib
`Matrix.IsIrreducible` (nonnegative matrices only — hence the `A.map ‖·‖` trick: `toQuiver` has an
arrow `i ⟶ j` iff `0 < ‖A i j‖` iff `A i j ≠ 0`). Equivalence: `isStrictRowDiagDominant_iff :
IsStrictRowDiagDominant A ↔ Matrix.IsStrictDiagDominant A` (rfl).

**D16. Property A (Def 4.11), consistent ordering (Def 4.13), T-matrices, `B(α)`.**
```lean
def HasPropertyA (A : Matrix (Fin n) (Fin n) ℝ) : Prop := ∃ c : Fin n → Bool, ∀ i j, i ≠ j → A i j ≠ 0 → c i ≠ c j
/-- Def 4.13: labels `c` (the partition `S₁, …, S_p`) with adjacent `i, j` in consecutive sets,
`c j = c i + 1` if `j > i`, `c j = c i − 1` if `j < i`. -/
def IsConsistentlyOrdered (A) : Prop :=
  ∃ c : Fin n → ℤ, ∀ i j, i ≠ j → (A i j ≠ 0 ∨ A j i ≠ 0) → c j = c i + (if i < j then 1 else -1)
/-- T-matrix (Example 4.2): block tridiagonal w.r.t. consecutive index blocks, diagonal blocks diagonal. -/
def IsTMatrix (A) : Prop := ∃ (p : ℕ) (c : Fin n → Fin p), Monotone c ∧
  ∀ i j, A i j ≠ 0 → (c i = c j → i = j) ∧ ((c i : ℕ) ≤ c j + 1 ∧ (c j : ℕ) ≤ c i + 1)
def Bα (B : Matrix (Fin n) (Fin n) ℂ) (α : ℂ) := α • strictLower B + α⁻¹ • strictUpper B   -- Prop 4.12/4.15
```
(both `Prop` defs checked.) Backbone: 2.3.5 (phase 2) "Young's SOR theory (Prop 4.12–Thm 4.16,
Kress Def 4.13–Cor 4.16)"; §8.1 marks the definitions surface-only. Equivalence: to whatever
combinatorial bundle 2.3.5 introduces (request G8 asks it to reuse these definitions verbatim).

**D17. Projection step (5.2)/(5.3), (5.5)–(5.6); matrix form (5.7); Alg 5.1.** "Find
`x̃ ∈ x₀ + K` with `b − Ax̃ ⟂ L`", `K, L` `m`-dimensional subspaces of ℝⁿ; orthogonal (`L = K`) vs
oblique; with bases `V, W`: `x̃ = x₀ + V(WᵀAV)⁻¹Wᵀr₀`, `r₀ = b − Ax₀`.
```lean
def IsProjectionApprox (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (K L : Submodule ℝ (E n)) (x : E n) : Prop :=
  x - x₀ ∈ K ∧ ∀ w ∈ L, inner ℝ (b - A ⬝ x) w = 0                                  -- (5.5)–(5.6) (checked)
noncomputable def projStep (A) (b) (V W : Matrix (Fin n) (Fin m) ℝ) (x : E n) : E n :=
  x + toEuclideanLin (V * (Wᵀ * A * V)⁻¹ * Wᵀ) (b - A ⬝ x)                          -- (5.7)/Alg 5.1 (checked)
```
Backbone: 2.4.1 `IsPetrovGalerkin A b x₀ K L x` (`mem : x − x₀ ∈ K`, `orth : b − A x ∈ Lᗮ`),
`IsGalerkin`, `IsMinRes`, `isPetrovGalerkin_iff_toMatrix` (sketch). Equivalence:
`isProjectionApprox_iff : IsProjectionApprox A b x₀ K L x ↔ IsPetrovGalerkin (toEuclideanLin A) b x₀ K L x`
(`Submodule.mem_orthogonal'`); the dimension hypothesis `finrank K = m = finrank L` is carried by
`IsBasisOf` when bases are present.

**D18. `P_K`, `Q_K^L`, `A_m` (§5.2.3).** `P_K` orthogonal projector onto `K`, `Q_K^L` projector
onto `K` orthogonal to `L`, `A_m = Q_K^L A P_K`.
```lean
abbrev P_K (K) := K.starProjection                       -- Mathlib
abbrev Q (K L) (h : K ⊓ Lᗮ = ⊥) (hd : finrank K = finrank L) := obliqueProjection K L   -- backbone 2.1.7
noncomputable def A_m (A) (K L) … : E n →ₗ[ℝ] E n := Q K L h hd ∘ₗ toEuclideanLin A ∘ₗ K.starProjection
```
Equivalence: D5 (`IsProjOnto K L x (Q x)`), D7.

**D19. One-dimensional processes (5.12), Alg 5.2–5.4; `E(x)`, `R(x)`.** `K = span{v}`,
`L = span{w}`, `x ← x + αv`, `α = (r, w)/(Av, w)`. SD: `v = w = r`; MR: `v = r, w = Ar`;
RNSD: `v = Aᵀr, w = Av`. `E(x) = (A(x* − x), x* − x)^{1/2}`, `R(x) = ‖b − Ax‖₂`.
```lean
noncomputable def step1 (A) (b) (v w x : E n) : E n :=
  x + (inner ℝ (b - A ⬝ x) w / inner ℝ (A ⬝ v) w) • v                                 -- (5.12) (checked)
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
Backbone: 2.4.3 `Projection.step1`, `steepestDescentStep`, `minimalResidualStep`,
`residualNormSDStep`; 2.1.5 `energyNorm`. Equivalences: `step1_eq : step1 A b v w x = Projection.step1 (toEuclideanLin A) b v w x`
(inner-product orientation is immaterial over ℝ), `E_A_eq_energyNorm`, `sdAlg_x_eq : (sdAlgStep A)^[k] ⟨x₀, r₀, A r₀⟩ = ⟨(sdStep A b)^[k] x₀, b − A x_k, A r_k⟩`
(surface-only bookkeeping, same pattern as backbone `CG.residual_eq`).

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
Backbone: 2.4.4 `Projection/Additive.lean` (phase 2): residual `r_{k+1} = (1 − Σ P_i) r_k` with `P_i`
the projector onto `A K_i` orthogonal to `K_i`. Equivalence: `P_i = obliqueProj (A * V_i) V_i` (rfl),
`toEuclideanLin (P_i) = obliqueProjection (K_i.map A) K_i` (D6), `additiveStep = additiveProjectionStep`.

## Results

Fields: **Book** (faithful statement with exact hypotheses) · **Lean** (sketch) · **Backbone** ·
**Route** · **Status** (`direct` / `needs-equivalence` / `GAP` / `surface-only`).

### §1.11 Positive-definite matrices (`Ch01/PositiveDefinite.lean`)

**R-1.1 (1.49)–(1.52) Hermitian/skew decomposition.** Book: any square (real or complex) `A`
equals `H + iS` with `H = (A+Aᴴ)/2`, `S = (A−Aᴴ)/(2i)` both Hermitian, `iS` skew-Hermitian; for real
`A` and real `u`, `(Au, u) = (Hu, u)`.
Lean: `hermitianPart_isHermitian`, `skewPart_isHermitian`, `eq_hermitianPart_add_I_smul_skewPart`,
`mulVec_dotProduct_eq_hermitianPart (A : Matrix _ _ ℝ) (u) : (A *ᵥ u) ⬝ᵥ u = (A.hermitianPart *ᵥ u) ⬝ᵥ u`
(all checked). Backbone: Mathlib `selfAdjointPart`. Route: `conjTranspose` algebra. Status:
`surface-only` (definitional algebra; acceptable).

**R-1.2 Theorem 1.34.** Book: `A` real positive definite ⇒ `A` nonsingular and
`∃ α > 0, (Au, u) ≥ α ‖u‖₂² ∀ u ∈ ℝⁿ`; the proof takes `α = λ_min(H)`.
Lean: `thm_1_34 (hA : A.IsPositiveReal) : IsUnit A ∧ ∃ α > 0, ∀ u, α * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u`;
`thm_1_34' [Nonempty (Fin n)] (hA) (u) : lambdaMin (hermitianPart_isHermitian A) * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u`
(checked). Backbone: 2.1.4 `LinearMap.isCoercive_iff_pos`, `IsCoercive.injective`,
`coercive_const_eq_iInf_eigenvalues`; 4.1 Rayleigh bounds. Route: D1 equivalence gives coercivity,
injective ⇒ `IsUnit` (`mulVec_injective_iff_isUnit`); the constant via R-1.1 and the Rayleigh bound
for the Hermitian `H` (Mathlib `hasEigenvalue_iInf_of_finiteDimensional` on `toEuclideanLin H`,
plus `spectrum_eq_image_range` to identify `⨅` with `λ_min`). Status: `needs-equivalence`.

**R-1.3 Theorem 1.35 (Bendixson).** Book: any square complex `A`, `H`, `S` as above: every
eigenvalue `λ` of `A` satisfies `λ_min(H) ≤ Re λ ≤ λ_max(H)` and `λ_min(S) ≤ Im λ ≤ λ_max(S)`.
Lean: `thm_1_35 [Nonempty (Fin n)] (A : Matrix _ _ ℂ) (hμ : μ ∈ spectrum ℂ A) : lambdaMin hH ≤ μ.re ∧ μ.re ≤ lambdaMax hH ∧ lambdaMin hS ≤ μ.im ∧ μ.im ≤ lambdaMax hS`
(checked). Backbone: 4.1 `bendixson` (phase 1). Route: direct specialization once 4.1 states it
for matrices with `hermitianPart`/`skewPart` (request G13 to fix its exact form). Status: `direct`.

**R-1.4 (1.57) the `B`-inner product.** Book: `B` SPD (HPD) ⇒ `(x, y)_B = (Bx, y)` is an inner
product on ℂⁿ (Saad §1.4 axioms). Lean: `energyInner_conj_symm`, `energyInner_add_left/smul_left`,
`energyInner_self_nonneg`, `energyInner_self_eq_zero_iff` for `hB : B.PosDef`; alternatively an
`InnerProductSpace.Core` instance. Backbone: 2.1.5 `WithEnergy` instance. Route: D3 equivalence +
`posDef_iff_isSymmetricCoercive`. Status: `needs-equivalence`.

**R-1.5 `B`-self-adjoint examples.** Book: `A = B⁻¹C`, `A = CB` (`C` Hermitian, `B` HPD) are
Hermitian w.r.t. `(·,·)_B` (text remark; Exercise 18). Lean: `isSelfAdjointWrt_inv_mul`,
`isSelfAdjointWrt_mul`. Status: `surface-only` (two-line matrix algebra), optional.

### §1.12 Projection operators (`Ch01/Projectors.lean`)

**R-1.6 Projector basics (1.58).** Book: `P` projector ⇒ `I − P` projector, `Null P = Ran (I−P)`,
`Null P ∩ Ran P = {0}`, `ℂⁿ = Null P ⊕ Ran P`; conversely each direct-sum pair `(M, S)` defines a
unique projector with `Ran = M`, `Null = S`; `rank P = m ⇒ dim Ran(I−P) = n − m`.
Lean: `isProjector_one_sub`, `ker_eq_range_one_sub`, `isCompl_ker_range : IsCompl (ker P) (range P)`,
`existsUnique_projector (h : IsCompl M S) : ∃! P, IsIdempotentElem P ∧ range P = M ∧ ker P = S`,
`finrank_ker_eq`. Backbone/Mathlib: `IsIdempotentElem.isCompl`, `Submodule.projection`,
`IsIdempotentElem.eq_projection`, `LinearMap.finrank_range_add_finrank_ker`. Route: transport
through `toEuclideanLin`. Status: `direct` (Mathlib).

**R-1.7 Lemma 1.36.** Book: `M, L ⊂ ℂⁿ` of the same dimension `m`: (i) no nonzero vector of `M`
is orthogonal to `L` ⟺ (ii) for every `x` there is a unique `u` with `u ∈ M`, `x − u ⟂ L`.
Lean: `lemma_1_36 (hdim : finrank 𝕜 M = finrank 𝕜 L) : (∀ v ∈ M, v ∈ Lᗮ → v = 0) ↔ ∀ x, ∃! u, IsProjOnto M L x u`
(checked). Backbone: 2.1.7 `K ⊓ Lᗮ = ⊥ ↔ IsCompl K Lᗮ` (equal dimensions), Mathlib
`Submodule.exists_unique_add_of_isCompl`. Route: (i) ⟺ `M ⊓ Lᗮ = ⊥` ⟺ `IsCompl M Lᗮ` ⟺ (ii).
Status: `direct`.

**R-1.8 (1.62).** Book: with `M ∩ Lᗮ = {0}`, the projector `P` onto `M` orthogonal to `L` has
`Ran P = M`, `Null P = Lᗮ`, and `Px = 0 ⟺ x ⟂ L`. Lean: `range_obliqueProjection`,
`ker_obliqueProjection`, `obliqueProjection_eq_zero_iff : Q x = 0 ↔ x ∈ Lᗮ`. Backbone: 2.1.7.
Status: `direct`.

**R-1.9 Matrix representations (1.64)–(1.66).** Book: bases `V` of `M`, `W` of `L`; `Px = Vy`
with `Wᴴ(x − Vy) = 0` (1.64); biorthogonal ⇒ `P = VWᴴ` (1.65); in general `P = V(WᴴV)⁻¹Wᴴ` (1.66);
if no vector of `M` is orthogonal to `L` then `WᴴV` is nonsingular.
Lean: `obliqueProj_isProjOnto (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) (h : IsUnit (Wᴴ * V)) (x) : IsProjOnto M L x (toEuclideanLin (obliqueProj V W) x)`
(checked); `obliqueProj_of_biorthogonal : Wᴴ * V = 1 → obliqueProj V W = V * Wᴴ`;
`isUnit_conjTranspose_mul_of_inf_eq_bot : (∀ v ∈ M, v ∈ Lᗮ → v = 0) → IsUnit (Wᴴ * V)` (the
converse too); `isProjOnto_iff_conjTranspose_mul_eq (hV) : IsProjOnto M L x (V ⬝ y) ↔ Wᴴ *ᵥ (x − V *ᵥ y) = 0` (1.64).
Backbone: 2.1.7 (request G3: the bases lemma). Route: `y ↦ V y` is injective with image `M`;
`Wᴴ z = 0 ↔ z ∈ Lᗮ` (columns of `W` span `L`). Status: `needs-equivalence` (G3).

**R-1.10 Adjoint projector (1.68)–(1.70).** Book: `Pᴴ` is a projector; `Null Pᴴ = (Ran P)ᗮ`,
`Null P = (Ran Pᴴ)ᗮ`. Lean: `isIdempotentElem_conjTranspose`, `ker_conjTranspose_eq_orthogonal_range`,
`ker_eq_orthogonal_range_conjTranspose`. Backbone/Mathlib: `LinearMap.orthogonal_range`
(`T.rangeᗮ = T.adjoint.ker`), `Matrix.toLin_conjTranspose` (adjoint of `toEuclideanLin A` is
`toEuclideanLin Aᴴ`). Status: `direct` (Mathlib).

**R-1.11 Proposition 1.37.** Book: a projector is orthogonal iff it is Hermitian.
Lean: `prop_1_37 (hP : IsIdempotentElem P) : (ker (toEuclideanLin P) = (range (toEuclideanLin P))ᗮ) ↔ P.IsHermitian`
(checked). Backbone/Mathlib: `IsIdempotentElem.isSymmetric_iff_orthogonal_range`;
`Matrix.isHermitian_iff_isSymmetric` (`toEuclideanLin`). Status: `direct`.

**R-1.12 `P = VVᴴ` and its non-uniqueness.** Book: `V` `n × m` with orthonormal columns
spanning `M` ⇒ `P = VVᴴ` is the orthogonal projector onto `M`; two orthonormal bases `V₁, V₂` of
`M` give `V₁V₁ᴴ = V₂V₂ᴴ`. Lean: `isOrthogonalProjector_mul_conjTranspose (hV : Vᴴ * V = 1) (hV' : V.IsBasisOf M) : (V * Vᴴ).IsOrthogonalProjector ∧ range … = M`,
`mul_conjTranspose_eq_of_isBasisOf : V₁ * V₁ᴴ = V₂ * V₂ᴴ`. Backbone/Mathlib: D7 equivalence,
`LinearMap.IsSymmetricProjection.ext_iff` (same range ⇒ equal). Status: `needs-equivalence` (D7) —
the identity `toEuclideanLin (V * Vᴴ) = M.starProjection` is the orthonormal case of G3.

**R-1.13 Properties of orthogonal projectors (§1.12.4).** Book: `‖x‖₂² = ‖Px‖₂² + ‖(I−P)x‖₂²`,
`‖Px‖₂ ≤ ‖x‖₂`, `‖P‖₂ = 1`, eigenvalues of an orthogonal projector are `0` or `1` (range vectors
for `1`, null-space vectors for `0`). Lean: `norm_sq_eq_add (hP : P.IsOrthogonalProjector)`,
`norm_apply_le`, `l2_opNorm_eq_one (hP) (h0 : P ≠ 0)` (scoped `Matrix.Norms.L2Operator`),
`spectrum_subset_pair (hP : IsIdempotentElem P) : spectrum ℂ P ⊆ {0, 1}`, `mem_range_iff_eigen_one`.
Backbone/Mathlib: `Submodule.norm_sq_eq_add_norm_sq_starProjection`, `starProjection_norm_le`.
Route: `starProjection` API; `‖P‖₂ = 1` needs `P ≠ 0` (book says "for any orthogonal projector";
`P = 0` is a counterexample — see §6). Status: `direct` for the norm facts, `surface-only` for the
eigenvalue facts (idempotent ⇒ `μ² = μ`).

**R-1.14 Theorem 1.38.** Book: `P` the orthogonal projector onto `M`, `x ∈ ℂⁿ`:
`min_{y ∈ M} ‖x − y‖₂ = ‖x − Px‖₂`. Lean: `thm_1_38 (M) (x) : IsLeast ((fun y => ‖x - y‖) '' (M : Set _)) ‖x - M.starProjection x‖`
(checked). Backbone/Mathlib: `Submodule.starProjection_minimal` (as `⨅`), `starProjection_apply_mem`.
Status: `direct`.

**R-1.15 Corollary 1.39.** Book: `M`, `x` given: `min_{y ∈ M} ‖x − y‖₂ = ‖x − y*‖₂` iff
`y* ∈ M` and `x − y* ⟂ M`. Lean: `cor_1_39 (M) (x y) : IsLeast ((fun y => ‖x - y‖) '' M) ‖x - y‖ ↔ y ∈ M ∧ x - y ∈ Mᗮ`
(checked; `IsLeast` includes membership, which is how the book's "min over `y ∈ M`" is read — see §6).
Backbone/Mathlib: `Submodule.norm_eq_iInf_iff_inner_eq_zero (hv : v ∈ K)`. Status: `direct`.

### §1.13 Basic concepts in linear systems (`Ch01/LinearSystems.lean`)

**R-1.16 Existence (§1.13.1, Cases 1–3).** Book: `A` nonsingular ⇒ unique solution `x = A⁻¹b`;
`A` singular and `b ∈ Ran A` ⇒ infinitely many solutions (`x₀ + Null A`); `b ∉ Ran A` ⇒ none.
Lean: `existsUnique_of_isUnit (hA : IsUnit A) : ∃! x, A *ᵥ x = b` (and `= A⁻¹ *ᵥ b`),
`solutions_eq_vadd_ker (hb : ∃ x₀, A *ᵥ x₀ = b) : {x | A *ᵥ x = b} = x₀ +ᵥ ker (mulVecLin A)`,
`infinite_solutions_of_not_isUnit (hA : ¬ IsUnit A) (hb) : Set.Infinite {x | A *ᵥ x = b}`,
`not_exists_of_not_mem_range`. Backbone/Mathlib: `Matrix.mulVec_injective_iff_isUnit`,
`Matrix.mulVec_surjective_iff_isUnit`. Status: `surface-only` (elementary linear algebra, not
numerical-analysis content; acceptable).

**R-1.17 Perturbed system (1.74)–(1.75).** Book: `A` nonsingular, any `E`: `A + εE` nonsingular
for `ε` small (Exercise 37); `(A + εE)x(ε) = b + εe`, `δ(ε) = x(ε) − x = ε(A+εE)⁻¹(e − Ex)`; `x(ε)` is
differentiable at `0` with `x'(0) = A⁻¹(e − Ex)`.
Lean: `isUnit_add_smul_of_small (hA : IsUnit A) (E) : ∀ᶠ ε in 𝓝 (0:𝕜), IsUnit (A + ε • E)`;
`delta_eq (hA) (hε : IsUnit (A + ε • E)) (hx : A *ᵥ x = b) : (A + ε • E)⁻¹ *ᵥ (b + ε • e) - x = ε • (A + ε • E)⁻¹ *ᵥ (e - E *ᵥ x)`;
`hasDerivAt_perturbed_solution (hA) (hx) : HasDerivAt (fun ε : ℝ => (A + ε • E)⁻¹ *ᵥ (b + ε • e)) (A⁻¹ *ᵥ (e - E *ᵥ x)) 0`
(matrices over ℝ; `𝕜` version with `HasDerivAt` over `𝕜`). Backbone: 2.1.1 (`Units.ofNearby`,
`norm_inverse_add_le` — the eventual invertibility), Mathlib `hasFDerivAt_ring_inverse`
(`Matrix.nonsing_inv_eq_ringInverse`, scoped `Matrix.Norms.Operator` for the normed-ring
structure). Route: algebra for `δ(ε)`; chain rule for the derivative. Status: `surface-only`
(Mathlib calculus; request G10 offers it to 2.2 as "first-order perturbation of the solution map").

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
(`x ε := (A + ε • E)⁻¹ *ᵥ (b + ε • e)`; `‖·‖_p` the `PiLp p` norm). Backbone: 2.2
`relative_error_le_condNumber` (✓, stated for `E ≃L[𝕜] E`), 2.1.2. Route: instantiate with
`ΔA = ε • E`, `Δb = ε • e` on `PiLp p`; `κ/(1 − t) = κ + κt/(1−t)` gives `g ε = O(ε²)`; the first
(`‖A⁻¹‖`) form is the same specialization before using `‖b‖ ≤ ‖A‖‖x‖`. Status:
`needs-equivalence` (D8 + the `o(ε)` corollary; request G10 asks 2.2 to provide the `IsLittleO`
form once, since Kress/Higham state it too).

**R-1.19 Properties of `κ`.** Book: `κ` is scaling invariant; `κ(αI) = 1` for the standard
norms while `det(αI) = αⁿ`; `κ_p(A)` labelled by the norm. Lean: `condNumberLp_smul (hc : c ≠ 0) : condNumberLp p (c • A) = condNumberLp p A`,
`condNumberLp_smul_one (hc) : condNumberLp p (c • 1) = 1`, `one_le_condNumberLp (hA : IsUnit A)`,
`det_smul_one : det (c • (1 : Matrix (Fin n) (Fin n) 𝕜)) = c ^ n`. Backbone: 2.1.2 `condNumber_smul`,
`one_le_condNumber`. Status: `direct` (via D8), `det` fact Mathlib `det_smul`.

**R-1.20 Example 1.5.** Book: `A_n = I + α e₁ eₙᵀ`, `A_n⁻¹ = I − α e₁ eₙᵀ`,
`‖A_n‖_∞ = ‖A_n⁻¹‖_∞ = 1 + |α|`, `κ_∞(A_n) = (1 + |α|)²` (for `n ≥ 2`), all eigenvalues `1`.
Lean: `example_1_5 (hn : 2 ≤ n) : condNumberLp ⊤ (1 + α • vecMulVec (Pi.single 0 1) (Pi.single (Fin.last _) 1)) = (1 + |α|) ^ 2`
plus `spectrum ℂ A_n = {1}`. Backbone: 2.1.2 says "Saad Example 1.5 in the surface". Route:
`linfty_opNorm_def` (row sums), `charpoly` of a unipotent matrix. Status: `surface-only`
(explicit computation; optional).

**R-1.21 Residual–error relation.** Book: `x` the solution, `x̃` any approximation, `r = b − Ax̃`:
`‖x − x̃‖/‖x‖ ≤ κ(A) ‖r‖/‖b‖`. Lean: `relative_error_le (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0) (xt) : ‖x - xt‖_p / ‖x‖_p ≤ condNumberLp p A * (‖b - A *ᵥ xt‖_p / ‖b‖_p)`.
Backbone: 2.2 `relative_error_le_condNumber_mul_relative_residual`. Status: `direct` (via D8).

### §4.1 Jacobi, Gauss–Seidel and SOR (`Ch04/Splittings.lean`)

**R-4.1 (4.3)–(4.5) Jacobi.** Book: annihilating the `i`-th residual component gives (4.4)
`ξ_i^{(k+1)} = (β_i − Σ_{j≠i} a_ij ξ_j^{(k)})/a_ii`, i.e. (4.5) `x_{k+1} = D⁻¹(E+F)x_k + D⁻¹b`.
Lean: `jacobiStep_residual (h : ∀ i, A i i ≠ 0) : (b - A *ᵥ jacobiStep A b x) i = 0` — careful: (4.3)
is `(b − A x_{k+1})_i = 0` *with the other components frozen*, i.e. `jacobiStep` is characterized by
`∀ i, A i i * (jacobiStep A b x) i + ∑ j ≠ i, A i j * x j = b i`; `jacobiStep_eq_vec (h) : jacobiStep A b x = (D A)⁻¹ *ᵥ ((E A + F A) *ᵥ x) + (D A)⁻¹ *ᵥ b`.
Backbone: 2.3.2 `jacobiSplitting` (D9). Status: `needs-equivalence` (D9; the componentwise formula is
surface algebra).

**R-4.2 (4.6)–(4.8) Gauss–Seidel.** Book: (4.6) with updated components, (4.7) componentwise,
`b + Ex_{k+1} − Dx_{k+1} + Fx_k = 0`, (4.8) `x_{k+1} = (D−E)⁻¹Fx_k + (D−E)⁻¹b`.
Lean: `gsStep_spec (h) : (D A - E A) *ᵥ gsStep A b x = F A *ᵥ x + b` (4.6 in vector form),
`gsStep_apply (h) (i) : gsStep A b x i = (-(∑ j ∈ Iio i, A i j * gsStep A b x j) - ∑ j ∈ Ioi i, A i j * x j + b i) / A i i` (4.7),
`gsStep_eq_vec : gsStep A b x = (D A - E A)⁻¹ *ᵥ (F A *ᵥ x) + (D A - E A)⁻¹ *ᵥ b` (4.8).
Backbone: 2.3.2 `gaussSeidelSplitting`. Route: `D − E` is lower triangular with nonzero diagonal,
`IsUnit` from `det` of a triangular matrix (`Matrix.det_of_lowerTriangular`); (4.7) is the forward
substitution identity. Status: `needs-equivalence` (D9) for (4.8); `surface-only` for (4.7).

**R-4.3 (4.9) backward and symmetric GS.** Book: `(D − F)x_{k+1} = Ex_k + b`, coordinate order
`n, …, 1`; symmetric GS = forward then backward sweep. Lean: `backwardGsStep_spec`,
`backwardGsStep_apply` (reverse-order recursion), `symmetricGsStep_eq`. Backbone: 2.3.2 (request
G6: a `backwardGaussSeidelSplitting`/generic constructor). Status: `needs-equivalence`.

**R-4.4 (4.10)–(4.11), (4.18)–(4.23) splitting form.** Book: Jacobi and GS are
`Mx_{k+1} = Nx_k + b = (M − A)x_k + b` with `M = D`, `D − E`, `D − F`; any splitting with `M`
nonsingular gives `x_{k+1} = M⁻¹Nx_k + M⁻¹b`, `G = M⁻¹N = I − M⁻¹A`, `f = M⁻¹b`;
`G_JA = I − D⁻¹A`, `G_GS = I − (D−E)⁻¹A`; the iteration solves `(I − G)x = f`, i.e. the
preconditioned system `M⁻¹Ax = M⁻¹b` (same solution as `Ax = b`).
Lean: `jacobiStep_eq_splitting`, `gsStep_eq_splitting`, `backwardGsStep_eq_splitting` (D9),
`Splitting.iterMatrix_eq_one_sub : s.iterMatrix = 1 - s.m⁻¹ * A`, `G_JA_eq : (jacobiSplitting A h).iterMatrix = 1 - (D A)⁻¹ * A`,
`G_GS_eq`, `fixedPoint_iff : x = G *ᵥ x + f ↔ s.m⁻¹ *ᵥ (A *ᵥ x) = s.m⁻¹ *ᵥ b`, `preconditioned_iff (hM : IsUnit M) : M⁻¹ *ᵥ (A *ᵥ x) = M⁻¹ *ᵥ b ↔ A *ᵥ x = b`.
Backbone: 2.3.2 `iterMatrix_eq`, consistency lemma, "preconditioned-system view". Status: `direct`.

**R-4.5 (4.12) SOR and its relaxation form.** Book: SOR from the splitting
`ωA = (D − ωE) − (ωF + (1−ω)D)`; equals the relaxation sequence
`ξ_i^{(k+1)} = ω ξ_i^{GS} + (1−ω) ξ_i^{(k)}` (`ξ_i^{GS}` the right side of (4.7) evaluated with the
already-updated components); backward SOR analogously.
Lean: `sorStep_spec (h) : (D A - ω • E A) *ᵥ sorStep A ω b x = (ω • F A + (1 - ω) • D A) *ᵥ x + ω • b`,
`sorStep_apply (h) (i) : sorStep A ω b x i = ω * ((-(∑ j ∈ Iio i, A i j * sorStep A ω b x j) - ∑ j ∈ Ioi i, A i j * x j + b i) / A i i) + (1 - ω) * x i`,
`sorStep_one : sorStep A 1 b = gsStep A b`, `omega_smul_decomp : ω • A = (D A - ω • E A) - (ω • F A + (1 - ω) • D A)`.
Backbone: 2.3.2 `sorSplitting` (D11). Status: `needs-equivalence` for the splitting form,
`surface-only` for the componentwise identity.

**R-4.6 (4.13)–(4.14) SSOR.** Book: SSOR step = SOR step followed by backward SOR step;
`x_{k+1} = G_ω x_k + f_ω` with `G_ω`, `f_ω` as in (4.13)–(4.14), and
`f_ω = ω(2−ω)(D − ωF)⁻¹D(D − ωE)⁻¹b` (using `[ωE + (1−ω)D](D − ωE)⁻¹ = −I + (2−ω)D(D − ωE)⁻¹`).
Lean: `ssorStep_eq_affine (h) : ssorStep A ω b x = G_ssor A ω *ᵥ x + f_ssor A ω b`,
`f_ssor_eq (h) : f_ssor A ω b = (ω * (2 - ω)) • (D A - ω • F A)⁻¹ *ᵥ (D A *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b))`,
`aux_identity : (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ = -1 + (2 - ω) • D A * (D A - ω • E A)⁻¹`.
Backbone: 2.3.2 `ssorSplitting`. Route: matrix algebra with `Matrix.mul_nonsing_inv`. Status:
`surface-only` (book-specific closed forms; acceptable) plus `needs-equivalence` for
`ssorStep = (ssorSplitting A ω h).step b` (G6).

**R-4.7 §4.1.1 block relaxation, (4.16)–(4.17), Alg 4.1–4.2.** Book: with a block partition,
block Jacobi is `A_ii ξ_i^{(k+1)} = ((E+F)x_k)_i + β_i`, i.e. the same vector equation with block
`D, E, F`; with `V_i`, `W_i` (`W_iᵀV_i = I`) the Jacobi component is (4.17); `V_iW_iᵀ` is a
projector onto `K_i = span(V_i)`; `x = Σ V_i ξ_i`.
Lean: `V_W_biorthogonal (P) (h : weights chosen) : (P.W i)ᵀ * P.V i = 1`,
`isProjector_V_mul_Wᵀ`, `sum_V_mulVec_Wᵀ (P : partition, no overlap) : ∑ i, P.V i *ᵥ ((P.W i)ᵀ *ᵥ x) = x`,
`blockJacobiStep_eq_of_partition : blockJacobiStep P A b x = (blockD)⁻¹ *ᵥ ((blockE + blockF) *ᵥ x) + (blockD)⁻¹ *ᵥ b`,
`blockJacobiStep_component (4.17)`. Backbone: 2.3.2/2.4.4 phase 2. Status: `surface-only`
definitions and identities now (definitional), `needs-equivalence` with 2.4.4 later.

**R-4.8 (4.24)–(4.27) preconditioners.** Book: `M_JA = D`, `M_GS = D − E`, `M_SOR = ω⁻¹(D − ωE)`,
`M_SSOR = (ω(2−ω))⁻¹(D − ωE)D⁻¹(D − ωF)`, and the SSOR iteration is the fixed-point iteration of
`M_SSOR⁻¹Ax = M_SSOR⁻¹b`, i.e. `G_ω = I − M_SSOR⁻¹A` (implicit in the text).
Lean: `M_JA_eq : (jacobiSplitting A h).m = D A` (rfl), `M_GS_eq`, `M_sor_eq` (D11),
`G_ssor_eq_one_sub (h) (hω : ω ≠ 0) (hω2 : ω ≠ 2) : G_ssor A ω = 1 - (M_ssor A ω)⁻¹ * A`,
`f_ssor_eq_inv_mulVec : f_ssor A ω b = (M_ssor A ω)⁻¹ *ᵥ b`. Backbone: 2.3.2 `ssorSplitting`
(request G6 to state exactly (4.27) as `m` and prove the product form). Status: `needs-equivalence`.

### §4.2 Convergence (`Ch04/Convergence.lean`, `DiagDominant.lean`, `SPD.lean`)

**R-4.9 (4.29) the limit solves the system.** Book: if `x_{k+1} = Gx_k + f` converges, the limit
satisfies `x = Gx + f`; for `G = M⁻¹N`, `f = M⁻¹b` this is `Mx = Nx + b`, i.e. `Ax = b`.
Lean: `tendsto_affineStep_fixed (h : Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) : x = G *ᵥ x + f`,
`fixed_iff_solves (s : Splitting A) : x = s.step b x ↔ A *ᵥ x = b`. Backbone: 2.3.2 consistency;
continuity of `affineStep`. Status: `direct` / `surface-only` (uniqueness of limits).

**R-4.10 (4.30) error recursion.** Book: `I − G` nonsingular ⇒ solution `x*` of (4.29) and
`x_{k+1} − x* = G(x_k − x*) = … = G^{k+1}(x₀ − x*)`; also `x_{k+1} − x_k = G^k(f − (I−G)x₀)`.
Lean: `affineStep_iterate_sub (hx : G *ᵥ x' + f = x') : (affineStep G f)^[k] x₀ - x' = (G ^ k) *ᵥ (x₀ - x')`,
`affineStep_iterate_succ_sub : (affineStep G f)^[k+1] x₀ - (affineStep G f)^[k] x₀ = (G ^ k) *ᵥ (f - (1 - G) *ᵥ x₀)`.
Backbone: 2.3.1 `Stationary.step_iterate_sub`. Status: `direct`.

**R-4.11 Theorem 4.1.** Book: `G` square (real) with `ρ(G) < 1` ⇒ `I − G` nonsingular and (4.28)
converges for any `f` and `x₀`; conversely, if (4.28) converges for any `f` and `x₀` then `ρ(G) < 1`.
Lean (checked):
```lean
theorem thm_4_1_mp (hG : spectralRadiusReal G < 1) : IsUnit (1 - G) ∧
    ∀ f x₀, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f))
theorem thm_4_1_mpr (h : ∀ f x₀, ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) :
    spectralRadiusReal G < 1
```
Backbone: 2.1.3 `spectralRadius_lt_one_iff_tendsto_pow`, `summable_pow_iff_spectralRadius_lt_one`;
2.1.11 real corollary `(∀ x, Gᵏ x → 0) ↔ Matrix.spectralRadius G < 1`; 2.3.1. Route (⇒): `IsUnit`
of `1 − complexify G` (Neumann series) ⇒ `det ≠ 0` ⇒ `IsUnit (1 − G)`; then R-4.10 with
`x* = (1−G)⁻¹f` and `Gᵏ(x₀ − x*) → 0`. (⇐): take `x₀ = 0`, `f = v`: `x_{k+1} − x_k = Gᵏ v → 0` for
all `v` (R-4.10), then 2.1.11. Status: `needs-equivalence` (real/complex transport; request G1 asks
2.1.11 to include `IsUnit (1 − G)` and `Tendsto (G^k) (𝓝 0)` forms).

**R-4.12 Corollary 4.2.** Book: `‖G‖ < 1` for *some matrix norm* (Saad §1.5: a norm on
`ℂ^{n×n}` that is consistent, `‖AB‖ ≤ ‖A‖‖B‖`) ⇒ `I − G` nonsingular and (4.28) converges for any
`x₀` (and `f`). Lean (checked): `cor_4_2 (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ)) (hG : N G < 1) : IsUnit (1 - G) ∧ ∀ f x₀, Tendsto … (𝓝 ((1 - G)⁻¹ *ᵥ f))`;
instances `cor_4_2_lp (p) (hG : lpOpNorm p G < 1)` and the scoped `‖G‖ < 1` forms for `p = 2, ∞`.
Backbone: 2.3.1 `Stationary.contractingWith (‖G‖ < 1)`; 2.1.3 `ρ ≤ ‖·‖` (Mathlib
`spectralRadius_le_nnnorm` for the scoped normed-algebra instances). Route for `lpOpNorm p`:
`lpOpNorm p (G^k) ≤ (lpOpNorm p G)^k → 0` ⇒ `Gᵏx → 0` ⇒ R-4.11 (⇐)+(⇒). Route for an arbitrary
`AlgebraNorm`: needs "all norms on the finite-dimensional space `Matrix` are equivalent" to get
`Gᵏ → 0` from `N(Gᵏ) ≤ N(G)ᵏ` — not in the backbone. Status: `direct` for `lpOpNorm p`; `GAP` (G2)
for the general consistent norm.

**R-4.13 Convergence factor and rate (§4.2.1).** Book: `d_k = Gᵏd₀`; specific factor
`ρ = lim (‖d_k‖/‖d₀‖)^{1/k}` equals `ρ(G)` (derived with the Jordan form under "one dominant
eigenvalue"); `τ = −ln ρ`; general factor `φ = lim (max_{d₀} ‖Gᵏd₀‖/‖d₀‖)^{1/k} = lim ‖Gᵏ‖^{1/k} = ρ(G)`.
Lean: `limsup_specific_le : limsup (fun k => (‖(G^k) ⬝ d₀‖/‖d₀‖)^(1/k:ℝ)) atTop ≤ (spectralRadiusReal G).toReal`;
`iSup_eq_opNorm : (⨆ d₀ : {d // d ≠ 0}, ‖(G^k) ⬝ d₀‖/‖d₀‖) = ‖G^k‖₂`;
`tendsto_generalFactor : Tendsto (fun k => ‖G^k‖₂ ^ (1/k:ℝ)) atTop (𝓝 (spectralRadiusReal G).toReal)` (Gelfand);
`exists_specific_eq : ∃ d₀ ≠ 0, limsup … = ρ(G)`. Backbone: 2.1.3 (Gelfand, `exists_norm_pow_le_of_spectralRadius_lt`),
2.3.1 "`limsup ‖Gᵏd‖^{1/k} ≤ ρ(G)`, `= ρ(G)` for the worst `d`", 2.1.11 (norm preservation under
`complexify`: only `l∞`/Frobenius are listed — request G1 for `‖·‖₂`, or use norm-independence of
Gelfand's limit). The book's claim that the *specific* limit exists and equals `ρ(G)` for the
generic `d₀` (Jordan asymptotics `‖d_k‖ ≈ C |λ|^{k−p+1} C(k, p−1)`) is heuristic ("≈") and needs
the Jordan form: left out (§5). Status: `needs-equivalence` for the three stated items.

**R-4.14 Example 4.1 (Richardson).** Book: `x_{k+1} = x_k + α(b − Ax_k)`, `G_α = I − αA`; if all
eigenvalues of `A` are real with `λ_min ≤ λ_i ≤ λ_max`: eigenvalues of `G_α` lie in
`[1 − αλ_max, 1 − αλ_min]`; if `λ_min < 0 < λ_max` the method diverges for some `x₀` for every
`α`; if `λ_min > 0` it converges iff `0 < α < 2/λ_max`; `ρ(G_α) = max{|1 − αλ_min|, |1 − αλ_max|}`,
`α_opt = 2/(λ_min + λ_max)`, `ρ_opt = (λ_max − λ_min)/(λ_max + λ_min)`.
Lean: `richardsonStep A α b x := x + α • (b - A *ᵥ x)`, `richardsonStep_eq_affine`,
`spectrum_one_sub_smul : spectrum ℂ (1 - α • A) = (fun μ => 1 - α * μ) '' spectrum ℂ A`,
`spectralRadius_richardson (hreal : spectrum ℂ A ⊆ range ofReal) (hmin hmax : attained extremes) : ρ(G_α) = max |1 − αλ_min| |1 − αλ_max|`,
`richardson_converges_iff (hpos : 0 < λ_min) : ρ(G_α) < 1 ↔ 0 < α ∧ α < 2/λ_max`,
`richardson_opt : IsLeast/argmin … = 2/(λ_min+λ_max)`, `ρ_opt` value. Backbone: 2.3.5 (phase 2)
"Richardson with optimal parameter (Saad Ex 4.1, AH Ex 5.2.3)". Route: spectral mapping for affine
polynomials (Mathlib `spectrum.sub_singleton`/`smul`), elementary real optimization. Status:
`direct (phase 2)`; optional in the surface.

**R-4.15 Definition 4.3 / Theorem 4.4 (regular splittings).** Book: `M, N` regular splitting of
`A` (`M` nonsingular, `M⁻¹ ≥ 0`, `N ≥ 0`): `ρ(M⁻¹N) < 1` iff `A` nonsingular and `A⁻¹ ≥ 0`;
consequently the iteration (4.34) converges whenever `A` is an M-matrix.
Lean: `thm_4_4 (h : A.IsRegularSplitting M N) : spectralRadiusReal (M⁻¹ * N) < 1 ↔ IsUnit A ∧ ∀ i j, 0 ≤ A⁻¹ i j`;
`converges_of_isMMatrix (hA : A.IsMMatrix) (h : A.IsRegularSplitting M N) : ∀ b x₀, Tendsto (iterates of M⁻¹N x + M⁻¹b) atTop (𝓝 (A⁻¹ *ᵥ b))`.
Backbone: 2.3.4 (phase 2; Thm 1.29 and weak Perron–Frobenius), 2.1.12, R-4.11. Status: `GAP`
(phase 2; G4). The M-matrix corollary is `direct` from Thm 4.4 + R-4.11 (only Def 1.30 is used, not
Thm 1.31–1.32).

**R-4.16 `|λ_i| ≤ ‖A‖`.** Book: for any matrix norm, every eigenvalue satisfies `|λ| ≤ ‖A‖`
(text before Thm 4.6). Lean: `norm_le_lpOpNorm_of_mem_spectrum (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ ≤ lpOpNorm p A`;
general `AlgebraNorm` version. Backbone/Mathlib: `spectrum.norm_le_norm_of_mem` (for the scoped
normed-algebra instances). Status: `direct` for `lpOpNorm 2/⊤` (scoped instances), `GAP` (G2) for a
general consistent norm.

**R-4.17 Theorem 4.6 (Gershgorin).** Book: every eigenvalue `λ` of `A` lies in some closed disc
`|λ − a_ii| ≤ ρ_i = Σ_{j≠i} |a_ij|`; the column-sum version holds too (transpose). Lean (checked):
`thm_4_6 (A : Matrix _ _ ℂ) (hμ : μ ∈ spectrum ℂ A) : ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ univ.erase i, ‖A i j‖`;
`thm_4_6_col`. Backbone/Mathlib: `eigenvalue_mem_ball` (on `HasEigenvalue (toLin' A)`),
`Module.End.hasEigenvalue_iff_mem_spectrum`, `Matrix.spectrum_toLin'`, `charpoly_transpose`.
Status: `direct`.

**R-4.18 Theorem 4.7.** Book: `A` irreducible, eigenvalue `λ` on the boundary of the union of the
`n` Gershgorin discs ⇒ `λ` lies on the boundary of every disc, `|λ − a_ii| = ρ_i ∀ i`.
Lean (checked): `thm_4_7 (hA : IsIrreducible A) (hμ : μ ∈ spectrum ℂ A) (hb : μ ∈ frontier (⋃ i, closedBall (A i i) (ρ i))) : ∀ i, ‖μ - A i i‖ = ρ i`.
Backbone: 2.3.3 says phase 2 (`Matrix.IsIrreducible`). Route: the book's path argument along the
strongly connected quiver of `A.map ‖·‖` (`Matrix.isIrreducible_iff_exists_pow_pos` or the
`IsSStronglyConnected` paths). Status: `GAP` (phase 2; G5).

**R-4.19 Corollary 4.8.** Book: strictly diagonally dominant or irreducibly diagonally dominant ⇒
nonsingular. Lean: `cor_4_8_strict (h : IsStrictRowDiagDominant A) : IsUnit A` (+ column form),
`cor_4_8_irred (h : IsIrreduciblyRowDiagDominant A) : IsUnit A`. Backbone/Mathlib:
`det_ne_zero_of_sum_row_lt_diag`, `det_ne_zero_of_sum_col_lt_diag`; 2.3.3
`IsStrictDiagDominant.isUnit`. Status: `direct` (strict), `GAP` phase 2 (irreducible, via R-4.18).

**R-4.20 Theorem 4.9.** Book: `A` strictly diagonally dominant or irreducibly diagonally dominant
⇒ the Jacobi and Gauss–Seidel iterations converge for any `x₀`.
Lean: `thm_4_9_jacobi (h : IsStrictRowDiagDominant A ∨ IsIrreduciblyRowDiagDominant A) (b x₀) : Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))`,
`thm_4_9_gs` likewise; column-dominance versions (`IsStrictColDiagDominant`) as separate theorems
(see §6 on Def 4.5). Backbone: 2.3.3 `Matrix.jacobi_spectralRadius_lt_one` (✓, over ℂ),
`gaussSeidel_spectralRadius_lt_one`, `linfty_opNorm_jacobi_lt_one`; 2.1.11 `complexify`; R-4.11.
Route: `complexify` commutes with `diagPart/strictLower/strictUpper/inverse` (`Matrix.map` lemmas)
so `spectralRadiusReal G_J = spectralRadius ℂ (jacobiSplitting (complexify A)).iterMatrix < 1`,
then R-4.11 (⇒) with `x* = A⁻¹b`. Status: `needs-equivalence` (strict), `GAP` phase 2
(irreducible; G5). Column variants: the backbone lists only "column variant" for the definition —
request G5 for the column-dominance convergence theorems (Jacobi via similarity `D G_J D⁻¹`, GS via
the Cor 4.8 argument applied to `N − λM`).

**R-4.21 Theorem 4.10.** Book: `A` symmetric with positive diagonal, `0 < ω < 2`: SOR converges for
any `x₀` iff `A` is positive definite. (As printed, "converges" must mean convergence to the
solution for every right-hand side, equivalently `ρ(G_ω) < 1`: for singular positive
semidefinite `A` and `b = 0` the iterates converge for every `x₀` — see §6.)
Lean: `thm_4_10 (hs : A.IsSymm) (hd : ∀ i, 0 < A i i) (hω : 0 < ω) (hω2 : ω < 2) : spectralRadiusReal (sorIterMatrix A ω) < 1 ↔ A.IsPositiveReal`
and, via R-4.11, `(∀ f x₀, ∃ x, Tendsto …) ↔ A.PosDef`. Backbone: 2.3.5 (phase 2) Householder–John/
Ostrowski–Reich (`A` symmetric coercive, `M + Mᴴ − A` coercive ⇒ `ρ(M⁻¹N) < 1`) gives (⇐) with
`M = ω⁻¹D − E`, `M + Mᵀ − A = (2/ω − 1)D`; the converse (⇒) is not in the backbone. Status: `GAP`
(G7: phase 2 plus the converse).

**R-4.22 Proposition 4.12.** Book: `B = [[0, B₁₂],[B₂₁, 0]]`, `L`, `U` its strict lower/upper
parts: (1) `μ` eigenvalue ⇒ `−μ` eigenvalue; (2) the eigenvalues of `B(α) = αL + α⁻¹U` (`α ≠ 0`)
are independent of `α`. Lean (index type `Fin n₁ ⊕ Fin n₂`, `B := fromBlocks 0 B₁₂ B₂₁ 0`):
`prop_4_12_neg (hμ : μ ∈ spectrum ℂ B) : -μ ∈ spectrum ℂ B`,
`prop_4_12_alpha (hα : α ≠ 0) : spectrum ℂ (α • fromBlocks 0 0 B₂₁ 0 + α⁻¹ • fromBlocks 0 B₁₂ 0 0) = spectrum ℂ B`.
Backbone: 2.3.5 phase 2. Route: similarity by `fromBlocks 1 0 0 (α • 1)` (`spectrum` invariant under
conjugation, `Matrix.charpoly_units_conj`). Status: `direct (phase 2)`; simple enough to be
`surface-only` meanwhile.

**R-4.23 Definition 4.11/4.13 facts.** Book: Property A ⟺ can be symmetrically permuted to the
block form (4.42) with diagonal `D₁, D₂`; consistently ordered ⇒ Property A; T-matrices are
consistently ordered; Property A is invariant under symmetric permutations; Property A ⟺ some
symmetric permutation is consistently ordered. Lean: `hasPropertyA_iff_reindex : HasPropertyA A ↔ ∃ (σ : Equiv.Perm (Fin n)) (k : ℕ), ∀ i j, (A.reindex σ σ) i j ≠ 0 → i ≠ j → ((i : ℕ) < k ↔ ¬ ((j : ℕ) < k))`,
`hasPropertyA_of_isConsistentlyOrdered`, `isConsistentlyOrdered_of_isTMatrix`,
`hasPropertyA_reindex`, `hasPropertyA_iff_exists_reindex_isConsistentlyOrdered`. Backbone: none
(§8.1: surface-only). Status: `surface-only` (combinatorics of labels; the last item is harder and
optional).

**R-4.24 Proposition 4.14.** Book: `A` consistently ordered ⇒ there is a permutation `P` with
`PᵀAP` a T-matrix and `(PᵀAP)_L = PᵀA_LP`, `(PᵀAP)_U = PᵀA_UP`.
Lean: `prop_4_14 (h : IsConsistentlyOrdered A) : ∃ σ : Equiv.Perm (Fin n), IsTMatrix (A.reindex σ σ) ∧ strictLower (A.reindex σ σ) = (strictLower A).reindex σ σ ∧ strictUpper … `.
Backbone: 2.3.5 phase 2. Route: sort indices by label, stably (order-preserving within a label
class). Status: `GAP` (phase 2; G8).

**R-4.25 Proposition 4.15.** Book: `B` the Jacobi matrix of a consistently ordered `A`, `L, U`
its strict lower/upper parts: eigenvalues of `αL + α⁻¹U` (`α ≠ 0`) do not depend on `α`.
Lean: `prop_4_15 (h : IsConsistentlyOrdered A) (hd : ∀ i, A i i ≠ 0) (hα : α ≠ 0) : spectrum ℂ (Bα (complexify (jacobiIterMatrix A)) α) = spectrum ℂ (complexify (jacobiIterMatrix A))`.
Backbone: 2.3.5 phase 2. Route: R-4.24 then similarity by `diag(α^{c i})`. Status: `GAP` (G8).

**R-4.26 Theorem 4.16.** Book: `A` consistently ordered, `a_ii ≠ 0`, `ω ≠ 0`; `M_SOR` here denotes
the SOR *iteration matrix* `(I − ωL)⁻¹(ωU + (1−ω)I)` with `L = D⁻¹E`, `U = D⁻¹F`, `B = L + U`
Jacobi: if `λ ≠ 0` is an eigenvalue of `M_SOR` and `(λ + ω − 1)² = λω²μ²` then `μ` is an eigenvalue
of `B`; conversely `μ ∈ σ(B)` and (4.46) ⇒ `λ ∈ σ(M_SOR)`.
Lean: `thm_4_16_mp (h) (hd) (hω : ω ≠ 0) (hλ : λ ≠ 0) (hλG : λ ∈ spectrum ℂ G_ω) (hμ : (λ + ω - 1)^2 = λ * ω^2 * μ^2) : μ ∈ spectrum ℂ B`,
`thm_4_16_mpr (h) (hd) (hω) (hμB : μ ∈ spectrum ℂ B) (hλ : (λ + ω - 1)^2 = λ * ω^2 * μ^2) : λ ∈ spectrum ℂ G_ω`
(`G_ω := complexify ((sorSplitting A ω _).iterMatrix)`, `B := complexify (jacobiSplitting A _).iterMatrix`).
Backbone: 2.3.5 phase 2. Route: determinant identity `det((λ+ω−1)I − ω(λL + U)) = 0` and R-4.25 with
`α = λ^{1/2}` (complex square root). Status: `GAP` (G8).

**R-4.27 (4.47) optimal `ω`.** Book: "this theorem allows us to compute an optimal `ω`, which can be
shown to be `ω_opt = 2/(1 + √(1 − ρ(B)²))`" (Young; needs `B` with real eigenvalues and
`ρ(B) < 1`). Lean: `omega_opt (h) (hd) (hreal : spectrum ℂ B ⊆ range ofReal) (hρ : ρ(B) < 1) : IsMinOn (fun ω => ρ(G_ω).toReal) (Ioo 0 2) (2 / (1 + √(1 − ρ(B)²)))` and `ρ(G_{ω_opt}) = ω_opt − 1`.
Backbone: 2.3.5 phase 2 ("`ω_opt`, `ρ_GS = ρ_J²`"). Status: `GAP` (G8; lowest priority).

### §5.1 Basic definitions (`Ch05/Projection.lean`)

**R-5.1 (5.3)–(5.7) reformulations and matrix representation.** Book: (5.3) ⟺ (5.5)–(5.6)
with `δ = x̃ − x₀`, `r₀ = b − Ax₀`; with bases `V` of `K`, `W` of `L`, `x̃ = x₀ + Vy` satisfies the
Petrov–Galerkin condition iff `WᵀAVy = Wᵀr₀`; if `WᵀAV` is nonsingular, `x̃ = x₀ + V(WᵀAV)⁻¹Wᵀr₀`
(5.7); Algorithm 5.1 computes exactly this.
Lean: `isProjectionApprox_iff_isPetrovGalerkin` (D17), `isProjectionApprox_add_iff (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) (y) : IsProjectionApprox A b x₀ K L (x₀ + V ⬝ y) ↔ (Wᵀ * A * V) *ᵥ y = Wᵀ *ᵥ (b - A ⬝ x₀)`,
`isProjectionApprox_iff_eq_projStep (hV hW) (h : IsUnit (Wᵀ * A * V)) : IsProjectionApprox A b x₀ K L x ↔ x = projStep A b V W x₀`,
`projStep_isProjectionApprox`. Backbone: 2.4.1 `IsPetrovGalerkin`, `isPetrovGalerkin_iff_toMatrix`
(sketch). Status: `needs-equivalence` (G3/G9: the bases form of 2.4.1 must be stated with
`IsBasisOf`-style hypotheses).

**R-5.2 Example 5.1.** Book: an elementary Gauss–Seidel step (4.6) is a projection step with
`K = L = span{e_i}`. Lean: `gsComponentUpdate A b x i = step1 A b (e i) (e i) x` where the left side
changes only component `i` to annihilate `(b − Ax)_i`. Status: `surface-only` (definitional;
optional).

**R-5.3 Nonsingularity of `WᵀAV`.** Book: "`WᵀAV` is nonsingular iff no vector of the subspace
`AK` is orthogonal to `L`" (read as: `Au ⟂ L` for `u ∈ K` forces `u = 0`; the literal reading
"no nonzero vector of `AK` is orthogonal to `L`" fails for `A = 0` — see §6). Lean:
`isUnit_iff_forall (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) : IsUnit (Wᵀ * A * V) ↔ ∀ u ∈ K, u ≠ 0 → A ⬝ u ∉ Lᗮ`;
also `↔ ∀ r₀, ∃! x, IsProjectionApprox A b x₀ K L x` (any `b`, `x₀`). Backbone: 2.1.7 G3 applied
to `V' := A * V` when `A` is injective on `K`; 2.4.1. Status: `needs-equivalence` (G9 — the
`∃!`-form belongs in 2.4.1 since it is what makes Prop 5.1 a corollary of
`existsUnique_isGalerkin_of_isCoercive`/`existsUnique_isMinRes_of_injOn`).

**R-5.4 Proposition 5.1.** Book: (i) `A` positive definite (Saad's sense) and `L = K`, or (ii) `A`
nonsingular and `L = AK` ⇒ `B = WᵀAV` is nonsingular for any bases `V` of `K`, `W` of `L`.
Lean: `prop_5_1_i (hA : A.IsPositiveReal) (hV : V.IsBasisOf K) (hW : W.IsBasisOf K) : IsUnit (Wᵀ * A * V)`,
`prop_5_1_ii (hA : IsUnit A) (hV : V.IsBasisOf K) (hW : W.IsBasisOf (K.map (toEuclideanLin A))) : IsUnit (Wᵀ * A * V)`.
Backbone: 2.4.1 `existsUnique_isGalerkin_of_isCoercive` (✓), `existsUnique_isMinRes_of_injOn` (✓).
Route: R-5.3: (i) `u ∈ K`, `u ≠ 0` ⇒ `(Au, u) > 0` ⇒ `Au ∉ Kᗮ`; (ii) `Au ≠ 0`, `Au ∈ AK = L` ⇒
`Au ∉ Lᗮ`. Status: `needs-equivalence` (via R-5.3; the book's own proof through
`VᵀAV` positive definite / `(AV)ᵀAV` full rank is R-5.5).

**R-5.5 Projected matrix remarks.** Book: `A` symmetric, `L = K`, same basis ⇒ `B = VᵀAV`
symmetric; `A` SPD ⇒ `B` SPD; (in the proof of Prop 5.1) `A` positive definite ⇒ `VᵀAV` positive
definite; `A` nonsingular ⇒ `AV` full rank ⇒ `(AV)ᵀAV` nonsingular.
Lean: `isSymm_conjTranspose_mul_mul`, `posDef_transpose_mul_mul (hA : A.PosDef) (hV : LinearIndependent …)`,
`isPositiveReal_transpose_mul_mul`, `isUnit_transpose_mul_self_of_injective`. Backbone/Mathlib:
`Matrix.PosDef.conjTranspose_mul_mul_same (hB : Function.Injective B.mulVec)`,
`Matrix.PosDef.conjTranspose_mul_self`. Status: `direct` (Mathlib) / `surface-only` for the
`IsPositiveReal` variant.

### §5.2 General theory

**R-5.6 Proposition 5.2.** Book: `A` SPD, `L = K`: `x̃` is the result of the orthogonal projection
method onto `K` with starting vector `x₀` iff it minimizes `E(x) = (A(x* − x), x* − x)^{1/2}` over
`x₀ + K`. Lean: `prop_5_2 (hA : A.PosDef) (hstar : A ⬝ xstar = b) : IsProjectionApprox A b x₀ K K x ↔ (x - x₀ ∈ K ∧ IsMinOn (E_A A xstar) {y | y - x₀ ∈ K} x)`.
Backbone: 2.4.2 `isGalerkin_iff_energy_min` (✓, one direction in the prototype; both needed).
Route: D1/D17/D19 equivalences. Status: `direct` after equivalences (`needs-equivalence`).

**R-5.7 Proposition 5.3.** Book: `A` an arbitrary square matrix, `L = AK`: `x̃` is the result of the
oblique projection method onto `K` orthogonally to `L` with starting vector `x₀` iff it minimizes
`R(x) = ‖b − Ax‖₂` over `x₀ + K` (`A` need not be nonsingular). Lean:
`prop_5_3 : IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x ↔ (x - x₀ ∈ K ∧ IsMinOn (R_A A b) {y | y - x₀ ∈ K} x)`.
Backbone: 2.4.2 `isMinRes_iff_isPetrovGalerkin` (✓). Status: `direct`.

**R-5.8 Proposition 5.4 and `‖r̃‖₂ ≤ ‖r₀‖₂`.** Book: `L = AK`: `r̃ = b − Ax̃ = (I − P)r₀` with `P` the
orthogonal projector onto `AK`; hence `‖r̃‖₂ ≤ ‖r₀‖₂`. Lean:
`prop_5_4 (hx : IsProjectionApprox A b x₀ K (K.map A') x) : b - A ⬝ x = (b - A ⬝ x₀) - (K.map A').starProjection (b - A ⬝ x₀)`,
`norm_residual_le_of_prop_5_4 : ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ x₀‖`. Backbone: 2.4.1 `IsMinRes.residual_eq`
(✓) with R-5.7; the norm bound from `IsMinRes.min x₀` (`x₀ − x₀ = 0 ∈ K`). Status: `direct`.

**R-5.9 Proposition 5.5 and `‖d̃‖_A ≤ ‖d₀‖_A`.** Book: `A` SPD, orthogonal projection onto `K`:
`d̃ = x* − x̃ = (I − P_A)d₀`, `P_A` the projector onto `K` orthogonal w.r.t. the `A`-inner product
(`δ = x̃ − x₀` is the `A`-orthogonal projection of `d₀` onto `K`); hence `‖d̃‖_A ≤ ‖d₀‖_A`.
Lean: `prop_5_5_char (hA : A.PosDef) (hstar) (hx : IsProjectionApprox A b x₀ K K x) : (x - x₀) ∈ K ∧ ∀ w ∈ K, A.energyInner (xstar - x) w = 0`
(the (1.59)–(1.60) characterization in the `A`-inner product; this is the Galerkin condition
rewritten), `prop_5_5 : xstar - x = WithEnergy.equiv.symm ((K.energy hA')ᗮ.starProjection (WithEnergy.equiv (xstar - x₀)))`,
`energyNorm_le : E_A A xstar x ≤ E_A A xstar x₀`. Backbone: 2.4.2 `IsGalerkin.error_eq`, 2.1.5
`WithEnergy`. Status: `needs-equivalence` (D3).

**R-5.10 §5.2.3 reformulation `A_m x̃ = Q b`.** Book: with `x₀ = 0` and `Q = Q_K^L` defined
(`K ∩ Lᗮ = {0}`), (5.5)–(5.6) ⟺ `x̃ ∈ K ∧ Q(b − Ax̃) = 0` ⟺ `x̃ ∈ K ∧ A_m x̃ = Qb`, `A_m = QAP_K`.
Lean: `isProjectionApprox_zero_iff_Q (h : K ⊓ Lᗮ = ⊥) (hd) : IsProjectionApprox A b 0 K L x ↔ x ∈ K ∧ Q K L h hd (b - A ⬝ x) = 0`,
`… ↔ x ∈ K ∧ A_m A K L h hd x = Q K L h hd b`. Backbone: 2.1.7 (`P x = 0 ↔ x ∈ Lᗮ`, R-1.8),
`starProjection_eq_self_iff`. Status: `direct`.

**R-5.11 Proposition 5.6 (and its `x₀ ≠ 0` extension).** Book: `K` invariant under `A`, `x₀ = 0`,
`b ∈ K` ⇒ the approximate solution of any (oblique or orthogonal) projection method onto `K` is
exact; for `x₀ ≠ 0` the assumption is `r₀ = b − Ax₀ ∈ K`. The proof uses `Q_K^L`, so the implicit
hypothesis `K ∩ Lᗮ = {0}` is needed (see §6). Lean:
`prop_5_6 (hK : K ∈ Module.End.invtSubmodule (toEuclideanLin A)) (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) (hb : b - A ⬝ x₀ ∈ K) (hx : IsProjectionApprox A b x₀ K L x) : A ⬝ x = b`
(the book's case is `x₀ = 0`). Backbone: 2.4.1 `IsPetrovGalerkin.eq_of_invt` (✓). Status: `direct`.

**R-5.12 Distance to `K`.** Book: for `x̃ ∈ K`, `‖x̃ − x*‖₂ ≥ ‖(I − P_K)x*‖₂` (the sine of the angle
between `x*` and `K` times `‖x*‖₂`). Lean: `norm_sub_ge_of_mem (hx : x ∈ K) : ‖(1 - K.starProjection) xstar‖ ≤ ‖x - xstar‖`.
Backbone/Mathlib: `starProjection_minimal`. Status: `direct`.

**R-5.13 Theorem 5.7.** Book: `γ = ‖Q_K^L A (I − P_K)‖₂`, `b ∈ K`, `x₀ = 0`: the exact solution
`x*` satisfies `‖b − A_m x*‖₂ ≤ γ ‖(I − P_K)x*‖₂`. Lean:
`thm_5_7 (h : K ⊓ Lᗮ = ⊥) (hd) (hb : b ∈ K) (hstar : A ⬝ xstar = b) : ‖b - A_m A K L h hd xstar‖ ≤ ‖(Q ∘L A' ∘L (1 - K.starProjection) : E n →L[ℝ] E n)‖ * ‖(1 - K.starProjection) xstar‖`.
Backbone: 2.4.1 `norm_projected_residual_le`. Status: `direct`.

**R-5.14 Matrix interpretation of Thm 5.7.** Book: `L = K`, `V` orthonormal basis, `W = V`:
`b = VVᵀb` and (5.11) reads `‖Vᵀb − (VᵀAV)Vᵀx*‖₂ ≤ γ ‖(I − P_K)x*‖₂` (since
`‖V(Vᵀb − (VᵀAV)Vᵀx*)‖₂ = ‖Vᵀb − (VᵀAV)Vᵀx*‖₂`). Lean: `thm_5_7_matrix (hV : Vᵀ * V = 1) (hV' : V.IsBasisOf K) (hb : b ∈ K) (hstar) : ‖Vᵀ *ᵥ b - (Vᵀ * A * V) *ᵥ (Vᵀ *ᵥ xstar)‖ ≤ γ * ‖(1 - K.starProjection) xstar‖`.
Backbone: R-1.12 (`VVᵀ = P_K`), 2.1.6 `toMatrix_compression` (`VᵀAV` is the compression in the
basis `V`), `‖V y‖ = ‖y‖` for isometric `V`. Status: `needs-equivalence`.

### §5.3 One-dimensional projection processes (`Ch05/OneDimensional.lean`)

**R-5.15 (5.12).** Book: `K = span{v}`, `L = span{w}`: the new approximation is `x + αv` with
`α = (r, w)/(Av, w)`. Lean: `step1_isProjectionApprox (h : inner ℝ (A ⬝ v) w ≠ 0) : IsProjectionApprox A b x (span {v}) (span {w}) (step1 A b v w x)`
and `isProjectionApprox_span_singleton_iff (h) : IsProjectionApprox A b x (span {v}) (span {w}) x' ↔ x' = step1 A b v w x`.
Backbone: 2.4.3 `Projection.step1`, `step1_isPetrovGalerkin` (request G9 for the `iff`).
Status: `direct` / `needs-equivalence`.

**R-5.16 Algorithm 5.2 and its line-minimization property.** Book: SD (`A` SPD): `v = w = r`;
Alg 5.2 with the recursive residual `r ← r − αp`, `p = Ar`; each step minimizes
`f(x) = ‖x − x*‖_A²` over `x + αd` with `d = −∇f = 2r` (negative gradient direction).
Lean: `sdAlg_spec (k) : ((sdAlgStep A)^[k] ⟨x₀, b - A ⬝ x₀, A ⬝ (b - A ⬝ x₀)⟩).x = (sdStep A b)^[k] x₀ ∧ ….r = b - A ⬝ (…) ∧ ….p = A ⬝ (….r)`,
`sdStep_isMinOn (hA : A.PosDef) (hstar) : IsMinOn (fun x' => E_A A xstar x' ^ 2) {x + α • r | α : ℝ} (sdStep A b x)`,
`gradient_energy (hA : A.IsSymm) : HasGradientAt (fun x => E_A A xstar x ^ 2) (2 • (A ⬝ (x - xstar))) x` (optional).
Backbone: 2.4.3 `steepestDescentStep`, R-5.6 with `K = span{r}`. Status: `surface-only`
(bookkeeping, same pattern as backbone `CG.residual_eq`) + `direct` (minimization via Prop 5.2).

**R-5.17 Lemma 5.8 (Kantorovich).** Book: `B` real SPD, `λ_max, λ_min` its extreme eigenvalues:
`(Bx,x)(B⁻¹x,x)/(x,x)² ≤ (λ_max + λ_min)²/(4λ_maxλ_min)` for all `x ≠ 0`. Lean (checked):
`lemma_5_8 [Nonempty (Fin n)] (hB : B.PosDef) (hx : x ≠ 0) : ((B *ᵥ x) ⬝ᵥ x) * ((B⁻¹ *ᵥ x) ⬝ᵥ x) / (x ⬝ᵥ x) ^ 2 ≤ (lambdaMax hB.1 + lambdaMin hB.1) ^ 2 / (4 * lambdaMax hB.1 * lambdaMin hB.1)`.
Backbone: 2.4.3 `kantorovich_inequality` (finite-dimensional, `hspec : ∀ μ, HasEigenvalue A μ → μ ∈ Icc lmin lmax`).
Route: `posDef_iff_isSymmetricCoercive`; `HasEigenvalue (toEuclideanLin B) μ ↔ μ ∈ spectrum ℝ B`
(`hasEigenvalue_iff_mem_spectrum`, `spectrum_toLpLin`) and `spectrum_eq_image_range` give
`μ ∈ [λ_min, λ_max]`; glue `toEuclideanLin B⁻¹ = (toEuclideanLin B)⁻¹` (whatever inverse 2.4.3
uses — G11). Status: `needs-equivalence`.

**R-5.18 Theorem 5.9.** Book: `A` SPD: the `A`-norms of the errors `d_k = x* − x_k` of Alg 5.2
satisfy `‖d_{k+1}‖_A ≤ ((λ_max − λ_min)/(λ_max + λ_min)) ‖d_k‖_A`, and Alg 5.2 converges for any
`x₀`. Lean (checked): `thm_5_9 [Nonempty (Fin n)] (hA : A.PosDef) (hstar : A ⬝ xstar = b) (k) : E_A A xstar ((sdStep A b)^[k+1] x₀) ≤ (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) * E_A A xstar ((sdStep A b)^[k] x₀)`;
`thm_5_9_tendsto : Tendsto (fun k => (sdStep A b)^[k] x₀) atTop (𝓝 xstar)`. Backbone: 2.4.3
`steepestDescent_energyNorm_le`; 2.1.5 `energyNorm_le/le_energyNorm` (norm equivalence) for the
convergence. Route: contraction factor `< 1` (since `λ_min > 0`), geometric decay, norm equivalence.
Status: `needs-equivalence` (request G9: state the `Tendsto` corollary in the backbone, it is
generic).

**R-5.19 Algorithm 5.3 and its minimization property.** Book: MR (`A` positive definite,
`A + Aᵀ` SPD): `v = r`, `w = Ar`, `α = (Ar, r)/(Ar, Ar)`; Alg 5.3 (`α = (p, r)/(p, p)`, `p = Ar`);
each step minimizes `f(x) = ‖b − Ax‖₂²` in the direction `r`. Lean: `mrAlg_spec`,
`mrStep_isMinOn : IsMinOn (fun x' => R_A A b x' ^ 2) {x + α • r | α} (mrStep A b x)` (via R-5.7 with
`K = span{r}`). Backbone: 2.4.3 `minimalResidualStep`, 2.4.2. Status: `surface-only` + `direct`.

**R-5.20 Theorem 5.10.** Book: `A` real positive definite, `μ = λ_min((A + Aᵀ)/2)`, `σ = ‖A‖₂`:
the residuals of Alg 5.3 satisfy `‖r_{k+1}‖₂ ≤ (1 − μ²/σ²)^{1/2} ‖r_k‖₂`, and Alg 5.3 converges for
any `x₀`. Lean (checked, scoped `Matrix.Norms.L2Operator`):
`thm_5_10 [Nonempty (Fin n)] (hA : A.IsPositiveReal) (k) : ‖b - A ⬝ ((mrStep A b)^[k+1] x₀)‖ ≤ Real.sqrt (1 - lambdaMin (hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) * ‖b - A ⬝ ((mrStep A b)^[k] x₀)‖`;
`thm_5_10_tendsto : Tendsto (fun k => (mrStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ ⬝ b))`. Backbone: 2.4.3
`minimalResidual_norm_le` (`c`-coercive bounded `A`: `‖r'‖ ≤ √(1 − c²/‖A‖²) ‖r‖`), R-1.2 (`c = μ`),
`Matrix.l2_opNorm_def`/`cstar_norm_def` (`‖A‖₂ = ‖toEuclideanCLM A‖`). Route: `0 < μ ≤ σ` so the
factor is `< 1`; `r_k → 0` and `x_k = A⁻¹(b − r_k)`. Status: `needs-equivalence`.

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
sphere for `ρ < 1`). Backbone: 2.4.3 gives only the bound (5.15); the exact identity (5.18) is
requested (G9). Status: `GAP` for (5.18)/(5.20) as backbone items (small; can be `surface-only`
meanwhile since they are two-line inner-product identities), `surface-only` for the `sin ∠` form.

**R-5.22 Algorithm 5.4 (RNSD) and its convergence.** Book: `v = Aᵀr`, `w = Av`, `α = ‖v‖₂²/‖Av‖₂²`
(5.21); Alg 5.4 with the recursive residual; each step minimizes `f(x) = ‖b − Ax‖₂²` along
`−∇f = 2Aᵀr`; the method is SD applied to the normal equations `AᵀAx = Aᵀb`, and since `AᵀA` is
SPD for nonsingular `A`, it converges whenever `A` is nonsingular (by Thm 5.9).
Lean: `rnsdAlg_spec`, `rnsdStep_eq_sdStep_normal : rnsdStep A b x = sdStep (Aᵀ * A) (Aᵀ ⬝ b) x`,
`rnsdStep_isMinOn : IsMinOn (fun x' => R_A A b x' ^ 2) {x + α • (Aᵀ ⬝ r) | α} (rnsdStep A b x)`,
`posDef_transpose_mul_self (hA : IsUnit A) : (Aᵀ * A).PosDef`,
`thm_rnsd (hA : IsUnit A) : ‖r_{k+1}‖ ≤ (λ_max(AᵀA) − λ_min(AᵀA))/(λ_max + λ_min) * ‖r_k‖ ∧ Tendsto x_k (𝓝 (A⁻¹ ⬝ b))`
(the `AᵀA`-norm of the error is the residual norm). Backbone: 2.4.3 `residualNormSDStep` ("SD on
the normal equations is a one-line corollary"), R-5.18, Mathlib `PosDef.conjTranspose_mul_self`.
Status: `direct` (via R-5.18) + `surface-only` (algebraic identities).

### §5.4 Additive and multiplicative processes (`Ch05/Additive.lean`)

**R-5.23 Block relaxations are projection processes.** Book: each inner step of Alg 4.1/4.2 is an
orthogonal projection process over `K_i = span(V_i)`; (4.17) is exactly (5.7) with `W = V = V_i`.
Lean: `blockCorrection_eq_projStep : x + V_i *ᵥ (V_iᵀ A V_i)⁻¹ *ᵥ (V_iᵀ *ᵥ (b − A x)) = projStep A b (V_i) (V_i) x`
(no overlap, `η = 1`). Status: `surface-only` (definitional).

**R-5.24 (5.22)–(5.23) residual of the additive procedure.** Book: `r_{k+1} = (I − Σ_i P_i) r_k`
with `P_i = AV_i(V_iᵀAV_i)⁻¹V_iᵀ`; with parameters `ω_i`, `r_{k+1} = (I − Σ ω_i P_i) r_k`; each `P_i`
is the projector onto `span(AV_i)` orthogonal to `span(V_i)`.
Lean: `residual_additiveStep (h : ∀ i, IsUnit ((V i)ᵀ * A * V i)) : b - A ⬝ additiveStep 𝒱 ω A b x = (1 - ∑ i, ω i • toEuclideanLin (P_i 𝒱 A i)) (b - A ⬝ x)`,
`P_i_isProjOnto (hV : (V i).IsBasisOf K_i) (h) : ∀ z, IsProjOnto (K_i.map A') K_i z (P_i ⬝ z)`.
Backbone: 2.4.4 (phase 2) residual formula; D6/R-1.9 (`P_i = obliqueProj (A * V i) (V i)`, and
`IsBasisOf (A * V i) (K_i.map A')` follows from `IsUnit (V_iᵀAV_i)`). Status: `surface-only` now for
the identity (one line of algebra), `needs-equivalence` with 2.4.4 later.

**R-5.25 Least-squares option and exactness.** Book: with `L_i = AK_i`, `P_i = AV_i((AV_i)ᵀAV_i)⁻¹(AV_i)ᵀ`
is the orthogonal projector onto `AK_i`, `r_{k+1} = (I − ΣP_i)r_k`; if the `AV_i` are mutually
orthogonal and the total rank of the `P_i` is `n`, then `I − ΣP_i = 0` and the exact solution is
obtained in one outer step; the maximal reduction occurs when the `V_i` are `A`-orthogonal.
Lean: `obliqueProj_self_isOrthogonalProjector (hV : V.IsBasisOf M) : (obliqueProj V V).IsOrthogonalProjector ∧ range … = M`,
`sum_starProjection_eq_one (horth : ∀ i ≠ j, (A V_i)ᵀ (A V_j) = 0) (hrank : ∑ i, rank (A V_i) = n) : ∑ i, (K_i.map A').starProjection = 1`.
Backbone/Mathlib: D7; `OrthogonalFamily`/`DirectSum.IsInternal` for the sum. Status: `surface-only`
(the sum lemma is a candidate for 2.4.4).

**R-5.26 Algorithm 5.6.** Book: multiplicative procedure = successive projection steps on
`K_1, …, K_p`; it is the analogue of block Gauss–Seidel. Lean: `multiplicativeSweep_eq_blockGs`
(when `V_i` are identity columns). Status: `surface-only` (definitional).

## Gaps and requests to the backbone

1. **G1 (2.1.11 `Complexify`, 2.3.1) — real forms of Thm 4.1.** Provide for `G : Matrix n n ℝ`:
   `Matrix.spectralRadius G < 1 ↔ Tendsto (fun k => G ^ k) atTop (𝓝 0)`,
   `Matrix.spectralRadius G < 1 → IsUnit (1 − G)`, the `(∀ x, Gᵏx → 0)` form (already listed), and
   `complexify` commuting with `diagPart`, `strictLower`, `strictUpper`, `⁻¹`, `*ᵥ` (for R-4.20).
   Norm preservation: the plan lists only `l∞` and Frobenius; R-4.13 needs `‖complexify G‖₂ = ‖G‖₂`
   (or, simpler, a lemma "Gelfand's limit does not depend on the norm": `Tendsto (‖Gᵏ‖^(1/k))` for
   one norm implies it for any equivalent norm, since `C^{1/k} → 1`).
2. **G2 (2.1.3) — arbitrary consistent matrix norms.** Saad's Cor 4.2 and the remark `|λ| ≤ ‖A‖`
   quantify over *any* matrix norm (Saad §1.5: a vector norm on `ℂ^{n×n}` with `‖AB‖ ≤ ‖A‖‖B‖`),
   i.e. an `AlgebraNorm ℝ (Matrix n n ℝ)` / `AlgebraNorm ℂ (Matrix n n ℂ)` (Mathlib
   `Mathlib/Analysis/Normed/Unbundled/AlgebraNorm`). Needed: `spectralRadius_le_algebraNorm
   (N : AlgebraNorm ℂ A) [FiniteDimensional ℂ A] (a) : spectralRadius ℂ a ≤ N a` (proof:
   `ρ(a)ᵏ ≤ ‖aᵏ‖_std ≤ C·N(aᵏ) ≤ C·N(a)ᵏ`, `C^{1/k} → 1`, using that every seminorm on a
   finite-dimensional space is bounded by the standard norm) and its real-matrix corollary
   `N G < 1 → Tendsto (G^k) (𝓝 0)`. Without it Cor 4.2 is only available for the induced `p`-norms
   (`lpOpNorm p`, R-4.12).
3. **G3 (2.1.7 `ObliqueProjection`) — projectors from bases.** Add the matrix representation:
   for `V W : Matrix n (Fin m) 𝕜` whose columns are bases of `K`, `L` (a `Matrix.IsBasisOf`
   predicate, or `Basis (Fin m) 𝕜 K` plus the coordinate map), `IsUnit (Wᴴ * V) ↔ K ⊓ Lᗮ = ⊥`, and
   `toEuclideanLin (V * (Wᴴ * V)⁻¹ * Wᴴ) = obliqueProjection K L`; orthonormal case
   `toEuclideanLin (V * Vᴴ) = K.starProjection`. Saad (1.66), (5.7), §5.4 `P_i` and 2.4.1's own
   `isPetrovGalerkin_iff_toMatrix` all reduce to this one lemma.
4. **G4 (2.3.4 `RegularSplitting`, 2.1.12) — phase 2.** Thm 4.4 and its M-matrix corollary need
   Thm 1.29 and the weak Perron theorem as planned. Request that 2.3.4 state Thm 4.4 exactly as
   `IsRegularSplitting A M N → (spectralRadius (M⁻¹ * N) < 1 ↔ IsUnit A ∧ 0 ≤ A⁻¹)` with the
   entrywise order spelled out (or with the 2.1.12 order plus an unfolding lemma), and that the
   M-matrix definition follow Saad Def 1.30 verbatim (D14).
5. **G5 (2.3.3 `DiagDominant`) — irreducibility and column dominance.** (a) Saad's
   irreducibility applies to arbitrary matrices; Mathlib's `Matrix.IsIrreducible` requires
   nonnegative entries. Adopt `Matrix.IsIrreducible (A.map ‖·‖)` (D15) as the backbone
   definition (or add `Matrix.IsIrreducible'`) so that Thm 4.7, Cor 4.8 (irreducible part) and
   Thm 4.9 (irreducible part) can be stated now even if proved in phase 2. (b) Add the column
   versions of the Jacobi/GS convergence theorems (Def 4.5 as printed uses column sums, §6):
   Jacobi via `D G_J D⁻¹ = (E+F)D⁻¹` and the `l1` operator norm (or `linfty` of the transpose), GS via
   the Cor 4.8 argument applied to `N − λM` for `|λ| ≥ 1` (this argument also proves the
   irreducible case, so it may be the cheapest uniform proof).
6. **G6 (2.3.2 `Splitting`) — SSOR and backward GS.** State `Matrix.ssorSplitting ω` with
   `m = (ω(2−ω))⁻¹ (D − ωE) D⁻¹ (D − ωF)` (Saad (4.27)) and prove
   `ssorSplitting.iterMatrix = (D − ωF)⁻¹(ωE + (1−ω)D)(D − ωE)⁻¹(ωF + (1−ω)D)` (4.13) and
   `m⁻¹ b = ω(2−ω)(D − ωF)⁻¹D(D − ωE)⁻¹ b` (4.14); add `backwardGaussSeidelSplitting` (`m = D − F`)
   and `backwardSorSplitting`, or a generic `Ring.Splitting.ofUnit (m) (h : IsUnit m) : Splitting a`
   with `n := m − a`. The surface's SOR/SSOR *steps* are defined by the book's equations (4.12)
   and compared to these.
7. **G7 (2.3.5 `SPD`) — Thm 4.10 both directions.** The plan lists Householder–John/
   Ostrowski–Reich as `M + Mᴴ − A` coercive ⇒ `ρ(M⁻¹N) < 1`. Saad's Thm 4.10 is an *iff*: for
   symmetric `A` with positive diagonal and `0 < ω < 2`, SOR converges (`ρ(G_ω) < 1`) iff `A` is
   positive definite. Add the converse: `A` symmetric, `Q := M + Mᵀ − A` positive definite,
   `ρ(M⁻¹N) < 1` ⇒ `A` positive definite (proof: the identity
   `e_kᵀAe_k − e_{k+1}ᵀAe_{k+1} = (e_k − e_{k+1})ᵀQ(e_k − e_{k+1}) ≥ 0` with `e_k → 0` forces
   `e₀ᵀAe₀ ≥ 0`, and `= 0` with `e₀ ≠ 0` would force `e₁ = e₀`, contradicting `e_k → 0`).
8. **G8 (2.3.5) — Young's theory, precise statements.** The plan devotes one sentence to Prop
   4.12–Thm 4.16. Needed statements (over ℂ after `complexify`): Prop 4.12 (block anti-diagonal:
   spectrum symmetric under negation; `spectrum (αL + α⁻¹U) = spectrum B`), Def 4.13/T-matrix
   definitions (D16, please reuse verbatim), Prop 4.14 (order-preserving permutation to a T-matrix),
   Prop 4.15 (`α`-independence for consistently ordered `A`), Thm 4.16 (the relation
   `(λ + ω − 1)² = λω²μ²` both ways, with `λ ≠ 0` in the forward direction), and (4.47) under the
   hypotheses "Jacobi eigenvalues real, `ρ(B) < 1`" with the value `ρ(G_{ω_opt}) = ω_opt − 1`.
   Kress Def 4.13–Cor 4.16 uses the same objects, so these can be shared.
9. **G9 (2.4.1–2.4.3 `Projection`) — bases form, `iff`s and sequence corollaries.**
   (a) `isPetrovGalerkin_iff_toMatrix` should be stated with explicit `V, W` and `IsBasisOf`
   hypotheses, together with `IsUnit (Wᴴ A V) ↔ (∀ u ∈ K, u ≠ 0 → A u ∉ Lᗮ) ↔ ∀ b x₀, ∃! x, IsPetrovGalerkin A b x₀ K L x`;
   Prop 5.1 (i)/(ii) then follow from the coercive/injective `∃!` lemmas already planned.
   (b) `isPetrovGalerkin_span_singleton_iff : (⟪A v, w⟫ ≠ 0) → (IsPetrovGalerkin A b x (span {v}) (span {w}) x' ↔ x' = step1 A b v w x)`.
   (c) The exact one-step identity for the MR step, `‖r'‖² = ‖r‖²(1 − ⟪Ar,r⟫²/(‖r‖²‖Ar‖²))`
   (Saad (5.18)), from which (5.15), (5.20) and the `sin ∠` form follow; likewise the SD identity
   `‖d'‖_A² = ‖d‖_A²(1 − ⟪r,r⟫²/(⟪Ar,r⟫⟪A⁻¹r,r⟫))` used in the proof of Thm 5.9.
   (d) A generic "per-step contraction with factor `< 1` ⇒ `Tendsto` to the solution" corollary
   for `sdStep`/`mrStep` iterations (the surface needs it three times: Thm 5.9, Thm 5.10, RNSD).
   (e) `isGalerkin_iff_energy_min` in both directions (the prototype has one).
10. **G10 (2.2 `Perturbation`) — first-order perturbation.** Add (i) the `IsLittleO` form of
    (1.76) (`‖x(ε) − x‖/‖x‖ ≤ |ε| κ (…) + o(ε)`) derived once from `relative_error_le_condNumber`,
    and (ii) differentiability of the solution map `ε ↦ (A + εE)⁻¹(b + εe)` at `0` with derivative
    `A⁻¹(e − Ex)` (Saad (1.75); Kress and Higham state the same). Also state 2.2 for `PiLp p`
    (any `p`) or for a general `E ≃L[𝕜] E` on a finite-dimensional space, so that `κ_p` for every
    `p` specializes (D8); 2.1.2 currently mentions only the scoped `p = 2, ∞` instances — consider
    adding `Matrix.lpOpNorm p` / `Matrix.condNumber p` to 2.1.2 itself (Higham Ch. 6 uses all `p`).
11. **G11 (2.1.4/2.4.3 glue).** Small lemmas the Ch. 1/5 files need repeatedly:
    `Matrix.toEuclideanLin_inv : toEuclideanLin A⁻¹ = (inverse used by 2.4.3) (toEuclideanLin A)`,
    `Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff : HasEigenvalue (toEuclideanLin A) μ ↔ μ ∈ range hA.eigenvalues`,
    Rayleigh bounds in matrix form `λ_min(H) ‖u‖² ≤ re (star u ⬝ᵥ H *ᵥ u) ≤ λ_max(H) ‖u‖²`
    (4.1 lists them abstractly), and `posDef_iff_isSymmetricCoercive` also for real `Matrix.PosDef`
    with `IsSymm` (D1).
12. **G12 (2.4.4 `Additive`, phase 2).** When written, state the residual identity with weights
    `ω_i` (Saad (5.23)), define the family by matrices `V_i` as in D20 (so that `P_i = obliqueProj (A V_i) V_i`
    is `rfl`), include the least-squares variant and the "orthogonal projectors onto mutually
    orthogonal subspaces of total dimension `n` sum to `1`" lemma (R-5.25).
13. **G13 (4.1 `Eigen/Perturbation`) — Bendixson's exact form.** State `bendixson` for
    `A : Matrix n n ℂ` with `H = hermitianPart A`, `S = skewPart A` (D2) and conclusions
    `λ_min(H) ≤ re λ ≤ λ_max(H)`, `λ_min(S) ≤ im λ ≤ λ_max(S)` in terms of
    `Matrix.IsHermitian.eigenvalues` extremes, so that R-1.3 is a one-line specialization.
14. **G14 (2.3.1) — `Stationary` for `Fin n → ℝ`.** `Stationary.step` is stated for
    `E →L[𝕜] E`; the surface iterates on `Fin n → ℝ` with `G *ᵥ`. Either add the
    `Matrix`-level wrappers (`Matrix.affineStep`, `step_iterate_sub`) in 2.3.2 or make the 2.3.1
    statements `LinearMap`-valued (continuity is automatic in finite dimension), to avoid
    `toEuclideanCLM` round trips in every Ch. 4 proof.

## Left out

Algorithms without theorems, examples, exercises (with the reason), and the Chapter 1 black boxes.

* Figures 1.1–1.2, 4.1–4.5, 5.1–5.4: illustrations.
* Example 1.3 (`A = [[1, 1],[10⁴, 1]]` eigenvalue rectangle), Example 1.4 (2×2 existence cases):
  numerical examples; Example 1.5 is kept as optional R-1.20 because 2.1.2 assigns it to the surface.
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
  (Gelfand — backbone 2.1.3), P-5.1 (Exercise 1 referenced in Example 5.1), P-5.15 (referenced
  after (5.23)). None is a theorem prerequisite beyond what the results above already state.
* The `B`-inner-product remark "sometimes an HPD `B` makes `A` Hermitian" (R-1.5): kept optional.

Chapter 1 black boxes cited by the selected sections (where the backbone provides them):

| Cited fact | Used by | Provided by |
|---|---|---|
| Thm 1.10 (`Aᵏ → 0 ⟺ ρ(A) < 1`), Thm 1.11 (Neumann series, `I − A` nonsingular), Thm 1.12 / P-1.10 (Gelfand `lim ‖Aᵏ‖^{1/k} = ρ`) | Thm 4.1, Cor 4.2, §4.2.1 convergence factors | 2.1.3 `spectralRadius_lt_one_iff_tendsto_pow`, `summable_pow_iff_spectralRadius_lt_one`, Gelfand via Mathlib; 2.1.11 for real matrices |
| `ρ(A) ≤ ‖A‖` for any matrix norm (§1.5/§1.8.4) | Cor 4.2, `|λ| ≤ ‖A‖` | Mathlib `spectralRadius_le_nnnorm` for the scoped norms; general consistent norms: G2 |
| Jordan canonical form (Thm 1.8) | §4.2.1 specific convergence factor | not provided (deliberately, §1.1); left out |
| Schur form (Thm 1.9) | not cited in the selected sections | Mathlib `Matrix.schur_triangulation` (listed in §8.1 for `Ch01/Spectral`) |
| Normal matrices / spectral theorem for Hermitian matrices (Thm 1.14, 1.19–1.20: "unitarily similar to a real diagonal matrix") | Lemma 5.8 proof, Thm 1.34/1.35 proofs | Mathlib `Matrix.IsHermitian.spectral_theorem`, `eigenvalues`, `eigenvectorBasis` |
| Min–max / Rayleigh-quotient bounds (Thm 1.21, (1.40)) | Thm 1.34 (`α = λ_min(H)`), Thm 1.35, Thm 5.10 | 4.1 Rayleigh bounds / 2.1.4 `coercive_const_eq_iInf_eigenvalues`; Mathlib `hasEigenvalue_iInf/iSup_of_finiteDimensional` |
| Perron–Frobenius (Thm 1.25), Thm 1.29 (`B ≥ 0`: `ρ(B) < 1 ⟺ (I−B)⁻¹ ≥ 0`) | Thm 4.4 | 2.3.4 phase 2 (weak Perron) |
| M-matrices (Def 1.30; Thm 1.31–1.33 not needed) | remark after Thm 4.4 | D14 (definition only) |
| Irreducibility (§1.10 / §3 adjacency graph) | Def 4.5, Thm 4.7, Cor 4.8, Thm 4.9 | Mathlib `Matrix.IsIrreducible` via `A.map ‖·‖` (G5) |
| (1.13.1) existence theory | §1.13 | Mathlib |
| Exercise 37 (`A + εE` invertible for small `ε`) | §1.13.2 | 2.1.1 |

## OCR uncertainties

1. **Definition 4.5 (lines ≈ 5327–5350).** As transcribed, all three dominance conditions read
   `|a_jj| ≥ Σ_{i=1, i≠j}^{n} |a_ij|, j = 1,…,n` — the sum runs over the *row* index `i` with the
   column `j` fixed (column sums). The proofs of Thm 4.6 (4.37)–(4.38) and Thm 4.9 use row sums
   `Σ_{j≠i} |a_ij|`, and Cor 4.8's proof again writes the column form. The `images` folder holds only
   figure crops, so the page could not be checked; the second edition is known to have this
   index swap. The surface provides both conventions (D15) and states Cor 4.8/Thm 4.9 for both;
   Thm 4.6 is stated in row form with a column corollary.
2. **Theorem 4.9 proof.** "`|ξ_i| ≤ 1` for `i ≠ 1`" should be "`i ≠ m`" (typo, harmless).
3. **Theorem 1.35 proof.** "`𝔗m(λ_j)`" is `Im(λ_j)` (glyph); statement unaffected.
4. **Theorem 4.16.** The book reuses `M_SOR` for the SOR *iteration matrix*
   `(D − ωE)⁻¹(ωF + (1−ω)D)`, whereas (4.26) uses `M_SOR` for the preconditioner
   `ω⁻¹(D − ωE)`; not an OCR issue but the surface names them `sorIterMatrix` vs `M_sor`.
5. **Orthogonal projector norm (§1.12.4).** "`‖P‖₂ = 1` for any orthogonal projector" needs
   `P ≠ 0` (`P = 0` is an orthogonal projector onto `{0}`); stated with `P ≠ 0` (R-1.13).
6. **Corollary 1.39.** "`min_{y∈M} ‖x − y‖₂ = ‖x − y*‖₂` iff `y* ∈ M` and `x − y* ⟂ M`" is read with
   `y*` ranging over `M` (a `y* ∉ M` at the same distance would break the literal "iff"); the
   surface uses `IsLeast` over `M`, which includes membership (R-1.15).
7. **§5.1.2 "`WᵀAV` is nonsingular iff no vector of `AK` is orthogonal to `L`".** Literally false
   for `A = 0` (`AK = {0}`); read as "`u ∈ K`, `u ≠ 0` ⇒ `Au ∉ Lᗮ`" (R-5.3).
8. **Proposition 5.6.** The proof presupposes that `Q_K^L` exists (`K ∩ Lᗮ = {0}`); without it the
   statement fails, so the hypothesis is added (R-5.11). Its proof also says "`x̃` is a nonzero
   vector in `K`", which is not needed.
9. **Theorem 4.10.** "SOR converges for any `x₀`" must be read as `ρ(G_ω) < 1` / convergence to the
   solution for every right-hand side: for singular positive semidefinite symmetric `A` with
   positive diagonal (e.g. the all-ones `2×2` matrix, `ω = 1`, `b = 0`) the iterates converge for
   every `x₀` although `A` is not positive definite (R-4.21).
10. **Theorem 5.10.** The word "Proof." is run into the statement paragraph in the OCR; the
    statement ends at "for any initial guess `x₀`".
11. **§5.4.** A running page header "### 5.4. ADDITIVE AND MULTIPLICATIVE PROCESSES" appears after
    the problems (line ≈ 6879); it is not a section.
12. **(4.13).** The product `G_ω` is split over two display lines with a trailing "×"; read as one
    product of four factors.
13. **Prop 5.1 proof** cites "see Chapter 1" for "`A` positive definite ⇒ `VᵀAV` positive definite";
    no numbered statement there covers the non-symmetric case — R-5.5 supplies it.
