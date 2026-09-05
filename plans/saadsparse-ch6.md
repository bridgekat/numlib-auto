<!--
The per-result Lean statements quoted below are historical wherever the result exists: the tracker
plan (the TOML group files beside this document) is the authority on which declarations exist, and
the source is the authority on what they say. Where the two disagree, this document is wrong.

What is worth reading here is the book alignment: which numbered result maps to which declaration,
how each book-specific definition relates to the backbone, what was deferred and why, and what was
deliberately left out.
-->

# Surface plan: Saad, Iterative Methods — Chapter 6

Surface library `SaadSparse`, chapter file set `NumlibSurface/SaadSparse/Chapter06/*.lean`, importing only the
backbone `Numlib` (backbone references are to `backbone.md` § numbers and to declarations
under `Numlib/`, cited with their module). Chapter 6 is the book's presentation of the Krylov
spine: every numbered result is either a statement about *the* Galerkin / minimal-residual iterate
(backbone specs `Krylov.IsGalerkinIterate`, `Krylov.IsMinResIterate`, §3.4) transported to a
concrete implementation (Arnoldi/Lanczos/Givens bookkeeping, §3.2–3.6), or a convergence bound
(§3.9–3.10, §2.1.9). The surface therefore consists of (a) *book-exact* definitions of the 24
algorithms as Lean functions over `Matrix (Fin n) (Fin n) 𝕜` acting on `EuclideanSpace 𝕜 (Fin n)`,
(b) an equivalence lemma per algorithm ("the book's algorithm computes the backbone object /
satisfies the backbone spec"), and (c) the numbered results as one-line specializations.
Truncated/restarted variants (FOM(m), IOM, DIOM, GMRES(m), QGMRES, DQGMRES, ORTHOMIN(k), GCR(m))
are defined faithfully and only the properties the book actually proves about them are stated
(§2 says which, per variant).

## 1. Conventions and file layout

* `𝕜` with `[RCLike 𝕜]`, `n : ℕ`, `𝔼 := EuclideanSpace 𝕜 (Fin n)`, `A : Matrix (Fin n) (Fin n) 𝕜`,
  `op A := Matrix.toEuclideanLin A : 𝔼 →ₗ[𝕜] 𝔼`. Definitions and algorithms are polymorphic in `𝕜`
  (so §6.5.9 "complex GMRES" is the same code). Each *result* is stated at the book's generality:
  `𝕜 := ℝ` where the book says real (all of §6.2–6.11 except the places listed next), `ℂ` for
  §6.5.9, Thm 6.11 (proof in `ℂ^m`), Lemma 6.23/Thm 6.24 (`A^H`), Prop 6.32/Cor 6.33 (complex
  eigenvalues). Where the backbone proof is field-agnostic an `RCLike` version may be added as a
  bonus lemma, but the book-faithful statement is the `ℝ`/`ℂ` one.
* Book inner product `(x, y) = ∑ x_i ȳ_i` (Saad (1.3)) is Mathlib's `inner 𝕜 y x`; so the book's
  `h_ij = (A v_j, v_i)` is `inner 𝕜 (v i) (A (v j))`, exactly the backbone `Arnoldi.coeff`.
* Indices: Arnoldi/Lanczos/IOP vectors are `ℕ`-indexed and 0-based (`v j` is the book's `v_{j+1}`,
  `coeff i j` is `h_{i+1,j+1}`); matrices `V_m : Matrix (Fin n) (Fin m) 𝕜`,
  `H_m : Matrix (Fin m) (Fin m) 𝕜`, `H̄_m : Matrix (Fin (m+1)) (Fin m) 𝕜` with `Fin` indices
  shifted by one from the book. CG/CR/GCR iterates are 0-based exactly as in the book. The Givens
  quantities `c_i, s_i, γ_i` are likewise 0-based functions of `ℕ` (D8).
* "Stop" semantics: a division by a vanishing norm yields `0` (Lean), which reproduces the book's
  "if `h_{j+1,j} = 0` then Stop" for the vectors (all later vectors are `0`); for FOM/GMRES the
  book's "set `m := j`" is implemented as `m' := min m (grade A r₀)`.
* Matrix ↔ operator glue is `Numlib/Analysis/Matrix/ToEuclideanLin.lean` (`Matrix.toEuclideanLin_pow`,
  `toEuclideanLin_mul`, `toEuclideanLin_conjTranspose`, `krylov_subspace_toEuclideanLin`,
  `toEuclideanLin_apply_eq_sum` for `V_m y = ∑ y_j • v_j`,
  `IsHermitian.hasEigenvalue_toEuclideanLin_iff`, `IsHermitian.isSymmetricBoundedBy_toEuclideanLin`,
  `l2_opNorm_eq_norm_toEuclideanLin`), together with Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`
  and `Matrix.posDef_iff_isSymmetricCoercive` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`).

Proposed files (in dependency order):

| File | Book | Contents |
|---|---|---|
| `Ch06/Basic.lean` | §6.1–6.2 | `op`, `krylov`, `grade` (minimal-polynomial degree), equivalence with `Krylov.subspace`/`Krylov.grade`; Prop 6.1–6.3 |
| `Ch06/Arnoldi.lean` | §6.3 | Alg 6.1–6.3, `V_m, H_m, H̄_m, w_m`; Prop 6.4–6.6, (6.6)–(6.13); P-6.1 |
| `Ch06/FOM.lean` | §6.4 | (6.16)–(6.18), Alg 6.4 (FOM), 6.5 (FOM(m)), 6.6 (IOP), 6.7 (IOM), 6.8 (DIOM); Prop 6.7–6.8, (6.19)–(6.24); P-6.22 |
| `Ch06/Residual.lean` | §6.4–6.5 preliminaries | `r₀`, `β`, `v₁`, `e₁`, `mEff` and the bridges from the book's unit starting vector to the backbone's residual-indexed Arnoldi data; shared by FOM, GMRES, Givens and DQGMRES |
| `Ch06/Givens.lean` | §6.5.3–6.5.4, 6.5.9 | (6.34)–(6.47), (6.80)–(6.81), the rotation data; **precedes `GMRES.lean`**, since `y_m = R⁻¹ g` needs D8 |
| `Ch06/GMRES.lean` | §6.5.1–6.5.2, 6.5.5 | (6.25)–(6.33), Alg 6.9 (GMRES), 6.10 (Householder GMRES), 6.11 (GMRES(m)); Prop 6.9–6.10; P-6.5 |
| `Ch06/DQGMRES.lean` | §6.5.6 | Alg 6.12 (QGMRES), 6.13 (DQGMRES), (6.48)–(6.58), Thm 6.11; P-6.25 |
| `Ch06/Relations.lean` | §6.5.7 | (6.62)–(6.75), Prop 6.12–6.17, Lemma 6.16, Cor 6.14; P-6.9, P-6.13, P-6.14 |
| `Ch06/Smoothing.lean` | §6.5.8 | Alg 6.14 (MRS), QMRS, Lemma 6.18, (6.76)–(6.79); P-6.26 |
| `Ch06/Lanczos.lean` | §6.6 | Thm 6.19, `T_m`, Alg 6.15, §6.6.2 (6.85) |
| `Ch06/CG.lean` | §6.7 | (6.86)–(6.103), Alg 6.16 (Lanczos method), 6.17 (D-Lanczos), 6.18 (CG), 6.19 (three-term CG), Prop 6.20; P-6.17, P-6.19 |
| `Ch06/CR.lean` | §6.8 | Alg 6.20 and its invariants |
| `Ch06/GCR.lean` | §6.9 | Lemma 6.21, Alg 6.21 (GCR), ORTHOMIN(k), ORTHODIR, GCR(m) |
| `Ch06/FaberManteuffel.lean` | §6.10 | Prop 6.22, `ν(A)`, `CG(s)`; Lemma 6.23, Thm 6.24 (deferred, §4) |
| `Ch06/Chebyshev.lean` | §6.11.1–6.11.2 | (6.109)–(6.121), Thm 6.25; Lemma 6.26, Thm 6.27 (deferred, §4) |
| `Ch06/Convergence.lean` | §6.11.3–6.11.4 | Lemma 6.28, Thm 6.29, (6.122)–(6.128), Thm 6.30, Lemma 6.31, Prop 6.32; Cor 6.33 (deferred, §4) |
| `Ch06/Block.lean` | §6.12 | Alg 6.22–6.24, (6.129)–(6.136), block-FOM/GMRES specifications (relations deferred, §4) |
| `Ch06/Problems.lean` | Problems | P-6.1, 6.5, 6.9, 6.13, 6.14, 6.17, 6.22, 6.25, 6.26, 6.29 (cited by the text, or supplying proofs the text omits) |

## 2. Book-specific definitions and algorithms

Each entry: book formulation → Lean surface sketch → backbone counterpart → equivalence lemma.
All Lean below is a sketch (namespace `SaadSparse.Ch06`, `variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]`,
`local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)`, `open Matrix` for `ᴴ`).

### D1. Operator of a matrix, Krylov subspace (6.2), grade (§6.2)

Book: `𝒦_m(A, v) = span{v, Av, …, A^{m−1} v}`; the grade of `v` is the degree of the minimal
polynomial of `v` w.r.t. `A` (lowest-degree nonzero monic `p` with `p(A) v = 0`); by Cayley–Hamilton
it is `≤ n`.

```lean
abbrev op (A : Matrix (Fin n) (Fin n) 𝕜) : 𝔼 →ₗ[𝕜] 𝔼 := Matrix.toEuclideanLin A
/-- (6.2). -/
def krylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (m : ℕ) : Submodule 𝕜 𝔼 :=
  Submodule.span 𝕜 (Set.range fun i : Fin m => Matrix.toEuclideanLin (A ^ (i : ℕ)) v)
/-- degree of the minimal polynomial of `v` w.r.t. `A` (exists by Cayley–Hamilton). -/
noncomputable def grade (A) (v : 𝔼) : ℕ := by
  classical
  exact Nat.find (p := fun d => ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧
      Matrix.toEuclideanLin (aeval A p) v = 0)
    ⟨_, A.charpoly, A.charpoly_monic, rfl, by simp [Matrix.aeval_self_charpoly]⟩
noncomputable def minpolyVec (A) (v : 𝔼) : 𝕜[X]   -- a monic witness of degree `grade A v`
```

Backbone (§3.1, `Numlib/Krylov/Subspace.lean`): `Krylov.subspace`, `Krylov.grade`
(`Module.finrank 𝕜 (fullSubspace A v)`, equal to `sInf {m | A^m v ∈ 𝒦_m}` by `Krylov.grade_eq_sInf`),
`Krylov.grade_le_finrank`, `Krylov.subspace_eq_map_degreeLT`, `Krylov.mem_subspace_iff_exists_aeval`,
`Krylov.grade_le_iff`, `Krylov.pow_apply_mem_subspace_iff_exists_monic`
(`A^m v ∈ 𝒦_m ↔ ∃ p, p.Monic ∧ p.natDegree = m ∧ aeval A p v = 0`); glue
`Matrix.krylov_subspace_toEuclideanLin`, `Matrix.toEuclideanLin_pow`. The finite-grade hypothesis
`[FiniteDimensional 𝕜 (fullSubspace A v)]` of §3.1 is automatic on `𝔼`.
Equivalence lemmas: `krylov_eq : krylov A v m = 𝒦[op A, v] m` (the symmetric form of
`Matrix.krylov_subspace_toEuclideanLin`); `grade_eq : grade A v = Krylov.grade (op A) v`
(`Nat.find` of the monic-annihilator predicate is `sInf {m | A^m v ∈ 𝒦_m}` by
`pow_apply_mem_subspace_iff_exists_monic`, `grade_eq_sInf` and `grade_le_iff`, after moving
`toEuclideanLin (aeval A p)` to `aeval (op A) p` with `toEuclideanLin_pow`);
`grade_le : grade A v ≤ n` (`grade_le_finrank`, `finrank_euclideanSpace`).

### D2. Algorithm 6.1 (Arnoldi, classical Gram–Schmidt) and `V_m, H_m, H̄_m, w_m`

Book: `v_1` unit; for `j = 1..m`: `h_ij = (A v_j, v_i)` (`i ≤ j`), `w_j = A v_j − ∑_{i≤j} h_ij v_i`,
`h_{j+1,j} = ‖w_j‖₂`, stop if `0`, `v_{j+1} = w_j/h_{j+1,j}`.

```lean
/-- Alg 6.1, 0-based; `0` after the process has stopped. -/
noncomputable def arnoldiCGS (A) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => v₁
  | j + 1 =>
    let v : Fin (j + 1) → 𝔼 := fun i => arnoldiCGS A v₁ i
    let Av := op A (v (Fin.last j))
    let w := Av - ∑ i : Fin (j + 1), inner 𝕜 (v i) Av • v i
    ((‖w‖ : 𝕜)⁻¹) • w
termination_by j => j
decreasing_by exact i.isLt
noncomputable def arnoldiCoeff (A) (v₁) (i j : ℕ) : 𝕜 :=
  inner 𝕜 (arnoldiCGS A v₁ i) (op A (arnoldiCGS A v₁ j))
noncomputable def arnoldiW (A) (v₁) (j : ℕ) : 𝔼 :=
  op A (v j) - ∑ i ∈ Finset.range (j + 1), arnoldiCoeff A v₁ i j • v i
noncomputable def V (A) (v₁) (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 := Matrix.of fun i j => arnoldiCGS A v₁ j i
noncomputable def Hbar (A) (v₁) (m) : Matrix (Fin (m + 1)) (Fin m) 𝕜 := Matrix.of fun i j => arnoldiCoeff A v₁ i j
noncomputable def H (A) (v₁) (m) : Matrix (Fin m) (Fin m) 𝕜 := Matrix.of fun i j => arnoldiCoeff A v₁ i j
/-- "Algorithm 6.1 does not stop before the `m`-th step": `h_{j+1,j} ≠ 0` for `j < m`. -/
def NoBreakdownBefore (A) (v₁) (m : ℕ) : Prop := ∀ j, j + 1 < m → arnoldiCoeff A v₁ (j + 1) j ≠ 0
```

Backbone (§3.2, `Numlib/Krylov/Arnoldi.lean`): `Arnoldi.vec` (`gramSchmidtNormed` of `A^i b`),
`Arnoldi.coeff`, `Arnoldi.w`, `Arnoldi.vec_succ_eq` (`v_{j+1} = ‖w_j‖⁻¹ • w_j`),
`Arnoldi.coeff_succ_self`, `Arnoldi.hessenberg`, `Arnoldi.hessenbergSq`, `Arnoldi.vec_zero`,
`Arnoldi.coeff_succ_self_eq_zero_iff`, `Arnoldi.hessenberg_isUpperHessenbergRect`.
Equivalence: `arnoldiCGS_eq (hv : ‖v₁‖ = 1) : arnoldiCGS A v₁ j = Arnoldi.vec (op A) v₁ j` (induction
on `j` using `vec_zero`, `vec_succ_eq`, `coeff_succ_self`: the surface definition is literally the
backbone's recurrence), hence `arnoldiCoeff = Arnoldi.coeff`, `Hbar = Arnoldi.hessenberg`,
`H = Arnoldi.hessenbergSq`, `NoBreakdownBefore A v₁ m ↔ m ≤ Krylov.grade (op A) v₁`.

### D3. Algorithm 6.2 (Arnoldi, modified Gram–Schmidt)

Book: `w := A v_j`; for `i = 1..j`: `h_ij = (w, v_i)`, `w := w − h_ij v_i`; then as in Alg 6.1.

```lean
/-- inner loop of Alg 6.2: fold over `i = 0..j`, returning `(w, h_{·j})`. -/
noncomputable def mgsLoop (v : Fin (j+1) → 𝔼) (w₀ : 𝔼) : 𝔼 × (Fin (j+1) → 𝕜) :=
  (List.finRange (j+1)).foldl
    (fun (w, h) i => (w - inner 𝕜 (v i) w • v i, Function.update h i (inner 𝕜 (v i) w))) (w₀, 0)
noncomputable def arnoldiMGS (A) (v₁ : 𝔼) : ℕ → 𝔼      -- same recursion shape as `arnoldiCGS`, with `mgsLoop`
noncomputable def arnoldiMGSCoeff (A) (v₁) (i j : ℕ) : 𝕜   -- the `h_ij` produced by the loop
```

Backbone: none (§1.2: MGS is surface material); the flag-uniqueness lemmas
`InnerProductSpace.exists_norm_eq_one_smul_gramSchmidtNormed` (an orthonormal family spanning the
same flag agrees with `gramSchmidtNormed` up to a unimodular factor) and
`InnerProductSpace.eq_gramSchmidtNormed_of_re_inner_pos (hu : Orthonormal 𝕜 u) (hspan) (j)
(hpos : 0 < inner 𝕜 (u j) (f j)) : u j = gramSchmidtNormed 𝕜 f j`
(`Numlib/Analysis/InnerProductSpace/GramSchmidt.lean`) are the general tool. The normalization
`hpos` is positivity *in `𝕜`* (`open scoped ComplexOrder`: the inner product is a positive real);
over `ℂ` a unimodular `ε` with `0 < re ε` need not be `1`, so a real-part-only hypothesis does not
pin the vector down. Over `ℝ` the two readings coincide.
Equivalence: `arnoldiMGS_eq_arnoldiCGS (hv : ‖v₁‖ = 1) : arnoldiMGS A v₁ = arnoldiCGS A v₁` and
`arnoldiMGSCoeff = arnoldiCoeff` ("in exact arithmetic … mathematically equivalent"): induction,
using orthonormality of `v_0..v_j` (`Arnoldi.orthonormal` via D2) to show that the partial
subtractions do not change `inner (v i) w`. Alternatively: the MGS vectors are orthonormal, span the
Krylov flag and satisfy `0 < inner 𝕜 (v j) ((op A ^ j) v₁)` in `𝕜` (not just in real part), so
`eq_gramSchmidtNormed_of_re_inner_pos` identifies them with `Arnoldi.vec` (which is
`gramSchmidtNormed` of the Krylov sequence).

### D4. Algorithm 6.3 (Householder Arnoldi), (6.10)–(6.13)

Book: `z_1 = v`; for `j = 1..m+1`: Householder unit vector `w_j` with `(w_j)_i = 0` (`i < j`) and
`(P_j z_j)_i = 0` (`i > j`), `P_j = I − 2 w_j w_jᵀ` (Ch. 1 (1.23)–(1.26): `w = z'/‖z'‖`, `z'_i = 0`
for `i < j`, `z'_j = β + (z_j)_j`, `z'_i = (z_j)_i` for `i > j`, `β = sign((z_j)_j)(∑_{i≥j}(z_j)_i²)^{1/2}`);
`h_{j−1} = P_j z_j`; `v_j = P_1 ⋯ P_j e_j`; if `j ≤ m`, `z_{j+1} = P_j ⋯ P_1 A v_j`. `Q_j = P_j ⋯ P_1` (6.10).

```lean
/-- Householder vector of Saad (1.24)–(1.26) at position `k` (real convention; `0` if `z` already
has the required zeros). -/
noncomputable def householderVec (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) : EuclideanSpace ℝ (Fin n)
/-- `P = I − 2 w wᵀ` (`= reflection (ℝ ∙ w)ᗮ` for unit `w`; `1` for `w = 0`). -/
noncomputable def householder (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)
noncomputable def householderArnoldi (A : Matrix (Fin n) (Fin n) ℝ) (v : 𝔼) (m : ℕ) (hm : m + 1 ≤ n) :
    (Fin (m + 1) → 𝔼) × (Fin (m + 2) → 𝔼) × (Fin (m + 1) → 𝔼)   -- `(v_j)_{j ≤ m+1}`, `(h_{j−1})_{j ≤ m+1}`, `(w_j)_{j ≤ m+1}`
noncomputable def Qhh (…) (j : ℕ) : 𝔼 →ₗ[ℝ] 𝔼            -- (6.10) `P_j ⋯ P_1`
noncomputable def HbarHH (…) : Matrix (Fin (m + 1)) (Fin m) ℝ   -- first `m+1` rows of `[h_1, …, h_m]`
```

Backbone: none (§3.2: Householder Arnoldi is surface); Mathlib `reflection`;
`InnerProductSpace.exists_norm_eq_one_smul_gramSchmidtNormed` for the sign statement.
Equivalence (§6.3.2 last paragraph, P-6.1(f)):
`∃ ε : ℕ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∀ j ≤ m, vHH j = ε j • arnoldiCGS A (‖v‖⁻¹ • v) j` and
`HbarHH = diagonal ε * Hbar * diagonal ε`. Proof: (6.12) is a QR factorization of
`[v, A v_1, …, A v_m]` with `Q_mᵀ` orthogonal and `[h_0, …, h_m]` upper triangular, hence
`span{v_1..v_j} = 𝒦_j` and orthonormality; the flag lemma applied to `f i = (op A)^i v` (whose
Gram–Schmidt is `Arnoldi.vec`) gives the `±`. Surface-heavy.

### D5. FOM (6.16)–(6.17), Algorithm 6.4, Algorithm 6.5 (FOM(m))

Book: `r_0 = b − A x_0`, `β = ‖r_0‖₂`, `v_1 = r_0/β`, Arnoldi (MGS) `m` steps (if `h_{j+1,j} = 0` set
`m := j`), `y_m = H_m^{-1}(β e_1)`, `x_m = x_0 + V_m y_m`. FOM(m): repeat with `x_0 := x_m`.

```lean
noncomputable def r₀ (A) (b x₀ : 𝔼) : 𝔼 := b - op A x₀
noncomputable def β (A) (b x₀) : ℝ := ‖r₀ A b x₀‖
noncomputable def v₁ (A) (b x₀) : 𝔼 := ((β A b x₀ : 𝕜)⁻¹) • r₀ A b x₀
noncomputable def e₁ (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then 1 else 0
/-- effective dimension after the "set m := j" rule -/
noncomputable def mEff (A) (b x₀) (m : ℕ) : ℕ := min m (grade A (v₁ A b x₀))
/-- (6.16)–(6.17) with exactly `m` Arnoldi steps (`Matrix.inv` is `0` when `H_m` is singular). -/
noncomputable def fomFixed (A) (b x₀) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (V A (v₁ A b x₀) m)
    (WithLp.toLp 2 ((H A (v₁ A b x₀) m)⁻¹.mulVec ((β A b x₀ : 𝕜) • e₁ m)))
/-- Alg 6.4. -/
noncomputable def fom (A) (b x₀) (m : ℕ) : 𝔼 := fomFixed A b x₀ (mEff A b x₀ m)
/-- FOM is "defined" at step `m` iff `H_m` is nonsingular. -/
def FOMDefined (A) (b x₀) (m : ℕ) : Prop := IsUnit (H A (v₁ A b x₀) m)
/-- Alg 6.5: one restart cycle and the restarted sequence. -/
noncomputable def fomCycle (A) (b) (m : ℕ) (x₀ : 𝔼) : 𝔼 := fom A b x₀ m
noncomputable def fomRestarted (A) (b) (m : ℕ) (x₀ : 𝔼) (k : ℕ) : 𝔼 := (fomCycle A b m)^[k] x₀
```

Backbone (§3.4–3.5): `Krylov.IsGalerkinIterate` (`Numlib/Krylov/Iterate.lean`); in coordinates
(`Numlib/Krylov/Hessenberg.lean`, for `m ≤ grade`): `Krylov.isGalerkinIterate_iff_mulVec_eq`
(`x₀ + ∑ y_j v_j` is the Galerkin iterate iff `H_m y = β e₁`),
`Krylov.isGalerkinIterate_iff_exists_mulVec_eq`, `Krylov.existsUnique_isGalerkinIterate_iff_isUnit`
(a unique Galerkin iterate exists iff `IsUnit H_m`); §2.4.1 `isPetrovGalerkin_iff_mulVec`
(Saad (5.7)), `existsUnique_isGalerkin_of_isCoercive`. The backbone writes the book's `β e₁` as
`Krylov.firstVec β m` and `V_m y` as `∑ y_j • v_j` (`Matrix.toEuclideanLin_apply_eq_sum`).
Equivalence: `fom_isGalerkinIterate (h : FOMDefined A b x₀ m) (hm : m ≤ grade) :
Krylov.IsGalerkinIterate (op A) b x₀ m (fom A b x₀ m)` (`H_m (H_m⁻¹ (β e₁)) = β e₁` for a unit
`H_m`, then `isGalerkinIterate_iff_mulVec_eq`); `existsUnique_isGalerkinIterate_iff (hm : m ≤ grade) :
(∃! x, IsGalerkinIterate … m x) ↔ FOMDefined …` (`existsUnique_isGalerkinIterate_iff_isUnit` through
`H = Arnoldi.hessenbergSq`, D2); `IsGalerkinIterate … x → FOMDefined → x = fom …`. What the book
proves about FOM(m): nothing (Example 6.1 is numerical); only the definition is formalized.

### D6. Algorithms 6.6 (IOP), 6.7 (IOM), 6.8 (DIOM); (6.19)–(6.21)

Book: IOP = Alg 6.2 with the inner loop restricted to `i = max{1, j−k+1}, …, j`. IOM = Alg 6.4 with
IOP. DIOM: `H_m = L_m U_m` (no pivoting; `L_m` unit lower bidiagonal, `U_m` banded upper triangular
with `k` diagonals), `P_m = V_m U_m^{-1}`, `z_m = L_m^{-1}(β e_1)`, `ζ_1 = β`, `ζ_m = −l_{m,m−1} ζ_{m−1}`,
`p_m = u_mm^{-1}(v_m − ∑_{i=m−k+1}^{m−1} u_im p_i)`, `x_m = x_{m−1} + ζ_m p_m` (6.21); stop if `u_mm = 0`.

```lean
noncomputable def iop (A) (v₁ : 𝔼) (k : ℕ) : ℕ → 𝔼          -- Alg 6.6 (MGS loop over book `i ∈ [j−k+1, j]`)
noncomputable def iopCoeff (A) (v₁) (k) (i j : ℕ) : 𝕜        -- `h_ij` from the loop; `0` outside the band; `h_{j+1,j} = ‖w_j‖`
noncomputable def VI (A) (v₁) (k) (m) : Matrix (Fin n) (Fin m) 𝕜 ; HI ; HbarI     -- as in D2
noncomputable def iom (A) (b x₀) (k m : ℕ) : 𝔼                -- Alg 6.7: `x₀ + VI (HI⁻¹ (β e₁))` with `mEff`
/-- Doolittle LU of a Hessenberg matrix without pivoting: `l_{j+1,j} = h_{j+1,j}/u_jj`,
`u_ij = h_ij − l_{i,i−1} u_{i−1,j}` (`1 < i ≤ j`), `u_{1j} = h_{1j}`. -/
noncomputable def hessLU (Hm : Matrix (Fin m) (Fin m) 𝕜) : Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin m) 𝕜
structure DIOMState where (x : 𝔼) (ζ : 𝕜) (p : ℕ → 𝔼) (u : ℕ → ℕ → 𝕜) (l : ℕ → 𝕜)
noncomputable def diom (A) (b x₀) (k : ℕ) : ℕ → DIOMState     -- Alg 6.8, one step per `m`
```

Backbone: none for the IOP/IOM/DIOM recurrences (§1.2: surface until a second book needs them).
The identities the book reuses for them "because orthogonality was not used" are stated in the
backbone for any sequence satisfying `Krylov.HessenbergRelation A v h : Prop`
(`Numlib/Krylov/Hessenberg.lean`; fields `apply_eq : ∀ j, A (v j) = ∑ i ∈ range (j + 2), h i j • v i`
and `eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0`), with `HessenbergRelation.apply_sum` ((6.7) in
coordinates), `HessenbergRelation.residual_eq` ((6.27), for `b − A x₀ = β • v 0`) and
`HessenbergRelation.residual_eq_of_mulVec_eq` (Prop 6.7 / (6.18)); `Arnoldi.hessenbergRelation` is
the Arnoldi instance. What the book proves about IOP/IOM/DIOM: (i) (6.6)/(6.7) still hold for IOP
vectors (by construction); (ii) Prop 6.7 and (6.18) for IOM/DIOM; (iii)
`‖b − A x_m‖ = h_{m+1,m} |ζ_m/u_mm|` for DIOM; (iv) DIOM ≡ IOM when all `u_jj ≠ 0`; (v) Prop 6.8;
(vi) (6.22)–(6.24) (P-6.22); (vii) IOP with `k ≥ m` is Alg 6.2. These are in §3 as
`needs-equivalence` ((i)–(iii), through `iop_hessenbergRelation`) or `surface-only`.
Equivalence lemmas: `iop_hessenbergRelation : Krylov.HessenbergRelation (op A) (iop A v₁ k) (iopCoeff A v₁ k)`
(the loop computes `A v_j = ∑_{i ∈ band} h_ij v_i + w_j` with `v_{j+1} = w_j/‖w_j‖`, and `iopCoeff`
is `0` outside the band); `iop_eq_arnoldiMGS_of_le (hk : m ≤ k) (j < m) : iop A v₁ k j = arnoldiMGS A v₁ j`
(vii); `diom_x_eq_iom (hu : ∀ j ≤ m, u_jj ≠ 0) : (diom A b x₀ k m).x = iom A b x₀ k m` (iv).

### D7. GMRES (6.25)–(6.30), Algorithm 6.9, Algorithm 6.10 (Householder GMRES), Algorithm 6.11 (GMRES(m))

Book: `x = x_0 + V_m y`, `J(y) = ‖b − A x‖₂ = ‖β e_1 − H̄_m y‖₂` (6.28), `x_m = x_0 + V_m y_m`,
`y_m = argmin_y ‖β e_1 − H̄_m y‖₂` (6.29)–(6.30). Householder GMRES: Alg 6.3 basis, `β := e_1ᵀ h_0`
(`= ±‖r_0‖`), `y_m = argmin`, then `z := 0; z := P_j(η_j e_j + z), j = m..1; x_m = x_0 + z` (6.31)–(6.33).
GMRES(m): repeat with `x_0 := x_m`.

```lean
/-- `J(y)` of (6.26)/(6.28) in Hessenberg coordinates. -/
noncomputable def J (A) (b x₀) (m) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 ((β A b x₀ : 𝕜) • e₁ (m+1) - (Hbar A (v₁ A b x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖
/-- Alg 6.9 as a relation (line 12: "compute `y_m` the minimizer"). -/
def IsGMRESIterate (A) (b x₀ : 𝔼) (m : ℕ) (x : 𝔼) : Prop :=
  ∃ y : Fin m → 𝕜, IsMinOn (J A b x₀ m) Set.univ y ∧ x = x₀ + Matrix.toEuclideanLin (V A (v₁ A b x₀) m) (WithLp.toLp 2 y)
/-- the minimizer as computed in §6.5.3 (Prop 6.9(2)): `y_m = R_m⁻¹ g_m` (`R, g` from D8). -/
noncomputable def gmresY (A) (b x₀) (m) : Fin m → 𝕜 := (R (arnoldiCoeff A (v₁ A b x₀)) m)⁻¹.mulVec (g … m)
noncomputable def gmresFixed (A) (b x₀) (m) : 𝔼 := x₀ + Matrix.toEuclideanLin (V …) (WithLp.toLp 2 (gmresY A b x₀ m))
noncomputable def gmres (A) (b x₀) (m : ℕ) : 𝔼 := gmresFixed A b x₀ (mEff A b x₀ m)   -- Alg 6.9 with "set m := j"
/-- Alg 6.10: Householder basis, `βHH := (h_0)_1`, Horner accumulation (6.31)–(6.33). -/
noncomputable def hornerAccumulate (P : Fin m → (𝔼 →ₗ[ℝ] 𝔼)) (η : Fin m → ℝ) : 𝔼 :=
  (List.finRange m).reverse.foldl (fun z j => P j (η j • EuclideanSpace.single (Fin.castLE _ j) 1 + z)) 0
noncomputable def gmresHH (A : Matrix (Fin n) (Fin n) ℝ) (b x₀) (m) (hm : m + 1 ≤ n) : 𝔼
/-- Alg 6.11. -/
noncomputable def gmresCycle (A) (b) (m : ℕ) (x₀ : 𝔼) : 𝔼 := gmres A b x₀ m
noncomputable def gmresRestarted (A) (b) (m) (x₀) (k : ℕ) : 𝔼 := (gmresCycle A b m)^[k] x₀
```

Backbone (§3.4–3.5): `Krylov.IsMinResIterate`, `Krylov.exists_isMinResIterate`,
`Krylov.existsUnique_isMinResIterate_of_injective` (`Numlib/Krylov/Iterate.lean`); in coordinates
(`Numlib/Krylov/Hessenberg.lean`, `m ≤ grade`): `Krylov.norm_residual_eq_norm_firstVec_sub_mulVec`
(6.28), `Krylov.isMinResIterate_iff_isMinOn` ((6.29)–(6.30): `x₀ + ∑ y_j v_j` is the
minimal-residual iterate iff `y` minimizes `‖β e₁ − H̄_m z‖₂` over `z`),
`Krylov.IsMinResIterate.exists_mulVec_rotated_eq` (the minimizer solves `R_m y = g_m`, D8);
§2.4.1 `IsMinRes.residual_unique`, `existsUnique_isMinRes_of_injOn`.
Equivalence: `isGMRESIterate_iff (hm : m ≤ grade) : IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResIterate (op A) b x₀ m x`
(`J` is the backbone's function once `Hbar = Arnoldi.hessenberg`, `β • e₁ = firstVec β` and
`V_m y = ∑ y_j • v_j` are rewritten; `⇒` is `isMinResIterate_iff_isMinOn`, `⇐` adds "every element
of `x₀ + 𝒦_m` is `x₀ + V_m y`" from `Arnoldi.span_vec`);
`gmresFixed_isGMRESIterate (hm : m ≤ grade) (hR : IsUnit (R …))` (Prop 6.9(2));
`gmresHH_eq (hm) : gmresHH A b x₀ m = gmres A b x₀ m` (Householder basis is `V_m D_m`,
`H̄^{HH} = D_{m+1} H̄ D_m`, `βHH = ε_1 β`, so `J^{HH}(y) = J(D_m y)`, and the two minimizers give the
same `x`; (6.31)–(6.33) is Horner's scheme for `x₀ + ∑ η_j v_j`). What the book proves about
GMRES(m): Thm 6.30 (convergence for positive definite `A`) and the remark "full GMRES converges in
at most `n` steps"; nothing else.

### D8. Givens rotations and `Q_m, R̄_m, ḡ_m` (§6.5.3, §6.5.9)

Book: `Ω_i` (6.34) (real) / (6.80) (complex: row `i` = `(c̄_i, s̄_i)`, row `i+1` = `(−s_i, c_i)`,
`|c_i|² + |s_i|² = 1`), `s_i = h_{i+1,i}/√(|h_ii^{(i−1)}|² + h_{i+1,i}²)`, `c_i = h_ii^{(i−1)}/√(…)`
(6.37)/(6.81), `Q_m = Ω_m ⋯ Ω_1` (6.38), `R̄_m = Q_m H̄_m` (6.39), `ḡ_m = Q_m(β e_1) = (γ_1, …, γ_{m+1})ᵀ`
(6.40); `R_m, g_m` drop the last row/component; `H̄_m^{(k)}, ḡ_m^{(k)}` after the first `k` rotations.

```lean
/-- (6.37)/(6.81): the book's `c_i, s_i` (0-based), computed from the coefficients after the first
`i` rotations; functions of the `ℕ`-indexed coefficient function `h`, not of `m`. -/
abbrev c (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := Krylov.givensC h i
abbrev s (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := Krylov.givensS h i
/-- (6.34)/(6.80) in the `(i, i+1)` plane, as an `(m+1) × (m+1)` matrix. -/
abbrev Ω (h) (i m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := Krylov.givensMatrix h i m
/-- (6.38) `Q_m = Ω_m ⋯ Ω_1`. -/
abbrev Qrot (h) (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := Krylov.givensQ h m
/-- (6.39) `R̄_m = Q_m H̄_m`; (6.40) `ḡ_m = Q_m (β e₁) = (γ_1, …, γ_{m+1})ᵀ`. -/
noncomputable def Rbar (h) (m) : Matrix (Fin (m + 1)) (Fin m) 𝕜 := Qrot h m * Krylov.hessenbergOf h m
noncomputable def gbar (h) (β : 𝕜) (m) : Fin (m + 1) → 𝕜 := (Qrot h m).mulVec (Krylov.firstVec β (m + 1))
/-- the book's `γ_{i+1}` as it enters rotation `i+1` (so `γ 0 = β`, `γ_{m+1}` of `ḡ_m` is `γ h β m`). -/
abbrev γ (h) (β : 𝕜) (i : ℕ) : 𝕜 := Krylov.gamma h β i
noncomputable def R (h) (m) : Matrix (Fin m) (Fin m) 𝕜 := (Rbar h m).submatrix Fin.castSucc id
noncomputable def g (h) (β) (m) : Fin m → 𝕜 := fun i => gbar h β m i.castSucc
-- GMRES instances: `h := arnoldiCoeff A v₁` (`= Arnoldi.coeff (op A) v₁` by D2), `β := β A b x₀`;
-- `H̄_m^{(k)}` is `Krylov.hessenbergOf (Krylov.rotated h k) m`.
```

Backbone (`Numlib/Krylov/Hessenberg.lean`, section Givens; everything is indexed by `ℕ` and computed
from the infinite coefficient function, so the book's "progressive" facts (6.44)–(6.46) hold by
definition): `Krylov.rotated h k` (coefficients after `k` rotations), `Krylov.givensRho`, `givensC`,
`givensS`, `gamma` (`γ_0 = β`, `γ_{k+1} = −s_k γ_k`), `gvec` (`g_k = c̄_k γ_k`), `givensMatrix`,
`givensQ`; lemmas `givensQ_mul_hessenbergOf` (`Q_m H̄_m = H̄_m^{(m)}`), `givensQ_mulVec_firstVec`
(`Q_m (β e₁) = (g_0, …, g_{m−1}, γ_m)`), `givensMatrix_mem_unitaryGroup`, `givensQ_mem_unitaryGroup`,
`norm_givensC_sq_add_norm_givensS_sq`, `rotated_eq_zero_of_lt` and `rotated_last_row` (triangular
with zero last row), `rotated_succ_self` (`r_kk = ρ_k ≥ 0`), `rotated_succ_eq_of_lt` (rotation `k`
leaves columns `j < k` unchanged), `rotated_eq_of_le` (rows below `k` untouched), `gamma_succ`,
`norm_gamma_eq_prod`, `givensS_arnoldi_eq` (`s_k` real nonnegative for Arnoldi coefficients). The
degenerate case `ρ_k = 0` (only possible when `A` is singular) gives `c_k = s_k = 0` by Lean's
`x / 0 = 0`; the unitarity lemmas carry the hypothesis `givensRho h k ≠ 0`, and
`givensMatrix_mem_unitaryGroup` also needs `k < m`, since at `k = m` the rotated row and column
`k + 1` fall outside `Fin (m + 1)` and the matrix is not unitary.
Equivalence: `Rbar_eq : Rbar h m = Krylov.hessenbergOf (Krylov.rotated h m) m` (`givensQ_mul_hessenbergOf`)
and `gbar_eq : gbar h β m = fun i => if (i : ℕ) < m then Krylov.gvec h β i else Krylov.gamma h β m`
(`givensQ_mulVec_firstVec`), so the book's `R_m`, `g_m`, `γ_{m+1}` are definitionally the backbone's
`Krylov.hessenbergSqOf (Krylov.rotated h m) m`, `Krylov.gvec h β`, `Krylov.gamma h β m`.

### D9. Algorithms 6.12 (QGMRES), 6.13 (DQGMRES); `Z_{m+1}, z_{m+1}, ζ_m` (§6.5.6)

Book: QGMRES = Alg 6.9 with IOP; DQGMRES: `γ_1 = ‖r_0‖`, per step `m`: IOP column, apply
`Ω_{m−k..m−1}` to it, `c_m, s_m` by (6.37), `γ_{m+1} := −s_m γ_m`, `γ_m := c_m γ_m`,
`h_mm := c_m h_mm + s_m h_{m+1,m}`, `p_m = (v_m − ∑_{i=m−k}^{m−1} h_im p_i)/h_mm`, `x_m = x_{m−1} + γ_m p_m`.
`Z_{m+1} = V_{m+1} Q_mᵀ` (6.52), `z_{m+1}` its last column, `ζ_m = ‖z_m‖₂`; quasi-residual norm `|γ_{m+1}|`.

```lean
noncomputable def qgmres (A) (b x₀) (k m : ℕ) : 𝔼    -- `x₀ + VI_m R_m⁻¹ g_m`, `R, g` of D8 at `h := iopCoeff A v₁ k`
structure DQGMRESState where (x : 𝔼) (γ : 𝕜) (p : ℕ → 𝔼) …
noncomputable def dqgmres (A) (b x₀) (k : ℕ) : ℕ → DQGMRESState   -- Alg 6.13 verbatim
noncomputable def Z (A) (b x₀) (k m) : Matrix (Fin n) (Fin (m + 1)) 𝕜 := VI … (m+1) * (Qrot (iopCoeff …) m)ᴴ   -- (6.52)
noncomputable def z (…) (m) : 𝔼 := WithLp.toLp 2 fun i => Z … i (Fin.last m) ;  noncomputable def ζ (…) (m) : ℝ := ‖z … m‖
noncomputable def quasiResidualNorm (…) (m) : ℝ := ‖γ (iopCoeff …) (β …) m‖
```

Backbone: none for the recurrence (§1.2: DQGMRES is surface); the residual identities come from
`Krylov.HessenbergRelation` (D6) and the Givens data of D8 applied to `iopCoeff A v₁ k`. What the
book proves: (6.50), (6.51), (6.53)–(6.58), Thm 6.11, and "QGMRES/DQGMRES = GMRES when `k ≥ m`".
Equivalence: `dqgmres_x_eq_qgmres (h : ∀ j ≤ m, h_jj ≠ 0) : (dqgmres A b x₀ k m).x = qgmres A b x₀ k m`
(same argument as DIOM ≡ IOM with the QR in place of the LU) and
`qgmres_eq_gmres (hk : m ≤ k) : qgmres A b x₀ k m = gmres A b x₀ m`.

### D10. FOM/GMRES residual norms `ρ_m^F, ρ_m^G`, `ξ, h`, `R̃_m, g̃_m, ỹ_m` (§6.5.7)

```lean
noncomputable def ρG (A) (b x₀) (m) : ℝ := ‖b - op A (gmresFixed A b x₀ m)‖
noncomputable def ρF (A) (b x₀) (m) : ℝ := ‖b - op A (fomFixed A b x₀ m)‖   -- meaningful when `FOMDefined`
/-- `ξ_m = (Q_{m−1} H̄_m)_{mm}` (Prop 6.12), 0-based: the diagonal entry after `m − 1` rotations. -/
noncomputable def ξ (h : ℕ → ℕ → 𝕜) (m : ℕ) : 𝕜 := Krylov.rotated h (m - 1) (m - 1) (m - 1)
/-- Lemma 6.16: `R̃_m`, `g̃_m` are the top `m × m` block / first `m` entries after `m − 1` rotations. -/
noncomputable def Rtilde (h) (m) : Matrix (Fin m) (Fin m) 𝕜 := Krylov.hessenbergSqOf (Krylov.rotated h (m - 1)) m
noncomputable def gtilde (h) (β) (m) : Fin m → 𝕜 :=
  fun i => if (i : ℕ) < m - 1 then Krylov.gvec h β i else Krylov.gamma h β (m - 1)
noncomputable def ytilde (h) (β) (m) : Fin m → 𝕜 := (Rtilde h m)⁻¹.mulVec (gtilde h β m)
/-- "the smallest residual norm achieved by FOM in the first `m` steps (singular `H_i` skipped)". -/
noncomputable def ρFmin (A) (b x₀) (m) : ℝ :=
  ((Finset.range (m+1)).filter (FOMDefined A b x₀)).inf' ⟨0, by simp [FOMDefined]⟩ (ρF A b x₀)
```

Backbone (§3.6, `Numlib/Krylov/Relations.lean`, at the specification level):
`Krylov.inv_sq_norm_residual_minRes` (Prop 6.13), `Krylov.inv_sq_norm_residual_minRes_eq_sum`
(Cor 6.14), `Krylov.norm_residual_minRes_le_galerkin`, `Krylov.exists_norm_residual_galerkin_le`
(Prop 6.15), `Krylov.minRes_eq_combination` (6.74), `Krylov.norm_residual_minRes_eq_iff_not_exists_galerkin`
(Prop 6.17); identifications with the Givens data (§3.5, `Numlib/Krylov/Hessenberg.lean`):
`Krylov.IsMinResIterate.norm_residual_eq_norm_gamma` (6.42, hypothesis `m < grade`, strict: at
`m = grade` the padded recurrence degenerates — `A = 0`, `b = 1`, `x₀ = 0` in `ℝ` has `γ_1 = 0` while
every residual is `1`), `Krylov.IsMinResIterate.norm_residual_succ_eq`
(`‖r^G_{m+1}‖ = |s_m| ‖r^G_m‖`, hypothesis `m + 1 < grade`, strict for the same reason),
`Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero` (`m + 1 ≤ grade`; `H_{m+1}` is a
unit iff `c_m ≠ 0`), `Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC`
(`m + 1 ≤ grade`; `‖r^F_{m+1}‖ = ‖r^G_{m+1}‖/|c_m|`, Prop 6.12 — the identity carries content only
where `c_m ≠ 0`, since Lean's `x / 0 = 0` makes the right-hand side vanish at a breakdown).
These four, together with `Krylov.IsMinResIterate.exists_mulVec_rotated_eq` (D8), rest on one
ingredient Mathlib does not provide: that a unitary matrix preserves the Euclidean norm,
`‖U.mulVec v‖₂ = ‖v‖₂` for `U ∈ Matrix.unitaryGroup` (the route is `Matrix.toEuclideanCLM` and the
fact that a unitary element of a C⋆-algebra is an isometry — itself an upstreaming candidate for
`Numlib/Analysis/Matrix/`), plus the splitting of `‖Q_m(β e₁) − R̄_m y‖²` into
`‖g_m − R_m y‖² + ‖γ_m‖²` from `rotated_last_row` and the nonsingularity of `R_m`
(`det R_m = ∏_k ρ_k ≠ 0` by upper-triangularity). Every surface item routed through the Givens
identities inherits that dependency.

### D11. Residual smoothing: Algorithm 6.14 (MRS) and QMRS (§6.5.8)

Book: from an original sequence `(x_m^O, r_m^O)`: `x_0^S = x_0^O`;
`η_m = −(r^S_{m−1}, r^O_m − r^S_{m−1})/‖r^O_m − r^S_{m−1}‖²`; `x^S_m = x^S_{m−1} + η_m(x^O_m − x^S_{m−1})`,
`r^S_m = r^S_{m−1} + η_m(r^O_m − r^S_{m−1})`. QMRS: the same with `η_m = τ_{m−1}²/(τ_{m−1}² + ρ_m²)`,
`1/τ_m² = 1/τ_{m−1}² + 1/ρ_m²`, `τ_0 = ρ_0`, `ρ_m = ‖r^O_m‖`.

```lean
noncomputable def mrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼            -- Alg 6.14 (`η` with Lean's `x/0 = 0`)
noncomputable def mrsEta (xO rO) (m : ℕ) : 𝕜
noncomputable def qmrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼 × ℝ         -- `(x^S_m, r^S_m, τ_m)`
```

Backbone (§3.6, `Numlib/Krylov/Relations.lean`): `Krylov.smoothingCoeff s r = ⟪r − s, −s⟫/‖r − s‖²`
(the book's `η_m`: its `(r^S, r^O − r^S)` is `inner (r^O − r^S) r^S`), `Krylov.inv_sq_norm_smoothing`
(Lemma 6.18), `Krylov.mrs A b xO` (Alg 6.14 on the iterates, residuals recomputed as `b − A x`),
`Krylov.IsGalerkinIterate.mrs_isMinResIterate` (MRS of Galerkin iterates = minimal-residual
iterates), `Krylov.residual_mrs_eq` (6.79).
Equivalence: `mrs_eq (hr : ∀ j, rO j = b - op A (xO j)) (m) : (mrs xO rO m).1 = Krylov.mrs (op A) b xO m ∧
(mrs xO rO m).2 = b - op A (Krylov.mrs (op A) b xO m)` (induction on `m`; `mrsEta xO rO m` is
`Krylov.smoothingCoeff (rS (m−1)) (rO m)` definitionally).

### D12. Lanczos: `T_m` (6.84) and Algorithm 6.15 (§6.6)

Book: `α_j = h_jj`, `β_j = h_{j−1,j}`; Alg 6.15: `β_1 = 0, v_0 = 0`; `w_j = A v_j − β_j v_{j−1}`,
`α_j = (w_j, v_j)`, `w_j := w_j − α_j v_j`, `β_{j+1} = ‖w_j‖₂`, stop if `0`, `v_{j+1} = w_j/β_{j+1}`.

```lean
noncomputable def lanczos (A) (v₁ : 𝔼) : ℕ → 𝔼 × ℝ × ℝ   -- `(v_{j+1}, α_{j+1}, β_{j+2})`, 0-based; `v 0 = v₁`, `β 0 = 0`
noncomputable def lanczosV (A) (v₁) (j : ℕ) : 𝔼 ; lanczosAlpha : ℕ → ℝ ; lanczosBeta : ℕ → ℝ
/-- (6.84) `T_m = tridiag(β_i, α_i, β_{i+1})`. -/
noncomputable def T (A) (v₁) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j =>
  if i = j then lanczosAlpha A v₁ i else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
  else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i else 0
noncomputable def Tbar (A) (v₁) (m) : Matrix (Fin (m + 1)) (Fin m) ℝ
```

Backbone (§3.3, `Numlib/Krylov/Lanczos.lean`): `Arnoldi.coeff_eq_zero_of_isSymmetric`,
`Arnoldi.coeff_conj_of_isSymmetric`, `Arnoldi.coeff_diag_re_of_isSymmetric`, `Lanczos.alpha`
(`re ⟪v_j, A v_j⟫`), `Lanczos.beta` (`‖w_j‖`), `Lanczos.coe_alpha`, `Lanczos.coe_beta`,
`Lanczos.apply_vec_zero`, `Lanczos.apply_vec` (three-term recurrence), `Lanczos.w_succ_eq`
(the algorithmic form `w_{j+1} = A v_{j+1} − α_{j+1} v_{j+1} − β_j v_j`), `Lanczos.tridiag`,
`Lanczos.tridiagExt`, `Lanczos.hessenbergSq_eq_map_tridiag`, `Lanczos.hessenberg_eq_map_tridiagExt`,
`Lanczos.beta_eq_zero_iff`.
Equivalence (real symmetric `A`): `lanczosV_eq (hA : A.IsSymm) : lanczosV A v₁ j = arnoldiMGS A v₁ j (= Arnoldi.vec (op A) v₁ j)`,
`lanczosAlpha_eq : lanczosAlpha A v₁ j = Lanczos.alpha (op A) v₁ j`, `lanczosBeta_eq`,
`T_eq : T A v₁ m = Lanczos.tridiag (op A) v₁ m` (`= H A v₁ m`). Proof: induction with Thm 6.19 and
`Lanczos.w_succ_eq` (the MGS loop subtracts only the `i = j−1, j` terms; the other `h_ij` vanish).

### D13. §6.6.2: the inner product (6.85) and the Lanczos polynomials

```lean
/-- `⟨p, q⟩_{v₁} = (p(A) v₁, q(A) v₁)` on `P_{m−1}`. -/
noncomputable def polyInner (A) (v₁ : 𝔼) (p q : 𝕜[X]) : 𝕜 := inner 𝕜 (aeval (op A) q v₁) (aeval (op A) p v₁)
noncomputable def lanczosPoly (A) (v₁) (i : ℕ) : 𝕜[X]   -- the `q_{i−1}` with `v_i = q_{i−1}(A) v₁` (from `Krylov.mem_subspace_iff_exists_aeval`)
```

Backbone: §3.1 `subspace_eq_map_degreeLT`, `linearIndependent_of_le_grade`, `Krylov.polyEval`.
The two claims the book cites without proof ((d), (e) of R46) belong to the deferred items
`Arnoldi.charpoly_compression_isMinOn` (§4.2) and `Krylov/OrthogonalPolynomials.lean` (§3.12), see §4.

### D14. Algorithms 6.16 (Lanczos method), 6.17 (D-Lanczos), 6.18 (CG), 6.19 (three-term CG); (6.86)–(6.98) (§6.7)

Book: (6.86) `x_m = x_0 + V_m y_m`, `y_m = T_m^{-1}(β e_1)`; D-Lanczos: `T_m = L_m U_m` with
`λ_m = β_m/η_{m−1}` (6.88), `η_m = α_m − λ_m β_m` (6.89), `ζ_m = −λ_m ζ_{m−1}` (`ζ_1 = β`),
`p_m = η_m^{-1}(v_m − β_m p_{m−1})`, `x_m = x_{m−1} + ζ_m p_m`; CG (Alg 6.18): `p_0 = r_0`,
`α_j = (r_j,r_j)/(A p_j,p_j)`, `x_{j+1} = x_j + α_j p_j`, `r_{j+1} = r_j − α_j A p_j`,
`β_j = (r_{j+1},r_{j+1})/(r_j,r_j)`, `p_{j+1} = r_{j+1} + β_j p_j`; three-term CG (Alg 6.19):
`x_{−1} = 0`, `ρ_0 = 1`, `γ_j = (r_j,r_j)/(A r_j,r_j)`,
`ρ_j = [1 − (γ_j/γ_{j−1})((r_j,r_j)/(r_{j−1},r_{j−1}))/ρ_{j−1}]^{-1}` (`j > 0`),
`x_{j+1} = ρ_j(x_j + γ_j r_j) + (1−ρ_j) x_{j−1}`, `r_{j+1} = ρ_j(r_j − γ_j A r_j) + (1−ρ_j) r_{j−1}`.

```lean
noncomputable def lanczosMethod (A : Matrix (Fin n) (Fin n) ℝ) (b x₀) (m) : 𝔼 :=      -- Alg 6.16 (with `mEff`)
  x₀ + Matrix.toEuclideanLin (VL …) (WithLp.toLp 2 ((T A (v₁ …) m)⁻¹.mulVec (β • e₁ m)))
structure DLState where (x : 𝔼) (v vPrev : 𝔼) (p : 𝔼) (ζ η β : ℝ)
noncomputable def dLanczos (A) (b x₀) : ℕ → DLState                                     -- Alg 6.17 verbatim
/-- Alg 6.18. -/
noncomputable def cgStep (A) (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  let Ap := op A s.2.2; let α : 𝕜 := inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 Ap; let r' := s.2.1 - α • Ap
  let β : 𝕜 := inner 𝕜 r' r' / inner 𝕜 s.2.1 s.2.1; (s.1 + α • s.2.2, r', r' + β • s.2.2)
noncomputable def cg (A) (b x₀) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 := (cgStep A)^[j] (x₀, r₀ A b x₀, r₀ A b x₀)
noncomputable def cgAlpha (A) (b x₀) (j) : 𝕜 ; cgBeta   -- the scalars of step `j`
noncomputable def cg3 (A) (b x₀) : ℕ → 𝔼 × 𝔼 × 𝔼 × 𝔼 × ℝ × ℝ   -- Alg 6.19: `(x_j, x_{j−1}, r_j, r_{j−1}, ρ_j, γ_j)`
noncomputable def cgGamma ; cgRho                                -- (6.95)–(6.97)
```

Backbone (§3.7, `Numlib/Krylov/CG.lean`): `CG.State`, `CG.alpha`, `CG.step`, `CG.beta`, `CG.init`,
`CG.iterate`, `CG.residual_eq`, `CG.step_x`, `CG.step_r`, `CG.isGalerkinIterate`,
`CG.inner_residual_eq_zero`, `CG.inner_apply_direction_eq_zero`, `CG.inner_residual_direction_eq`
(`⟪r_i, p_j⟫ = ‖r_j‖²` for `i ≤ j`; the right-hand side carries the *later* index — already
`⟪r₀, p₁⟫ = β₀‖r₀‖² = ‖r₁‖²`), `CG.inner_residual_direction_eq_zero` (`⟪r_i, p_j⟫ = 0` for `j < i`),
`CG.span_direction_eq`, `CG.arnoldi_vec_eq`, and the three-term form `CG.gamma`, `CG.rho`
(the book's (6.97) with `ρ_0 = 1`), `CG.iterate_succ_eq_three_term` (6.98),
`CG.residual_succ_eq_three_term` (6.96), valid while `r_j ≠ 0` for `j ≤ m`; §3.5
`Krylov.residual_galerkin_eq` for the Lanczos residual formula (6.87).
Equivalence: `cg_eq_CG (hA : A.IsSymm) : cg A b x₀ j = ((CG.iterate (op A) b x₀ j).x, .r, .p)` (definitional
up to `real_inner_comm` in `α`); `lanczosMethod_eq_fom (hA) : lanczosMethod A b x₀ m = fom A b x₀ m` (D12);
`dLanczos_x_eq (hη : ∀ j ≤ m, η_j ≠ 0) : (dLanczos A b x₀ m).x = lanczosMethod A b x₀ m` (this is DIOM(2)
for symmetric `A`, as the book remarks; reuse D6's LU argument);
`cg_x_eq_dLanczos (hA : A.PosDef) : (cg A b x₀ j).1 = (dLanczos A b x₀ j).x` (both are the unique Galerkin iterate);
`cg3_eq_cg (hA : A.PosDef) (hr : ∀ i ≤ j, r_i ≠ 0) : (cg3 …).x = (cg …).1 ∧ (cg3 …).r = (cg …).2.1`
(induction on `j` with `CG.iterate_succ_eq_three_term` and `CG.residual_succ_eq_three_term`;
`cgGamma = CG.gamma`, `cgRho = CG.rho` after `cg_eq_CG`).

### D15. Algorithm 6.20 (CR), Algorithm 6.21 (GCR), ORTHOMIN(k), ORTHODIR, GCR(m) (§6.8–6.9)

Book: CR: `p_0 = r_0`; `α_j = (r_j, A r_j)/(A p_j, A p_j)`, `x_{j+1} = x_j + α_j p_j`, `r_{j+1} = r_j − α_j A p_j`,
`β_j = (r_{j+1}, A r_{j+1})/(r_j, A r_j)`, `p_{j+1} = r_{j+1} + β_j p_j`, `A p_{j+1} = A r_{j+1} + β_j A p_j`.
GCR: same `α_j`, `x, r` updates, `β_ij = −(A r_{j+1}, A p_i)/(A p_i, A p_i)` for `i = 0..j`,
`p_{j+1} = r_{j+1} + ∑_{i≤j} β_ij p_i`; ORTHOMIN(k): `i = j−k+1..j`; ORTHODIR: `p_{j+1} = A p_j + ∑_{i≤j} β_ij p_i`,
`β_ij = −(A² p_j, A p_i)/(A p_i, A p_i)` (6.107), `x` by (6.105).

```lean
noncomputable def crStep (A) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 ; noncomputable def cr (A) (b x₀) (j : ℕ) : …  -- `(x, r, p, Ap)`, Alg 6.20 verbatim
structure GCRState where (x r : 𝔼) (p Ap : List 𝔼)
noncomputable def gcr (A) (b x₀) : ℕ → GCRState        -- Alg 6.21
noncomputable def orthomin (A) (b x₀) (k : ℕ) : ℕ → GCRState   -- lines 6a/7a
noncomputable def orthodir (A) (b x₀) : ℕ → GCRState   -- (6.107) + (6.105)
noncomputable def gcrRestarted (A) (b) (m) (x₀) (k : ℕ) : 𝔼   -- GCR(m)
```

Backbone (§3.8, `Numlib/Krylov/CR.lean`): `CR.State`, `CR.alpha`, `CR.step`, `CR.init`, `CR.iterate`,
`CR.residual_eq`, `CR.q_eq`, `CR.isMinResIterate` (symmetric coercive `A`),
`CR.isMinResIterate_of_no_breakdown` (symmetric `A` with the no-breakdown hypotheses
`⟪r_j, A r_j⟫ ≠ 0` and `A p_j ≠ 0` for `j < k`: the book's Hermitian generality),
`CR.inner_apply_direction_eq_zero`, `CR.inner_residual_apply_direction_eq_zero`,
`CR.inner_residual_apply_residual_eq_zero` (Fong–Saunders Thm 2.1 invariants),
`Krylov.isMinResIterate_of_orthogonal_directions` (Lemma 6.21, no symmetry assumption).
Equivalence: `cr_eq_CR : cr A b x₀ j = (CR.iterate (op A) b x₀ j).(x, r, p, q)` (definitional; the book's
`(r_j, A r_j)` is `inner (A r_j) r_j`, the backbone's is `inner r (A r)` — equal for Hermitian `A`);
`gcr_x_isMinResIterate (h : ∀ i < m, A p_i ≠ 0) (hm : m ≤ grade)`; `orthomin_eq_gcr (hk : m ≤ k)`;
`orthodir_x_isMinResIterate (h : ∀ i < m, A p_i ≠ 0) (hm)`. What the book proves about ORTHOMIN(k) and
GCR(m): nothing (definitions only); only the definitions and `ORTHOMIN(k) = GCR` for `k ≥ m` are formalized.

### D16. §6.10 objects: `ν(A)`, the class `CG(s)`

```lean
/-- `ν(A)`: least degree of a polynomial `q` with `A^H = q(A)` (junk `0` if none; exists iff `A` normal). -/
noncomputable def ν (A : Matrix (Fin n) (Fin n) ℂ) : ℕ := sInf {d | ∃ q : ℂ[X], q.natDegree = d ∧ aeval A q = Aᴴ}
/-- Faber–Manteuffel's `CG(s)` (Euclidean inner product): for every `v₁`, `(A v_j, v_i) = 0`
whenever `i + s ≤ j ≤ μ(v₁) − 1` (0-based shift below). -/
def IsCGs (A : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) : Prop :=
  ∀ v₁ : EuclideanSpace ℂ (Fin n), ∀ i j : ℕ, i + s ≤ j → j + 1 ≤ grade A v₁ → arnoldiCoeff A v₁ i j = 0
```

Backbone: none (§3.12: Faber–Manteuffel is Saad-surface; Lemma 6.23 and Thm 6.24 depend on the
deferred normal-matrix theory, §4).

### D17. Chebyshev polynomials and the quantities of §6.11

```lean
abbrev C (k : ℕ) : ℝ[X] := Polynomial.Chebyshev.T ℝ k                 -- (6.109)–(6.111)
noncomputable def Ccomplex (k : ℕ) : ℂ[X] := Polynomial.Chebyshev.T ℂ k   -- (6.114)
/-- (6.113). -/
noncomputable def Chat (k : ℕ) (α β γ : ℝ) : ℝ[X] :=
  Polynomial.C (1 / (C k).eval (1 + 2 * (γ - β) / (β - α))) *
    (C k).comp (Polynomial.C (1 - 2 * β / (β - α)) + Polynomial.C (2 / (β - α)) * X)
noncomputable def η (lmin lmax : ℝ) : ℝ := lmin / (lmax - lmin)          -- (6.122)
noncomputable def κ (lmin lmax : ℝ) : ℝ := lmax / lmin
noncomputable def anorm (A) (x : 𝔼) : ℝ := Real.sqrt (RCLike.re (inner 𝕜 (op A x) x))   -- `‖x‖_A`
/-- `ε^{(m)}` of Prop 6.32. -/
noncomputable def epsMin (lam : Fin n → ℂ) (m : ℕ) : ℝ :=
  ⨅ p : {p : ℂ[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ⨆ i, ‖p.1.eval (lam i)‖
noncomputable def ellipse (c d a : ℂ) : Set ℂ                                -- `E(c, d, a)`, deferred (§4)
```

Backbone (§2.1.9, `Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean`): `Polynomial.Chebyshev.eval_T_eq_half_add_pow`,
`half_pow_le_eval_T`, `one_le_eval_T`, `shifted`, `shifted_degree_le`, `shifted_eval_self`,
`one_div_eval_T_le_sSup_abs_eval` (general `γ`), `sSup_abs_eval_shifted`,
`one_div_eval_T_le_sSup_abs_eval_of_eval_zero`, `one_div_eval_T_le_two_mul_pow`; §2.1.5 `energyNorm`
(`Numlib/Analysis/InnerProductSpace/Energy.lean`); §3.9–3.10 (`Numlib/Krylov/Convergence/Polynomial.lean`,
`Numlib/Krylov/Convergence/CG.lean`), whose hypothesis `A.IsSymmetricBoundedBy lmin lmax`
(`Numlib/Analysis/InnerProductSpace/Coercive.lean`) replaces the book's eigenvalue list.
Equivalence: `Chat_eq_shifted : Chat k α β γ = Polynomial.Chebyshev.shifted k α β γ` (the arguments differ by a
sign, `T_k(−x) = (−1)^k T_k(x)` cancels in the quotient); `anorm_eq : anorm A x = energyNorm (op A) x` (rfl);
`one_add_two_mul_η : 1 + 2 * η lmin lmax = (lmax + lmin) / (lmax - lmin)`.

### D18. Block Krylov: Algorithms 6.22–6.24 and the block-FOM/GMRES specifications (§6.12)

```lean
/-- Alg 6.24 (Ruhe): `v_1..v_p` orthonormal; for `j = p, …`: `k = j − p + 1`, `w = A v_k`
MGS-orthogonalized against `v_1..v_j`, `v_{j+1} = w/‖w‖`. -/
noncomputable def ruhe (A) (p : ℕ) (v : Fin p → 𝔼) : ℕ → 𝔼 ; ruheCoeff : ℕ → ℕ → 𝕜
noncomputable def HbarBlock (A) (p) (v) (m) : Matrix (Fin (m + p)) (Fin m) 𝕜      -- (6.130)
/-- Alg 6.22 / 6.23 with the Q-R factorization of `W_j` fixed to Gram–Schmidt of its columns
(`H_{j+1,j}` upper triangular with nonnegative diagonal). -/
noncomputable def blockArnoldi (A) (p) (V₁ : Matrix (Fin n) (Fin p) 𝕜) : ℕ → Matrix (Fin n) (Fin p) 𝕜 × Matrix (Fin p) (Fin p) 𝕜
noncomputable def blockArnoldiMGS …
/-- block-GMRES / block-FOM approximation for the `i`-th right-hand side over `x₀^{(i)} + span{v_1..v_m}`. -/
def IsBlockGMRES (A) (B X₀ : Matrix (Fin n) (Fin p) 𝕜) (m) (i : Fin p) (x : 𝔼) : Prop :=
  IsMinRes (op A) (col B i) (col X₀ i) (Submodule.span 𝕜 (ruhe A p (qrCols (B - A * X₀)) '' Set.Iio m)) x
def IsBlockFOM … := IsGalerkin (op A) … (Submodule.span 𝕜 …) x
```

Backbone: §2.4.1 `IsMinRes`, `IsGalerkin` (`Numlib/LinearSolve/Projection/Basic.lean`; general
subspaces, not the Krylov abbreviations); the block relations belong to the deferred
`Krylov/Block.lean` (§3.12, see §4).

## 3. Results

One block per numbered result and per equation-level fact stated as a result, in book order. In the
Lean sketches `Aop := op A`, `r₀ := r₀ A b x₀`, `v₁ := v₁ A b x₀`, `β := β A b x₀`,
`μ := grade A v₁` (`= Krylov.grade Aop v₁` by D1), `v j := arnoldiCGS A v₁ j`,
`h i j := arnoldiCoeff A v₁ i j`; the Givens quantities `c, s, γ, R, g, ξ` of D8/D10 are taken at
this `h` and at `β` unless another coefficient function is named.
Classification of each item: `direct` = specialization of a backbone (or Mathlib) theorem through
the D-lemmas; `needs-equivalence` = the main work is a surface bridging lemma (one of D2–D18 or a
named one); `surface-only` = proved in the surface (from Mathlib, with backbone lemmas as tools)
because the backbone plan (§1.2) deliberately leaves the object there; `deferred` = needs a backbone
item scheduled for a later phase (listed in §4); `out-of-scope` = not formalized, with the reason.

### R1. §6.2, first property — `𝒦_m` is the set of `p(A) v` with `deg p ≤ m − 1`
- **Book statement.** `𝒦_m(A, v) = {p(A) v : p polynomial, deg p ≤ m − 1}` (real `n × n` `A`,
  `v ∈ ℝⁿ`).
- **Lean surface statement.** `theorem krylov_eq_image_degreeLT : krylov A v m =
  (Polynomial.degreeLT ℝ m).map (Krylov.polyEval Aop v)`; and
  `x ∈ krylov A v m ↔ ∃ p, p.degree < m ∧ x = aeval Aop p v`.
- **Backbone item.** §3.1 `Krylov.subspace_eq_map_degreeLT`, `Krylov.mem_subspace_iff_exists_aeval`
  (`Numlib/Krylov/Subspace.lean`).
- **Proof route.** Rewrite by `krylov_eq` (D1).
- **Classification.** `direct`.

### R2. Proposition 6.1
- **Book statement.** Let `μ` be the grade of `v`. Then `𝒦_μ` is invariant under `A`, and
  `𝒦_m = 𝒦_μ` for all `m ≥ μ`.
- **Lean surface statement.** `theorem proposition_6_1 : (krylov A v (grade A v)) ∈ Module.End.invtSubmodule Aop ∧
  ∀ m, grade A v ≤ m → krylov A v m = krylov A v (grade A v)`.
- **Backbone item.** §3.1 `Krylov.subspace_grade_mem_invtSubmodule`, `Krylov.subspace_eq_of_grade_le`
  (under `[FiniteDimensional 𝕜 (fullSubspace A v)]`, automatic on `𝔼`).
- **Proof route.** `krylov_eq`, `grade_eq` (D1), then the two backbone lemmas.
- **Classification.** `direct`.

### R3. Proposition 6.2, (6.3)–(6.4), and "grade ≤ n"
- **Book statement.** `dim 𝒦_m = m ↔ grade(v) ≥ m` (6.3); hence `dim 𝒦_m = min{m, grade(v)}` (6.4).
  Also (text): the grade of `v` does not exceed `n` (Cayley–Hamilton).
- **Lean surface statement.** `theorem proposition_6_2 : Module.finrank ℝ (krylov A v m) = m ↔ m ≤ grade A v`;
  `theorem equation_6_4 : Module.finrank ℝ (krylov A v m) = min m (grade A v)`;
  `theorem grade_le_card : grade A v ≤ n`.
- **Backbone item.** §3.1 `Krylov.finrank_subspace`, `Krylov.grade_le_finrank`,
  `Krylov.linearIndependent_of_le_grade`.
- **Proof route.** (6.4) is the backbone lemma; (6.3) from (6.4) by `min_eq_left_iff`; `grade ≤ n`
  from `grade_le_finrank` and `finrank_euclideanSpace`.
- **Classification.** `direct`.

### R4. Proposition 6.3 (polynomials of `A` versus the section `A_m`)
- **Book statement.** Let `Q_m` be *any* projector onto `𝒦_m`, `A_m = Q_m A|_{𝒦_m}` the section of
  `A` in `𝒦_m`. Then `q(A) v = q(A_m) v` for `deg q ≤ m − 1`, and `Q_m q(A) v = q(A_m) v` for
  `deg q ≤ m`.
- **Lean surface statement.**
  ```lean
  theorem proposition_6_3 (Q : 𝔼 →ₗ[ℝ] 𝔼) (hQ : IsIdempotentElem Q) (hrange : LinearMap.range Q = krylov A v m)
      (hm : 0 < m) (q : ℝ[X]) :
      (q.degree < m → aeval Aop q v = (aeval (section' A Q hrange) q ⟨v, _⟩ : 𝔼)) ∧
      (q.degree ≤ m → Q (aeval Aop q v) = (aeval (section' A Q hrange) q ⟨v, _⟩ : 𝔼))
  -- `section' A Q hrange : krylov A v m →ₗ[ℝ] krylov A v m :=
  --   compressionBy (Q.codRestrict (krylov A v m) (fun x => hrange ▸ LinearMap.mem_range_self Q x)) Aop`
  ```
- **Backbone item.** §2.1.6 `compressionBy` (compression through an arbitrary projector
  `Q : E →ₗ[𝕜] K` with `∀ x : K, Q x = x`), `compressionBy.aeval_apply_of_forall_pow_mem` (first
  part), `compressionBy.apply_aeval_of_forall_pow_lt_mem` (second part); the orthogonal case is
  `compression` with `compression.aeval_apply_of_forall_pow_mem` and `compression.eq_compressionBy`
  (`Numlib/Analysis/InnerProductSpace/Projection/Compression.lean`).
- **Proof route.** `Q x = x` on `𝒦_m` from `hQ` and `hrange`; the membership hypotheses
  `A^i v ∈ 𝒦_m` for `i ≤ natDegree q < m` (resp. `i < natDegree q ≤ m`) are
  `Krylov.pow_apply_mem_subspace` through `krylov_eq`.
- **Classification.** `direct`.

### R5. Proposition 6.4
- **Book statement.** If Algorithm 6.1 does not stop before the `m`-th step, then `v_1, …, v_m` form
  an orthonormal basis of `𝒦_m = span{v_1, A v_1, …, A^{m−1} v_1}`.
- **Lean surface statement.** `theorem proposition_6_4 (hv : ‖v₁‖ = 1) (h : NoBreakdownBefore A v₁ m) :
  Orthonormal ℝ (fun i : Fin m => v i) ∧ Submodule.span ℝ (Set.range fun i : Fin m => v i) = krylov A v₁ m`
  (equivalently an `OrthonormalBasis (Fin m) ℝ (krylov A v₁ m)`).
- **Backbone item.** §3.2 `Arnoldi.orthonormal` (indexed by `Fin (grade)`), `Arnoldi.span_vec`,
  `Arnoldi.orthonormalBasis`.
- **Proof route.** `arnoldiCGS_eq` (D2) and `NoBreakdownBefore ↔ m ≤ grade`, then restrict
  `Arnoldi.orthonormal` to `Fin m`.
- **Classification.** `direct`.

### R6. Proposition 6.5, (6.6)–(6.9)
- **Book statement.** With `V_m = [v_1 … v_m]`, `H̄_m` the `(m+1)×m` Hessenberg matrix of the
  `h_ij`, `H_m` its top `m×m` part: `A V_m = V_m H_m + w_m e_mᵀ` (6.6) `= V_{m+1} H̄_m` (6.7),
  `V_mᵀ A V_m = H_m` (6.8); and `A v_j = ∑_{i=1}^{j+1} h_ij v_i` (6.9).
- **Lean surface statement.** `theorem equation_6_7 : A * V A v₁ m = V A v₁ (m + 1) * Hbar A v₁ m`;
  `theorem equation_6_6 : A * V A v₁ m = V A v₁ m * H A v₁ m + Matrix.vecMulVec (arnoldiW A v₁ (m-1)) (Pi.single (Fin.last _) 1)`
  (for `m ≥ 1`); `theorem equation_6_8 (hv) (hm : m ≤ μ) : (V A v₁ m)ᵀ * A * V A v₁ m = H A v₁ m`;
  `theorem equation_6_9 : Aop (v j) = ∑ i ∈ Finset.range (j + 2), h i j • v i`.
- **Backbone item.** §3.2 `Arnoldi.apply_vec` (6.9), `Arnoldi.apply_sum` and `Arnoldi.hessenbergRelation`
  with `Krylov.HessenbergRelation.apply_sum` ((6.7) in coordinates),
  `Arnoldi.hessenbergSq_eq_toMatrix_compression` + §2.1.6 `compression.toMatrix_orthonormalBasis`
  (6.8), `Arnoldi.coeff_succ_self` (`w_m = h_{m+1,m} v_{m+1}`); `Matrix.toEuclideanLin_apply_eq_sum`
  for `V_m y = ∑ y_j • v_j`.
- **Proof route.** Column `j` of (6.7) is `apply_vec`; (6.6) splits the last term of (6.9) at
  `j = m` via `vec_succ_eq`; (6.8): entry `(i, j)` of `V_mᵀ A V_m` is `inner (v i) (A v j) = h i j`
  by definition (real transpose = `ᴴ`). (6.8) needs no `hm` with our convention if `v j = 0` for
  `j ≥ μ` — but then `V_m` is not a basis; the book assumes `m` steps were taken, keep `hm`.
- **Classification.** `direct` (matrix-form bookkeeping only).

### R7. Proposition 6.6
- **Book statement.** Arnoldi's algorithm breaks down at step `j` (`h_{j+1,j} = 0` in line 5) iff the
  minimal polynomial of `v_1` has degree `j`; moreover `𝒦_j` is then invariant under `A`.
- **Lean surface statement.** `theorem proposition_6_6 (hv : ‖v₁‖ = 1) (hj : 0 < j) :
  (NoBreakdownBefore A v₁ j ∧ h j (j-1) = 0) ↔ grade A v₁ = j` and
  `theorem proposition_6_6' (h : NoBreakdownBefore A v₁ j ∧ h j (j-1) = 0) : krylov A v₁ j ∈ Module.End.invtSubmodule Aop`.
- **Backbone item.** §3.2 `Arnoldi.coeff_succ_self_eq_zero_iff` (`h_{j+1,j} = 0 ↔ grade ≤ j+1`),
  `Arnoldi.vec_eq_zero_iff`; §3.1 `subspace_grade_mem_invtSubmodule`.
- **Proof route.** "no earlier breakdown" gives `j ≤ grade`, the vanishing coefficient gives
  `grade ≤ j`; invariance from R2.
- **Classification.** `direct`.

### R8. Corollary of Prop 6.6 (lucky breakdown; text after Prop 6.6)
- **Book statement.** A projection method onto `𝒦_j` (any `L` with `𝒦_j ⊓ Lᗮ = 0`, `r_0 ∈ 𝒦_j`) is
  exact when a breakdown occurs at step `j` (via Prop 5.6).
- **Lean surface statement.** `theorem lucky_breakdown (hbreak : grade A v₁ ≤ j) {L}
  (hKL : ∀ z ∈ krylov A r₀ j, z ∈ Lᗮ → z = 0) (hx : IsPetrovGalerkin Aop b x₀ (krylov A r₀ j) L x) : Aop x = b`
  (with `v₁ = r₀/β`).
- **Backbone item.** §2.4.1 `IsPetrovGalerkin.eq_of_invt` + R2 invariance.
- **Proof route.** R7/R2 give invariance of `𝒦_j`, `r₀ ∈ 𝒦_j` for `j ≥ 1`; apply `eq_of_invt`.
- **Classification.** `direct`.

### R9. §6.3.2 — Algorithm 6.2 is mathematically equivalent to Algorithm 6.1
- **Book statement.** "In exact arithmetic, this algorithm and Algorithm 6.1 are mathematically
  equivalent" (same `v_j`, same `h_ij`).
- **Lean surface statement.** `theorem algorithm_6_2_eq_alg_6_1 (hv : ‖v₁‖ = 1) :
  arnoldiMGS A v₁ = arnoldiCGS A v₁ ∧ arnoldiMGSCoeff A v₁ = arnoldiCoeff A v₁`.
- **Backbone item.** §3.2 `Arnoldi.orthonormal` (through D2), or the flag lemma
  `InnerProductSpace.eq_gramSchmidtNormed_of_re_inner_pos`.
- **Proof route.** D3.
- **Classification.** `needs-equivalence` (this *is* the equivalence lemma; surface proof).

### R10. §6.3.2 — Householder Arnoldi: (6.10)–(6.13), (6.12) factorization, `A V_m = V_{m+1} H̄_m`, orthonormality, `±` Arnoldi; P-6.1 (a)–(f)
- **Book statement.** With `Q_j = P_j ⋯ P_1` (6.10): `Q_j A v_j = z_{j+1}`, `h_j = Q_{j+1} A v_j = Q_m A v_j`
  (6.11), `Q_m [v, A v_1, …, A v_m] = [h_0, …, h_m]` upper triangular with `Q_m` unitary (6.12),
  `Q_{j+1}ᵀ e_i = v_i` for `i ≤ j + 1` (6.13), hence `A V_m = V_{m+1} H̄_m`; the `v_i` are orthonormal
  and identical with the Arnoldi vectors apart from a possible sign. P-6.1: (a) `Q_{j+1}` unitary with
  inverse `Q_{j+1}ᵀ`, (b) `Q_{j+1}ᵀ = P_1 ⋯ P_{j+1}`, (c) `Q_{j+1}ᵀ e_i = v_i` (`i < j`),
  (d) `Q_{j+1} A V_m = V_{m+1}[e_1 … e_{j+1}] H̄_m`, (e) orthonormality, (f) equality with
  Gram–Schmidt Arnoldi up to scaling.
- **Lean surface statement.** For `A : Matrix (Fin n) (Fin n) ℝ`, `v ≠ 0`, `m + 1 ≤ n`, with
  `(vHH, hHH, wHH) := householderArnoldi A v m _`: `theorem hh_Q_orthogonal (j) : (Qhh j)ᵀ * Qhh j = 1`;
  `theorem equation_6_11 (j ≤ m) : hHH j = Qhh m (A v_j)`;
  `theorem equation_6_12 : Qhh m * [v, A v_1, …, A v_m] = [h_0, …, h_m] ∧ upperTriangular`;
  `theorem equation_6_13 (i ≤ j + 1) : (Qhh (j+1))ᵀ e_i = vHH i`;
  `theorem hh_arnoldi_relation : A * VHH m = VHH (m+1) * HbarHH`; `theorem hh_orthonormal : Orthonormal ℝ (vHH)`;
  `theorem hh_eq_arnoldi_up_to_sign : ∃ ε, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∀ j ≤ m, vHH j = ε j • arnoldiCGS A (‖v‖⁻¹ • v) j`.
- **Backbone item.** none (§3.2: Householder is surface); Mathlib `reflection`,
  `reflection_orthogonal`; `InnerProductSpace.exists_norm_eq_one_smul_gramSchmidtNormed`
  (`Numlib/Analysis/InnerProductSpace/GramSchmidt.lean`) for the sign statement.
- **Proof route.** `P_j` is an orthogonal involution fixing `e_i` (`i < j`) (`(w_j)_i = 0`); the
  triangular structure comes from the zero pattern of `h_j`; (6.13) by `P_k e_i = e_i` for `i < k`;
  orthonormality from (6.13) and orthogonality of `Q_{j+1}`; `A V_m = V_{m+1} H̄_m` by transporting
  (6.11) with (6.13); the `±` from the flag lemma applied to the flag `span{v_1..v_j} = 𝒦_j` (which
  follows from the triangular factorization by induction), with `ε j ∈ {±1}` since `‖ε j‖ = 1` in `ℝ`.
- **Classification.** `surface-only` (the backbone plan puts Householder in the surface; ~150 lines).

### R11. (6.16)–(6.17) — the FOM iterate is the Galerkin iterate on `𝒦_m(A, r_0)`
- **Book statement.** With `v_1 = r_0/‖r_0‖`, `β = ‖r_0‖`: `V_mᵀ A V_m = H_m`, `V_mᵀ r_0 = β e_1`, and
  the orthogonal projection method with `L = K = 𝒦_m(A, r_0)` (6.15) gives `x_m = x_0 + V_m y_m`,
  `y_m = H_m^{-1}(β e_1)`.
- **Lean surface statement.** `theorem fom_isGalerkinIterate (hH : FOMDefined A b x₀ m) (hm : m ≤ μ) :
  Krylov.IsGalerkinIterate Aop b x₀ m (fomFixed A b x₀ m)`;
  `theorem equation_6_16_17 (hH) (hm) (hx : Krylov.IsGalerkinIterate Aop b x₀ m x) : x = fomFixed A b x₀ m`;
  `theorem Vt_r₀ : (V A v₁ m)ᵀ *ᵥ r₀ = β • e₁ m`.
- **Backbone item.** §3.5 `Krylov.isGalerkinIterate_iff_mulVec_eq`,
  `Krylov.isGalerkinIterate_iff_exists_mulVec_eq`, `Krylov.existsUnique_isGalerkinIterate_iff_isUnit`
  (`Numlib/Krylov/Hessenberg.lean`); §2.4.1 `isPetrovGalerkin_iff_mulVec` (with
  `V = W = Arnoldi.orthonormalBasis`) for the book's derivation through (5.7).
- **Proof route.** `fom_isGalerkinIterate` and `existsUnique_isGalerkinIterate_iff` (D5); `Vt_r₀` from
  `Arnoldi.vec_zero` and orthonormality.
- **Classification.** `direct`.

### R12. Proposition 6.7, (6.18)
- **Book statement.** The FOM residual satisfies `b − A x_m = −h_{m+1,m} (e_mᵀ y_m) v_{m+1}`, hence
  `‖b − A x_m‖₂ = h_{m+1,m} |e_mᵀ y_m|` (6.18).
- **Lean surface statement.** `theorem proposition_6_7 (hH : FOMDefined A b x₀ m) (hm : m ≤ μ) (hm0 : 0 < m) :
  b - Aop (fomFixed A b x₀ m) = -(h m (m-1) * fomY A b x₀ m (Fin.last _)) • v m` and
  `theorem equation_6_18 … : ‖b - Aop (fomFixed …)‖ = ‖h m (m-1)‖ * ‖fomY … (Fin.last _)‖` (`h m (m-1)` is
  real `≥ 0`, `‖v m‖ = 1` when `m < μ`; when `m = μ` both sides are `0`).
- **Backbone item.** §3.5 `Krylov.residual_galerkin_eq` (the Arnoldi instance of
  `Krylov.HessenbergRelation.residual_eq_of_mulVec_eq`); §3.4 `Krylov.IsGalerkinIterate.residual_mem_span`;
  §3.2 `Arnoldi.norm_vec_eq_one_of_lt_grade`, `Arnoldi.vec_eq_zero_iff`.
- **Proof route.** `H_m y = β e₁` for `y = fomY` (D5), then `residual_galerkin_eq`; the norm form by
  `‖v m‖ = 1` or `v m = 0`.
- **Classification.** `direct`.

### R13. §6.4.2 — (6.6)/(6.7), Prop 6.7 and (6.18) remain valid for IOP/IOM/DIOM; DIOM residual `h_{m+1,m}|ζ_m/u_mm|`
- **Book statement.** "(6.6) is still valid" for the incomplete orthogonalization (orthogonality was
  not used), so Prop 6.7 and (6.18) hold for IOM/DIOM; moreover
  `‖b − A x_m‖₂ = h_{m+1,m}|e_mᵀ y_m| = h_{m+1,m}|ζ_m/u_mm|`.
- **Lean surface statement.** `theorem iop_eq_6_7 : A * VI A v₁ k m = VI A v₁ k (m+1) * HbarI A v₁ k m`;
  `theorem iom_residual (hH : IsUnit (HI …)) (hnb : ∀ j < m, iopCoeff … (j+1) j ≠ 0) :
  b - Aop (iom A b x₀ k m) = -(h^I_{m+1,m} * y^I_m) • vI m ∧ ‖…‖ = h^I_{m+1,m} * |y^I_m|`;
  `theorem diom_residual (hu : ∀ j ≤ m, u_jj ≠ 0) : ‖b - Aop (diom A b x₀ k m).x‖ = h^I_{m+1,m} * |ζ_m / u_mm|`.
- **Backbone item.** §3.5 `Krylov.HessenbergRelation.apply_sum`,
  `Krylov.HessenbergRelation.residual_eq_of_mulVec_eq` (`Numlib/Krylov/Hessenberg.lean`), instantiated
  by `iop_hessenbergRelation` (D6).
- **Proof route.** The backbone residual formula with the IOP relation; `e_mᵀ y_m = ζ_m/u_mm` from
  `U_m y_m = z_m` and `U_m` upper triangular.
- **Classification.** `needs-equivalence` (`iop_hessenbergRelation`; the DIOM form adds R14's LU
  bookkeeping).

### R14. §6.4.2 — DIOM is mathematically equivalent to IOM (6.20)–(6.21)
- **Book statement.** With `H_m = L_m U_m` (no pivoting), `P_m = V_m U_m^{-1}`, `z_m = L_m^{-1}(β e_1)`:
  `x_m = x_0 + P_m z_m` (6.20) and `x_m = x_{m−1} + ζ_m p_m` (6.21), so Alg 6.8 produces the IOM
  iterates.
- **Lean surface statement.** `theorem hessLU_spec (hu : ∀ j, u_jj ≠ 0) :
  (hessLU Hm).1 * (hessLU Hm).2 = Hm ∧ unitLowerBidiagonal L ∧ upperTriangularBand U k`;
  `theorem diom_x_eq_iom (hu : ∀ j ≤ m, (hessLU (HI … m)).2 j j ≠ 0) : (diom A b x₀ k m).x = iom A b x₀ k m`.
- **Backbone item.** none (§1.2).
- **Proof route.** Induction on `m` with the last-column identities `∑_{i=m−k+1}^m u_im p_i = v_m`
  and `ζ_m = −l_{m,m−1} ζ_{m−1}`; the LU of a Hessenberg matrix is `Matrix.BlockTriangular`
  bookkeeping.
- **Classification.** `surface-only`.

### R15. Proposition 6.8
- **Book statement.** IOM and DIOM are mathematically equivalent to a projection process onto `𝒦_m`
  orthogonally to `L_m = span{z_1, …, z_m}`, `z_i = v_i − (v_i, v_{m+1}) v_{m+1}`.
- **Lean surface statement.** `theorem proposition_6_8 (hH : IsUnit (HI …)) (hnb : ∀ j < m, iopCoeff … (j+1) j ≠ 0)
  (hspan : span (vI '' Iio m) = krylov A r₀ m) : IsPetrovGalerkin Aop b x₀ (krylov A r₀ m)
  (Submodule.span ℝ (Set.range fun i : Fin m => vI i - inner (vI m) (vI i) • vI m)) (iom A b x₀ k m)`.
- **Backbone item.** §2.4.1 `IsPetrovGalerkin`.
- **Proof route.** `mem`: `x_m − x_0 ∈ span(V_m) = 𝒦_m`; `orth`: the residual is a multiple of
  `v_{m+1}` (R13) and `(z_i, v_{m+1}) = 0` by construction.
- **Classification.** `surface-only` (5 lines given R13).

### R16. (6.22)–(6.24) (P-6.22)
- **Book statement.** For IOM/DIOM with parameter `k`: `(r_j, r_i) = 0` for `|i − j| ≤ k, i ≠ j`
  (6.22); `(A p_j, v_i) = 0` for `j − k + 1 < i < j` (6.23); for `k = ∞` (full orthogonalization)
  `(A p_j, p_i) = 0` for `i < j` (6.24) (semi-conjugacy).
- **Lean surface statement.** `theorem equation_6_22 (hij : i ≠ j) (hk : |(i:ℤ) - j| ≤ k) : inner (rI i) (rI j) = 0`;
  `theorem equation_6_23 (h₁ : j + 1 < i + k) (h₂ : i < j) : inner (vI i) (Aop (pD j)) = 0`;
  `theorem equation_6_24 (hk : m ≤ k) (h : i < j) : inner (pD i) (Aop (pD j)) = 0` (under the no-breakdown
  hypotheses of R13/R14).
- **Backbone item.** none.
- **Proof route.** (6.22): `r_j ∝ v_{j+1}` and local orthogonality of IOP vectors; (6.23):
  `A P_m = V_{m+1} H̄_m U_m^{-1}` and `H̄_m U_m^{-1}` is unit lower bidiagonal plus a last row, so
  `A p_j ∈ span{v_j, v_{j+1}}`; (6.24): `P_mᵀ A P_m = U_m^{-T} L_m` is lower triangular.
- **Classification.** `surface-only`.

### R17. (6.27)–(6.28)
- **Book statement.** For `x = x_0 + V_m y`: `b − A x = V_{m+1}(β e_1 − H̄_m y)` (6.27) and
  `J(y) = ‖b − A(x_0 + V_m y)‖₂ = ‖β e_1 − H̄_m y‖₂` (6.28).
- **Lean surface statement.** `theorem equation_6_27 (y : Fin m → ℝ) :
  b - Aop (x₀ + V *ᵥ y) = V A v₁ (m+1) *ᵥ (β • e₁ (m+1) - Hbar A v₁ m *ᵥ y)`;
  `theorem equation_6_28 (hm : m ≤ μ) (y) : ‖b - Aop (x₀ + V *ᵥ y)‖ = J A b x₀ m y`.
- **Backbone item.** §3.5 `Krylov.HessenbergRelation.residual_eq` through `Arnoldi.hessenbergRelation`
  (6.27), `Krylov.norm_residual_eq_norm_firstVec_sub_mulVec` (6.28) (`Numlib/Krylov/Hessenberg.lean`);
  §3.2 `Arnoldi.vec_zero`, `Arnoldi.orthonormal`.
- **Proof route.** `r₀ = β v_0` (`Arnoldi.vec_zero`), then the two backbone lemmas, with
  `Matrix.toEuclideanLin_apply_eq_sum` for `V y`. (If `m = μ`, `v_m = 0` and the last coordinate of
  `β e_1 − H̄ y` is `0` since `h_{m+1,m} = 0`, which is why (6.28) holds up to `m = μ`.)
- **Classification.** `direct`.

### R18. (6.29)–(6.30) — GMRES iterate is the (unique) minimal-residual iterate
- **Book statement.** The GMRES approximation is the unique vector of `x_0 + 𝒦_m` minimizing (6.26);
  it is `x_m = x_0 + V_m y_m` with `y_m = argmin_y ‖β e_1 − H̄_m y‖₂`.
- **Lean surface statement.** `theorem isGMRESIterate_iff (hm : m ≤ μ) :
  IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResIterate Aop b x₀ m x`;
  `theorem gmres_unique (hm) (hA : IsUnit A) : ∃! x, IsGMRESIterate A b x₀ m x`.
- **Backbone item.** §3.4 `Krylov.IsMinResIterate`, `Krylov.exists_isMinResIterate`,
  `Krylov.existsUnique_isMinResIterate_of_injective` (`Numlib/Krylov/Iterate.lean`); §3.5
  `Krylov.isMinResIterate_iff_isMinOn`; §2.4.1 `existsUnique_isMinRes_of_injOn`, `exists_isMinRes`.
- **Proof route.** D7 (both directions via (6.28) and the parametrization `x₀ + V_m y` of
  `x₀ + 𝒦_m`).
- **Classification.** `direct`.

### R19. §6.5.2 — Householder GMRES (Alg 6.10) computes the GMRES iterate; (6.31)–(6.33); `β = ±‖r_0‖`; residual norm `‖h_0 − ∑ η_i h_i‖`
- **Book statement.** With the Householder Arnoldi basis, `x_m = x_0 + ∑ η_j v_j` is obtained by
  `z := 0; z := P_j(η_j e_j + z)` for `j = m..1`; `x_m = x_0 + z` (6.31)–(6.33); the scalar
  `β = e_1ᵀ h_0` equals `±‖r_0‖₂`; the residual norm of `x_0 + V_m y` equals
  `‖h_0 − η_1 h_1 − ⋯ − η_m h_m‖₂` whose minimizer is the same `y_m`.
- **Lean surface statement.** `theorem horner_eq (P) (η) : hornerAccumulate P η = ∑ j, η j • (P 0 ∘ … ∘ P j) e_j`;
  `theorem hh_beta : |βHH| = ‖r₀‖`; `theorem hh_residual_norm (y) : ‖b - Aop (x₀ + VHH *ᵥ y)‖ = ‖h₀ - ∑ j, y j • hHH j‖`;
  `theorem gmresHH_eq (hm : m ≤ μ) (hn : m + 1 ≤ n) : gmresHH A b x₀ m hn = gmres A b x₀ m`.
- **Backbone item.** none (surface); uses R10 and R18.
- **Proof route.** D7; `Q_m` orthogonal makes the residual norm `‖Q_m(r_0 − ∑ η_i A v_i)‖ = ‖h_0 − ∑ η_i h_i‖`.
- **Classification.** `surface-only` (depends on R10).

### R20. §6.5.3/§6.5.9 — properties of the rotations (6.34)–(6.40), (6.80)–(6.81)
- **Book statement.** `c_i² + s_i² = 1` (real) / `|c_i|² + |s_i|² = 1` (complex); each `Ω_i` and
  `Q_m = Ω_m ⋯ Ω_1` is unitary; `R̄_m = Q_m H̄_m` is upper triangular with zero last row;
  `ḡ_m = Q_m(β e_1)`; in the complex case `s_i` is real nonnegative, `c_i` complex, the diagonal of
  `R_m` is real nonnegative and the `γ_i` are real (§6.5.9).
- **Lean surface statement.** `theorem c_sq_add_s_sq (i) (hρ : Krylov.givensRho h i ≠ 0) : ‖c h i‖^2 + ‖s h i‖^2 = 1`;
  `theorem givens_mem_unitary (hρ) : Ω h i m ∈ Matrix.unitaryGroup _ 𝕜`; `theorem Qrot_mem_unitary (hρ : ∀ i < m, …)`;
  `theorem Rbar_upperTriangular : (∀ i j : Fin _, (j : ℕ) < i → Rbar h m i j = 0) ∧ ∀ j, Rbar h m (Fin.last m) j = 0`
  (for upper Hessenberg `h`); `theorem s_real_nonneg : s h i = ((‖arnoldiW A v₁ i‖ / Krylov.givensRho h i : ℝ) : 𝕜)`;
  `theorem Rbar_diag_real_nonneg : R h m i i = (Krylov.givensRho h i : 𝕜)`; `theorem γ_real : ∀ i, (γ h β i).im = 0`.
- **Backbone item.** `Numlib/Krylov/Hessenberg.lean` (D8): `Krylov.norm_givensC_sq_add_norm_givensS_sq`,
  `givensMatrix_mem_unitaryGroup`, `givensQ_mem_unitaryGroup`, `rotated_eq_zero_of_lt`,
  `rotated_last_row` (with `Rbar_eq`), `rotated_succ_self`, `givensS_arnoldi_eq`, `gamma_succ`;
  §3.2 `Arnoldi.hessenberg_isUpperHessenbergRect` / `Arnoldi.coeff_eq_zero_of_lt` for the Hessenberg
  hypothesis.
- **Proof route.** Instances of the backbone lemmas at `h = arnoldiCoeff A v₁`; `γ_i` real by
  induction from `gamma_succ` and real `s_i`.
- **Classification.** `direct` (the reality of `γ_i` is a three-line surface induction).

### R21. (6.43)
- **Book statement.** For every `y`: `‖β e_1 − H̄_m y‖₂² = ‖Q_m(β e_1 − H̄_m y)‖² = ‖ḡ_m − R̄_m y‖² = |γ_{m+1}|² + ‖g_m − R_m y‖₂²`.
- **Lean surface statement.** `theorem equation_6_43 (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0) (y : Fin m → 𝕜) :
  (J A b x₀ m y)^2 = ‖γ h β m‖^2 + ‖g h β m - R h m *ᵥ y‖^2` (Euclidean norms on `Fin m → 𝕜` via
  `WithLp.toLp 2`).
- **Backbone item.** `Krylov.givensQ_mem_unitaryGroup`, `Rbar_eq`, `gbar_eq` (D8),
  `Krylov.rotated_last_row`, and the Euclidean-norm invariance of a unitary matrix, which now
  exists as `Matrix.norm_toLp_mulVec_of_mem_unitaryGroup` in
  `Numlib/Analysis/Matrix/ToEuclideanLin.lean`.
- **Proof route.** `Q_m` unitary preserves the norm (the lemma just named); split the last
  coordinate (last row of `R̄_m` is `0`, last entry of `ḡ_m` is `γ_{m+1}`).
- **Classification.** `surface-only` once the unitary-invariance lemma exists (ten lines from the
  D8 lemmas); it is the same ingredient the Givens residual identities of D10 wait on.

### R22. Proposition 6.9 (1)–(3), (6.41)–(6.42)
- **Book statement.** Let `m ≤ n`, rotations as above, `R_m, g_m` the top parts. (1) `rank(A V_m) = rank(R_m)`;
  in particular `r_mm = 0 ⇒ A` singular. (2) The minimizer of `‖β e_1 − H̄_m y‖₂` is `y_m = R_m^{-1} g_m`.
  (3) `b − A x_m = V_{m+1}(β e_1 − H̄_m y_m) = V_{m+1} Q_mᵀ(γ_{m+1} e_{m+1})` (6.41) and
  `‖b − A x_m‖₂ = |γ_{m+1}|` (6.42).
- **Lean surface statement.** (implicit hypothesis "m steps taken": `hm : m ≤ μ`)
  `theorem proposition_6_9_1 (hm) : (A * V A v₁ m).rank = (R h m).rank ∧ (R h m (Fin.last _) (Fin.last _) = 0 → ¬ IsUnit A)`;
  `theorem proposition_6_9_2 (hm) (hR : IsUnit (R h m)) : IsMinOn (J A b x₀ m) univ (gmresY A b x₀ m) ∧ ∀ y, IsMinOn (J …) univ y → y = gmresY …`;
  `theorem equation_6_41 (hm) (hR) : b - Aop (gmresFixed A b x₀ m) = V A v₁ (m+1) *ᵥ ((Qrot h m)ᴴ *ᵥ (γ h β m • e_{m+1}))`;
  `theorem equation_6_42 (hm' : m < μ) (hR) : ‖b - Aop (gmresFixed A b x₀ m)‖ = ‖γ h β m‖`
  (strict here: `norm_residual_eq_norm_gamma` is false at `m = μ`, where `γ_m` degenerates to `0`
  while the residual need not vanish; `hR : IsUnit (R h m)` is exactly `∀ k < m, ρ_k ≠ 0`, which is
  what would rescue the boundary case, but the backbone statement is the `m < μ` one).
- **Backbone item.** §3.5 `Krylov.IsMinResIterate.norm_residual_eq_norm_gamma` (6.42),
  `Krylov.IsMinResIterate.exists_mulVec_rotated_eq` (the minimal-residual iterate has coordinates
  with `R_m y = g_m`), `Krylov.HessenbergRelation.residual_eq` and `Krylov.givensQ_mulVec_firstVec`
  (6.41); §2.4.1 `IsMinRes.residual_eq`; R17, R21.
- **Proof route.** (2): R21 shows the minimum of `|γ|² + ‖g − R y‖²` is attained exactly at
  `R y = g`, unique when `R` is a unit (and `exists_mulVec_rotated_eq` gives the same `y` for the
  backbone iterate); (3): `isGMRESIterate_iff` then `norm_residual_eq_norm_gamma`; (6.41) from
  (6.27) and `Q_mᴴ Q_m = 1`; (1): `A V_m = (V_{m+1} Q_mᴴ) R̄_m` with `V_{m+1} Q_mᴴ` injective, so
  `rank(A V_m) = rank R̄_m = rank R_m`; `r_mm = 0` gives `rank R_m ≤ m − 1` while `V_m` has rank `m`.
- **Classification.** `direct` for (2)–(3); `surface-only` for (1) (rank bookkeeping with
  `Matrix.rank`).

### R23. (6.44)–(6.47) — progressive update and `γ_{j+1} = −s_j γ_j`
- **Book statement.** Appending the `(m+1)`-st Arnoldi column and applying `Ω_1..Ω_m` to it, then
  `Ω_{m+1}`, yields `R̄_{m+1}, ḡ_{m+1}` with `ḡ_{m+1} = (γ_1, …, γ_m, c_{m+1} γ_{m+1}, −s_{m+1} γ_{m+1})ᵀ`;
  hence `γ_{j+1} = −s_j γ_j` (6.47); if `s_j = 0` the solution is exact at step `j`.
- **Lean surface statement.** `theorem Rbar_succ_submatrix : (Rbar h (m+1)).submatrix Fin.castSucc Fin.castSucc = Rbar h m`
  (the first `m` columns of `R̄_{m+1}` are those of `R̄_m`, extended by a zero row);
  `theorem gbar_succ : gbar h β (m+1) = Fin.snoc (Fin.snoc (g h β m) (Krylov.gvec h β m)) (γ h β (m+1))`;
  `theorem equation_6_47 (j : ℕ) : γ h β (j+1) = -(s h j) * γ h β j`;
  `theorem exact_of_s_eq_zero (hm) (hR) (hs : s h (m-1) = 0) : Aop (gmresFixed A b x₀ m) = b`.
- **Backbone item.** `Krylov.gamma_succ` (6.47), `Krylov.givensQ_mulVec_firstVec` ((6.44)–(6.46)),
  `Krylov.rotated_succ_eq_of_lt` (rotation `m` leaves the first `m` columns unchanged) and
  `Krylov.rotated_eq_of_le`; since `c_i, s_i, γ_i` are defined from the infinite coefficient function
  they do not depend on `m` (the book's "the previous rotations need not be recomputed").
- **Proof route.** `Rbar_eq`/`gbar_eq` and the listed lemmas; exactness from (6.42) and
  `gamma_succ`.
- **Classification.** `direct`.

### R24. Proposition 6.10 (breakdown of GMRES)
- **Book statement.** Let `A` be nonsingular. GMRES breaks down at step `j` (`h_{j+1,j} = 0`) iff the
  approximate solution `x_j` is exact.
- **Lean surface statement.** `theorem proposition_6_10 (hA : IsUnit A) (hj : NoBreakdownBefore A v₁ j) (hj0 : 0 < j) :
  h j (j-1) = 0 ↔ Aop (gmresFixed A b x₀ j) = b`.
- **Backbone item.** §3.4 `Krylov.IsMinResIterate.apply_eq_of_grade_le` (⇒, lucky breakdown; its
  `Set.InjOn` hypothesis from `IsUnit A`) and `Krylov.grade_le_of_apply_eq` (⇐: an exact solution in
  `x₀ + 𝒦_j` forces `grade ≤ j`) (`Numlib/Krylov/Iterate.lean`); §3.2
  `Arnoldi.coeff_succ_self_eq_zero_iff`.
- **Proof route.** `h_{j+1,j} = 0 ↔ grade ≤ j` (R7); both directions are the backbone lemmas. (The
  book's route through `s_j = 0` is R23 + R22(1).)
- **Classification.** `direct`.

### R25. §6.5.5 remark — full GMRES converges in at most `n` steps
- **Book statement.** "The full GMRES algorithm is guaranteed to converge in at most `n` steps"
  (nonsingular `A`).
- **Lean surface statement.** `theorem gmres_exact_of_card_le (hA : IsUnit A) (hm : n ≤ m) : Aop (gmres A b x₀ m) = b`
  (and `∃ m ≤ n, Aop (gmres A b x₀ m) = b`).
- **Backbone item.** §3.4 `Krylov.IsMinResIterate.apply_eq_of_grade_le` + §3.1 `Krylov.grade_le_finrank`.
- **Proof route.** `mEff = min m μ ≥ μ` when `m ≥ n ≥ μ`.
- **Classification.** `direct`.

### R26. (6.50) — DQGMRES residual
- **Book statement.** For QGMRES/DQGMRES, `b − A x_m = V_{m+1} Q_mᵀ(γ_{m+1} e_{m+1}) ≡ γ_{m+1} z_{m+1}`
  ((6.41) is still valid since orthogonality was not used); `‖b − A x_m‖ = ‖V_{m+1}(β e_1 − H̄_m y_m)‖`
  with `y_m` the minimizer of the quasi-residual norm.
- **Lean surface statement.** `theorem equation_6_50 (hR : IsUnit (R (iopCoeff …) m)) :
  b - Aop (qgmres A b x₀ k m) = γ (iopCoeff …) β m • z A b x₀ k m`.
- **Backbone item.** `Krylov.HessenbergRelation.residual_eq` (through `iop_hessenbergRelation`, D6),
  `Krylov.givensQ_mem_unitaryGroup`, `Krylov.givensQ_mulVec_firstVec`, `Rbar_eq`/`gbar_eq` at
  `h = iopCoeff A v₁ k` (D8–D9).
- **Proof route.** R22(3)'s computation with `VI` in place of `V` (no orthogonality used).
- **Classification.** `needs-equivalence` (`iop_hessenbergRelation`).

### R27. (6.51)
- **Book statement.** `‖b − A x_m‖ ≤ √(m − k + 1) |γ_{m+1}|` (with `k := m` when `m ≤ k`): the
  quasi-residual overestimates the residual by at most `√(m−k+1)`.
- **Lean surface statement.** `theorem equation_6_51 (hR) (hnb : IOP no breakdown up to m) :
  ‖b - Aop (qgmres A b x₀ k m)‖ ≤ Real.sqrt (m - min k m + 1) * ‖γ (iopCoeff …) β m‖`.
- **Backbone item.** none.
- **Proof route.** The book's: split `q = Q_mᵀ e_{m+1}` into the first `k+1` (orthonormal `v_i`) and
  remaining components; triangle inequality, Cauchy–Schwarz twice, `‖q‖ = 1`.
- **Classification.** `surface-only`.

### R28. (6.53)–(6.54) (and P-6.25)
- **Book statement.** `Z_{m+1} = [Z_m, v_{m+1}] Ω_mᵀ`, so `z_{m+1} = −s_m z_m + c_m v_{m+1}` (6.53)
  and `ζ_{m+1} ≤ |s_m| ζ_m + |c_m|` (6.54). P-6.25: (6.54) implies `ζ_{m+1} ≤ √(m − k + 1)` for
  `m ≥ k`, so (6.54) is sharper than (6.51).
- **Lean surface statement.** `theorem equation_6_53 : z A b x₀ k (m+1) = -(s (iopCoeff …) m) • z … m + c (iopCoeff …) m • vI m`;
  `theorem equation_6_54 : ζ … (m+1) ≤ ‖s … m‖ * ζ … m + ‖c … m‖`;
  `theorem problem_6_25 (hk : k ≤ m) : ζ … (m+1) ≤ Real.sqrt (m - k + 1)`.
- **Backbone item.** the entries of `Krylov.givensMatrix` (D8).
- **Proof route.** Last column of `[Z_m, v_{m+1}] Ω_mᵀ`; norm triangle inequality; P-6.25 by
  induction and Cauchy–Schwarz as hinted.
- **Classification.** `surface-only`.

### R29. (6.55) — two successive DQGMRES residuals
- **Book statement.** `r_m = γ_{m+1} z_{m+1} = γ_{m+1}[−s_m z_m + c_m v_{m+1}] = s_m² r_{m−1} + c_m γ_{m+1} v_{m+1}`.
- **Lean surface statement.** `theorem equation_6_55 (hR) : rQ m = (s … m)^2 • rQ (m-1) + (c … m * γ … m) • vI m`
  (`rQ j := b - Aop (qgmres A b x₀ k j)`).
- **Backbone item.** R26 + R28 + `Krylov.gamma_succ` (6.47).
- **Proof route.** Substitute (6.53) into (6.50) and use (6.47).
- **Classification.** `surface-only` (the `k ≥ m` GMRES instance is the same proof after
  `qgmres_eq_gmres`).

### R30. (6.56)–(6.58) — DQGMRES versus IOM
- **Book statement.** `r_m^I = −h_{m+1,m}(e_mᵀ y_m) v_{m+1} = (h_{m+1,m}/(s_m h_mm^{(m−1)})) γ_{m+1} v_{m+1}`;
  since `h_{m+1,m}/h_mm^{(m)} = tan θ_m`: `γ_{m+1} v_{m+1} = c_m r_m^I` (6.56), `ρ_m^Q = |c_m| ρ_m`
  with `ρ_m = ‖r_m^I‖` (6.57), and `r_m = s_m² r_{m−1} + c_m² r_m^I` (6.58).
- **Lean surface statement.** `theorem equation_6_56 (hI : IsUnit (HI …)) (hR) : γ … m • vI m = c … m • rI m`;
  `theorem equation_6_57 : ‖γ … m‖ = ‖c … m‖ * ‖rI m‖`;
  `theorem equation_6_58 : rQ m = (s … m)^2 • rQ (m-1) + (c … m)^2 • rI m`.
- **Backbone item.** none beyond R13 and the D8 data (the orthonormal instance is §3.5/§3.6,
  R33/R38).
- **Proof route.** R13 for `r^I_m`, the FOM-`y` last component `γ_m/h_mm^{(m−1)}` (as in R33),
  (6.37) and (6.47).
- **Classification.** `surface-only`.

### R31. Theorem 6.11 (Freund–Nachtigal bound for DQGMRES)
- **Book statement.** Assume `V_{m+1}` (the IOP basis) has full rank. Let `r_m^Q`, `r_m^G` be the
  DQGMRES and GMRES residuals after `m` steps. Then `‖r_m^Q‖₂ ≤ κ₂(V_{m+1}) ‖r_m^G‖₂` (6.59). (Proof
  in `ℂ^m`.)
- **Lean surface statement.** Over `ℂ`: `theorem theorem_6_11 (hV : (VI A v₁ k (m+1)).rank = m + 1)
  (S : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hS : IsUnit S) (hW : (VI … (m+1) * S)ᴴ * (VI … (m+1) * S) = 1) :
  ‖rQ m‖ ≤ ‖S‖₂ * ‖S⁻¹‖₂ * ‖b - Aop (gmresFixed A b x₀ m)‖` (`‖·‖₂` = `Matrix.Norms.L2Operator`),
  together with `theorem exists_S (hV) : ∃ S, IsUnit S ∧ (VI * S)ᴴ (VI * S) = 1` and the remark
  `κ₂(V_{m+1}) = ‖S‖‖S⁻¹‖` for any such `S` (which is how `κ₂` of a rectangular matrix is defined
  here).
- **Backbone item.** §3.4 `Krylov.IsMinResIterate` (for `r^G`); §2.1.2 `NormedRing.condNumber`
  (`Numlib/Analysis/Normed/Ring/CondNumber.lean`) under the L2 operator norm.
- **Proof route.** The book's: `r = W S⁻¹ t`, `t = S Wᴴ r`; minimality of `t_m` over the set `ℛ` of
  residuals of `x₀ + span(V_m) = x₀ + 𝒦_m`, and `r^G ∈ ℛ`.
- **Classification.** `surface-only` (Gram–Schmidt `S` from `hV`; ~60 lines).

### R32. (6.62)
- **Book statement.** `ρ_m^G = |s_m| ρ_{m−1}^G`, hence `ρ_m^G = |s_1 s_2 ⋯ s_m| β` (the `s_i` of (6.37)
  are nonnegative).
- **Lean surface statement.** `theorem equation_6_62 (hm : m < μ) (hR) : ρG A b x₀ m = (∏ i ∈ range m, ‖s h i‖) * β`
  and `theorem ρG_succ (hm : m + 1 < μ) : ρG … (m+1) = ‖s h m‖ * ρG … m`.
- **Backbone item.** §3.5 `Krylov.IsMinResIterate.norm_residual_succ_eq` (`‖r^G_{m+1}‖ = |s_m| ‖r^G_m‖`,
  hypothesis `m + 1 < grade`), `Krylov.norm_gamma_eq_prod` with
  `Krylov.IsMinResIterate.norm_residual_eq_norm_gamma` (hypothesis `m < grade`)
  (`Numlib/Krylov/Hessenberg.lean`); both grade hypotheses are strict, which is why the surface
  statements above stop one step short of the grade.
- **Proof route.** `isGMRESIterate_iff` then the backbone lemmas.
- **Classification.** `direct`.

### R33. Proposition 6.12 (Brown), (6.63)
- **Book statement.** Assume `m` Arnoldi steps taken and `H_m` nonsingular; `ξ = (Q_{m−1} H̄_m)_{mm}`,
  `h = h_{m+1,m}`. Then `ρ_m^F = ρ_m^G/|c_m| = ρ_m^G √(1 + h²/ξ²)`.
- **Lean surface statement.** `theorem proposition_6_12 (hm : m ≤ μ) (hm0 : 0 < m) (hH : FOMDefined A b x₀ m) :
  c h (m-1) ≠ 0 ∧ ρF A b x₀ m = ρG A b x₀ m / ‖c h (m-1)‖ ∧ ρF … = ρG … * Real.sqrt (1 + (h m (m-1))^2 / ‖ξ h m‖^2)`.
- **Backbone item.** §3.5 `Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC`
  (`‖r^F_{m+1}‖ = ‖r^G_{m+1}‖/|c_m|`), `Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero` (`c_m ≠ 0`);
  R12, R32.
- **Proof route.** The first two claims are the backbone lemmas after `fom_isGalerkinIterate` and
  `isGMRESIterate_iff`; the `√(1 + h²/ξ²)` form from `c_{m−1} = ξ_m/ρ_{m−1}` (`Krylov.givensC`),
  `ρ_{m−1}² = |ξ_m|² + h²` (`Krylov.givensRho`, with `Krylov.rotated_eq_of_le` showing `h_{m+1,m}` is
  untouched by the first `m − 1` rotations).
- **Classification.** `direct` (plus a few lines of real algebra for the second form).

### R34. Proposition 6.13 (Cullum–Greenbaum), (6.64)–(6.65)
- **Book statement.** Assume `m` Arnoldi steps and `H_m` nonsingular. Then
  `ρ_m^F = ρ_m^G/√(1 − (ρ_m^G/ρ_{m−1}^G)²)` (6.64), i.e. `1/(ρ_m^F)² + 1/(ρ_{m−1}^G)² = 1/(ρ_m^G)²` (6.65).
- **Lean surface statement.** `theorem proposition_6_13 (hm : m ≤ μ) (hm0 : 0 < m) (hH : FOMDefined A b x₀ m) (hG : ρG A b x₀ m ≠ 0) :
  ρF … m = ρG … m / Real.sqrt (1 - (ρG … m / ρG … (m-1))^2)` and
  `theorem equation_6_65 … : 1 / (ρF … m)^2 + 1 / (ρG … (m-1))^2 = 1 / (ρG … m)^2`.
- **Backbone item.** §3.6 `Krylov.inv_sq_norm_residual_minRes` (`Numlib/Krylov/Relations.lean`; spec
  form with `r^G_m ≠ 0`).
- **Proof route.** R11/R18 turn `fomFixed`/`gmresFixed` into the specs; apply the backbone identity;
  (6.64) is algebra from (6.65). (The extra hypothesis `ρ_m^G ≠ 0` is implicit in the book's
  divisions.)
- **Classification.** `direct`.

### R35. (6.66) and Corollary 6.14, (6.67)
- **Book statement.** Summing (6.65) for `m, m−1, …, 1` (with `ρ_0^G = ρ_0^F = β`):
  `∑_{i=0}^m 1/(ρ_i^F)² = 1/(ρ_m^G)²` (6.66), i.e. `ρ_m^G = 1/√(∑_{i=0}^m (1/ρ_i^F)²)` (6.67).
- **Lean surface statement.** `theorem equation_6_66 (hm : m ≤ μ) (hH : ∀ i ≤ m, FOMDefined A b x₀ i) (hG : ρG … m ≠ 0) :
  ∑ i ∈ Finset.range (m+1), 1 / (ρF … i)^2 = 1 / (ρG … m)^2`; `corollary_6_14 : ρG … m = 1 / Real.sqrt (∑ …)`.
  (With singular `H_i` skipped, as in Prop 6.15: replace `1/(ρF i)^2` by
  `if FOMDefined … i then … else 0`; the sum identity still holds because `c_i = 0` contributes `0`.)
- **Backbone item.** §3.6 `Krylov.inv_sq_norm_residual_minRes_eq_sum` (all Galerkin iterates `i ≤ m`
  exist).
- **Proof route.** Backbone; for the skipped-steps form, telescoping induction on R34
  (`ρG (m-1) ≠ 0` follows from `ρG m ≠ 0` by monotonicity `IsMinRes.norm_residual_le`).
- **Classification.** `direct` (all `H_i` nonsingular); `surface-only` telescoping for the
  skipped-steps form.

### R36. Proposition 6.15, (6.68)
- **Book statement.** Assume `m` steps of GMRES and FOM (FOM steps with singular `H_i` skipped). Let
  `ρ^F_{m*}` be the smallest FOM residual norm in the first `m` steps. Then
  `ρ_m^G ≤ ρ^F_{m*} ≤ √(m+1) ρ_m^G` (the constant is discussed in §6).
- **Lean surface statement.** `theorem proposition_6_15 (hm : m ≤ μ) (hG : ρG … m ≠ 0) :
  ρG A b x₀ m ≤ ρFmin A b x₀ m ∧ ρFmin A b x₀ m ≤ Real.sqrt (m + 1) * ρG A b x₀ m`.
- **Backbone item.** §3.6 `Krylov.norm_residual_minRes_le_galerkin`, `Krylov.exists_norm_residual_galerkin_le`
  (`min_{i ≤ m} ‖r_i^F‖ ≤ √(m+1) ‖r_m^G‖`, all Galerkin iterates existing); §2.4.1
  `IsMinRes.norm_residual_le` (nested subspaces).
- **Proof route.** Lower bound: every FOM iterate lies in `x₀ + 𝒦_i ⊆ x₀ + 𝒦_m`; upper bound:
  backbone when all `H_i` are nonsingular, otherwise at most `m+1` terms in the skipped form of
  (6.66), each `≤ 1/(ρ^F_{m*})²`.
- **Classification.** `direct`; `surface-only` for the skipped-steps form (from R35).

### R37. Lemma 6.16 (Freund), (6.69)–(6.73)
- **Book statement.** `R̃_m` = top `m×m` part of `Q_{m−1} H̄_m`, `R_m` = top part of `Q_m H̄_m`,
  `g̃_m`, `g_m` the first `m` components of `Q_{m−1}(β e_1)`, `Q_m(β e_1)`; `ỹ_m = R̃_m^{-1} g̃_m`
  (FOM), `y_m = R_m^{-1} g_m` (GMRES). Then `y_m − (y_{m−1}; 0) = c_m²(ỹ_m − (y_{m−1}; 0))` (6.69),
  where `γ_m = c_m γ̃_m` (6.70) and `ξ_m = ξ̃_m/c_m` (6.71).
- **Lean surface statement.** `theorem lemma_6_16 (hm : m ≤ μ) (hm0 : 0 < m) (hR : IsUnit (R h m)) (hRt : IsUnit (Rtilde h m)) :
  gmresY A b x₀ m - Fin.snoc (gmresY A b x₀ (m-1)) 0 = (c h (m-1))^2 • (ytilde h β m - Fin.snoc (gmresY … (m-1)) 0)`;
  `theorem equation_6_70 : g h β m (Fin.last _) = c h (m-1) * γ h β (m-1)`; `theorem equation_6_71 : R h m (last) (last) = ξ h m / c h (m-1)`.
- **Backbone item.** `Krylov.rotated_succ_eq_of_lt` (`R̃_m` and `R_m` differ only in the last row),
  `Krylov.givensQ_mulVec_firstVec`, `Krylov.gamma_succ`, `Krylov.rotated_succ_self`
  (`r_mm = ρ_{m−1}`), `Krylov.givensC` (D8, D10); §3.5 `Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`.
- **Proof route.** The book's block computation (6.72)–(6.73) (`Matrix.inv` of a block upper
  triangular matrix — `Matrix.fromBlocks` lemmas); (6.70) is `gvec = c̄ γ` (real case), (6.71) is
  `ρ_{m−1} = ξ_m / c_{m−1}`.
- **Classification.** `surface-only` (~80 lines of block bookkeeping from the D8 lemmas).

### R38. (6.74)–(6.75)
- **Book statement.** `x_m^G = s_m² x_{m−1}^G + c_m² x_m^F` (6.74) and `r_m^G = s_m² r_{m−1}^G + c_m² r_m^F` (6.75).
- **Lean surface statement.** `theorem equation_6_74 (hm) (hm0) (hA : IsUnit A) (hH : FOMDefined A b x₀ m) :
  gmresFixed A b x₀ m = (s h (m-1))^2 • gmresFixed … (m-1) + (c h (m-1))^2 • fomFixed … m`;
  `theorem equation_6_75 : rG m = (s h (m-1))^2 • rG (m-1) + (c h (m-1))^2 • rF m`.
- **Backbone item.** §3.6 `Krylov.minRes_eq_combination` (spec level: `x^G_{m+1} = (1 − c²) x^G_m + c² x^F_{m+1}`
  with `c² = ‖r^G_{m+1}‖²/‖r^F_{m+1}‖²`, for injective `A` and `r^F_{m+1} ≠ 0`); R33 identifies `c_m`;
  `Krylov.norm_givensC_sq_add_norm_givensS_sq` gives `s_m² = 1 − c_m²`.
- **Proof route.** The spec-level statement with R33; apply `b − A ·` for (6.75). (Alternatively R37
  and `x = x₀ + V_m y`.)
- **Classification.** `direct`.

### R39. Proposition 6.17 (Brown; stated without proof; P-6.9)
- **Book statement.** If GMRES makes no progress at step `m` (`x_m^G = x_{m−1}^G`) then `H_m` is
  singular and `x_m^F` is undefined. Conversely, if `H_m` is singular (FOM breaks down at step `m`)
  and `A` is nonsingular, then `x_m^G = x_{m−1}^G`.
- **Lean surface statement.** `theorem proposition_6_17 (hm : m ≤ μ) (hm0 : 0 < m) (hA : IsUnit A) (hG : ρG … m ≠ 0) :
  gmresFixed A b x₀ m = gmresFixed A b x₀ (m-1) ↔ ¬ FOMDefined A b x₀ m`.
- **Backbone item.** §3.6 `Krylov.norm_residual_minRes_eq_iff_not_exists_galerkin` (stagnation
  `‖r^G_m‖ = ‖r^G_{m−1}‖ ≠ 0` iff no Galerkin iterate exists at step `m`); §3.5
  `Krylov.existsUnique_isGalerkinIterate_iff_isUnit`, `Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`,
  `Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC`; §3.4
  `Krylov.existsUnique_isMinResIterate_of_injective`, `Krylov.grade_le_of_apply_eq`.
- **Proof route.** `x^G_m = x^G_{m−1} ↔ ‖r^G_m‖ = ‖r^G_{m−1}‖` (⇐ by uniqueness of the minimal-residual
  iterate, `x^G_{m−1}` competing in `x₀ + 𝒦_m`); then the backbone equivalence, and
  `(∃ xF) ↔ FOMDefined` for nonsingular `A` and `m ≤ μ`: `⇐` is `existsUnique_isGalerkinIterate_iff_isUnit`;
  `⇒`: a Galerkin iterate with `c_{m−1} = 0` has zero residual (`norm_residual_eq_div_norm_givensC`),
  so `μ ≤ m` (`grade_le_of_apply_eq`), and at `m = μ` the matrix `H_m` of the injective
  `A|_{𝒦_μ}` (`Arnoldi.hessenbergSq_eq_toMatrix_compression`, `compression.apply_of_invt`) is a unit.
  The hypothesis `ρ^G_m ≠ 0` is implicit in the book's "makes no progress".
- **Classification.** `direct` (with the short bridge above).

### R40. Lemma 6.18 (Weiss), (6.76)–(6.77)
- **Book statement.** In Alg 6.14, if `r_m^O ⟂ r_{m−1}^S` at each step `m ≥ 1`, then
  `1/‖r_m^S‖² = 1/‖r_{m−1}^S‖² + 1/‖r_m^O‖²` (6.76) and `η_m = ‖r_{m−1}^S‖²/(‖r_{m−1}^S‖² + ‖r_m^O‖²)` (6.77).
- **Lean surface statement.** `theorem lemma_6_18 (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - Aop (xO j))
  (horth : ∀ m ≥ 1, inner (rS (m-1)) (rO m) = 0) (m ≥ 1) (h0 : rS (m-1) ≠ 0) (h1 : rO m ≠ 0) :
  1 / ‖rS m‖^2 = 1 / ‖rS (m-1)‖^2 + 1 / ‖rO m‖^2 ∧ mrsEta xO rO m = ‖rS (m-1)‖^2 / (‖rS (m-1)‖^2 + ‖rO m‖^2)`
  where `rS := (mrs xO rO ·).2`.
- **Backbone item.** §3.6 `Krylov.inv_sq_norm_smoothing`, `Krylov.smoothingCoeff`
  (`Numlib/Krylov/Relations.lean`); `mrs_eq` (D11).
- **Proof route.** Backbone (Pythagoras); (6.77) expands `smoothingCoeff` with `⟪r^O, r^S⟫ = 0`. (The
  nonvanishing hypotheses are implicit in the book's divisions.)
- **Classification.** `direct`.

### R41. (6.78)–(6.79)
- **Book statement.** Under the hypotheses of Lemma 6.18, with `ρ_j = ‖r_j^O‖`, `τ_j = ‖r_j^S‖`:
  `r_m^S = (ρ_m²/(ρ_m²+τ_{m−1}²)) r_{m−1}^S + (τ_{m−1}²/(ρ_m²+τ_{m−1}²)) r_m^O` (6.78),
  `1/τ_j² = ∑_{i=0}^j 1/ρ_i²`, and `r_m^S = (∑_{j=0}^m r_j^O/ρ_j²)/(∑_{j=0}^m 1/ρ_j²)` (6.79) (index
  ranges as in §6).
- **Lean surface statement.** `theorem equation_6_78 …`, `theorem inv_tau_sq_eq_sum …`,
  `theorem equation_6_79 … : rS m = (∑ j ∈ range (m+1), 1/ρ j^2)⁻¹ • ∑ j ∈ range (m+1), (1/ρ j^2 : ℝ) • rO j`.
- **Backbone item.** §3.6 `Krylov.residual_mrs_eq` ((6.79) for a Galerkin sequence `xO`, injective
  `A`), `Krylov.inv_sq_norm_smoothing`.
- **Proof route.** (6.78) from (6.77); the `τ` sum by induction on `inv_sq_norm_smoothing`; (6.79)
  for FOM is the backbone theorem through `mrs_eq`, and under the book's bare orthogonality
  hypothesis it is the same induction.
- **Classification.** `direct` for the FOM sequence ((6.79) via `residual_mrs_eq`); `surface-only`
  (short inductions) for (6.78), the `τ` sum and the general-orthogonality form.

### R42. §6.5.8 — minimal residual smoothing of FOM gives GMRES (and P-6.26)
- **Book statement.** If the original residuals are mutually orthogonal (as for FOM), Lemma 6.18
  applies at every step, the smoothed residual norms satisfy (6.67), hence coincide with GMRES's, and
  since GMRES minimizes over the same subspace the smoothed iterates are the GMRES iterates. P-6.26:
  alternatively, the vectors `r_j^O − r_{j−1}^S = −A(x_j^O − x_{j−1}^S)` are mutually orthogonal, and
  Lemma 6.21 shows the MRS iterates coincide with ORTHOMIN/GMRES.
- **Lean surface statement.** `theorem mrs_isMinResIterate (hA : IsUnit A) (xO : ℕ → 𝔼)
  (hO : ∀ m, Krylov.IsGalerkinIterate Aop b x₀ m (xO m)) (m) :
  Krylov.IsMinResIterate Aop b x₀ m ((mrs xO (fun j => b - Aop (xO j)) m).1)`; corollary
  `mrs_fom_eq_gmres (hA) (hH : ∀ i ≤ m, FOMDefined …) (hm) : (mrs (fomFixed A b x₀) _ m).1 = gmresFixed A b x₀ m`;
  `problem_6_26 : ∀ i ≠ j, inner (Aop (pS i)) (Aop (pS j)) = 0` with `pS j := xO j - xS (j-1)`.
- **Backbone item.** §3.6 `Krylov.IsGalerkinIterate.mrs_isMinResIterate` (injective `A`),
  `Krylov.mrs` (`Numlib/Krylov/Relations.lean`); §3.8 `Krylov.isMinResIterate_of_orthogonal_directions`
  for the P-6.26 route; `Krylov.existsUnique_isMinResIterate_of_injective` for the corollary.
- **Proof route.** `mrs_eq` (D11), then the backbone theorem; the corollary by uniqueness.
- **Classification.** `direct` (after `mrs_eq`).

### R43. §6.5.8 — QMRS identities
- **Book statement.** With `η_m = τ_{m−1}²/(τ_{m−1}² + ρ_m²)` and `1/τ_m² = 1/τ_{m−1}² + 1/ρ_m²` (no
  orthogonality assumed), (6.78) holds with `‖r_j^S‖²` replaced by `τ_j²`, and (6.79) holds.
- **Lean surface statement.** `theorem qmrs_eq_6_78 …`,
  `theorem qmrs_eq_6_79 (xO rO) (m) : (qmrs xO rO m).2.1 = (∑ …)⁻¹ • ∑ j ∈ range (m+1), (1/ρ j^2) • rO j`.
- **Backbone item.** none.
- **Proof route.** Same induction as R41 (purely algebraic).
- **Classification.** `surface-only`. (The further claim "QMRS applied to IOM/DIOM yields
  QGMRES/DQGMRES" is left out, §5.)

### R44. Theorem 6.19, (6.82)–(6.83)
- **Book statement.** Arnoldi applied to a real symmetric `A`: `h_ij = 0` for `1 ≤ i < j − 1` (6.82)
  and `h_{j,j+1} = h_{j+1,j}` (6.83); `H_m` is symmetric tridiagonal.
- **Lean surface statement.** `theorem theorem_6_19 (hA : A.IsSymm) (hv) :
  (∀ i j, i + 1 < j → h i j = 0) ∧ (∀ j, h j (j+1) = h (j+1) j) ∧ (H A v₁ m).IsTridiagonal ∧ (H A v₁ m).IsSymm`.
- **Backbone item.** §3.3 `Arnoldi.coeff_eq_zero_of_isSymmetric`, `Arnoldi.coeff_conj_of_isSymmetric`,
  `Lanczos.hessenbergSq_eq_map_tridiag`, `Lanczos.tridiag_isTridiagonal`, `Lanczos.tridiag_isSymm`
  (`Numlib/Krylov/Lanczos.lean`); §2.1.10 `Matrix.IsTridiagonal` (`Numlib/LinearAlgebra/Matrix/Hessenberg.lean`);
  Mathlib `Matrix.isSymmetric_toEuclideanLin_iff` for `A.IsSymm → (op A).IsSymmetric` over `ℝ`.
- **Proof route.** Backbone.
- **Classification.** `direct`.

### R45. §6.6.1 — Algorithm 6.15 is the MGS Arnoldi algorithm for symmetric `A`; `T_m = H_m`
- **Book statement.** "This leads to the following form of the Modified Gram–Schmidt variant of
  Arnoldi's method" — Alg 6.15 produces the same `v_j`, with `α_j = h_jj`, `β_{j+1} = h_{j+1,j}` and
  `T_m = H_m` (6.84).
- **Lean surface statement.** `theorem lanczosV_eq (hA : A.IsSymm) (hv) : lanczosV A v₁ j = arnoldiCGS A v₁ j`,
  `lanczosAlpha_eq : lanczosAlpha A v₁ j = h j j`, `lanczosBeta_eq : lanczosBeta A v₁ (j+1) = h (j+1) j`,
  `T_eq_H : T A v₁ m = H A v₁ m`.
- **Backbone item.** §3.3 `Lanczos.apply_vec`, `Lanczos.apply_vec_zero`, `Lanczos.w_succ_eq`,
  `Lanczos.alpha`, `Lanczos.beta`, `Lanczos.coe_alpha`, `Lanczos.coe_beta`, `Lanczos.tridiag`,
  `Lanczos.hessenbergSq_eq_map_tridiag`, `Lanczos.hessenberg_eq_map_tridiagExt`.
- **Proof route.** D12.
- **Classification.** `needs-equivalence` (this is the equivalence lemma).

### R46. §6.6.2 — the inner product (6.85) and orthogonal polynomials
- **Book statement.** If the grade of `v_1` is `≥ m`: (a) `q ↦ q(A) v_1` is an isomorphism
  `P_{m−1} → 𝒦_m`; (b) `⟨p, q⟩_{v_1} = (p(A) v_1, q(A) v_1)` (6.85) is a nondegenerate bilinear form
  on `P_{m−1}` (for `m ≤ μ`); (c) `v_i = q_{i−1}(A) v_1` and the `q_i` are orthogonal for (6.85);
  (d) [cited] the characteristic polynomial of `T_m` minimizes `‖·‖_{v_1}` over monic polynomials of
  degree `m`; (e) Lanczos computes `p_{T_m}(A) v_1` (up to the scaling `β_2 ⋯ β_{m+1}`).
- **Lean surface statement.** (a) `theorem polyEval_bijective (hm : m ≤ μ) : Function.Bijective
  ((Krylov.polyEval Aop v₁).domRestrict (degreeLT ℝ m) codRestricted to krylov)`;
  (b) `theorem polyInner_nondegenerate (hm) : ∀ p ∈ degreeLT ℝ m, (∀ q ∈ degreeLT ℝ m, polyInner A v₁ p q = 0) → p = 0`;
  (c) `theorem lanczosPoly_spec (i < μ) : (lanczosPoly A v₁ i).degree = i ∧ aeval Aop (lanczosPoly A v₁ i) v₁ = v i`
  and `polyInner … (lanczosPoly i) (lanczosPoly j) = 0` for `i ≠ j`;
  (d) `theorem charpoly_T_isMinOn (hm) : IsMinOn (fun p => ‖aeval Aop p v₁‖) {p | p.Monic ∧ p.natDegree = m} (T A v₁ m).charpoly`;
  (e) `theorem lanczos_charpoly : aeval Aop (T A v₁ m).charpoly v₁ = (∏ j ∈ range m, lanczosBeta A v₁ (j+1)) • v m`.
- **Backbone item.** (a)–(c): §3.1 `Krylov.subspace_eq_map_degreeLT`, `Krylov.linearIndependent_of_le_grade`
  + §3.2 `Arnoldi.vec_mem_subspace`, `Arnoldi.inner_vec_eq_zero`; (d): `Arnoldi.charpoly_compression_isMinOn`
  (§4.2, deferred); (e): `Krylov/OrthogonalPolynomials.lean` (§3.12, deferred).
- **Proof route.** (a)–(c) from the listed lemmas; (d)–(e) with the deferred items.
- **Classification.** (a)–(c) `direct`; (d), (e) `deferred` (§4, Ritz-value and orthogonal-polynomial
  items; the book cites (d) without proof).

### R47. (6.86)–(6.87) — the Lanczos method for linear systems (Alg 6.16) and its residual
- **Book statement.** For symmetric `A`, the orthogonal projection method onto `𝒦_m` gives
  `x_m = x_0 + V_m y_m`, `y_m = T_m^{-1}(β e_1)` (6.86); `b − A x_m = −β_{m+1}(e_mᵀ y_m) v_{m+1}` (6.87).
- **Lean surface statement.** `theorem lanczosMethod_eq_fom (hA : A.IsSymm) : lanczosMethod A b x₀ m = fom A b x₀ m`;
  `theorem lanczosMethod_isGalerkinIterate (hA) (hT : IsUnit (T …)) (hm) : Krylov.IsGalerkinIterate Aop b x₀ m (lanczosMethod A b x₀ m)`;
  `theorem equation_6_87 … : b - Aop (lanczosMethod …) = -(lanczosBeta A v₁ m * y_m (Fin.last _)) • lanczosV A v₁ m`.
- **Backbone item.** R11, R12, R45; §3.5 `Krylov.residual_galerkin_eq` with §3.3 `Lanczos.coe_beta`
  (`h_{m+1,m} = β_{m+1}`).
- **Proof route.** Rewrite with `T_eq_H`, `lanczosV_eq`, then R11/R12.
- **Classification.** `direct` (given R45).

### R48. §6.7.1 — D-Lanczos (Alg 6.17) is mathematically equivalent to Alg 6.16; (6.88)–(6.89)
- **Book statement.** With `T_m = L_m U_m` (`L_m` unit lower bidiagonal with `λ_m = β_m/η_{m−1}`, `U_m`
  upper bidiagonal with diagonal `η_m = α_m − λ_m β_m` and superdiagonal `β_{m+1}`), `P_m = V_m U_m^{-1}`,
  `z_m = L_m^{-1} β e_1`: `p_m = η_m^{-1}(v_m − β_m p_{m−1})`, `ζ_m = −λ_m ζ_{m−1}`, `x_m = x_{m−1} + ζ_m p_m`;
  the two algorithms deliver the same `x_m` when both are executable.
- **Lean surface statement.** `theorem dLanczos_eq_diom2 (hA : A.IsSymm) : (dLanczos A b x₀ m).x = (diom A b x₀ 2 m).x`
  (the book's remark "CG is a variation of DIOM(2)");
  `theorem dLanczos_x_eq (hA) (hη : ∀ j ≤ m, (dLanczos A b x₀ j).η ≠ 0) : (dLanczos A b x₀ m).x = lanczosMethod A b x₀ m`;
  `theorem tridiag_LU (hη) : T A v₁ m = L * U` with the stated shapes.
- **Backbone item.** none (§3.7: "D-Lanczos / `LDLᵀ` derivation is surface").
- **Proof route.** R14 specialized to the tridiagonal band (`k = 2`).
- **Classification.** `surface-only`.

### R49. Proposition 6.20
- **Book statement.** Let `r_m` be the residuals of Alg 6.16/6.17 and `p_m` the auxiliary vectors of
  Alg 6.17. (1) `r_m = σ_m v_{m+1}` for a scalar `σ_m`; hence the residuals are mutually orthogonal.
  (2) The `p_i` are `A`-conjugate: `(A p_i, p_j) = 0` for `i ≠ j`.
- **Lean surface statement.** `theorem proposition_6_20_1 (hA : A.IsSymm) (hT) (hm) :
  ∃ σ : ℝ, b - Aop (lanczosMethod A b x₀ m) = σ • lanczosV A v₁ m` and `inner (rL i) (rL j) = 0` for
  `i ≠ j`; `theorem proposition_6_20_2 (hA) (hη) (hij : i ≠ j) : inner (Aop (pDL i)) (pDL j) = 0`.
- **Backbone item.** §3.4 `Krylov.IsGalerkinIterate.residual_mem_span`,
  `Krylov.IsGalerkinIterate.inner_residual_eq_zero` (`Numlib/Krylov/Iterate.lean`) for (1); for (2)
  §3.7 `CG.inner_apply_direction_eq_zero` via the CG ≡ D-Lanczos equivalence (R50), or the book's
  `P_mᵀ A P_m = U_m^{-T} L_m` argument.
- **Proof route.** (1) backbone; (2) either route; the book's own proof is 6 lines of matrix algebra
  once `T_m = L_m U_m` (R48) is available.
- **Classification.** (1) `direct`; (2) `needs-equivalence` (through R50) or `surface-only` (book's
  proof).

### R50. §6.7.1 — CG (Alg 6.18) from the orthogonality/conjugacy conditions: (6.90)–(6.94); CG ≡ D-Lanczos
- **Book statement.** Imposing `x_{j+1} = x_j + α_j p_j` (6.90), `r_{j+1} = r_j − α_j A p_j` (6.91),
  orthogonal residuals and `p_{j+1} = r_{j+1} + β_j p_j` (6.93) with `A`-conjugate `p`'s forces
  `α_j = (r_j,r_j)/(A p_j, r_j) = (r_j,r_j)/(A p_j,p_j)` (6.92),
  `β_j = −(r_{j+1}, A p_j)/(p_j, A p_j) = (r_{j+1},r_{j+1})/(r_j,r_j)`, using
  `A p_j = −(r_{j+1} − r_j)/α_j` (6.94). The `p_j` of Alg 6.18 are multiples of those of Alg 6.17.
- **Lean surface statement.** `theorem cg_eq_CG (hA : A.IsSymm) : cg A b x₀ j = ((CG.iterate Aop b x₀ j).x, .r, .p)`;
  `theorem cg_residual : (cg A b x₀ j).2.1 = b - Aop (cg A b x₀ j).1`;
  `theorem cg_alpha_eq (hA : A.PosDef) : cgAlpha A b x₀ j = inner r r / inner (Aop p) r` (6.92) and
  `cg_beta_eq : cgBeta … j = -(inner (Aop p_j) r_{j+1}) / inner (Aop p_j) p_j`;
  `theorem cg_x_eq_dLanczos (hA : A.PosDef) : (cg A b x₀ j).1 = (dLanczos A b x₀ j).x`;
  `theorem cg_p_smul (hA) (hr : r_j ≠ 0) : ∃ c ≠ 0, (cg A b x₀ j).2.2 = c • (dLanczos A b x₀ (j+1)).p`.
- **Backbone item.** §3.7 `CG.iterate`, `CG.residual_eq`, `CG.isGalerkinIterate`,
  `CG.inner_residual_eq_zero`, `CG.inner_apply_direction_eq_zero`, `CG.inner_residual_direction_eq`
  (`Numlib/Krylov/CG.lean`); §3.4 `Krylov.existsUnique_isGalerkinIterate_of_isCoercive`; §2.1.4
  `Matrix.posDef_iff_isSymmetricCoercive` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`).
- **Proof route.** `cg_eq_CG` is definitional; the coefficient identities follow from the backbone
  invariants; `cg_x_eq_dLanczos` from uniqueness of the Galerkin iterate (both R47/R48 and
  `CG.isGalerkinIterate` produce it); `cg_p_smul` from `x_{j+1} − x_j = α_j p_j = ζ_{j+1} p^{DL}_{j+1}`
  with `α_j ≠ 0`.
- **Classification.** `direct` (`cg_eq_CG`, invariants); `needs-equivalence` (D-Lanczos link).

### R51. §6.7.2 — three-term recurrence variant (Alg 6.19), (6.95)–(6.98); (6.97) from (6.96) (P-6.17)
- **Book statement.** The CG residual polynomials satisfy
  `r_{m+1}(t) = ρ_m(r_m(t) − γ_m t r_m(t)) + (1 − ρ_m) r_{m−1}(t)` (6.95), i.e.
  `r_{m+1} = ρ_m(r_m − γ_m A r_m) + (1 − ρ_m) r_{m−1}` (6.96) with `γ_m = (r_m,r_m)/(A r_m,r_m)` and
  `ρ_m` given by (6.97); the iterates satisfy `x_{m+1} = ρ_m(x_m + γ_m r_m) + (1 − ρ_m) x_{m−1}` (6.98),
  started with `x_{−1} = 0`, `ρ_0 = 1`. Alg 6.19 computes the CG iterates.
- **Lean surface statement.** `theorem cg3_eq_cg (hA : A.PosDef) (hr : ∀ i ≤ j, (cg A b x₀ i).2.1 ≠ 0) :
  (cg3 A b x₀ j).x = (cg A b x₀ j).1 ∧ (cg3 A b x₀ j).r = (cg A b x₀ j).2.1`;
  `theorem equation_6_96 (hA) (hr) : r_{m+1} = ρ_m • (r_m - γ_m • Aop r_m) + (1 - ρ_m) • r_{m-1}` and
  `theorem equation_6_98 (hA) (hr) : x_{m+1} = ρ_m • (x_m + γ_m • r_m) + (1 - ρ_m) • x_{m-1}` for the CG
  iterates with `γ_m, ρ_m` as in the book;
  `theorem equation_6_97_of_6_96 : (6.96) ∧ orthogonality ⟹ ρ_m = (1 - (γ_m/γ_{m-1}) * (‖r_m‖²/‖r_{m-1}‖²) / ρ_{m-1})⁻¹` (P-6.17).
- **Backbone item.** §3.7 `CG.gamma`, `CG.rho` (the book's coefficients, `ρ_0 = 1`),
  `CG.residual_succ_eq_three_term` (6.96), `CG.iterate_succ_eq_three_term` (6.98), valid while
  `r_j ≠ 0` for `j ≤ m` (`Numlib/Krylov/CG.lean`); `CG.inner_residual_eq_zero` for P-6.17.
- **Proof route.** (6.96)/(6.98) are the backbone theorems after `cg_eq_CG`; `cg3_eq_cg` by induction
  on `j` (D14); P-6.17: take the inner product of (6.96) with `r_{m−1}` and use orthogonality.
- **Classification.** `direct` ((6.96)–(6.98)); `needs-equivalence` (`cg3_eq_cg`); `surface-only`
  (P-6.17, short).

### R52. §6.7.3 — eigenvalue estimates: (6.99)–(6.103)
- **Book statement.** With `T_m = tridiag[η_j, δ_j, η_{j+1}]` the Lanczos matrix and `α_j, β_j` the CG
  coefficients: `r_j = scalar × v_{j+1}` (6.99), `r_j = p_j − β_{j−1} p_{j−1}` (6.100),
  `δ_{j+1} = 1/α_j + β_{j−1}/α_{j−1}` for `j > 0` (6.101), `δ_1 = 1/α_0` (6.102),
  `η_{j+1} = √β_{j−1}/α_{j−1}` (6.103).
- **Lean surface statement.** `theorem equation_6_99 (hA : A.PosDef) (hr) : ∃ σ : ℝ, (cg A b x₀ j).2.1 = σ • lanczosV A v₁ j`;
  `theorem equation_6_100 (hj : 0 < j) : r_j = p_j - β_{j-1} • p_{j-1}`;
  `theorem equation_6_102 : lanczosAlpha A v₁ 0 = 1 / cgAlpha … 0` and
  `theorem equation_6_101 (hj : 0 < j) : lanczosAlpha A v₁ j = 1 / cgAlpha … j + cgBeta … (j-1) / cgAlpha … (j-1)`;
  `theorem equation_6_103 (hj : 0 < j) : lanczosBeta A v₁ (j+1)… = Real.sqrt (cgBeta … (j-1)) / cgAlpha … (j-1)`
  (indices per D12/D14), and `T A v₁ m = tridiag of these`.
- **Backbone item.** §3.7 `CG.arnoldi_vec_eq` (6.99: `v_k = (−1)^k r_k/‖r_k‖`), `CG.step_r`,
  `CG.inner_residual_direction_eq`, `CG.inner_apply_direction_eq_zero`, `CG.inner_residual_eq_zero`;
  §3.3 `Lanczos.alpha`, `Lanczos.beta`, `Lanczos.coe_alpha`, `Lanczos.coe_beta`; R45.
- **Proof route.** (6.99) backbone; (6.100) unfolds `CG.step`; (6.101)–(6.103):
  `α^L_j = ⟪v_j, A v_j⟫ = ⟪r_j, A r_j⟫/‖r_j‖²` with `A r_j = A p_j − β_{j−1} A p_{j−1}`,
  `A p_j = (r_j − r_{j+1})/α_j` (6.94) and the orthogonality invariants; `β^L_{j+1} = ‖w_j‖` from
  `⟪v_{j+1}, A v_j⟫` by the same substitutions (the signs `(−1)^k` of `arnoldi_vec_eq` cancel).
- **Classification.** `surface-only` for (6.101)–(6.103) (~40 lines from the CG invariants);
  `direct` for (6.99)–(6.100).

### R53. §6.8 — Conjugate Residual invariants; CR = GMRES for Hermitian positive definite `A`
- **Book statement.** For Hermitian `A`, CR (Alg 6.20) produces `A`-orthogonal (conjugate) residuals
  `(r_i, A r_j) = 0` (`i ≠ j`) and orthogonal `A p_i`'s `(A p_i, A p_j) = 0` (`i ≠ j`); it is the GMRES
  analogue of CG for Hermitian `A` ("derived from GMRES for the particular case where `A` is
  Hermitian"; §6.10: "the full GMRES algorithm gives rise to the Conjugate Residual algorithm").
- **Lean surface statement.** (over `ℝ`, symmetric `A`) `theorem cr_eq_CR : cr A b x₀ j = (CR.iterate Aop b x₀ j).(x, r, p, q)`;
  `theorem cr_Ap_orth (hA : A.PosDef) (hij : i ≠ j) : inner (Aop (crP i)) (Aop (crP j)) = 0`;
  `theorem cr_res_conj (hA) (hij) : inner (crR i) (Aop (crR j)) = 0`;
  `theorem cr_isMinResIterate (hA : A.PosDef) : Krylov.IsMinResIterate Aop b x₀ j (crX j)`;
  `theorem cr_isMinResIterate_of_no_breakdown (hA : A.IsSymm) (h1 : ∀ i < j, inner (crR i) (Aop (crR i)) ≠ 0)
  (h2 : ∀ i < j, Aop (crP i) ≠ 0) : Krylov.IsMinResIterate Aop b x₀ j (crX j)` (the book's Hermitian
  generality); `theorem cr_eq_gmres (hA : A.PosDef) (hj : j ≤ μ) : crX j = gmresFixed A b x₀ j`.
- **Backbone item.** §3.8 `CR.iterate`, `CR.isMinResIterate` (symmetric coercive),
  `CR.isMinResIterate_of_no_breakdown` (symmetric, no-breakdown hypotheses),
  `CR.inner_apply_direction_eq_zero`, `CR.inner_residual_apply_direction_eq_zero`,
  `CR.inner_residual_apply_residual_eq_zero` (`Numlib/Krylov/CR.lean`); §3.4
  `Krylov.existsUnique_isMinResIterate_of_injective`.
- **Proof route.** `cr_eq_CR` definitional; the invariants are the backbone lemmas; `cr_eq_gmres` by
  uniqueness of the minimal-residual iterate (R18).
- **Classification.** `direct`.

### R54. Lemma 6.21, (6.104)–(6.105)
- **Book statement.** Let `p_0, …, p_{m−1}` be such that each `{p_0, …, p_{j−1}}` (`j ≤ m`) is a basis
  of `𝒦_j(A, r_0)` and `(A p_i, A p_k) = 0` for `i ≠ k`. Then the minimal-residual approximation in
  `x_0 + 𝒦_m(A, r_0)` is `x_m = x_0 + ∑_{i<m} ((r_0, A p_i)/(A p_i, A p_i)) p_i` (6.104), and
  `x_m = x_{m−1} + ((r_{m−1}, A p_{m−1})/(A p_{m−1}, A p_{m−1})) p_{m−1}` (6.105).
- **Lean surface statement.** `theorem lemma_6_21 (p : ℕ → 𝔼)
  (horth : ∀ i < m, ∀ k < m, i ≠ k → inner (Aop (p i)) (Aop (p k)) = 0) (hne : ∀ i < m, Aop (p i) ≠ 0)
  (hspan : Submodule.span ℝ (Set.range fun i : Fin m => p i) = krylov A r₀ m) (x : ℕ → 𝔼) (hx0 : x 0 = x₀)
  (hstep : ∀ j, x (j+1) = x j + (inner (Aop (p j)) (b - Aop (x j)) / inner (Aop (p j)) (Aop (p j))) • p j) :
  Krylov.IsMinResIterate Aop b x₀ m (x m) ∧ x m = x₀ + ∑ i : Fin m, (inner (Aop (p i)) r₀ / inner (Aop (p i)) (Aop (p i))) • p i`.
  (The nonvanishing of `(A p_i, A p_i)` is implicit in the book's divisions; it is automatic for
  nonsingular `A`. The book's nested-basis hypothesis for every `j ≤ m` follows from `hspan` at `m`
  together with the recurrence, which only uses `p_0..p_{j−1}` up to step `j`.)
- **Backbone item.** §3.8 `Krylov.isMinResIterate_of_orthogonal_directions` (`Numlib/Krylov/CR.lean`;
  exactly the hypotheses above, no symmetry assumption).
- **Proof route.** (6.105) is the backbone theorem; (6.104) by unfolding the recurrence and
  `(r_j, A p_j) = (r_0, A p_j)` (`r_j − r_0 ∈ span{A p_i : i < j} ⟂ A p_j`); the book's own proof goes
  through Prop 5.3 = §2.4.1 `IsMinRes.iff_isPetrovGalerkin`.
- **Classification.** `direct` ((6.105)); the closed form (6.104) is a short surface computation.

### R55. §6.9 — GCR and ORTHODIR are mathematically equivalent to full GMRES; ORTHOMIN(k) = GCR for `k ≥ m`
- **Book statement.** Lemma 6.21 "opens up many different ways to obtain algorithms that are
  mathematically equivalent to the full GMRES": GCR (Alg 6.21), and ORTHODIR (6.107) (both build
  `AᵀA`-orthogonal bases of the Krylov subspaces and update by (6.105)). ORTHOMIN(k) truncates lines
  6–7; GCR(m) restarts.
- **Lean surface statement.** `theorem gcr_isMinResIterate (h : ∀ i < m, Aop (gcrP i) ≠ 0) (hm : m ≤ μ) :
  Krylov.IsMinResIterate Aop b x₀ m (gcr A b x₀ m).x` and `gcr_eq_gmres … : (gcr A b x₀ m).x = gmresFixed A b x₀ m`;
  `theorem orthodir_isMinResIterate (h : ∀ i < m, Aop (odP i) ≠ 0) (hm) : …`;
  `theorem orthomin_eq_gcr (hk : m ≤ k) : orthomin A b x₀ k m = gcr A b x₀ m`;
  `theorem gcr_Ap_orth (h) : ∀ i j < m, i ≠ j → inner (Aop (gcrP i)) (Aop (gcrP j)) = 0`.
- **Backbone item.** R54 (§3.8 `Krylov.isMinResIterate_of_orthogonal_directions`); no backbone
  recurrence for GCR/ORTHODIR (§1.2).
- **Proof route.** Induction: `p_j ∈ 𝒦_{j+1}`, `AᵀA`-orthogonality by construction of `β_ij`, nonzero
  `A p_i` ⇒ linear independence ⇒ basis of `𝒦_{j+1}` for `j + 1 ≤ μ`; then R54 (`α_j` of Alg 6.21 is
  exactly the coefficient in (6.105)).
- **Classification.** `needs-equivalence` (surface induction + R54).

### R56. Proposition 6.22
- **Book statement.** If `Aᵀ v ∈ 𝒦_s(A, v)` for every `v`, then DIOM(s) is mathematically equivalent
  to FOM (because then `h_ij = (v_j, Aᵀ v_i) = 0` for `i < j − s + 1` (6.108)).
- **Lean surface statement.** `theorem proposition_6_22 (hs : ∀ v : 𝔼, Aop.adjoint v ∈ krylov A v s) :
  (∀ v₁ i j, i + s ≤ j → arnoldiCoeff A v₁ i j = 0) ∧ ∀ b x₀ m, iop A v₁ s = arnoldiMGS A v₁ ∧
  iom A b x₀ s m = fom A b x₀ m ∧ (diom A b x₀ s m).x = fom A b x₀ m` (the last under the DIOM
  no-breakdown hypothesis of R14).
- **Backbone item.** §3.2 `Arnoldi.coeff_eq_zero_of_adjoint_mem` (`Numlib/Krylov/Arnoldi.lean`;
  hypotheses `hB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫` and `hs : ∀ v, B v ∈ 𝒦_s(A, v)`, conclusion
  `coeff A b i j = 0` for `i + s ≤ j`; its `s = 2` case is Lanczos tridiagonality), with `B := op Aᵀ`
  through `Matrix.toEuclideanLin_conjTranspose` and `LinearMap.adjoint_inner_right`.
- **Proof route.** (6.108) is the backbone lemma; then the IOP loop subtracts exactly the nonzero
  terms, so IOP = MGS Arnoldi (D6 (vii) generalized to the band condition).
- **Classification.** `direct` ((6.108)); `needs-equivalence` (the algorithmic consequences, D6).

### R57. §6.10 text — `Aᵀ = q(A)` implies normal; normal implies `A^H = q(A)` for some `q` of degree `≤ n − 1`
- **Book statement.** If `Aᵀ = q(A)` then `A` is normal (since `A q(A) = q(A) A`); conversely, if `A`
  is normal (`A = Q Λ Q^H`), choosing `q` with `q(λ_j) = λ̄_j` gives `q(A) = A^H` (degree `≤ n − 1`).
- **Lean surface statement.** Over `ℂ`: `theorem isStarNormal_of_exists_aeval (h : ∃ q : ℂ[X], aeval A q = Aᴴ) : IsStarNormal A`;
  `theorem exists_aeval_eq_conjTranspose (hA : IsStarNormal A) : ∃ q : ℂ[X], q.natDegree ≤ n - 1 ∧ aeval A q = Aᴴ`.
- **Backbone item.** none for the first; the second is
  `Matrix.IsStarNormal.exists_aeval_eq_conjTranspose` in `Eigen/Normal.lean` (§4 item 2, written).
  Mathlib supplies `IsStarNormal` and `Lagrange.interpolate` but has no Schur triangulation and no
  unitary diagonalization of normal matrices (only the Hermitian
  `Matrix.IsHermitian.spectral_theorem`); the backbone item needs neither.
- **Proof route.** First: `Aᴴ A = q(A) A = A q(A) = A Aᴴ`. Second: a normal operator has no
  generalized eigenvectors (`ker N² = ker N`), so over `ℂ` its eigenspaces span, and they are the
  eigenspaces of `Aᴴ` at the conjugate eigenvalues; Lagrange interpolation of `z ↦ conj z` at the
  distinct eigenvalues then gives `q(A) = Aᴴ`, whose degree is lowered below `n` by reduction
  modulo the characteristic polynomial.
- **Classification.** both `direct` (the first on Mathlib, the second on the backbone's
  normal-matrix theory).

### R58. Lemma 6.23 (Faber–Manteuffel)
- **Book statement.** A nonsingular `A` satisfies `A^H v ∈ 𝒦_s(A, v)` for every `v` iff `A` is normal
  and `ν(A) ≤ s − 1` (`ν(A)` = least degree of `q` with `A^H = q(A)`).
- **Lean surface statement.** `theorem lemma_6_23 (hs : 0 < s) :
  (∀ v : EuclideanSpace ℂ (Fin n), op Aᴴ v ∈ krylov A v s) ↔ IsStarNormal A ∧ ν A ≤ s - 1`.
  The book's `IsUnit A` is absent (the proof does not use it) and `0 < s` is present (the printed
  statement is false without it); both are recorded in §6.
- **Backbone item.** `Eigen/Normal.lean` (§4 item 2): `isStarNormal_of_adjoint_apply_eq_smul`
  (Saad Lemma 1.15, shared eigenvectors ⇒ normal), `IsStarNormal.eigenspace_adjoint`,
  `IsStarNormal.inner_eq_zero_of_ne`, `IsStarNormal.aeval_eq_adjoint_of_eval_eq`,
  `Matrix.isStarNormal_toEuclideanLin_iff` and `Matrix.aeval_eq_conjTranspose_iff`; also R57.
  `Krylov.linearIndependent_of_le_grade` is not needed — see the proof route.
- **Proof route.** Not the book's. `Aᴴ v ∈ 𝒦_s(A, v)` at an eigenvector `v` of `A` forces
  `Aᴴ v ∈ span{v}`, so shared eigenvectors ⇒ normal (Lemma 1.15). Then, instead of the book's
  maximal vector `w` of grade `μ = deg minpoly A`, take `w = ∑ x_i` with one nonzero `x_i` from each
  eigenspace: the `x_i` are pairwise orthogonal, so the coordinates of `Aᴴ w = ∑ conj(λ_i) x_i` are
  unique, and a polynomial `q` of degree `≤ s − 1` with `Aᴴ w = q(A) w` must satisfy
  `q(λ_i) = conj λ_i`; hence `q(A) = Aᴴ` on every eigenspace, hence everywhere, hence
  `ν(A) ≤ s − 1`. This needs neither a maximal vector nor `deg minpoly` = number of distinct
  eigenvalues.
- **Classification.** `direct` (on the backbone's normal-matrix theory).

### R59. Theorem 6.24 (Faber–Manteuffel; stated without proof)
- **Book statement.** `A ∈ CG(s)` iff the minimal polynomial of `A` has degree `≤ s`, or `A` is normal
  and `ν(A) ≤ s − 1`.
- **Lean surface statement.** `theorem theorem_6_24 (A : Matrix (Fin n) (Fin n) ℂ) :
  IsCGs A s ↔ (minpoly ℂ A).natDegree ≤ s ∨ (IsStarNormal A ∧ ν A ≤ s - 1)`.
- **Backbone item.** none missing: `Eigen/Normal.lean` (§4 item 2) is written, and R58 is proved on
  it. What is missing is the proof itself.
- **Proof route.** Not in the book (reference [121]; a short proof is Liesen–Strakoš 2008 /
  Faber–Manteuffel 1984). A research-level formalization; the surface carries only the module doc
  comment's mention (§5).
- **Classification.** `out-of-scope` (§5, no printed proof; research-level).

### R60. (6.109)–(6.112) — real Chebyshev polynomials
- **Book statement.** `C_k(t) = cos(k cos⁻¹ t)` on `[−1, 1]` (6.109); `C_{k+1} = 2t C_k − C_{k−1}`,
  `C_0 = 1`, `C_1 = t`; `C_k(t) = cosh(k cosh⁻¹ t)` for `|t| ≥ 1` (6.110);
  `C_k(t) = ½[(t + √(t²−1))^k + (t + √(t²−1))^{−k}]` for `|t| ≥ 1` (6.111); `C_k(t) ≳ ½(t + √(t²−1))^k`
  (6.112) (we state the inequality `≥`).
- **Lean surface statement.** `theorem equation_6_109 (ht : t ∈ Icc (-1) 1) : (C k).eval t = Real.cos (k * Real.arccos t)`;
  `theorem C_rec : C (k+2) = 2 * X * C (k+1) - C k`;
  `theorem equation_6_110 (ht : 1 ≤ t) : (C k).eval t = Real.cosh (k * Real.arcosh t)`;
  `theorem equation_6_111 (ht : 1 ≤ t) : (C k).eval t = ((t + √(t^2-1))^k + (t + √(t^2-1))⁻¹^k)/2`;
  `theorem equation_6_112 (ht : 1 ≤ t) : (t + √(t^2-1))^k / 2 ≤ (C k).eval t`.
- **Backbone item.** Mathlib `Polynomial.Chebyshev.T_real_cos`, `T_real_cosh`, `T_add_two`; §2.1.9
  `Polynomial.Chebyshev.eval_T_eq_half_add_pow` (with `(t − √(t²−1))^k`; equal since
  `(t+√)(t−√) = 1`), `half_pow_le_eval_T`.
- **Proof route.** Mathlib/backbone; (6.110) from `T_real_cosh` with `cosh (arcosh t) = t`.
- **Classification.** `direct`.

### R61. Theorem 6.25 (Chebyshev min–max) and its corollary formula
- **Book statement.** For a (nondegenerate) interval `[α, β]` and real `γ ∉ [α, β]`,
  `min_{p ∈ P_k, p(γ)=1} max_{t ∈ [α,β]} |p(t)|` is attained by
  `Ĉ_k(t) = C_k(1 + 2(t−β)/(β−α)) / C_k(1 + 2(γ−β)/(β−α))` (6.113); the minimum equals
  `1/|C_k(1 + 2(γ−β)/(β−α))| = 1/|C_k(2(γ−μ)/(β−α))|`, `μ = (α+β)/2`.
- **Lean surface statement.** `theorem theorem_6_25 (k) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
  IsLeast {M | ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧ M = sSup ((fun t => |p.eval t|) '' Set.Icc α β)}
  (sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β))` together with
  `theorem theorem_6_25_value : sSup (… Chat …) = 1 / |(C k).eval (1 + 2 * (γ - β) / (β - α))| = 1 / |(C k).eval (2 * (γ - (α + β)/2) / (β - α))|`
  and `Chat_degree_le`, `Chat_eval_γ : (Chat k α β γ).eval γ = 1`.
- **Backbone item.** §2.1.9 `Polynomial.Chebyshev.one_div_eval_T_le_sSup_abs_eval` (general `γ`),
  `sSup_abs_eval_shifted`, `shifted_degree_le`, `shifted_eval_self`
  (`Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean`).
- **Proof route.** `Chat_eq_shifted` (D17) then the four backbone lemmas; the second form of the value
  is algebra (`1 + 2(γ−β)/(β−α) = 2(γ−μ)/(β−α)`).
- **Classification.** `direct`.

### R62. Lemma 6.26 (Zarantonello; proof by reference)
- **Book statement.** For the circle `C(0, ρ)` and `γ ∈ ℂ` not enclosed by it,
  `min_{p ∈ P_k, p(γ)=1} max_{|z|=ρ} |p(z)| = (ρ/|γ|)^k`, attained by `(z/γ)^k`; by translation the
  same for `C(c, ρ)` with `|γ − c| > ρ`.
- **Lean surface statement.** `theorem lemma_6_26 (hγ : ρ < ‖γ‖) :
  IsLeast {M | ∃ p : ℂ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧ M = sSup ((fun z => ‖p.eval z‖) '' Metric.sphere 0 ρ)} ((ρ / ‖γ‖)^k)`.
- **Backbone item.** the deferred complex Chebyshev / ellipse results of §2.1.9 (§4).
- **Proof route.** Not in the book (ref. [232]); standard proof via the maximum principle /
  Bernstein-type argument for `w ↦ p(γ w)`.
- **Classification.** `deferred` (§4).

### R63. Theorem 6.27 and the ellipse bound (6.117), (6.119)–(6.120)
- **Book statement.** For the ellipse `E_ρ = J(C(0, ρ))`, `ρ ≥ 1`, and `γ` not enclosed by it, with
  `w_γ` the dominant root of `J(w) = γ`:
  `ρ^k/|w_γ|^k ≤ min_{p ∈ P_k, p(γ)=1} max_{z ∈ E_ρ} |p(z)| ≤ (ρ^k + ρ^{−k})/|w_γ^k + w_γ^{−k}|` (6.117).
  For `E(c, d, a)`: `max_{z ∈ E(c,d,a)} |Ĉ_k(z)| = C_k(a/d)/|C_k((c−γ)/d)|` with `Ĉ_k` as in (6.119);
  the explicit form (6.120).
- **Lean surface statement.** `theorem theorem_6_27 (hρ : 1 ≤ ρ) (hγ : γ ∉ closed ellipse) :
  ρ^k / ‖wγ‖^k ≤ sInf {…} ∧ sInf {…} ≤ (ρ^k + ρ⁻¹^k) / ‖wγ^k + wγ⁻¹^k‖`;
  `theorem ellipse_max_Chat : sSup ((fun z => ‖(Chat_ℂ k c d γ).eval z‖) '' ellipse c d a) = (C k).eval (a/d) / ‖(Ccomplex k).eval ((c - γ)/d)‖`
  (for real `a/d`).
- **Backbone item.** the deferred complex Chebyshev / ellipse results of §2.1.9 (§4).
- **Proof route.** Upper bound: the explicit polynomial and `max |w^k + w^{−k}|` on `|w| = ρ` at
  `w = ρ`; lower bound: Lemma 6.26 applied to a degree-`2k` polynomial in `w`.
- **Classification.** `deferred` (§4; depends on R62).

### R64. Lemma 6.28
- **Book statement.** Let `x_m` be the `m`-th CG iterate, `d_m = x_* − x_m`. Then
  `x_m = x_0 + q_m(A) r_0` with `deg q_m ≤ m − 1` and
  `‖(I − A q_m(A)) d_0‖_A = min_{q ∈ P_{m−1}} ‖(I − A q(A)) d_0‖_A`.
- **Lean surface statement.** `theorem lemma_6_28 (hA : A.PosDef) (hstar : Aop xstar = b) (m) :
  ∃ q : ℝ[X], q.degree < m ∧ (cg A b x₀ m).1 = x₀ + aeval Aop q r₀ ∧ ∀ q' : ℝ[X], q'.degree < m →
  anorm A ((1 - Aop ∘ₗ aeval Aop q) (xstar - x₀)) ≤ anorm A ((1 - Aop ∘ₗ aeval Aop q') (xstar - x₀))`.
- **Backbone item.** §3.4 `Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf` (`Numlib/Krylov/Iterate.lean`;
  the `min_{deg p ≤ m, p 0 = 1} ‖p(A)(x* − x₀)‖_A` form), `IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval`;
  §3.7 `CG.isGalerkinIterate`; §2.1.4 `Matrix.posDef_iff_isSymmetricCoercive`; §3.1
  `Krylov.mem_subspace_iff_exists_aeval`; §2.4.2 `IsGalerkin.iff_energyNorm_min` behind the backbone
  proof.
- **Proof route.** `cg_eq_CG` + `CG.isGalerkinIterate` + `posDef_iff_isSymmetricCoercive`; the
  polynomial form is `mem_subspace_iff_exists_aeval` on `x_m − x_0` and on any competitor;
  `(1 − A q(A)) d_0 = x_* − (x_0 + q(A) r_0)` and `p = 1 − X q` translates to the backbone's form.
- **Classification.** `direct`.

### R65. Theorem 6.29, (6.122)–(6.123)
- **Book statement.** For SPD `A` with extreme eigenvalues `λ_min, λ_max`, `η = λ_min/(λ_max − λ_min)`:
  `‖x_* − x_m‖_A ≤ ‖x_* − x_0‖_A / C_m(1 + 2η)` (6.123).
- **Lean surface statement.**
  ```lean
  theorem theorem_6_29 [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b x₀ xstar : 𝔼)
      (hstar : Aop xstar = b) (hl : ⨅ i, hA.1.eigenvalues i < ⨆ i, hA.1.eigenvalues i) (m : ℕ) :
      anorm A (xstar - (cg A b x₀ m).1) ≤
        anorm A (xstar - x₀) / (C m).eval (1 + 2 * η (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i))
  ```
  (when `λ_min = λ_max` the book's `η` is `+∞`; the book tacitly assumes at least two distinct
  eigenvalues, hence `hl`).
- **Backbone item.** §3.10 `Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T`
  (`Numlib/Krylov/Convergence/CG.lean`; hypotheses `0 < lmin`, `lmin < lmax`,
  `hA : A.IsSymmetricBoundedBy lmin lmax`, `hx : IsGalerkinIterate A b x₀ m x`, `hstar : A xstar = b`;
  conclusion `energyNorm A (xstar - x) ≤ energyNorm A (xstar - x₀) / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin))`);
  the glue `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin` (`Numlib/Analysis/Matrix/ToEuclideanLin.lean`)
  with `lmin = ⨅ i, eigenvalues i`, `lmax = ⨆ i, eigenvalues i` (`ciInf_le`, `le_ciSup`) and Mathlib
  `Matrix.PosDef.eigenvalues_pos` for `0 < lmin`; behind the backbone proof: §3.9
  `LinearMap.IsSymmetricBoundedBy.energyNorm_aeval_map_apply_le`, §2.1.9
  `one_div_eval_T_le_sSup_abs_eval_of_eval_zero` (Thm 6.25 with `[α, β] = [λ_min, λ_max]`, `γ = 0`).
- **Proof route.** `cg_eq_CG`, `CG.isGalerkinIterate` (through `posDef_iff_isSymmetricCoercive`), the
  glue, then the backbone bound with `one_add_two_mul_η` (D17).
- **Classification.** `direct`.

### R66. (6.124)–(6.128)
- **Book statement.** `C_m(1+2η) ≥ ½(1 + 2η + √((1+2η)²−1))^m = ½(1 + 2η + 2√(η(η+1)))^m`;
  `1 + 2η + 2√(η(η+1)) = (√η + √(η+1))² = (√λ_min + √λ_max)²/(λ_max − λ_min) = (√λ_max + √λ_min)/(√λ_max − √λ_min) = (√κ + 1)/(√κ − 1)`
  (6.124)–(6.127), `κ = λ_max/λ_min`; hence `‖x_* − x_m‖_A ≤ 2[(√κ − 1)/(√κ + 1)]^m ‖x_* − x_0‖_A` (6.128).
- **Lean surface statement.** `theorem equation_6_124_127 (h : 0 < lmin) (h' : lmin < lmax) :
  1 + 2 * η lmin lmax + 2 * √(η (η + 1)) = (√η + √(η+1))^2 ∧ … = (√(κ lmin lmax) + 1) / (√κ - 1)`;
  `theorem equation_6_128 … : anorm A (xstar - (cg A b x₀ m).1) ≤ 2 * ((√κ - 1)/(√κ + 1))^m * anorm A (xstar - x₀)`.
- **Backbone item.** §3.10 `Krylov.IsGalerkinIterate.energyNorm_error_le` ((6.128) with the same
  hypotheses as R65, `κ = lmax / lmin`); §2.1.9 `one_div_eval_T_le_two_mul_pow`
  (`1/T_m((κ+1)/(κ−1)) ≤ 2((√κ−1)/(√κ+1))^m`; note `(κ+1)/(κ−1) = 1 + 2η`), `half_pow_le_eval_T`.
- **Proof route.** (6.128) is the backbone theorem after `cg_eq_CG` and the R65 glue;
  (6.124)–(6.127) are real-algebra identities (surface, `field_simp`/`nlinarith` with `Real.sq_sqrt`).
- **Classification.** `direct` ((6.128)); `surface-only` (the identity chain, 20 lines).

### R67. Theorem 6.30
- **Book statement.** If `A` is (real) positive definite (`(Ax, x) > 0` for all real `x ≠ 0`,
  equivalently `(A + Aᵀ)/2` SPD), then GMRES(m) converges for any `m ≥ 1`. (Proof: each outer
  iteration reduces the residual at least as much as one MR step, so (5.15)
  `‖r_{k+1}‖ ≤ (1 − μ²/σ²)^{1/2} ‖r_k‖` holds with `μ = λ_min((A+Aᵀ)/2)`, `σ = ‖A‖₂`.)
- **Lean surface statement.** `theorem theorem_6_30 (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ x ≠ 0, 0 < inner (Aop x) x)
  (b x₀) (m) (hm : 1 ≤ m) : Filter.Tendsto (fun k => gmresRestarted A b m x₀ k) Filter.atTop (nhds (Aop.symm b))`
  (`Aop` invertible from `hA`), with the rate
  `theorem theorem_6_30_rate : ‖b - Aop (gmresRestarted A b m x₀ (k+1))‖ ≤ Real.sqrt (1 - μ^2/σ^2) * ‖b - Aop (gmresRestarted A b m x₀ k)‖`
  where `μ = ⨅ i, (symmPart A).eigenvalues i`, `σ = ‖A‖₂`.
- **Backbone item.** §3.10 `Krylov.restarted_minRes_tendsto`, `Krylov.IsMinResIterate.norm_residual_le_of_isCoerciveWith`
  (`Numlib/Krylov/Convergence/CG.lean`; for `A : E →L[𝕜] E` with `(A : E →ₗ E).IsCoerciveWith c`,
  `0 < c`, `1 ≤ m`: contraction factor `√(1 − c²/‖A‖²)` per cycle); §2.4.3
  `Projection.norm_residual_minResStep_le` behind it; the constants (`Numlib/Analysis/InnerProductSpace/Coercive.lean`):
  `LinearMap.isCoercive_iff_forall_pos` (the book's hypothesis), `ContinuousLinearMap.isCoerciveWith_iff_hermitianPart`
  and `LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue` (best constant
  `c = λ_min(½(A + Aᵀ))`), with `Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff`,
  `Matrix.toEuclideanLin_conjTranspose` and `Matrix.l2_opNorm_eq_norm_toEuclideanLin`
  (`Numlib/Analysis/Matrix/ToEuclideanLin.lean`) identifying `μ` and `σ`.
- **Proof route.** `gmres A b x₀ m` is a minimal-residual iterate over `𝒦_m ⊇ span{r₀}` (R18,
  `mEff ≥ 1` when `r₀ ≠ 0`), so the backbone contraction applies to
  `LinearMap.toContinuousLinearMap Aop`; `Tendsto` of the iterates from that of the residuals via
  `‖x − x*‖ ≤ ‖Aop⁻¹‖ ‖r‖`.
- **Classification.** `direct` (convergence); `needs-equivalence` (the glue above identifying the
  book's `μ, σ` in the rate).

### R68. Lemma 6.31
- **Book statement.** The `m`-th GMRES iterate is `x_m = x_0 + q_m(A) r_0` with `deg q_m ≤ m − 1`, and
  `‖r_m‖₂ = ‖(I − A q_m(A)) r_0‖₂ = min_{q ∈ P_{m−1}} ‖(I − A q(A)) r_0‖₂`.
- **Lean surface statement.** `theorem lemma_6_31 (hm : m ≤ μ) (hR) : ∃ q : ℝ[X], q.degree < m ∧
  gmresFixed A b x₀ m = x₀ + aeval Aop q r₀ ∧ ‖b - Aop (gmresFixed …)‖ = ‖(1 - Aop ∘ₗ aeval Aop q) r₀‖ ∧
  ∀ q', q'.degree < m → ‖(1 - Aop ∘ₗ aeval Aop q) r₀‖ ≤ ‖(1 - Aop ∘ₗ aeval Aop q') r₀‖`.
- **Backbone item.** §3.4 `Krylov.IsMinResIterate.norm_residual_eq_iInf`
  (`min_{deg p ≤ m, p(0) = 1} ‖p(A) r₀‖` form), `Krylov.IsMinResIterate.norm_residual_le_norm_aeval`,
  `Krylov.exists_residual_poly` (`Numlib/Krylov/Iterate.lean`); §3.1 `Krylov.mem_subspace_iff_exists_aeval`.
- **Proof route.** R18 + `p = 1 − X q` translation between the two polynomial forms.
- **Classification.** `direct`.

### R69. Proposition 6.32
- **Book statement.** Let `A = X Λ X^{-1}` be diagonalizable, `Λ = diag(λ_1, …, λ_n)`,
  `ε^{(m)} = min_{p ∈ P_m, p(0)=1} max_i |p(λ_i)|`. Then the `m`-th GMRES residual satisfies
  `‖r_m‖₂ ≤ κ₂(X) ε^{(m)} ‖r_0‖₂`, `κ₂(X) = ‖X‖₂ ‖X^{-1}‖₂`.
- **Lean surface statement.** Over `ℂ`, `open scoped Matrix.Norms.L2Operator`:
  `theorem proposition_6_32 (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X) (lam : Fin n → ℂ)
  (hA : A = X * Matrix.diagonal lam * X⁻¹) (hm : m ≤ μ) (hR) :
  ‖b - Aop (gmresFixed A b x₀ m)‖ ≤ ‖X‖ * ‖X⁻¹‖ * epsMin lam m * ‖r₀‖`.
- **Backbone item.** §3.4 `Krylov.IsMinResIterate.norm_residual_le_norm_aeval` /
  `norm_residual_eq_iInf` (the minimization over consistent polynomials); §3.9
  `norm_aeval_apply_le_of_conj` (`Numlib/Krylov/Convergence/Polynomial.lean`) is the same bound for
  a *symmetric* `D` (real spectrum) and covers that case directly; §2.1.2 `NormedRing.condNumber`;
  Mathlib `Matrix.l2_opNorm_diagonal`.
- **Proof route.** For complex `Λ` the surface proves `‖p(Λ) y‖ ≤ max_i |p(λ_i)| ‖y‖` entrywise
  (`aeval` of a diagonal matrix is diagonal) and conjugates:
  `‖X p(Λ) X⁻¹ r₀‖ ≤ ‖X‖ ‖X⁻¹‖ max_i |p(λ_i)| ‖r₀‖`, then `norm_residual_le_norm_aeval` and the
  `iInf` over `p` with `p(0) = 1`, `deg p ≤ m`.
- **Classification.** `needs-equivalence` (surface diagonal bound `norm_aeval_diagonal_mulVec_le`;
  the minimization is backbone).

### R70. Corollary 6.33
- **Book statement.** With `A = X Λ X^{-1}` diagonalizable and all eigenvalues in the ellipse
  `E(c, d, a)` excluding the origin, `‖r_m‖₂ ≤ κ₂(X) (C_m(a/d)/|C_m(c/d)|) ‖r_0‖₂`.
- **Lean surface statement.** `theorem corollary_6_33 (hX) (hA) (hE : ∀ i, lam i ∈ closedEllipse c d a) (h0 : 0 ∉ closedEllipse c d a) :
  ‖b - Aop (gmresFixed …)‖ ≤ ‖X‖ * ‖X⁻¹‖ * ((C m).eval (a/d).re / ‖(Ccomplex m).eval (c/d)‖) * ‖r₀‖`.
- **Backbone item.** R69 + R63 (deferred, §4); Mathlib `Complex.norm_le_of_forall_mem_frontier_norm_le`
  (maximum modulus) for "the maximum on the ellipse is on its boundary".
- **Proof route.** `ε^{(m)} ≤ max_{E} |Ĉ_m|` with `γ = 0`, then R63's ellipse maximum.
- **Classification.** `deferred` (§4; needs R63).

### R71. (6.129) — block Arnoldi relation
- **Book statement.** For Alg 6.22 (blocks `V_1, …, V_{m+1}` of size `n × p`, `H_ij` `p × p`,
  `U_m = [V_1 … V_m]`, `H_m = (H_ij)` band-Hessenberg, `E_m` the last `p` columns of `I_{mp}`):
  `A U_m = U_m H_m + V_{m+1} H_{m+1,m} E_mᵀ`; the blocks are orthonormal and mutually orthogonal.
- **Lean surface statement.** `theorem equation_6_129 (hV₁ : V₁ᴴ * V₁ = 1) (hfull : ∀ j ≤ m, (W j).rank = p) :
  A * U m = U m * Hblock m + Vb (m+1) * Hsub m * (E m)ᵀ ∧ ∀ i j, (Vb i)ᴴ * Vb j = if i = j then 1 else 0`.
- **Backbone item.** the deferred `Krylov/Block.lean` (§3.12, §4); Mathlib `gramSchmidtNormed` for
  the block QR.
- **Proof route.** Column-block form of the defining recurrence; orthogonality by induction as in
  Prop 6.4.
- **Classification.** `deferred` (§4, block Krylov methods).

### R72. §6.12 — Algorithms 6.23 and 6.24 are mathematically equivalent when `m` is a multiple of `p`
- **Book statement.** "The mathematical equivalence of Algorithms 6.23 and 6.24 when `m` is a
  multiple of `p` is straightforward to show" (same vectors up to the block-QR sign/phase
  convention).
- **Lean surface statement.** `theorem ruhe_eq_blockArnoldiMGS (hm : p ∣ m) (hfull) :
  ∀ j < m, ruhe A p v j = column (j % p) of (blockArnoldiMGS A p V₁ (j / p)).1` (with the
  Gram–Schmidt QR convention of D18; otherwise up to a unitary diagonal).
- **Backbone item.** the deferred `Krylov/Block.lean` (§4);
  `InnerProductSpace.exists_norm_eq_one_smul_gramSchmidtNormed` (flag uniqueness) for the "up to
  phase" form.
- **Proof route.** Both produce orthonormal bases of the same nested flag `span{v_1, …, v_j}`; with
  the Gram–Schmidt QR they coincide exactly.
- **Classification.** `deferred` (§4, block Krylov methods).

### R73. (6.130) — Ruhe's variant relation
- **Book statement.** For Alg 6.24, `w = A v_k − ∑_{i=1}^{j} h_ik v_i` with `k = j − p + 1` and line 9
  gives `A v_k = ∑_{i=1}^{k+p} h_ik v_i`; hence `A V_m = V_{m+p} H̄_m` with `H̄_m` of size `(m+p) × m`.
- **Lean surface statement.** `theorem ruhe_apply (k) : Aop (ruhe A p v k) = ∑ i ∈ Finset.range (k + p + 1), ruheCoeff A p v i k • ruhe A p v i`;
  `theorem equation_6_130 : A * Vruhe m = Vruhe (m + p) * HbarBlock A p v m`.
- **Backbone item.** the deferred `Krylov/Block.lean` (§4); the `p = 1` case is `Arnoldi.apply_vec` /
  (6.7).
- **Proof route.** Definition of `ruhe` (MGS loop) and orthonormality of the previous `v_i`;
  `ruhe A 1 v = arnoldiMGS A (v 0)` is a bonus equivalence.
- **Classification.** `deferred` (§4, block Krylov methods).

### R74. (6.135)–(6.136) — block residuals; block-FOM and block-GMRES
- **Book statement.** With `R_0 = [v_1 … v_p] R` (QR), `X = X_0 + V_m Y` (6.134), `E_1` the
  `(m+p) × p` matrix with identity top block: `B − A X = V_{m+p}(E_1 R − H̄_m Y)` (6.135); with
  `ḡ^{(i)} = E_1 R e_i`: `‖b^{(i)} − A x^{(i)}‖₂ = ‖ḡ^{(i)} − H̄_m y^{(i)}‖₂` (6.136). Block-FOM
  solves `H_m y^{(i)} = g^{(i)}`; block-GMRES minimizes (6.136) over `y^{(i)}` (unique minimizer); the
  residual norm is the 2-norm of components `m+1..m+i` of the transformed right-hand side.
- **Lean surface statement.** `theorem equation_6_135 (Y : Matrix (Fin m) (Fin p) 𝕜) : B - A * (X₀ + Vruhe m * Y) = Vruhe (m+p) * (E₁ * Rqr - HbarBlock … * Y)`;
  `theorem equation_6_136 (y : Fin m → 𝕜) (i) : ‖col B i - Aop (col X₀ i + Vruhe m *ᵥ y)‖ = ‖gbar i - HbarBlock … *ᵥ y‖`;
  `theorem blockGMRES_iff (i) : IsBlockGMRES A B X₀ m i x ↔ ∃ y, IsMinOn (fun y => ‖gbar i - HbarBlock *ᵥ y‖) univ y ∧ x = col X₀ i + Vruhe m *ᵥ y`;
  `theorem blockFOM_iff : IsBlockFOM … x ↔ ∃ y, Hblock *ᵥ y = g i ∧ x = …`.
- **Backbone item.** §2.4.1 `IsMinRes`, `IsGalerkin`, `isPetrovGalerkin_iff_mulVec` (general
  subspaces) for the specification statements; the deferred `Krylov/Block.lean` (§4) for the
  relations.
- **Proof route.** Same as R17/R18/R11 with `span{v_1..v_m}` (block Krylov space) in place of `𝒦_m`
  and `E_1 R e_i` in place of `β e_1`; the Givens elimination with `p` rotations per column is not
  formalized (no result is stated about it).
- **Classification.** `direct` for the specification statements (§2.4.1 is basis-agnostic);
  `deferred` for (6.135)–(6.136) (§4, block Krylov methods).

### R75. P-6.5 — GMRES from (5.7) with `V = V_m`, `W = A V_m`
- **Book statement.** Derive GMRES from `x = x_0 + V (Wᵀ A V)^{-1} Wᵀ r_0` with `V = V_m`, `W = A V_m`:
  `y_m = (H̄_mᵀ H̄_m)^{-1} H̄_mᵀ (β e_1)` (normal equations).
- **Lean surface statement.** `theorem problem_6_5 (hm : m ≤ μ) (hR) : gmresY A b x₀ m = ((Hbar …)ᵀ * Hbar …)⁻¹ *ᵥ ((Hbar …)ᵀ *ᵥ (β • e₁ (m+1)))`
  and `gmresFixed A b x₀ m = x₀ + V *ᵥ ((V ᵀ Aᵀ A V)⁻¹ *ᵥ (Vᵀ Aᵀ r₀))`.
- **Backbone item.** §2.4.1 `isPetrovGalerkin_iff_mulVec` + §2.4.2 `IsMinRes.iff_isPetrovGalerkin`
  (Prop 5.3).
- **Proof route.** `L = A 𝒦_m` with basis `A v_j`; `(A V_m)ᵀ A V_m = H̄_mᵀ H̄_m` by (6.7).
- **Classification.** `direct`.

### R76. P-6.13 — if `H_m` is nonsingular and `x_m^G = x_m^F` then both are exact
- **Book statement.** If `H_m` nonsingular and `x_m^G = x_m^F`, then `r_m^G = r_m^F = 0`.
- **Lean surface statement.** `theorem problem_6_13 (hm) (hH : FOMDefined A b x₀ m) (heq : gmresFixed A b x₀ m = fomFixed A b x₀ m) :
  b - Aop (gmresFixed …) = 0 ∧ b - Aop (fomFixed …) = 0`.
- **Backbone item.** R33/R34 (`ρ^F = ρ^G/|c_m|` with `|c_m| < 1` unless `s_m = 0`), or R38.
- **Proof route.** (6.74): `x^G_m = x^F_m` and `c_m ≠ 0` give `s_m²(x^G_{m−1} − x^F_m) = 0`; if
  `s_m = 0` then `r^G_m = 0` (R23) and `r^F_m = r^G_m/|c_m| = 0`; if `s_m ≠ 0` then
  `x^G_{m−1} = x^F_m ∈ x₀ + 𝒦_{m−1}` ⇒ … ⇒ `r^F_m ⟂ 𝒦_m` and `r^F_m ∈ 𝒦_m` (Galerkin residual at
  step `m−1` lies in `𝒦_m`), so `r^F_m = 0`.
- **Classification.** `direct` (from R33–R38).

### R77. P-6.14 — Prop 6.12 from (6.75)
- **Book statement.** Derive (6.63) from `r_m^G = s_m² r_{m−1}^G + c_m² r_m^F` using orthogonality of
  the two vectors on the right.
- **Lean surface statement.** `theorem problem_6_14 (hm) (hH) : inner (rG (m-1)) (rF m) = 0 ∧ (ρG m)^2 = s^4 (ρG (m-1))^2 + c^4 (ρF m)^2`
  and hence `ρF m = ρG m / |c_m|`.
- **Backbone item.** §3.6 `Krylov.minRes_eq_combination` (R38); §3.4
  `Krylov.IsGalerkinIterate.residual_mem_span`, §2.4.1 `IsMinRes.residual_eq`.
- **Proof route.** `r^F_m ∈ span{v_{m+1}} ⟂ 𝒦_m` and `r^G_{m−1} ∈ 𝒦_m`; Pythagoras plus
  `c_m² + s_m² = 1` and R32.
- **Classification.** `direct`.

### R78. P-6.22 — see R16.

### R79. P-6.25 — see R28.

### R80. P-6.26 — see R42.

### R81. P-6.29 — Hessenberg matrices of IOP and Arnoldi
- **Book statement.** Let `S_m` be the unit upper triangular matrix of the Gram–Schmidt process
  applied to the IOP basis `V_m` (as in the proof of Thm 6.11). Then `H̄_m^G = S_{m+1}^{-1} H̄_m^Q S_m`.
- **Lean surface statement.** `theorem problem_6_29 (hV : (VI … (m+1)).rank = m + 1) : Hbar A v₁ m = (S (m+1))⁻¹ * HbarI A v₁ k m * S m`
  where `S j` is the (unit upper triangular) change of basis with `VI j = V j * S j`.
- **Backbone item.** §3.2 `Arnoldi.span_vec` (both bases span the same flag);
  `InnerProductSpace.eq_gramSchmidtNormed_of_re_inner_pos` (`Numlib/Analysis/InnerProductSpace/GramSchmidt.lean`)
  for the identification of the Gram–Schmidt basis of the IOP flag with `Arnoldi.vec` (its
  normalization hypothesis is positivity of the inner product in `𝕜`, as in D3).
- **Proof route.** `A V^Q_m = V^Q_{m+1} H̄^Q_m` and `V^Q_j = V^G_j S_j` (same flag, both leading
  coefficients positive in `𝕜`) give `A V^G_m S_m = V^G_{m+1} S_{m+1} H̄^Q_m`, and `A V^G_m = V^G_{m+1} H̄^G_m`
  with `V^G_{m+1}` injective.
- **Classification.** `surface-only`.

### R82. P-6.9 — see R39 (the surface proves Prop 6.17 via the backbone; P-6.9 asks for exactly this proof).

### R83. P-6.17 — see R51. P-6.19 (Lanczos coefficients from Alg 6.19) — left out (§5).

## 4. Deferred backbone items

Items 1, 3 and 4 are open nodes of the plan now: `Numlib/RingTheory/Polynomial/ChebyshevEllipse.toml`,
`Numlib/Krylov/OrthogonalPolynomials.toml` (with `Arnoldi.charpoly_compression_isMinOn` already
proved in `Numlib/Eigen/RayleighRitz`) and `Numlib/Krylov/Block.toml`; the surface results are
`lemma_6_26`, `theorem_6_27`, `corollary_6_33` in `Chapter06/Section11.toml`, the two §6.6.2 nodes in
`Chapter06/Section06.toml`, and the new group `NumlibSurface/SaadSparse/Chapter06/Section12.toml`.

Backbone items scheduled for later phases of `backbone.md` (§7) on which some Chapter 6
results depend. Each is stated as a plan; the affected results are classified `deferred` above and
the corresponding surface theorems are written once the item exists.

1. **Complex Chebyshev polynomials on ellipses** (§2.1.9, phase 3): Zarantonello's circle lemma
   (Lemma 6.26, R62), the ellipse bound (Thm 6.27, R63) with the maximum of the shifted Chebyshev
   polynomial on `E(c, d, a)`, and their GMRES consequence (Cor 6.33, R70). Natural home:
   `Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean` (complex part) or a sibling `ChebyshevEllipse.lean`.
2. **Normal-matrix theory** — **written**, as `Numlib/Eigen/Normal.lean`, so R57's second half is
   now `direct` on it. The module proves that a normal operator has no generalized eigenvectors and
   hence, over an algebraically closed field, that its eigenspaces span
   (`LinearMap.IsStarNormal.iSup_eigenspace_eq_top`); that they are the eigenspaces of the adjoint
   at the conjugate eigenvalues (`…eigenspace_adjoint`, the easy half of Saad Lemma 1.15); that they
   are pairwise orthogonal and decompose the space (`…orthogonalFamily_eigenspaces`,
   `…direct_sum_isInternal`); and that the adjoint is a polynomial in the operator
   (`…exists_aeval_eq_adjoint`, matrix form `Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`).
   It also proves the hard half of Saad Lemma 1.15 — an operator sharing its eigenvectors with its
   adjoint is normal (`LinearMap.isStarNormal_of_adjoint_apply_eq_smul`) — which is what Lemma 6.23
   (R58) needed, so R58 is proved too and nothing in §6.10 is deferred any longer.
   It reaches all of that without Schur triangulation, which Mathlib does not have, and
   `natDegree (minpoly ℂ A)` = number of distinct eigenvalues turned out not to be needed at all
   (see R58's proof route), so it is not in the module.
   Thm 6.24 (R59) stays out regardless (§5): the book states it without proof and the known proofs
   are research-level.
3. **Ritz values and orthogonal polynomials** (phase 2): `Arnoldi.charpoly_compression_isMinOn`
   (§4.2, the characteristic polynomial of `H_m`/`T_m` minimizes `‖p(A) v₁‖` over monic `p` of
   degree `m`) and `Krylov/OrthogonalPolynomials.lean` (§3.12, Lanczos polynomials and
   `p_{T_m}(A) v_1 = β_2 ⋯ β_{m+1} v_{m+1}`). Needed by §6.6.2 (d)–(e) (R46).
4. **Block Krylov methods** (§3.12 `Krylov/Block.lean`, phase 3): block Arnoldi (Alg 6.22–6.24) with
   the block Hessenberg relation (6.129)–(6.130), the equivalence of the block and Ruhe variants,
   and the block-FOM/GMRES coordinate forms (6.135)–(6.136). Needed by R71–R74; the specification
   statements of R74 do not wait for it.

## 5. Left out

* Operation counts and storage tables: §6.3.2 table (GS/MGS/MGSR/HO flops), FOM cost/storage
  (§6.4), Householder-GMRES cost remarks (§6.5.2), DQGMRES `4n`/`2n` remarks, GCR "50% higher",
  P-6.3, P-6.6, P-6.15, P-6.16(3) — not mathematical statements.
* Examples 6.1–6.3 (Tables 6.1–6.3): numerical experiments.
* Double orthogonalization / Kahan's remark (§6.3.2), FOM(m) with adaptive `m` (§6.4.1), DIOM with
  partial pivoting ([240], P-6.7), "practical" stopping remarks (§6.5.3), preconditioning remarks
  (§6.5.5): implementation advice, no statements.
* (6.112) as an approximation `≳` and (6.121) `≈`: only the inequality/identity parts are stated
  (R60, R63); the asymptotic remarks after Thm 6.27 ("Chebyshev polynomials are asymptotically
  optimal") are not theorems in the book.
* Theorem 6.24 (Faber–Manteuffel): stated without proof. The normal-matrix theory it would rest on
  now exists (§4 item 2), so what is left is the proof, and the known proofs (Faber–Manteuffel 1984,
  Liesen–Strakoš 2008) are research-level. It appears in `Chapter06/Section10.lean` as a module doc
  comment mention only, with no `sorry` in the library.
* The final remark of §6.10 (`ν(A) ≤ 1` iff `A` has minimal degree `≤ 1`, or is Hermitian, or
  `A = e^{iθ}(ρI + B)` with `B` skew-Hermitian): "easy to show", not numbered; belongs with the
  normal-matrix items of §4, which now exist, so it is reachable if a second source ever cites
  it.
* "QMRS applied to IOM/DIOM yields QGMRES/DQGMRES" (§6.5.8, "can easily be shown"): unnumbered,
  heavy bookkeeping across D6/D9/D11; postponed until DQGMRES is needed by a second source.
* §6.5.9 alternatives for complex rotations (P-6.27) and the complex Householder GMRES (P-6.28):
  only the book's convention (6.80)–(6.81) is formalized (R20).
* Problems not cited by the text: P-6.2 (defining `w_j`: absorbed into D4), P-6.4 (variant GMRES with
  triangular least squares), P-6.8, P-6.10–6.12 (step counts for specific `A`; nice exercises on
  `grade`, optional), P-6.18 (`det T_m = 1/∏ α_i`), P-6.19 (Lanczos coefficients from Alg 6.19),
  P-6.20–6.21 (skew-symmetric `A`; P-6.21(b) is `Arnoldi.coeff_eq_zero_of_adjoint_mem` with `s = 2`,
  Saad Ch. 9), P-6.23 (`|c_m| ≥ c > 0` ⇒ convergence of GMRES/DQGMRES/FOM), P-6.24 (residual in the
  basis `v_1..v_{m+1}`), P-6.16(1)–(2) (alternative accumulation in Householder GMRES). None is
  required by a numbered result.
* Notes and References.

## 6. Statement conventions

Places where the formal statement fixes a detail the printed text leaves loose or states
differently; the choice is recorded here so that the semantic-alignment check has a reference.

* **(6.68), Prop 6.15:** stated with the constant `√(m+1)` (R36): the derivation
  `1/(ρ_m^G)² = ∑_{i=0}^m 1/(ρ_i^F)² ≤ (m+1)/(ρ^F_{m*})²` gives `√(m+1)`, which is also the constant
  of the backbone's `Krylov.exists_norm_residual_galerkin_le`.
* **(6.79) and the display before it:** the sums run over `j = 0, …, m` (they include
  `r_0^S = r_0^O`) and `1/τ_j² = ∑_{i=0}^j 1/ρ_i²` (R41), matching `Krylov.residual_mrs_eq`.
* **(6.103):** the plan uses the entrywise formulas (6.101)–(6.102) and `η_{j+1} = √β_{j−1}/α_{j−1}`
  from the text rather than the displayed matrix (R52).
* **Alg 6.19 / (6.98):** the iterate recurrence is `x_{j+1} = ρ_j(x_j + γ_j r_j) + (1 − ρ_j) x_{j−1}`,
  the form forced by (6.96) and `r = b − A x` (`CG.iterate_succ_eq_three_term`).
* **Prop 6.22 / Lemma 6.23:** Prop 6.22 is stated with `Aᵀ` (real) and Lemma 6.23 with `A^H`
  (complex); the paragraph between them switches from `Aᵀ = q(A)` to `A^H = q(A)`. The plan states
  Prop 6.22 over `ℝ` with `adjoint` (= transpose) and Lemma 6.23 over `ℂ` (R56–R58).
* **Lemma 6.23, `0 < s`:** the printed statement is false at `s = 0`, because `ℕ` truncates `s - 1`:
  for `A = I` the right-hand side holds (`ν(I) = 0 ≤ 0 - 1 = 0`) while the left-hand side fails
  (`𝒦_0(A, v) = ⊥`). `lemma_6_23` therefore assumes `0 < s`, which the book assumes implicitly —
  an `s`-term recurrence has `s ≥ 1`.
* **Lemma 6.23, nonsingularity:** the book assumes `A` nonsingular, and its proof uses that in the
  final step (a vector `w` of maximal grade with `A^H w = 0` would have to be zero). The proof of
  `lemma_6_23` reaches `ν(A) ≤ s - 1` from the uniqueness of coordinates in an orthogonal family of
  eigenvectors instead, which needs no such hypothesis, so the formal statement omits it and is
  strictly stronger than the printed one.
* **Thm 6.25:** "non-empty interval `[α, β]`" is read as nondegenerate (`α < β`), since (6.113)
  divides by `β − α` (R61).
* **P-6.1(c):** the plan uses the range `i ≤ j + 1` of (6.13) rather than the `i < j` printed in the
  problem (R10).
* **Prop 6.9:** the printed hypothesis "`m ≤ n`" is supplemented by "`m` Arnoldi steps completed"
  (`m ≤ grade`), which the proof uses (R22).
* **Prop 6.17:** the hypothesis `‖r^G_m‖ ≠ 0` ("makes no progress" at a nonzero residual) is made
  explicit (R39), as is `H_m` nonsingular in Props 6.12–6.13 and Lemma 6.16 (`FOMDefined`).
