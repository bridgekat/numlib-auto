# Adversarial review of `plans/backbone.md` (v0)

Reviewer: independent agent, 2026-09-04. Scope: README §"Reviewing a plan". Evidence: Mathlib
`v4.34.0-rc2` checkout (`grep`), LeanSearch (`leansearch.txt`), the two prototypes (both compile:
`proto1.log`, `proto2.log`), the emerging skeleton under `Numlib/` (read, not modified; three files
type-checked with `lake env lean`), and four scratch experiments in this directory:
`Exp1.lean` (T1–T9), `Exp2.lean`, `Exp3.lean`, `EnergyMerged.lean`. "Elaborates" below always means
"type-checks with `sorry`"; nothing was proved.

---

## (A) Summary verdict

The plan is well-researched and its architecture is right: Prop-valued specs (`IsPetrovGalerkin`,
`IsMinRes`, …) as the canonical objects, algebra at L0 (`Module.End`), Krylov/projection theory at
L1 (`E →ₗ[𝕜] E`, no completeness), analysis at L2, matrices only at L4. The Mathlib reuse table is
largely accurate and the backbone/surface split is sound. **It is not yet ready to formalize as
written**: (1) the `WithEnergy` construction (D17) does not elaborate and the skeleton built from it
fails; (2) several `RCLike`-level statements in the plan cannot elaborate (no order on `𝕜`, no
`A⁻¹` on `→ₗ`) — the skeleton already patched two of them ad hoc, so the plan must fix the
convention; (3) two type-checked ("✓") statements are false (`backwardError_antitone` at `k = 0`,
`tendsto_affineIter_iff` in infinite dimension) and one skeleton lemma derived from the
`IsMinError` spec is false (`exists_isMinError`), i.e. that spec is mis-designed for singular `A`;
(4) the grade/`Fact` convention should be replaced now (cheap) rather than after the Krylov chain
is built. With the changes in (B) — about a day of plan editing, no new mathematics — the plan is
good to go; (C) lists changes that reduce later refactoring, especially for Brenner–Scott, Choi and
Liesen–Strakoš.

---

## (B) Blocking issues

### R1 — `WithEnergy` (2.1.5, D17): the specified construction does not elaborate
* **Location.** §2.1.5, §9 D17, §11 Q1; skeleton `Numlib/ForMathlib/InnerProductSpace/Energy.lean`.
* **Problem.** Three independent failures (reproduced in `EnergyMerged.lean` = skeleton
  `Coercive.lean` + `Energy.lean` merged so it compiles standalone):
  1. `InnerProductSpace.ofCore (core A hA)` — in this Mathlib `ofCore` takes a
     `PreInnerProductSpace.Core` (`Analysis/InnerProductSpace/Defs.lean:569`); pass `(core A hA).toCore`.
  2. `K.map (equiv A hA)` — `Submodule.map` wants a `→ₛₗ`, not a `≃ₗ`; needs `.toLinearMap`.
  3. Instance diamond: `submoduleMap` is elaborated with the plain `instAddCommGroup`, while `ᗮ`
     and `starProjection` need the `AddCommMonoid` of `instNormedAddCommGroup`
     (= `core.toNormedAddCommGroup`); they are not defeq at instance transparency, so
     `(WithEnergy.submoduleMap A hA K)ᗮ` is rejected ("Application type mismatch …
     `@Submodule 𝕜 (WithEnergy A hA) … (WithEnergy.instAddCommGroup …)`").
* **Fix (verified in `Exp3.lean`).** Build the synonym the way Mathlib builds
  `Matrix.toInnerProductSpace` (`Analysis/Matrix/PosDef.lean:95–131`):
  ```lean
  def WithEnergy (A : E →ₗ[𝕜] E) (_hA : A.IsSymmetricCoercive) : Type _ := E
  namespace WithEnergy
  def toEnergy : E → WithEnergy A hA := id
  def ofEnergy : WithEnergy A hA → E := id
  section Build
  local instance : AddCommGroup (WithEnergy A hA) := inferInstanceAs (AddCommGroup E)
  local instance : Module 𝕜 (WithEnergy A hA) := inferInstanceAs (Module 𝕜 E)
  noncomputable def core : InnerProductSpace.Core 𝕜 (WithEnergy A hA) where
    inner x y := inner 𝕜 (A (ofEnergy A hA x)) (ofEnergy A hA y) ; …
  noncomputable instance : NormedAddCommGroup (WithEnergy A hA) := (core A hA).toNormedAddCommGroup
  noncomputable instance : InnerProductSpace 𝕜 (WithEnergy A hA) :=
    InnerProductSpace.ofCore (core A hA).toCore
  end Build            -- only the core-derived instances are global
  def equiv : E ≃ₗ[𝕜] WithEnergy A hA := { toFun := toEnergy A hA, invFun := ofEnergy A hA, … all rfl }
  def submoduleMap (K : Submodule 𝕜 E) := K.map (equiv A hA).toLinearMap
  ```
  With this, `inner (equiv x) (equiv y) = ⟪A x, y⟫` and `‖equiv x‖ = √(re ⟪A x, x⟫)` are `rfl`,
  `(submoduleMap K)ᗮ.starProjection` elaborates for finite-dimensional `K`, and the file must be a
  `noncomputable section`. Also record in the plan: the inner-product structure needs **no
  boundedness of `A`** (only `IsSymmetricCoercive`), so keep `A : E →ₗ[𝕜] E` for the instance
  (contrary to D17's suggestion); boundedness is needed only for `Continuous (equiv A hA)`, norm
  equivalence and `CompleteSpace (WithEnergy A hA)` — state those separately with `A : E →L[𝕜] E`.
  See R9 for building it on a sesquilinear form instead.

### R2 — `RCLike` statements that cannot elaborate (order on `𝕜`, `A⁻¹`)
* **Location.** §2.1.4 (`Matrix.posDef_iff_isSymmetricCoercive`), §2.4.3 (`kantorovich_inequality`
  with `A⁻¹ x` and `hspec : … → μ ∈ Set.Icc lmin lmax`), §3.10 ("state over `RCLike 𝕜`" a
  ✓-statement that was only checked over `ℝ`), §4.1–4.2 (`IsRitzPair.mem_Icc`).
* **Evidence.** `lake env lean Numlib/ForMathlib/InnerProductSpace/Coercive.lean` fails at line 92:
  `failed to synthesize PartialOrder 𝕜` (`Matrix.PosDef` needs `[PartialOrder 𝕜] [StarOrderedRing 𝕜]`,
  which for `RCLike` exist only under `open scoped ComplexOrder`, `Analysis/RCLike/Basic.lean:87,944`).
  `Exp1.lean` T2a: `∀ μ, Module.End.HasEigenvalue A μ → μ ∈ Set.Icc lmin lmax` fails
  (`Membership 𝕜 (Set ℝ)`); T3a: `A⁻¹ x` for `A : E →ₗ[𝕜] E` fails (`Inv (E →ₗ[𝕜] E)`).
* **Fix.** (i) `open scoped ComplexOrder` wherever `Matrix.PosDef` or `spectrum 𝕜 A ⊆ Icc` appears
  (T2d, T4 elaborate then). (ii) Never compare a `𝕜`-valued eigenvalue with a real interval; use
  real parameters `∀ μ : ℝ, HasEigenvalue A (μ : 𝕜) → μ ∈ Icc lmin lmax` (T2b) or, better, R3.
  (iii) Kantorovich inverse-free: the skeleton's `(hy : A y = x)` form, or
  `re⟪A(Ay), Ay⟫ · re⟪Ay, y⟫ ≤ C ‖Ay‖⁴` (T3), which is what Saad Thm 5.9's proof actually uses.
  The skeleton silently switched to `RCLike.re μ ∈ Icc`; make the convention explicit in the plan
  so all files agree.

### R3 — Fix the spectral-hypothesis convention now (§11 Q3): quadratic-form bounds, not eigenvalue lists
* **Location.** §2.4.3, §3.9, §3.10, §4.1–4.4, §5.2.3 (AH 5.6.1), §11 Q3.
* **Problem.** Every convergence bound is parametrized by "`∀ μ, HasEigenvalue A μ → μ ∈ Icc`",
  which (a) does not elaborate over `RCLike` (R2), (b) is finite-dimensional only, (c) does not
  match AH Thm 5.6.1, whose hypothesis is `m‖v‖² ≤ (Av,v) ≤ M‖v‖²` (`analysis/atkinson-han.md:874–890`),
  and (d) forces a second statement later for the Hilbert-space/CFC version.
* **Fix.** Bundle once, at L1, with no spectrum at all (`Exp1.lean` T2c elaborates):
  ```lean
  /-- `lmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ lmax ‖x‖²` for symmetric `A`: "the spectrum lies in `[lmin, lmax]`". -/
  structure LinearMap.IsSymmetricBoundedBy (A : E →ₗ[𝕜] E) (lmin lmax : ℝ) : Prop where
    isSymmetric : A.IsSymmetric
    le_re_inner : ∀ x, lmin * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)   -- = IsCoerciveWith lmin
    re_inner_le : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * ‖x‖ ^ 2
  ```
  and state Kantorovich, Saad Thm 5.9/6.29, AH 5.6.1, the Chebyshev and Ritz bounds with it. In
  finite dimension it is equivalent to "all eigenvalues in `[lmin, lmax]`" (Rayleigh:
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` / `_iInf_`) — provide that as the
  L3 bridge; the Saad surface instantiates `lmin = λ_min`, `lmax = λ_max`. The polynomial bound
  (3.9) still needs the spectral theorem (finite-dim) or CFC (phase 2), but no *statement* changes.
  Decide before 2.4.3/3.9/3.10 are written.

### R4 — `Krylov.grade` + `Fact (HasFiniteGrade A v)` (3.1, §11 Q4): replace before the Krylov chain is built
* **Location.** §3.1, §11 Q4; skeleton `Numlib/Krylov/Subspace.lean`, `Arnoldi.lean` (every
  breakdown lemma carries `[Fact (HasFiniteGrade A b)]`).
* **Problem.** `Fact` on a parametric Prop is non-idiomatic; synthesis does work at use sites
  (`Exp2.lean`), but a Hilbert-space user must write `haveI := Fact.mk h` everywhere, and the
  junk-`0` `sInf` definition has no Mathlib counterpart to lean on.
* **Fix (verified, `Exp1.lean` T1).** Define the grade as the dimension of the cyclic subspace and
  use Mathlib's own finiteness class as the hypothesis:
  ```lean
  noncomputable def Krylov.grade (A : Module.End K V) (v : V) : ℕ := Module.finrank K (fullSubspace A v)
  -- hypothesis [FiniteDimensional K (fullSubspace A v)] — automatic from [FiniteDimensional K V]
  theorem finrank_subspace [FiniteDimensional K (fullSubspace A v)] (m) :
      Module.finrank K (𝒦[A, v] m) = min m (grade A v)
  theorem grade_le_iff [FiniteDimensional K (fullSubspace A v)] : grade A v ≤ m ↔ (A ^ m) v ∈ 𝒦[A, v] m
  theorem hasFiniteGrade_iff : FiniteDimensional K (fullSubspace A v) ↔ ∃ m, (A ^ m) v ∈ 𝒦[A, v] m
  ```
  `grade = sInf {m | A^m v ∈ 𝒦_m}` becomes a lemma (`grade_eq_sInf`) used in D5's proof. This
  matches Mathlib's `finrank` junk convention, is the definition used by Liesen–Strakoš ("grade =
  dim of the cyclic subspace = degree of the minimal polynomial of `v`"), and connects to
  `Module.AEval'` / `Submodule.span R[X] {v}` for the phase-2 minimal-polynomial item. `ℕ∞` is not
  worth it: every consumer takes `min m grade` in `ℕ`.

### R5 — False or misleading "✓" statements
* **`Krylov.IsMinResIterate.backwardError_antitone`** (Proto2 l.212; §3.11 "✓ (the β = 0 form)").
  `Antitone fun k => ‖b - A (x k)‖ / ‖x k‖` with `x 0 = 0` is **false** in Lean: at `k = 0` the value
  is `‖b‖ / 0 = 0`, so antitonicity forces `‖r₁‖ = 0`. Fong–Saunders Thm 3.1 is for `k ≥ 1`. State
  `Antitone fun k => ‖b - A (x (k + 1))‖ / ‖x (k + 1)‖` (or `AntitoneOn … (Set.Ici 1)`), and audit
  every ratio-valued statement (`Krylov.inv_sq_norm_residual_minRes` is fine thanks to `h0`).
* **`tendsto_affineIter_iff`** (Proto1 l.156; §2.3.1 "✓ (as an iff in the prototype)"). The `⇐`
  direction ("convergence for all `f, x₀` ⇒ `ρ(G) < 1`") is **false** in infinite dimension (the
  plan says so itself in 2.3.1). Remove the iff from the prototype; keep the two one-directional
  statements. Add to §0 that "✓" means *elaborates*, not *true*.
* **`exists_isMinError`** (skeleton `Projection/Basic.lean`, derived from §2.4.1 `IsMinError`). With
  `IsMinError` quantifying over *every* solution `xstar`, `∃ x, IsMinError A b x₀ K x` is **false**
  when `ker A ≠ ⊥` (e.g. `A = 0`, `b = 0`, `K = ⊤`: no `x` is nearest to every `xstar`). Redesign
  the spec (this is also what Choi's SYMMLQ/CGNE on singular systems needs): make the target explicit,
  ```lean
  structure IsMinError (A : E →ₗ[𝕜] E) (xstar x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
    mem : x - x₀ ∈ K
    min : ∀ y, y - x₀ ∈ K → ‖xstar - x‖ ≤ ‖xstar - y‖
  ```
  with `Krylov.IsMinErrorIterate A xstar x₀ m x` using `K = A 𝒦_m(A, A xstar − A x₀)`; then
  `eq_starProjection` is the definition unfolded and existence is `starProjection`.

---

## (C) Should-fix issues

### R6 — Take D4 (`Arnoldi.vec_succ_eq`, "Gram–Schmidt = classical recurrence") off the phase-1 critical path
* **Location.** §3.2, §7 (row `Krylov/{Subspace,Arnoldi,Lanczos}` ★★★), §9 D4.
* **Problem.** Nothing in the phase-1 *backbone* uses the classical recurrence: Lanczos (3.3),
  Iterate (3.4), Hessenberg (3.5), Relations (3.6), CG/CR (3.7–3.8), Convergence (3.9–3.10) use only
  orthonormality, `span_vec`, `coeff` and `apply_vec`, which Mathlib gives for free
  (`gramSchmidtNormed_orthonormal'`, `span_gramSchmidt_Iic`, `gramSchmidt_ne_zero_coe`). Only the
  surface file `SaadSparse/Ch06/Arnoldi.lean` (Alg 6.1–6.3) needs D4.
* **Fix.** Keep `Arnoldi.vec := gramSchmidtNormed` (the right choice) and move
  `vec_succ_eq`/`coeff_succ_self` to a phase-1b file `Krylov/ArnoldiRecurrence.lean`. Simpler
  proof than the leading-coefficient induction: both `vec (j+1)` and `w_j/‖w_j‖` are unit vectors
  of the ≤1-dimensional space `𝒦_{j+2} ⊓ 𝒦_{j+1}ᗮ` (skeleton lemmas `vec_mem_subspace`,
  `vec_mem_orthogonal`, `starProjection_apply_vec` give this), so they differ by a unimodular
  scalar; the scalar is `1` because `⟪vec (j+1), A^{j+1} b⟫ > 0` (Gram–Schmidt),
  `⟪vec (j+1), A (vec j)⟫ = ‖w_j‖ > 0`, and `A (vec j) − c_j A^{j+1} b ∈ 𝒦_{j+1}` with `c_j > 0` — one
  induction on `c_j > 0`.

### R7 — D7 (Cullum–Greenbaum without Givens): the sketch has a gap; fill it or route through 3.5
* **Location.** §3.6, §9 D7.
* **Problem.** The residual-smoothing argument needs `r^G_m ∈ span{r^G_{m−1}, r^F_m}` (equivalently,
  that the minimum over the *line* is the minimum over `r₀ + A𝒦_m`); the plan asserts "minimal by
  induction" without this step.
* **Fix.** Add the lemma: for `m < grade`, `A𝒦_m = A𝒦_{m−1} ⊕ 𝕜∙d` with `d := r^F_m − r^G_{m−1} ∈ A𝒦_m`
  and `d ∉ A𝒦_{m−1}` (since `r^F_m ∈ 𝕜∙v_{m+1}`, Prop 6.7, while `A𝒦_{m−1} ⊆ 𝒦_m`); `r^S_m ⟂ A𝒦_{m−1}`
  (both `r^G_{m−1}` and `r^F_m` are) and `r^S_m ⟂ d` (line optimality) give `r^S_m ⟂ A𝒦_m`, hence
  `r^S_m = r^G_m` by `IsMinRes.residual_unique`. Cases `r^F_m = 0` / `m ≥ grade` are trivial. Still
  L1 and a solid ★★; otherwise derive it in 3.5 from the Hessenberg least-squares problem.

### R8 — Real Banach spaces and the spectral radius: make the restriction explicit and safe
* **Location.** §2.1.3, §2.3.1, §8.1 Ch04.
* **Problem.** `spectralRadius ℝ G` exists in Mathlib for real Banach algebras, and
  `spectralRadius ℝ G < 1 → Gᵏ → 0` is **false** (rotation by 90° in `ℝ²`: empty real spectrum). A
  future agent asked to "generalize 2.1.3 to `RCLike`" will produce this.
* **Fix.** Put the counterexample in 2.1.3's docstring; make `Matrix.spectralRadius A :=
  spectralRadius ℂ (A.map Complex.ofReal)` the *only* real notion (2.1.11); keep Gelfand-based
  results over `ℂ`. Note `summable_pow_iff_spectralRadius_lt_one` ⇐ is
  `NormedRing.summable_geometric_of_norm_lt_one` after Gelfand, ⇒ is `spectrum.spectralRadius_pow_le`.

### R9 — Build the energy structure on a sesquilinear *form*, not on an operator (unifies 2.1.5 with 5.2)
* **Location.** §2.1.5, §5.2.1–5.2.3 (`cea_hermitian`, `SesqForm.toOperator`), §10.
* **Problem.** `energyInner A x y = ⟪A x, y⟫` is a Hermitian coercive sesquilinear form; Céa with
  constant 1 (5.2.3) and Saad Prop 5.5 (2.4.2) are the same theorem about such a form. A
  finite-element book (Brenner–Scott, Ern–Guermond) works with forms `a(u,v)` on a possibly
  non-complete `V`, where `SesqForm.toOperator` (needs `CompleteSpace`) is unavailable; the plan
  would then need a second `WithEnergy`.
* **Fix (elaborates, `Exp1.lean` T5 modulo the R1 pattern).** Define
  `energyForm A : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜).comp A` (`energyForm A x y = ⟪A x, y⟫` is `rfl`),
  define `WithEnergy` for any `B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜` with `IsHermitian B ∧ IsCoerciveWith B c`, and
  let the operator version be `WithEnergy (energyForm A)`. Use the *unbundled* `→ₗ⋆` form so L1
  needs no norms; the bounded `→L⋆` forms of 5.2 coerce to it. Mathlib already has the L4 instance
  `Matrix.toInnerProductSpace` / `Matrix.toNormedAddCommGroup` (`Analysis/Matrix/PosDef.lean`) for
  `n → 𝕜` with a `PosDef` matrix — add the bridge lemma so the surface can use either.

### R10 — `Ring.Splitting`: right level, wrong shape and name
* **Location.** §2.3.2, §1.3.
* **Problem.** The structure stores `m`, `n` and `eq : a = m − n`; `n` is determined by `m`, so
  each constructor carries a proof obligation and two splittings with the same `m` are not
  syntactically equal. `Ring.Splitting` suggests a ring-theoretic notion (split sequences,
  splitting fields) and will never be upstreamed under that name; `iterMatrix` is wrong at ring level.
* **Fix (elaborates on `→L` and on matrices, `Exp1.lean` T7).**
  ```lean
  structure Stationary.Splitting {R : Type*} [Ring R] (a : R) where
    m : R
    isUnit : IsUnit m
  def Splitting.n (s : Splitting a) : R := s.m - a
  def Splitting.iterationOperator (s : Splitting a) : R := 1 - Ring.inverse s.m * a   -- `= m⁻¹ n`
  ```
  On matrices `Ring.inverse = ⁻¹` via `Matrix.nonsing_inv_eq_ringInverse` (`simp` closes it). Keep
  the constructors (`jacobiSplitting := ⟨diagPart A, h⟩`, …).

### R11 — Matrix layer (§11 Q5): index the Givens/Hessenberg recurrences by `ℕ`, not `Fin (m+1)`
* **Location.** §2.1.10, §3.5, §7 ("Givens bookkeeping").
* **Problem.** `Matrix (Fin (m+1)) (Fin m) 𝕜` with `Fin.castSucc`/`Fin.succ` casts is the classic
  dependent-type tar pit; Saad (6.37)–(6.47) and Choi's MINRES are *scalar recurrences* in `j`.
* **Fix.** State the QR of `H̄_m` as sequences `c s γ : ℕ → 𝕜` with `γ (j+1) = -s j * γ j`,
  `‖r_m‖ = |γ (m+1)|`, packaging into `Fin`-matrices only at the end (as the skeleton's
  `hessenberg`/`hessenbergSq` do). Independently, 3.6 can *define* `s_m := ‖r^G_m‖/‖r^G_{m−1}‖`,
  `c_m := ‖r^G_m‖/‖r^F_m‖` and prove `c_m² + s_m² = 1` (Cullum–Greenbaum); 3.5 then shows the Givens
  parameters equal these. That makes 2.1.10 non-blocking for phase 1 (Saad Prop 6.9/6.12,
  Fong–Saunders (4.1) become spec-level).

### R12 — Dependency/phasing corrections (§7)
* `Eigen/Perturbation` is listed as blocked by 2.1.6; Bauer–Fike/Bendixson need only matrix norms and
  `LinearMap.IsSymmetric.eigenvalues` — unblock it (parallel work).
* `Variational/*` is listed as blocked by 2.1.4; with R9 it depends only on Mathlib (real
  `IsCoercive.*` Lax–Milgram) — parallelizable.
* `Krylov/Monotonicity` (3.11) is the true tail: needs `CR.isMinResIterate` (3.8), uniqueness (2.4.1)
  **and** the L3 sign lemma with finite termination; schedule last, budget ★★★.
* `SaadSparse` at "1200 lines ★" is optimistic: Ch. 6 algorithms (FOM `H_m⁻¹ β e₁`, GMRES least
  squares, MGS/Householder) need `Fin`-indexed definitions plus equivalence lemmas; ★★.
* Suggested split. **Phase 1a**: 2.1.1–2.1.6, 2.1.8–2.1.9, 2.4, 3.1–3.4, 3.7, 3.9–3.10, §5,
  `FongSaunders` §2. **Phase 1b**: 2.1.10–2.1.11, 2.3, 3.5–3.6, 3.8, 3.11, D4, remaining surfaces.
  The ≈9.5k-line total is plausible for statements; proofs of D4/D6/D7/D8 typically double their
  estimates.

### R13 — Mathlib names that are wrong or missing in §1.6/§2/§4
* `Matrix.schur_triangulation` — **does not exist** (grep + LeanSearch); Mathlib has only
  `Matrix.IsHermitian.spectral_theorem`. Move Schur form to "Mathlib gap" (§4.5, §8.1 Ch01).
* `Submodule.finrank_inf_add_finrank_sup` → `Submodule.finrank_sup_add_finrank_inf_eq`
  (`LinearAlgebra/FiniteDimensional/Lemmas.lean:53`).
* `ContinuousLinearMap.isClosed_range_of_antilipschitz` →
  `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective` (`Analysis/Normed/Operator/Banach.lean:400`);
  the coercive case already has `IsCoercive.isClosed_range`, `.antilipschitz`, `.ker_eq_bot`,
  `.range_eq_top` (real).
* `ContinuousLinearMap.coe_pow` is deprecated → `ContinuousLinearMap.toLinearMap_pow` (`Exp1.lean` T6).
* `Matrix.IsIrreducible` / `IsPrimitive` do exist (`LinearAlgebra/Matrix/Irreducible/Defs.lean`) — correct.
* 2.1.1's first lemma is essentially in Mathlib: `Units.oneSub t h` has inverse `∑' n, t ^ n`
  (`geom_series_mul_neg`, `mul_neg_geom_series`, `NormedRing.inverse_one_sub`) and
  `NormedRing.tsum_geometric_of_norm_lt_one : ‖∑' n, x ^ n‖ ≤ ‖(1:R)‖ - 1 + (1 - ‖x‖)⁻¹` gives
  `‖(1 − t)⁻¹‖ ≤ 1/(1 − ‖t‖)` under `NormOneClass` in two lines; say so.

### R14 — Two spec-level adjustments to 2.4.1 / §11 Q6
* `IsPetrovGalerkin.eq_of_invt` uses `hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0` (`K ⊓ Lᗮ = ⊥`); Saad Prop 5.6's
  hypothesis is nonsingularity of `Wᴴ A V`, which for `L = A K` is *not* `K ⊓ (AK)ᗮ = ⊥`. Add the
  `IsMinRes` corollary (`Krylov.IsMinResIterate.apply_eq_of_grade_le` with `Injective A`) so the
  surface can prove Prop 5.6 for both FOM and GMRES.
* Restarted GMRES(m) *does* satisfy a spec: `∀ k, Krylov.IsMinResIterate A b (x k) m (x (k+1))`. Then
  Saad Thm 6.30 (3.10 `restarted_minRes_tendsto`) is a backbone theorem about any such sequence and
  the surface never needs the algorithm; only truncated methods (IOM/DIOM/ORTHOMIN(k)) are
  algorithm-only.

### R15 — `Fl.RoundingModel` (§6): fix the algebraic footing before it is used as an interface
`Rounds : K → K → Prop` with only `|y − x| ≤ u|x|` is fine (exact arithmetic is a model), but
"results for an explicit evaluation order" need an expression datatype (a `SumTree`/fold) *and* a
relation-lifting lemma. Decide now that the layer is relational (Higham's "some `δ` with
`|δ| ≤ u`") — then every theorem is `∀ y, Rounds … y → …`. Use the namespace `FloatingPoint`
(not `Fl`) to match the directory.

---

## (D) Nice-to-have

### R16 — Naming (§1.4, §10) for discoverability
* `IsMinRes` / `Krylov.IsMinResIterate` → `IsMinResidual` / `Krylov.IsMinResidualIterate` (avoids a
  clash with the algorithm namespace `MINRES` that the Choi/Fong–Saunders surfaces will introduce;
  pairs with `IsMinError`).
* `compression` → `LinearMap.compression` (dot notation `A.compression K`; docstring should mention
  "Rayleigh–Ritz section" (Saad-eig) and "restriction" (Meurant)).
* `Arnoldi.vec` → `Arnoldi.vector`; `Ring.Splitting.iterMatrix` → `Stationary.Splitting.iterationOperator` (R10).
* `Krylov.fullSubspace`: keep, docstring alias "cyclic subspace generated by `v`".
* `Matrix.IsStrictDiagDominant` → `Matrix.IsStrictlyDiagDominantRow` / `…Col` (Kress and Saad need both).
* `Matrix.IsUpperHessenberg` via `∃ k, j < k ∧ k < i` on a general linear order is hard to use;
  every consumer is `Fin n`/`ℕ`, so define it there as `j + 1 < i → H i j = 0` (as the skeleton's
  `IsUpperHessenbergRect` does) and drop the generic version.
* `Fl` → `FloatingPoint`; keep scoped `κ` for `NormedRing.condNumber`.
* `LinearMap.IsSymmetricCoercive`: keep (honest in infinite dimension) but add "(= SPD/HPD,
  `Matrix.PosDef`, 'strongly positive')" to the docstring so grep for `PosDef` finds it.

### R17 — Chebyshev min–max (D2): avoid the parity lemma
Mathlib's `T_neg` is about a negative *index* (`T R (-n) = T R n`), not `T_n(−x)`. Apply
`eval_iterate_derivative_le_of_forall_abs_le_one` (k = 0) to `q.comp (−X)` and to `−q` at
`−x₀ > 1`; this gives `|q(x₀)| ≤ T_m(|x₀|)` with no parity argument. Use `one_lt_abs_eval_T_real`
(`Chebyshev/RootsExtrema.lean:87`) for positivity of the denominator.

### R18 — D14/D18 (power/subspace iteration)
The route is right; it needs `Module.End.iSup_maxGenEigenspace_eq_top` (algebraically closed) and
`Module.End.independent_maxGenEigenspace`; the spectrum of the restriction to
`W = ⨆_{μ ≠ λ₁} maxGenEigenspace μ` is `σ(A) \ {λ₁}` (eigenvector lift through `LinearMap.restrict`).
The gap metric between subspaces (D18) is a genuine Mathlib gap; postpone.

### R19 — `norm_residual_eq_iInf` and `cea` use `⨅` over reals
Fine, but each needs `BddBelow` + nonemptiness side lemmas (`ciInf_le`, `le_ciInf`); prefer
`IsLeast` statements (`IsLeast {‖p(A) r₀‖ | deg p ≤ m ∧ p 0 = 1} ‖r_m‖`), which are stronger and
simp-friendlier.

### R20 — Prototype hygiene (§11 Q7)
Keep `plans/prototypes/*.lean` until the skeleton builds under `lake build`, then delete; fix the
two false ✓ statements (R5) immediately so nobody copies them.

---

## (E) Answers to the §11 open questions

1. **`→ₗ` vs `→L`.** Keep the plan's choice: `E →ₗ[𝕜] E` at L0/L1 (specs, Krylov, Arnoldi/Lanczos,
   CG/CR, optimality), `E →L[𝕜] E` only where `‖A‖`, `spectralRadius`, adjoints or completeness
   enter. Evidence: a `→L` user pays one coercion `(A : E →ₗ[𝕜] E)` and one `simp` lemma
   (`ContinuousLinearMap.coe_coe`; powers via `toLinearMap_pow`) — `Exp2.lean`; a
   `FunLike`-polymorphic spec (`IsMinRes'`) also elaborates but loses `Submodule.map A` and dot
   notation, so do not. `WithEnergy` needs `→ₗ` only (R1). Provide `@[simp]` coercion lemmas for
   `Krylov.subspace`, `Arnoldi.vec`, `IsMinRes` with `→L` arguments; the finite-dimensional surface
   uses `LinearMap.toContinuousLinearMap`.
2. **`RCLike` vs real.** Keep `RCLike 𝕜` with `RCLike.re` (Mathlib's own convention:
   `LinearMap.IsPositive := IsSymmetric ∧ ∀ x, 0 ≤ re ⟪T x, x⟫`, `ContinuousLinearMap.reApplyInnerSelf`).
   Do **not** add real `abbrev`s in the backbone; the surface states real theorems and
   `RCLike.re_to_real` normalizes. Two rules: `open scoped ComplexOrder` whenever `Matrix.PosDef`
   or `spectrum 𝕜 A ⊆ Icc` appears (R2), and never compare a `𝕜`-valued eigenvalue with a real
   interval (R3).
3. **Spectral hypotheses.** Quadratic-form bounds bundled as `LinearMap.IsSymmetricBoundedBy A lmin lmax`
   (R3), with the L3 equivalence to eigenvalue bounds. No CFC in phase 1; record the compression
   trick (5.2.3) as the phase-1 route to the Hilbert-space CG bound and CFC as phase 2.
4. **Grade.** `grade := finrank (fullSubspace A v)` with `[FiniteDimensional K (fullSubspace A v)]`
   (R4). Not `ℕ∞`, no `Fact`.
5. **Matrix layer.** A small Givens API is acceptable and needed by three sources, but index the
   recurrences by `ℕ` and make it non-blocking by deriving `‖r^G_m‖ = |s_m| ‖r^G_{m−1}‖` from 3.6 with
   `s_m` *defined* as the residual ratio (R11). GMRES's least-squares definition needs no Givens.
6. **Surface fidelity.** Yes, state only what the book proves — but GMRES(m) satisfies a per-cycle
   spec, so Thm 6.30 is backbone (R14); only truncated methods are algorithm-only.
7. **Prototypes.** Keep until the skeleton builds; fix R5 now; add "✓ = elaborates" (R20).

---

## (F) Mathlib findings table

| Plan item | Mathlib (`v4.34.0-rc2`) | Verdict |
|---|---|---|
| 2.1.1 `‖(1−t)⁻¹‖ ≤ 1/(1−‖t‖)` | `NormedRing.tsum_geometric_of_norm_lt_one`, `geom_series_mul_neg`, `NormedRing.inverse_one_sub`, `Units.oneSub` | two-line corollary (R13) |
| 2.1.1 `‖(x+t)⁻¹‖`, `‖(x+t)⁻¹ − x⁻¹‖` bounds | only asymptotic: `NormedRing.inverse_add_norm_diff_first_order`, `inverse_one_sub_norm` (`=O`), `Units.add`, `Units.ofNearby` | add |
| 2.1.2 `condNumber` | none (LeanSearch: only `norm_inv`) | add |
| 2.1.3 `ρ<1 ↔ aⁿ→0` | ingredients: `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (alias `gelfand_formula`), `spectrum.spectralRadius_pow_le`, `spectrum.spectralRadius_le_nnnorm`, `spectrum.spectralRadius_lt_of_forall_lt`, `spectrum.exists_nnnorm_eq_spectralRadius`, `NormedRing.summable_geometric_of_norm_lt_one`, `HasSummableGeomSeries` | add (ℂ only, R8) |
| 2.1.4 operator coercivity | none. Related: root `IsCoercive` = real bilinear forms only (`Analysis/Normed/Operator/NormedSpace.lean:319`); `LinearMap.IsPositive`, `ContinuousLinearMap.IsPositive`, `ContinuousLinearMap.reApplyInnerSelf`; `Matrix.PosDef` (needs `ComplexOrder`), `Matrix.PosSemidef.posDef_iff_isUnit` | add |
| 2.1.5 energy inner product | operator level: none; matrix level: `Matrix.toInnerProductSpace`, `Matrix.toNormedAddCommGroup`, `Matrix.toSeminormedAddCommGroup` (`Analysis/Matrix/PosDef.lean`), `Matrix.toMatrixInnerProductSpace` (`Analysis/Matrix/Order.lean`) | add; bridge to matrix version (R9) |
| 2.1.6 compression | none | add |
| 2.1.7 oblique projections / Kato | `LinearMap.IsSymmetricProjection`, `IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`, `IsIdempotentElem.isSymmetric_iff_orthogonal_range`, `LinearMap.IsSymmetric.orthogonal_range`; Kato `‖P‖=‖1−P‖`: none | add Kato |
| 2.1.8 degreeLT glue | `Polynomial.degreeLT`, `Polynomial.aeval`, `Module.AEval'`, `Polynomial.annIdeal` / `annIdealGenerator` (algebra elements) | add glue |
| 2.1.9 Chebyshev min–max (`p(0)=1`) | none; ingredients `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`, `leadingCoeff_le_of_forall_abs_le_one`, `abs_eval_T_real_le_one`, `one_lt_abs_eval_T_real`, `T_complex_cosh`; `T_neg` is index parity | add (R17) |
| 2.1.10 Hessenberg / tridiagonal / Givens | none (`Matrix.BlockTriangular` for triangular parts) | add |
| 2.1.11 complexify | `Matrix.map`, `Matrix.charpoly_map`, `Matrix.mem_spectrum_iff_isRoot_charpoly`, `Module.End.hasEigenvalue_iff_mem_spectrum` | add wrapper |
| 2.1.12 entrywise matrix order | none (Mathlib's `Matrix` order is Loewner, `Analysis/Matrix/Order.lean`) | add, scoped |
| Gershgorin, diagonal dominance | `eigenvalue_mem_ball`, `det_ne_zero_of_sum_row_lt_diag`, `det_ne_zero_of_sum_col_lt_diag` | reuse |
| Irreducible / primitive matrices | `Matrix.IsIrreducible`, `Matrix.IsPrimitive`, `Matrix.isIrreducible_iff_exists_pow_pos` | reuse; Perron–Frobenius: none |
| Schur triangulation | **none** (plan claims `Matrix.schur_triangulation`) | fix (R13) |
| Rayleigh quotient / extreme eigenvalues | `ContinuousLinearMap.rayleighQuotient`, `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`, `…_iInf_…`, `ContinuousLinearMap.spectralRadius_eq_nnnorm` | reuse |
| Courant–Fischer, Weyl, Bauer–Fike, Kantorovich, Bendixson, Kato–Temple | none | add |
| Symmetric-operator spectral theorem | `LinearMap.IsSymmetric.eigenvalues (hn : finrank 𝕜 E = n)`, `eigenvalues_antitone`, `hasEigenvalue_eigenvalues`, `eigenvectorBasis` | reuse |
| Hermitian matrices | `Matrix.IsHermitian.eigenvalues`, `eigenvalues₀`, `eigenvalues₀_antitone`, `spectrum_real_eq_range_eigenvalues`, `spectral_theorem` | reuse |
| Lax–Milgram | real only: `IsCoercive.continuousLinearEquivOfBilin`, `.bounded_below`, `.antilipschitz`, `.ker_eq_bot`, `.isClosed_range`, `.range_eq_top`; `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective` | add complex version (D11) |
| Dimension formula | `Submodule.finrank_sup_add_finrank_inf_eq` | reuse (name fixed) |
| Gram–Schmidt | `InnerProductSpace.gramSchmidtNormed`, `gramSchmidtNormed_orthonormal'`, `span_gramSchmidt_Iic`, `gramSchmidt_ne_zero_coe`, `gramSchmidtOrthonormalBasis` | reuse |
| Krylov subspaces, Arnoldi, Lanczos | none (LeanSearch: nothing) | add |
| Newton's method (analytic) | none (`Polynomial.newtonMap` is algebraic) | add |
| Banach fixed point | `ContractingWith.*`, `efixedPoint'` | reuse |
| Singular values, LDL | `LinearMap.singularValues`, `Matrix.LDL` | reuse |
| Fredholm / compact | `ContinuousLinearMap.IsFredholm`, `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` | reuse |
| Mean value / Taylor remainder | `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` | reuse (D15) |
| Generalized eigenspaces | `Module.End.iSup_maxGenEigenspace_eq_top` | reuse (D14) |
| `RCLike` order | `RCLike.toPartialOrder`, `RCLike.toStarOrderedRing` — scoped `ComplexOrder` | must open (R2) |
| Floating point | `Mathlib/Data/FP/Basic.lean` definitions only | none |

---

## (G) Notes on future-book extensibility

* **Choi (singular systems, MINRES-QLP).** `IsMinRes` survives singular `A` (existence via
  projection, residual unique); `IsMinError` does not (R5) — parametrize by the target `xstar`.
  Fix now the shape of `Krylov.IsMinNormMinResIterate` as `IsLeast` of `‖·‖` on the `IsMinRes` set.
  Mathlib has no Moore–Penrose pseudoinverse for operators (only `LinearMap.singularValues`); state
  Choi Thm 2.25/2.27 as "minimum-norm solution" / "`{2,3}`-inverse" properties, not via `A†`.
  Lanczos (3.3) correctly assumes only `IsSymmetric` — keep it so (Choi's `A` is indefinite and
  singular). The residual/`‖A r_k‖` recurrences (3.5) should be `ℕ`-indexed (R11).
* **Meurant–Strakoš.** Needs `Lanczos.alpha beta : ℕ → ℝ` (already) → Jacobi matrices → orthogonal
  polynomials and Gauss quadrature; the L3 spectral measure is a finite sum, so no measure theory.
  The `finrank`-grade (R4) and `compression` are exactly their Vorobyev moment problem. HS 6:1/6:3
  are local identities (3.7) — good.
* **Saad-eig.** `IsRitzPair`, `LinearMap.compression`, `Arnoldi.hessenbergSq_eq_toMatrix_compression`
  (skeleton) are the right bridges; Courant–Fischer (D16) is the one big missing brick, and Schur
  form is *not* in Mathlib (R13). The R3 bundle gives Kaniel–Paige–Saad's hypotheses for free.
* **Kress.** Banach-space statements fit L2; direct methods (LU/QR/SVD factorizations) are Mathlib
  gaps — reserve `ForMathlib/Matrix/{LU,QR}` names now so Trefethen–Bau and Higham land in the same
  place. Kress's `κ` for rectangular matrices (`σ_max/σ_min`) is not `NormedRing.condNumber`;
  reserve `Matrix.condNumber₂` via singular values.
* **Higham.** `Fl.RoundingModel` as a *relation* is right (R15); the entrywise matrix order (2.1.12)
  must be scoped to avoid the Loewner instance. Do not contort phase 1 to fit
  `Arnoldi.IsPerturbedRelation`; write exact statements against `Arnoldi.vec`/`coeff` and derive
  the `ε = 0` instance later.
* **Greenbaum, Liesen–Strakoš, Trefethen–Bau.** All want complex matrices on `Fin n`, the polynomial
  characterization (3.4) and the cyclic-subspace/minimal-polynomial view (R4); Greenbaum–Pták–Strakoš
  ("any GMRES curve is possible") is a matrix construction → surface. Trefethen–Bau's "Arnoldi =
  polynomial approximation" is `Arnoldi.charpoly_compression_isMinOn` (4.2).
* **Brenner–Scott / Ern–Guermond.** The variational layer (5.2) on abstract Hilbert spaces is right;
  R9 (energy structure on unbundled forms) is the single change that prevents a second `WithEnergy`
  and duplicated Céa lemmas; Sobolev spaces remain the Mathlib gap.
* **Nocedal–Wright.** State `isGalerkin_iff_isMinOn_quadratic` with Mathlib's `IsMinOn` on
  `{y | y - x₀ ∈ K}` so line-search vocabulary matches; "conjugate directions = Gram–Schmidt in
  `WithEnergy`" (available with the R1 pattern) is the bridge to their Thm 5.1–5.3.
* **General.** Every spec is quantified over an arbitrary iterate sequence — this is what makes all
  of the above cheap; protect it by never letting a recurrence (`CG.step`, `CR.step`) appear in a
  theorem hypothesis where the spec would do.
