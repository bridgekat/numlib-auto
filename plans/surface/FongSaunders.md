# Surface plan: Fong–Saunders (2012)

Paper: D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU J. Sci.
17:1 (2012) 44–62 (Report SOL 2011-2R; surface docstrings cite the SQU version). Setting: a real
symmetric positive definite `n × n` system `A x = b`, `x₀ = 0`, 2-norm for vectors, Frobenius norm
for matrices. Mathematical content: (§1) Lanczos/Krylov setting; (§2) the CG/CR pseudocode of
Table 2.1, the minimization characterizations of CG and MINRES, the CR sign lemmas Thm 2.1–2.2, and
the monotonicity theorems Thm 2.3–2.5 for CR (hence MINRES); (§3) normwise relative backward error
(3.1)–(3.6), the stopping rule (3.4), Thm 3.1; (§4.1.1) the FOM/GMRES-type relation (4.1); (§4.2)
Steihaug's indefinite-case monotonicity and its CR analogue; (§5) Table 5.1.
Lean files: `Surface/FongSaunders/Sec1.lean` (setting), `Sec2.lean`, `Sec3.lean`, `Sec4.lean`
(only (4.1), the telescoping identity, §4.2), `Sec5.lean` (Table 5.1 as a structure). Numerical-only
material (§4 experiments, Figures 4.1–4.8, the MINRES-QLP heuristic in §4.2, Table 5.2, §5 prose) is
left out (section "Left out" below). Count: 26 result blocks; two deferred backbone items (both
from §4.2). Backbone dependencies: `plans/backbone.md` §2.1.4–2.1.5, §2.2, §2.4, §3.1–3.8, §3.11,
§8.2.

Conventions used below. `n : ℕ`; `Vec n := EuclideanSpace ℝ (Fin n)`; `A : Matrix (Fin n) (Fin n) ℝ`
with standing hypothesis `hA : A.PosDef` (Mathlib's `Matrix.PosDef`, which for `ℝ` is "symmetric
and `xᵀ A x > 0` for `x ≠ 0`"); `b : Vec n`; `A ⬝ x := Matrix.toEuclideanLin A x` (scoped infix, the
surface's matrix–vector product on Euclidean vectors); `⟪x, y⟫_ℝ` is `xᵀ y`; `‖x‖` on `Vec n` is the
2-norm; `‖A‖` is the Frobenius norm via `open scoped Matrix.Norms.Frobenius`. Backbone declarations
are cited by name together with their module under `Numlib/`; parenthesized section numbers refer
to `plans/backbone.md`. Backbone statements are about an operator `A : E →ₗ[𝕜] E`; the surface
instantiates `𝕜 = ℝ`, `E = Vec n`, `A := toEuclideanLin A`, `x₀ = 0`, so the backbone's instance
hypotheses `[FiniteDimensional 𝕜 E]` and `[FiniteDimensional 𝕜 (Krylov.fullSubspace …)]` are
automatic and `RCLike.re` disappears (`RCLike.re_to_real`).

Classification of each result block: `direct` = a backbone or Mathlib theorem applies after
rewriting with the equivalence lemmas of the definitions section; `needs-equivalence` = the
mathematics is in the backbone but a surface bridging lemma (named in the block) is required;
`surface-only` = proved in the surface from Mathlib; `deferred` = depends on a backbone item listed
under "Deferred backbone items".

## Paper-specific definitions

Each block: paper formulation → Lean surface definition → backbone counterpart → equivalence lemma.

### D1. Vectors, matrices, norms (§1.1)
* Paper: real `n × n` spd `A`, `‖v‖` the 2-norm, `‖A‖` the Frobenius norm, `A ≻ 0` means spd.
* Lean: `abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)`;
  `noncomputable abbrev mulVecE (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Vec n := Matrix.toEuclideanLin A x`,
  `scoped infixr:73 " ⬝ " => mulVecE`; `A ≻ 0` is `A.PosDef`.
* Backbone: `LinearMap.IsSymmetricCoercive` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`, §2.1.4);
  matrix glue `Matrix.toEuclideanLin_one`, `Matrix.toEuclideanLin_mul`, `Matrix.toEuclideanLin_pow`,
  `Matrix.l2_opNorm_eq_norm_toEuclideanLin` (`Numlib/Analysis/Matrix/ToEuclideanLin.lean`).
* Equivalence: `Matrix.posDef_iff_isSymmetricCoercive (M) : M.PosDef ↔ (toEuclideanLin M).IsSymmetricCoercive`
  (`Numlib/Analysis/InnerProductSpace/Coercive.lean`). Surface glue lemmas (trivial `simp`/`rfl`, in `Sec1.lean`):
  `mulVecE_add`, `mulVecE_smul`, `mulVecE_zero`,
  `inner_mulVecE : ⟪x, A ⬝ y⟫_ℝ = x.ofLp ⬝ᵥ (A *ᵥ y.ofLp)` (unfold `Matrix.toEuclideanLin`,
  `EuclideanSpace.inner_eq_star_dotProduct`),
  `inner_mulVecE_comm (hA : A.IsSymm) : ⟪x, A ⬝ y⟫_ℝ = ⟪A ⬝ x, y⟫_ℝ`,
  `isSymm_of_posDef (hA : A.PosDef) : A.IsSymm` (`hA.1` with Mathlib's `Matrix.isHermitian_iff_isSymm`),
  `isSymmetric_toEuclideanLin (hA : A.IsSymm) : (toEuclideanLin A).IsSymmetric`
  (Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`),
  `mulVecE_pow : (A ^ i) ⬝ x = (toEuclideanLin A ^ i) x` (from `Matrix.toEuclideanLin_pow`).

### D2. Krylov subspace and the Lanczos objects (§1)
* Paper: `𝒦_k(A, b) = span{b, A b, …, A^(k−1) b}`; Lanczos with starting vector `b` gives
  `V_k = (v_1 … v_k)` orthonormal, `T_k` of size `(k+1) × k` tridiagonal with `A V_k = V_{k+1} T_k`
  for `k = 1, …, ℓ`, `A V_ℓ = V_ℓ T_ℓ` for some `ℓ ≤ n`; iterates `x_k = V_k y_k`.
* Lean: `noncomputable def krylov (A) (b) (k : ℕ) : Submodule ℝ (Vec n) := Submodule.span ℝ (Set.range fun i : Fin k => (A ^ (i : ℕ)) ⬝ b)`;
  Lanczos vectors are *not* redefined: `lanczosVec A b j := Arnoldi.vec (toEuclideanLin A) b j`
  (paper's `v_{j+1}`; index shift by one), `lanczosT A b k := Lanczos.tridiagExt (toEuclideanLin A) b k`
  (the `(k+1) × k` matrix `T̲_k`), `lanczosTsq A b k := Lanczos.tridiag (toEuclideanLin A) b k` (the
  square `T_k`), `lanczosTerm A b := Krylov.grade (toEuclideanLin A) b` (the paper's `ℓ`).
* Backbone: `Krylov.subspace` (notation `𝒦[A, v] m`), `Krylov.grade`, `Krylov.grade_le_finrank`
  (`Numlib/Krylov/Subspace.lean`, §3.1); `Arnoldi.vec`, `Arnoldi.span_vec`, `Arnoldi.apply_sum`,
  `Arnoldi.orthonormal` (`Numlib/Krylov/Arnoldi.lean`, §3.2); `Lanczos.tridiag`, `Lanczos.tridiagExt`,
  `Lanczos.hessenberg_eq_map_tridiagExt`, `Lanczos.apply_sum_grade` (`Numlib/Krylov/Lanczos.lean`, §3.3);
  `Matrix.krylov_subspace_toEuclideanLin` (`Numlib/Analysis/Matrix/ToEuclideanLin.lean`).
* Equivalence: `krylov_eq : krylov A b k = Krylov.subspace (toEuclideanLin A) b k` is
  `Matrix.krylov_subspace_toEuclideanLin` read backwards (`mulVecE` unfolds to `toEuclideanLin (A ^ i) b`);
  `mem_krylov_iff_exists_lanczos (k) : x ∈ krylov A b k ↔ ∃ y : Fin k → ℝ, x = ∑ j, y j • lanczosVec A b j`
  (from `Arnoldi.span_vec` + `Submodule.mem_span_range_iff_exists_fun`; valid for every `k`, the
  vectors beyond `ℓ` being `0`), which is the paper's "`x_k = V_k y_k`".

### D3. The exact solution `x*` (§1.1)
* Paper: the unique solution `x*` of `A x = b`.
* Lean: state theorems with a variable `(xstar : Vec n) (hstar : A ⬝ xstar = b)`; provide
  `noncomputable def xstar (A) (b) : Vec n := A⁻¹ ⬝ b` with `mulVecE_xstar (hA) : A ⬝ xstar A b = b`
  and `xstar_unique (hA) (h : A ⬝ x = b) : x = xstar A b`.
* Backbone: none needed (Mathlib `Matrix.PosDef.isUnit`, `Matrix.mulVec_mulVec`, `Matrix.nonsing_inv_mul`;
  alternatively `LinearMap.IsCoercive.injective` of `Numlib/Analysis/InnerProductSpace/Coercive.lean` plus
  finite dimension).
* Equivalence: `xstar_unique` as above.

### D4. The quadratic form `φ` and the energy norm (§2.1)
* Paper: `φ(x) = ½ xᵀ A x − bᵀ x`; `‖x* − x_k‖_A` (written in §2.1 as `(x* − x_k)ᵀ A (x* − x_k)`,
  see C3 — we take the norm, `√(vᵀ A v)`; every statement below is invariant under squaring).
* Lean: `noncomputable def phi (A) (b) (x : Vec n) : ℝ := (1/2) * ⟪x, A ⬝ x⟫_ℝ - ⟪b, x⟫_ℝ`;
  `noncomputable def energyNorm (A) (v : Vec n) : ℝ := Real.sqrt ⟪v, A ⬝ v⟫_ℝ` (scoped notation `‖v‖_A`).
* Backbone: `energyNorm (A : E →ₗ[𝕜] E) x = √(re ⟪A x, x⟫)` and
  `LinearMap.IsSymmetricCoercive.energyNorm_sq` (`Numlib/Analysis/InnerProductSpace/Energy.lean`, §2.1.5); the
  quadratic `re⟪A x, x⟫/2 − re⟪b, x⟫` of `IsGalerkin.quadratic_le`
  (`Numlib/LinearSolve/Projection/Optimality.lean`, §2.4.2).
* Equivalence: `energyNorm_eq : energyNorm A v = _root_.energyNorm (toEuclideanLin A) v`
  (`RCLike.re_to_real`, `real_inner_comm`); `phi_eq : phi A b x = re⟪(toEuclideanLin A) x, x⟫/2 − re⟪b, x⟫` (`ring`).

### D5. Algorithm CG (Table 2.1, column 1)
* Paper: Initialize `x = 0, r = b, ρ = ‖r‖², p = r`. Repeat: `q = A p; α = ρ / pᵀ q; x ← x + α p;
  r ← r − α q; ρ̄ = ρ, ρ = rᵀ r; β = ρ/ρ̄; p ← r + β p`. Terminate when `r = 0` (`⇒ ρ = β = 0`).
* Lean:
  ```lean
  structure CGState (n : ℕ) where (x r : Vec n) (ρ : ℝ) (p : Vec n)
  noncomputable def cgStep (A) (s : CGState n) : CGState n :=
    let q := A ⬝ s.p
    let α := s.ρ / ⟪s.p, q⟫_ℝ
    let x := s.x + α • s.p
    let r := s.r - α • q
    let ρ := ⟪r, r⟫_ℝ
    let β := ρ / s.ρ
    { x := x, r := r, ρ := ρ, p := r + β • s.p }
  noncomputable def cgInit (b : Vec n) : CGState n := { x := 0, r := b, ρ := ‖b‖ ^ 2, p := b }
  noncomputable def cg (A) (b) (k : ℕ) : CGState n := (cgStep A)^[k] (cgInit b)
  noncomputable def cgAlpha (A) (b) : ℕ → ℝ            -- α_k = ρ_{k−1} / p_{k−1}ᵀ q_{k−1}, α_0 := 0 (junk)
    | 0 => 0 | k + 1 => (cg A b k).ρ / ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ
  noncomputable def cgBeta (A) (b) : ℕ → ℝ             -- β_k = ρ_k / ρ_{k−1}, β_0 := 0
    | 0 => 0 | k + 1 => (cg A b (k + 1)).ρ / (cg A b k).ρ
  /-- termination index `ℓ` -/
  noncomputable def cgTerm (A) (b) : ℕ := sInf {k | (cg A b k).r = 0}
  ```
  Lean's `0/0 = 0` makes the recurrence stationary after termination (`r = 0 ⇒ ρ = 0 ⇒ α = β = 0 ⇒ p = 0`),
  exactly the paper's "termination", so no `Option`/partiality is needed.
* Backbone (`Numlib/Krylov/CG.lean`, §3.7): `CG.State` (fields `x r p`), `CG.alpha A s = ⟪r, r⟫/⟪A p, p⟫`,
  `CG.beta A s = ⟪r', r'⟫/⟪r, r⟫`, `CG.step` (unfolding lemmas `CG.step_x`, `CG.step_r`), `CG.init A b x₀`,
  `CG.iterate A b x₀ k`, `CG.iterate_succ`, `CG.residual_eq`.
* Equivalence: `cg_eq_backbone (k) : (cg A b k).x = (CG.iterate (toEuclideanLin A) b 0 k).x ∧ (cg A b k).r = (…).r ∧ (cg A b k).p = (…).p ∧ (cg A b k).ρ = ‖(cg A b k).r‖ ^ 2`
  by induction on `k` (`Function.iterate_succ_apply'`, `map_zero`, `sub_zero`, `real_inner_self_eq_norm_sq`,
  `real_inner_comm`); `cgAlpha_eq (k) : cgAlpha A b (k+1) = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k)`
  and `cgBeta_eq` likewise with `CG.beta`.

### D6. Algorithm CR (Table 2.1, columns 2–3)
* Paper (indexed form): `x_0 = 0, r_0 = b, s_0 = A r_0, ρ_0 = r_0ᵀ s_0, p_0 = r_0, q_0 = s_0`; for
  `k = 1, 2, …`: `(q_{k−1} = A p_{k−1})`, `α_k = ρ_{k−1}/‖q_{k−1}‖²`, `x_k = x_{k−1} + α_k p_{k−1}`,
  `r_k = r_{k−1} − α_k q_{k−1}`, `s_k = A r_k`, `ρ_k = r_kᵀ s_k`, `β_k = ρ_k/ρ_{k−1}`, `p_k = r_k + β_k p_{k−1}`,
  `q_k = s_k + β_k q_{k−1}`. Termination at `k = ℓ ≤ n` with `r_ℓ = 0` (`⇒ ρ_ℓ = β_ℓ = 0`, `r_ℓ = s_ℓ = p_ℓ = q_ℓ = 0`).
* Lean:
  ```lean
  structure CRState (n : ℕ) where (x r s : Vec n) (ρ : ℝ) (p q : Vec n)
  noncomputable def crStep (A) (st : CRState n) : CRState n :=
    let α := st.ρ / ‖st.q‖ ^ 2
    let x := st.x + α • st.p
    let r := st.r - α • st.q
    let s := A ⬝ r
    let ρ := ⟪r, s⟫_ℝ
    let β := ρ / st.ρ
    { x := x, r := r, s := s, ρ := ρ, p := r + β • st.p, q := s + β • st.q }
  noncomputable def crInit (A) (b) : CRState n :=
    { x := 0, r := b, s := A ⬝ b, ρ := ⟪b, A ⬝ b⟫_ℝ, p := b, q := A ⬝ b }
  noncomputable def cr (A) (b) (k : ℕ) : CRState n := (crStep A)^[k] (crInit A b)
  noncomputable def crAlpha (A) (b) : ℕ → ℝ | 0 => 0 | k + 1 => (cr A b k).ρ / ‖(cr A b k).q‖ ^ 2
  noncomputable def crBeta  (A) (b) : ℕ → ℝ | 0 => 0 | k + 1 => (cr A b (k + 1)).ρ / (cr A b k).ρ
  /-- termination index `ℓ` -/
  noncomputable def crTerm (A) (b) : ℕ := sInf {k | (cr A b k).r = 0}
  ```
* Backbone (`Numlib/Krylov/CR.lean`, §3.8): `CR.State` (fields `x r p q`), `CR.alpha A s = ⟪r, A r⟫/⟪q, q⟫`,
  `CR.step` (with `β := ⟪r', A r'⟫/⟪r, A r⟫` and `q' := A r' + β • q` inline), `CR.init`, `CR.iterate`,
  `CR.iterate_succ`, `CR.residual_eq`, `CR.q_eq : q_k = A p_k` — the paper's recurrence verbatim.
* Equivalence: `cr_eq_backbone (k) : let s := cr A b k; let t := CR.iterate (toEuclideanLin A) b 0 k; s.x = t.x ∧ s.r = t.r ∧ s.p = t.p ∧ s.q = t.q ∧ s.s = A ⬝ s.r ∧ s.ρ = ⟪s.r, A ⬝ s.r⟫_ℝ`
  (induction on `k`; holds for every matrix `A`); the paper's remark "`q = A p` in both methods" is
  `cr_q_eq (k) : (cr A b k).q = A ⬝ (cr A b k).p` (from `CR.q_eq`);
  `cr_residual_eq (k) : (cr A b k).r = b - A ⬝ (cr A b k).x` (from `CR.residual_eq`);
  `crAlpha_eq (k) : crAlpha A b (k+1) = CR.alpha (toEuclideanLin A) (CR.iterate (toEuclideanLin A) b 0 k)`
  (`real_inner_self_eq_norm_sq`); `crBeta_succ (k) : crBeta A b (k+1) = (cr A b (k+1)).ρ / (cr A b k).ρ`
  (`rfl`; the backbone keeps this quotient inline in `CR.step`, so the sign of `β_k` is a surface
  corollary, R2.5 (b)). Termination indices: `crTerm_eq_grade (hA) : crTerm A b = Krylov.grade (toEuclideanLin A) b`
  (R2.3), likewise `cgTerm_eq_grade` and `cgTerm_eq_crTerm` — the paper's "Note: this `ℓ` is the same
  as the `ℓ` at which the Lanczos process terminates".

### D7. MINRES iterates (2.1)
* Paper: `x_k^M = V_k y_k^M`, `y_k^M = argmin_y ‖b − A V_k y‖`; "MINRES minimizes `‖r_k‖` within the
  `k`-th Krylov subspace" (for nonsingular, possibly indefinite `A`).
* Lean: `def IsMinresIterate (A) (b) (k : ℕ) (x : Vec n) : Prop := x ∈ krylov A b k ∧ ∀ y ∈ krylov A b k, ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖`.
  Theorems "for MINRES" quantify over `x : ℕ → Vec n` with `hx : ∀ k, IsMinresIterate A b k (x k)`
  (this is exactly the paper's "and hence MINRES", since the paper uses only the minimization property).
* Backbone: `Krylov.IsMinResIterate A b x₀ m x := IsMinRes A b x₀ (𝒦[A, b − A x₀] m) x`
  (`Numlib/Krylov/Iterate.lean`, §3.4); `IsMinRes` is a structure with fields `mem : x − x₀ ∈ K` and
  `min : ∀ y, y − x₀ ∈ K → ‖b − A x‖ ≤ ‖b − A y‖` (`Numlib/LinearSolve/Projection/Basic.lean`, §2.4.1).
* Equivalence: `isMinresIterate_iff : IsMinresIterate A b k x ↔ Krylov.IsMinResIterate (toEuclideanLin A) b 0 k x`
  (`map_zero`, `sub_zero`, `krylov_eq`); the literal `V_k y` form via `mem_krylov_iff_exists_lanczos` (D2).

### D8. CG as a minimizer (§2.1)
* Paper: `x_k^C = V_k y_k^C`, `y_k^C = argmin_y φ(V_k y)`, equivalently minimizing `‖x* − x_k‖_A` over `𝒦_k`.
* Lean: no new definition; stated as theorems R2.1 about `cg A b k` (D5) and as the predicate
  `IsMinOn (phi A b) (krylov A b k)`.
* Backbone: `Krylov.IsGalerkinIterate` (`Numlib/Krylov/Iterate.lean`, §3.4), `CG.isGalerkinIterate`
  (`Numlib/Krylov/CG.lean`), `IsGalerkin.quadratic_le`, `IsGalerkin.iff_energyNorm_min`,
  `IsGalerkin.energyNorm_le` (`Numlib/LinearSolve/Projection/Optimality.lean`, §2.4.2),
  `Krylov.IsGalerkinIterate.eq_CG_iterate` (`Numlib/Krylov/Monotonicity.lean`, §3.11).
* Equivalence: `isGalerkinIterate_iff_isMinOn_phi (hA) (hstar) : Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k x ↔ x ∈ krylov A b k ∧ IsMinOn (phi A b) (krylov A b k) x`.
  ⇒ is `quadratic_le` + `phi_eq`; ⇐ goes through `iff_energyNorm_min` and the surface identity
  `energyNorm_sq_eq_two_phi_add` (R2.1), which turns `IsMinOn (phi A b) K x` into
  `∀ y ∈ K, energyNorm A (xstar − x) ≤ energyNorm A (xstar − y)` (`Real.sqrt_le_sqrt`, `pow_le_pow_left`).

### D9. Backward error (3.1)–(3.3)
* Paper: `x_k` is *acceptable* iff `∃ E, f` with `(A + E) x_k = b + f`, `‖E‖/‖A‖ ≤ α`, `‖f‖/‖b‖ ≤ β`
  (`α, β ≥ 0`). The NRBE `ξ_k` is the optimal value of `min_{ξ,E,f} ξ` s.t. `(A+E) x_k = b + f`,
  `‖E‖/‖A‖ ≤ α ξ`, `‖f‖/‖b‖ ≤ β ξ`; with `r_k = b − A x_k` the optimum is
  `φ_k = β‖b‖/(α‖A‖‖x_k‖ + β‖b‖)`, `E_k = ((1 − φ_k)/‖x_k‖²) r_k x_kᵀ`, `ξ_k = ‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)`, `f_k = −φ_k r_k`.
* Lean (Frobenius norm on matrices):
  ```lean
  def IsAcceptable (A) (b) (α β : ℝ) (x : Vec n) : Prop :=
    ∃ (E : Matrix (Fin n) (Fin n) ℝ) (f : Vec n), (A + E) ⬝ x = b + f ∧ ‖E‖ / ‖A‖ ≤ α ∧ ‖f‖ / ‖b‖ ≤ β
  noncomputable def nrbe (A) (b) (α β : ℝ) (x : Vec n) : ℝ := ‖b - A ⬝ x‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖)
  noncomputable def nrbePhi (A) (b) (α β : ℝ) (x : Vec n) : ℝ := β * ‖b‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖)
  noncomputable def nrbePertA (A) (b) (α β) (x) : Matrix (Fin n) (Fin n) ℝ :=
    ((1 - nrbePhi A b α β x) / ‖x‖ ^ 2) • Matrix.vecMulVec (b - A ⬝ x).ofLp x.ofLp
  noncomputable def nrbePertb (A) (b) (α β) (x) : Vec n := -(nrbePhi A b α β x) • (b - A ⬝ x)
  ```
  The feasible set of the optimization problem is
  `nrbeFeasible A b α β x := {ξ : ℝ | ∃ E f, (A + E) ⬝ x = b + f ∧ ‖E‖ / ‖A‖ ≤ α * ξ ∧ ‖f‖ / ‖b‖ ≤ β * ξ}`.
* Backbone (`Numlib/LinearSolve/Perturbation.lean`, §2.2): `backwardError (A : E →L[𝕜] E) b y α β`,
  `isLeast_backwardError`, `exists_optimal_perturbation`, `backwardError_le_iff` — all with the
  *operator* norm on `E →L[𝕜] E` and the weights `α ‖A‖`, `β ‖b‖`. The Frobenius-norm form is
  surface-specific (§8.2: state both, and record that the rank-one optimal perturbation has equal
  operator and Frobenius norms).
* Equivalence: `nrbe_op_eq_backwardError : ‖b - A ⬝ x‖ / (α * ‖A‖₂ * ‖x‖ + β * ‖b‖) = backwardError (toEuclideanLin A).toContinuousLinearMap b x α β`
  (`Matrix.l2_opNorm_eq_norm_toEuclideanLin`, with `open scoped Matrix.Norms.L2Operator` locally) is the
  operator-norm twin of `nrbe`; `l2_opNorm_nrbePertA : ‖nrbePertA A b α β x‖₂ = ‖nrbePertA A b α β x‖`
  (rank one). The Frobenius statements themselves are R3.1–R3.4.

### D10. Steihaug's indefinite setting (§4.2)
* Paper: CG applied to a symmetric, possibly indefinite `A x = b` (notation of Table 2.1); the
  hypothesis is `p_jᵀ A p_j > 0` for all iterations `1 ≤ j ≤ k`; for CR/MINRES additionally `r_jᵀ A r_j > 0`.
* Lean: no new definition — the same `cg`/`cr` (D5–D6) with `hA' : A.IsSymm` instead of `A.PosDef`;
  the hypotheses are `∀ j < k, 0 < ⟪(cg A b j).p, A ⬝ (cg A b j).p⟫_ℝ` (directions `p_0, …, p_{k−1}` used
  in iterations `1..k`; see C5) and, for CR, also `∀ j < k, 0 < (cr A b j).ρ` (`ρ_j = r_jᵀ A r_j`).
* Backbone: `CG.norm_iterate_monotone` (`Numlib/Krylov/CG.lean`; spd, nonstrict) and
  `CR.isMinResIterate_of_no_breakdown (hA : A.IsSymmetric) (k) (h1 : ∀ j < k, ⟪r_j, A r_j⟫ ≠ 0) (h2 : ∀ j < k, q_j ≠ 0)`
  (`Numlib/Krylov/CR.lean`), which identifies the CR iterates with the MINRES iterates on symmetric
  indefinite systems while no breakdown occurs. The strict indefinite-case statements are the two
  deferred backbone items (R4.3, R4.4).
* Equivalence: `cg_eq_backbone` and `cr_eq_backbone` hold for every matrix (no `PosDef` needed), so
  the same lemmas serve.

### D11. Table 5.1 profile (§5)
* Paper: the five rows `‖x_k‖`, `‖x* − x_k‖`, `‖x* − x_k‖_A`, `‖r_k‖`, `‖r_k‖/‖x_k‖` with ↗/↘/"not-monotonic" for CG and MINRES.
* Lean:
  ```lean
  /-- Rows 1–3 of Table 5.1 for an iterate sequence. -/
  structure MonotoneProfile (A) (xstar : Vec n) (x : ℕ → Vec n) : Prop where
    norm_iterate      : Monotone fun k => ‖x k‖
    norm_error        : Antitone fun k => ‖xstar - x k‖
    energyNorm_error  : Antitone fun k => energyNorm A (xstar - x k)
  /-- All five rows (MINRES column). -/
  structure MinresProfile (A) (b) (xstar) (x : ℕ → Vec n) : Prop extends MonotoneProfile A xstar x where
    norm_residual     : Antitone fun k => ‖b - A ⬝ x k‖
    backwardError     : AntitoneOn (fun k => ‖b - A ⬝ x k‖ / ‖x k‖) (Set.Ici 1)
  ```
* Backbone: `Numlib/Krylov/CG.lean` (§3.7), `Numlib/Krylov/Monotonicity.lean` (§3.11); see R5.1.
* Equivalence: none (a restatement).

## Results

Numbering: `R<section>.<item>`; the paper's own labels are in the `Book statement` field.

### R1.1 — Lanczos relation and termination (§1, unnumbered setting)
* Book statement: The Lanczos process with starting vector `b` gives orthonormal `V_k` spanning `𝒦_k(A, b)`
  and tridiagonal `(k+1) × k` `T_k` with `A V_k = V_{k+1} T_k` for `k = 1, …, ℓ` and `A V_ℓ = V_ℓ T_ℓ` for some `ℓ ≤ n`.
* Lean surface statement:
  ```lean
  theorem lanczos_relation (hA) (k : ℕ) (y : Fin k → ℝ) :
      A ⬝ (∑ j, y j • lanczosVec A b j) = ∑ i : Fin (k+1), (lanczosT A b k).mulVec y i • lanczosVec A b i
  theorem lanczos_relation_term (hA) (y : Fin (lanczosTerm A b) → ℝ) :
      A ⬝ (∑ j, y j • lanczosVec A b j) = ∑ i, (lanczosTsq A b (lanczosTerm A b)).mulVec y i • lanczosVec A b i
  theorem lanczosVec_orthonormal : Orthonormal ℝ (fun j : Fin (lanczosTerm A b) => lanczosVec A b j)
  theorem span_lanczosVec (k) : span ℝ (lanczosVec A b '' Set.Iio k) = krylov A b k
  theorem lanczosTerm_le : lanczosTerm A b ≤ n
  ```
  (`lanczos_relation` holds for every `k`; beyond `ℓ` the extra Lanczos vectors are `0`.)
* Backbone item: `Arnoldi.apply_sum`, `Arnoldi.orthonormal`, `Arnoldi.span_vec` (`Numlib/Krylov/Arnoldi.lean`);
  `Lanczos.hessenberg_eq_map_tridiagExt`, `Lanczos.apply_sum_grade` (`Numlib/Krylov/Lanczos.lean`,
  hypothesis `A.IsSymmetric`); `Krylov.grade_le_finrank` (`Numlib/Krylov/Subspace.lean`).
* Proof route: `Arnoldi.apply_sum`, then rewrite `Arnoldi.hessenberg` as `tridiagExt` by
  `hessenberg_eq_map_tridiagExt` (symmetry from `isSymmetric_toEuclideanLin`, D1) and
  `algebraMap ℝ ℝ = RingHom.id` (`Matrix.map_id`); `finrank_euclideanSpace_fin` for `≤ n`.
* Classification: `needs-equivalence` (only the `map (algebraMap ℝ ℝ)` and `krylov_eq` rewrites).

### R1.2 — "`x_k = V_k y_k` for some `k`-vector `y_k`" (§1)
* Book statement: approximate solutions in `𝒦_k` are exactly the vectors `V_k y_k`.
* Lean surface statement: `mem_krylov_iff_exists_lanczos` (D2).
* Backbone item: `Arnoldi.span_vec` (`Numlib/Krylov/Arnoldi.lean`).
* Proof route: `Submodule.mem_span_range_iff_exists_fun` after `span_vec` (image of `Set.Iio k` as a range over `Fin k`).
* Classification: `direct`.

### R1.3 — Unique solution (§1.1)
* Book statement: `A x = b` has a unique solution `x*` (`A` spd).
* Lean surface statement: `theorem existsUnique_solution (hA) : ∃! x : Vec n, A ⬝ x = b`.
* Backbone item: none needed (Mathlib `Matrix.PosDef.isUnit`); alternatively `LinearMap.IsCoercive.injective`
  (`Numlib/Analysis/InnerProductSpace/Coercive.lean`) with `LinearMap.injective_iff_surjective`.
* Proof route: `posDef_iff_isSymmetricCoercive`, `IsCoercive.injective`, finite dimension.
* Classification: `direct`.

### R2.1 — CG minimizes `φ` and the energy-norm error (§2.1, unnumbered)
* Book statement: `x_k^C = V_k y_k^C` with `y_k^C = argmin_y φ(V_k y)`; with `b = A x*` and
  `2φ(x_k) = x_kᵀ A x_k − 2 x_kᵀ A x*` this is equivalent to minimizing `‖x* − x_k‖_A` within `𝒦_k`.
* Lean surface statement:
  ```lean
  theorem cg_mem_krylov (hA) (k) : (cg A b k).x ∈ krylov A b k
  theorem cg_isMinOn_phi (hA) (k) : IsMinOn (phi A b) (krylov A b k) (cg A b k).x
  theorem cg_energyNorm_le (hA) (hstar) (k) (y) (hy : y ∈ krylov A b k) :
      energyNorm A (xstar - (cg A b k).x) ≤ energyNorm A (xstar - y)
  theorem isMinOn_phi_iff_energyNorm_min (hA) (hstar) (x) (hx : x ∈ krylov A b k) :
      IsMinOn (phi A b) (krylov A b k) x ↔ ∀ y ∈ krylov A b k, energyNorm A (xstar - x) ≤ energyNorm A (xstar - y)
  theorem cg_unique_min (hA) (x) (hx : x ∈ krylov A b k) (hmin : IsMinOn (phi A b) (krylov A b k) x) :
      x = (cg A b k).x
  theorem two_phi_eq (hstar) : 2 * phi A b x = ⟪x, A ⬝ x⟫_ℝ - 2 * ⟪x, A ⬝ xstar⟫_ℝ
  theorem energyNorm_sq_eq_two_phi_add (hA) (hstar) :
      energyNorm A (xstar - x) ^ 2 = 2 * phi A b x + ⟪xstar, A ⬝ xstar⟫_ℝ
  ```
* Backbone item: `CG.isGalerkinIterate`, `CG.iterate_sub_mem` (`Numlib/Krylov/CG.lean`);
  `IsGalerkin.quadratic_le`, `IsGalerkin.iff_energyNorm_min`, `IsGalerkin.energyNorm_le`
  (`Numlib/LinearSolve/Projection/Optimality.lean`); `Krylov.IsGalerkinIterate.eq_CG_iterate`
  (`Numlib/Krylov/Monotonicity.lean`); `Krylov.existsUnique_isGalerkinIterate_of_isCoercive`
  (`Numlib/Krylov/Iterate.lean`).
* Proof route: `cg_eq_backbone` + `CG.isGalerkinIterate` give `IsGalerkinIterate`; `quadratic_le` + `phi_eq`
  give the `IsMinOn`; `iff_energyNorm_min` + `energyNorm_sq_eq_two_phi_add` give the equivalence;
  uniqueness is `eq_CG_iterate` after the ⇐ direction of D8's `isGalerkinIterate_iff_isMinOn_phi`.
* Classification: `needs-equivalence` (bridge `isGalerkinIterate_iff_isMinOn_phi`, built on the
  surface identity `energyNorm_sq_eq_two_phi_add`).

### R2.2 — MINRES minimizes `‖r_k‖`; CR and MINRES coincide on spd systems (§2.2, (2.1))
* Book statement: (2.1) defines MINRES; "MINRES minimizes `‖r_k‖` within the `k`-th Krylov subspace";
  CR also minimizes the residual for spd systems, "thus CR and MINRES must generate the same iterates on spd systems".
* Lean surface statement:
  ```lean
  theorem cr_isMinresIterate (hA) (k) : IsMinresIterate A b k (cr A b k).x
  theorem isMinresIterate_unique (hA) (k) {x y} (hx : IsMinresIterate A b k x) (hy : IsMinresIterate A b k y) : x = y
  theorem isMinresIterate_iff_eq_cr (hA) (k) (x) : IsMinresIterate A b k x ↔ x = (cr A b k).x
  theorem minres_norm_residual_le (hx : IsMinresIterate A b k x) (hy : y ∈ krylov A b k) :
      ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖   -- definitional
  ```
* Backbone item: `CR.isMinResIterate` (`Numlib/Krylov/CR.lean`); `Krylov.IsMinResIterate.eq_CR_iterate`
  (`Numlib/Krylov/Monotonicity.lean`); `Krylov.existsUnique_isMinResIterate_of_injective`
  (`Numlib/Krylov/Iterate.lean`); `LinearMap.IsCoercive.injective` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`).
* Proof route: `cr_eq_backbone` + `CR.isMinResIterate`; the ⇒ direction of `isMinresIterate_iff_eq_cr`
  is `eq_CR_iterate` through `isMinresIterate_iff`; uniqueness follows.
* Classification: `direct` (after D6/D7 equivalences).

### R2.3 — Well-definedness and termination of CG and CR (§2.3, unnumbered)
* Book statement: CG is well defined if `A` is spd; termination occurs when `r_k = 0` for some
  `k = ℓ ≤ n`, then `ρ_ℓ = β_ℓ = 0` and `r_ℓ = s_ℓ = p_ℓ = q_ℓ = 0`; this `ℓ` equals the Lanczos termination index.
* Lean surface statement:
  ```lean
  theorem cg_inner_p_q_pos (hA) (k) (hk : (cg A b k).r ≠ 0) : 0 < ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ
  theorem cr_rho_pos (hA) (k) (hk : (cr A b k).r ≠ 0) : 0 < (cr A b k).ρ
  theorem cg_residual_eq_zero_iff (hA) (k) : (cg A b k).r = 0 ↔ lanczosTerm A b ≤ k
  theorem cr_residual_eq_zero_iff (hA) (k) : (cr A b k).r = 0 ↔ lanczosTerm A b ≤ k
  theorem crTerm_eq_grade (hA) : crTerm A b = lanczosTerm A b   -- and `cgTerm_eq_grade`, `cgTerm_eq_crTerm`
  theorem crTerm_le (hA) : crTerm A b ≤ n
  theorem cr_term_state (hA) : let s := cr A b (crTerm A b)
      s.r = 0 ∧ s.s = 0 ∧ s.ρ = 0 ∧ s.p = 0 ∧ s.q = 0 ∧ crBeta A b (crTerm A b) = 0
  theorem cr_stationary (hA) (h : crTerm A b ≤ k) : cr A b k = cr A b (crTerm A b)
  ```
* Backbone item: `CG.re_inner_apply_direction_pos`, `CG.residual_eq_zero_of_grade_le`,
  `CG.residual_ne_zero_of_lt_grade`, `CG.iterate_eq_of_residual_eq_zero'` (`Numlib/Krylov/CG.lean`);
  `CR.residual_eq_zero_of_grade_le`, `CR.isMinResIterate` (`Numlib/Krylov/CR.lean`);
  `Krylov.grade_le_of_apply_eq` (`Numlib/Krylov/Iterate.lean`); `Krylov.grade_le_finrank`
  (`Numlib/Krylov/Subspace.lean`); `LinearMap.IsCoercive.inner_self_pos` (`Numlib/Analysis/InnerProductSpace/Coercive.lean`).
* Proof route: CG: `⇐` is `residual_eq_zero_of_grade_le`, `⇒` is the contrapositive of
  `residual_ne_zero_of_lt_grade`. CR: `⇐` is `CR.residual_eq_zero_of_grade_le`; for `⇒`, `r_k = 0`
  means `A x_k = b` with `x_k ∈ 𝒦_k` (`(CR.isMinResIterate …).mem`), so `Krylov.grade_le_of_apply_eq`.
  `crTerm_eq_grade` from the two directions and `Nat.sInf_def`; `cr_rho_pos` is coercivity
  (`inner_self_pos`, `real_inner_comm`); `cr_term_state` and `cr_stationary` are `simp [cr, crStep]`
  after `r_ℓ = 0` (`ρ_ℓ = 0`, so `α = 0`, `β_ℓ = 0/ρ_{ℓ−1} = 0`, `p_ℓ = q_ℓ = 0`, and the step is the
  identity by Lean's `x / 0 = 0`; for `ℓ = 0`, `b = 0` and every field is `0`).
* Classification: `needs-equivalence` (the CR converse `cr_residual_eq_zero_iff` is assembled from
  `CR.isMinResIterate` and `Krylov.grade_le_of_apply_eq`; the state equalities are surface computations).

### R2.4 — Theorem 2.1 (a), (b)
* Book statement: For Algorithm CR (spd `A`): (a) `q_iᵀ q_j = 0` for `i ≠ j`; (b) `r_iᵀ q_j = 0` for `i ≥ j + 1`.
* Lean surface statement:
  `theorem thm_2_1_a (hA) {i j : ℕ} (hij : i ≠ j) : ⟪(cr A b i).q, (cr A b j).q⟫_ℝ = 0`;
  `theorem thm_2_1_b (hA) {i j : ℕ} (hij : j + 1 ≤ i) : ⟪(cr A b i).r, (cr A b j).q⟫_ℝ = 0`.
* Backbone item: `CR.inner_apply_direction_eq_zero (h : i ≠ j) : ⟪A p_i, A p_j⟫ = 0`,
  `CR.inner_residual_apply_direction_eq_zero (h : j < i) : ⟪r_i, A p_j⟫ = 0`, `CR.q_eq` (`Numlib/Krylov/CR.lean`).
* Proof route: rewrite `q_i = A p_i` (`cr_q_eq`) and apply the backbone lemmas through `cr_eq_backbone`.
* Classification: `direct`.

### R2.5 — Theorem 2.2 (a)–(f)
* Book statement: For Algorithm CR on spd `A x = b`, `x_0 = 0`: (a) `α_i ≥ 0` (strict until `i = ℓ`,
  where `r_ℓ = 0`; via `ρ_i = r_iᵀ A r_i ≥ 0` (2.2)); (b) `β_i ≥ 0`; (c) `p_iᵀ q_j ≥ 0`; (d) `p_iᵀ p_j ≥ 0`;
  (e) `x_iᵀ p_j ≥ 0`; (f) `r_iᵀ p_j ≥ 0` (all `i, j`; readings C4, C6).
* Lean surface statement:
  ```lean
  theorem eq_2_2 (hA) (i) : 0 ≤ (cr A b i).ρ
  theorem eq_2_2_strict (hA) (hi : (cr A b i).r ≠ 0) : 0 < (cr A b i).ρ   -- = `cr_rho_pos`
  theorem thm_2_2_a (hA) (i) : 0 ≤ crAlpha A b i
  theorem thm_2_2_a_strict (hA) (hi : 1 ≤ i) (hℓ : i ≤ crTerm A b) : 0 < crAlpha A b i
  theorem thm_2_2_b (hA) (i) : 0 ≤ crBeta A b i
  theorem thm_2_2_c (hA) (i j) : 0 ≤ ⟪(cr A b i).p, (cr A b j).q⟫_ℝ
  theorem thm_2_2_d (hA) (i j) : 0 ≤ ⟪(cr A b i).p, (cr A b j).p⟫_ℝ
  theorem thm_2_2_e (hA) (i j) : 0 ≤ ⟪(cr A b i).x, (cr A b j).p⟫_ℝ
  theorem thm_2_2_f (hA) (i j) : 0 ≤ ⟪(cr A b i).r, (cr A b j).p⟫_ℝ
  ```
* Backbone item (`Numlib/Krylov/CR.lean`): `CR.re_alpha_nonneg` (a),
  `CR.re_inner_direction_apply_direction_nonneg` (c), `CR.re_inner_direction_nonneg` (d),
  `CR.re_inner_iterate_direction_nonneg` (e, for `x₀ = 0`), `CR.re_inner_residual_direction_nonneg` (f),
  `CR.inner_residual_apply_direction_eq_zero` (Thm 2.1 (b)); `LinearMap.IsCoercive.inner_self_pos`
  (`Numlib/Analysis/InnerProductSpace/Coercive.lean`) for (2.2).
* Proof route: (a), (c)–(f) through `cr_eq_backbone`, `crAlpha_eq`, `cr_q_eq` and `RCLike.re_to_real`.
  (2.2): `ρ_i = ⟪r_i, A r_i⟫ ≥ 0` by coercivity, `> 0` for `r_i ≠ 0`. (b): `β_i = ρ_i/ρ_{i−1}`
  (`crBeta_succ`) is a quotient of nonnegative reals (`div_nonneg`). Strict (a), the surface lemma
  `crAlpha_pos (hA) (hk : (cr A b k).r ≠ 0) : 0 < crAlpha A b (k+1)`: `α_{k+1} = ρ_k/‖q_k‖²` with
  `ρ_k > 0`, and `q_k ≠ 0` because `⟪r_k, q_k⟫ = ⟪r_k, A r_k⟫ + β_k ⟪r_k, A p_{k−1}⟫ = ρ_k > 0`
  (Thm 2.1 (b)). Its companion `cr_direction_ne_zero (hk : r_k ≠ 0) : p_k ≠ 0` follows from `q_k = A p_k`.
* Classification: `direct` for (a), (c)–(f); `needs-equivalence` for (2.2), (b) and the strict form
  (surface corollaries `eq_2_2`, `thm_2_2_b`, `crAlpha_pos` of coercivity and Thm 2.1 (b)).

### R2.6 — Theorem 2.3
* Book statement: For CR (and hence MINRES) on an spd system, `‖x_k‖` increases monotonically
  (the proof gives `‖x_i‖² − ‖x_{i−1}‖² ≥ 0`, i.e. nondecreasing; reading C1).
* Lean surface statement:
  `theorem thm_2_3_cr (hA) : Monotone fun k => ‖(cr A b k).x‖`;
  `theorem thm_2_3_minres (hA) (x : ℕ → Vec n) (hx : ∀ k, IsMinresIterate A b k (x k)) : Monotone fun k => ‖x k‖`;
  strict form `theorem thm_2_3_strict (hA) (hk : (cr A b k).r ≠ 0) : ‖(cr A b k).x‖ < ‖(cr A b (k+1)).x‖`.
* Backbone item: `CR.norm_iterate_monotone` (`Numlib/Krylov/CR.lean`);
  `Krylov.IsMinResIterate.norm_monotone` (`Numlib/Krylov/Monotonicity.lean`).
* Proof route: `cr_eq_backbone` resp. `isMinresIterate_iff` + `posDef_iff_isSymmetricCoercive`; the
  strict form from `‖x_{k+1}‖² − ‖x_k‖² = 2 α_{k+1} ⟪x_k, p_k⟫ + α_{k+1}² ‖p_k‖²` with Thm 2.2 (e),
  `crAlpha_pos` and `cr_direction_ne_zero` (R2.5).
* Classification: `direct` (nonstrict); `needs-equivalence` for the strict form (surface corollary
  `thm_2_3_strict`).

### R2.7 — Theorem 2.4
* Book statement: For CR (and hence MINRES) on an spd system, `‖x* − x_k‖` decreases monotonically
  (nonincreasing; the proof shows the difference of squares is `≥ 0`; reading C2).
* Lean surface statement:
  `theorem thm_2_4_cr (hA) (hstar : A ⬝ xstar = b) : Antitone fun k => ‖xstar - (cr A b k).x‖`;
  `theorem thm_2_4_minres (hA) (hstar) (x) (hx : ∀ k, IsMinresIterate A b k (x k)) : Antitone fun k => ‖xstar - x k‖`.
* Backbone item: `CR.norm_error_antitone` (`Numlib/Krylov/CR.lean`);
  `Krylov.IsMinResIterate.norm_error_antitone` (`Numlib/Krylov/Monotonicity.lean`).
* Proof route: as R2.6.
* Classification: `direct`.

### R2.8 — Theorem 2.5
* Book statement: For CR (and hence MINRES) on an spd system, `‖x* − x_k‖_A` is strictly decreasing
  (the proof gives `> 0` using Thm 2.2 (a), (c); strictness needs `α_k > 0`, i.e. `k ≤ ℓ`).
* Lean surface statement:
  ```lean
  theorem thm_2_5_cr (hA) (hstar) (k) (hk : (cr A b k).r ≠ 0) :
      energyNorm A (xstar - (cr A b (k+1)).x) < energyNorm A (xstar - (cr A b k).x)
  theorem thm_2_5_cr_antitone (hA) (hstar) : Antitone fun k => energyNorm A (xstar - (cr A b k).x)
  theorem thm_2_5_minres (hA) (hstar) (x) (hx) (hk : b - A ⬝ x k ≠ 0) :
      energyNorm A (xstar - x (k+1)) < energyNorm A (xstar - x k)
  ```
* Backbone item: `CR.energyNorm_error_antitone` (`Numlib/Krylov/CR.lean`);
  `Krylov.IsMinResIterate.energyNorm_error_antitone`, `Krylov.IsMinResIterate.eq_CR_iterate`
  (`Numlib/Krylov/Monotonicity.lean`); the sign lemmas of R2.5.
* Proof route: the nonstrict forms via `energyNorm_eq`. Strict form: with `e_k = x* − x_k` and
  `e_{k+1} = e_k − α_{k+1} p_k`, `‖e_k‖_A² − ‖e_{k+1}‖_A² = α_{k+1} (2 ⟪r_{k+1}, p_k⟫ + α_{k+1} ⟪p_k, q_k⟫)`
  (using `A e_k = r_k` and `r_k = r_{k+1} + α_{k+1} q_k`); the bracket is `≥ 0` by Thm 2.2 (f), (c) and
  `> 0` since `α_{k+1} > 0` (`crAlpha_pos`) and `⟪p_k, A p_k⟫ > 0` (`cr_direction_ne_zero` + coercivity).
  The MINRES form is the CR form after `eq_CR_iterate`.
* Classification: `direct` (nonstrict); `needs-equivalence` for the strict form (surface corollary
  `thm_2_5_cr` of the sign lemmas).

### R3.1 — (3.2)–(3.3): the optimal backward-error perturbation
* Book statement: For tolerances `α, β ≥ 0`, the optimization problem `min ξ` s.t. `(A + E) x_k = b + f`,
  `‖E‖/‖A‖ ≤ αξ`, `‖f‖/‖b‖ ≤ βξ` has optimal solution `ξ_k, E_k, f_k` given by (3.2)–(3.3) (`‖·‖` Frobenius on `E`).
* Lean surface statement:
  ```lean
  theorem nrbe_isLeast (α β) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
      IsLeast (nrbeFeasible A b α β x) (nrbe A b α β x)
  theorem nrbePert_attains (α β) (x) (hx : x ≠ 0) :
      (A + nrbePertA A b α β x) ⬝ x = b + nrbePertb A b α β x ∧
        ‖nrbePertA A b α β x‖ / ‖A‖ = α * nrbe A b α β x ∧ ‖nrbePertb A b α β x‖ / ‖b‖ = β * nrbe A b α β x
  ```
  Hypothesis note: `hden` (equivalently `(α, β) ≠ (0,0)` when `A, b, x ≠ 0`) is implicit in the paper; for `x = 0`
  (i.e. `k = 0`) the paper's `E_k` is undefined, Lean's `nrbePertA … 0 = 0` and the first conjunct still holds.
* Backbone item: `isLeast_backwardError`, `exists_optimal_perturbation` (`Numlib/LinearSolve/Perturbation.lean`,
  §2.2) are the operator-norm statements; the Frobenius form is surface-specific (§8.2).
* Proof route: lower bound: from `(A + E) ⬝ x = b + f`, `b − A ⬝ x = E ⬝ x − f`, so
  `‖r‖ ≤ ‖E‖ ‖x‖ + ‖f‖ ≤ ξ (α ‖A‖ ‖x‖ + β ‖b‖)` by the surface lemma
  `norm_mulVecE_le_frobenius : ‖E ⬝ x‖ ≤ ‖E‖ * ‖x‖` (Mathlib `Matrix.frobenius_norm_mul` applied to
  `E * Matrix.replicateCol Unit x.ofLp`, the one-column matrix of `x`, whose Frobenius norm is `‖x‖`).
  Attainment: `nrbePert_attains` by
  `frobenius_norm_vecMulVec : ‖Matrix.vecMulVec r.ofLp x.ofLp‖ = ‖r‖ * ‖x‖` (`Matrix.frobenius_norm_def`,
  `EuclideanSpace.norm_eq`, `Finset.sum_mul_sum`) and `field_simp`. The argument mirrors the backbone
  proof of `isLeast_backwardError` with the Frobenius norm in place of the operator norm.
* Classification: `surface-only` (the two surface norm lemmas are the only ingredients beyond Mathlib).

### R3.2 — Acceptable solution ⇔ `ξ_k ≤ 1` (§3, unnumbered)
* Book statement: `x_k` is an acceptable solution (3.1) iff `ξ_k ≤ 1`.
* Lean surface statement: `theorem isAcceptable_iff_nrbe_le_one (hα) (hβ) (hden) : IsAcceptable A b α β x ↔ nrbe A b α β x ≤ 1`.
* Backbone item: as R3.1.
* Proof route: `nrbe_isLeast` gives ⇒ (`1 ∈ nrbeFeasible`) and ⇐ (the optimal perturbation is
  feasible at `ξ = 1`; the constraints are monotone in `ξ`).
* Classification: `needs-equivalence` (bridge from R3.1's `IsLeast` to the `ξ = 1` membership).

### R3.3 — Stopping rule (3.4)
* Book statement: `ξ_k ≤ 1` iff `‖r_k‖ ≤ α‖A‖‖x_k‖ + β‖b‖` (the LSQR rule S1).
* Lean surface statement: `theorem nrbe_le_one_iff (α β) (x) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) : nrbe A b α β x ≤ 1 ↔ ‖b - A ⬝ x‖ ≤ α * ‖A‖ * ‖x‖ + β * ‖b‖`.
* Backbone item: `backwardError_le_iff` (`Numlib/LinearSolve/Perturbation.lean`) is the operator-norm twin.
* Proof route: `div_le_one hden`.
* Classification: `direct` (Mathlib).

### R3.4 — (3.5)–(3.6): norms of the optimal perturbations
* Book statement: `‖E_k‖ = (1 − φ_k) ‖r_k‖/‖x_k‖ = α‖A‖‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)`; `‖f_k‖ = φ_k ‖r_k‖ = β‖b‖‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)`.
* Lean surface statement (the last two conjuncts of `nrbePert_attains`, plus the intermediate forms):
  `theorem norm_nrbePertA (x) (hx : x ≠ 0) : ‖nrbePertA A b α β x‖ = (1 - nrbePhi A b α β x) * ‖b - A ⬝ x‖ / ‖x‖` and
  `theorem norm_nrbePertb (x) : ‖nrbePertb A b α β x‖ = nrbePhi A b α β x * ‖b - A ⬝ x‖` (needs `0 ≤ φ_k`, i.e. `hden` and `0 ≤ β`).
  The second equality in (3.5) requires `x ≠ 0` (at `k = 0` the paper's expression is `0/0`).
* Backbone item: none (Frobenius norm of a rank-one matrix is the surface lemma `frobenius_norm_vecMulVec`, R3.1).
* Proof route: `Matrix.frobenius_norm_def` + `EuclideanSpace.norm_eq` + `Finset.sum_mul_sum`; then `field_simp`.
* Classification: `surface-only`.

### R3.5 — `φ_k` decreases for CG and MINRES (§3.2, unnumbered remark)
* Book statement: since `‖x_k‖` is monotonically increasing for CG and MINRES, `φ_k` is monotonically decreasing for both solvers.
* Lean surface statement: `theorem nrbePhi_cg_antitone (hA) (hα : 0 ≤ α) (hβ : 0 ≤ β) : Antitone fun k => nrbePhi A b α β (cg A b k).x`;
  `theorem nrbePhi_minres_antitone (hA) (hα) (hβ) (hx : ∀ k, IsMinresIterate A b k (x k)) : Antitone fun k => nrbePhi A b α β (x k)`.
* Backbone item: `CG.norm_iterate_monotone` (`Numlib/Krylov/CG.lean`; Steihaug, spd),
  `Krylov.IsMinResIterate.norm_monotone` (`Numlib/Krylov/Monotonicity.lean`).
* Proof route: `div_le_div_of_nonneg_left` with the monotone denominator (constant numerator).
* Classification: `direct`.

### R3.6 — Theorem 3.1 and the monotone NRBE
* Book statement: Suppose `α > 0` and `β > 0`. For CR and MINRES (but not CG), the relative backward
  errors `‖E_k‖/‖A‖` and `‖f_k‖/‖b‖` decrease monotonically. (Implicitly, so does `ξ_k`; Table 5.1 row 5 lists `‖r_k‖/‖x_k‖ ↘ (Thm 3.1)`.)
* Lean surface statement:
  ```lean
  theorem thm_3_1_minres (hA) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 < β) (x) (hx : ∀ k, IsMinresIterate A b k (x k)) :
      AntitoneOn (fun k => ‖nrbePertA A b α β (x k)‖ / ‖A‖) (Set.Ici 1) ∧
        Antitone (fun k => ‖nrbePertb A b α β (x k)‖ / ‖b‖)
  theorem thm_3_1_cr …   -- same with `(cr A b k).x`
  theorem nrbe_minres_antitone (hA) (hb) (hα : 0 ≤ α) (hβ : 0 < β) (x) (hx) : Antitone fun k => nrbe A b α β (x k)
  theorem nrbe_minres_antitoneOn (hA) (hb) (hα : 0 < α) (hβ : 0 ≤ β) (x) (hx) :
      AntitoneOn (fun k => nrbe A b α β (x k)) (Set.Ici 1)   -- covers the `β = 0` form `‖r_k‖/‖x_k‖` of §4.1
  ```
  Why `Set.Ici 1` for `E_k` and for `β = 0`: at `k = 0`, `x_0 = 0` makes the paper's `E_0` undefined and Lean's `‖E_0‖ = 0`
  (also `‖r_0‖/‖x_0‖ = ‖b‖/0 = 0` under Lean's junk division), so a statement over all `k ≥ 0` is false in Lean; with `β > 0`
  the closed forms are finite at `k = 0` and `Antitone` on all of `ℕ` is correct. `hb : b ≠ 0` matches the
  backbone (for `b = 0` every iterate and every quantity is `0`). The "but not CG" clause is R5.2.
* Backbone item (`Numlib/Krylov/Monotonicity.lean`, §3.11):
  `Krylov.IsMinResIterate.backwardError_antitone (hx) {normA α β} (hα : 0 ≤ α) (hβ : 0 < β) (hnormA : 0 ≤ normA) (hb : b ≠ 0) : Antitone fun k => ‖b − A (x k)‖ / (α * normA * ‖x k‖ + β * ‖b‖)`
  — `normA` is a free real, so the Frobenius `‖A‖` is plugged in directly;
  `Krylov.IsMinResIterate.norm_residual_div_norm_antitoneOn (hx) (hb) : AntitoneOn (fun k => ‖b − A (x k)‖ / ‖x k‖) (Set.Ici 1)`;
  `Krylov.IsMinResIterate.norm_residual_antitone` (`Numlib/Krylov/Iterate.lean`); `CR.isMinResIterate`.
* Proof route: `nrbe_minres_antitone` is `backwardError_antitone` with `normA := ‖A‖` after
  `isMinresIterate_iff`; `nrbe_minres_antitoneOn`: for `β > 0` restrict the previous, for `β = 0` the
  function is `(α ‖A‖)⁻¹ • ‖r_k‖/‖x_k‖` and `norm_residual_div_norm_antitoneOn` applies (constant `0`
  if `‖A‖ = 0`); Thm 3.1 proper transports through (3.5)–(3.6) (R3.4): `‖E_k‖/‖A‖ = α ξ_k` for
  `x_k ≠ 0` and `‖f_k‖/‖b‖ = β ξ_k`. The surface lemma `minres_iterate_ne_zero (hk : 1 ≤ k) : x k ≠ 0`
  comes from `x_1 = α_1 b` with `α_1 = ⟪b, A b⟫/‖A b‖² > 0` (via `eq_CR_iterate`) and Thm 2.3.
* Classification: `direct` (the general-weight backbone form), with surface bookkeeping for (3.5)–(3.6)
  and for `x_k ≠ 0` on `Set.Ici 1`.

### R3.7 — MINRES stops no later than CG under rule (3.4) with `α = 0` (§1, §4 claim)
* Book statement: "with looser stopping tolerances, MINRES is sure to terminate sooner than CG when the
  stopping rule is based on the backward error" — rigorous only for `α = 0` (`‖r_k‖ ≤ β‖b‖`), which is the rule used in §4.
* Lean surface statement: `theorem minres_norm_residual_le_cg (hA) (k) (hx : IsMinresIterate A b k x) : ‖b - A ⬝ x‖ ≤ ‖(cg A b k).r‖`;
  `theorem minres_stops_first (hA) (β) (x) (hx) (k) (hcg : ‖(cg A b k).r‖ ≤ β * ‖b‖) : ‖b - A ⬝ x k‖ ≤ β * ‖b‖`
  (hence `Nat.find` of the MINRES stopping time `≤` that of CG).
* Backbone item: `Krylov.norm_residual_minRes_le_galerkin` (`Numlib/Krylov/Relations.lean`, §3.6) with
  `CG.isGalerkinIterate`; or the field `IsMinRes.min` with `CG.iterate_sub_mem` (`Numlib/Krylov/CG.lean`).
* Proof route: `hx.2 _ (cg_mem_krylov k)`.
* Classification: `direct`.

### R4.1 — Equation (4.1)
* Book statement: `‖r_k^C‖ = ‖r_k^M‖ / √(1 − ‖r_k^M‖²/‖r_{k−1}^M‖²)` (cited from Greenbaum Lemma 5.4.1 / Titley-Péloquin; implicitly `k ≥ 1`, `r_k^M ≠ 0`).
* Lean surface statement:
  `theorem eq_4_1 (hA) (k : ℕ) (hk : (cr A b (k+1)).r ≠ 0) : ‖(cg A b (k+1)).r‖ = ‖(cr A b (k+1)).r‖ / Real.sqrt (1 - ‖(cr A b (k+1)).r‖ ^ 2 / ‖(cr A b k).r‖ ^ 2)`;
  also in the `IsMinresIterate` form with `x (k+1)`, `x k`.
* Backbone item: `Krylov.inv_sq_norm_residual_minRes` (`1/‖r_{m+1}^G‖² = 1/‖r_m^G‖² + 1/‖r_{m+1}^F‖²`
  when `r_{m+1}^G ≠ 0`) and `Krylov.norm_residual_minRes_le_galerkin` (`Numlib/Krylov/Relations.lean`, §3.6);
  `CG.isGalerkinIterate`, `CR.isMinResIterate`. The Givens route `Krylov.IsMinResIterate.norm_residual_succ_eq`,
  `Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC`, `Krylov.norm_givensC_sq_add_norm_givensS_sq`
  (`Numlib/Krylov/Hessenberg.lean`, §3.5) gives the same identity through `|s_k|, |c_k|`.
* Proof route: with `r^C = r^F_{k+1}` and `r^M = r^G`, the identity gives
  `1/‖r^C‖² = (1 − ‖r^M_{k+1}‖²/‖r^M_k‖²)/‖r^M_{k+1}‖²`; `‖r^M_{k+1}‖ ≤ ‖r^C‖` and `r^M_{k+1} ≠ 0` give
  `r^C ≠ 0`, so the left side is positive and hence `‖r^M_{k+1}‖ < ‖r^M_k‖` (no separate strict-decrease
  lemma is needed); then `Real.sqrt` algebra (`Real.sqrt_inv`, `div_eq_iff`).
* Classification: `needs-equivalence` (surface algebra between the harmonic identity and the paper's form).

### R4.2 — Telescoping product (§4.1.1, unnumbered)
* Book statement: if the rule `‖r_k‖ ≤ β‖b‖` (rule (3.4) with `α = 0`) first holds at iteration `l`, then `∏_{k=1}^{l} ‖r_k‖/‖r_{k−1}‖ = ‖r_l‖/‖b‖` (`≈ β`).
* Lean surface statement: `theorem prod_ratio_residual (r : ℕ → Vec n) (hr0 : r 0 = b) (hne : ∀ k < l, r k ≠ 0) : ∏ k ∈ Finset.range l, ‖r (k+1)‖ / ‖r k‖ = ‖r l‖ / ‖b‖`.
* Backbone item: none (Mathlib `Finset.prod_range_div`).
* Proof route: telescoping.
* Classification: `direct` (Mathlib). The "`≈ β`" and "on average closer to 1" remarks are heuristics (left out).

### R4.3 — Steihaug's theorem for CG on indefinite systems (§4.2)
* Book statement: when CG is applied to a symmetric (possibly indefinite) `A x = b` (notation of Table 2.1, `x_0 = 0`),
  the solution norms `‖x_1‖, …, ‖x_k‖` are strictly increasing as long as `p_jᵀ A p_j > 0` for all iterations `1 ≤ j ≤ k`.
* Lean surface statement:
  `theorem steihaug_cg (A' : Matrix (Fin n) (Fin n) ℝ) (hA' : A'.IsSymm) (b) (k) (hpos : ∀ j < k, 0 < ⟪(cg A' b j).p, A' ⬝ (cg A' b j).p⟫_ℝ) : ∀ i < k, ‖(cg A' b i).x‖ < ‖(cg A' b (i+1)).x‖`
  (indexing per C5; strictness is justified since `p_iᵀ A p_i > 0 ⇒ p_i ≠ 0 ⇒ r_i ≠ 0 ⇒ α_{i+1} > 0`).
* Backbone item: deferred item 1 (`CG.norm_iterate_lt_of_re_inner_apply_direction_pos`, symmetric `A`);
  `CG.norm_iterate_monotone` (`Numlib/Krylov/CG.lean`) is the spd nonstrict case.
* Proof route (for the backbone item): `⟪r_i, p_j⟫ = ‖r_j‖²` for `i ≤ j`, hence `⟪p_i, p_j⟫ ≥ 0`, hence
  `⟪x_i, p_i⟫ ≥ 0`; a local argument needing only symmetry and the positivity of the denominators used so far.
* Classification: `deferred` (backbone item 1).

### R4.4 — The CR/MINRES analogue on indefinite systems (§4.2)
* Book statement: "From our proof of Theorem 2.2, we see that the same property holds for CR and MINRES as long as
  both `p_jᵀ A p_j > 0` and `r_jᵀ A r_j > 0` for all iterations `1 ≤ j ≤ k`."
* Lean surface statement (with the no-breakdown hypothesis discussed below):
  `theorem steihaug_cr (hA' : A'.IsSymm) (k) (hℓ : ∀ j < crTerm A' b, (cr A' b j).ρ ≠ 0) (hp : ∀ j < k, 0 < ⟪(cr A' b j).p, A' ⬝ (cr A' b j).p⟫_ℝ) (hr : ∀ j < k, 0 < (cr A' b j).ρ) : ∀ i < k, ‖(cr A' b i).x‖ < ‖(cr A' b (i+1)).x‖`.
* Backbone item: deferred item 2; `CR.isMinResIterate_of_no_breakdown` (`Numlib/Krylov/CR.lean`)
  identifies the CR iterates with the MINRES iterates under exactly these hypotheses, so the statement
  transfers to MINRES on indefinite systems.
* Proof route: **the paper's local formulation is not supported by its proof sketch.** The proof of
  Thm 2.2 (d) expands `p_i` in the complete orthogonal basis `{q_0, …, q_{ℓ−1}}` of `𝒬 = A 𝒦_ℓ`, which
  requires the CR recurrence to run to termination without breakdown (`ρ_j ≠ 0` for all `j < ℓ`, not
  only `j < k`); a purely local proof (hypotheses up to `k` only) is not given in the paper and may not
  exist (the component of `p_i` orthogonal to `span{q_0..q_{k−1}}` has no controlled sign). The surface
  therefore states the version with the global no-breakdown hypothesis `hℓ` (equivalently, both
  positivity conditions for all `j < ℓ`).
* Classification: `deferred` (backbone item 2).

### R4.5 — MINRES subproblem in Lanczos coordinates (§4.2, unnumbered)
* Book statement: MINRES (and MINRES-QLP) compute `x_k^M = V_k y_k^M` with `y_k^M = argmin_{y ∈ ℝ^k} ‖T̲_k y − β_1 e_1‖`
  (and possibly `T_ℓ y_ℓ^M = β_1 e_1`); when `A` is nonsingular or the system is consistent, `y_k^M` is uniquely defined for each `k ≤ ℓ`.
* Lean surface statement:
  ```lean
  theorem minres_subproblem (hA) (k) (hk : k ≤ lanczosTerm A b) (y : Fin k → ℝ) :
      IsMinresIterate A b k (∑ j, y j • lanczosVec A b j) ↔
        IsMinOn (fun z : Fin k → ℝ =>
          ‖(WithLp.toLp 2 (Krylov.firstVec (‖b‖ : ℝ) (k+1) - (lanczosT A b k).mulVec z) : Vec (k+1))‖) Set.univ y
  theorem minres_coeff_unique (hA) (k) (hk : k ≤ lanczosTerm A b) :
      ∃! y : Fin k → ℝ, IsMinresIterate A b k (∑ j, y j • lanczosVec A b j)
  ```
* Backbone item: `Krylov.isMinResIterate_iff_isMinOn` (hypothesis `m ≤ grade`), `Krylov.norm_residual_eq_norm_firstVec_sub_mulVec`,
  `Krylov.firstVec` (`Numlib/Krylov/Hessenberg.lean`, §3.5); `Lanczos.hessenberg_eq_map_tridiagExt`
  (`Numlib/Krylov/Lanczos.lean`); `Krylov.exists_isMinResIterate`, `Krylov.existsUnique_isMinResIterate_of_injective`
  (`Numlib/Krylov/Iterate.lean`); `Arnoldi.orthonormal` (linear independence of `v_0, …, v_{k−1}` for `k ≤ ℓ`).
* Proof route: `isMinResIterate_iff_isMinOn` with `x₀ = 0` (`zero_add`, `map_zero`, `sub_zero`), then
  `hessenberg_eq_map_tridiagExt` and `Matrix.map_id`; uniqueness of `y` from uniqueness of the iterate
  and linear independence of the Lanczos vectors; existence from `exists_isMinResIterate` and
  `mem_krylov_iff_exists_lanczos`.
* Classification: `needs-equivalence` (index bookkeeping `Fin k`/`Fin (k+1)` and the `tridiagExt` rewrite).

### R5.1 — Table 5.1 (the monotone entries)
* Book statement: on an spd system, for CG: `‖x_k‖ ↗` [Steihaug Thm 2.1], `‖x* − x_k‖ ↘` [HS Thm 4:3], `‖x* − x_k‖_A ↘` [HS Thm 6:3];
  for MINRES: `‖x_k‖ ↗` (Thm 2.3), `‖x* − x_k‖ ↘` (Thm 2.4), `‖x* − x_k‖_A ↘` (Thm 2.5), `‖r_k‖ ↘` [18; HS 7:2], `‖r_k‖/‖x_k‖ ↘` (Thm 3.1).
* Lean surface statement: `theorem cg_profile (hA) (hstar) : MonotoneProfile A xstar (fun k => (cg A b k).x)`;
  `theorem minres_profile (hA) (hb) (hstar) (x) (hx : ∀ k, IsMinresIterate A b k (x k)) : MinresProfile A b xstar x`;
  `theorem cr_profile (hA) (hb) (hstar) : MinresProfile A b xstar (fun k => (cr A b k).x)` (D11).
* Backbone item: CG column: `CG.norm_iterate_monotone`, `CG.norm_error_antitone`, `CG.energyNorm_error_antitone`
  (`Numlib/Krylov/CG.lean`; specification forms `Krylov.IsGalerkinIterate.norm_monotone`,
  `Krylov.IsGalerkinIterate.norm_error_antitone` in `Numlib/Krylov/Monotonicity.lean`); MINRES column:
  R2.6–R2.8, `Krylov.IsMinResIterate.norm_residual_antitone` (`Numlib/Krylov/Iterate.lean`), R3.6
  (`norm_residual_div_norm_antitoneOn`).
* Proof route: assemble the fields from the theorems above.
* Classification: `direct`.

### R5.2 — Table 5.1 (the "not-monotonic" entries for CG)
* Book statement: for CG, `‖r_k‖` and `‖r_k‖/‖x_k‖` are not monotonic (in general).
* Lean surface statement (faithful reading: existence of counterexamples):
  `theorem cg_norm_residual_not_antitone : ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Vec 2), A.PosDef ∧ ¬ Antitone fun k => ‖(cg A b k).r‖`
  with witness `A = diag(1, 9)`, `b = (3, 1)`: `‖r_0‖² = 10`, `α_1 = 5/9`, `r_1 = (4/3, −4)`, `‖r_1‖² = 160/9 > 10`;
  `theorem cg_backwardError_not_antitoneOn : ∃ (n) (A : Matrix (Fin n) (Fin n) ℝ) (b), A.PosDef ∧ ¬ AntitoneOn (fun k => ‖(cg A b k).r‖ / ‖(cg A b k).x‖) (Set.Ici 1)`
  (a `2 × 2` witness cannot work since `r_2 = 0`; the witness is an explicit `3 × 3` matrix, to be
  chosen numerically when the file is written).
* Backbone item: none (surface-only computation with `norm_num`/`simp [cg, cgStep]` on explicit `Fin 2` data).
* Proof route: unfold two steps of `cg`; `EuclideanSpace.norm_eq`, `Fin.sum_univ_two`.
* Classification: `surface-only`.

## Deferred backbone items

Both items are the strict, symmetric-indefinite forms of the monotonicity theorems that
`plans/backbone.md` §3.11 lists under "Steihaug's generalization"; they are scheduled for phase 2
(`plans/backbone.md` §7). The surface states R4.3–R4.4 against them.

1. **Steihaug for symmetric indefinite `A` (strict), `Numlib/Krylov/CG.lean` (§3.7/§3.11).**
   `theorem CG.norm_iterate_lt_of_re_inner_apply_direction_pos (hA : A.IsSymmetric) (b) (k) (h : ∀ j < k, 0 < re ⟪A p_j, p_j⟫) : ∀ i < k, ‖x_i‖ < ‖x_{i+1}‖`
   for the iterates from `x₀ = 0`; the spd `Monotone` statement `CG.norm_iterate_monotone` becomes its
   corollary through `CG.re_inner_apply_direction_pos`. Proof: the local argument of R4.3. Serves R4.3
   and the strict CG entry of Table 5.1.
2. **The CR/MINRES analogue, `Numlib/Krylov/CR.lean` or `Numlib/Krylov/Monotonicity.lean` (§3.8/§3.11).**
   `theorem CR.norm_iterate_lt_of_pos (hA : A.IsSymmetric) (hℓ : ∀ j < ℓ, ⟪r_j, A r_j⟫ ≠ 0) (h : ∀ j < k, 0 < ⟪A p_j, p_j⟫ ∧ 0 < ⟪r_j, A r_j⟫) : ∀ i < k, ‖x_i‖ < ‖x_{i+1}‖`
   with `ℓ` the termination index (global no-breakdown), the version supported by the paper's proof of
   Thm 2.2 (d); or a counterexample showing that the paper's local version (hypotheses for `j ≤ k`
   only) fails. Serves R4.4; the MINRES transfer is `CR.isMinResIterate_of_no_breakdown`.

## Left out

* §4 experiments: the test-set description, diagonal preconditioning, condition-number statistics, iteration limits `5n`/`n`, all
  of Figures 4.1–4.8 and their captions (percentages of monotone steps) — empirical, no theorem.
* §4.1.1's "cumulative minimum ≈" heuristic and "on average `‖r_k^M‖/‖r_{k−1}^M‖` closer to 1 if `l` is large" — informal reasoning;
  only the exact identities (4.1) and the telescoping product (R4.1–R4.2) are kept.
* §4.2: the `3 × 3` indefinite example (4.2) with its non-monotone plots — could be a computable counterexample
  (`¬ Monotone ‖x_k^M‖` for MINRES on an indefinite system), but the paper only reports it graphically; optional surface exercise.
* §4.2: the MINRES-QLP relationship (`Q_k [T̲_k β_1 e_1]`, `R_k P_k = L_k`, `W_k = V_k P_k`, `‖x_k^M‖ = ‖u_k‖`, the `χ²`
  update and "approximately monotonic") — a heuristic built on Choi–Paige–Saunders [3]; the identities belong to the Choi
  surface / backbone phase 2 (`Krylov/Singular.lean`, `plans/backbone.md` §3.12), and the paper draws no theorem from them.
* Table 5.2 (LSQR/LSMR properties) and the §5 discussion of least-squares solvers — results of other papers ([7], [8], [19]); the
  reduction "LSQR/LSMR = CG/MINRES on the normal equations" is a definition-level remark about other algorithms.
* §5 conclusions, acknowledgements, references, footnotes, key words.
* The literature attributions inside Table 5.1 (HS Thm 4:3, 6:3, 7:2, 7:4, 7:5; Steihaug Thm 2.1) are recorded in docstrings only.

## Reading conventions

Places where the paper's text is ambiguous or inconsistent, with the reading adopted above (each
was settled by internal consistency with the paper's own proofs).

* C1. Proof of Thm 2.3: the identity is read as `‖x_i‖² − ‖x_{i−1}‖² = 2α_i x_{i−1}ᵀ p_{i−1} + α_i² p_{i−1}ᵀ p_{i−1}`
  (the printed last term lacks the factor `α_i²`); the theorem is unaffected.
* C2. Proof of Thm 2.4: `x_l = x_{l−1} + α_{l−1} p_{l−1}` and `x_k + α_{k+1} p_k + ⋯ + α_{l−1} p_{l−1}` shift the `α` index by one
  relative to Table 2.1 (`x_k = x_{k−1} + α_k p_{k−1}` gives `α_{k+1} p_k + ⋯ + α_l p_{l−1}`); also `l` and `ℓ` are used for the same
  index. The Table 2.1 indexing is used throughout; statements unaffected.
* C3. §2.1 writes `‖x* − x_k‖_A ≡ (x* − x_k)ᵀ A (x* − x_k)` without a square root. We define the energy *norm*
  with the square root (D4); all monotonicity statements are invariant under squaring, and R2.1 records the
  squared identity `‖x* − x‖_A² = 2φ(x) + x*ᵀ A x*`.
* C4. Thm 2.2 (a): "The inequalities are strict until `i = ℓ` (and `r_ℓ = 0`)". Read as `ρ_i > 0` for `i < ℓ` and `α_i > 0` for
  `1 ≤ i ≤ ℓ` (so `β_i > 0` for `i < ℓ`), which is what the proofs of Thm 2.5 and (4.1) use.
* C5. §4.2 "as long as `p_jᵀ A p_j > 0` for all iterations `1 ≤ j ≤ k`" versus Table 2.1's indexing (iteration `j` uses `p_{j−1}`):
  interpreted as the directions used in iterations `1..k`, i.e. `p_0, …, p_{k−1}` (D10, R4.3); with the literal `p_1..p_k` the
  statement would also constrain the unused `p_k` and omit `p_0`, which contradicts Steihaug's original.
* C6. Thm 2.2 (e) is proved only for `x_iᵀ p_i` ("Therefore `x_iᵀ p_i ≥ 0`") but stated for `x_iᵀ p_j`; the general case follows
  from `x_i = ∑ α_k p_{k−1}` and (d), and R2.5 states it for all `i, j`.
* C7. Table 5.1: the CG entry for `‖x_k‖` is `↗ [21, Thm 2.1]`; the last table row is the legend (`↗` monotonically increasing,
  `↘` monotonically decreasing); the MINRES entry for `‖r_k‖/‖x_k‖` reads "(Thm 3.1)" and is taken as `↘ (Thm 3.1)`.
