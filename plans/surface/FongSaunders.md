# Surface plan: Fong–Saunders (2012)

Paper: D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU J. Sci.
17:1 (2012) 44–62 (Report SOL 2011-2R; the OCR title page carries the SQU reference). Setting: a
real symmetric positive definite `n × n` system `A x = b`, `x₀ = 0`, 2-norm for vectors, Frobenius
norm for matrices. Mathematical content: (§1) Lanczos/Krylov setting; (§2) the CG/CR pseudocode of
Table 2.1, the minimization characterizations of CG and MINRES, the CR sign lemmas Thm 2.1–2.2, and
the monotonicity theorems Thm 2.3–2.5 for CR (hence MINRES); (§3) normwise relative backward error
(3.1)–(3.6), the stopping rule (3.4), Thm 3.1; (§4.1.1) the FOM/GMRES-type relation (4.1); (§4.2)
Steihaug's indefinite-case monotonicity and its CR analogue; (§5) Table 5.1.
Lean files: `Surface/FongSaunders/Sec1.lean` (setting), `Sec2.lean`, `Sec3.lean`, `Sec4.lean`
(only (4.1), the telescoping identity, §4.2), `Sec5.lean` (Table 5.1 as a structure). Numerical-only
material (§4 experiments, Figures 4.1–4.8, the MINRES-QLP heuristic in §4.2, Table 5.2, §5 prose) is
left out (§5 of this plan). Count: 26 result blocks below; 9 gaps/requests to the backbone.

Conventions used below. `n : ℕ`; `Vec n := EuclideanSpace ℝ (Fin n)`; `A : Matrix (Fin n) (Fin n) ℝ`
with standing hypothesis `hA : A.PosDef` (Mathlib's `Matrix.PosDef`, which for `ℝ` is "symmetric
and `xᵀ A x > 0` for `x ≠ 0`"); `b : Vec n`; `A ⬝ x := Matrix.toEuclideanLin A x` (scoped infix, the
surface's matrix–vector product on Euclidean vectors); `⟪x, y⟫_ℝ` is `xᵀ y`; `‖x‖` on `Vec n` is the
2-norm; `‖A‖` is the Frobenius norm via `open scoped Matrix.Norms.Frobenius`. Backbone names are
those of `plans/backbone.md` (section numbers in parentheses) or of the skeleton under `Numlib/`
when it already exists (marked "skeleton"). All of the Lean sketches marked ✓ were elaborated
(with `sorry` bodies and local stubs of the backbone) in `FSScratch.lean` next to this file.

Status legend: `direct` = the backbone theorem applies after rewriting with the equivalence
lemmas of §2 of this plan; `needs-equivalence` = a nontrivial surface-side bridge (or a naming /
unfolding lemma the backbone should add) is required, but the mathematics is in the backbone;
`GAP` = the backbone plan lacks the statement or its statement cannot be specialized to the paper's.

## Paper-specific definitions

Each block: paper formulation → Lean surface definition → backbone counterpart → equivalence lemma.

### D1. Vectors, matrices, norms (§1.1)
* Paper: real `n × n` spd `A`, `‖v‖` the 2-norm, `‖A‖` the Frobenius norm, `A ≻ 0` means spd.
* Lean: `abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)`;
  `noncomputable abbrev mulVecE (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Vec n := Matrix.toEuclideanLin A x`,
  `scoped infixr:73 " ⬝ " => mulVecE`; `A ≻ 0` is `A.PosDef`. ✓
* Backbone: `LinearMap.IsSymmetricCoercive` (2.1.4; skeleton `Numlib/ForMathlib/InnerProductSpace/Coercive.lean`).
* Equivalence: `Matrix.posDef_iff_isSymmetricCoercive (M) : M.PosDef ↔ (toEuclideanLin M).IsSymmetricCoercive`
  (skeleton, ✓). Surface glue lemmas (trivial `simp`/`rfl`, put in `Sec1.lean`):
  `mulVecE_add`, `mulVecE_smul`, `mulVecE_zero`, `inner_mulVecE : ⟪x, A ⬝ y⟫_ℝ = x.ofLp ⬝ᵥ (A *ᵥ y.ofLp)`,
  `inner_mulVecE_comm (hA : A.IsSymm) : ⟪x, A ⬝ y⟫_ℝ = ⟪A ⬝ x, y⟫_ℝ`,
  `mulVecE_pow : (A ^ i) ⬝ x = (toEuclideanLin A ^ i) x` (needs `Matrix.toEuclideanLin_pow`, see gap G9).

### D2. Krylov subspace and the Lanczos objects (§1)
* Paper: `𝒦_k(A, b) = span{b, A b, …, A^(k−1) b}`; Lanczos with starting vector `b` gives
  `V_k = (v_1 … v_k)` orthonormal, `T_k` of size `(k+1) × k` tridiagonal with `A V_k = V_{k+1} T_k`
  for `k = 1, …, ℓ`, `A V_ℓ = V_ℓ T_ℓ` for some `ℓ ≤ n`; iterates `x_k = V_k y_k`.
* Lean: `noncomputable def krylov (A) (b) (k : ℕ) : Submodule ℝ (Vec n) := Submodule.span ℝ (Set.range fun i : Fin k => (A ^ (i : ℕ)) ⬝ b)` ✓;
  Lanczos vectors are *not* redefined: `lanczosVec A b j := Arnoldi.vec (toEuclideanLin A) b j`
  (paper's `v_{j+1}`; index shift by one), `lanczosT A b k := Lanczos.tridiagExt (toEuclideanLin A) b k`,
  `lanczosTerm A b := Krylov.grade (toEuclideanLin A) b` (the paper's `ℓ`).
* Backbone: `Krylov.subspace` (3.1, skeleton), `Arnoldi.vec`, `Arnoldi.span_vec`, `Arnoldi.apply_sum`
  (3.2, skeleton), `Lanczos.tridiagExt`, `Lanczos.hessenberg_eq_tridiagExt` (3.3, plan only),
  `Krylov.grade`, `Krylov.grade_le_finrank` (3.1, skeleton).
* Equivalence: `krylov_eq : krylov A b k = Krylov.subspace (toEuclideanLin A) b k` ✓ (by `mulVecE_pow`);
  `mem_krylov_iff_exists_lanczos (hk : k ≤ ℓ) : x ∈ krylov A b k ↔ ∃ y : Fin k → ℝ, x = ∑ j, y j • lanczosVec A b j`
  (from `Arnoldi.span_vec` + `Submodule.mem_span_range_iff_exists_fun`), which is the paper's "`x_k = V_k y_k`".

### D3. The exact solution `x*` (§1.1)
* Paper: the unique solution `x*` of `A x = b`.
* Lean: state theorems with a variable `(xstar : Vec n) (hstar : A ⬝ xstar = b)`; provide
  `noncomputable def xstar (A) (b) : Vec n := A⁻¹ ⬝ b` with `mulVecE_xstar (hA) : A ⬝ xstar A b = b`
  and `xstar_unique (hA) (h : A ⬝ x = b) : x = xstar A b`.
* Backbone: none needed (Mathlib `Matrix.PosDef.isUnit`/`det_pos`, `Matrix.mulVec_mulVec`, `nonsing_inv_mul`).
* Equivalence: `xstar_eq_of_apply_eq` as above.

### D4. The quadratic form `φ` and the energy norm (§2.1)
* Paper: `φ(x) = ½ xᵀ A x − bᵀ x`; `‖x* − x_k‖_A ≡ (x* − x_k)ᵀ A (x* − x_k)` (OCR shows no square root;
  see O4 — we take the norm, `√(vᵀ A v)`; every statement below is invariant under squaring).
* Lean: `noncomputable def phi (A) (b) (x : Vec n) : ℝ := (1/2) * ⟪x, A ⬝ x⟫_ℝ - ⟪b, x⟫_ℝ` ✓;
  `noncomputable def energyNorm (A) (v : Vec n) : ℝ := Real.sqrt ⟪v, A ⬝ v⟫_ℝ` ✓ (scoped notation `‖v‖_A`).
* Backbone: `energyNorm (A : E →ₗ[𝕜] E) x = √(re ⟪A x, x⟫)` (2.1.5; skeleton `Energy.lean`), the
  quadratic `re⟪A x, x⟫/2 − re⟪b, x⟫` appearing in `IsGalerkin.quadratic_le` (2.4.2, skeleton).
* Equivalence: `energyNorm_eq : energyNorm A v = _root_.energyNorm (toEuclideanLin A) v`
  (`RCLike.re_to_real`, `real_inner_comm`); `phi_eq : phi A b x = re⟪(toEuclideanLin A) x, x⟫/2 − re⟪b, x⟫` (`ring`).

### D5. Algorithm CG (Table 2.1, column 1)
* Paper: Initialize `x = 0, r = b, ρ = ‖r‖², p = r`. Repeat: `q = A p; α = ρ / pᵀ q; x ← x + α p;
  r ← r − α q; ρ̄ = ρ, ρ = rᵀ r; β = ρ/ρ̄; p ← r + β p`. Terminate when `r = 0` (`⇒ ρ = β = 0`).
* Lean ✓:
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
  ```
  Lean's `0/0 = 0` makes the recurrence stationary after termination (`r = 0 ⇒ ρ = 0 ⇒ α = β = 0 ⇒ p = 0`),
  exactly the paper's "termination", so no `Option`/partiality is needed.
* Backbone: `CG.State`, `CG.step`, `CG.iterate A b x₀ k` (3.7; prototype `Proto2.lean`), whose step
  uses `α := ⟪r, r⟫/⟪A p, p⟫`, `β := ⟪r', r'⟫/⟪r, r⟫`.
* Equivalence: `cg_eq_backbone (k) : (cg A b k).x = (CG.iterate (toEuclideanLin A) b 0 k).x ∧ (cg A b k).r = (…).r ∧ (cg A b k).p = (…).p ∧ (cg A b k).ρ = ‖(cg A b k).r‖ ^ 2`
  by induction on `k` (`Function.iterate_succ_apply'`, `map_zero`, `sub_zero`, `real_inner_self_eq_norm_sq`);
  `cgAlpha_eq`, `cgBeta_eq` unfold to the backbone's local `let`s (needs the backbone to *name* them, gap G3).

### D6. Algorithm CR (Table 2.1, columns 2–3)
* Paper (indexed form): `x_0 = 0, r_0 = b, s_0 = A r_0, ρ_0 = r_0ᵀ s_0, p_0 = r_0, q_0 = s_0`; for
  `k = 1, 2, …`: `(q_{k−1} = A p_{k−1})`, `α_k = ρ_{k−1}/‖q_{k−1}‖²`, `x_k = x_{k−1} + α_k p_{k−1}`,
  `r_k = r_{k−1} − α_k q_{k−1}`, `s_k = A r_k`, `ρ_k = r_kᵀ s_k`, `β_k = ρ_k/ρ_{k−1}`, `p_k = r_k + β_k p_{k−1}`,
  `q_k = s_k + β_k q_{k−1}`. Termination at `k = ℓ ≤ n` with `r_ℓ = 0` (`⇒ ρ_ℓ = β_ℓ = 0`, `r_ℓ = s_ℓ = p_ℓ = q_ℓ = 0`).
* Lean ✓:
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
* Backbone: `CR.State` (fields `x r p q`), `CR.step`, `CR.iterate` (3.8; prototype), with
  `α := ⟪r, A r⟫/⟪q, q⟫`, `β := ⟪r', A r'⟫/⟪r, A r⟫`, `q' := A r' + β q` — the paper's recurrence verbatim.
* Equivalence: `cr_eq_backbone (k) : let s := cr A b k; let t := CR.iterate (toEuclideanLin A) b 0 k; s.x = t.x ∧ s.r = t.r ∧ s.p = t.p ∧ s.q = t.q ∧ s.s = A ⬝ s.r ∧ s.ρ = ⟪s.r, A ⬝ s.r⟫_ℝ` ✓
  (induction on `k`); the paper's remark "`q = A p` in both methods" is `cr_q_eq (hA.1) : (cr A b k).q = A ⬝ (cr A b k).p`
  (induction; backbone should provide `CR.q_eq_apply_p`, gap G3); `cr_residual_eq : (cr A b k).r = b - A ⬝ (cr A b k).x`
  (from `CR.residual_eq`, to be added like `CG.residual_eq`, gap G3); `crTerm_eq_grade (hA) : crTerm A b = Krylov.grade (toEuclideanLin A) b`
  (gap G4). Same for CG: `cgTerm`, `cgTerm_eq_grade`, and `cgTerm_eq_crTerm` (both equal the grade — the
  paper's "Note: this `ℓ` is the same as the `ℓ` at which the Lanczos process terminates").

### D7. MINRES iterates (2.1)
* Paper: `x_k^M = V_k y_k^M`, `y_k^M = argmin_y ‖b − A V_k y‖`; "MINRES minimizes `‖r_k‖` within the
  `k`-th Krylov subspace" (for nonsingular, possibly indefinite `A`).
* Lean ✓: `def IsMinresIterate (A) (b) (k : ℕ) (x : Vec n) : Prop := x ∈ krylov A b k ∧ ∀ y ∈ krylov A b k, ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖`.
  Theorems "for MINRES" quantify over `x : ℕ → Vec n` with `hx : ∀ k, IsMinresIterate A b k (x k)`
  (this is exactly the paper's "and hence MINRES", since the paper uses only the minimization property).
* Backbone: `Krylov.IsMinResIterate A b x₀ m x := IsMinRes A b x₀ (𝒦[A, b − A x₀] m) x` (3.4; `IsMinRes` in skeleton `Projection/Basic.lean`).
* Equivalence: `isMinresIterate_iff : IsMinresIterate A b k x ↔ Krylov.IsMinResIterate (toEuclideanLin A) b 0 k x` ✓
  (`map_zero`, `sub_zero`, `krylov_eq`); the literal `V_k y` form via `mem_krylov_iff_exists_lanczos` (D2).

### D8. CG as a minimizer (§2.1)
* Paper: `x_k^C = V_k y_k^C`, `y_k^C = argmin_y φ(V_k y)`, equivalently minimizing `‖x* − x_k‖_A` over `𝒦_k`.
* Lean: no new definition; stated as theorems R2.1 about `cg A b k` (D5) and as the predicate
  `IsMinOn (phi A b) (krylov A b k)`.
* Backbone: `Krylov.IsGalerkinIterate` (3.4), `CG.isGalerkinIterate` (3.7), `IsGalerkin.quadratic_le`,
  `IsGalerkin.iff_energyNorm_min` (2.4.2, skeleton).
* Equivalence: `isGalerkinIterate_iff_isMinOn_phi (hA) : Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k x ↔ x ∈ krylov A b k ∧ IsMinOn (phi A b) (krylov A b k) x`
  (⇒ from `quadratic_le`; ⇐ is the plan's `isGalerkin_iff_isMinOn_quadratic`, not in the skeleton — gap G8).

### D9. Backward error (3.1)–(3.3)
* Paper: `x_k` is *acceptable* iff `∃ E, f` with `(A + E) x_k = b + f`, `‖E‖/‖A‖ ≤ α`, `‖f‖/‖b‖ ≤ β`
  (`α, β ≥ 0`). The NRBE `ξ_k` is the optimal value of `min_{ξ,E,f} ξ` s.t. `(A+E) x_k = b + f`,
  `‖E‖/‖A‖ ≤ α ξ`, `‖f‖/‖b‖ ≤ β ξ`; with `r_k = b − A x_k` the optimum is
  `φ_k = β‖b‖/(α‖A‖‖x_k‖ + β‖b‖)`, `E_k = ((1 − φ_k)/‖x_k‖²) r_k x_kᵀ`, `ξ_k = ‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)`, `f_k = −φ_k r_k`.
* Lean ✓ (Frobenius norm on matrices):
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
* Backbone: `backwardError_eq` (2.2), stated with the *operator* norm on `E →L[𝕜] E` and with the
  weights `α ‖A‖`, `β ‖b‖` baked in.
* Equivalence: `nrbe_eq_backbone` — only after gap G1 (norm-generic / weight-generic form of
  `backwardError_eq`); `nrbePertA` corresponds to the backbone's rank-one `((1−ω)/‖y‖²) r ⊗ y` via
  `InnerProductSpace.symm_toEuclideanLin_rankOne` (Mathlib) and `‖vecMulVec r x‖_F = ‖r‖ ‖x‖` (gap G1).

### D10. Steihaug's indefinite setting (§4.2)
* Paper: CG applied to a symmetric, possibly indefinite `A x = b` (notation of Table 2.1); the
  hypothesis is `p_jᵀ A p_j > 0` for all iterations `1 ≤ j ≤ k`; for CR/MINRES additionally `r_jᵀ A r_j > 0`.
* Lean: no new definition — the same `cg`/`cr` (D5–D6) with `hA' : A.IsSymm` instead of `A.PosDef`;
  the hypotheses are `∀ j < k, 0 < ⟪(cg A b j).p, A ⬝ (cg A b j).p⟫_ℝ` (directions `p_0, …, p_{k−1}` used
  in iterations `1..k`; see O7) and, for CR, also `∀ j < k, 0 < (cr A b j).ρ` (`ρ_j = r_jᵀ A r_j`).
* Backbone: `CG.norm_iterate_monotone` (3.7, SPD, nonstrict) and the unnamed "Steihaug's
  generalization" of 3.11 — gaps G6, G7.
* Equivalence: `cg_eq_backbone` holds for every matrix (no `PosDef` needed), so the same lemma serves.

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
* Backbone: 3.7, 3.11 (see R5.1).
* Equivalence: none (a restatement).

## Results

Numbering: `R<section>.<item>`; the paper's own labels are in the `Book statement` field.

### R1.1 — Lanczos relation and termination (§1, unnumbered setting)
* Book statement: The Lanczos process with starting vector `b` gives orthonormal `V_k` spanning `𝒦_k(A, b)`
  and tridiagonal `(k+1) × k` `T_k` with `A V_k = V_{k+1} T_k` for `k = 1, …, ℓ` and `A V_ℓ = V_ℓ T_ℓ` for some `ℓ ≤ n`.
* Lean surface statement:
  `theorem lanczos_relation (hA) (k : ℕ) (hk : k < lanczosTerm A b) (y : Fin k → ℝ) : A ⬝ (∑ j, y j • lanczosVec A b j) = ∑ i : Fin (k+1), (lanczosT A b k).mulVec y i • lanczosVec A b i`;
  `theorem lanczosVec_orthonormal (hA) : Orthonormal ℝ (fun j : Fin (lanczosTerm A b) => lanczosVec A b j)`;
  `theorem span_lanczosVec (k) : span ℝ (lanczosVec A b '' Set.Iio k) = krylov A b k`;
  `theorem lanczosTerm_le : lanczosTerm A b ≤ n`.
* Backbone item: 3.2 `Arnoldi.apply_sum`, `Arnoldi.orthonormal`, `Arnoldi.span_vec` (skeleton); 3.3
  `Lanczos.tridiagExt`, `Lanczos.hessenberg_eq_tridiagExt` (plan); 3.1 `Krylov.grade_le_finrank` (skeleton).
* Proof route: `Arnoldi.apply_sum` + rewrite the Hessenberg matrix as `tridiagExt` using symmetry
  (`posDef_iff_isSymmetricCoercive`); `finrank_euclideanSpace_fin` for `≤ n`.
* Status: `needs-equivalence` (the `Lanczos` file is planned, not yet in the skeleton; the surface only unfolds).

### R1.2 — "`x_k = V_k y_k` for some `k`-vector `y_k`" (§1)
* Book statement: approximate solutions in `𝒦_k` are exactly the vectors `V_k y_k`.
* Lean surface statement: `mem_krylov_iff_exists_lanczos` (D2).
* Backbone item: 3.2 `Arnoldi.span_vec` (skeleton).
* Proof route: `Submodule.mem_span_range_iff_exists_fun` after `span_vec`.
* Status: `direct`.

### R1.3 — Unique solution (§1.1)
* Book statement: `A x = b` has a unique solution `x*` (`A` spd).
* Lean surface statement: `theorem existsUnique_solution (hA) : ∃! x : Vec n, A ⬝ x = b`.
* Backbone item: none (Mathlib: `Matrix.PosDef.isUnit`, `Matrix.toEuclideanLin` is a `LinearEquiv` on units; or 2.1.4 `IsCoercive.injective` + finite dimension).
* Proof route: `LinearMap.injective_iff_surjective` from `IsCoercive.injective` (skeleton `Coercive.lean`).
* Status: `direct`.

### R2.1 — CG minimizes `φ` and the energy-norm error (§2.1, unnumbered)
* Book statement: `x_k^C = V_k y_k^C` with `y_k^C = argmin_y φ(V_k y)`; with `b = A x*` and
  `2φ(x_k) = x_kᵀ A x_k − 2 x_kᵀ A x*` this is equivalent to minimizing `‖x* − x_k‖_A` within `𝒦_k`.
* Lean surface statement ✓:
  `theorem cg_mem_krylov (k) : (cg A b k).x ∈ krylov A b k`;
  `theorem cg_isMinOn_phi (hA) (k) : IsMinOn (phi A b) (krylov A b k) (cg A b k).x`;
  `theorem cg_energyNorm_le (hA) (hstar) (k) (y) (hy : y ∈ krylov A b k) : energyNorm A (xstar - (cg A b k).x) ≤ energyNorm A (xstar - y)`;
  `theorem isMinOn_phi_iff_energyNorm_min (hA) (hstar) (x) (hx : x ∈ krylov A b k) : IsMinOn (phi A b) (krylov A b k) x ↔ ∀ y ∈ krylov A b k, energyNorm A (xstar - x) ≤ energyNorm A (xstar - y)`;
  `theorem cg_unique_min (hA) (x) (hx : x ∈ krylov A b k) (hmin : IsMinOn (phi A b) (krylov A b k) x) : x = (cg A b k).x`;
  plus the identity `two_phi_eq (hstar) : 2 * phi A b x = ⟪x, A ⬝ x⟫_ℝ - 2 * ⟪x, A ⬝ xstar⟫_ℝ` and
  `energyNorm_sq_eq_two_phi_add (hA) (hstar) : energyNorm A (xstar - x) ^ 2 = 2 * phi A b x + ⟪xstar, A ⬝ xstar⟫_ℝ`.
* Backbone item: 3.7 `CG.isGalerkinIterate`; 2.4.2 `IsGalerkin.quadratic_le`, `IsGalerkin.iff_energyNorm_min`, `IsGalerkin.energyNorm_le` (skeleton); 2.4.1 `existsUnique_isGalerkin_of_isCoercive` (skeleton).
* Proof route: `cg_eq_backbone` + `CG.isGalerkinIterate` give `IsGalerkinIterate`; `quadratic_le` + `phi_eq` give the `IsMinOn`; `iff_energyNorm_min` for the equivalence; uniqueness from `∃!` plus the ⇐ direction of D8's equivalence.
* Status: `needs-equivalence` (the ⇐ direction `IsMinOn φ ⇒ IsGalerkin` is in the plan but not in the skeleton, gap G8).

### R2.2 — MINRES minimizes `‖r_k‖`; CR and MINRES coincide on spd systems (§2.2, (2.1))
* Book statement: (2.1) defines MINRES; "MINRES minimizes `‖r_k‖` within the `k`-th Krylov subspace";
  CR also minimizes the residual for spd systems, "thus CR and MINRES must generate the same iterates on spd systems".
* Lean surface statement ✓ (shapes):
  `theorem cr_isMinresIterate (hA) (k) : IsMinresIterate A b k (cr A b k).x`;
  `theorem isMinresIterate_unique (hA) (k) {x y} (hx : IsMinresIterate A b k x) (hy : IsMinresIterate A b k y) : x = y`;
  `theorem isMinresIterate_iff_eq_cr (hA) (k) (x) : IsMinresIterate A b k x ↔ x = (cr A b k).x`;
  `theorem minres_norm_residual_le (hx : IsMinresIterate A b k x) (hy : y ∈ krylov A b k) : ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖` (definitional).
* Backbone item: 3.8 `CR.isMinResIterate` (prototype ✓); 2.4.1 `existsUnique_isMinRes_of_injOn` (skeleton); 2.1.4 `IsCoercive.injective`.
* Proof route: `cr_eq_backbone` + `CR.isMinResIterate`; uniqueness from `existsUnique_isMinRes_of_injOn` with `Set.InjOn` from injectivity.
* Status: `direct` (after D6/D7 equivalences).

### R2.3 — Well-definedness and termination of CG and CR (§2.3, unnumbered)
* Book statement: CG is well defined if `A` is spd; termination occurs when `r_k = 0` for some
  `k = ℓ ≤ n`, then `ρ_ℓ = β_ℓ = 0` and `r_ℓ = s_ℓ = p_ℓ = q_ℓ = 0`; this `ℓ` equals the Lanczos termination index.
* Lean surface statement:
  `theorem cg_inner_p_q_pos (hA) (k) (hk : (cg A b k).r ≠ 0) : 0 < ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ`;
  `theorem cr_rho_pos (hA) (k) (hk : (cr A b k).r ≠ 0) : 0 < (cr A b k).ρ`;
  `theorem cr_residual_eq_zero_iff (hA) (k) : (cr A b k).r = 0 ↔ lanczosTerm A b ≤ k` (and the CG twin);
  `theorem crTerm_le (hA) : crTerm A b ≤ n`; `theorem crTerm_eq_grade`, `cgTerm_eq_crTerm`;
  `theorem cr_term_state (hA) : let s := cr A b (crTerm A b); s.r = 0 ∧ s.s = 0 ∧ s.ρ = 0 ∧ s.p = 0 ∧ s.q = 0 ∧ crBeta A b (crTerm A b) = 0`;
  `theorem cr_stationary (hA) (h : crTerm A b ≤ k) : cr A b k = cr A b (crTerm A b)`.
* Backbone item: 3.7 `CG.inner_apply_direction_pos`; 3.7/3.8 "Termination (L3): `r_k = 0` for `k ≥ grade`" (unnamed); 3.1 `Krylov.grade_le_finrank` (skeleton).
* Proof route: positivity from coercivity + `p_k ≠ 0` when `r_k ≠ 0`; `⇐` of `residual_eq_zero_iff` is the backbone termination fact; `⇒` needs `Krylov.grade_le_of_apply_eq` (gap G4); the state equalities are `simp` after `r = 0`.
* Status: `GAP` (G4: the converse "`r_k ≠ 0` for `k < grade`" and named termination lemmas are missing).

### R2.4 — Theorem 2.1 (a), (b)
* Book statement: For Algorithm CR (spd `A`): (a) `q_iᵀ q_j = 0` for `i ≠ j`; (b) `r_iᵀ q_j = 0` for `i ≥ j + 1`.
* Lean surface statement ✓:
  `theorem thm_2_1_a (hA) {i j : ℕ} (hij : i ≠ j) : ⟪(cr A b i).q, (cr A b j).q⟫_ℝ = 0`;
  `theorem thm_2_1_b (hA) {i j : ℕ} (hij : j + 1 ≤ i) : ⟪(cr A b i).r, (cr A b j).q⟫_ℝ = 0`.
* Backbone item: 3.8 "Fong–Saunders Thm 2.1 / Luenberger: `⟪A p_i, A p_j⟫ = 0` (`i ≠ j`), `⟪r_i, A p_j⟫ = 0` (`j < i`)" (unnamed; proposed `CR.inner_apply_direction_apply_direction_eq_zero`, `CR.inner_residual_apply_direction_eq_zero`).
* Proof route: rewrite `q_i = A p_i` (`cr_q_eq`) and apply the backbone lemmas through `cr_eq_backbone`.
* Status: `needs-equivalence` (statements exist in the plan without names; needs `CR.q_eq_apply_p`, gap G3).

### R2.5 — Theorem 2.2 (a)–(f)
* Book statement: For Algorithm CR on spd `A x = b`, `x_0 = 0`: (a) `α_i ≥ 0` (strict until `i = ℓ`,
  where `r_ℓ = 0`; via `ρ_i = r_iᵀ A r_i ≥ 0` (2.2)); (b) `β_i ≥ 0`; (c) `p_iᵀ q_j ≥ 0`; (d) `p_iᵀ p_j ≥ 0`;
  (e) `x_iᵀ p_j ≥ 0`; (f) `r_iᵀ p_j ≥ 0` (all `i, j`).
* Lean surface statement ✓ (shapes):
  `theorem eq_2_2 (hA) (i) : 0 ≤ (cr A b i).ρ` and `theorem eq_2_2_strict (hA) (hi : (cr A b i).r ≠ 0) : 0 < (cr A b i).ρ`;
  `theorem thm_2_2_a (hA) (i) : 0 ≤ crAlpha A b i`; `theorem thm_2_2_a_strict (hA) (hi : 1 ≤ i) (hℓ : i ≤ crTerm A b) : 0 < crAlpha A b i`;
  `theorem thm_2_2_b (hA) (i) : 0 ≤ crBeta A b i`;
  `theorem thm_2_2_c (hA) (i j) : 0 ≤ ⟪(cr A b i).p, (cr A b j).q⟫_ℝ`;
  `theorem thm_2_2_d (hA) (i j) : 0 ≤ ⟪(cr A b i).p, (cr A b j).p⟫_ℝ`;
  `theorem thm_2_2_e (hA) (i j) : 0 ≤ ⟪(cr A b i).x, (cr A b j).p⟫_ℝ`;
  `theorem thm_2_2_f (hA) (i j) : 0 ≤ ⟪(cr A b i).r, (cr A b j).p⟫_ℝ`.
* Backbone item: 3.8 "Fong–Saunders Thm 2.2 (L3): all of `α_i, β_i, ⟪p_i, A p_j⟫, ⟪p_i, p_j⟫, ⟪x_i, p_j⟫, ⟪r_i, p_j⟫` are `≥ 0`" (unnamed; proposed `CR.alpha_nonneg`, `CR.beta_nonneg`, `CR.inner_direction_apply_direction_nonneg`, `CR.inner_direction_nonneg`, `CR.inner_iterate_direction_nonneg`, `CR.inner_residual_direction_nonneg`, plus `CR.alpha_pos`/`CR.rho_pos`).
* Proof route: (a)–(c) are local (coercivity + Thm 2.1 (b) + induction on `|i − j|`); (d)–(f) use finite termination and the orthogonal expansion in `{q_i}` (backbone 3.11 proof note). The surface only unfolds `crAlpha`/`crBeta` to the backbone's coefficients (gap G3) and rewrites `q_j = A p_j`.
* Status: `needs-equivalence` (mathematics planned in 3.8; naming, coefficient functions and the strict form (a) are gap G3).

### R2.6 — Theorem 2.3
* Book statement: For CR (and hence MINRES) on an spd system, `‖x_k‖` increases monotonically
  (the proof gives `‖x_i‖² − ‖x_{i−1}‖² ≥ 0`, i.e. nondecreasing).
* Lean surface statement ✓:
  `theorem thm_2_3_cr (hA) : Monotone fun k => ‖(cr A b k).x‖`;
  `theorem thm_2_3_minres (hA) (x : ℕ → Vec n) (hx : ∀ k, IsMinresIterate A b k (x k)) : Monotone fun k => ‖x k‖`;
  optional strict form `theorem thm_2_3_strict (hA) (hk : k < crTerm A b) : ‖(cr A b k).x‖ < ‖(cr A b (k+1)).x‖`.
* Backbone item: 3.8 `CR.norm_iterate_monotone` ✓; 3.11 `Krylov.IsMinResIterate.norm_monotone` ✓ (both prototyped).
* Proof route: `cr_eq_backbone` resp. `isMinresIterate_iff` + `posDef_iff_isSymmetricCoercive`; the strict form from `‖x_{k+1}‖² − ‖x_k‖² ≥ α_{k+1}² ‖p_k‖² > 0` (needs `CR.alpha_pos`, gap G3/G5).
* Status: `direct`.

### R2.7 — Theorem 2.4
* Book statement: For CR (and hence MINRES) on an spd system, `‖x* − x_k‖` decreases monotonically (nonincreasing; the proof shows the difference of squares is `≥ 0`).
* Lean surface statement ✓:
  `theorem thm_2_4_cr (hA) (hstar : A ⬝ xstar = b) : Antitone fun k => ‖xstar - (cr A b k).x‖`;
  `theorem thm_2_4_minres (hA) (hstar) (x) (hx : ∀ k, IsMinresIterate A b k (x k)) : Antitone fun k => ‖xstar - x k‖`.
* Backbone item: 3.11 `Krylov.IsMinResIterate.norm_error_antitone`.
* Proof route: as R2.6.
* Status: `direct`.

### R2.8 — Theorem 2.5
* Book statement: For CR (and hence MINRES) on an spd system, `‖x* − x_k‖_A` is strictly decreasing
  (the proof gives `> 0` using Thm 2.2 (a), (c); strictness needs `α_k > 0`, i.e. `k ≤ ℓ`).
* Lean surface statement ✓:
  `theorem thm_2_5_cr (hA) (hstar) (k) (hk : (cr A b k).r ≠ 0) : energyNorm A (xstar - (cr A b (k+1)).x) < energyNorm A (xstar - (cr A b k).x)`;
  `theorem thm_2_5_cr_antitone (hA) (hstar) : Antitone fun k => energyNorm A (xstar - (cr A b k).x)`;
  `theorem thm_2_5_minres (hA) (hstar) (x) (hx) (hk : b - A ⬝ x k ≠ 0) : energyNorm A (xstar - x (k+1)) < energyNorm A (xstar - x k)`.
* Backbone item: 3.11 `Krylov.IsMinResIterate.energyNorm_error_antitone` ("strictly while `r_k ≠ 0`" is mentioned in the docstring but no strict statement is named).
* Proof route: nonstrict form is `direct`; strict form via `energyNorm_eq` from the backbone strict lemma (gap G5).
* Status: `needs-equivalence` for the nonstrict form; `GAP` (G5) for the strict form as the paper states it.

### R3.1 — (3.2)–(3.3): the optimal backward-error perturbation
* Book statement: For tolerances `α, β ≥ 0`, the optimization problem `min ξ` s.t. `(A + E) x_k = b + f`,
  `‖E‖/‖A‖ ≤ αξ`, `‖f‖/‖b‖ ≤ βξ` has optimal solution `ξ_k, E_k, f_k` given by (3.2)–(3.3) (`‖·‖` Frobenius on `E`).
* Lean surface statement ✓:
  `theorem nrbe_isLeast (α β) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) : IsLeast (nrbeFeasible A b α β x) (nrbe A b α β x)`;
  `theorem nrbePert_attains (α β) (x) (hx : x ≠ 0) : (A + nrbePertA A b α β x) ⬝ x = b + nrbePertb A b α β x ∧ ‖nrbePertA A b α β x‖ / ‖A‖ = α * nrbe A b α β x ∧ ‖nrbePertb A b α β x‖ / ‖b‖ = β * nrbe A b α β x`.
  Hypothesis note: `hden` (equivalently `(α, β) ≠ (0,0)` when `A, b, x ≠ 0`) is implicit in the paper; for `x = 0`
  (i.e. `k = 0`) the paper's `E_k` is undefined, Lean's `nrbePertA … 0 = 0` and the first conjunct still holds.
* Backbone item: 2.2 `backwardError_eq` (Rigal–Gaches/Titley-Péloquin), *operator* norm, weights baked in.
* Proof route: should be a specialization with `N = ‖·‖_F`, weights `a = α‖A‖_F`, `c = β‖b‖`; the lower bound uses
  `‖E x‖ ≤ ‖E‖_F ‖x‖` (Mathlib `Matrix.frobenius_norm_mulVec`-type lemma / `l2_opNorm ≤ frobenius`) and attainment uses
  `‖vecMulVec r x‖_F = ‖r‖ ‖x‖`.
* Status: `GAP` (G1: the backbone statement uses the operator norm and cannot be specialized to the Frobenius constraint set).

### R3.2 — Acceptable solution ⇔ `ξ_k ≤ 1` (§3, unnumbered)
* Book statement: `x_k` is an acceptable solution (3.1) iff `ξ_k ≤ 1`.
* Lean surface statement: `theorem isAcceptable_iff_nrbe_le_one (hα) (hβ) (hden) : IsAcceptable A b α β x ↔ nrbe A b α β x ≤ 1`.
* Backbone item: as R3.1.
* Proof route: `IsLeast` gives ⇒ (`1 ∈ feasible`) and ⇐ (the optimal perturbation is feasible at `ξ = 1`, monotonicity of the constraints in `ξ`).
* Status: `needs-equivalence` (follows from R3.1 once G1 is done).

### R3.3 — Stopping rule (3.4)
* Book statement: `ξ_k ≤ 1` iff `‖r_k‖ ≤ α‖A‖‖x_k‖ + β‖b‖` (the LSQR rule S1).
* Lean surface statement ✓: `theorem nrbe_le_one_iff (α β) (x) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) : nrbe A b α β x ≤ 1 ↔ ‖b - A ⬝ x‖ ≤ α * ‖A‖ * ‖x‖ + β * ‖b‖`.
* Backbone item: 3.11 "Stopping rule (3.4)" (unnamed, trivial).
* Proof route: `div_le_one hden`.
* Status: `direct` (Mathlib).

### R3.4 — (3.5)–(3.6): norms of the optimal perturbations
* Book statement: `‖E_k‖ = (1 − φ_k) ‖r_k‖/‖x_k‖ = α‖A‖‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)`; `‖f_k‖ = φ_k ‖r_k‖ = β‖b‖‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)`.
* Lean surface statement ✓ (as the last two conjuncts of `nrbePert_attains`, plus the intermediate forms):
  `theorem norm_nrbePertA (x) (hx : x ≠ 0) : ‖nrbePertA A b α β x‖ = (1 - nrbePhi A b α β x) * ‖b - A ⬝ x‖ / ‖x‖` and
  `theorem norm_nrbePertb (x) : ‖nrbePertb A b α β x‖ = nrbePhi A b α β x * ‖b - A ⬝ x‖` (needs `0 ≤ φ_k`, i.e. `hden` and `0 ≤ β`).
  The second equality in (3.5) requires `x ≠ 0` (at `k = 0` the paper's expression is `0/0`).
* Backbone item: none (Frobenius norm of a rank-one matrix: ForMathlib, gap G1).
* Proof route: `Matrix.frobenius_norm_def` + `EuclideanSpace.norm_eq` + `Finset.sum_mul_sum`; then `field_simp`.
* Status: `needs-equivalence` (one ForMathlib lemma).

### R3.5 — `φ_k` decreases for CG and MINRES (§3.2, unnumbered remark)
* Book statement: since `‖x_k‖` is monotonically increasing for CG and MINRES, `φ_k` is monotonically decreasing for both solvers.
* Lean surface statement: `theorem nrbePhi_cg_antitone (hA) (hα : 0 ≤ α) (hβ : 0 ≤ β) : Antitone fun k => nrbePhi A b α β (cg A b k).x`;
  `theorem nrbePhi_minres_antitone (hA) (hα) (hβ) (hx : ∀ k, IsMinresIterate A b k (x k)) : Antitone fun k => nrbePhi A b α β (x k)`.
* Backbone item: 3.7 `CG.norm_iterate_monotone` ✓ (Steihaug, spd), 3.11 `Krylov.IsMinResIterate.norm_monotone` ✓.
* Proof route: `div_le_div_of_nonneg_left` with the monotone denominator (the constant-numerator case).
* Status: `direct`.

### R3.6 — Theorem 3.1 and the monotone NRBE
* Book statement: Suppose `α > 0` and `β > 0`. For CR and MINRES (but not CG), the relative backward
  errors `‖E_k‖/‖A‖` and `‖f_k‖/‖b‖` decrease monotonically. (Implicitly, so does `ξ_k`; Table 5.1 row 5 lists `‖r_k‖/‖x_k‖ ↘ (Thm 3.1)`.)
* Lean surface statement ✓:
  `theorem thm_3_1_minres (hA) (α β) (hα : 0 < α) (hβ : 0 < β) (x) (hx : ∀ k, IsMinresIterate A b k (x k)) : AntitoneOn (fun k => ‖nrbePertA A b α β (x k)‖ / ‖A‖) (Set.Ici 1) ∧ Antitone (fun k => ‖nrbePertb A b α β (x k)‖ / ‖b‖)`;
  `theorem thm_3_1_cr` (same with `(cr A b k).x`);
  `theorem nrbe_minres_antitone (hA) (hα : 0 ≤ α) (hβ : 0 < β) (hx) : Antitone fun k => nrbe A b α β (x k)`;
  `theorem nrbe_minres_antitoneOn (hA) (hα : 0 < α) (hβ : 0 ≤ β) (hx) : AntitoneOn (fun k => nrbe A b α β (x k)) (Set.Ici 1)` (covers the `β = 0` form `‖r_k‖/‖x_k‖` of §4.1).
  Why `Set.Ici 1` for `E_k` and for `β = 0`: at `k = 0`, `x_0 = 0` makes the paper's `E_0` undefined and Lean's `‖E_0‖ = 0`
  (also `‖r_0‖/‖x_0‖ = ‖b‖/0 = 0` under Lean's junk division), so a statement over all `k ≥ 0` is false in Lean; with `β > 0`
  the closed forms are finite at `k = 0` and `Antitone` on all of `ℕ` is correct. The "but not CG" clause is R5.2.
* Backbone item: 3.11 `Krylov.IsMinResIterate.backwardError_antitone` ✓ — prototyped as `Antitone fun k => ‖b − A (x k)‖ / ‖x k‖` over all `k`, which is **false** at `k = 0 → 1` for the same junk-division reason (gap G2).
* Proof route: numerator `‖r_k‖` antitone (`IsMinRes.norm_residual_le` on nested `𝒦_k`, skeleton) and denominator
  `α‖A‖‖x_k‖ + β‖b‖` monotone (Thm 2.3), then `div_le_div`; (3.5)–(3.6) (R3.4) transport to `‖E_k‖/‖A‖`, `‖f_k‖/‖b‖`.
* Status: `GAP` (G2: the backbone statement must be corrected/generalized; after that `direct`).

### R3.7 — MINRES stops no later than CG under rule (3.4) with `α = 0` (§1, §4 claim)
* Book statement: "with looser stopping tolerances, MINRES is sure to terminate sooner than CG when the
  stopping rule is based on the backward error" — rigorous only for `α = 0` (`‖r_k‖ ≤ β‖b‖`), which is the rule used in §4.
* Lean surface statement: `theorem minres_norm_residual_le_cg (hA) (k) (hx : IsMinresIterate A b k x) : ‖b - A ⬝ x‖ ≤ ‖(cg A b k).r‖`;
  `theorem minres_stops_first (hA) (β) (x) (hx) (k) (hcg : ‖(cg A b k).r‖ ≤ β * ‖b‖) : ‖b - A ⬝ x k‖ ≤ β * ‖b‖`
  (hence `Nat.find` of the MINRES stopping time `≤` that of CG).
* Backbone item: 3.4 (`IsMinRes.min`), 3.7 `CG.isGalerkinIterate` (gives `x_k^C ∈ 𝒦_k`).
* Proof route: `hx.2 _ (cg_mem_krylov k)`.
* Status: `direct`.

### R4.1 — Equation (4.1)
* Book statement: `‖r_k^C‖ = ‖r_k^M‖ / √(1 − ‖r_k^M‖²/‖r_{k−1}^M‖²)` (cited from Greenbaum Lemma 5.4.1 / Titley-Péloquin; implicitly `k ≥ 1`, `r_k^M ≠ 0`).
* Lean surface statement ✓:
  `theorem eq_4_1 (hA) (k : ℕ) (hk : (cr A b (k+1)).r ≠ 0) : ‖(cg A b (k+1)).r‖ = ‖(cr A b (k+1)).r‖ / Real.sqrt (1 - ‖(cr A b (k+1)).r‖ ^ 2 / ‖(cr A b k).r‖ ^ 2)`;
  also in the `IsMinresIterate` form with `x (k+1)`, `x k`.
* Backbone item: 3.6 `Krylov.inv_sq_norm_residual_minRes` ✓ (`1/‖r_{m+1}^G‖² = 1/‖r_m^G‖² + 1/‖r_{m+1}^F‖²` when `r_{m+1}^G ≠ 0`); 3.8 (CR residual strictly decreasing while `r_k ≠ 0`, unnamed).
* Proof route: from the identity, `1/‖r^C‖² = (1 − ‖r_k^M‖²/‖r_{k−1}^M‖²)/‖r_k^M‖²`; the bracket is `> 0` because
  `‖r_{k−1}‖² = ‖r_k‖² + α_k² ‖q_{k−1}‖²` with `α_k > 0`, `q_{k−1} ≠ 0` (Thm 2.1 (b) + Thm 2.2 (a) strict); then `Real.sqrt` algebra.
* Status: `needs-equivalence` (algebra at the surface; the strict residual decrease is gap G5; a Greenbaum-form corollary in 3.6 would make it `direct`).

### R4.2 — Telescoping product (§4.1.1, unnumbered)
* Book statement: if the rule `‖r_k‖ ≤ β‖b‖` (rule (3.4) with `α = 0`) first holds at iteration `l`, then `∏_{k=1}^{l} ‖r_k‖/‖r_{k−1}‖ = ‖r_l‖/‖b‖` (`≈ β`).
* Lean surface statement: `theorem prod_ratio_residual (r : ℕ → Vec n) (hr0 : r 0 = b) (hne : ∀ k < l, r k ≠ 0) : ∏ k ∈ Finset.range l, ‖r (k+1)‖ / ‖r k‖ = ‖r l‖ / ‖b‖`.
* Backbone item: none (Mathlib `Finset.prod_range_div'`).
* Proof route: telescoping.
* Status: `direct` (Mathlib). The "`≈ β`" and "on average closer to 1" remarks are heuristics (left out).

### R4.3 — Steihaug's theorem for CG on indefinite systems (§4.2)
* Book statement: when CG is applied to a symmetric (possibly indefinite) `A x = b` (notation of Table 2.1, `x_0 = 0`),
  the solution norms `‖x_1‖, …, ‖x_k‖` are strictly increasing as long as `p_jᵀ A p_j > 0` for all iterations `1 ≤ j ≤ k`.
* Lean surface statement ✓:
  `theorem steihaug_cg (A' : Matrix (Fin n) (Fin n) ℝ) (hA' : A'.IsSymm) (b) (k) (hpos : ∀ j < k, 0 < ⟪(cg A' b j).p, A' ⬝ (cg A' b j).p⟫_ℝ) : ∀ i < k, ‖(cg A' b i).x‖ < ‖(cg A' b (i+1)).x‖`
  (indexing per O7; strictness is justified since `p_iᵀ A p_i > 0 ⇒ p_i ≠ 0 ⇒ r_i ≠ 0 ⇒ α_{i+1} > 0`).
* Backbone item: 3.7 `CG.norm_iterate_monotone` ✓ (spd only, nonstrict); 3.11 "Steihaug's generalization (indefinite `A`)" (unnamed, unstated).
* Proof route: local argument (backbone 3.7 note): `⟪r_i, p_j⟫ = ‖r_j‖²` for `i ≤ j`, hence `⟪p_i, p_j⟫ ≥ 0`, hence `⟪x_{i}, p_i⟫ ≥ 0`; needs only symmetry and the positivity of the `i` denominators used so far.
* Status: `GAP` (G6: the backbone should state the L1 symmetric-indefinite strict version; the spd version is its corollary).

### R4.4 — The CR/MINRES analogue on indefinite systems (§4.2)
* Book statement: "From our proof of Theorem 2.2, we see that the same property holds for CR and MINRES as long as
  both `p_jᵀ A p_j > 0` and `r_jᵀ A r_j > 0` for all iterations `1 ≤ j ≤ k`."
* Lean surface statement (paper's form): `theorem steihaug_cr (hA' : A'.IsSymm) (k) (hp : ∀ j < k, 0 < ⟪(cr A' b j).p, A' ⬝ (cr A' b j).p⟫_ℝ) (hr : ∀ j < k, 0 < (cr A' b j).ρ) : ∀ i < k, ‖(cr A' b i).x‖ < ‖(cr A' b (i+1)).x‖`.
* Backbone item: 3.11 "resp. also `⟪r_j, A r_j⟫ > 0` (CR/MINRES)" (unnamed, unstated).
* Proof route: **unclear as stated.** The paper's own proof of Thm 2.2 (d) expands `p_i` in the complete orthogonal basis
  `{q_0, …, q_{ℓ−1}}` of `𝒬 = A 𝒦_ℓ`, which requires the CR recurrence to run to termination without breakdown
  (`ρ_j ≠ 0` for all `j < ℓ`, not only `j < k`); a purely local proof (hypotheses up to `k` only) is not given in the
  paper and may not exist (the component of `p_i` orthogonal to `span{q_0..q_{k−1}}` has no controlled sign). The
  safe statement supported by the paper's argument adds the global hypothesis `∀ j < ℓ, (cr A' b j).ρ ≠ 0` (no
  breakdown), or equivalently assumes both positivity conditions for all `j < ℓ`.
* Status: `GAP` (G7: hypotheses must be settled by the backbone; the paper's local formulation is unproven).

### R4.5 — MINRES subproblem in Lanczos coordinates (§4.2, unnumbered)
* Book statement: MINRES (and MINRES-QLP) compute `x_k^M = V_k y_k^M` with `y_k^M = argmin_{y ∈ ℝ^k} ‖T̲_k y − β_1 e_1‖`
  (and possibly `T_ℓ y_ℓ^M = β_1 e_1`); when `A` is nonsingular or the system is consistent, `y_k^M` is uniquely defined for each `k ≤ ℓ`.
* Lean surface statement: `theorem minres_subproblem (hA) (k) (hk : k ≤ lanczosTerm A b) (y : Fin k → ℝ) : IsMinresIterate A b k (∑ j, y j • lanczosVec A b j) ↔ IsLeast (Set.range fun z : Fin k → ℝ => ‖(‖b‖ • Pi.single 0 1 : Fin (k+1) → ℝ) - (lanczosT A b k).mulVec z‖) ‖(‖b‖ • Pi.single 0 1) - (lanczosT A b k).mulVec y‖`;
  `theorem minres_coeff_unique (hA) (hk : k ≤ lanczosTerm A b) : ∃! y, …`.
* Backbone item: 3.5 `Krylov.norm_residual_eq_norm_hessenberg`, `Krylov.isMinResIterate_of_isLeast` (plan; not in skeleton), 3.3 `Lanczos.tridiagExt`.
* Proof route: the isometry `‖b − A V_k y‖ = ‖β_1 e_1 − T̲_k y‖` (orthonormal columns) + `Lanczos.hessenberg_eq_tridiagExt`; uniqueness from `existsUnique_isMinRes_of_injOn` and linear independence of the Lanczos vectors.
* Status: `needs-equivalence` (index bookkeeping `Fin k`/`Fin (k+1)`; depends on 3.5 being formalized in the `Fin`-indexed form).

### R5.1 — Table 5.1 (the monotone entries)
* Book statement: on an spd system, for CG: `‖x_k‖ ↗` [Steihaug Thm 2.1], `‖x* − x_k‖ ↘` [HS Thm 4:3], `‖x* − x_k‖_A ↘` [HS Thm 6:3];
  for MINRES: `‖x_k‖ ↗` (Thm 2.3), `‖x* − x_k‖ ↘` (Thm 2.4), `‖x* − x_k‖_A ↘` (Thm 2.5), `‖r_k‖ ↘` [18; HS 7:2], `‖r_k‖/‖x_k‖ ↘` (Thm 3.1).
* Lean surface statement: `theorem cg_profile (hA) (hstar) : MonotoneProfile A xstar (fun k => (cg A b k).x)`;
  `theorem minres_profile (hA) (hstar) (x) (hx : ∀ k, IsMinresIterate A b k (x k)) : MinresProfile A b xstar x`;
  `theorem cr_profile (hA) (hstar) : MinresProfile A b xstar (fun k => (cr A b k).x)` (D11).
* Backbone item: CG column: 3.7 `CG.norm_iterate_monotone` ✓, `CG.norm_error_antitone` ✓, 2.4.2 `IsGalerkin.energyNorm_le_of_le` (skeleton) with `CG.isGalerkinIterate`; MINRES column: R2.6–R2.8, `IsMinRes.norm_residual_le` (skeleton), R3.6.
* Proof route: assemble the fields from the theorems above.
* Status: `direct` (modulo R3.6's gap G2 for the last field).

### R5.2 — Table 5.1 (the "not-monotonic" entries for CG)
* Book statement: for CG, `‖r_k‖` and `‖r_k‖/‖x_k‖` are not monotonic (in general).
* Lean surface statement (faithful reading: existence of counterexamples):
  `theorem cg_norm_residual_not_antitone : ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Vec 2), A.PosDef ∧ ¬ Antitone fun k => ‖(cg A b k).r‖`
  with witness `A = diag(1, 9)`, `b = (3, 1)`: `‖r_0‖² = 10`, `α_1 = 5/9`, `r_1 = (4/3, −4)`, `‖r_1‖² = 160/9 > 10`;
  `theorem cg_backwardError_not_antitoneOn : ∃ (n) (A : Matrix (Fin n) (Fin n) ℝ) (b), A.PosDef ∧ ¬ AntitoneOn (fun k => ‖(cg A b k).r‖ / ‖(cg A b k).x‖) (Set.Ici 1)`
  (a `2 × 2` example cannot work since `r_2 = 0`; a `3 × 3` witness must be found numerically — not yet done).
* Backbone item: none (surface-only computation with `norm_num`/`simp [cg, cgStep]` on explicit `Fin 2` data).
* Proof route: unfold two steps of `cg`; `EuclideanSpace.norm_eq`, `Fin.sum_univ_two`.
* Status: `direct` for `‖r_k‖`; the backward-error witness is an open surface task (no backbone content).

## Gaps and requests to the backbone

1. **G1 — `backwardError_eq` (2.2) is stated with the operator norm and fixed weights; the paper needs the
   Frobenius norm.** The paper's constraint set is `{ξ | ∃ E f, (A+E)x = b+f, ‖E‖_F/‖A‖_F ≤ αξ, ‖f‖/‖b‖ ≤ βξ}`;
   the operator-norm set is *larger* (`‖E‖_op ≤ ‖E‖_F`), so the backbone `IsLeast` does not specialize (its
   feasible set is not the paper's, and its formula has `‖A‖_op`). Proposal: state the theorem for an
   arbitrary "operator-dominating" norm and arbitrary nonnegative weights:
   `theorem backwardError_isLeast (N : (E →L[𝕜] E) → ℝ) (hN : ∀ T x, ‖T x‖ ≤ N T * ‖x‖) (hN1 : ∀ r y, N (rankOne r y) = ‖r‖ * ‖y‖) (A) (b y) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hden : 0 < a * ‖y‖ + c) : IsLeast {ξ | ∃ ΔA Δb, (A + ΔA) y = b + Δb ∧ N ΔA ≤ ξ * a ∧ ‖Δb‖ ≤ ξ * c} (‖b − A y‖ / (a * ‖y‖ + c))`
   plus the attainment lemma naming the optimal pair `(((1−ω)/‖y‖²) • rankOne r y, −ω • r)` with `ω = c/(a‖y‖ + c)`;
   instantiate `N = ‖·‖_op` (current statement) and, in an L4 file `LinearSolve/Perturbation/Matrix.lean`, `N = ‖·‖_F`
   on `Matrix n n 𝕜` via `toEuclideanLin`. Needs ForMathlib: `Matrix.frobenius_norm_vecMulVec : ‖vecMulVec r x‖ = ‖r‖ * ‖x‖`
   (Euclidean norms of `r, x`) and `‖A *ᵥ x‖ ≤ ‖A‖_F * ‖x‖` (if not already derivable from `Matrix.l2_opNorm_le_frobenius`-type lemmas).
   Note `E x = 0` at `y = 0`: with `hden`, `y = 0` forces `c > 0` and the formula still holds (`ω = 1`, `ΔA = 0`).
2. **G2 — `Krylov.IsMinResIterate.backwardError_antitone` (3.11, ✓ in `Proto2.lean`) is false as stated.**
   With `x₀ = 0` and Lean's `‖b‖/‖0‖ = 0`, `Antitone fun k => ‖b − A (x k)‖/‖x k‖` fails at `0 ≤ 1` unless `r_1 = 0`.
   Replace by (i) `AntitoneOn (fun k => ‖b − A (x k)‖ / ‖x k‖) (Set.Ici 1)` and (ii) the general form
   `theorem Krylov.IsMinResIterate.nrbe_antitone (hA) (hx) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) : Antitone fun k => ‖b − A (x k)‖ / (a * ‖x k‖ + c)`
   (with `0 ≤ c`, `0 < a` on `Set.Ici 1`). Also add the CG-side remark used in R3.5 as a lemma about any
   sequence with monotone norms (pure order lemma, could live next to it).
3. **G3 — Expose the CG/CR coefficients and state Thm 2.1/2.2 with names.** The prototypes hide `α, β` in
   `let`s inside `step`, so the paper's Thm 2.2 (a), (b) (`α_i ≥ 0`, `β_i ≥ 0`) cannot even be stated against
   the backbone. Request in 3.7/3.8: `CG.alpha A b x₀ k`, `CG.beta`, `CR.alpha`, `CR.beta`, `CR.rho` (:= `⟪r_k, A r_k⟫`)
   with `step`-unfolding lemmas (`CR.iterate_succ_x : x_{k+1} = x_k + alpha (k+1) • p_k`, etc.), `CR.q_eq_apply_p`,
   `CR.residual_eq` (twin of `CG.residual_eq`), and the named lemmas listed in R2.4/R2.5 including the strict forms
   `CR.rho_pos (hA) (h : r_k ≠ 0)`, `CR.alpha_pos`. Convention to fix: backbone `alpha k` = paper's `α_{k+1}`
   (0-based) or paper's `α_k` with `alpha 0 = 0`; the surface will provide `crAlpha_eq` either way.
4. **G4 — Termination characterization.** 3.7/3.8 only state "`r_k = 0` for `k ≥ grade`" (unnamed). The paper's
   `ℓ` ("first `k` with `r_k = 0`, `= ` Lanczos termination index, `≤ n`") needs the converse. Request in 3.1:
   `theorem Krylov.grade_le_of_apply_eq (hx : x ∈ 𝒦[A, b] k) (hAx : A x = b) : grade A b ≤ k`
   (if `x = q(A) b`, `deg q < k`, then `(1 − X q)(A) b = 0` with a nonzero polynomial of degree `≤ k`, so `A^d b ∈ 𝒦_d` for its degree `d ≤ k`),
   and in 3.4/3.7/3.8: `Krylov.IsMinResIterate.residual_eq_zero_iff (hinj) : b − A x = 0 ↔ grade A r₀ ≤ m`,
   `CG.residual_eq_zero_iff`, `CR.residual_eq_zero_iff`, `CR.iterate_eq_of_grade_le` (stationarity after termination).
5. **G5 — Strict monotonicity lemmas.** Thm 2.5 is *strict*; (4.1) needs `‖r_k^M‖ < ‖r_{k−1}^M‖` while `r_k^M ≠ 0`.
   Request in 3.8/3.11: `CR.energyNorm_error_lt (hA) (hstar) (h : r_k ≠ 0)`, `CR.norm_residual_lt (hA) (h : r_k ≠ 0)`
   (from `‖r_{k}‖² = ‖r_{k+1}‖² + α_{k+1}² ‖q_k‖²`), and their `IsMinResIterate` forms
   `Krylov.IsMinResIterate.energyNorm_error_lt_of_residual_ne_zero`, `…norm_residual_lt_of_residual_ne_zero` (spd, L3).
   Optionally the strict forms of Thm 2.3/2.4 (`‖x_k‖ < ‖x_{k+1}‖`, `‖x* − x_{k+1}‖ < ‖x* − x_k‖` while `r_k ≠ 0`).
   A Greenbaum-form corollary of `inv_sq_norm_residual_minRes` in 3.6,
   `‖r_{m+1}^F‖ = ‖r_{m+1}^G‖ / √(1 − ‖r_{m+1}^G‖²/‖r_m^G‖²)` under `‖r_{m+1}^G‖ < ‖r_m^G‖`, would make R4.1 `direct`.
6. **G6 — Steihaug for symmetric indefinite `A` (strict).** 3.7's `CG.norm_iterate_monotone` assumes
   `IsSymmetricCoercive` and is nonstrict; 3.11 mentions the generalization without a statement. Request (L1):
   `theorem CG.norm_iterate_lt_of_inner_apply_direction_pos (hA : A.IsSymmetric) (b) (k) (h : ∀ j < k, 0 < re⟪A p_j, p_j⟫) : ∀ i < k, ‖x_i‖ < ‖x_{i+1}‖` (iterates from `x₀ = 0`),
   and derive the spd `Monotone` version from it (`CG.inner_apply_direction_pos` supplies the hypothesis).
7. **G7 — CR/MINRES version of Steihaug (§4.2).** The paper's claim (hypotheses only for `j ≤ k`) is not
   supported by its proof sketch (see R4.4). The backbone should state the version it can prove; proposal:
   `CR.norm_iterate_lt_of_pos (hA : A.IsSymmetric) (hℓ : ∀ j < ℓ, ⟪r_j, A r_j⟫ ≠ 0) (h : ∀ j < k, 0 < ⟪A p_j, p_j⟫ ∧ 0 < ⟪r_j, A r_j⟫) : ∀ i < k, ‖x_i‖ < ‖x_{i+1}‖`
   where `ℓ` is the termination index, or an honest counterexample search showing the local version fails.
   The surface will state the paper's version and mark it with the extra hypothesis until settled.
8. **G8 — `IsGalerkin ⇔ IsMinOn` of the quadratic.** The plan lists `isGalerkin_iff_isMinOn_quadratic` (2.4.2) but the
   skeleton has only the ⇒ direction `IsGalerkin.quadratic_le`. The ⇐ direction is needed for the paper's *characterization*
   of CG ("`y_k^C = argmin φ(V_k y)`", R2.1 uniqueness). Request: `theorem isGalerkin_iff_isMinOn_quadratic (hA) [FiniteDimensional 𝕜 K] : IsGalerkin A b x₀ K x ↔ x − x₀ ∈ K ∧ IsMinOn (fun y => re⟪A y, y⟫/2 − re⟪b, y⟫) {y | y − x₀ ∈ K} x`
   (strict convexity of the quadratic on `x₀ + K`).
9. **G9 — Matrix ↔ `toEuclideanLin` glue (ForMathlib/Matrix).** Not in Mathlib (checked `v4.34.0-rc2`):
   `Matrix.toEuclideanLin_pow : toEuclideanLin (A ^ i) = toEuclideanLin A ^ i` (`toEuclideanLin_mul` exists only via `toLin'`),
   `Matrix.toEuclideanLin_one`, `EuclideanSpace.inner_toEuclideanLin : ⟪x, toEuclideanLin A y⟫ = ofLp x ⬝ᵥ (A *ᵥ ofLp y)` (real case),
   `Matrix.isSymm_iff_toEuclideanLin_isSymmetric` for real matrices (Mathlib has `isHermitian_iff_isSymmetric`; over `ℝ`, `IsHermitian ↔ IsSymm`).
   Also the L4 coercions announced in 3.1 ("coercions for matrices via `Matrix.toLin'` with `simp` lemmas") should be for
   `toEuclideanLin` (norm-aware), since every surface statement here involves norms.

Non-blocking dependencies (no change requested, just ordering): 3.3 `Lanczos` and 3.5 `Krylov/Hessenberg` (R1.1, R4.5)
and 3.11 `Krylov/Monotonicity` are in the plan but not yet in the skeleton.

## Left out

* §4 experiments: the test-set description, diagonal preconditioning, condition-number statistics, iteration limits `5n`/`n`, all
  of Figures 4.1–4.8 and their captions (percentages of monotone steps) — empirical, no theorem.
* §4.1.1's "cumulative minimum ≈" heuristic and "on average `‖r_k^M‖/‖r_{k−1}^M‖` closer to 1 if `l` is large" — informal reasoning;
  only the exact identities (4.1) and the telescoping product (R4.1–R4.2) are kept.
* §4.2: the `3 × 3` indefinite example (4.2) with its non-monotone plots — could be a computable counterexample
  (`¬ Monotone ‖x_k^M‖` for MINRES on an indefinite system), but the paper only reports it graphically; optional surface exercise.
* §4.2: the MINRES-QLP relationship (`Q_k [T̲_k β_1 e_1]`, `R_k P_k = L_k`, `W_k = V_k P_k`, `‖x_k^M‖ = ‖u_k‖`, the `χ²`
  update and "approximately monotonic") — a heuristic built on Choi–Paige–Saunders [3]; the identities belong to the Choi
  surface / backbone phase 2 (`Krylov/Singular.lean`, 3.12), and the paper draws no theorem from them.
* Table 5.2 (LSQR/LSMR properties) and the §5 discussion of least-squares solvers — results of other papers ([7], [8], [19]); the
  reduction "LSQR/LSMR = CG/MINRES on the normal equations" is a definition-level remark about other algorithms.
* §5 conclusions, acknowledgements, references, footnotes, key words.
* The literature attributions inside Table 5.1 (HS Thm 4:3, 6:3, 7:2, 7:4, 7:5; Steihaug Thm 2.1) are recorded in docstrings only.

## OCR uncertainties

(The PDF next to the OCR is password-protected and the `images/` folder contains only the figure crops, so these
were resolved by internal consistency with the proofs rather than by inspecting page images.)

* O1. Table 2.1 (OCR lines 57–87) has its three columns interleaved: the CR column appears as an HTML table before the
  CG column's plain-text lines, and the indexed CR column follows. Reconstruction used in D5/D6: CG = `x=0, r=b, ρ=‖r‖², p=r;
  q=Ap, α=ρ/pᵀq, x←x+αp, r←r−αq, ρ̄=ρ, ρ=rᵀr, β=ρ/ρ̄, p←r+βp`; CR = `x=0, r=b, s=Ar, ρ=rᵀs, p=r, q=s; (q=Ap), α=ρ/‖q‖²,
  x←x+αp, r←r−αq, s=Ar, ρ̄=ρ, ρ=rᵀs, β=ρ/ρ̄, p←r+βp, q←s+βq`. Consistent with the proofs of Thm 2.2 (`ρ_i = r_iᵀ s_i = r_iᵀ A r_i`,
  `α_i = ρ_{i−1}/‖q_{i−1}‖²`) and Thm 2.3.
* O2. Proof of Thm 2.3: `‖x_i‖² − ‖x_{i−1}‖² = 2α_i x_{i−1}ᵀ p_{i−1} + p_{i−1}ᵀ p_{i−1}` lacks the factor `α_i²` on the last term
  (OCR drop or typo in the original). Assumed `+ α_i² p_{i−1}ᵀ p_{i−1}`; the theorem is unaffected.
* O3. Proof of Thm 2.4: `x_l = x_{l−1} + α_{l−1} p_{l−1}` and `x_k + α_{k+1} p_k + ⋯ + α_{l−1} p_{l−1}` shift the `α` index by one
  relative to Table 2.1 (`x_k = x_{k−1} + α_k p_{k−1}` gives `α_{k+1} p_k + ⋯ + α_l p_{l−1}`); also `l` and `ℓ` are used for the same
  index. Assumed the Table 2.1 indexing; statements unaffected.
* O4. §2.1 defines `‖x* − x_k‖_A ≡ (x* − x_k)ᵀ A (x* − x_k)` without a square root (may be the paper's own abuse). We define the
  energy *norm* with the square root (D4); all monotonicity statements are invariant under squaring, and R2.1 records the
  squared identity `‖x* − x‖_A² = 2φ(x) + x*ᵀ A x*`.
* O5. Table 5.1: the CG entry "7 [21, Thm 2.1]" is the arrow `↗`; the last table row is the legend (`↗` monotonically increasing,
  `↘` monotonically decreasing); the MINRES entry for `‖r_k‖/‖x_k‖` reads "(Thm 3.1)" and is taken as `↘ (Thm 3.1)`.
* O6. Thm 2.2 (a): "The inequalities are strict until `i = ℓ` (and `r_ℓ = 0`)". Read as `ρ_i > 0` for `i < ℓ` and `α_i > 0` for
  `1 ≤ i ≤ ℓ` (so `β_i > 0` for `i < ℓ`), which is what the proofs of Thm 2.5 and (4.1) use.
* O7. §4.2 "as long as `p_jᵀ A p_j > 0` for all iterations `1 ≤ j ≤ k`" versus Table 2.1's indexing (iteration `j` uses `p_{j−1}`):
  interpreted as the directions used in iterations `1..k`, i.e. `p_0, …, p_{k−1}` (D10, R4.3); with the literal `p_1..p_k` the
  statement would also constrain the unused `p_k` and omit `p_0`, which contradicts Steihaug's original.
* O8. (3.2)–(3.3) and (3.5)–(3.6) are clean; the "`[12, p12]`, `[12, §7.1 and p336]`" pointers (Higham) are for `β = 0` and `α = β`.
* O9. Thm 2.2 (e) is proved only for `x_iᵀ p_i` ("Therefore `x_iᵀ p_i ≥ 0`") but stated for `x_iᵀ p_j`; the general case follows
  from `x_i = ∑ α_k p_{k−1}` and (d), and R2.5 states it for all `i, j`.
* O10. Title page: the OCR says "Report SOL 2011-2R (to appear in SQU Journal for Science, 17:1 (2012), 44–62)", not SIAM J. Sci.
  Comput.; the surface docstrings should cite the SQU version.
