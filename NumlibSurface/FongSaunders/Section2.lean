import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.Subspace
import Numlib.LinearSolve.Projection.Basic
import Numlib.LinearSolve.Projection.Optimality
import NumlibSurface.FongSaunders.Section1

/-!
# §2: CG and CR, their minimization properties and the monotonicity theorems

Surface file for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical
comparison*, SQU Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R).

The paper's Algorithm CG and Algorithm CR of Table 2.1 are transcribed literally as state
recurrences (`cg`, `cr`) and identified with the backbone's `CG.iterate` and `CR.iterate` at
`x₀ = 0` (`cg_eq_backbone`, `cr_eq_backbone`); everything else in §2 is then a specialization of
`Numlib`. Contents: the quadratic `φ` and the energy norm (§2.1); CG as the minimizer of `φ`,
equivalently of `‖x* − x_k‖_A`, over `𝒦_k` (§2.1); MINRES as the minimizer of `‖r_k‖` and the
coincidence of CR and MINRES on spd systems (§2.2, (2.1)); well-definedness and termination at
`ℓ ≤ n` (§2.3); the orthogonality relations of Theorem 2.1; the sign relations of Theorem 2.2;
and the monotonicity Theorems 2.3, 2.4 and 2.5.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

/-! ### D4: the quadratic form `φ` and the energy norm -/

/-- The paper's quadratic form `φ(x) = ½ xᵀ A x − bᵀ x` (§2.1). -/
noncomputable def phi (A : Matrix (Fin n) (Fin n) ℝ) (b x : Vec n) : ℝ :=
  1 / 2 * ⟪x, A ⬝ x⟫_ℝ - ⟪b, x⟫_ℝ

/-- The energy norm `‖v‖_A = √(vᵀ A v)` (§2.1 writes `‖·‖_A` for the square; every statement
below is invariant under squaring). -/
noncomputable def energyNorm (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) : ℝ :=
  Real.sqrt ⟪v, A ⬝ v⟫_ℝ

/-- The surface energy norm is the backbone energy norm of `toEuclideanLin A`. -/
theorem energyNorm_eq (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) :
    energyNorm A v = _root_.energyNorm (toEuclideanLin A) v := by
  rw [energyNorm, _root_.energyNorm, RCLike.re_to_real, real_inner_comm]

/-- The energy norm is nonnegative, being a square root. -/
theorem energyNorm_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) : 0 ≤ energyNorm A v :=
  Real.sqrt_nonneg _

/-- `‖v‖_A² = vᵀ A v` for `A ≻ 0`. -/
theorem energyNorm_sq (hA : A.PosDef) (v : Vec n) : energyNorm A v ^ 2 = ⟪v, A ⬝ v⟫_ℝ :=
  Real.sq_sqrt (inner_mulVecE_self_nonneg hA v)

/-- The surface quadratic form is the backbone one. -/
theorem phi_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x : Vec n) :
    phi A b x = RCLike.re (inner ℝ (toEuclideanLin A x) x) / 2 - RCLike.re (inner ℝ b x) := by
  rw [phi, RCLike.re_to_real, RCLike.re_to_real, real_inner_comm (A ⬝ x) x]
  ring

/-! ### D5: Algorithm CG (Table 2.1, column 1) -/

/-- The state of Algorithm CG: iterate `x`, residual `r`, `ρ = rᵀ r`, direction `p`. -/
structure CGState (n : ℕ) where
  /-- The iterate `x_k`. -/
  x : Vec n
  /-- The residual `r_k = b − A x_k`. -/
  r : Vec n
  /-- The scalar `ρ_k = r_kᵀ r_k`. -/
  ρ : ℝ
  /-- The search direction `p_k`. -/
  p : Vec n

/-- One iteration of Algorithm CG: `q = A p; α = ρ / pᵀ q; x ← x + α p; r ← r − α q;
ρ̄ = ρ, ρ = rᵀ r; β = ρ/ρ̄; p ← r + β p`. -/
noncomputable def cgStep (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : CGState n :=
  let q := A ⬝ s.p
  let α := s.ρ / ⟪s.p, q⟫_ℝ
  let r := s.r - α • q
  let ρ := ⟪r, r⟫_ℝ
  { x := s.x + α • s.p, r := r, ρ := ρ, p := r + (ρ / s.ρ) • s.p }

/-- The initialization of Algorithm CG: `x = 0, r = b, ρ = ‖r‖², p = r`. -/
noncomputable def cgInit (b : Vec n) : CGState n := { x := 0, r := b, ρ := ‖b‖ ^ 2, p := b }

/-- The `k`-th state of Algorithm CG.  Lean's `0 / 0 = 0` makes the recurrence stationary after
termination (`r = 0 ⇒ ρ = 0 ⇒ α = β = 0 ⇒ p = 0`), which is exactly the paper's "terminate when
`r = 0`", so no partiality is needed. -/
noncomputable def cg (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) : CGState n :=
  (cgStep A)^[k] (cgInit b)

/-- Algorithm CG starts at its initialization. -/
@[simp] theorem cg_zero : cg A b 0 = cgInit b := rfl

/-- One more CG iteration is one more `cgStep`. -/
theorem cg_succ (k : ℕ) : cg A b (k + 1) = cgStep A (cg A b k) :=
  Function.iterate_succ_apply' _ _ _

/-- The step length `α_k = ρ_{k−1} / p_{k−1}ᵀ q_{k−1}` (`α_0 := 0`, an unused junk value). -/
noncomputable def cgAlpha (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cg A b k).ρ / ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ

/-- The direction coefficient `β_k = ρ_k / ρ_{k−1}` (`β_0 := 0`). -/
noncomputable def cgBeta (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cg A b (k + 1)).ρ / (cg A b k).ρ

/-- The termination index `ℓ` of Algorithm CG. -/
noncomputable def cgTerm (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ :=
  sInf {k | (cg A b k).r = 0}

/-! ### D6: Algorithm CR (Table 2.1, columns 2–3) -/

/-- The state of Algorithm CR: iterate `x`, residual `r`, `s = A r`, `ρ = rᵀ s`, direction `p`
and `q = A p`. -/
structure CRState (n : ℕ) where
  /-- The iterate `x_k`. -/
  x : Vec n
  /-- The residual `r_k = b − A x_k`. -/
  r : Vec n
  /-- The auxiliary vector `s_k = A r_k`. -/
  s : Vec n
  /-- The scalar `ρ_k = r_kᵀ s_k = r_kᵀ A r_k`. -/
  ρ : ℝ
  /-- The search direction `p_k`. -/
  p : Vec n
  /-- The auxiliary vector `q_k = A p_k`. -/
  q : Vec n

/-- One iteration of Algorithm CR: `α = ρ/‖q‖²; x ← x + α p; r ← r − α q; s = A r; ρ̄ = ρ,
ρ = rᵀ s; β = ρ/ρ̄; p ← r + β p; q ← s + β q`. -/
noncomputable def crStep (A : Matrix (Fin n) (Fin n) ℝ) (st : CRState n) : CRState n :=
  let α := st.ρ / ‖st.q‖ ^ 2
  let r := st.r - α • st.q
  let s := A ⬝ r
  let ρ := ⟪r, s⟫_ℝ
  { x := st.x + α • st.p, r := r, s := s, ρ := ρ,
    p := r + (ρ / st.ρ) • st.p, q := s + (ρ / st.ρ) • st.q }

/-- The initialization of Algorithm CR: `x = 0, r = b, s = A r, ρ = rᵀ s, p = r, q = s`. -/
noncomputable def crInit (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : CRState n :=
  { x := 0, r := b, s := A ⬝ b, ρ := ⟪b, A ⬝ b⟫_ℝ, p := b, q := A ⬝ b }

/-- The `k`-th state of Algorithm CR.  As for `cg`, Lean's `0 / 0 = 0` makes the recurrence
stationary after termination. -/
noncomputable def cr (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) : CRState n :=
  (crStep A)^[k] (crInit A b)

/-- Algorithm CR starts at its initialization. -/
@[simp] theorem cr_zero : cr A b 0 = crInit A b := rfl

/-- One more CR iteration is one more `crStep`. -/
theorem cr_succ (k : ℕ) : cr A b (k + 1) = crStep A (cr A b k) :=
  Function.iterate_succ_apply' _ _ _

/-- The step length `α_k = ρ_{k−1} / ‖q_{k−1}‖²` (`α_0 := 0`). -/
noncomputable def crAlpha (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cr A b k).ρ / ‖(cr A b k).q‖ ^ 2

/-- The direction coefficient `β_k = ρ_k / ρ_{k−1}` (`β_0 := 0`). -/
noncomputable def crBeta (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cr A b (k + 1)).ρ / (cr A b k).ρ

/-- The termination index `ℓ` of Algorithm CR. -/
noncomputable def crTerm (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ :=
  sInf {k | (cr A b k).r = 0}

/-! ### The identification of `cg` and `cr` with the backbone recurrences

Both identifications hold for an arbitrary matrix `A`: positive definiteness is not needed. -/

/-- Table 2.1, column 1 is the backbone CG recurrence at `x₀ = 0`, with `ρ_k = ‖r_k‖²`. -/
theorem cg_eq_backbone (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) :
    cg A b k =
      { x := (CG.iterate (toEuclideanLin A) b 0 k).x,
        r := (CG.iterate (toEuclideanLin A) b 0 k).r,
        ρ := ‖(CG.iterate (toEuclideanLin A) b 0 k).r‖ ^ 2,
        p := (CG.iterate (toEuclideanLin A) b 0 k).p } := by
  induction k with
  | zero => simp [cgInit, CG.init]
  | succ k ih =>
    rw [cg_succ, ih, CG.iterate_succ]
    have halpha : ‖(CG.iterate (toEuclideanLin A) b 0 k).r‖ ^ 2 /
        ⟪(CG.iterate (toEuclideanLin A) b 0 k).p,
          A ⬝ (CG.iterate (toEuclideanLin A) b 0 k).p⟫_ℝ
        = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
      rw [CG.alpha, real_inner_self_eq_norm_sq, real_inner_comm]
    have hbeta : ‖(CG.step (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k)).r‖ ^ 2 /
        ‖(CG.iterate (toEuclideanLin A) b 0 k).r‖ ^ 2
        = CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
      rw [CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp only [cgStep, mulVecE_eq, halpha, real_inner_self_eq_norm_sq, ← CG.step_r]
    refine CGState.mk.injEq .. ▸ ⟨rfl, rfl, rfl, ?_⟩
    rw [hbeta]
    exact (CG.step_p _ _).symm

/-- Table 2.1, columns 2–3 are the backbone CR recurrence at `x₀ = 0`, with `s_k = A r_k` and
`ρ_k = r_kᵀ A r_k`. -/
theorem cr_eq_backbone (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) :
    cr A b k =
      { x := (CR.iterate (toEuclideanLin A) b 0 k).x,
        r := (CR.iterate (toEuclideanLin A) b 0 k).r,
        s := A ⬝ (CR.iterate (toEuclideanLin A) b 0 k).r,
        ρ := ⟪(CR.iterate (toEuclideanLin A) b 0 k).r,
          A ⬝ (CR.iterate (toEuclideanLin A) b 0 k).r⟫_ℝ,
        p := (CR.iterate (toEuclideanLin A) b 0 k).p,
        q := (CR.iterate (toEuclideanLin A) b 0 k).q } := by
  induction k with
  | zero => simp [crInit, CR.iterate, CR.init]
  | succ k ih =>
    rw [cr_succ, ih, CR.iterate_succ]
    have halpha : ⟪(CR.iterate (toEuclideanLin A) b 0 k).r,
        A ⬝ (CR.iterate (toEuclideanLin A) b 0 k).r⟫_ℝ /
          ‖(CR.iterate (toEuclideanLin A) b 0 k).q‖ ^ 2
        = CR.alpha (toEuclideanLin A) (CR.iterate (toEuclideanLin A) b 0 k) := by
      rw [CR.alpha, real_inner_self_eq_norm_sq]
    simp only [crStep, halpha]
    rfl

/-! ### The projections of the two identifications -/

/-- The paper's `x_k^C` is the backbone CG iterate. -/
@[simp] theorem cg_x (k : ℕ) : (cg A b k).x = (CG.iterate (toEuclideanLin A) b 0 k).x := by
  rw [cg_eq_backbone]

/-- The paper's `r_k^C` is the backbone CG residual. -/
@[simp] theorem cg_r (k : ℕ) : (cg A b k).r = (CG.iterate (toEuclideanLin A) b 0 k).r := by
  rw [cg_eq_backbone]

/-- The paper's `p_k^C` is the backbone CG direction. -/
@[simp] theorem cg_p (k : ℕ) : (cg A b k).p = (CG.iterate (toEuclideanLin A) b 0 k).p := by
  rw [cg_eq_backbone]

/-- `ρ_k = ‖r_k‖²`, the paper's invariant for Algorithm CG. -/
theorem cg_rho (k : ℕ) : (cg A b k).ρ = ‖(cg A b k).r‖ ^ 2 := by
  rw [cg_eq_backbone]

/-- The paper's `x_k` of Algorithm CR is the backbone CR iterate. -/
@[simp] theorem cr_x (k : ℕ) : (cr A b k).x = (CR.iterate (toEuclideanLin A) b 0 k).x := by
  rw [cr_eq_backbone]

/-- The paper's `r_k` of Algorithm CR is the backbone CR residual. -/
@[simp] theorem cr_r (k : ℕ) : (cr A b k).r = (CR.iterate (toEuclideanLin A) b 0 k).r := by
  rw [cr_eq_backbone]

/-- The paper's `p_k` of Algorithm CR is the backbone CR direction. -/
@[simp] theorem cr_p (k : ℕ) : (cr A b k).p = (CR.iterate (toEuclideanLin A) b 0 k).p := by
  rw [cr_eq_backbone]

/-- The paper's `q_k` of Algorithm CR is the backbone `q_k`. -/
@[simp] theorem cr_q (k : ℕ) : (cr A b k).q = (CR.iterate (toEuclideanLin A) b 0 k).q := by
  rw [cr_eq_backbone]

/-- `s_k = A r_k`, the paper's invariant for Algorithm CR. -/
theorem cr_s (k : ℕ) : (cr A b k).s = A ⬝ (cr A b k).r := by
  rw [cr_eq_backbone]

/-- `ρ_k = r_kᵀ A r_k` (the paper's (2.2)). -/
theorem cr_rho (k : ℕ) : (cr A b k).ρ = ⟪(cr A b k).r, A ⬝ (cr A b k).r⟫_ℝ := by
  rw [cr_eq_backbone]

/-- The paper's remark that `q = A p` in both methods. -/
theorem cr_q_eq (k : ℕ) : (cr A b k).q = A ⬝ (cr A b k).p := by
  rw [cr_q, cr_p]
  exact CR.q_eq _ _ _ k

/-- The state's residual field is the true residual, `r_k = b − A x_k`. -/
theorem cg_residual_eq (k : ℕ) : (cg A b k).r = b - A ⬝ (cg A b k).x := by
  rw [cg_r, cg_x]
  exact CG.residual_eq _ _ _ k

/-- The state's residual field is the true residual, `r_k = b − A x_k`. -/
theorem cr_residual_eq (k : ℕ) : (cr A b k).r = b - A ⬝ (cr A b k).x := by
  rw [cr_r, cr_x]
  exact CR.residual_eq _ _ _ k

/-- The paper's `α_{k+1}` for CG is the backbone's `CG.alpha` at step `k`. -/
theorem cgAlpha_eq (k : ℕ) :
    cgAlpha A b (k + 1) = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
  rw [cgAlpha, cg_rho, cg_r, cg_p, CG.alpha, real_inner_self_eq_norm_sq, real_inner_comm]

/-- The paper's `β_{k+1}` for CG is the backbone's `CG.beta` at step `k`. -/
theorem cgBeta_eq (k : ℕ) :
    cgBeta A b (k + 1) = CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
  rw [cgBeta, cg_rho, cg_rho, cg_r, cg_r, CG.beta, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, CG.iterate_succ]

/-- The paper's `α_{k+1}` for CR is the backbone's `CR.alpha` at step `k`. -/
theorem crAlpha_eq (k : ℕ) :
    crAlpha A b (k + 1) = CR.alpha (toEuclideanLin A) (CR.iterate (toEuclideanLin A) b 0 k) := by
  rw [crAlpha, cr_rho, cr_r, cr_q, CR.alpha, real_inner_self_eq_norm_sq]

/-! ### D7: MINRES iterates (2.1) -/

/-- MINRES at step `k`: `x ∈ 𝒦_k(A, b)` minimizes `‖b − A x‖` over `𝒦_k(A, b)` (the paper's
(2.1) with `x₀ = 0`).  Theorems "and hence MINRES" quantify over sequences satisfying this. -/
def IsMinresIterate (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) (x : Vec n) : Prop :=
  x ∈ krylov A b k ∧ ∀ y ∈ krylov A b k, ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖

/-- The surface MINRES specification is the backbone one at `x₀ = 0`. -/
theorem isMinresIterate_iff {k : ℕ} {x : Vec n} :
    IsMinresIterate A b k x ↔ Krylov.IsMinResIterate (toEuclideanLin A) b 0 k x := by
  have hK : Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A 0) k = krylov A b k := by
    rw [krylov_eq, map_zero, sub_zero]
  constructor
  · rintro ⟨hmem, hmin⟩
    exact ⟨by rw [sub_zero, hK]; exact hmem, fun y hy => hmin y (by rwa [sub_zero, hK] at hy)⟩
  · rintro ⟨hmem, hmin⟩
    rw [sub_zero, hK] at hmem
    exact ⟨hmem, fun y hy => hmin y (by rw [sub_zero, hK]; exact hy)⟩

/-- R2.2, last item: by definition a MINRES iterate minimizes the residual over `𝒦_k`. -/
theorem minres_norm_residual_le {k : ℕ} {x y : Vec n} (hx : IsMinresIterate A b k x)
    (hy : y ∈ krylov A b k) : ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖ := hx.2 y hy

/-! ### One-step unfoldings of the two recurrences -/

/-- The unused junk value `α_0 = 0`. -/
@[simp] theorem cgAlpha_zero : cgAlpha A b 0 = 0 := rfl

/-- The unused junk value `β_0 = 0`. -/
@[simp] theorem cgBeta_zero : cgBeta A b 0 = 0 := rfl

/-- The unused junk value `α_0 = 0`. -/
@[simp] theorem crAlpha_zero : crAlpha A b 0 = 0 := rfl

/-- The unused junk value `β_0 = 0`. -/
@[simp] theorem crBeta_zero : crBeta A b 0 = 0 := rfl

/-- `α_{k+1} = ρ_k / ‖q_k‖²`, the CR step length of Table 2.1. -/
theorem crAlpha_succ (k : ℕ) : crAlpha A b (k + 1) = (cr A b k).ρ / ‖(cr A b k).q‖ ^ 2 := rfl

/-- `β_k = ρ_k / ρ_{k−1}`: the backbone keeps this quotient inline in `CR.step`, so the sign of
`β_k` is a surface corollary (Theorem 2.2 (b)). -/
theorem crBeta_succ (k : ℕ) : crBeta A b (k + 1) = (cr A b (k + 1)).ρ / (cr A b k).ρ := rfl

/-- Table 2.1: `x_{k+1} = x_k + α_{k+1} p_k`. -/
theorem cr_succ_x (k : ℕ) :
    (cr A b (k + 1)).x = (cr A b k).x + crAlpha A b (k + 1) • (cr A b k).p := by
  rw [cr_succ, crAlpha]
  rfl

/-- Table 2.1: `r_{k+1} = r_k − α_{k+1} q_k`. -/
theorem cr_succ_r (k : ℕ) :
    (cr A b (k + 1)).r = (cr A b k).r - crAlpha A b (k + 1) • (cr A b k).q := by
  rw [cr_succ, crAlpha]
  rfl

/-- Table 2.1: `p_{k+1} = r_{k+1} + β_{k+1} p_k`. -/
theorem cr_succ_p (k : ℕ) :
    (cr A b (k + 1)).p = (cr A b (k + 1)).r + crBeta A b (k + 1) • (cr A b k).p := by
  rw [crBeta, cr_succ]
  rfl

/-- Table 2.1: `q_{k+1} = s_{k+1} + β_{k+1} q_k`. -/
theorem cr_succ_q (k : ℕ) :
    (cr A b (k + 1)).q = (cr A b (k + 1)).s + crBeta A b (k + 1) • (cr A b k).q := by
  rw [crBeta, cr_succ]
  rfl

/-! ### R2.1: CG minimizes `φ`, equivalently the energy-norm error (§2.1) -/

/-- CG realises the backbone Galerkin specification on `𝒦_k(A, b)`. -/
theorem cg_isGalerkinIterate (hA : A.PosDef) (k : ℕ) :
    Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k (cg A b k).x := by
  rw [cg_x]
  exact CG.isGalerkinIterate b 0 (isSymmetricCoercive_of_posDef hA) k

/-- §2.1: the CG iterate lies in the `k`-th Krylov subspace. -/
theorem cg_mem_krylov (hA : A.PosDef) (k : ℕ) : (cg A b k).x ∈ krylov A b k :=
  sub_zero_mem_subspace_iff.1 (cg_isGalerkinIterate hA k).mem

/-- `2 φ(x) = xᵀ A x − 2 xᵀ A x*` (§2.1). -/
theorem two_phi_eq {xstar x : Vec n} (hstar : A ⬝ xstar = b) :
    2 * phi A b x = ⟪x, A ⬝ x⟫_ℝ - 2 * ⟪x, A ⬝ xstar⟫_ℝ := by
  rw [phi, ← hstar, real_inner_comm (A ⬝ xstar) x]
  ring

/-- The identity behind "minimizing `φ` is minimizing `‖x* − x_k‖_A`" (§2.1, reading C3). -/
theorem energyNorm_sq_eq_two_phi_add (hA : A.PosDef) {xstar x : Vec n} (hstar : A ⬝ xstar = b) :
    energyNorm A (xstar - x) ^ 2 = 2 * phi A b x + ⟪xstar, A ⬝ xstar⟫_ℝ := by
  have h1 : ⟪xstar, A ⬝ x⟫_ℝ = ⟪x, A ⬝ xstar⟫_ℝ :=
    (inner_mulVecE_comm (isSymm_of_posDef hA) xstar x).trans (real_inner_comm x (A ⬝ xstar))
  rw [energyNorm_sq hA, two_phi_eq hstar, mulVecE_sub, inner_sub_left, inner_sub_right,
    inner_sub_right, h1]
  ring

/-- Minimizing `φ` over `𝒦_k` is minimizing the energy norm of the error (§2.1). -/
theorem isMinOn_phi_iff_energyNorm_min (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b)
    {k : ℕ} {x : Vec n} :
    IsMinOn (phi A b) (krylov A b k) x ↔
      ∀ y ∈ krylov A b k, energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  have key : ∀ u v : Vec n,
      (phi A b u ≤ phi A b v ↔ energyNorm A (xstar - u) ≤ energyNorm A (xstar - v)) := by
    intro u v
    have hu := energyNorm_sq_eq_two_phi_add hA hstar (x := u)
    have hv := energyNorm_sq_eq_two_phi_add hA hstar (x := v)
    have hnu := energyNorm_nonneg A (xstar - u)
    have hnv := energyNorm_nonneg A (xstar - v)
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  rw [isMinOn_iff]
  exact forall_congr' fun y => imp_congr_right fun _ => key x y

/-- R2.1 (⇒): a Galerkin iterate minimizes `φ` over `𝒦_k` (§2.1). -/
theorem isMinOn_phi_of_isGalerkinIterate (hA : A.PosDef) {k : ℕ} {x : Vec n}
    (hx : Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k x) :
    IsMinOn (phi A b) (krylov A b k) x := by
  rw [isMinOn_iff]
  intro y hy
  rw [phi_eq, phi_eq]
  exact IsGalerkin.quadratic_le (isSymmetricCoercive_of_posDef hA) hx
    (sub_zero_mem_subspace_iff.2 hy)

/-- R2.1: the Galerkin iterates on `𝒦_k` are exactly the minimizers of `φ` there (§2.1). -/
theorem isGalerkinIterate_iff_isMinOn_phi (hA : A.PosDef) {k : ℕ} {x : Vec n} :
    Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k x ↔
      x ∈ krylov A b k ∧ IsMinOn (phi A b) (krylov A b k) x := by
  have hstar : A ⬝ xstar A b = b := mulVecE_xstar hA
  refine ⟨fun hx => ⟨sub_zero_mem_subspace_iff.1 hx.mem,
    isMinOn_phi_of_isGalerkinIterate hA hx⟩, ?_⟩
  rintro ⟨hmem, hmin⟩
  refine (IsGalerkin.iff_energyNorm_min (isSymmetricCoercive_of_posDef hA) hstar).2
    ⟨sub_zero_mem_subspace_iff.2 hmem, fun y hy => ?_⟩
  have h := (isMinOn_phi_iff_energyNorm_min hA hstar).1 hmin y (sub_zero_mem_subspace_iff.1 hy)
  rwa [energyNorm_eq, energyNorm_eq] at h

/-- §2.1: `x_k^C` minimizes `φ` over `𝒦_k(A, b)`. -/
theorem cg_isMinOn_phi (hA : A.PosDef) (k : ℕ) :
    IsMinOn (phi A b) (krylov A b k) (cg A b k).x :=
  isMinOn_phi_of_isGalerkinIterate hA (cg_isGalerkinIterate hA k)

/-- §2.1: `x_k^C` minimizes `‖x* − x‖_A` over `𝒦_k(A, b)`. -/
theorem cg_energyNorm_le (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) (k : ℕ)
    {y : Vec n} (hy : y ∈ krylov A b k) :
    energyNorm A (xstar - (cg A b k).x) ≤ energyNorm A (xstar - y) :=
  (isMinOn_phi_iff_energyNorm_min hA hstar).1 (cg_isMinOn_phi hA k) y hy

/-- The minimizer of `φ` over `𝒦_k(A, b)` is unique, hence equal to `x_k^C`. -/
theorem cg_unique_min (hA : A.PosDef) {k : ℕ} {x : Vec n} (hx : x ∈ krylov A b k)
    (hmin : IsMinOn (phi A b) (krylov A b k) x) : x = (cg A b k).x := by
  rw [cg_x]
  exact Krylov.IsGalerkinIterate.eq_CG_iterate (isSymmetricCoercive_of_posDef hA)
    ((isGalerkinIterate_iff_isMinOn_phi hA).2 ⟨hx, hmin⟩)

/-! ### R2.2: MINRES minimizes `‖r_k‖`; CR and MINRES coincide on spd systems (§2.2) -/

/-- §2.2: CR minimizes the residual over `𝒦_k`, i.e. it is a MINRES iterate. -/
theorem cr_isMinresIterate (hA : A.PosDef) (k : ℕ) : IsMinresIterate A b k (cr A b k).x := by
  rw [isMinresIterate_iff, cr_x]
  exact CR.isMinResIterate b 0 (isSymmetricCoercive_of_posDef hA) k

/-- §2.2: MINRES iterates are unique on an spd system. -/
theorem isMinresIterate_unique (hA : A.PosDef) {k : ℕ} {x y : Vec n}
    (hx : IsMinresIterate A b k x) (hy : IsMinresIterate A b k y) : x = y := by
  rw [Krylov.IsMinResIterate.eq_CR_iterate (isSymmetricCoercive_of_posDef hA)
      (isMinresIterate_iff.1 hx),
    Krylov.IsMinResIterate.eq_CR_iterate (isSymmetricCoercive_of_posDef hA)
      (isMinresIterate_iff.1 hy)]

/-- §2.2: "CR and MINRES must generate the same iterates on spd systems". -/
theorem isMinresIterate_iff_eq_cr (hA : A.PosDef) (k : ℕ) (x : Vec n) :
    IsMinresIterate A b k x ↔ x = (cr A b k).x :=
  ⟨fun hx => isMinresIterate_unique hA hx (cr_isMinresIterate hA k),
    fun hx => hx ▸ cr_isMinresIterate hA k⟩

/-! ### R2.3: well-definedness and termination (§2.3) -/

/-- Well-definedness of CG: the denominator `p_kᵀ A p_k` is positive until termination. -/
theorem cg_inner_p_q_pos (hA : A.PosDef) {k : ℕ} (hk : (cg A b k).r ≠ 0) :
    0 < ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ := by
  rw [cg_p]
  have h := CG.re_inner_apply_direction_pos b 0 (isSymmetricCoercive_of_posDef hA)
    (k := k) (by rwa [cg_r] at hk)
  rw [RCLike.re_to_real] at h
  rwa [real_inner_comm]

/-- (2.2) with the strict inequality: `ρ_k = r_kᵀ A r_k > 0` until termination. -/
theorem cr_rho_pos (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) : 0 < (cr A b k).ρ := by
  rw [cr_rho]
  exact inner_mulVecE_self_pos hA hk

/-- CG terminates exactly at the Lanczos termination index `ℓ`. -/
theorem cg_residual_eq_zero_iff (hA : A.PosDef) (k : ℕ) :
    (cg A b k).r = 0 ↔ lanczosTerm A b ≤ k := by
  rw [cg_r]
  constructor
  · intro h
    by_contra hlt
    exact CG.residual_ne_zero_of_lt_grade b 0 (isSymmetricCoercive_of_posDef hA)
      (by rw [sub_mulVecE_zero]; exact not_le.1 hlt) h
  · intro h
    exact CG.residual_eq_zero_of_grade_le b 0 (isSymmetricCoercive_of_posDef hA)
      (by rwa [sub_mulVecE_zero])

/-- CR terminates exactly at the Lanczos termination index `ℓ`. -/
theorem cr_residual_eq_zero_iff (hA : A.PosDef) (k : ℕ) :
    (cr A b k).r = 0 ↔ lanczosTerm A b ≤ k := by
  constructor
  · intro h
    have h2 := cr_residual_eq (A := A) (b := b) k
    rw [h] at h2
    have hx : A ⬝ (cr A b k).x = b := (sub_eq_zero.1 h2.symm).symm
    have hle := Krylov.grade_le_of_apply_eq
      (sub_zero_mem_subspace_iff.2 (cr_isMinresIterate hA k).1) hx
    rwa [sub_mulVecE_zero] at hle
  · intro h
    rw [cr_r]
    exact CR.residual_eq_zero_of_grade_le b 0 (isSymmetricCoercive_of_posDef hA)
      (by rwa [sub_mulVecE_zero])

/-- The CR termination index is attained: `r_ℓ = 0`. -/
theorem cr_residual_crTerm (hA : A.PosDef) : (cr A b (crTerm A b)).r = 0 := by
  have hne : {k | (cr A b k).r = 0}.Nonempty :=
    ⟨lanczosTerm A b, (cr_residual_eq_zero_iff hA _).2 le_rfl⟩
  rw [crTerm]
  exact Nat.sInf_mem hne

/-- The CG termination index is attained: `r_ℓ = 0`. -/
theorem cg_residual_cgTerm (hA : A.PosDef) : (cg A b (cgTerm A b)).r = 0 := by
  have hne : {k | (cg A b k).r = 0}.Nonempty :=
    ⟨lanczosTerm A b, (cg_residual_eq_zero_iff hA _).2 le_rfl⟩
  rw [cgTerm]
  exact Nat.sInf_mem hne

/-- "This `ℓ` is the same as the `ℓ` at which the Lanczos process terminates" (§2.3). -/
theorem crTerm_eq_grade (hA : A.PosDef) : crTerm A b = lanczosTerm A b :=
  le_antisymm (Nat.sInf_le ((cr_residual_eq_zero_iff hA _).2 le_rfl))
    ((cr_residual_eq_zero_iff hA _).1 (cr_residual_crTerm (b := b) hA))

/-- CG terminates at the Lanczos termination index `ℓ` (§2.3). -/
theorem cgTerm_eq_grade (hA : A.PosDef) : cgTerm A b = lanczosTerm A b :=
  le_antisymm (Nat.sInf_le ((cg_residual_eq_zero_iff hA _).2 le_rfl))
    ((cg_residual_eq_zero_iff hA _).1 (cg_residual_cgTerm (b := b) hA))

/-- CG and CR terminate at the same index (§2.3). -/
theorem cgTerm_eq_crTerm (hA : A.PosDef) : cgTerm A b = crTerm A b :=
  (cgTerm_eq_grade hA).trans (crTerm_eq_grade hA).symm

/-- Termination happens in at most `n` steps. -/
theorem crTerm_le (hA : A.PosDef) : crTerm A b ≤ n :=
  (crTerm_eq_grade hA).le.trans (lanczosTerm_le A b)

/-- CG terminates in at most `n` steps. -/
theorem cgTerm_le (hA : A.PosDef) : cgTerm A b ≤ n :=
  (cgTerm_eq_grade hA).le.trans (lanczosTerm_le A b)

/-- `r_k = 0` forces `s_k = ρ_k = 0` and `p_k = q_k = 0` (§2.3). -/
theorem cr_of_residual_eq_zero {k : ℕ} (h : (cr A b k).r = 0) :
    (cr A b k).s = 0 ∧ (cr A b k).ρ = 0 ∧ (cr A b k).p = 0 ∧ (cr A b k).q = 0 := by
  have hs : (cr A b k).s = 0 := by rw [cr_s, h, mulVecE_zero]
  have hρ : (cr A b k).ρ = 0 := by rw [cr_rho, h, inner_zero_left]
  refine ⟨hs, hρ, ?_, ?_⟩ <;> rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hb : b = 0 := h
    simp [crInit, hb]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [cr_succ_p, h, crBeta, hρ, zero_div, zero_smul, add_zero]
  · have hb : b = 0 := h
    simp [crInit, hb]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [cr_succ_q, hs, crBeta, hρ, zero_div, zero_smul, add_zero]

/-- At termination all the CR quantities vanish: `r_ℓ = s_ℓ = p_ℓ = q_ℓ = 0`, `ρ_ℓ = β_ℓ = 0`. -/
theorem cr_term_state (hA : A.PosDef) :
    (cr A b (crTerm A b)).r = 0 ∧ (cr A b (crTerm A b)).s = 0 ∧ (cr A b (crTerm A b)).ρ = 0 ∧
      (cr A b (crTerm A b)).p = 0 ∧ (cr A b (crTerm A b)).q = 0 ∧
      crBeta A b (crTerm A b) = 0 := by
  have hr := cr_residual_crTerm (b := b) hA
  obtain ⟨hs, hρ, hp, hq⟩ := cr_of_residual_eq_zero hr
  refine ⟨hr, hs, hρ, hp, hq, ?_⟩
  rcases Nat.eq_zero_or_pos (crTerm A b) with h0 | hpos
  · rw [h0, crBeta]
  · obtain ⟨m, hm⟩ : ∃ m, crTerm A b = m + 1 := ⟨crTerm A b - 1, by omega⟩
    rw [hm, crBeta, ← hm, hρ, zero_div]

private theorem crStep_eq_self {st : CRState n} (hr : st.r = 0) (hs : st.s = 0) (hρ : st.ρ = 0)
    (hp : st.p = 0) (hq : st.q = 0) : crStep A st = st := by
  obtain ⟨x, r, s, ρ, p, q⟩ := st
  simp_all [crStep]

/-- Once the residual vanishes the CR recurrence is stationary. -/
theorem cr_stationary (hA : A.PosDef) {k : ℕ} (h : crTerm A b ≤ k) :
    cr A b k = cr A b (crTerm A b) := by
  obtain ⟨hr, hs, hρ, hp, hq, -⟩ := cr_term_state (A := A) (b := b) hA
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k _ ih => rw [cr_succ, ih, crStep_eq_self hr hs hρ hp hq]

/-! ### R2.4: Theorem 2.1 -/

/-- Theorem 2.1 (a): `q_iᵀ q_j = 0` for `i ≠ j`. -/
theorem theorem_2_1_a (hA : A.PosDef) {i j : ℕ} (hij : i ≠ j) :
    ⟪(cr A b i).q, (cr A b j).q⟫_ℝ = 0 := by
  rw [cr_q_eq, cr_q_eq]
  simp only [cr_p, mulVecE_eq]
  exact CR.inner_apply_direction_eq_zero b 0 (isSymmetricCoercive_of_posDef hA) hij

/-- Theorem 2.1 (b): `r_iᵀ q_j = 0` for `i ≥ j + 1`. -/
theorem theorem_2_1_b (hA : A.PosDef) {i j : ℕ} (hij : j + 1 ≤ i) :
    ⟪(cr A b i).r, (cr A b j).q⟫_ℝ = 0 := by
  rw [cr_q_eq]
  simp only [cr_p, cr_r, mulVecE_eq]
  exact CR.inner_residual_apply_direction_eq_zero b 0 (isSymmetricCoercive_of_posDef hA) hij

/-- `r_kᵀ q_k = ρ_k`: the CR analogue of `r_kᵀ p_k = ‖r_k‖²`. -/
theorem cr_inner_residual_q (hA : A.PosDef) (k : ℕ) :
    ⟪(cr A b k).r, (cr A b k).q⟫_ℝ = (cr A b k).ρ := by
  rw [cr_q_eq, cr_rho]
  simp only [cr_p, cr_r, mulVecE_eq]
  exact CR.inner_residual_apply_direction_eq b 0 (isSymmetricCoercive_of_posDef hA) le_rfl

/-! ### R2.5: Theorem 2.2 and (2.2) -/

/-- (2.2): `ρ_i = r_iᵀ A r_i ≥ 0`. -/
theorem equation_2_2 (hA : A.PosDef) (i : ℕ) : 0 ≤ (cr A b i).ρ := by
  rw [cr_rho]
  exact inner_mulVecE_self_nonneg hA _

/-- Theorem 2.2 (a): `α_i ≥ 0`. -/
theorem theorem_2_2_a (hA : A.PosDef) (i : ℕ) : 0 ≤ crAlpha A b i := by
  cases i with
  | zero => simp
  | succ k => rw [crAlpha_succ]; exact div_nonneg (equation_2_2 hA k) (sq_nonneg _)

/-- Theorem 2.2 (b): `β_i ≥ 0`. -/
theorem theorem_2_2_b (hA : A.PosDef) (i : ℕ) : 0 ≤ crBeta A b i := by
  cases i with
  | zero => simp
  | succ k => rw [crBeta_succ]; exact div_nonneg (equation_2_2 hA (k + 1)) (equation_2_2 hA k)

/-- Theorem 2.2 (c): `p_iᵀ q_j ≥ 0`. -/
theorem theorem_2_2_c (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).p, (cr A b j).q⟫_ℝ := by
  rw [cr_q_eq]
  simp only [cr_p, mulVecE_eq]
  have h := CR.re_inner_direction_apply_direction_nonneg b 0
    (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- Theorem 2.2 (d): `p_iᵀ p_j ≥ 0`. -/
theorem theorem_2_2_d (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).p, (cr A b j).p⟫_ℝ := by
  simp only [cr_p]
  have h := CR.re_inner_direction_nonneg b 0 (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- Theorem 2.2 (e): `x_iᵀ p_j ≥ 0` (for `x₀ = 0`). -/
theorem theorem_2_2_e (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).x, (cr A b j).p⟫_ℝ := by
  simp only [cr_x, cr_p]
  have h := CR.re_inner_iterate_direction_nonneg b (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- Theorem 2.2 (f): `r_iᵀ p_j ≥ 0`. -/
theorem theorem_2_2_f (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).r, (cr A b j).p⟫_ℝ := by
  simp only [cr_r, cr_p]
  have h := CR.re_inner_residual_direction_nonneg b 0 (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- The CR denominator vector `q_k` is nonzero until termination, so `α_{k+1}` is well defined. -/
theorem cr_q_ne_zero (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) : (cr A b k).q ≠ 0 := by
  intro h
  have hρ := cr_inner_residual_q (b := b) hA k
  rw [h, inner_zero_right] at hρ
  exact (cr_rho_pos hA hk).ne' hρ.symm

/-- The search direction is nonzero until termination. -/
theorem cr_direction_ne_zero (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) :
    (cr A b k).p ≠ 0 := fun h => cr_q_ne_zero hA hk (by rw [cr_q_eq, h, mulVecE_zero])

/-- Theorem 2.2 (a), strict form: `α_{k+1} > 0` while `r_k ≠ 0`. -/
theorem crAlpha_pos (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) :
    0 < crAlpha A b (k + 1) := by
  rw [crAlpha_succ]
  exact div_pos (cr_rho_pos hA hk) (pow_pos (norm_pos_iff.2 (cr_q_ne_zero hA hk)) 2)

/-- Theorem 2.2 (a), strict form in the paper's indexing: `α_i > 0` for `1 ≤ i ≤ ℓ`. -/
theorem theorem_2_2_a_strict (hA : A.PosDef) {i : ℕ} (hi : 1 ≤ i) (hℓ : i ≤ crTerm A b) :
    0 < crAlpha A b i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine crAlpha_pos hA fun h => ?_
  rw [cr_residual_eq_zero_iff hA, ← crTerm_eq_grade hA] at h
  omega

/-! ### R2.6: Theorem 2.3 -/

/-- Theorem 2.3 for CR: `‖x_k‖` increases monotonically. -/
theorem theorem_2_3_cr (hA : A.PosDef) : Monotone fun k => ‖(cr A b k).x‖ := by
  simp only [cr_x]
  exact CR.norm_iterate_monotone b (isSymmetricCoercive_of_posDef hA)

/-- Theorem 2.3 for MINRES: `‖x_k‖` increases monotonically. -/
theorem theorem_2_3_minres (hA : A.PosDef) {x : ℕ → Vec n}
    (hx : ∀ k, IsMinresIterate A b k (x k)) : Monotone fun k => ‖x k‖ :=
  Krylov.IsMinResIterate.norm_monotone (isSymmetricCoercive_of_posDef hA)
    fun k => isMinresIterate_iff.1 (hx k)

/-- Theorem 2.3, strict form: `‖x_k‖ < ‖x_{k+1}‖` while `r_k ≠ 0`. -/
theorem theorem_2_3_strict (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) :
    ‖(cr A b k).x‖ < ‖(cr A b (k + 1)).x‖ := by
  have hα := crAlpha_pos hA hk
  have hpn : 0 < ‖(cr A b k).p‖ := norm_pos_iff.2 (cr_direction_ne_zero hA hk)
  have h1 : 0 ≤ crAlpha A b (k + 1) * ⟪(cr A b k).x, (cr A b k).p⟫_ℝ :=
    mul_nonneg hα.le (theorem_2_2_e hA k k)
  have h2 : 0 < crAlpha A b (k + 1) ^ 2 * ‖(cr A b k).p‖ ^ 2 :=
    mul_pos (pow_pos hα 2) (pow_pos hpn 2)
  have hsq : ‖(cr A b k).x‖ ^ 2 < ‖(cr A b (k + 1)).x‖ ^ 2 := by
    rw [cr_succ_x, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hα, mul_pow]
    linarith
  nlinarith [norm_nonneg (cr A b k).x, norm_nonneg (cr A b (k + 1)).x]

/-! ### R2.7: Theorem 2.4 -/

/-- Theorem 2.4 for CR: `‖x* − x_k‖` decreases monotonically. -/
theorem theorem_2_4_cr (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    Antitone fun k => ‖xstar - (cr A b k).x‖ := by
  simp only [cr_x]
  exact CR.norm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar

/-- Theorem 2.4 for MINRES: `‖x* − x_k‖` decreases monotonically. -/
theorem theorem_2_4_minres (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) {x : ℕ → Vec n}
    (hx : ∀ k, IsMinresIterate A b k (x k)) : Antitone fun k => ‖xstar - x k‖ :=
  Krylov.IsMinResIterate.norm_error_antitone (isSymmetricCoercive_of_posDef hA)
    (fun k => isMinresIterate_iff.1 (hx k)) hstar

/-! ### R2.8: Theorem 2.5 -/

/-- Theorem 2.5 for CR, nonstrict form: `‖x* − x_k‖_A` decreases monotonically. -/
theorem theorem_2_5_cr_antitone (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    Antitone fun k => energyNorm A (xstar - (cr A b k).x) := by
  simp only [energyNorm_eq, cr_x]
  exact CR.energyNorm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar

/-- Theorem 2.5 for MINRES, nonstrict form. -/
theorem theorem_2_5_minres_antitone (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b)
    {x : ℕ → Vec n} (hx : ∀ k, IsMinresIterate A b k (x k)) :
    Antitone fun k => energyNorm A (xstar - x k) := by
  simp only [energyNorm_eq]
  exact Krylov.IsMinResIterate.energyNorm_error_antitone (isSymmetricCoercive_of_posDef hA)
    (fun k => isMinresIterate_iff.1 (hx k)) hstar

/-- Theorem 2.5 for CR, strict form: `‖x* − x_{k+1}‖_A < ‖x* − x_k‖_A` while `r_k ≠ 0`. -/
theorem theorem_2_5_cr (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) {k : ℕ}
    (hk : (cr A b k).r ≠ 0) :
    energyNorm A (xstar - (cr A b (k + 1)).x) < energyNorm A (xstar - (cr A b k).x) := by
  have hα := crAlpha_pos hA hk
  have hpp : 0 < ⟪(cr A b k).p, A ⬝ (cr A b k).p⟫_ℝ :=
    inner_mulVecE_self_pos hA (cr_direction_ne_zero hA hk)
  have h1 : 0 ≤ 2 * crAlpha A b (k + 1) * ⟪(cr A b (k + 1)).r, (cr A b k).p⟫_ℝ := by
    have := mul_nonneg hα.le (theorem_2_2_f (b := b) hA (k + 1) k)
    linarith
  have h2 : 0 < crAlpha A b (k + 1) ^ 2 * ⟪(cr A b k).p, A ⬝ (cr A b k).p⟫_ℝ :=
    mul_pos (pow_pos hα 2) hpp
  have hAe : A ⬝ (xstar - (cr A b (k + 1)).x) = (cr A b (k + 1)).r := by
    rw [mulVecE_sub, hstar, ← cr_residual_eq]
  have hsplit : xstar - (cr A b k).x
      = (xstar - (cr A b (k + 1)).x) + crAlpha A b (k + 1) • (cr A b k).p := by
    rw [cr_succ_x]; abel
  have hsq : energyNorm A (xstar - (cr A b (k + 1)).x) ^ 2
      < energyNorm A (xstar - (cr A b k).x) ^ 2 := by
    rw [energyNorm_sq hA, energyNorm_sq hA, hsplit,
      inner_mulVecE_add_smul (isSymm_of_posDef hA), hAe]
    linarith
  nlinarith [energyNorm_nonneg A (xstar - (cr A b k).x),
    energyNorm_nonneg A (xstar - (cr A b (k + 1)).x)]

/-- Theorem 2.5 for MINRES, strict form. -/
theorem theorem_2_5_minres (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) {x : ℕ → Vec n}
    (hx : ∀ k, IsMinresIterate A b k (x k)) {k : ℕ} (hk : b - A ⬝ x k ≠ 0) :
    energyNorm A (xstar - x (k + 1)) < energyNorm A (xstar - x k) := by
  have he : ∀ j, x j = (cr A b j).x := fun j => (isMinresIterate_iff_eq_cr hA j (x j)).1 (hx j)
  rw [he, he]
  refine theorem_2_5_cr hA hstar (k := k) ?_
  rw [cr_residual_eq]
  rwa [he k] at hk

end FongSaunders
