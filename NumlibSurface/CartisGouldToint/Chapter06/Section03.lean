import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section02

/-!
# Cartis–Gould–Toint §6.3: Convexly constrained least-Euclidean-norm problems

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §6.3: `minimize_{x ∈ 𝒞} ‖r(x)‖`
for a residual `r : ℝⁿ → ℝᵐ` (`ℝⁿ = EuclideanSpace ℝ (Fin n)`) and a closed convex nonempty set
`𝒞`, attacked through `Φ_ℓ(x) = ‖r(x)‖^ℓ/ℓ` (5.1.3) by the ARpLE-CC algorithm (Algorithm 6.3.1):
the first-order convexly constrained method ARp1-CC (Algorithm 6.2.2, the backbone
`Optimization.IsFirstOrderCCStep`) applied to `Φ_ℓ`, with the termination tests (6.3.1)–(6.3.2).

## Main definitions

* `PhiEll r ℓ` — `Φ_ℓ` for a natural exponent `ℓ` (the same function as Chapter 5's `Phi`).
* `AssumptionPhiDpLC` — assumption Φℓ.DpL.C.
* `stopLE`, `algorithm_6_3_1` — the termination test and the ARpLE-CC run predicate.

## Main results

* `algorithm_6_3_1.exists_run` — ARpLE-CC runs exist.
* `arpleCC_decrease` — the decrease of `‖r‖^ℓ` (Lemma 6.2.4 for `Φ_ℓ`) and of the potential
  `‖r‖^{1/2^i}` ((6.3.3) with (5.1.27)).
* `theorem_6_3_1` — the complexity of ARpLE-CC.

## Deviations from the book

* The test (6.3.2), `ω_{Φ_ℓ,𝒞,1}(x)/‖r(x)‖^{ℓ-1} ≤ ε₁`, is written multiplicatively,
  `ω_{Φ_ℓ,𝒞,1}(x) ≤ ε₁ ‖r(x)‖^{ℓ-1}`; the two agree whenever (6.3.1) fails (`ε₀ ≥ 0`), and the
  multiplicative form avoids dividing by zero.
* The constants are those of ARp-CC (`ARpCCParams`, (6.2.7)); among the step-termination
  constants only `θ₁` plays a role.
* The display before (6.3.3) multiplies the unscaled measure `ω_{Φ_ℓ,𝒞,1}(x_{k+1})^{(p+1)/p}` by
  `‖r(x_{k+1})‖^{(ℓ-1)(p+1)/p}`, mixing the scaled and unscaled forms of (5.1.15); the decrease
  that holds (and is used) is `κ₁ ℓ ω_{Φ_ℓ,𝒞,1}(x_{k+1})^{(p+1)/p}` (`arpleCC_decrease`).
* Theorem 6.3.1 reads "(5.1.38) for (5.1.39)" (meant: "or"); the exponents printed `2^*` are
  `2^i`. Only `ι₁(p, ℓ, i) ≥ 0` is used, so the theorem is stated under that hypothesis (implied by
  (5.1.38) or (5.1.39), `Chapter05.lemma_5_1_6`); the book's `ε₀, ε₁ ≤ 1` is not needed.
-/

open Set Optimization
open scoped Nat

namespace CartisGouldToint.Chapter06

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-- The objective `Φ_ℓ(x) = ‖r(x)‖^ℓ/ℓ` of [cartis2022evaluation], (5.1.3), for a natural
exponent `ℓ`; the same function as Chapter 5's `Chapter05.Phi r ℓ` (`PhiEll_eq_Phi`). -/
noncomputable abbrev PhiEll (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) : ℝⁿ → ℝ :=
  residualPow r ℓ

theorem PhiEll_eq_Phi (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) : PhiEll r ℓ = Chapter05.Phi r ℓ :=
  rfl

theorem PhiEll_apply (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (x : ℝⁿ) : PhiEll r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  residualPow_natCast r ℓ x

/-- **Assumption Φℓ.DpL.C** ([cartis2022evaluation], §6.3): `Φ_ℓ` is `p` times continuously
differentiable on an open set `𝒟 ⊇ 𝒞` and its `p`-th derivative is Lipschitz on `𝒞` with
constant `L ≥ 0` (tensor norm = operator norm): f.DpL.C (`AssumptionDpLC`) for `f = Φ_ℓ`. -/
abbrev AssumptionPhiDpLC (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (C : Set ℝⁿ) (p : ℕ) (L : ℝ) : Prop :=
  AssumptionDpLC (PhiEll r ℓ) C p L

/-- Chapter 5's Φℓ.DpL is Φℓ.DpL.C with `𝒞 = ℝⁿ`. -/
theorem assumptionPhiDpLC_univ {r : ℝⁿ → ℝᵐ} {ℓ p : ℕ} {L : ℝ}
    (h : Chapter05.AssumptionPhiDpL r ℓ p L) : AssumptionPhiDpLC r ℓ univ p L :=
  ⟨h.nonneg, ⟨univ, isOpen_univ, subset_rfl, h.contDiff.contDiffOn⟩, h.lipschitz⟩

/-- The termination test of ARpLE-CC ([cartis2022evaluation], Algorithm 6.3.1, (6.3.1)–(6.3.2)):
`‖r(x)‖ ≤ ε₀` or `ω_{Φ_ℓ,𝒞,1}(x) ≤ ε₁ ‖r(x)‖^{ℓ-1}`. -/
def stopLE (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (C : Set ℝⁿ) (ε₀ ε₁ : ℝ) (x : ℝⁿ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ omega1 (PhiEll r ℓ) C x ≤ ε₁ * ‖r x‖ ^ (ℓ - 1)

/-- **Algorithm 6.3.1** (ARpLE-CC, [cartis2022evaluation]): ARp1-CC (Algorithm 6.2.2) applied to
`f = Φ_ℓ` from a feasible `x_0 ∈ 𝒞`, with the model (5.1.8)
`m_k = regularizedModel (ftaylorSeries ℝ Φ_ℓ (x k)) p (σ k)`, the step conditions
`Optimization.IsFirstOrderCCStep` (`x_k + s_k ∈ 𝒞`, `m_k(s_k) < m_k(0)`, (6.2.29) with `θ₁`), the
ratio (4.1.15), the update (4.1.16), and the termination test `stopLE`. -/
structure algorithm_6_3_1 (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams)
    (ε₀ ε₁ : ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop where
  /-- The initial point is feasible. -/
  mem_zero : x 0 ∈ C
  /-- The run of ARp1-CC with the test (6.3.1)–(6.3.2). -/
  run : IsARRun P.toARParams (fun k => stopLE r ℓ C ε₀ ε₁ (x k))
    (fun k => IsFirstOrderCCStep (PhiEll r ℓ) C p P.θ₁ (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio (PhiEll r ℓ) p x s) x s σ

/-- **Existence of ARpLE-CC runs** ([cartis2022evaluation], Algorithm 6.3.1): under C.CNe, if
`Φ_ℓ` is `C^p` at the points of `𝒞` (`p ≥ 1`) and `ε₁ ≥ 0`, there is a run from every
`x_0 ∈ 𝒞` (a failing test gives `ω_{Φ_ℓ,𝒞,1}(x_k) > 0`, so a global minimizer of the model over
the feasible steps is admissible, `Optimization.exists_isFirstOrderCCStep`). -/
theorem algorithm_6_3_1.exists_run {r : ℝⁿ → ℝᵐ} {ℓ : ℕ} {C : Set ℝⁿ} {p : ℕ} (P : ARpCCParams)
    {ε₀ ε₁ : ℝ} (hC : AssumptionCNe C) (hΦ : ∀ y ∈ C, ContDiffAt ℝ p (PhiEll r ℓ) y)
    (hp : 1 ≤ p) (hε₁ : 0 ≤ ε₁) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s : ℕ → ℝⁿ, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := stopLE r ℓ C ε₀ ε₁)
    (stepOK := fun y σ s => IsFirstOrderCCStep (PhiEll r ℓ) C p P.θ₁ y σ s)
    (fun y _ t => reductionRatio (PhiEll r ℓ) y t
      ((ftaylorSeries ℝ (PhiEll r ℓ) y).taylorDecrement p t))
    (fun y σ hy _ hσ ht => by
      have hω : 0 < omega1 (PhiEll r ℓ) C y := by
        simp only [stopLE, not_or, not_le] at ht
        exact lt_of_le_of_lt (by positivity) ht.2
      obtain ⟨s, -, hs, -⟩ := exists_isFirstOrderCCStep hC.isClosed hC.convex hy (hΦ y hy) hp
        hσ P.θ₁_pos.le hω
      exact ⟨s, hs, hs.mem⟩) hx₀
  exact ⟨x, s, σ, hx0, ⟨hx0 ▸ hx₀, hrun⟩⟩

namespace algorithm_6_3_1

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℕ} {C : Set ℝⁿ} {p : ℕ} {P : ARpCCParams} {ε₀ ε₁ L : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- The iterates of ARpLE-CC stay in `𝒞` up to (and including) termination. -/
theorem mem (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) : x k ∈ C :=
  h.run.mem h.mem_zero (fun _ hk _ _ => (h.run.step_of_forall_le hk).mem) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)

/-- Lemma 4.1.2 for ARpLE-CC ("Lemmas 4.1.1 and 4.1.2 continue to hold", §6.2.2): up to
termination the iterates are feasible and `σ_min ≤ σ_k ≤ σ_max = max(σ₀, γ₃ L/(1 - η₂))`. -/
theorem sigma_le (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hC : AssumptionCNe C)
    (hΦ : AssumptionPhiDpLC r ℓ C p L) {k : ℕ} (hk : ∀ j < k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  arpcc_sigma_le h.run hC hΦ h.mem_zero (fun _ hstep => ⟨hstep.mem, hstep.decrease⟩) k hk

/-- The residual norm does not increase along an ARpLE-CC run before termination (`ℓ ≥ 1`). -/
theorem norm_succ_le (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hℓ : 1 ≤ ℓ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) : ‖r (x (k + 1))‖ ≤ ‖r (x k)‖ := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  by_cases hs : P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k
  · obtain ⟨-, hdec⟩ := h.run.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk)
      (h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)).decrease hs
    have hσ : 0 ≤ σ k := (h.run.sigma_pos (K := k)
      (fun j hj => IsARRun.forall_le_not_stop_iff.2 hk j hj.le) k le_rfl).le
    have : 0 ≤ P.η₁ * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by
      have := P.η₁_pos; positivity
    have hle : PhiEll r ℓ (x (k + 1)) ≤ PhiEll r ℓ (x k) := by linarith
    rw [PhiEll_apply, PhiEll_apply, div_le_div_iff_of_pos_right hℓpos] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by omega)).1 hle
  · rw [h.run.eq_of_not_succ (IsARRun.forall_le_not_stop_iff.2 hk) (not_le.1 hs)]

/-- The residual norms stay below `‖r(x_0)‖` up to termination. -/
theorem norm_le_norm_zero (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hℓ : 1 ≤ ℓ) :
    ∀ k, (∀ j < k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) → ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  intro k
  induction k with
  | zero => exact fun _ => le_rfl
  | succ k ih =>
    intro hk
    exact (h.norm_succ_le hℓ fun j hj => hk j (Nat.lt_succ_of_le hj)).trans
      (ih fun j hj => hk j (hj.trans k.lt_succ_self))

end algorithm_6_3_1

section Decrease

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℕ} {C : Set ℝⁿ} {p : ℕ} {P : ARpCCParams} {ε₀ ε₁ L : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- **(6.3.3)** and the display before it ([cartis2022evaluation]): under C.CNe and Φℓ.DpL.C, on a
successful iteration `k` of ARpLE-CC before termination (`p, ℓ ≥ 1`):
`‖r(x_k)‖^ℓ - ‖r(x_{k+1})‖^ℓ ≥ κ₁ ℓ ω_{Φ_ℓ,𝒞,1}(x_{k+1})^{(p+1)/p}` (Lemma 6.2.4 for `f = Φ_ℓ`,
`κ₁` of (4.1.32) with `L = L_{Φ_ℓ,p}`); if moreover the test fails at `x_{k+1}`, then for every
`β ∈ (0, 1)`, `ε₀, ε₁ > 0` and `i` with `ι₁ = (2^i - 1)/2^i - (ℓ - 1)/p ≥ 0`,
`‖r(x_k)‖^{1/2^i} - ‖r(x_{k+1})‖^{1/2^i} ≥
min(κ_{r0}, κ_{r1}) min(ε₀^{1/2^i}, ε₁^{(p+1)/p}) / max(1, ‖r(x_0)‖^{ι₁})` with
`κ_{r0} = 1 - β^{1/2^i}`, `κ_{r1} = κ₁ β^{(ℓ-1)(p+1)/p}/2^i` ((6.3.3) with (5.1.27)). -/
theorem arpleCC_decrease (hC : AssumptionCNe C) (hΦ : AssumptionPhiDpLC r ℓ C p L)
    (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) (hs : P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k) :
    ℓ * kappa1CC P L p * omega1 (PhiEll r ℓ) C (x (k + 1)) ^ (((p : ℝ) + 1) / p) ≤
        ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ ∧
      (¬ stopLE r ℓ C ε₀ ε₁ (x (k + 1)) → ∀ i : ℕ,
        0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p → ∀ β : ℝ, 0 < β → β < 1 →
        0 < ε₀ → 0 < ε₁ →
        min (1 - β ^ (1 / 2 ^ i : ℝ))
            (kappa1CC P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i) *
          min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) /
          max 1 (‖r (x 0)‖ ^ (((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)) ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hk' : ∀ j ≤ k, ¬ IsARRun.Stop (fun k => stopLE r ℓ C ε₀ ε₁ (x k)) (fun _ => False) j :=
    fun j hj h' => h'.elim (hk j hj) id
  obtain ⟨hxk, hσ1, hσ2⟩ := h.sigma_le hC hΦ (k := k) fun j hj => hk j hj.le
  have hstep := h.run.step_of_forall_le hk'
  have hdec := hstep.sub_ge hC.convex hΦ.contDiffAt hΦ.lipschitz hΦ.nonneg hxk hp
    P.θ₁_pos.le P.σmin_nonneg hσ1 hσ2 P.η₁_pos hs
  rw [← h.run.eq_add_of_succ hk' hs, PhiEll_apply, PhiEll_apply] at hdec
  have hA : ℓ * kappa1CC P L p * omega1 (PhiEll r ℓ) C (x (k + 1)) ^ (((p : ℝ) + 1) / p) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := by
    have h1 : ‖r (x k)‖ ^ ℓ / ℓ - ‖r (x (k + 1))‖ ^ ℓ / ℓ =
        (‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) / ℓ := by ring
    rw [h1, le_div_iff₀ hℓpos] at hdec
    rw [kappa1CC, omega1]
    linarith
  refine ⟨hA, fun hnot i hι β hβ0 hβ1 hε₀ hε₁ => ?_⟩
  simp only [stopLE, not_or, not_le] at hnot
  have hba := h.norm_succ_le hℓ hk
  have haR := h.norm_le_norm_zero hℓ k fun j hj => hk j hj.le
  exact rpow_inv_two_pow_sub_ge_min hp hℓ hι hβ0 hβ1 (kappa1CC_pos hΦ.nonneg) hε₀
    hε₁ haR hba hnot.1 hnot.2 (by linarith)

/-- `R^a R^b ≤ R^{a+b}` for `R ≥ 0`, `a > 0` (equality if `R > 0`). -/
private theorem rpow_mul_rpow_le {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    R ^ a * R ^ b ≤ R ^ (a + b) := by
  rcases hR.lt_or_eq with hR | hR
  · rw [Real.rpow_add hR]
  · rw [← hR, Real.zero_rpow ha.ne', zero_mul]; exact Real.rpow_nonneg le_rfl _

/-- `1/κ_{r1} = 2^i/β^{(ℓ-1)(p+1)/p} κ^S_{ARp1CC}` with `κ_{r1} = κ_{1,CC} β^{(ℓ-1)(p+1)/p}/2^i`,
the book's form of the second entry of
`κ^S_{ARpLE,1}`. -/
theorem one_div_kappa1CC_mul_rpow_div_two_pow (hL : 0 ≤ L) {β : ℝ} (hβ : 0 < β) (i : ℕ) :
    1 / (kappa1CC P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i) =
      2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) * kappaSARp1CC P L p := by
  have h1 := kappa1CC_mul_kappaSARp1CC (P := P) hL p
  have := kappa1CC_pos (P := P) (p := p) hL
  have hβe : 0 < β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) := Real.rpow_pos_of_pos hβ _
  have hS : kappaSARp1CC P L p = 1 / kappa1CC P L p := by
    rw [eq_div_iff this.ne', mul_comm]; exact h1
  rw [hS]
  field_simp

@[deprecated one_div_kappa1CC_mul_rpow_div_two_pow (since := "2026-10-26")]
alias one_div_kappaR1 := one_div_kappa1CC_mul_rpow_div_two_pow

/-- **Theorem 6.3.1** ([cartis2022evaluation]): let `p ≥ 1`, `ℓ ≥ 2` and `i ≥ 0` be integers with
`ι₁ = (2^i - 1)/2^i - (ℓ - 1)/p ≥ 0` (which holds under (5.1.38) or (5.1.39)), `β ∈ (0, 1)`,
C.CNe, Φℓ.DpL.C and `ε₀, ε₁ > 0`. Then every ARpLE-CC run terminates at some `k_ε`
(the first index with `‖r(x_ε)‖ ≤ ε₀` or `ω_{Φ_ℓ,𝒞,1}(x_ε) ≤ ε₁ ‖r(x_ε)‖^{ℓ-1}`) after at most
`κ^A max[‖r_0‖^{1/2^i}, ‖r_0‖^{1-(ℓ-1)/p}] / min[ε₀^{1/2^i}, ε₁^{(p+1)/p}] + κ^C` evaluations of
`r` and `κ^S (same ratio) + 2` evaluations of its derivatives, with
`κ^S = max(1/(1 - β^{1/2^i}),`
`2^i/β^{(ℓ-1)(p+1)/p} (p+1)!/(η₁σ_min) ((L + σ_max + θ₁ p!)/p!)^{(p+1)/p})`,
`σ_max = max(σ₀, γ₃ L/(1 - η₂))` (5.1.60), `κ^A = κ^S (1 + |log γ₁|/log γ₂)` and
`κ^C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2` (5.1.61). -/
theorem theorem_6_3_1 {i : ℕ} (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ)
    (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hC : AssumptionCNe C) (hΦ : AssumptionPhiDpLC r ℓ C p L)
    (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) :
    ∃ kε, IsFirstHit (fun k => stopLE r ℓ C ε₀ ε₁ (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) * kappaSARp1CC P L p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k) kε : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) * kappaSARp1CC P L p) *
          max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2 := by
  have hL := hΦ.nonneg
  rw [← one_div_kappa1CC_mul_rpow_div_two_pow (ℓ := ℓ) hL hβ0 i]
  set α : ℝ := 1 / 2 ^ i with hαdef
  have hα : 0 < α := by positivity
  set R := ‖r (x 0)‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg _
  set ι := ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p with hιdef
  set κr0 := 1 - β ^ α with hκr0def
  set κr1 := kappa1CC P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i
  have hκr0 : 0 < κr0 := by have := Real.rpow_lt_one hβ0.le hβ1 hα; linarith
  have hκr1 : 0 < κr1 := by
    have := kappa1CC_pos (P := P) (p := p) hL; positivity
  set μ := min (ε₀ ^ α) (ε₁ ^ (((p : ℝ) + 1) / p)) with hμdef
  have hμ : 0 < μ := by positivity
  set δ := min κr0 κr1 * μ / max 1 (R ^ ι) with hδdef
  have hM1 : 0 < max 1 (R ^ ι) := one_pos.trans_le (le_max_left _ _)
  have hδ : 0 < δ := div_pos (mul_pos (lt_min hκr0 hκr1) hμ) hM1
  have hdec : ∀ k, (∀ j ≤ k + 1, ¬ IsARRun.Stop (fun k => stopLE r ℓ C ε₀ ε₁ (x k))
      (fun _ => False) j) → P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k →
      δ ≤ ‖r (x k)‖ ^ α - ‖r (x (k + 1))‖ ^ α := by
    intro k hk hs
    have hk' : ∀ j ≤ k + 1, ¬ stopLE r ℓ C ε₀ ε₁ (x j) := fun j hj h' => hk j hj (Or.inl h')
    exact (arpleCC_decrease hC hΦ h hp (by omega) (fun j hj => hk' j (hj.trans k.le_succ))
      hs).2 (hk' (k + 1) le_rfl) i hι β hβ0 hβ1 hε₀ hε₁
  obtain ⟨kε, hfirst, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease
    (σmax := P.sigmaMax L)
    (fun k hk => (h.sigma_le hC hΦ (k := k) fun j hj h' => hk j hj (Or.inl h')).2.2)
    (V := fun k => ‖r (x k)‖ ^ α) (Vlow := 0) hδ
    (fun k hk => Real.rpow_le_rpow (norm_nonneg _)
      (h.norm_succ_le (by omega) fun j hj h' => hk j hj (Or.inl h')) hα.le)
    (fun k _ => by positivity) hdec
  -- `‖r_0‖^{1/2^i}/δ ≤ κ^S M/μ`
  set κS := max (1 / κr0) (1 / κr1) with hκS
  have hmin : 1 / min κr0 κr1 ≤ κS := by
    rcases min_cases κr0 κr1 with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]; exact le_max_left _ _
    · rw [hm]; exact le_max_right _ _
  have hp0 : (p : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ p := by exact_mod_cast hp
                               positivity
  have hRM : R ^ α * max 1 (R ^ ι) ≤ max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) := by
    rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hR0 _), mul_one]
    refine max_le_max le_rfl ((rpow_mul_rpow_le hR0 hα).trans_eq ?_)
    congr 1
    rw [hαdef, hιdef]; field_simp; ring
  have hratio : R ^ α / δ ≤ κS * max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) / μ := by
    have hmpos : 0 < min κr0 κr1 := lt_min hκr0 hκr1
    calc R ^ α / δ = 1 / min κr0 κr1 * (R ^ α * max 1 (R ^ ι)) / μ := by
          rw [hδdef]; field_simp
      _ ≤ κS * max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) / μ := by
          refine div_le_div_of_nonneg_right ?_ hμ.le
          exact mul_le_mul hmin hRM (by positivity) ((one_div_pos.2 hmpos).le.trans hmin)
  have hκA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
    have := P.log_γ₂_pos; positivity
  refine ⟨kε, ?_, ?_, ?_⟩
  · simpa [isFirstHit_iff, IsARRun.Stop] using hfirst
  · simp only [sub_zero] at hF
    refine hF.trans ?_
    have := mul_le_mul_of_nonneg_left hratio hκA
    calc (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (R ^ α / δ) +
          ((|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2)
        ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (κS * max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) / μ) +
          ((|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2) :=
          by linarith
      _ = _ := by ring
  · simp only [sub_zero] at hD
    linarith

end Decrease

end CartisGouldToint.Chapter06
