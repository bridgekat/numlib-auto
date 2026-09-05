import SaadSparse.Ch06.Relations

/-!
# Saad, §6.5.8: residual smoothing

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.5.8, together with the problem P-6.26.

Residual smoothing turns an arbitrary sequence of approximations `(x^O_m, r^O_m)` into a
sequence `(x^S_m, r^S_m)` with monotone residual norms. `smoothEta` is the coefficient `η_m` of
Algorithm 6.14, `mrs` is Algorithm 6.14 itself and `qmrs` its quasi-minimal variant QMRS, whose
scale factors `τ_m` are `qmrsTau`.

The bridge to the backbone is `smoothEta_eq` (the book's `η_m` is `Krylov.smoothingCoeff`) and
`mrs_eq` (Algorithm 6.14 run on `(x^O_m, b - A x^O_m)` computes `Krylov.mrs`); Lemma 6.18
(Weiss) is then `Krylov.inv_sq_norm_smoothing`, and "minimal residual smoothing of FOM gives
GMRES" is `Krylov.IsGalerkinIterate.mrs_isMinResIterate`, both from
`Numlib/Krylov/Relations.lean`. The remaining items — (6.77)–(6.79) and their QMRS analogues —
are the short inductions the book performs, shared here by the single private lemma
`residual_eq_weighted`.

§6.5.8 is real throughout in the book, so this file is written over `ℝ`.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section Smoothing

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-! ### D11: Algorithm 6.14 and QMRS -/

/-- **Algorithm 6.14**, line 3: `η_m = -(r^S_{m-1}, r^O_m - r^S_{m-1})/‖r^O_m - r^S_{m-1}‖₂²`.
The book's inner product `(x, y) = ∑ x_i ȳ_i` is Mathlib's `inner ℝ y x`. -/
noncomputable def smoothEta (s r : 𝔼) : ℝ := -inner ℝ (r - s) s / ‖r - s‖ ^ 2

/-- The book's `η_m` is the backbone's residual-minimizing smoothing coefficient. -/
theorem smoothEta_eq (s r : 𝔼) : smoothEta s r = Krylov.smoothingCoeff s r := by
  rw [smoothEta, Krylov.smoothingCoeff, inner_neg_right]
  simp [RCLike.ofReal_real_eq_id]

/-- **Algorithm 6.14** (minimal residual smoothing, Weiss): the smoothed pair
`(x^S_m, r^S_m)` produced from an original sequence `(x^O_m, r^O_m)`. -/
noncomputable def mrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼
  | 0 => (xO 0, rO 0)
  | m + 1 =>
      let p := mrs xO rO m
      let η := smoothEta p.2 (rO (m + 1))
      (p.1 + η • (xO (m + 1) - p.1), p.2 + η • (rO (m + 1) - p.2))

/-- The smoothed approximations `x^S_m` of Algorithm 6.14. -/
noncomputable abbrev mrsX (xO rO : ℕ → 𝔼) (m : ℕ) : 𝔼 := (mrs xO rO m).1

/-- The smoothed residuals `r^S_m` of Algorithm 6.14. -/
noncomputable abbrev mrsR (xO rO : ℕ → 𝔼) (m : ℕ) : 𝔼 := (mrs xO rO m).2

/-- The coefficient `η_{m+1}` of Algorithm 6.14 (`0`-based). -/
noncomputable abbrev mrsEta (xO rO : ℕ → 𝔼) (m : ℕ) : ℝ :=
  smoothEta (mrsR xO rO m) (rO (m + 1))

theorem mrsX_zero (xO rO : ℕ → 𝔼) : mrsX xO rO 0 = xO 0 := rfl

theorem mrsR_zero (xO rO : ℕ → 𝔼) : mrsR xO rO 0 = rO 0 := rfl

theorem mrsX_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    mrsX xO rO (m + 1) = mrsX xO rO m + mrsEta xO rO m • (xO (m + 1) - mrsX xO rO m) := rfl

theorem mrsR_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    mrsR xO rO (m + 1) = mrsR xO rO m + mrsEta xO rO m • (rO (m + 1) - mrsR xO rO m) := rfl

/-- QMRS (§6.5.8): `τ_0 = ρ_0` and `1/τ_m² = 1/τ_{m-1}² + 1/ρ_m²`, with `ρ_j = ‖r^O_j‖₂`. -/
noncomputable def qmrsTau (rO : ℕ → 𝔼) : ℕ → ℝ
  | 0 => ‖rO 0‖
  | m + 1 => Real.sqrt (1 / (1 / qmrsTau rO m ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2))

/-- QMRS (§6.5.8): the coefficient `η_m = τ_{m-1}²/(τ_{m-1}² + ρ_m²)` (`0`-based). -/
noncomputable def qmrsEta (rO : ℕ → 𝔼) (m : ℕ) : ℝ :=
  qmrsTau rO m ^ 2 / (qmrsTau rO m ^ 2 + ‖rO (m + 1)‖ ^ 2)

/-- **QMRS** (§6.5.8): Algorithm 6.14 with `η_m` replaced by the quasi-residual ratio. -/
noncomputable def qmrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼
  | 0 => (xO 0, rO 0)
  | m + 1 =>
      let p := qmrs xO rO m
      (p.1 + qmrsEta rO m • (xO (m + 1) - p.1), p.2 + qmrsEta rO m • (rO (m + 1) - p.2))

theorem qmrs_zero (xO rO : ℕ → 𝔼) : qmrs xO rO 0 = (xO 0, rO 0) := rfl

theorem qmrs_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    qmrs xO rO (m + 1) =
      ((qmrs xO rO m).1 + qmrsEta rO m • (xO (m + 1) - (qmrs xO rO m).1),
        (qmrs xO rO m).2 + qmrsEta rO m • (rO (m + 1) - (qmrs xO rO m).2)) := rfl

/-! ### The bridge to `Krylov.mrs` -/

/-- **D11**: Algorithm 6.14 applied to a sequence of iterates and their residuals computes the
backbone's minimal-residual smoothing, and its second component really is the residual of the
first. -/
theorem mrs_eq (A : Matrix (Fin n) (Fin n) ℝ) (b : 𝔼) (xO rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (xO j)) (m : ℕ) :
    mrsX xO rO m = Krylov.mrs (op A) b xO m ∧
      mrsR xO rO m = b - op A (Krylov.mrs (op A) b xO m) := by
  induction m with
  | zero => exact ⟨rfl, by rw [mrsR_zero, hr 0, Krylov.mrs]⟩
  | succ m ih =>
    obtain ⟨ihx, ihr⟩ := ih
    have hη : mrsEta xO rO m =
        Krylov.smoothingCoeff (b - op A (Krylov.mrs (op A) b xO m)) (b - op A (xO (m + 1))) := by
      rw [mrsEta, ihr, hr (m + 1), smoothEta_eq]
    have hx : mrsX xO rO (m + 1) = Krylov.mrs (op A) b xO (m + 1) := by
      rw [mrsX_succ, ihx, hη, Krylov.mrs]
    refine ⟨hx, ?_⟩
    rw [mrsR_succ, ihr, hη, hr (m + 1), Krylov.mrs]
    simp only [map_add, map_smul, map_sub]
    module

/-! ### Lemma 6.18 (Weiss), (6.76)–(6.77) -/

/-- A vector orthogonal to `r^O_0, …, r^O_m` is orthogonal to `r^S_m`: the smoothed residual is
a combination of the original ones. -/
theorem inner_mrsR_eq_zero (xO rO : ℕ → 𝔼) (w : 𝔼) :
    ∀ m : ℕ, (∀ i ≤ m, inner ℝ w (rO i) = 0) → inner ℝ w (mrsR xO rO m) = 0 := by
  intro m
  induction m with
  | zero => intro h; rw [mrsR_zero]; exact h 0 le_rfl
  | succ m ih =>
    intro h
    rw [mrsR_succ, inner_add_right, real_inner_smul_right, inner_sub_right,
      ih fun i hi => h i (by omega), h (m + 1) le_rfl]
    ring

/-- **(6.76)** (Lemma 6.18, Weiss): if `r^O_{m+1} ⟂ r^S_m` then
`1/‖r^S_{m+1}‖² = 1/‖r^S_m‖² + 1/‖r^O_{m+1}‖²`. -/
theorem eq_6_76 (xO rO : ℕ → 𝔼) {m : ℕ} (h0 : mrsR xO rO m ≠ 0) (h1 : rO (m + 1) ≠ 0)
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    1 / ‖mrsR xO rO (m + 1)‖ ^ 2 = 1 / ‖mrsR xO rO m‖ ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2 := by
  have hkey := Krylov.inv_sq_norm_smoothing (𝕜 := ℝ) h0 h1 horth
  rw [mrsR_succ, mrsEta, smoothEta_eq]
  exact hkey

/-- **(6.77)** (Lemma 6.18, Weiss): if `r^O_{m+1} ⟂ r^S_m` then
`η_{m+1} = ‖r^S_m‖²/(‖r^S_m‖² + ‖r^O_{m+1}‖²)`. -/
theorem eq_6_77 (xO rO : ℕ → 𝔼) {m : ℕ}
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    mrsEta xO rO m
      = ‖mrsR xO rO m‖ ^ 2 / (‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2) := by
  have hnum : inner ℝ (rO (m + 1) - mrsR xO rO m) (mrsR xO rO m) = -‖mrsR xO rO m‖ ^ 2 := by
    rw [inner_sub_left, horth, real_inner_self_eq_norm_sq]
    ring
  have hden : ‖rO (m + 1) - mrsR xO rO m‖ ^ 2
      = ‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2 := by
    rw [norm_sub_sq_real, horth]
    ring
  rw [mrsEta, smoothEta, hnum, hden, neg_neg]

/-! ### (6.78)–(6.79) and the QMRS identities

Both the smoothed and the quasi-smoothed residual obey the same recurrence, once the weight is
written in terms of the partial sums `∑_{i ≤ j} 1/ρ_i²`; this single induction gives (6.79) and
its QMRS analogue. -/

/-- The scalar identity behind (6.79). -/
private theorem smul_combination_eq {S rho : ℝ} (hS : 0 < S) (hr : 0 < rho) (u v : 𝔼) :
    (1 - S⁻¹ / (S⁻¹ + rho)) • (S⁻¹ • u) + (S⁻¹ / (S⁻¹ + rho)) • v
      = (S + 1 / rho)⁻¹ • (u + (1 / rho) • v) := by
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hr0 : rho ≠ 0 := ne_of_gt hr
  have hd : S⁻¹ + rho ≠ 0 := ne_of_gt (by have := inv_pos.2 hS; linarith)
  have hd2 : S + 1 / rho ≠ 0 := ne_of_gt (by have := one_div_pos.2 hr; linarith)
  have e1 : (1 - S⁻¹ / (S⁻¹ + rho)) * S⁻¹ = (S + 1 / rho)⁻¹ := by
    field_simp
    ring
  have e2 : S⁻¹ / (S⁻¹ + rho) = (S + 1 / rho)⁻¹ * (1 / rho) := by
    field_simp
    ring
  rw [smul_smul, e1, smul_add, smul_smul, e2]

private theorem sum_inv_sq_pos {rO : ℕ → 𝔼} {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    (0 : ℝ) < ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 :=
  Finset.sum_pos (fun j hj => one_div_pos.2 (pow_pos
    (norm_pos_iff.2 (hr j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))) 2)) ⟨0, by simp⟩

/-- The induction behind **(6.79)**: a sequence started at `r^O_0` and obeying the smoothing
recurrence with the weights of Lemma 6.18 is the weighted average of the original residuals. -/
private theorem residual_eq_weighted (rO S : ℕ → 𝔼) (hS0 : S 0 = rO 0) {m : ℕ}
    (hr : ∀ j ≤ m, rO j ≠ 0)
    (hstep : ∀ j < m, S (j + 1) = S j +
      ((∑ i ∈ Finset.range (j + 1), 1 / ‖rO i‖ ^ 2)⁻¹ /
        ((∑ i ∈ Finset.range (j + 1), 1 / ‖rO i‖ ^ 2)⁻¹ + ‖rO (j + 1)‖ ^ 2)) •
        (rO (j + 1) - S j)) :
    S m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  induction m with
  | zero =>
    have hne : ‖rO 0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (hr 0 le_rfl))
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [hS0, smul_smul, inv_mul_cancel₀ (one_div_ne_zero hne), one_smul]
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hSpos := sum_inv_sq_pos hrk
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    have hcomb : ∀ (t : ℝ) (a v : 𝔼), a + t • (v - a) = (1 - t) • a + t • v := by
      intro t a v
      module
    rw [hstep k (by omega), ih hrk (fun j hj => hstep j (by omega)), hcomb,
      Finset.sum_range_succ (fun j => 1 / ‖rO j‖ ^ 2) (k + 1),
      Finset.sum_range_succ (fun j => (1 / ‖rO j‖ ^ 2) • rO j) (k + 1)]
    exact smul_combination_eq hSpos hrpos _ _

/-! #### The QMRS scale factors -/

theorem qmrsTau_pos (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) : 0 < qmrsTau rO m := by
  induction m with
  | zero => rw [qmrsTau]; exact norm_pos_iff.2 (hr 0 le_rfl)
  | succ k ih =>
    have hk := ih fun j hj => hr j (by omega)
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    rw [qmrsTau]
    refine Real.sqrt_pos.2 (one_div_pos.2 ?_)
    have : (0 : ℝ) < 1 / qmrsTau rO k ^ 2 := by positivity
    have : (0 : ℝ) < 1 / ‖rO (k + 1)‖ ^ 2 := by positivity
    linarith

/-- The defining relation of QMRS: `1/τ_m² = ∑_{j ≤ m} 1/ρ_j²`. -/
theorem inv_qmrsTau_sq (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    1 / qmrsTau rO m ^ 2 = ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 := by
  induction m with
  | zero => rw [qmrsTau]; simp
  | succ k ih =>
    have hk := ih fun j hj => hr j (by omega)
    have hkpos := qmrsTau_pos rO fun j hj => hr j (Nat.le_succ_of_le hj)
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    have hsum : (0 : ℝ) < 1 / qmrsTau rO k ^ 2 + 1 / ‖rO (k + 1)‖ ^ 2 := by positivity
    rw [qmrsTau, Real.sq_sqrt (le_of_lt (one_div_pos.2 hsum)), one_div_one_div,
      Finset.sum_range_succ, ← hk]

/-- `τ_m² = (∑_{j ≤ m} 1/ρ_j²)⁻¹`. -/
theorem qmrsTau_sq (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    qmrsTau rO m ^ 2 = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ := by
  rw [← inv_qmrsTau_sq rO hr, one_div, inv_inv]

/-- **(6.79) for QMRS**: the quasi-smoothed residual is the weighted average of the original
residuals. -/
theorem qmrs_eq_6_79 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    (qmrs xO rO m).2 = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  refine residual_eq_weighted rO (fun j => (qmrs xO rO j).2) rfl hr fun j hj => ?_
  rw [qmrs_succ, qmrsEta, qmrsTau_sq rO fun i hi => hr i (by omega)]

/-- **(6.78) for QMRS**: the quasi-smoothed residual is the convex combination
`r^S_{m+1} = (ρ²/(ρ² + τ_m²)) r^S_m + (τ_m²/(ρ² + τ_m²)) r^O_{m+1}`. -/
theorem qmrs_eq_6_78 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : rO (m + 1) ≠ 0) :
    (qmrs xO rO (m + 1)).2
      = (‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2)) • (qmrs xO rO m).2 +
        (qmrsTau rO m ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2)) • rO (m + 1) := by
  have hrpos : (0 : ℝ) < ‖rO (m + 1)‖ ^ 2 := pow_pos (norm_pos_iff.2 hr) 2
  have hden : ‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2 ≠ 0 := by positivity
  have he : qmrsEta rO m = qmrsTau rO m ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2) := by
    rw [qmrsEta, add_comm (qmrsTau rO m ^ 2)]
  have he' : 1 - qmrsEta rO m
      = ‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2) := by
    rw [he]
    field_simp
    ring
  rw [qmrs_succ]
  simp only
  rw [show (qmrs xO rO m).2 + qmrsEta rO m • (rO (m + 1) - (qmrs xO rO m).2)
      = (1 - qmrsEta rO m) • (qmrs xO rO m).2 + qmrsEta rO m • rO (m + 1) by module, he', he]

/-! #### Algorithm 6.14 under the orthogonality hypothesis of Lemma 6.18 -/

/-- Under the hypothesis of Lemma 6.18, `1/‖r^S_m‖² = ∑_{j ≤ m} 1/ρ_j²`: the smoothed residual
norms are the QMRS scale factors. -/
theorem inv_sq_norm_mrsR (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    1 / ‖mrsR xO rO m‖ ^ 2 = ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 := by
  induction m with
  | zero => rw [mrsR_zero]; simp
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hk := ih hrk fun j hj => horth j (by omega)
    have hne : mrsR xO rO k ≠ 0 := by
      intro h0
      have hpos : (0 : ℝ) < 1 / ‖mrsR xO rO k‖ ^ 2 := hk ▸ sum_inv_sq_pos hrk
      rw [h0, norm_zero] at hpos
      norm_num at hpos
    rw [eq_6_76 xO rO hne (hr (k + 1) le_rfl) (horth k (by omega)), hk,
      Finset.sum_range_succ (fun j => 1 / ‖rO j‖ ^ 2) (k + 1)]

/-- Under the hypothesis of Lemma 6.18 the smoothed residual norms are exactly the QMRS scale
factors `τ_m`. -/
theorem norm_mrsR_eq_qmrsTau (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    ‖mrsR xO rO m‖ = qmrsTau rO m := by
  have h1 := inv_sq_norm_mrsR xO rO hr horth
  have h2 := inv_qmrsTau_sq rO hr
  have hne : ‖mrsR xO rO m‖ ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < 1 / ‖mrsR xO rO m‖ ^ 2 := h1 ▸ sum_inv_sq_pos hr
    rw [h0] at hpos
    norm_num at hpos
  have hsq : ‖mrsR xO rO m‖ ^ 2 = qmrsTau rO m ^ 2 := by
    have h3 : (‖mrsR xO rO m‖ ^ 2)⁻¹ = (qmrsTau rO m ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact h1.trans h2.symm
    exact inv_injective h3
  have hpos := qmrsTau_pos rO hr
  nlinarith [norm_nonneg (mrsR xO rO m), hpos, hsq]

/-- **§6.5.8**: under the hypothesis of Lemma 6.18, Algorithm 6.14 and QMRS coincide. -/
theorem mrs_eq_qmrs (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrs xO rO m = qmrs xO rO m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hk := ih hrk fun j hj => horth j (by omega)
    have hη : mrsEta xO rO k = qmrsEta rO k := by
      rw [eq_6_77 xO rO (horth k (by omega)), qmrsEta,
        norm_mrsR_eq_qmrsTau xO rO hrk fun j hj => horth j (by omega)]
    rw [qmrs_succ, ← hk]
    have hx : mrs xO rO (k + 1) =
        (mrsX xO rO k + mrsEta xO rO k • (xO (k + 1) - mrsX xO rO k),
          mrsR xO rO k + mrsEta xO rO k • (rO (k + 1) - mrsR xO rO k)) := rfl
    rw [hx, hη]

/-- **(6.78)**: `r^S_{m+1} = (ρ²/(ρ² + τ_m²)) r^S_m + (τ_m²/(ρ² + τ_m²)) r^O_{m+1}` with
`τ_m = ‖r^S_m‖`. -/
theorem eq_6_78 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m + 1, rO j ≠ 0)
    (horth : ∀ j < m + 1, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrsR xO rO (m + 1)
      = (‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + ‖mrsR xO rO m‖ ^ 2)) • mrsR xO rO m +
        (‖mrsR xO rO m‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + ‖mrsR xO rO m‖ ^ 2)) • rO (m + 1) := by
  have hrk : ∀ j ≤ m, rO j ≠ 0 := fun j hj => hr j (by omega)
  have hτ := norm_mrsR_eq_qmrsTau xO rO hrk fun j hj => horth j (by omega)
  have hq := qmrs_eq_6_78 xO rO (hr (m + 1) le_rfl)
  have h1 : mrsR xO rO (m + 1) = (qmrs xO rO (m + 1)).2 :=
    congrArg Prod.snd (mrs_eq_qmrs xO rO hr horth)
  have h2 : mrsR xO rO m = (qmrs xO rO m).2 :=
    congrArg Prod.snd (mrs_eq_qmrs xO rO hrk fun j hj => horth j (by omega))
  rw [h1, hq, ← h2, hτ]

/-- **(6.79)**: the smoothed residual is the weighted average
`r^S_m = (∑_{j ≤ m} r^O_j/ρ_j²)/(∑_{j ≤ m} 1/ρ_j²)`. -/
theorem eq_6_79 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrsR xO rO m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  rw [show mrsR xO rO m = (qmrs xO rO m).2 from
    congrArg Prod.snd (mrs_eq_qmrs xO rO hr horth)]
  exact qmrs_eq_6_79 xO rO hr

/-- **Lemma 6.18** (Weiss), as stated in the book: under `r^O_{m+1} ⟂ r^S_m` the smoothed
residual norms satisfy (6.76) and the coefficient is given by (6.77). -/
theorem lemma_6_18 (xO rO : ℕ → 𝔼) {m : ℕ} (h0 : mrsR xO rO m ≠ 0)
    (h1 : rO (m + 1) ≠ 0)
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    1 / ‖mrsR xO rO (m + 1)‖ ^ 2 = 1 / ‖mrsR xO rO m‖ ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2 ∧
      mrsEta xO rO m
        = ‖mrsR xO rO m‖ ^ 2 / (‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2) :=
  ⟨eq_6_76 xO rO h0 h1 horth, eq_6_77 xO rO horth⟩

end Smoothing

/-! ### §6.5.8: minimal residual smoothing of FOM gives GMRES -/

section FOM

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The smoothed iterate stays in the affine space `x_0 + 𝒦_m`. -/
theorem mrsX_sub_mem (xO rO : ℕ → 𝔼) {m : ℕ}
    (hO : ∀ i ≤ m, xO i - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) i) :
    mrsX xO rO m - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) m := by
  induction m with
  | zero => rw [mrsX_zero]; exact hO 0 le_rfl
  | succ k ih =>
    have hmono := Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ k)
    have ihk := ih fun i hi => hO i (by omega)
    rw [mrsX_succ, show mrsX xO rO k + mrsEta xO rO k • (xO (k + 1) - mrsX xO rO k) - x₀
        = (mrsX xO rO k - x₀) + mrsEta xO rO k • ((xO (k + 1) - x₀) - (mrsX xO rO k - x₀)) by
      module]
    exact Submodule.add_mem _ (hmono ihk)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hO (k + 1) le_rfl) (hmono ihk)))

/-- **§6.5.8**: minimal residual smoothing of a sequence of Galerkin (FOM) iterates produces the
minimal-residual (GMRES) iterates. -/
theorem mrs_isMinResIterate (hA : IsUnit A) (xO rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (xO j))
    (hO : ∀ m, Krylov.IsGalerkinIterate (op A) b x₀ m (xO m)) (m : ℕ) :
    Krylov.IsMinResIterate (op A) b x₀ m (mrsX xO rO m) := by
  rw [(mrs_eq A b xO rO hr m).1]
  exact Krylov.IsGalerkinIterate.mrs_isMinResIterate hO (injective_op_of_isUnit hA) m

/-- **§6.5.8**: minimal residual smoothing of the FOM approximations produces exactly the GMRES
approximations. The FOM residuals are mutually orthogonal, so Lemma 6.18 applies at every step
and the smoothed residual norms satisfy (6.66)–(6.67); GMRES minimizes over the same subspace,
so the two sequences agree. -/
theorem mrs_fom_eq_gmres (hA : IsUnit A) (rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (fomFixed A b x₀ j)) {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : ∀ i ≤ m, FOMDefined A b x₀ i) (h0 : ρG A b x₀ m ≠ 0) :
    mrsX (fomFixed A b x₀) rO m = gmresFixed A b x₀ m := by
  have hgal : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (fomFixed A b x₀ i) :=
    fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi)
  have hG := gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl))
  have hrne : ∀ j ≤ m, rO j ≠ 0 := by
    intro j hj hz
    rw [hr j] at hz
    have hAy : op A (fomFixed A b x₀ j) = b := (sub_eq_zero.1 hz).symm
    have hex := hG.apply_eq_of_exists
      (Krylov.subspace_mono (op A) (b - op A x₀) hj (hgal j hj).mem) hAy
    exact h0 (norm_eq_zero.2 (by rw [hex, sub_self]))
  have hpair : ∀ i ≤ m, ∀ j ≤ m, i ≠ j → inner ℝ (rO i) (rO j) = 0 := by
    intro i hi j hj hij
    rw [hr i, hr j]
    exact Krylov.IsGalerkinIterate.inner_residual_eq_zero (hgal i hi) (hgal j hj) hij
  have horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR (fomFixed A b x₀) rO j) = 0 := fun j hj =>
    inner_mrsR_eq_zero (fomFixed A b x₀) rO _ j fun i hi =>
      hpair (j + 1) (by omega) i (by omega) (by omega)
  have hsum := inv_sq_norm_mrsR (fomFixed A b x₀) rO hrne horth
  have h66 := eq_6_66 A b x₀ hm hH h0
  have heq := mrs_eq A b (fomFixed A b x₀) rO hr m
  have hres : mrsR (fomFixed A b x₀) rO m
      = b - op A (mrsX (fomFixed A b x₀) rO m) := by rw [heq.1]; exact heq.2
  have hGpos : 0 < ρG A b x₀ m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hnorm : ‖b - op A (mrsX (fomFixed A b x₀) rO m)‖ = ρG A b x₀ m := by
    rw [← hres]
    have hsum' : 1 / ‖mrsR (fomFixed A b x₀) rO m‖ ^ 2 = 1 / ρG A b x₀ m ^ 2 := by
      rw [hsum, ← h66]
      exact Finset.sum_congr rfl fun j _ => by rw [hr j]
    have hne : ‖mrsR (fomFixed A b x₀) rO m‖ ≠ 0 := by
      intro hz
      rw [hz] at hsum'
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at hsum'
      exact (one_div_pos.2 (pow_pos hGpos 2)).ne hsum'
    have hsq : ‖mrsR (fomFixed A b x₀) rO m‖ ^ 2 = ρG A b x₀ m ^ 2 := by
      field_simp at hsum'
      linarith
    nlinarith [norm_nonneg (mrsR (fomFixed A b x₀) rO m), hGpos, hsq]
  have hmres : Krylov.IsMinResIterate (op A) b x₀ m (mrsX (fomFixed A b x₀) rO m) := by
    refine ⟨mrsX_sub_mem A b x₀ _ rO fun i hi => (hgal i hi).mem, fun y hy => ?_⟩
    rw [hnorm]
    exact hG.min y hy
  obtain ⟨z, -, huniq⟩ :=
    Krylov.existsUnique_isMinResIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [huniq _ hmres, huniq _ hG]

/-- **(6.79)** for a sequence of Galerkin (FOM) iterates, read off the backbone directly. -/
theorem residual_mrs_eq (hA : IsUnit A) (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - op A (xO j))
    (hO : ∀ m, Krylov.IsGalerkinIterate (op A) b x₀ m (xO m)) {m : ℕ}
    (h0 : ∀ j ≤ m, rO j ≠ 0) :
    mrsR xO rO m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  have hkey := Krylov.residual_mrs_eq hO (injective_op_of_isUnit hA) m
    (fun j hj => by rw [← hr j]; exact h0 j hj)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hkey
  rw [(mrs_eq A b xO rO hr m).2, hkey]
  simp only [← hr]

/-- **P-6.26**: the directions `x^O_{j+1} - x^S_j` produced by Algorithm 6.14 from a sequence of
Galerkin iterates are `AᵀA`-orthogonal, the hypothesis of Lemma 6.21 (GCR / ORTHOMIN). -/
theorem p_6_26 (hA : IsUnit A) (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - op A (xO j))
    (hO : ∀ m, Krylov.IsGalerkinIterate (op A) b x₀ m (xO m)) {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (op A (xO (i + 1) - mrsX xO rO i)) (op A (xO (j + 1) - mrsX xO rO j)) = 0 := by
  have hmemS : ∀ k, mrsX xO rO k - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) k :=
    fun k => mrsX_sub_mem A b x₀ xO rO fun i _ => (hO i).mem
  have hres : ∀ k, mrsR xO rO k = b - op A (mrsX xO rO k) := fun k => by
    have h := mrs_eq A b xO rO hr k
    rw [h.1]
    exact h.2
  have hminres : ∀ k, Krylov.IsMinResIterate (op A) b x₀ k (mrsX xO rO k) :=
    fun k => mrs_isMinResIterate A b x₀ hA xO rO hr hO k
  have key : ∀ p q : ℕ, p < q →
      inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (op A (xO (q + 1) - mrsX xO rO q)) = 0 := by
    intro p q hpq
    have hmem : op A (xO (p + 1) - mrsX xO rO p)
        ∈ (Krylov.subspace (op A) (b - op A x₀) q).map (op A) := by
      refine Submodule.mem_map_of_mem ?_
      rw [show xO (p + 1) - mrsX xO rO p = (xO (p + 1) - x₀) - (mrsX xO rO p - x₀) by abel]
      exact Submodule.sub_mem _
        (Krylov.subspace_mono (op A) (b - op A x₀) (by omega) (hO (p + 1)).mem)
        (Krylov.subspace_mono (op A) (b - op A x₀) (by omega) (hmemS p))
    have h1 : inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (mrsR xO rO q) = 0 := by
      rw [hres q]
      exact (Submodule.mem_orthogonal _ _).1
        (Krylov.IsMinResIterate.residual_mem_orthogonal (hminres q)) _ hmem
    have h2 : inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (rO (q + 1)) = 0 := by
      rw [hr (q + 1)]
      exact IsPetrovGalerkin.inner_residual_eq_zero (hO (q + 1))
        (Krylov.map_subspace_le (op A) (b - op A x₀) q hmem)
    have hd : op A (xO (q + 1) - mrsX xO rO q) = mrsR xO rO q - rO (q + 1) := by
      rw [hres q, hr (q + 1), map_sub]
      abel
    rw [hd, inner_sub_right, h1, h2, sub_zero]
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [real_inner_comm]
    exact key j i h

end FOM


end SaadSparse.Ch06
