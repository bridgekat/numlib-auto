import Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity

/-!
# Elementary bounds on evaluation-complexity orders

Real inequalities about the orders `max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` (written with
`Optimization.finMax`) that appear in the complexity of two-phase high-order methods
([cartis2022evaluation], §14.3), for the exponents `π_j = j + 1` and `π_j = arqpPiOf u p j` of
the regularization methods.

## Main results

* `Constrained.inv_mul_pow_le_rpow_succ`, `Constrained.inv_mul_mul_pow_le_rpow_succ`,
  `Constrained.inv_mul_pow_le_add_arqpPiOf`: the terms `(ε₀ ε_j)^{-j}` against
  `ε₀^{1-π_j} ε_j^{-π_j}`;
* `Constrained.mul_sum_le_mul_sum_abs_mul`: a weighted sum of the terms is within any order;
* `Constrained.one_le_mul_sq_div_two_mul_rpow_neg`,
  `Constrained.exists_mul_sq_div_two_mul_rpow_neg_lt_one`: cost bounds above and below one
  evaluation;
* `Constrained.exists_tol_mul_finMax_lt`, `Constrained.exists_tol_mul_finMax_lt_arqpPiOf`,
  `Constrained.exists_tol_mul_finMax_lt_arqpPiOf_true`: `(ε₀ ε_1)^{-1}` is not dominated by the
  order when `1 < π_1 < 2` and the other exponents are small.
-/

namespace Constrained

open Optimization

/-- `(ε₀ ε_j)^{-j} ≤ ε₀^{1-π_j} ε_j^{-π_j}` for the exponent `π_j = j + 1`, `ε₀ > 0` and
`ε_j ∈ (0, 1]`. -/
theorem inv_mul_pow_le_rpow_succ {ε₀ εj : ℝ} (h0 : 0 < ε₀) (hj0 : 0 < εj) (hj1 : εj ≤ 1)
    (j : ℕ) :
    ((ε₀ * εj) ^ j)⁻¹ ≤ ε₀ ^ (1 - ((j : ℝ) + 1)) * εj ^ (-((j : ℝ) + 1)) := by
  have e1 : ε₀ ^ (1 - ((j : ℝ) + 1)) = (ε₀ ^ j)⁻¹ := by
    rw [show 1 - ((j : ℝ) + 1) = -(j : ℝ) by ring, Real.rpow_neg h0.le, Real.rpow_natCast]
  have e2 : εj ^ (-((j : ℝ) + 1)) = (εj ^ j)⁻¹ * εj⁻¹ := by
    rw [Real.rpow_neg hj0.le, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_succ, mul_inv]
  rw [e1, e2, mul_pow, mul_inv]
  have : 1 ≤ εj⁻¹ := (one_le_inv₀ hj0).2 hj1
  have : 0 ≤ (ε₀ ^ j)⁻¹ * (εj ^ j)⁻¹ := by positivity
  nlinarith

/-- A bad-iteration term with the radii `ρ'_j = ε₀ ε_min` is within the order with the
exponents `q + 1`: `(ε₀ ε_j (ε₀ ε_min)^{j-1})^{-1} ≤ ε₀^{-q} ε_min^{-(q+1)}` for `j ∈ [1 : q]`
and tolerances in `(0, 1]`. -/
theorem inv_mul_mul_pow_le_rpow_succ {ε₀ εj εm : ℝ} (h0 : 0 < ε₀) (h01 : ε₀ ≤ 1) (hm0 : 0 < εm)
    (hm1 : εm ≤ 1) (hmj : εm ≤ εj) {j q : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (ε₀ * εj * (ε₀ * εm) ^ (j - 1))⁻¹ ≤ ε₀ ^ (1 - ((q : ℝ) + 1)) * εm ^ (-((q : ℝ) + 1)) := by
  have hp : 0 < ε₀ * εm := mul_pos h0 hm0
  have hp1 : ε₀ * εm ≤ 1 := (mul_le_of_le_one_left hm0.le h01).trans hm1
  have h1 : (ε₀ * εm) ^ j ≤ ε₀ * εj * (ε₀ * εm) ^ (j - 1) := by
    rw [← mul_pow_sub_one (by omega : j ≠ 0) (ε₀ * εm)]
    gcongr
  have h2 : (ε₀ * εm) ^ q ≤ (ε₀ * εm) ^ j := pow_le_pow_of_le_one hp.le hp1 hjq
  calc (ε₀ * εj * (ε₀ * εm) ^ (j - 1))⁻¹ ≤ ((ε₀ * εm) ^ j)⁻¹ := inv_anti₀ (pow_pos hp _) h1
    _ ≤ ((ε₀ * εm) ^ q)⁻¹ := inv_anti₀ (pow_pos hp _) h2
    _ ≤ _ := inv_mul_pow_le_rpow_succ h0 hm0 hm1 q

/-- `(ε₀ ε_j)^{-j} ≤ ε₀^{-p} + ε₀^{1-π_j} ε_j^{-π_j}` for the exponents `π_j = j(p+1)/p`
(`arqpPiOf False p`) and `ε₀, ε_j > 0`: by the weighted AM–GM inequality, `(ε₀ ε_j)^{-j}` is the
geometric mean of `ε₀^{-p}` and `ε₀^{1-π_j} ε_j^{-π_j}` with weights `1/(p+1)`, `p/(p+1)`. -/
theorem inv_mul_pow_le_add_arqpPiOf {ε₀ εj : ℝ} (h0 : 0 < ε₀) (hj0 : 0 < εj) {p j : ℕ}
    (hp : 1 ≤ p) :
    ((ε₀ * εj) ^ j)⁻¹ ≤ (ε₀ ^ p)⁻¹ +
      ε₀ ^ (1 - arqpPiOf False p j) * εj ^ (-arqpPiOf False p j) := by
  rw [arqpPiOf_of_neg not_false]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set π : ℝ := (j : ℝ) * (p + 1) / p with hπ
  set w₁ : ℝ := 1 / (p + 1) with hw₁
  set w₂ : ℝ := p / (p + 1) with hw₂
  have hw : w₁ + w₂ = 1 := by rw [hw₁, hw₂]; field_simp; ring
  have hA : 0 ≤ (ε₀ ^ p)⁻¹ := by positivity
  have hB : 0 ≤ ε₀ ^ (1 - π) * εj ^ (-π) := by positivity
  have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := w₁) (w₂ := w₂) (by positivity)
    (by positivity) hA hB hw
  have e1 : ((ε₀ ^ p)⁻¹) ^ w₁ = ε₀ ^ (-(p : ℝ) * w₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg h0.le, ← Real.rpow_mul h0.le]
  have e2 : (ε₀ ^ (1 - π) * εj ^ (-π)) ^ w₂ = ε₀ ^ ((1 - π) * w₂) * εj ^ (-π * w₂) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul h0.le,
      ← Real.rpow_mul hj0.le]
  have e3 : ((ε₀ * εj) ^ j)⁻¹ = ε₀ ^ (-(p : ℝ) * w₁ + (1 - π) * w₂) * εj ^ (-π * w₂) := by
    have x1 : -(p : ℝ) * w₁ + (1 - π) * w₂ = -(j : ℝ) := by
      rw [hw₁, hw₂, hπ]; field_simp; ring
    have x2 : -π * w₂ = -(j : ℝ) := by rw [hw₂, hπ]; field_simp
    rw [x1, x2, Real.rpow_neg h0.le, Real.rpow_neg hj0.le, Real.rpow_natCast, Real.rpow_natCast,
      mul_pow, mul_inv]
  rw [e3, Real.rpow_add h0, mul_assoc, ← e2, ← e1]
  have h1 : w₁ ≤ 1 := by rw [hw₁, div_le_one (by positivity)]; linarith
  have h2 : w₂ ≤ 1 := by rw [hw₂, div_le_one (by positivity)]; linarith
  calc _ ≤ w₁ * (ε₀ ^ p)⁻¹ + w₂ * (ε₀ ^ (1 - π) * εj ^ (-π)) := hgm
    _ ≤ _ := add_le_add (mul_le_of_le_one_left hA h1) (mul_le_of_le_one_left hB h2)

/-- `½ κ r ∑_j β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j} ε₀^{1-π_j} ε_j^{-π_j} ≤ ½ κ r W O` with
`W = ∑_j |β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j}|`, for `κ, r ≥ 0`, positive tolerances and every
`O ≥ ε₀^{1-π_j} ε_j^{-π_j}` (the sum of a two-phase Phase-1 bound is within any such order). -/
theorem mul_sum_le_mul_sum_abs_mul {q : ℕ} {ε : ℕ → ℝ} {κ r β₁ θ O : ℝ} {π : ℕ → ℝ}
    (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hO : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ O) :
    1 / 2 * κ * r * ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) *
        θ ^ (1 - π j) * ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤
      1 / 2 * κ * r * (∑ j ∈ Finset.Icc 1 q,
        |β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j)|) * O := by
  rw [mul_assoc (1 / 2 * κ * r), Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
  have h0 : 0 ≤ ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
    have := hε 0 (by simp)
    have := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    positivity
  rw [mul_assoc _ (ε 0 ^ (1 - π j))]
  calc _ ≤ |β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j)| *
        (ε 0 ^ (1 - π j) * ε j ^ (-π j)) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hO j hj) (abs_nonneg _)

/-- `1 ≤ 2 (R²/2) (β R e)^{-π}` for `π ≥ 2`, `β e ≤ 1` and `β R e ≤ 1`: a multiplicative cost
bound `κ (R²/2) (β R e)^{-π}` with `κ ≥ 2` is at least one evaluation. -/
theorem one_le_mul_sq_div_two_mul_rpow_neg {β e R π : ℝ} (hβ : 0 < β) (he : 0 < e)
    (hβe : β * e ≤ 1)
    (hR : 0 < R) (ha : β * R * e ≤ 1) (hπ : 2 ≤ π) :
    1 ≤ 2 * (R ^ 2 / 2) * (β * R * e) ^ (-π) := by
  set a := β * R * e with hadef
  have ha0 : 0 < a := by positivity
  have h1 : a ^ (-(2 : ℝ)) ≤ a ^ (-π) := Real.rpow_le_rpow_of_exponent_ge ha0 ha (by linarith)
  have h2 : a ^ (-(2 : ℝ)) = (a ^ 2)⁻¹ := by
    rw [Real.rpow_neg ha0.le]
    norm_cast
  have haR : a ≤ R := by
    have : a = (β * e) * R := by rw [hadef]; ring
    rw [this]
    nlinarith
  have h3 : a ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ ha0.le haR 2
  have h4 : 1 ≤ R ^ 2 * (a ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  calc (1 : ℝ) ≤ R ^ 2 * (a ^ 2)⁻¹ := h4
    _ = 2 * (R ^ 2 / 2) * a ^ (-(2 : ℝ)) := by rw [h2]; ring
    _ ≤ 2 * (R ^ 2 / 2) * a ^ (-π) := by gcongr

/-- **A cost bound below one evaluation**: for `0 < π < 2`, `β ∈ (0, 1)` and every `κ` there is
`R ∈ (0, 1]` with `κ (R²/2) (β R)^{-π} < 1` (a cost bound `κ μ (β R)^{-π}` at a point where
`μ = R²/2` and `‖r‖ = R`). -/
theorem exists_mul_sq_div_two_mul_rpow_neg_lt_one {π β : ℝ} (hπ0 : 0 < π) (hπ2 : π < 2)
    (hβ0 : 0 < β) (hβ1 : β < 1) (κ : ℝ) :
    ∃ R : ℝ, 0 < R ∧ R ≤ 1 ∧ κ * (R ^ 2 / 2) * (β * R) ^ (-π) < 1 := by
  set κ' := max κ 0
  set b := β ^ π / (κ' + 1) with hb
  have hκ' : 0 ≤ κ' := le_max_right _ _
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one (by linarith)]
    have : β ^ π ≤ 1 := Real.rpow_le_one hβ0.le hβ1.le hπ0.le
    linarith
  set R := b ^ (2 - π)⁻¹ with hR
  have hs : 0 < 2 - π := by linarith
  have hR0 : 0 < R := Real.rpow_pos_of_pos hb0 _
  have hR1 : R ≤ 1 := Real.rpow_le_one hb0.le hb1 (inv_nonneg.2 hs.le)
  have hRs : R ^ (2 - π) = b := Real.rpow_inv_rpow hb0.le hs.ne'
  refine ⟨R, hR0, hR1, ?_⟩
  have e1 : R ^ 2 / 2 * (β * R) ^ (-π) = β ^ (-π) * R ^ (2 - π) / 2 := by
    rw [Real.mul_rpow hβ0.le hR0.le, Real.rpow_sub hR0, Real.rpow_neg hR0.le, Real.rpow_two]
    field_simp
  have e2 : β ^ (-π) * b = 1 / (κ' + 1) := by
    rw [hb, Real.rpow_neg hβ0.le]
    have : 0 < β ^ π := Real.rpow_pos_of_pos hβ0 _
    field_simp
  have hpos : 0 ≤ R ^ 2 / 2 * (β * R) ^ (-π) := by positivity
  calc κ * (R ^ 2 / 2) * (β * R) ^ (-π) = κ * (R ^ 2 / 2 * (β * R) ^ (-π)) := by ring
    _ ≤ κ' * (R ^ 2 / 2 * (β * R) ^ (-π)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ = κ' * (β ^ (-π) * b) / 2 := by rw [e1, hRs]; ring
    _ = κ' / (κ' + 1) / 2 := by rw [e2]; ring
    _ < 1 := by
        rw [div_div, div_lt_one (by positivity)]
        linarith

/-- **The term `(ε₀ ε_1)^{-1}` is not dominated by `max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]`**
when `1 < π_1 < 2` and
`π_i - 2 < (2 - π_1)/(π_1 - 1)` for every `i ∈ [1 : q]`: for every `C` there are tolerances
`ε ∈ (0, 1]^{q+1}` (`ε₀ = δ`, `ε_1 = δ^a`, `ε_i = 1` for `i ≥ 2`, `δ` small) with
`C max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}] < (ε₀ ε_1)^{-1}`. -/
theorem exists_tol_mul_finMax_lt {π : ℕ → ℝ} {q : ℕ} (hπ1 : 1 < π 1) (hπ2 : π 1 < 2)
    (hπ : ∀ i ∈ Finset.Icc 1 q, π i - 2 < (2 - π 1) / (π 1 - 1)) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q < (ε 0 * ε 1)⁻¹ := by
  obtain ⟨b, hb_def⟩ : ∃ b, b = (2 - π 1) / (π 1 - 1) := ⟨_, rfl⟩
  have hb : 0 < b := hb_def ▸ div_pos (by linarith) (by linarith)
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = finMax 0 (fun i => π i - 2) q := ⟨_, rfl⟩
  have hm0 : 0 ≤ mm := hmm ▸ le_finMax_left
  have hmb : mm < b := hmm ▸ finMax_lt hb (hb_def ▸ hπ)
  obtain ⟨a, ha_def⟩ : ∃ a, a = (mm + b) / 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hma : ∀ i ∈ Finset.Icc 1 q, π i - 2 < a := fun i hi =>
    lt_of_le_of_lt (hmm ▸ le_finMax (u := fun i => π i - 2) hi)
      (by rw [ha_def]; linarith)
  -- the exponents of `δ^{-1}` in the order
  set γ := finMax 1 (fun i => if i = 1 then π 1 - 1 + a * π 1 else π i - 1) q with hγ
  have hγ1 : 1 ≤ γ := le_finMax_left
  have hγa : γ < 1 + a := by
    refine finMax_lt (by linarith) fun i hi => ?_
    split_ifs with h
    · have : a * (π 1 - 1) < 2 - π 1 := by
        rw [hb_def, lt_div_iff₀ (by linarith)] at hab; linarith
      nlinarith
    · linarith [hma i hi]
  set g := 1 + a - γ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set δ := min (1 / 2) ((|C| + 1) ^ (-g⁻¹)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδC : |C| + 1 ≤ δ ^ (-g) := by
    have h1 : δ ≤ (|C| + 1) ^ (-g⁻¹) := min_le_right _ _
    have h2 := Real.rpow_le_rpow_of_nonpos hδ0 h1 (by linarith : -g ≤ 0)
    rwa [← Real.rpow_mul (by positivity), show -g⁻¹ * -g = 1 by field_simp, Real.rpow_one] at h2
  set ε : ℕ → ℝ := fun i => if i = 0 then δ else if i = 1 then δ ^ a else 1 with hε
  have hε0 : ε 0 = δ := by simp [hε]
  have hε1 : ε 1 = δ ^ a := by simp [hε]
  have hεi : ∀ i, 2 ≤ i → ε i = 1 := fun i hi => by
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    simp [hε, h0, h1]
  refine ⟨ε, fun j _ => ?_, ?_⟩
  · simp only [hε]
    split_ifs
    · exact ⟨hδ0, hδ1⟩
    · exact ⟨Real.rpow_pos_of_pos hδ0 _, Real.rpow_le_one hδ0.le hδ1 ha0.le⟩
    · exact ⟨one_pos, le_rfl⟩
  -- every term of the order is at most `δ^{-γ}`
  have hpow : ∀ e : ℝ, e ≤ γ → δ ^ (-e) ≤ δ ^ (-γ) := fun e he =>
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hO : finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q ≤ δ ^ (-γ) := by
    refine finMax_le ?_ fun i hi => ?_
    · rw [hε0, ← Real.rpow_neg_one]; exact hpow 1 hγ1
    · have hγi : (if i = 1 then π 1 - 1 + a * π 1 else π i - 1) ≤ γ :=
        le_finMax (u := fun i => if i = 1 then π 1 - 1 + a * π 1 else π i - 1) hi
      by_cases h1 : i = 1
      · subst h1
        simp only [ite_true] at hγi
        rw [hε0, hε1, ← Real.rpow_mul hδ0.le, ← Real.rpow_add hδ0]
        refine le_of_eq_of_le (by ring_nf) (hpow _ hγi)
      · simp only [h1, ite_false] at hγi
        rw [hε0, hεi i (by have := (Finset.mem_Icc.1 hi).1; omega), Real.one_rpow, mul_one]
        exact le_of_eq_of_le (by ring_nf) (hpow _ hγi)
  have hL : (ε 0 * ε 1)⁻¹ = δ ^ (-γ) * δ ^ (-g) := by
    rw [hε0, hε1, ← Real.rpow_add hδ0, ← Real.rpow_one_add' hδ0.le (by linarith),
      ← Real.rpow_neg hδ0.le]
    congr 1
    rw [hg]; ring
  rw [hL]
  have hγpos : 0 < δ ^ (-γ) := Real.rpow_pos_of_pos hδ0 _
  calc C * finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q ≤ |C| * δ ^ (-γ) := by
        have hO0 : 0 ≤ finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q :=
          (inv_pos.2 (by rw [hε0]; exact hδ0)).le.trans le_finMax_left
        calc C * finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q ≤
              |C| * finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q :=
              mul_le_mul_of_nonneg_right (le_abs_self C) hO0
          _ ≤ |C| * δ ^ (-γ) := mul_le_mul_of_nonneg_left hO (abs_nonneg C)
    _ < (|C| + 1) * δ ^ (-γ) := by nlinarith
    _ ≤ δ ^ (-g) * δ ^ (-γ) := mul_le_mul_of_nonneg_right hδC hγpos.le
    _ = δ ^ (-γ) * δ ^ (-g) := mul_comm _ _

/-- **The term `(ε₀ ε_1)^{-1}` is not dominated by the order of the exponents `j(p+1)/p`** for
`1 ≤ q < p` (`arqpPiOf False p`): for every `C` there are tolerances with
`C max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}] < (ε₀ ε_1)^{-1}` (`exists_tol_mul_finMax_lt` with
`π_1 = (p+1)/p`, `(2 - π_1)/(π_1 - 1) = p - 1 > q(p+1)/p - 2`). -/
theorem exists_tol_mul_finMax_lt_arqpPiOf {p q : ℕ} (hq : 1 ≤ q) (hqp : q < p) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * finMax (ε 0)⁻¹
        (fun j => ε 0 ^ (1 - arqpPiOf False p j) * ε j ^ (-arqpPiOf False p j)) q <
        (ε 0 * ε 1)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hqp' : (q : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : q + 1 ≤ p)
  have e1 : arqpPiOf False p 1 = 1 + 1 / p := by
    rw [arqpPiOf_of_neg not_false]; field_simp; push_cast; ring
  have hp1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  have hp1' : 0 < 1 / (p : ℝ) := by positivity
  refine exists_tol_mul_finMax_lt (by rw [e1]; linarith) (by rw [e1]; linarith)
    (fun i hi => ?_) C
  have hb : (2 - arqpPiOf False p 1) / (arqpPiOf False p 1 - 1) =
      (p : ℝ) - 1 := by rw [e1]; field_simp; ring
  rw [hb, arqpPiOf_of_neg not_false]
  have hiq : (i : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hi).2
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp0]
  nlinarith

/-- **The term `(ε₀ ε_1)^{-1}` is not dominated by the order of the exponents
`(p+1)/(p-j+1)`** for `1 ≤ q ≤ 2`, `q < p` (`arqpPiOf True p`): for every `C` there are tolerances
with `C max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}] < (ε₀ ε_1)^{-1}` (`exists_tol_mul_finMax_lt`;
`(2 - π_1)/(π_1 - 1) = p - 1`, and `π_2 - 2 = (3 - p)/(p - 1) < p - 1` for `p ≥ 3`). -/
theorem exists_tol_mul_finMax_lt_arqpPiOf_true {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q < p) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * finMax (ε 0)⁻¹
        (fun j => ε 0 ^ (1 - arqpPiOf True p j) * ε j ^ (-arqpPiOf True p j)) q <
        (ε 0 * ε 1)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have e1 : arqpPiOf True p 1 = 1 + 1 / p := by
    rw [arqpPiOf_of_pos trivial, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    field_simp; push_cast; ring
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hp1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  have hp1' : 0 < 1 / (p : ℝ) := by positivity
  refine exists_tol_mul_finMax_lt (by rw [e1]; linarith) (by rw [e1]; linarith)
    (fun i hi => ?_) C
  have hb : (2 - arqpPiOf True p 1) / (arqpPiOf True p 1 - 1) =
      (p : ℝ) - 1 := by rw [e1]; field_simp; ring
  rw [hb]
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  have hi2 : i ≤ 2 := hiq.trans hq2
  interval_cases i
  · rw [e1]; have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    rw [arqpPiOf_of_pos trivial]
    have e2 : ((p - 2 + 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [show p - 2 + 1 = p - 1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
    rw [e2, sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]
    push_cast
    nlinarith

end Constrained
