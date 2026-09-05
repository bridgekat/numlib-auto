import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The standard model of floating-point arithmetic

Rounding is described here by a *relation* rather than by a function: a `RoundingModel K` on an
ordered field `K` fixes a unit roundoff `u` and says which values `y` are admissible results of
rounding `x`, namely those with `|y - x| ≤ u |x|`, equivalently `y = x (1 + δ)` with `|δ| ≤ u`.
A theorem proved in the model therefore holds for *every* rounding rule meeting the bound, and,
when the theorem is about an algorithm, for every evaluation order that its statement spells out.
A concrete format is plugged in later by exhibiting its rounding relation as a `RoundingModel`.

The bookkeeping constants are Higham's: `gamma u n = n u / (1 - n u)`, and `IsRelPert u n x y`
says that `y = x (1 + θ)` for some `|θ| ≤ gamma u n`.  The two facts that drive every error
analysis are that a product of `n` factors `(1 + δ_i)^{±1}` is `1 + θ` with `|θ| ≤ gamma u n`
(`abs_prod_one_add_sub_one_le_gamma`), and that relative perturbations compose by adding their
orders (`IsRelPert.trans`, `IsRelPert.mul`, `IsRelPert.div`).

## References

[^higham]: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd edition,
  SIAM, 2002.  The model is his (2.4) and the constants are his Lemma 3.1 and Lemma 3.3.
-/

open Finset

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The rounding relation -/

/-- **The standard model of floating-point arithmetic** (Higham, *Accuracy and Stability of
Numerical Algorithms*, (2.4)): a unit roundoff `u` together with a relation saying which values are
admissible roundings, each within a relative error `u` of its argument.

The relation is not required to be functional, total or deterministic, so a theorem stated for a
`RoundingModel` holds for every rounding rule obeying the bound — which is exactly the strength an
error analysis wants. -/
structure RoundingModel (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The unit roundoff. -/
  u : K
  /-- The unit roundoff is nonnegative. -/
  u_nonneg : 0 ≤ u
  /-- `Rounds x y` holds when `y` is an admissible floating-point value of the exact `x`. -/
  Rounds : K → K → Prop
  /-- Every admissible rounding has relative error at most the unit roundoff. -/
  abs_sub_le : ∀ {x y : K}, Rounds x y → |y - x| ≤ u * |x|

/-- Higham's form of the model: an admissible rounding of `x` is `x (1 + δ)` for some `|δ| ≤ u`. -/
theorem RoundingModel.Rounds.exists_delta {m : RoundingModel K} {x y : K} (h : m.Rounds x y) :
    ∃ δ : K, |δ| ≤ m.u ∧ y = x * (1 + δ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : |y - 0| ≤ m.u * |0| := m.abs_sub_le h
    rw [sub_zero, abs_zero, mul_zero] at hy
    exact ⟨0, by simpa using m.u_nonneg, by simp [abs_nonpos_iff.1 hy]⟩
  · refine ⟨(y - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hx)]
      simpa [mul_comm] using m.abs_sub_le h
    · field_simp
      ring

/-! ### The constants `γ_n` -/

/-- Higham's constant `γ_n = n u / (1 - n u)` (*Accuracy and Stability of Numerical Algorithms*,
Lemma 3.1), the bound on the relative error accumulated by `n` roundings.  It is meaningful under
the hypothesis `n u < 1`, which every statement below carries. -/
def gamma (u : K) (n : ℕ) : K := n * u / (1 - n * u)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem gamma_def (u : K) (n : ℕ) : gamma u n = n * u / (1 - n * u) := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp]
theorem gamma_zero (u : K) : gamma u 0 = 0 := by simp [gamma]

theorem gamma_nonneg {u : K} (hu : 0 ≤ u) {n : ℕ} (h : (n : K) * u < 1) : 0 ≤ gamma u n :=
  div_nonneg (mul_nonneg (by positivity) hu) (by linarith)

/-- `1 + γ_n = (1 - n u)⁻¹`, the identity behind the whole calculus of the constants. -/
theorem one_add_gamma {u : K} {n : ℕ} (h : (n : K) * u < 1) :
    1 + gamma u n = (1 - (n : K) * u)⁻¹ := by
  have hne : (1 : K) - (n : K) * u ≠ 0 := by linarith
  rw [gamma_def]
  field_simp
  ring

theorem gamma_mono {u : K} (hu : 0 ≤ u) {m n : ℕ} (hmn : m ≤ n) (h : (n : K) * u < 1) :
    gamma u m ≤ gamma u n := by
  have hmnn : (0 : K) ≤ (m : K) * u := mul_nonneg (by positivity) hu
  have hcast : (m : K) * u ≤ (n : K) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmn) hu
  rw [gamma_def, gamma_def, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- A single rounding is bounded by `γ₁`. -/
theorem le_gamma_one {u : K} (hu : 0 ≤ u) (h : u < 1) : u ≤ gamma u 1 := by
  rw [gamma_def, Nat.cast_one, one_mul, le_div_iff₀ (by linarith)]
  nlinarith

/-! ### Products of rounding factors -/

/-- **Higham's Lemma 3.1** (*Accuracy and Stability of Numerical Algorithms*): a product of `n`
factors `(1 + δ_i)^{ρ_i}` with `|δ_i| ≤ u` and `ρ_i = ±1` differs from `1` by at most `γ_n`,
provided `n u < 1`.

Every factor lies between `1 - u` and `(1 - u)⁻¹`, so the product lies between `(1 - u)^n` and
`(1 - u)^{-n}`, and Bernoulli's inequality `1 - n u ≤ (1 - u)^n` turns the latter bound into
`1 + γ_n`. -/
theorem abs_prod_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u) {n : ℕ} (hnu : (n : K) * u < 1)
    {δ : Fin n → K} (hδ : ∀ i, |δ i| ≤ u) {ρ : Fin n → ℤ} (hρ : ∀ i, ρ i = 1 ∨ ρ i = -1) :
    |∏ i, (1 + δ i) ^ (ρ i) - 1| ≤ gamma u n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- `u < 1`, because `u ≤ n u < 1`
  have hu1 : u < 1 := by
    have hle : (1 : K) * u ≤ (n : K) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hu
    rw [one_mul] at hle
    linarith
  have hpos : (0 : K) < 1 - u := by linarith
  -- every factor lies in `[1 - u, (1 - u)⁻¹]`
  have hfac : ∀ i, 1 - u ≤ (1 + δ i) ^ (ρ i) ∧ (1 + δ i) ^ (ρ i) ≤ (1 - u)⁻¹ := by
    intro i
    have h1 : -u ≤ δ i := neg_le_of_abs_le (hδ i)
    have h2 : δ i ≤ u := le_of_abs_le (hδ i)
    have hd : (0 : K) < 1 + δ i := by linarith
    have hub : (1 : K) + δ i ≤ (1 - u)⁻¹ := by
      rw [← sub_nonneg]
      have heq : (1 - u)⁻¹ - (1 + δ i) = (1 - (1 + δ i) * (1 - u)) / (1 - u) := by
        field_simp
      rw [heq]
      exact div_nonneg (by nlinarith) hpos.le
    have hlb : 1 - u ≤ (1 + δ i)⁻¹ := by
      rw [← sub_nonneg]
      have heq : (1 + δ i)⁻¹ - (1 - u) = (1 - (1 - u) * (1 + δ i)) / (1 + δ i) := by
        field_simp
      rw [heq]
      exact div_nonneg (by nlinarith) hd.le
    have hub' : (1 + δ i)⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hpos (by linarith)
    rcases hρ i with hr | hr <;> rw [hr]
    · rw [zpow_one]; exact ⟨by linarith, hub⟩
    · rw [zpow_neg_one]; exact ⟨hlb, hub'⟩
  have hnn : ∀ i, (0 : K) ≤ (1 + δ i) ^ (ρ i) := fun i => hpos.le.trans (hfac i).1
  -- hence the product lies in `[(1 - u)^n, ((1 - u)^n)⁻¹]`
  have hppos : (0 : K) < (1 - u) ^ n := pow_pos hpos n
  have hple : (1 - u) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hlow : (1 - u) ^ n ≤ ∏ i, (1 + δ i) ^ (ρ i) := by
    calc (1 - u) ^ n = ∏ _i : Fin n, (1 - u) := by simp
      _ ≤ ∏ i, (1 + δ i) ^ (ρ i) :=
          Finset.prod_le_prod (fun _ _ => hpos.le) fun i _ => (hfac i).1
  have hhigh : (∏ i, (1 + δ i) ^ (ρ i)) ≤ ((1 - u) ^ n)⁻¹ := by
    calc (∏ i, (1 + δ i) ^ (ρ i)) ≤ ∏ _i : Fin n, (1 - u)⁻¹ :=
          Finset.prod_le_prod (fun i _ => hnn i) fun i _ => (hfac i).2
      _ = ((1 - u) ^ n)⁻¹ := by simp
  -- Bernoulli's inequality turns `((1 - u)^n)⁻¹ - 1` into `γ_n`
  have hbern : 1 - (n : K) * u ≤ (1 - u) ^ n := by
    have h := one_add_mul_le_pow (a := -u) (by linarith) n
    simpa [sub_eq_add_neg, mul_neg] using h
  have hgamma : ((1 - u) ^ n)⁻¹ - 1 ≤ gamma u n := by
    have h1 : ((1 - u) ^ n)⁻¹ ≤ (1 - (n : K) * u)⁻¹ := by
      rw [← sub_nonneg]
      have heq : (1 - (n : K) * u)⁻¹ - ((1 - u) ^ n)⁻¹
          = ((1 - u) ^ n - (1 - (n : K) * u)) / ((1 - (n : K) * u) * (1 - u) ^ n) := by
        field_simp
      rw [heq]
      exact div_nonneg (by linarith) (mul_pos (by linarith) hppos).le
    have h2 := one_add_gamma (u := u) (n := n) hnu
    linarith
  have hlow2 : 1 - (1 - u) ^ n ≤ ((1 - u) ^ n)⁻¹ - 1 := by
    rw [← sub_nonneg]
    have heq : ((1 - u) ^ n)⁻¹ - 1 - (1 - (1 - u) ^ n)
        = (1 - (1 - u) ^ n) ^ 2 / (1 - u) ^ n := by
      field_simp
    rw [heq]
    exact div_nonneg (sq_nonneg _) hppos.le
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ### Relative perturbations -/

/-- `IsRelPert u n x y` says that `y = x (1 + θ)` for some `|θ| ≤ γ_n`: the value `y` is `x` to
within a relative perturbation of order `n` in a model of unit roundoff `u`.  This is Higham's
`θ_n` notation (*Accuracy and Stability of Numerical Algorithms*, Lemma 3.1), turned into a
relation so that it composes. -/
def IsRelPert (u : K) (n : ℕ) (x y : K) : Prop := ∃ θ : K, |θ| ≤ gamma u n ∧ y = x * (1 + θ)

theorem IsRelPert.refl (u : K) (x : K) : IsRelPert u 0 x x := ⟨0, by simp, by simp⟩

theorem IsRelPert.mono {u : K} (hu : 0 ≤ u) {m n : ℕ} (hmn : m ≤ n) (h : (n : K) * u < 1)
    {x y : K} (hxy : IsRelPert u m x y) : IsRelPert u n x y := by
  obtain ⟨θ, hθ, rfl⟩ := hxy
  exact ⟨θ, hθ.trans (gamma_mono hu hmn h), rfl⟩

/-- A single rounding is a relative perturbation of order one. -/
theorem RoundingModel.Rounds.isRelPert {m : RoundingModel K} (hu : m.u < 1) {x y : K}
    (h : m.Rounds x y) : IsRelPert m.u 1 x y := by
  obtain ⟨δ, hδ, rfl⟩ := h.exists_delta
  exact ⟨δ, hδ.trans (le_gamma_one m.u_nonneg hu), rfl⟩

/-- The scalar inequality behind `IsRelPert.trans`, `γ_j + γ_k + γ_j γ_k ≤ γ_{j+k}`, written out
with `x = j u` and `y = k u`. -/
private theorem add_add_mul_div_le {x y : K} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y < 1) :
    x / (1 - x) + y / (1 - y) + x / (1 - x) * (y / (1 - y)) ≤ (x + y) / (1 - (x + y)) := by
  have h1 : (0 : K) < 1 - x := by linarith
  have h2 : (0 : K) < 1 - y := by linarith
  have h3 : (0 : K) < 1 - (x + y) := by linarith
  rw [← sub_nonneg]
  have heq : (x + y) / (1 - (x + y))
      - (x / (1 - x) + y / (1 - y) + x / (1 - x) * (y / (1 - y)))
      = x * y / ((1 - x) * (1 - y) * (1 - (x + y))) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg (mul_nonneg hx hy) (by positivity)

/-- **Higham's Lemma 3.3** (*Accuracy and Stability of Numerical Algorithms*):
`γ_j + γ_k + γ_j γ_k ≤ γ_{j+k}`, which is `(1 + γ_j)(1 + γ_k) ≤ 1 + γ_{j+k}`. -/
theorem gamma_add_gamma_add_mul_le {u : K} (hu : 0 ≤ u) {j k : ℕ}
    (h : ((j + k : ℕ) : K) * u < 1) :
    gamma u j + gamma u k + gamma u j * gamma u k ≤ gamma u (j + k) := by
  have hcast : ((j + k : ℕ) : K) * u = (j : K) * u + (k : K) * u := by push_cast; ring
  rw [hcast] at h
  have hj : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hk : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hmain := add_add_mul_div_le (x := (j : K) * u) (y := (k : K) * u) hj hk h
  rwa [gamma_def, gamma_def, gamma_def, hcast]

/-- The scalar inequality behind `IsRelPert.div`, `γ_k + γ_j + γ_{k+2j} γ_j ≤ γ_{k+2j}`, written
out with `x = k u` and `y = j u`. -/
private theorem add_add_mul_div_le_div {x y : K} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + 2 * y < 1) :
    x / (1 - x) + y / (1 - y)
        + (x + 2 * y) / (1 - (x + 2 * y)) * (y / (1 - y))
      ≤ (x + 2 * y) / (1 - (x + 2 * y)) := by
  have h1 : (0 : K) < 1 - x := by linarith
  have h2 : (0 : K) < 1 - y := by linarith
  have h3 : (0 : K) < 1 - (x + 2 * y) := by linarith
  rw [← sub_nonneg]
  have heq : (x + 2 * y) / (1 - (x + 2 * y))
      - (x / (1 - x) + y / (1 - y) + (x + 2 * y) / (1 - (x + 2 * y)) * (y / (1 - y)))
      = y * (1 + x - 2 * y) / ((1 - x) * (1 - y) * (1 - (x + 2 * y))) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg (mul_nonneg hy (by linarith)) (by positivity)

/-- The form of Higham's Lemma 3.3 that division needs:
`γ_k + γ_j + γ_{k+2j} γ_j ≤ γ_{k+2j}`. -/
theorem gamma_add_gamma_add_mul_le_of_add_two_mul {u : K} (hu : 0 ≤ u) {k j : ℕ}
    (h : ((k + 2 * j : ℕ) : K) * u < 1) :
    gamma u k + gamma u j + gamma u (k + 2 * j) * gamma u j ≤ gamma u (k + 2 * j) := by
  have hcast : ((k + 2 * j : ℕ) : K) * u = (k : K) * u + 2 * ((j : K) * u) := by push_cast; ring
  rw [hcast] at h
  have hk : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hj : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hmain := add_add_mul_div_le_div (x := (k : K) * u) (y := (j : K) * u) hk hj h
  rwa [gamma_def, gamma_def, gamma_def, hcast]

/-- **Relative perturbations compose**: `(1 + θ_k)(1 + θ_j) = 1 + θ_{k+j}` (Higham, *Accuracy and
Stability of Numerical Algorithms*, Lemma 3.3). -/
theorem IsRelPert.trans {u : K} (hu : 0 ≤ u) {k j : ℕ} (h : ((k + j : ℕ) : K) * u < 1)
    {x y z : K} (h₁ : IsRelPert u k x y) (h₂ : IsRelPert u j y z) : IsRelPert u (k + j) x z := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  have hcast : ((k + j : ℕ) : K) * u = (k : K) * u + (j : K) * u := by push_cast; ring
  have hkn : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hjn : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hk : (k : K) * u < 1 := by rw [hcast] at h; linarith
  have hj : (j : K) * u < 1 := by rw [hcast] at h; linarith
  have hgk : 0 ≤ gamma u k := gamma_nonneg hu hk
  refine ⟨θ₁ + θ₂ + θ₁ * θ₂, ?_, by ring⟩
  calc |θ₁ + θ₂ + θ₁ * θ₂| ≤ |θ₁ + θ₂| + |θ₁ * θ₂| := abs_add_le _ _
    _ ≤ |θ₁| + |θ₂| + |θ₁| * |θ₂| := by
        rw [abs_mul]
        exact add_le_add (abs_add_le θ₁ θ₂) le_rfl
    _ ≤ gamma u k + gamma u j + gamma u k * gamma u j :=
        add_le_add (add_le_add hθ₁ hθ₂) (mul_le_mul hθ₁ hθ₂ (abs_nonneg _) hgk)
    _ ≤ gamma u (k + j) := gamma_add_gamma_add_mul_le hu h

/-- **Products of relative perturbations**: a perturbation of order `k` times one of order `j` is
one of order `k + j` (Higham, *Accuracy and Stability of Numerical Algorithms*, Lemma 3.3). -/
theorem IsRelPert.mul {u : K} (hu : 0 ≤ u) {k j : ℕ} (h : ((k + j : ℕ) : K) * u < 1)
    {x y z w : K} (h₁ : IsRelPert u k x y) (h₂ : IsRelPert u j z w) :
    IsRelPert u (k + j) (x * z) (y * w) := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  have hmid : IsRelPert u k (x * z) (x * (1 + θ₁) * z) := ⟨θ₁, hθ₁, by ring⟩
  have hlast : IsRelPert u j (x * (1 + θ₁) * z) (x * (1 + θ₁) * (z * (1 + θ₂))) :=
    ⟨θ₂, hθ₂, by ring⟩
  exact hmid.trans hu h hlast

/-- **Quotients of relative perturbations**: dividing a perturbation of order `k` by one of order
`j` gives one of order `k + 2 j` (Higham, *Accuracy and Stability of Numerical Algorithms*,
Lemma 3.3). -/
theorem IsRelPert.div {u : K} (hu : 0 ≤ u) {k j : ℕ} (h : ((k + 2 * j : ℕ) : K) * u < 1)
    {x y z w : K} (h₁ : IsRelPert u k x y) (h₂ : IsRelPert u j z w) :
    IsRelPert u (k + 2 * j) (x / z) (y / w) := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  have hcast : ((k + 2 * j : ℕ) : K) * u = (k : K) * u + 2 * ((j : K) * u) := by push_cast; ring
  have hkn : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hjn : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hj2 : 2 * ((j : K) * u) < 1 := by rw [hcast] at h; linarith
  have hj : (j : K) * u < 1 := by linarith
  have hgj : gamma u j < 1 := by
    rw [gamma_def, div_lt_one (by linarith)]
    linarith
  have hbound := abs_lt.1 (hθ₂.trans_lt hgj)
  have hden : (0 : K) < 1 + θ₂ := by linarith [hbound.1]
  have hgnn : 0 ≤ gamma u (k + 2 * j) := gamma_nonneg hu h
  have hstep := gamma_add_gamma_add_mul_le_of_add_two_mul hu h
  refine ⟨(1 + θ₁) / (1 + θ₂) - 1, ?_, ?_⟩
  · have hkey : (1 + θ₁) / (1 + θ₂) - 1 = (θ₁ - θ₂) / (1 + θ₂) := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have hnum : |θ₁ - θ₂| ≤ gamma u k + gamma u j := by
      calc |θ₁ - θ₂| = |θ₁ + -θ₂| := by rw [sub_eq_add_neg]
        _ ≤ |θ₁| + |-θ₂| := abs_add_le _ _
        _ = |θ₁| + |θ₂| := by rw [abs_neg]
        _ ≤ gamma u k + gamma u j := add_le_add hθ₁ hθ₂
    have hlow : 1 - gamma u j ≤ 1 + θ₂ := by
      linarith [neg_le_of_abs_le hθ₂]
    have hmul : gamma u (k + 2 * j) * (1 - gamma u j)
        ≤ gamma u (k + 2 * j) * (1 + θ₂) := mul_le_mul_of_nonneg_left hlow hgnn
    have hexpand : gamma u (k + 2 * j) * (1 - gamma u j)
        = gamma u (k + 2 * j) - gamma u (k + 2 * j) * gamma u j := by ring
    linarith
  · rw [show (1 : K) + ((1 + θ₁) / (1 + θ₂) - 1) = (1 + θ₁) / (1 + θ₂) by ring,
      div_mul_div_comm]

end FloatingPoint
