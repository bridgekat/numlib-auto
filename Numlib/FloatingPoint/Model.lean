import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The standard model of floating-point arithmetic

Rounding is described here by a *relation* rather than by a function: a `RoundingModel K` on an
ordered field `K` fixes a unit roundoff `u` and says which values `y` are admissible results of
rounding `x`, namely those with `|y - x| ≤ u |x|`, equivalently `y = x (1 + δ)` with `|δ| ≤ u`. A
theorem proved in the model therefore holds for *every* rounding rule meeting the bound, and, when
the theorem is about an algorithm, for every evaluation order that its statement spells out. A
concrete format is plugged in later by exhibiting its rounding relation as a `RoundingModel`.

Three properties a model may have are named here for the program semantics of
`Numlib/FloatingPoint/Program`: the exact model `RoundingModel.exact K` (`u = 0`, `Rounds x y ↔ y =
x`), whose rounding hook is `pure`, so that an exact specification can be read off a theorem proved
for every model; `RoundingModel.IsIdempotent` (rounding fixes its own outputs), which is what makes
the first addition `0 + fl(x₁ y₁)` of a textbook inner-product loop exact and so gives the book's
`γ_n` rather than `γ_{n+1}`; and `RoundingModel.IsTotal` (every value has a rounding), under which
the run set of a program is nonempty, so that theorems about every run are not vacuous.

The bookkeeping constants are those of [higham2002accuracy]: `gamma u n = n u / (1 - n u)`, and
`IsRelPert u n x y` says that `y = x (1 + θ)` for some `|θ| ≤ gamma u n`.  The two facts that drive
every error analysis are that a product of `n` factors `(1 + δ_i)^{±1}` is `1 + θ` with `|θ| ≤ gamma
u n` (`abs_prod_one_add_sub_one_le_gamma`), and that relative perturbations compose by adding their
orders (`IsRelPert.trans`, `IsRelPert.mul`, `IsRelPert.div`). The sharp form of the first fact,
`|∏ (1 + δ_i) - 1| ≤ (1 + u)^n - 1` (`abs_prod_one_add_sub_one_le_one_add_pow_sub_one`), needs no
hypothesis on `n u` and gives Wilkinson's classical constant `1.01 n u` for `n u ≤ 0.01`
(`abs_prod_one_add_sub_one_le_of_mul_le`, [golub2013matrix] Lemma 2.7.1), which `γ_n` does not.

The calculus is completed by the steps an algorithm takes one operation at a time: one more
rounding as a multiplication or a division (`IsRelPert.mul_one_add`, `IsRelPert.div_one_add`,
`IsRelPert.rounds`), a sum of nonnegative terms (`IsRelPert.add_of_nonneg`), a square root
(`IsRelPert.sqrt`, over `ℝ`), a common factor
(`IsRelPert.const_mul`), and the passage between a perturbation and an error bound
(`isRelPert_of_abs_sub_le`, `IsRelPert.abs_sub_le`) — the forms the Householder, Givens and
Cholesky analyses of `Numlib/FloatingPoint` need.
-/

open Finset

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The rounding relation -/

/-- **The standard model of floating-point arithmetic** ([higham2002accuracy], (2.4)): a unit
roundoff `u` together with a relation saying which values are admissible roundings, each within a
relative error `u` of its argument.

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

/-- [higham2002accuracy] form of the model: an admissible rounding of `x` is `x (1 + δ)` for some
`|δ| ≤ u`. -/
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

/-! ### The exact model, idempotence and totality -/

namespace RoundingModel

/-- **The exact model**: unit roundoff `0`, and the only admissible rounding of `x` is `x` itself.
Every theorem proved for all rounding models specializes to exact arithmetic here; in the program
semantics of `Numlib/FloatingPoint/Program` its rounding hook is `pure`. -/
def exact (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : RoundingModel K where
  u := 0
  u_nonneg := le_rfl
  Rounds x y := y = x
  abs_sub_le := by rintro x y rfl; simp

/-- The unit roundoff of the exact model is `0`. -/
@[simp] theorem exact_u : (exact K).u = 0 := rfl

/-- The rounding relation of the exact model is equality. -/
@[simp] theorem exact_rounds_iff {x y : K} : (exact K).Rounds x y ↔ y = x := Iff.rfl

/-- A rounding model is **idempotent** when rounding fixes its own outputs: an admissible rounding
`y` of any `x` rounds only to itself. Every concrete floating-point format has this property
(floating-point numbers round to themselves), but it does not follow from the relative-error bound
of the model. It is what makes the first addition `fl(0 + fl(x₁ y₁))` of an inner-product loop
started at `0` exact, the unstated assumption of the textbook analyses that start from `s = 0`
([golub2013matrix] (2.7.9)). -/
def IsIdempotent (m : RoundingModel K) : Prop :=
  ∀ ⦃x y z : K⦄, m.Rounds x y → m.Rounds y z → z = y

/-- The exact model is idempotent. -/
theorem isIdempotent_exact : (exact K).IsIdempotent := by
  rintro x y z rfl rfl
  rfl

/-- A rounding model is **total** when every value has an admissible rounding. A statement about
every run of a program in a model is vacuous when the run set is empty, which happens exactly when
some value the program rounds has no admissible rounding; over a total model every run set is
nonempty (`Numlib/FloatingPoint/Program`). -/
def IsTotal (m : RoundingModel K) : Prop := ∀ x : K, ∃ y, m.Rounds x y

/-- The exact model is total. -/
theorem isTotal_exact : (exact K).IsTotal := fun x => ⟨x, rfl⟩

end RoundingModel

/-! ### The constants `γ_n` -/

/-- [higham2002accuracy] constant `γ_n = n u / (1 - n u)` (*Accuracy and Stability of Numerical
Algorithms*, Lemma 3.1), the bound on the relative error accumulated by `n` roundings.  It is
meaningful under the hypothesis `n u < 1`, which every statement below carries. -/
def gamma (u : K) (n : ℕ) : K := n * u / (1 - n * u)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The defining formula of `FloatingPoint.gamma`, as a rewrite rule. -/
theorem gamma_def (u : K) (n : ℕ) : gamma u n = n * u / (1 - n * u) := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- No roundings, no error: `γ₀ = 0`. -/
@[simp]
theorem gamma_zero (u : K) : gamma u 0 = 0 := by simp [gamma]

/-- Below the breakdown point `n u = 1` the constant `γ_n` is nonnegative. -/
theorem gamma_nonneg {u : K} (hu : 0 ≤ u) {n : ℕ} (h : (n : K) * u < 1) : 0 ≤ gamma u n :=
  div_nonneg (mul_nonneg (by positivity) hu) (by linarith)

/-- `γ_k ≤ 2 k u` when `2 k u ≤ 1`. -/
theorem gamma_le_two_mul {u : K} (hu : 0 ≤ u) {k : ℕ} (h : 2 * ((k : K) * u) ≤ 1) :
    gamma u k ≤ 2 * (k * u) := by
  have hk0 : 0 ≤ (k : K) * u := by positivity
  rw [gamma_def, div_le_iff₀ (by linarith)]
  nlinarith

/-- `1 + γ_n = (1 - n u)⁻¹`, the identity behind the whole calculus of the constants. -/
theorem one_add_gamma {u : K} {n : ℕ} (h : (n : K) * u < 1) :
    1 + gamma u n = (1 - (n : K) * u)⁻¹ := by
  have hne : (1 : K) - (n : K) * u ≠ 0 := by linarith
  rw [gamma_def]
  field_simp
  ring

/-- More roundings cannot help: `γ_n` increases with `n` below the breakdown point. -/
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

/-- **[higham2002accuracy] Lemma 3.1** (*Accuracy and Stability of Numerical Algorithms*): a product
of `n` factors `(1 + δ_i)^{ρ_i}` with `|δ_i| ≤ u` and `ρ_i = ±1` differs from `1` by at most `γ_n`,
provided `n u < 1`.

Every factor lies between `1 - u` and `(1 - u)⁻¹`, so the product lies between `(1 - u)^n` and `(1 -
u)^{-n}`, and Bernoulli's inequality `1 - n u ≤ (1 - u)^n` turns the latter bound into `1 + γ_n`. -/
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
          Finset.prod_le_prod₀ (fun _ _ => hpos.le) fun i _ => (hfac i).1
  have hhigh : (∏ i, (1 + δ i) ^ (ρ i)) ≤ ((1 - u) ^ n)⁻¹ := by
    calc (∏ i, (1 + δ i) ^ (ρ i)) ≤ ∏ _i : Fin n, (1 - u)⁻¹ :=
          Finset.prod_le_prod₀ (fun i _ => hnn i) fun i _ => (hfac i).2
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

/-- One more rounding factor in the sharp form: if `|α| ≤ (1 + u)^k - 1` and `|δ| ≤ u`, then
`|(1 + α)(1 + δ) - 1| ≤ (1 + u)^(k+1) - 1`. -/
theorem abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one {u : K} {k : ℕ} {α δ : K}
    (hα : |α| ≤ (1 + u) ^ k - 1) (hδ : |δ| ≤ u) :
    |(1 + α) * (1 + δ) - 1| ≤ (1 + u) ^ (k + 1) - 1 := by
  have h1 : |1 + δ| ≤ 1 + u := (abs_add_le 1 δ).trans (by rw [abs_one]; linarith)
  calc |(1 + α) * (1 + δ) - 1| = |α * (1 + δ) + δ| := by ring_nf
    _ ≤ |α| * |1 + δ| + |δ| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ ((1 + u) ^ k - 1) * (1 + u) + u :=
        add_le_add (mul_le_mul hα h1 (abs_nonneg _) ((abs_nonneg _).trans hα)) hδ
    _ = (1 + u) ^ (k + 1) - 1 := by ring

/-- **The sharp product bound** ([golub2013matrix] proof of Lemma 2.7.1): a product of `n`
factors `1 + δ_i` with `|δ_i| ≤ u` differs from `1` by at most `(1 + u)^n - 1`. No hypothesis on
`n u` is needed; compare `abs_prod_one_add_sub_one_le_gamma`, whose `γ_n` is larger. -/
theorem abs_prod_one_add_sub_one_le_one_add_pow_sub_one {u : K} {n : ℕ} {δ : Fin n → K}
    (hδ : ∀ i, |δ i| ≤ u) : |∏ i, (1 + δ i) - 1| ≤ (1 + u) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    have hα := ih (δ := fun i => δ (Fin.castSucc i)) fun i => hδ _
    have h := abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one hα (hδ (Fin.last n))
    rwa [add_sub_cancel] at h

/-- `(1 + u)^n - 1 ≤ n u + (n u)^2` when `n u ≤ 1`. The step `n → n + 1` reduces to
`n² u³ ≤ n u² + u²`, which holds when `n u ≤ 1`. -/
theorem one_add_pow_sub_one_le_mul_add_sq {u : K} (hu : 0 ≤ u) {n : ℕ} (h : (n : K) * u ≤ 1) :
    (1 + u) ^ n - 1 ≤ n * u + (n * u) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast at h ⊢
    have hn0 : (0 : K) ≤ n := n.cast_nonneg
    have hnu0 : 0 ≤ (n : K) * u := mul_nonneg hn0 hu
    have hnu : (n : K) * u ≤ 1 := by nlinarith
    have ih := ih hnu
    -- `(1 + u)^(n+1) - 1 = (1 + u) ((1 + u)^n - 1) + u`
    have hrec : (1 + u) ^ (n + 1) - 1 = (1 + u) * ((1 + u) ^ n - 1) + u := by ring
    rw [hrec]
    have hstep : (1 + u) * ((1 + u) ^ n - 1) + u ≤ (1 + u) * (n * u + (n * u) ^ 2) + u := by
      gcongr
    refine hstep.trans ?_
    -- the remaining gap is `u² (n + 1 - n² u) ≥ u²`
    have hgap : (n : K) * ((n : K) * u) ≤ n := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hu hu) (sub_nonneg.2 hgap)]

/-- **Wilkinson's constant** ([golub2013matrix] Lemma 2.7.1): if `1 + α = ∏_{k<n} (1 + α_k)` with
`|α_k| ≤ u` and `n u ≤ 0.01`, then `|α| ≤ 1.01 n u`. This does not follow from
`abs_prod_one_add_sub_one_le_gamma`: at `n u = 0.01`, `γ_n = n u / 0.99 > 1.01 n u`. -/
theorem abs_prod_one_add_sub_one_le_of_mul_le {u : K} (hu : 0 ≤ u) {n : ℕ} {δ : Fin n → K}
    (hδ : ∀ i, |δ i| ≤ u) (h : (n : K) * u ≤ 1 / 100) :
    |∏ i, (1 + δ i) - 1| ≤ 101 / 100 * (n * u) := by
  have hnu0 : 0 ≤ (n : K) * u := mul_nonneg n.cast_nonneg hu
  refine (abs_prod_one_add_sub_one_le_one_add_pow_sub_one hδ).trans ?_
  refine (one_add_pow_sub_one_le_mul_add_sq hu (by linarith)).trans ?_
  nlinarith

/-! ### Relative perturbations -/

/-- `IsRelPert u n x y` says that `y = x (1 + θ)` for some `|θ| ≤ γ_n`: the value `y` is `x` to
within a relative perturbation of order `n` in a model of unit roundoff `u`.  This is
[higham2002accuracy] `θ_n` notation (*Accuracy and Stability of Numerical Algorithms*, Lemma 3.1),
turned into a relation so that it composes. -/
def IsRelPert (u : K) (n : ℕ) (x y : K) : Prop := ∃ θ : K, |θ| ≤ gamma u n ∧ y = x * (1 + θ)

/-- No perturbation at all is a relative perturbation of order `0`. -/
theorem IsRelPert.refl (u : K) (x : K) : IsRelPert u 0 x x := ⟨0, by simp, by simp⟩

/-- A relative perturbation of order `m` is one of every larger order `n`, since `γ_n` grows with
`n`. -/
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

/-- **[higham2002accuracy] Lemma 3.3** (*Accuracy and Stability of Numerical Algorithms*): `γ_j +
γ_k + γ_j γ_k ≤ γ_{j+k}`, which is `(1 + γ_j)(1 + γ_k) ≤ 1 + γ_{j+k}`. -/
theorem gamma_add_gamma_add_mul_le {u : K} (hu : 0 ≤ u) {j k : ℕ}
    (h : ((j + k : ℕ) : K) * u < 1) :
    gamma u j + gamma u k + gamma u j * gamma u k ≤ gamma u (j + k) := by
  have hcast : ((j + k : ℕ) : K) * u = (j : K) * u + (k : K) * u := by push_cast; ring
  rw [hcast] at h
  have hj : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hk : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hmain := add_add_mul_div_le (x := (j : K) * u) (y := (k : K) * u) hj hk h
  rwa [gamma_def, gamma_def, gamma_def, hcast]

/-- The scalar inequality behind `IsRelPert.div`, `γ_k + γ_j + γ_{k+2j} γ_j ≤ γ_{k+2j}`, written out
with `x = k u` and `y = j u`. -/
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

/-- The form of [higham2002accuracy] Lemma 3.3 that division needs: `γ_k + γ_j + γ_{k+2j} γ_j ≤
γ_{k+2j}`. -/
theorem gamma_add_gamma_add_mul_le_of_add_two_mul {u : K} (hu : 0 ≤ u) {k j : ℕ}
    (h : ((k + 2 * j : ℕ) : K) * u < 1) :
    gamma u k + gamma u j + gamma u (k + 2 * j) * gamma u j ≤ gamma u (k + 2 * j) := by
  have hcast : ((k + 2 * j : ℕ) : K) * u = (k : K) * u + 2 * ((j : K) * u) := by push_cast; ring
  rw [hcast] at h
  have hk : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hj : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hmain := add_add_mul_div_le_div (x := (k : K) * u) (y := (j : K) * u) hk hj h
  rwa [gamma_def, gamma_def, gamma_def, hcast]

/-- **Relative perturbations compose**: `(1 + θ_k)(1 + θ_j) = 1 + θ_{k+j}` ([higham2002accuracy],
Lemma 3.3). -/
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
one of order `k + j` ([higham2002accuracy], Lemma 3.3). -/
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
`j` gives one of order `k + 2 j` ([higham2002accuracy], Lemma 3.3). -/
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

/-! ### One more rounding, multiplied or divided -/

/-- One more rounding raises the order of a relative perturbation by one: `γ_k (1 + u) + u ≤
γ_{k+1}`.  This is [higham2002accuracy] Lemma 3.3 together with `u ≤ γ₁`. -/
theorem gamma_mul_one_add_add_le {u : K} (hu : 0 ≤ u) (hu1 : u < 1) {k : ℕ}
    (h : ((k + 1 : ℕ) : K) * u < 1) : gamma u k * (1 + u) + u ≤ gamma u (k + 1) := by
  have hcast : ((k + 1 : ℕ) : K) * u = (k : K) * u + u := by push_cast; ring
  have hk : (k : K) * u < 1 := by rw [hcast] at h; linarith
  have hgk : 0 ≤ gamma u k := gamma_nonneg hu hk
  have hg1 : u ≤ gamma u 1 := le_gamma_one hu hu1
  have hmain := gamma_add_gamma_add_mul_le (u := u) hu (j := k) (k := 1) h
  have hmul : gamma u k * u ≤ gamma u k * gamma u 1 := mul_le_mul_of_nonneg_left hg1 hgk
  rw [mul_add, mul_one]
  linarith

/-- Multiplying a relative perturbation of order `k` by one rounding factor gives one of order
`k + 1`: `(1 + θ_k)(1 + δ) = 1 + θ_{k+1}` ([higham2002accuracy] Lemma 3.3). -/
theorem abs_one_add_mul_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u) (hu1 : u < 1) {k : ℕ}
    (h : ((k + 1 : ℕ) : K) * u < 1) {θ δ : K} (hθ : |θ| ≤ gamma u k) (hδ : |δ| ≤ u) :
    |(1 + θ) * (1 + δ) - 1| ≤ gamma u (k + 1) := by
  have hk : (k : K) * u < 1 := by
    have : (k : K) * u ≤ ((k + 1 : ℕ) : K) * u := by push_cast; nlinarith
    linarith
  have hgk : 0 ≤ gamma u k := gamma_nonneg hu hk
  calc |(1 + θ) * (1 + δ) - 1| = |θ + δ + θ * δ| := by ring_nf
    _ ≤ |θ| + |δ| + |θ| * |δ| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ gamma u k + u + gamma u k * u :=
        add_le_add (add_le_add hθ hδ) (mul_le_mul hθ hδ (abs_nonneg _) hgk)
    _ = gamma u k * (1 + u) + u := by ring
    _ ≤ gamma u (k + 1) := gamma_mul_one_add_add_le hu hu1 h

/-- Dividing a relative perturbation of order `k` by one rounding factor gives one of order
`k + 1`: `(1 + θ_k) / (1 + δ) = 1 + θ_{k+1}`, because `(γ_k + u) / (1 - u) ≤ γ_{k+1}`. This is the
case `ρ = -1` of [higham2002accuracy] Lemma 3.1, and the reason a division costs one rounding and
not the two of `FloatingPoint.IsRelPert.div`. -/
theorem abs_one_add_div_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u) {k : ℕ}
    (h : ((k + 1 : ℕ) : K) * u < 1) {θ δ : K} (hθ : |θ| ≤ gamma u k) (hδ : |δ| ≤ u) :
    |(1 + θ) / (1 + δ) - 1| ≤ gamma u (k + 1) := by
  have hcast : ((k + 1 : ℕ) : K) * u = (k : K) * u + u := by push_cast; ring
  have hku : (k : K) * u < 1 := by
    rw [hcast] at h
    linarith
  have hu1 : u < 1 := by
    have : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
    rw [hcast] at h
    linarith
  have hd : 0 < 1 + δ := by linarith [neg_le_of_abs_le hδ]
  have hkey : (1 + θ) / (1 + δ) - 1 = (θ - δ) / (1 + δ) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have hnum : |θ - δ| ≤ gamma u k + u :=
    (abs_sub _ _).trans (add_le_add hθ hδ)
  have hlow : 1 - u ≤ 1 + δ := by linarith [neg_le_of_abs_le hδ]
  have hg1 : 0 ≤ gamma u (k + 1) := gamma_nonneg hu h
  -- the scalar inequality `(γ_k + u) ≤ γ_{k+1} (1 - u)`
  have hscalar : gamma u k + u ≤ gamma u (k + 1) * (1 - u) := by
    rw [gamma_def, gamma_def, hcast]
    have h1 : (0 : K) < 1 - (k : K) * u := by linarith
    have h2 : (0 : K) < 1 - ((k : K) * u + u) := by linarith
    rw [div_add' _ _ _ h1.ne', div_mul_eq_mul_div, div_le_div_iff₀ h1 h2]
    have hk0 : (0 : K) ≤ k := by positivity
    nlinarith [mul_nonneg hk0 hu, mul_nonneg (mul_nonneg hk0 hu) hu]
  calc |θ - δ| ≤ gamma u k + u := hnum
    _ ≤ gamma u (k + 1) * (1 - u) := hscalar
    _ ≤ gamma u (k + 1) * (1 + δ) := mul_le_mul_of_nonneg_left hlow hg1

/-! ### Relative perturbations, one operation at a time -/

section Steps

/-- Rounding `0` gives `0`. -/
theorem RoundingModel.Rounds.eq_zero_of_zero {m : RoundingModel K} {y : K} (h : m.Rounds 0 y) :
    y = 0 := by
  have := m.abs_sub_le h
  rw [sub_zero, abs_zero, mul_zero] at this
  exact abs_nonpos_iff.1 this

/-- A bound `|y - x| ≤ γ_n |x|` is a relative perturbation of order `n`. -/
theorem isRelPert_of_abs_sub_le {u : K} {n : ℕ} (hγ : 0 ≤ gamma u n) {x y : K}
    (h : |y - x| ≤ gamma u n * |x|) : IsRelPert u n x y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [sub_zero, abs_zero, mul_zero] at h
    exact ⟨0, by simpa using hγ, by simp [abs_nonpos_iff.1 h]⟩
  · refine ⟨(y - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hx)]
      exact h
    · field_simp
      ring

/-- The error of a relative perturbation, `|y - x| ≤ γ_n |x|`. -/
theorem IsRelPert.abs_sub_le {u : K} {n : ℕ} {x y : K} (h : IsRelPert u n x y) :
    |y - x| ≤ gamma u n * |x| := by
  obtain ⟨θ, hθ, rfl⟩ := h
  rw [show x * (1 + θ) - x = θ * x by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)

omit [IsStrictOrderedRing K] in
/-- A relative perturbation is unchanged by a common factor. -/
theorem IsRelPert.const_mul {u : K} {n : ℕ} {x y : K} (h : IsRelPert u n x y) (c : K) :
    IsRelPert u n (c * x) (c * y) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  exact ⟨θ, hθ, by ring⟩

/-- A relative perturbation of `0` is `0`. -/
theorem IsRelPert.zero {u : K} {n : ℕ} (hγ : 0 ≤ gamma u n) : IsRelPert u n (0 : K) 0 :=
  ⟨0, by simpa using hγ, by simp⟩

/-- Multiplying a relative perturbation of order `k` by one rounding factor `1 + δ`, `|δ| ≤ u`:
order `k + 1`. -/
theorem IsRelPert.mul_one_add {u : K} (hu : 0 ≤ u) (hu1 : u < 1) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * u < 1) {x y δ : K} (h : IsRelPert u k x y) (hδ : |δ| ≤ u) :
    IsRelPert u (k + 1) x (y * (1 + δ)) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  exact ⟨(1 + θ) * (1 + δ) - 1, abs_one_add_mul_one_add_sub_one_le_gamma hu hu1 hk hθ hδ,
    by ring⟩

/-- Dividing a relative perturbation of order `k` by one rounding factor `1 + δ`, `|δ| ≤ u`:
order `k + 1`. -/
theorem IsRelPert.div_one_add {u : K} (hu : 0 ≤ u) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * u < 1) {x y δ : K} (h : IsRelPert u k x y) (hδ : |δ| ≤ u) :
    IsRelPert u (k + 1) x (y / (1 + δ)) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  refine ⟨(1 + θ) / (1 + δ) - 1, abs_one_add_div_one_add_sub_one_le_gamma hu hk hθ hδ, ?_⟩
  rw [show (1 : K) + ((1 + θ) / (1 + δ) - 1) = (1 + θ) / (1 + δ) by ring, mul_div_assoc]

/-- One more rounding raises the order of a relative perturbation by one. -/
theorem IsRelPert.rounds {m : RoundingModel K} (hu : m.u < 1) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * m.u < 1) {x y z : K} (h : IsRelPert m.u k x y)
    (hz : m.Rounds y z) : IsRelPert m.u (k + 1) x z := by
  obtain ⟨δ, hδ, rfl⟩ := hz.exists_delta
  exact h.mul_one_add m.u_nonneg hu hk hδ

/-- The sum of two nonnegative quantities perturbed to the same relative order is perturbed to
that order: the perturbation of the sum is the convex combination `(x₁ θ₁ + x₂ θ₂) / (x₁ + x₂)` of
the two perturbations. The step of `1 + τ²`, `a² + b²` and the like in the Givens and Householder
analyses. -/
theorem IsRelPert.add_of_nonneg {u : K} {k : ℕ} {x₁ x₂ y₁ y₂ : K} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h₁ : IsRelPert u k x₁ y₁) (h₂ : IsRelPert u k x₂ y₂) :
    IsRelPert u k (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  rcases (add_nonneg hx₁ hx₂).eq_or_lt with h | h
  · obtain rfl : x₁ = 0 := by linarith
    obtain rfl : x₂ = 0 := by linarith
    exact ⟨0, by simpa using (abs_nonneg θ₁).trans hθ₁, by simp⟩
  · refine ⟨(x₁ * θ₁ + x₂ * θ₂) / (x₁ + x₂), ?_, ?_⟩
    · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
      calc |x₁ * θ₁ + x₂ * θ₂| ≤ x₁ * |θ₁| + x₂ * |θ₂| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hx₁, abs_of_nonneg hx₂]
        _ ≤ x₁ * gamma u k + x₂ * gamma u k := by gcongr
        _ = gamma u k * (x₁ + x₂) := by ring
    · field_simp
      ring

end Steps

/-! ### Square roots -/

/-- `|√(1 + θ) - 1| ≤ |θ|` for `θ ≥ -1`. -/
theorem abs_sqrt_one_add_sub_one_le {θ : ℝ} (h : -1 ≤ θ) : |√(1 + θ) - 1| ≤ |θ| := by
  have h0 : 0 ≤ 1 + θ := by linarith
  have hs : 0 ≤ √(1 + θ) := Real.sqrt_nonneg _
  have hsq : √(1 + θ) ^ 2 = 1 + θ := Real.sq_sqrt h0
  have key : (√(1 + θ) - 1) * (√(1 + θ) + 1) = θ := by nlinarith
  have hpos : 1 ≤ √(1 + θ) + 1 := by linarith
  calc |√(1 + θ) - 1| ≤ |√(1 + θ) - 1| * (√(1 + θ) + 1) :=
        le_mul_of_one_le_right (abs_nonneg _) hpos
    _ = |(√(1 + θ) - 1) * (√(1 + θ) + 1)| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < √(1 + θ) + 1)]
    _ = |θ| := by rw [key]

/-- The square root of a relative perturbation of order `n` is one of order `n`, when `γ_n ≤ 1`.
-/
theorem IsRelPert.sqrt {u : ℝ} {n : ℕ} (hγ : gamma u n ≤ 1) {x y : ℝ} (hx : 0 ≤ x)
    (h : IsRelPert u n x y) : IsRelPert u n (√x) (√y) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  have hθ1 : -1 ≤ θ := by linarith [neg_le_of_abs_le hθ]
  refine ⟨√(1 + θ) - 1, (abs_sqrt_one_add_sub_one_le hθ1).trans hθ, ?_⟩
  rw [Real.sqrt_mul hx, add_sub_cancel]

end FloatingPoint
