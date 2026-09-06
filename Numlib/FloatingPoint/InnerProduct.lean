import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Numlib.FloatingPoint.Model
import Numlib.LinearAlgebra.Matrix.Order

/-!
# Rounding errors of inner products and matrix products

The componentwise error bounds of [higham2002accuracy] §3.1–3.5 for recursive summation, inner
products, matrix–vector products and matrix products, in the relational model of
`Numlib/FloatingPoint/Model.lean`.

Everything here is about an *explicit evaluation order*: `RoundsSumFrom m s l t` says that `t`
arises from the partial sum `s` by adding the terms of the list `l` from left to right, rounding
after each addition, and `RoundsSum m l s` is the recursive summation `s₁ = x₁`, `sᵢ = fl(sᵢ₋₁ +
xᵢ)`.  `RoundsDot m x y s` computes an inner product as the recursive sum, in some order of the
indices, of the rounded products `fl(xᵢ yᵢ)`; the order is existentially quantified, so a theorem
about it holds whatever order an implementation uses.  Because the rounding relation is not a
function, every statement quantifies over all admissible roundings at once.

The bounds are [higham2002accuracy]:

* `abs_sub_le_of_roundsSum` — `|ŝ - ∑ xᵢ| ≤ γ_{n-1} ∑ |xᵢ|`;
* `abs_sub_le_of_roundsDot` — `|fl(xᵀy) - xᵀy| ≤ γ_n |x|ᵀ|y|`, with the backward form `fl(xᵀy) = (x
  + Δx)ᵀ y`, `|Δx| ≤ γ_n |x|`, as `exists_roundsDot_eq_dotProduct_add`;
* `abs_sub_le_of_roundsMulVec` and `abs_sub_entrywiseLE_of_roundsMul` — `|ŷ - A x| ≤ γ_n |A| |x|`
  and `|Ĉ - A B| ≤ γ_n |A| |B|`, in the entrywise order of `Numlib/LinearAlgebra/Matrix/Order.lean`.

The uniform bound `‖ŷ - A x‖_∞ ≤ γ_n ‖A‖_∞ ‖x‖_∞` is `abs_sub_le_of_roundsMulVec_of_abs_le`, stated
with row sums and an entrywise bound on `x` rather than with norms, since the scalar field here
carries an order but no norm.

Every proof rests on one scalar step, `FloatingPoint.gamma_mul_one_add_add_le`, that is `γ_k (1 + u)
+ u ≤ γ_{k+1}`: one more rounding raises the order of a relative perturbation by one.
-/

open Finset

open scoped Matrix

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The scalar step -/

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

/-! ### Recursive summation -/

/-- `RoundsSumFrom m s l t`: starting from the partial sum `s`, the terms of the list `l` are added
from left to right, one rounding per addition, and `t` is an admissible result.  The relation is not
functional, so a theorem proved about it holds for every admissible sequence of roundings. -/
inductive RoundsSumFrom (m : RoundingModel K) : K → List K → K → Prop
  /-- Adding no terms leaves the partial sum unchanged. -/
  | nil (s : K) : RoundsSumFrom m s [] s
  /-- One rounded addition, followed by the rest of the list. -/
  | cons {s x t r : K} {l : List K} (ht : m.Rounds (s + x) t) (hr : RoundsSumFrom m t l r) :
      RoundsSumFrom m s (x :: l) r

/-- `RoundsSum m l s`: `s` is an admissible floating-point value of the **recursive summation** `s₁
= x₁`, `sᵢ = fl(sᵢ₋₁ + xᵢ)` of the list `l` ([higham2002accuracy], §3.1).  The first term enters
unrounded, so a list of length `n` costs `n - 1` roundings. -/
def RoundsSum (m : RoundingModel K) : List K → K → Prop
  | [], s => s = 0
  | x :: l, s => RoundsSumFrom m x l s

/-- The recursive summation of the empty list is `0`. -/
@[simp]
theorem roundsSum_nil {m : RoundingModel K} {s : K} : RoundsSum m [] s ↔ s = 0 := Iff.rfl

/-- The recursive summation of `x :: l` is the left-to-right sweep over `l` started at the
*unrounded* first term `x`, which is why a list of length `n` costs only `n - 1` roundings. -/
@[simp]
theorem roundsSum_cons {m : RoundingModel K} {x : K} {l : List K} {s : K} :
    RoundsSum m (x :: l) s ↔ RoundsSumFrom m x l s := Iff.rfl

/-- The sum of the absolute values of a list is nonnegative. -/
private theorem sum_map_abs_nonneg (l : List K) : 0 ≤ (l.map (|·|)).sum :=
  List.sum_nonneg fun _ hy => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
    exact abs_nonneg z

/-- **[higham2002accuracy] bound for recursive summation from a partial sum** (*Accuracy and
Stability of Numerical Algorithms*, (3.2)–(3.3)): adding the `k` terms of `l` to `s`, one rounding
per addition, perturbs the exact value `s + ∑ lᵢ` by at most `γ_k (|s| + ∑ |lᵢ|)`. -/
theorem abs_sub_le_of_roundsSumFrom {m : RoundingModel K} (hu : m.u < 1) {s : K} {l : List K}
    {t : K} (h : RoundsSumFrom m s l t) (hlu : ((l.length : ℕ) : K) * m.u < 1) :
    |t - (s + l.sum)| ≤ gamma m.u l.length * (|s| + (l.map (|·|)).sum) := by
  induction h with
  | nil s => simp
  | @cons s x t r l ht hr ih =>
    rw [List.length_cons] at hlu
    have hcast : ((l.length + 1 : ℕ) : K) * m.u = (l.length : K) * m.u + m.u := by push_cast; ring
    have hl : (l.length : K) * m.u < 1 := by
      rw [hcast] at hlu; linarith [m.u_nonneg]
    have ihl := ih hl
    have hS : 0 ≤ (l.map (|·|)).sum := sum_map_abs_nonneg l
    have hA : 0 ≤ |s| + |x| := by positivity
    have hgl : 0 ≤ gamma m.u l.length := gamma_nonneg m.u_nonneg hl
    have hround : |t - (s + x)| ≤ m.u * (|s| + |x|) :=
      (m.abs_sub_le ht).trans (mul_le_mul_of_nonneg_left (abs_add_le s x) m.u_nonneg)
    have habs : |t| ≤ (1 + m.u) * (|s| + |x|) := by
      have h1 : |t| ≤ |t - (s + x)| + |s + x| := by
        simpa using abs_add_le (t - (s + x)) (s + x)
      have h2 : |s + x| ≤ |s| + |x| := abs_add_le s x
      nlinarith
    have htail : |r - (t + l.sum)|
        ≤ gamma m.u l.length * ((1 + m.u) * (|s| + |x|) + (l.map (|·|)).sum) :=
      ihl.trans (mul_le_mul_of_nonneg_left (by linarith) hgl)
    have hstep : gamma m.u l.length * (1 + m.u) + m.u ≤ gamma m.u (l.length + 1) :=
      gamma_mul_one_add_add_le m.u_nonneg hu hlu
    have hmono : gamma m.u l.length ≤ gamma m.u (l.length + 1) :=
      gamma_mono m.u_nonneg (Nat.le_succ _) hlu
    have hsplit : |r - (s + (x :: l).sum)| ≤ |r - (t + l.sum)| + |t - (s + x)| := by
      have harg : r - (s + (x :: l).sum) = r - (t + l.sum) + (t - (s + x)) := by
        simp only [List.sum_cons]; ring
      rw [harg]
      exact abs_add_le _ _
    refine hsplit.trans ?_
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    calc |r - (t + l.sum)| + |t - (s + x)|
        ≤ gamma m.u l.length * ((1 + m.u) * (|s| + |x|) + (l.map (|·|)).sum)
            + m.u * (|s| + |x|) := add_le_add htail hround
      _ = (gamma m.u l.length * (1 + m.u) + m.u) * (|s| + |x|)
            + gamma m.u l.length * (l.map (|·|)).sum := by ring
      _ ≤ gamma m.u (l.length + 1) * (|s| + |x|)
            + gamma m.u (l.length + 1) * (l.map (|·|)).sum :=
          add_le_add (mul_le_mul_of_nonneg_right hstep hA)
            (mul_le_mul_of_nonneg_right hmono hS)
      _ = gamma m.u (l.length + 1) * (|s| + (|x| + (l.map (|·|)).sum)) := by ring

/-- **[higham2002accuracy] bound for recursive summation** (*Accuracy and Stability of Numerical
Algorithms*, (3.2)–(3.3)): a computed sum of `n` numbers differs from the exact sum by at most
`γ_{n-1} ∑ |xᵢ|`. -/
theorem abs_sub_le_of_roundsSum {m : RoundingModel K} (hu : m.u < 1) {l : List K} {s : K}
    (h : RoundsSum m l s) (hlu : ((l.length - 1 : ℕ) : K) * m.u < 1) :
    |s - l.sum| ≤ gamma m.u (l.length - 1) * (l.map (|·|)).sum := by
  cases l with
  | nil => simp only [roundsSum_nil] at h; simp [h]
  | cons x l =>
    simp only [List.length_cons, Nat.add_sub_cancel] at hlu ⊢
    simpa using abs_sub_le_of_roundsSumFrom hu (roundsSum_cons.1 h) hlu

/-! ### Inner products -/

variable {ι : Type*}

/-- `RoundsDot m x y s`: `s` is an admissible floating-point value of the inner product `xᵀ y`,
computed as the recursive summation, in some order `o` of the indices, of the rounded products
`fl(xᵢ yᵢ)` ([higham2002accuracy], §3.1).  The order is existentially quantified, so a theorem about
`RoundsDot` holds for every order in which an implementation may accumulate the products. -/
def RoundsDot (m : RoundingModel K) (x y : ι → K) (s : K) : Prop :=
  ∃ (o : List ι) (p : ι → K), o.Nodup ∧ (∀ i, i ∈ o) ∧ (∀ i, m.Rounds (x i * y i) (p i)) ∧
    RoundsSum m (o.map p) s

variable [Fintype ι]

/-- **[higham2002accuracy] inner-product bound** (*Accuracy and Stability of Numerical Algorithms*,
(3.4)): a computed inner product of two vectors of length `n` satisfies `|fl(xᵀy) - xᵀy| ≤ γ_n
|x|ᵀ|y|`, whatever the order of accumulation. -/
theorem abs_sub_le_of_roundsDot {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ι : K) * m.u < 1) {x y : ι → K} {s : K} (h : RoundsDot m x y s) :
    |s - x ⬝ᵥ y| ≤ gamma m.u (Fintype.card ι) * (|x| ⬝ᵥ |y|) := by
  classical
  obtain ⟨o, p, hnodup, hfull, hp, hsum⟩ := h
  have hdotxy : x ⬝ᵥ y = ∑ i, x i * y i := rfl
  have hdotabs : |x| ⬝ᵥ |y| = ∑ i, |x i| * |y i| := rfl
  have huniv : o.toFinset = (univ : Finset ι) :=
    Finset.eq_univ_iff_forall.2 fun i => List.mem_toFinset.2 (hfull i)
  have hlen : o.length = Fintype.card ι := by
    rw [← List.toFinset_card_of_nodup hnodup, huniv, Finset.card_univ]
  have hD0 : (0 : K) ≤ ∑ i, |x i| * |y i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpi : ∀ i, |p i - x i * y i| ≤ m.u * (|x i| * |y i|) := fun i => by
    have h := m.abs_sub_le (hp i)
    rwa [abs_mul] at h
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hzero | hpos
  · have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.1 hzero
    rcases o with _ | ⟨i₀, o'⟩
    · simp only [List.map_nil, roundsSum_nil] at hsum
      simp [hsum, hdotxy, hdotabs]
    · exact (hempty.false i₀).elim
  · obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
    have hcast : ((n + 1 : ℕ) : K) * m.u = (n : K) * m.u + m.u := by push_cast; ring
    have hnu : ((n : ℕ) : K) * m.u < 1 := by
      rw [hn, hcast] at hcard; linarith [m.u_nonneg]
    have hgn : 0 ≤ gamma m.u n := gamma_nonneg m.u_nonneg hnu
    -- the sums over the order `o` are the sums over the index type
    have hmapabs : (o.map p).map (|·|) = o.map fun i => |p i| := by
      simp [List.map_map, Function.comp_def]
    have hsumeq : (o.map p).sum = ∑ i, p i := by rw [← List.sum_toFinset p hnodup, huniv]
    have habs : ((o.map p).map (|·|)).sum = ∑ i, |p i| := by
      rw [hmapabs, ← List.sum_toFinset (fun i => |p i|) hnodup, huniv]
    -- the error of the recursive summation of the rounded products
    have hbound := abs_sub_le_of_roundsSum hu hsum
      (by rw [List.length_map, hlen, hn, Nat.add_sub_cancel]; exact hnu)
    rw [List.length_map, hlen, hn, Nat.add_sub_cancel, hsumeq, habs] at hbound
    -- the error of the rounded products themselves
    have hprod : |∑ i, p i - x ⬝ᵥ y| ≤ m.u * ∑ i, |x i| * |y i| := by
      have hsplit : ∑ i, p i - x ⬝ᵥ y = ∑ i, (p i - x i * y i) := by
        rw [hdotxy, ← Finset.sum_sub_distrib]
      calc |∑ i, p i - x ⬝ᵥ y| = |∑ i, (p i - x i * y i)| := by rw [hsplit]
        _ ≤ ∑ i, |p i - x i * y i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, m.u * (|x i| * |y i|) := Finset.sum_le_sum fun i _ => hpi i
        _ = m.u * ∑ i, |x i| * |y i| := by rw [← Finset.mul_sum]
    have hsize : ∑ i, |p i| ≤ (1 + m.u) * ∑ i, |x i| * |y i| := by
      have hbd : ∀ i ∈ (univ : Finset ι), |p i| ≤ (1 + m.u) * (|x i| * |y i|) := fun i _ => by
        have h1 : |p i| ≤ |p i - x i * y i| + |x i * y i| := by
          simpa using abs_add_le (p i - x i * y i) (x i * y i)
        rw [abs_mul] at h1
        nlinarith [hpi i]
      calc ∑ i, |p i| ≤ ∑ i, (1 + m.u) * (|x i| * |y i|) := Finset.sum_le_sum hbd
        _ = (1 + m.u) * ∑ i, |x i| * |y i| := by rw [← Finset.mul_sum]
    have hstep : gamma m.u n * (1 + m.u) + m.u ≤ gamma m.u (n + 1) :=
      gamma_mul_one_add_add_le m.u_nonneg hu (by rw [← hn]; exact hcard)
    have hsplit : |s - x ⬝ᵥ y| ≤ |s - ∑ i, p i| + |∑ i, p i - x ⬝ᵥ y| := by
      have harg : s - x ⬝ᵥ y = s - ∑ i, p i + (∑ i, p i - x ⬝ᵥ y) := by ring
      rw [harg]
      exact abs_add_le _ _
    rw [hn, hdotabs]
    refine hsplit.trans ?_
    calc |s - ∑ i, p i| + |∑ i, p i - x ⬝ᵥ y|
        ≤ gamma m.u n * ((1 + m.u) * ∑ i, |x i| * |y i|) + m.u * ∑ i, |x i| * |y i| :=
          add_le_add (hbound.trans (mul_le_mul_of_nonneg_left hsize hgn)) hprod
      _ = (gamma m.u n * (1 + m.u) + m.u) * ∑ i, |x i| * |y i| := by ring
      _ ≤ gamma m.u (n + 1) * ∑ i, |x i| * |y i| := mul_le_mul_of_nonneg_right hstep hD0

/-- The elementary redistribution behind the backward form of an error bound: a residual `r` no
larger than `c ∑ |aᵢ| |bᵢ|` is realised by a componentwise perturbation of `a` of relative size `c`.
-/
private theorem exists_dot_eq_of_abs_le {c r : K} (hc : 0 ≤ c) {a b : ι → K}
    (h : |r| ≤ c * ∑ i, |a i| * |b i|) :
    ∃ d : ι → K, (∀ i, |d i| ≤ c * |a i|) ∧ ∑ i, d i * b i = r := by
  have hS0 : (0 : K) ≤ ∑ i, |a i| * |b i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsign : ∀ i, |b i| / b i * b i = |b i| := fun i => by
    rcases eq_or_ne (b i) 0 with hb | hb
    · simp [hb]
    · rw [div_mul_cancel₀ _ hb]
  rcases eq_or_lt_of_le (mul_nonneg hc hS0) with hcz | hcpos
  · refine ⟨0, fun i => by simpa using mul_nonneg hc (abs_nonneg (a i)), ?_⟩
    have hr : |r| ≤ 0 := by rw [← hcz] at h; exact h
    simp [abs_nonpos_iff.1 hr]
  · obtain ⟨θ, hθ, hθr⟩ : ∃ θ : K, |θ| ≤ 1 ∧ c * θ * ∑ i, |a i| * |b i| = r := by
      refine ⟨r / (c * ∑ i, |a i| * |b i|), ?_, ?_⟩
      · rw [abs_div, abs_of_pos hcpos, div_le_one hcpos]
        exact h
      · have hne : c * (∑ i, |a i| * |b i|) ≠ 0 := ne_of_gt hcpos
        have hrw : c * (r / (c * ∑ i, |a i| * |b i|)) * ∑ i, |a i| * |b i|
            = c * (∑ i, |a i| * |b i|) * (r / (c * ∑ i, |a i| * |b i|)) := by ring
        rw [hrw, mul_div_cancel₀ _ hne]
    refine ⟨fun i => c * θ * |a i| * (|b i| / b i), fun i => ?_, ?_⟩
    · have hq : |(|b i| / b i)| ≤ 1 := by
        rcases eq_or_ne (b i) 0 with hb | hb
        · simp [hb]
        · rw [abs_div, abs_abs, div_self (abs_ne_zero.2 hb)]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_abs]
      calc c * |θ| * |a i| * |(|b i| / b i)|
          ≤ c * 1 * |a i| * 1 := by gcongr
        _ = c * |a i| := by ring
    · have hterm : ∀ i : ι, c * θ * |a i| * (|b i| / b i) * b i = c * θ * (|a i| * |b i|) :=
        fun i => by rw [mul_assoc (c * θ * |a i|), hsign i]; ring
      calc ∑ i, c * θ * |a i| * (|b i| / b i) * b i
          = ∑ i, c * θ * (|a i| * |b i|) := Finset.sum_congr rfl fun i _ => hterm i
        _ = c * θ * ∑ i, |a i| * |b i| := by rw [Finset.mul_sum]
        _ = r := hθr

/-- **The backward form of [higham2002accuracy] inner-product bound** (*Accuracy and Stability of
Numerical Algorithms*, (3.5)): a computed inner product is the exact inner product of a
componentwise relative perturbation of `x` with `y`, `fl(xᵀ y) = (x + Δx)ᵀ y` with `|Δx| ≤ γ_n |x|`.
-/
theorem exists_roundsDot_eq_dotProduct_add {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ι : K) * m.u < 1) {x y : ι → K} {s : K} (h : RoundsDot m x y s) :
    ∃ dx : ι → K, (∀ i, |dx i| ≤ gamma m.u (Fintype.card ι) * |x i|) ∧ s = (x + dx) ⬝ᵥ y := by
  have hbound := abs_sub_le_of_roundsDot hu hcard h
  obtain ⟨d, hd, hsum⟩ :=
    exists_dot_eq_of_abs_le (c := gamma m.u (Fintype.card ι)) (r := s - x ⬝ᵥ y) (a := x) (b := y)
      (gamma_nonneg m.u_nonneg hcard) hbound
  refine ⟨d, hd, ?_⟩
  have hexp : (x + d) ⬝ᵥ y = x ⬝ᵥ y + ∑ i, d i * y i := by
    rw [add_dotProduct]
    rfl
  rw [hexp, hsum]
  ring

/-! ### Matrix–vector and matrix–matrix products -/

variable {μ ν ρ : Type*}

/-- `RoundsMulVec m A x ŷ`: every entry of `ŷ` is an admissible computed inner product of the
corresponding row of `A` with `x`, which is how a matrix–vector product is evaluated
([higham2002accuracy], §3.5). -/
def RoundsMulVec (m : RoundingModel K) (A : Matrix μ ν K) (x : ν → K) (yhat : μ → K) : Prop :=
  ∀ i, RoundsDot m (A i) x (yhat i)

/-- `RoundsMul m A B Ĉ`: every entry of `Ĉ` is an admissible computed inner product of a row of `A`
with a column of `B`. -/
def RoundsMul (m : RoundingModel K) (A : Matrix μ ν K) (B : Matrix ν ρ K) (C : Matrix μ ρ K) :
    Prop :=
  ∀ i j, RoundsDot m (A i) (fun k => B k j) (C i j)

variable [Fintype ν]

/-- **[higham2002accuracy] matrix–vector bound** (*Accuracy and Stability of Numerical Algorithms*,
(3.12)): a computed matrix–vector product satisfies `|ŷ - A x| ≤ γ_n |A| |x|` entrywise, `n` being
the inner dimension. -/
theorem abs_sub_le_of_roundsMulVec {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ν : K) * m.u < 1) {A : Matrix μ ν K} {x : ν → K} {yhat : μ → K}
    (h : RoundsMulVec m A x yhat) :
    |yhat - A *ᵥ x| ≤ gamma m.u (Fintype.card ν) • (A.abs *ᵥ |x|) := by
  refine Pi.le_def.2 fun i => ?_
  have hi := abs_sub_le_of_roundsDot hu hcard (h i)
  have hlhs : |yhat - A *ᵥ x| i = |yhat i - A i ⬝ᵥ x| := rfl
  have hrhs : (gamma m.u (Fintype.card ν) • (A.abs *ᵥ |x|)) i
      = gamma m.u (Fintype.card ν) * (|A i| ⬝ᵥ |x|) := rfl
  rw [hlhs, hrhs]
  exact hi

/-- **[higham2002accuracy] matrix–matrix bound** (*Accuracy and Stability of Numerical Algorithms*,
(3.13)): a computed matrix product satisfies `|Ĉ - A B| ≤ γ_n |A| |B|` in the entrywise order. -/
theorem abs_sub_entrywiseLE_of_roundsMul {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ν : K) * m.u < 1) {A : Matrix μ ν K} {B : Matrix ν ρ K}
    {C : Matrix μ ρ K} (h : RoundsMul m A B C) :
    (C - A * B).abs ≤ₑ gamma m.u (Fintype.card ν) • (A.abs * B.abs) := by
  intro i j
  have hij := abs_sub_le_of_roundsDot hu hcard (h i j)
  have hlhs : (C - A * B).abs i j = |C i j - A i ⬝ᵥ fun k => B k j| := rfl
  have hrhs : (gamma m.u (Fintype.card ν) • (A.abs * B.abs)) i j
      = gamma m.u (Fintype.card ν) * (|A i| ⬝ᵥ fun k => |B k j|) := rfl
  rw [hlhs, hrhs]
  exact hij

/-- The uniform (`∞`-norm) form of `abs_sub_le_of_roundsMulVec`: if every entry of `x` is at most
`c` in absolute value, then every entry of the computed residual is at most `γ_n` times the row sum
of `|A|` times `c`.  This is `‖ŷ - A x‖_∞ ≤ γ_n ‖A‖_∞ ‖x‖_∞` written without a norm, since the
scalar field carries only an order. -/
theorem abs_sub_le_of_roundsMulVec_of_abs_le {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ν : K) * m.u < 1) {A : Matrix μ ν K} {x : ν → K} {yhat : μ → K}
    (h : RoundsMulVec m A x yhat) {c : K} (hx : ∀ j, |x j| ≤ c) (i : μ) :
    |yhat i - (A *ᵥ x) i| ≤ gamma m.u (Fintype.card ν) * ((∑ j, |A i j|) * c) := by
  have hrow : ∑ j, |A i j| * |x j| ≤ (∑ j, |A i j|) * c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg (A i j))
  have hi := abs_sub_le_of_roundsDot hu hcard (h i)
  have hlhs : |yhat i - (A *ᵥ x) i| = |yhat i - A i ⬝ᵥ x| := rfl
  have hdot : (|A i| : ν → K) ⬝ᵥ |x| = ∑ j, |A i j| * |x j| := rfl
  rw [hlhs]
  refine hi.trans ?_
  rw [hdot]
  exact mul_le_mul_of_nonneg_left hrow (gamma_nonneg m.u_nonneg hcard)

end FloatingPoint
