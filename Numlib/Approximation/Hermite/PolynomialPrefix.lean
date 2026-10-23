import Numlib.Approximation.Hermite.Global

/-!
# Canonical finite polynomial-chain realizations

Successive actual polynomial intervals are appended to a smooth seed. Matching
endpoint jets prove finite smoothness and recover the exact polynomial on every
interval, including all derivatives through the specified order.
-/

open Polynomial Set
namespace Hermite

/-- The canonical function obtained by appending the first n polynomial intervals. -/
noncomputable def polynomialPrefix (p : ℕ) (x : ℕ → ℝ) (Q : ℕ → ℝ[X])
    (seed : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => seed
  | n + 1 => extendRight p (polynomialPrefix p x Q seed n) (Q n) (x n) (x (n + 1))

/-- The empty chain leaves its actual seed unchanged. -/
@[simp] theorem polynomialPrefix_zero (p : ℕ) (x : ℕ → ℝ) (Q : ℕ → ℝ[X])
    (seed : ℝ → ℝ) : polynomialPrefix p x Q seed 0 = seed := rfl

/-- Appending an interval uses the actual polynomial and its matching Taylor tail. -/
@[simp] theorem polynomialPrefix_succ (p : ℕ) (x : ℕ → ℝ) (Q : ℕ → ℝ[X])
    (seed : ℝ → ℝ) (n : ℕ) : polynomialPrefix p x Q seed (n + 1) =
      extendRight p (polynomialPrefix p x Q seed n) (Q n) (x n) (x (n + 1)) := rfl

/-- Increasing intervals and actual matching jets give a canonical smooth
realization, preserving every endpoint jet and exact polynomial interval. -/
theorem polynomialPrefix_spec {p n : ℕ} {x : ℕ → ℝ} {Q : ℕ → ℝ[X]}
    {jets : ℕ → ℕ → ℝ} {seed : ℝ → ℝ}
    (hx : ∀ i j, i < j → j ≤ n → x i < x j)
    (hleft : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (Q k).eval 0 = jets k j)
    (hright : ∀ k < n, ∀ j ≤ p,
      iteratedDeriv j (Q k).eval (x (k + 1) - x k) = jets (k + 1) j)
    (hs : ContDiff ℝ p seed)
    (hsj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j) :
    ContDiff ℝ p (polynomialPrefix p x Q seed n) ∧
      (∀ k ≤ n, ∀ j ≤ p,
        iteratedDeriv j (polynomialPrefix p x Q seed n) (x k) = jets k j) ∧
      ∀ k < n, ∀ j ≤ p, ∀ t ∈ Icc (x k) (x (k + 1)),
        iteratedDeriv j (polynomialPrefix p x Q seed n) t =
          iteratedDeriv j (Q k).eval (t - x k) := by
  induction n with
  | zero =>
    refine ⟨hs, ?_, ?_⟩
    · intro k hk j hj
      have hk0 : k = 0 := by omega
      subst k
      exact hsj j hj
    · intro k hk
      omega
  | succ n ih =>
    obtain ⟨hf, hjet, hint⟩ := ih
      (fun i j hij hj => hx i j hij (by omega))
      (fun k hk => hleft k (by omega)) (fun k hk => hright k (by omega))
    have hab : x n < x (n + 1) := hx n (n + 1) (by omega) le_rfl
    have hm : ∀ j ≤ p, iteratedDeriv j (polynomialPrefix p x Q seed n) (x n) =
        iteratedDeriv j (Q n).eval 0 := by
      intro j hj
      exact (hjet n le_rfl j hj).trans (hleft n (by omega) j hj).symm
    refine ⟨extendRight_contDiff hf hab.le hm, ?_, ?_⟩
    · intro k hk j hj
      by_cases hkn : k ≤ n
      · have hxn : x k ≤ x n := by
          rcases lt_or_eq_of_le hkn with hkn | rfl
          · exact (hx k n hkn (by omega)).le
          · exact le_rfl
        rw [polynomialPrefix_succ, extendRight_left hf hab.le hm hj hxn]
        exact hjet k hkn j hj
      · have hk' : k = n + 1 := by omega
        subst k
        rw [polynomialPrefix_succ, extendRight_interval hf hab.le hm hj ⟨hab.le, le_rfl⟩]
        exact hright n (by omega) j hj
    · intro k hk j hj t ht
      by_cases hkn : k < n
      · have hxn : x (k + 1) ≤ x n := by
          rcases lt_or_eq_of_le (show k + 1 ≤ n by omega) with hlt | heq
          · exact (hx (k + 1) n hlt (by omega)).le
          · exact congrArg x heq |>.le
        rw [polynomialPrefix_succ, extendRight_left hf hab.le hm hj (ht.2.trans hxn)]
        exact hint k hkn j hj t ht
      · have hkeq : k = n := by omega
        subst k
        rw [polynomialPrefix_succ, extendRight_interval hf hab.le hm hj ht]


/-- After a nonempty finite chain, all actual derivatives equal the terminal
Taylor tail. No behavior beyond the last interval is left unspecified. -/
theorem polynomialPrefix_tail {p n : ℕ} {x : ℕ → ℝ} {Q : ℕ → ℝ[X]}
    {jets : ℕ → ℕ → ℝ} {seed : ℝ → ℝ} (hn : 0 < n)
    (hx : ∀ i j, i < j → j ≤ n → x i < x j)
    (hleft : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (Q k).eval 0 = jets k j)
    (hright : ∀ k < n, ∀ j ≤ p,
      iteratedDeriv j (Q k).eval (x (k + 1) - x k) = jets (k + 1) j)
    (hs : ContDiff ℝ p seed)
    (hsj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j)
    {j : ℕ} (hj : j ≤ p) {t : ℝ} (ht : x n ≤ t) :
    iteratedDeriv j (polynomialPrefix p x Q seed n) t =
      iteratedDeriv j (taylorTail p (jets n) (x n)) t := by
  cases n with
  | zero => omega
  | succ n =>
    have hprev := polynomialPrefix_spec
      (fun i j hij hj => hx i j hij (hj.trans (Nat.le_succ n)))
      (fun k hk => hleft k (hk.trans_le (Nat.le_succ n)))
      (fun k hk => hright k (hk.trans_le (Nat.le_succ n))) hs hsj
    have hab : x n < x (n + 1) := hx n (n + 1) (by omega) le_rfl
    have hm : ∀ i ≤ p, iteratedDeriv i (polynomialPrefix p x Q seed n) (x n) =
        iteratedDeriv i (Q n).eval 0 := by
      intro i hi
      exact (hprev.2.1 n le_rfl i hi).trans (hleft n (by omega) i hi).symm
    rw [polynomialPrefix_succ, extendRight_tail hprev.1 hab hm hj ht,
      taylorTail_congr (hright n (by omega))]

/-- Actual derivatives before the chain preserve the entire smooth seed. -/
theorem polynomialPrefix_left {p n : ℕ} {x : ℕ → ℝ} {Q : ℕ → ℝ[X]}
    {jets : ℕ → ℕ → ℝ} {seed : ℝ → ℝ}
    (hx : ∀ i j, i < j → j ≤ n → x i < x j)
    (hleft : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (Q k).eval 0 = jets k j)
    (hright : ∀ k < n, ∀ j ≤ p,
      iteratedDeriv j (Q k).eval (x (k + 1) - x k) = jets (k + 1) j)
    (hs : ContDiff ℝ p seed)
    (hsj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j)
    {j : ℕ} (hj : j ≤ p) {t : ℝ} (ht : t ≤ x 0) :
    iteratedDeriv j (polynomialPrefix p x Q seed n) t = iteratedDeriv j seed t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx' : ∀ i j, i < j → j ≤ n → x i < x j :=
      fun i j hij hj => hx i j hij (hj.trans (Nat.le_succ n))
    have hl' : ∀ k < n, ∀ i ≤ p, iteratedDeriv i (Q k).eval 0 = jets k i :=
      fun k hk => hleft k (hk.trans_le (Nat.le_succ n))
    have hr' : ∀ k < n, ∀ i ≤ p,
        iteratedDeriv i (Q k).eval (x (k + 1) - x k) = jets (k + 1) i :=
      fun k hk => hright k (hk.trans_le (Nat.le_succ n))
    have hprev := polynomialPrefix_spec hx' hl' hr' hs hsj
    have hab : x n < x (n + 1) := hx n (n + 1) (by omega) le_rfl
    have hm : ∀ i ≤ p, iteratedDeriv i (polynomialPrefix p x Q seed n) (x n) =
        iteratedDeriv i (Q n).eval 0 := by
      intro i hi
      exact (hprev.2.1 n le_rfl i hi).trans (hleft n (by omega) i hi).symm
    have hx0 : x 0 ≤ x n := by
      by_cases hn : n = 0
      · simp [hn]
      · exact (hx 0 n (by omega) (Nat.le_succ n)).le
    rw [polynomialPrefix_succ, extendRight_left hprev.1 hab.le hm hj (ht.trans hx0)]
    exact ih hx' hl' hr'

/-- Uniform polynomial interval bounds give genuine derivative bounds over the
entire finite interpolation interval, without imposing bounds on the left tail. -/
theorem polynomialPrefix_bound {p n : ℕ} {x : ℕ → ℝ} {Q : ℕ → ℝ[X]}
    {jets : ℕ → ℕ → ℝ} {seed : ℝ → ℝ} {B : ℝ}
    (hx : ∀ i j, i < j → j ≤ n → x i < x j)
    (hleft : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (Q k).eval 0 = jets k j)
    (hright : ∀ k < n, ∀ j ≤ p,
      iteratedDeriv j (Q k).eval (x (k + 1) - x k) = jets (k + 1) j)
    (hs : ContDiff ℝ p seed)
    (hsj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j)
    (hsb : ∀ j ≤ p, |iteratedDeriv j seed (x 0)| ≤ B)
    (hb : ∀ k < n, ∀ j ≤ p, ∀ t ∈ Icc 0 (x (k + 1) - x k),
      |iteratedDeriv j (Q k).eval t| ≤ B) :
    ∀ j ≤ p, ∀ t ∈ Icc (x 0) (x n),
      |iteratedDeriv j (polynomialPrefix p x Q seed n) t| ≤ B := by
  induction n with
  | zero =>
    intro j hj t ht
    have he : t = x 0 := le_antisymm ht.2 ht.1
    subst t
    exact hsb j hj
  | succ n ih =>
    have hx' : ∀ i j, i < j → j ≤ n → x i < x j :=
      fun i j hij hj => hx i j hij (hj.trans (Nat.le_succ n))
    have hl' : ∀ k < n, ∀ i ≤ p, iteratedDeriv i (Q k).eval 0 = jets k i :=
      fun k hk => hleft k (hk.trans_le (Nat.le_succ n))
    have hr' : ∀ k < n, ∀ i ≤ p,
        iteratedDeriv i (Q k).eval (x (k + 1) - x k) = jets (k + 1) i :=
      fun k hk => hright k (hk.trans_le (Nat.le_succ n))
    have hprev := polynomialPrefix_spec hx' hl' hr' hs hsj
    have hab : x n < x (n + 1) := hx n (n + 1) (by omega) le_rfl
    have hm : ∀ i ≤ p, iteratedDeriv i (polynomialPrefix p x Q seed n) (x n) =
        iteratedDeriv i (Q n).eval 0 := by
      intro i hi
      exact (hprev.2.1 n le_rfl i hi).trans (hleft n (by omega) i hi).symm
    intro j hj t ht
    by_cases htn : t ≤ x n
    · rw [polynomialPrefix_succ, extendRight_left hprev.1 hab.le hm hj htn]
      exact ih hx' hl' hr' (fun k hk => hb k (hk.trans_le (Nat.le_succ n))) j hj t
        ⟨ht.1, htn⟩
    · rw [polynomialPrefix_succ, extendRight_interval hprev.1 hab.le hm hj
        ⟨(lt_of_not_ge htn).le, ht.2⟩]
      exact hb n (by omega) j hj (t - x n)
        ⟨sub_nonneg.mpr (lt_of_not_ge htn).le, sub_le_sub_right ht.2 (x n)⟩

end Hermite
