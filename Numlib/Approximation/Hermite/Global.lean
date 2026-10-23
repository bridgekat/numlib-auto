import Numlib.Approximation.Hermite.Endpoint
import Numlib.Approximation.Hermite.Reflection
import Numlib.Analysis.Calculus.ContDiff.Piecewise
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Tactic

/-!
# Global interpolation of finite real jets

A polynomial interval is prolonged by its terminal Taylor polynomial. Matching
jets make this prolongation `C^p`; its highest derivative has the same Lipschitz
constant as on the original interval. Appending these intervals inductively
produces a smooth interpolant of a finite chain of jets.

Two additional intervals join the endpoint jets to constant exterior tails.
Their widths depend on the endpoint jets, whereas the Lipschitz constant is
chosen before the data. Under a uniform bound on the original jets and steps,
the terminal jets and both exterior widths are uniformly bounded as well. This
gives bounds on every actual derivative through order `p` on the whole line.
-/

open Polynomial Set

namespace Hermite

/-- The highest derivative of an initial Taylor polynomial is its highest jet. -/
theorem initialPolynomial_iteratedDeriv_top (p : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    iteratedDeriv p (fun z => (initialPolynomial p a).eval z) t = a p := by
  have hdeg : (initialPolynomial p a).natDegree ≤ p := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact coeff_eq_zero_of_degree_lt ((initialPolynomial_degree_lt p a).trans_le
      (by exact_mod_cast hn))
  have htop := natDegree_iterate_derivative (initialPolynomial p a) p
  have hzero : (derivative^[p] (initialPolynomial p a)).natDegree = 0 := by omega
  calc
    _ = (derivative^[p] (initialPolynomial p a)).eval t :=
      congrFun (Polynomial.iteratedDeriv_eval _ p) t
    _ = (derivative^[p] (initialPolynomial p a)).eval 0 := by
      rw [eq_C_of_natDegree_eq_zero hzero]
      simp only [eval_C]
    _ = a p := initialPolynomial_zero p a le_rfl

/-- Every real polynomial is continuously differentiable to every finite order. -/
theorem polynomial_contDiff (Q : ℝ[X]) (p : ℕ) :
    ContDiff ℝ p (fun t => Q.eval t) := by
  simpa using Q.contDiff_aeval (𝕜 := ℝ) p

/-- The Taylor polynomial of a prescribed jet, centered at a real point. -/
noncomputable def taylorTail (p : ℕ) (a : ℕ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun t => (initialPolynomial p a).eval (t - b)

/-- A centered Taylor tail is continuously differentiable to order `p`. -/
theorem taylorTail_contDiff (p : ℕ) (a : ℕ → ℝ) (b : ℝ) :
    ContDiff ℝ p (taylorTail p a b) :=
  (polynomial_contDiff _ p).comp (contDiff_id.sub contDiff_const)

/-- A Taylor tail attains every prescribed derivative at its center. -/
theorem taylorTail_jet (p : ℕ) (a : ℕ → ℝ) (b : ℝ) {j : ℕ} (hj : j ≤ p) :
    iteratedDeriv j (taylorTail p a b) b = a j := by
  unfold taylorTail
  rw [iteratedDeriv_comp_sub_const j (fun z => (initialPolynomial p a).eval z) b]
  simpa only [sub_self, Polynomial.iteratedDeriv_eval] using initialPolynomial_zero p a hj

/-- The highest derivative of a Taylor tail is constant on the whole line. -/
theorem taylorTail_top (p : ℕ) (a : ℕ → ℝ) (b t : ℝ) :
    iteratedDeriv p (taylorTail p a b) t = a p := by
  unfold taylorTail
  rw [iteratedDeriv_comp_sub_const p (fun z => (initialPolynomial p a).eval z) b]
  exact initialPolynomial_iteratedDeriv_top p a _

/-- A polynomial up to an endpoint, prolonged by its matching Taylor tail. -/
noncomputable def intervalTail (p : ℕ) (Q : ℝ[X]) (s : ℝ) : ℝ → ℝ :=
  (Iic s).piecewise (fun t => Q.eval t)
    (taylorTail p (fun j => iteratedDeriv j (fun t => Q.eval t) s) s)

private theorem intervalTail_matching (p : ℕ) (Q : ℝ[X]) (s : ℝ) :
    ∀ j ≤ p, iteratedDeriv j (fun t => Q.eval t) s =
      iteratedDeriv j (taylorTail p (fun i => iteratedDeriv i (fun t => Q.eval t) s) s) s := by
  intro j hj
  rw [taylorTail_jet p _ s hj]

/-- Prolongation by a matching Taylor tail preserves `C^p` regularity. -/
theorem intervalTail_contDiff (p : ℕ) (Q : ℝ[X]) (s : ℝ) :
    ContDiff ℝ p (intervalTail p Q s) :=
  contDiff_piecewise_Iic (polynomial_contDiff Q p) (taylorTail_contDiff p _ s)
    (intervalTail_matching p Q s)

/-- Every derivative through order `p` is the corresponding piecewise derivative. -/
theorem intervalTail_iteratedDeriv (p : ℕ) (Q : ℝ[X]) (s : ℝ) {j : ℕ} (hj : j ≤ p) :
    iteratedDeriv j (intervalTail p Q s) =
      (Iic s).piecewise (iteratedDeriv j (fun t => Q.eval t))
        (iteratedDeriv j (taylorTail p (fun i => iteratedDeriv i (fun t => Q.eval t) s) s)) :=
  iteratedDeriv_piecewise_Iic (polynomial_contDiff Q p) (taylorTail_contDiff p _ s)
    (intervalTail_matching p Q s) hj

/-- Every derivative before the endpoint agrees with the original polynomial. -/
theorem intervalTail_left (p : ℕ) (Q : ℝ[X]) {s t : ℝ} {j : ℕ}
    (hj : j ≤ p) (ht : t ≤ s) :
    iteratedDeriv j (intervalTail p Q s) t = iteratedDeriv j (fun z => Q.eval z) t := by
  rw [intervalTail_iteratedDeriv p Q s hj, piecewise_eq_of_mem (Iic s) _ _ ht]

/-- Every derivative after the endpoint agrees with the terminal Taylor tail. -/
theorem intervalTail_right (p : ℕ) (Q : ℝ[X]) {s t : ℝ} {j : ℕ}
    (hj : j ≤ p) (ht : s ≤ t) :
    iteratedDeriv j (intervalTail p Q s) t =
      iteratedDeriv j (taylorTail p (fun i => iteratedDeriv i (fun z => Q.eval z) s) s) t := by
  rw [intervalTail_iteratedDeriv p Q s hj]
  by_cases hts : t ≤ s
  · have heq : t = s := le_antisymm hts ht
    subst t
    simpa only [piecewise_eq_of_mem (Iic s) _ _ (show s ∈ Iic s by simp)] using
      intervalTail_matching p Q s j hj
  · exact piecewise_eq_of_notMem (Iic s) _ _ hts

/-- A terminal Taylor tail preserves the highest derivative Lipschitz constant. -/
theorem intervalTail_lipschitzOn_top (p : ℕ) (Q : ℝ[X]) {s : ℝ} (hs : 0 ≤ s)
    {L : NNReal} (hQ : LipschitzOnWith L (iteratedDeriv p (fun t => Q.eval t)) (Icc 0 s)) :
    LipschitzOnWith L (iteratedDeriv p (intervalTail p Q s)) (Ici 0) := by
  rw [intervalTail_iteratedDeriv p Q s le_rfl]
  apply LipschitzOnWith.piecewise_Iic _ _ hs
    ((intervalTail_matching p Q s) p le_rfl)
  · convert hQ using 1
    ext t
    rfl
  · apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro x _hx y _hy
    rw [taylorTail_top, taylorTail_top, sub_self, norm_zero]
    positivity

/-- Append a translated polynomial interval and its Taylor tail to a function. -/
noncomputable def extendRight (p : ℕ) (f : ℝ → ℝ) (Q : ℝ[X]) (a b : ℝ) : ℝ → ℝ :=
  (Iic a).piecewise f (fun t => intervalTail p Q (b - a) (t - a))

private theorem extendRight_matching {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0) :
    ∀ j ≤ p, iteratedDeriv j f a =
      iteratedDeriv j (fun t => intervalTail p Q (b - a) (t - a)) a := by
  intro j hj
  rw [iteratedDeriv_comp_sub_const j (intervalTail p Q (b - a)) a]
  simpa only [sub_self, intervalTail_left p Q hj (sub_nonneg.mpr hab)] using hjet j hj

/-- Appending a polynomial interval with matching jets preserves `C^p` regularity. -/
theorem extendRight_contDiff {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b : ℝ}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0) :
    ContDiff ℝ p (extendRight p f Q a b) :=
  contDiff_piecewise_Iic hf
    ((intervalTail_contDiff p Q (b - a)).comp (contDiff_id.sub contDiff_const))
    (extendRight_matching hab hjet)

/-- Exact derivatives of a function with an appended polynomial interval. -/
theorem extendRight_iteratedDeriv {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b : ℝ}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    {j : ℕ} (hj : j ≤ p) :
    iteratedDeriv j (extendRight p f Q a b) =
      (Iic a).piecewise (iteratedDeriv j f)
        (fun t => iteratedDeriv j (intervalTail p Q (b - a)) (t - a)) := by
  have hder : iteratedDeriv j (extendRight p f Q a b) =
      (Iic a).piecewise (iteratedDeriv j f)
        (iteratedDeriv j (fun t => intervalTail p Q (b - a) (t - a))) :=
    iteratedDeriv_piecewise_Iic hf
      ((intervalTail_contDiff p Q (b - a)).comp (contDiff_id.sub contDiff_const))
      (extendRight_matching hab hjet) hj
  rw [hder, iteratedDeriv_comp_sub_const j (intervalTail p Q (b - a)) a]

/-- Appending an interval preserves every earlier derivative through order `p`. -/
theorem extendRight_left {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b t : ℝ}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    {j : ℕ} (hj : j ≤ p) (ht : t ≤ a) :
    iteratedDeriv j (extendRight p f Q a b) t = iteratedDeriv j f t := by
  rw [extendRight_iteratedDeriv hf hab hjet hj, piecewise_eq_of_mem (Iic a) _ _ ht]

/-- On the appended interval, derivatives are the translated polynomial derivatives. -/
theorem extendRight_interval {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b t : ℝ}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    {j : ℕ} (hj : j ≤ p) (ht : t ∈ Icc a b) :
    iteratedDeriv j (extendRight p f Q a b) t = iteratedDeriv j (fun z => Q.eval z) (t - a) := by
  by_cases hta : t ≤ a
  · have heq : t = a := le_antisymm hta ht.1
    subst t
    rw [extendRight_left hf hab hjet hj le_rfl, sub_self]
    exact hjet j hj
  · rw [extendRight_iteratedDeriv hf hab hjet hj, piecewise_eq_of_notMem (Iic a) _ _ hta,
      intervalTail_left p Q hj (sub_le_sub_right ht.2 a)]

/-- Appending a matching interval preserves a common highest derivative Lipschitz constant. -/
theorem extendRight_lipschitz_top {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b : ℝ} {L : NNReal}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    (hLf : LipschitzWith L (iteratedDeriv p f))
    (hLQ : LipschitzOnWith L (iteratedDeriv p (fun t => Q.eval t)) (Icc 0 (b - a))) :
    LipschitzWith L (iteratedDeriv p (extendRight p f Q a b)) := by
  rw [extendRight_iteratedDeriv hf hab hjet le_rfl, ← lipschitzOnWith_univ]
  have hm : iteratedDeriv p f a = iteratedDeriv p (intervalTail p Q (b - a)) (a - a) := by
    have hh := extendRight_matching hab hjet p le_rfl
    simpa only [iteratedDeriv_comp_sub_const p (intervalTail p Q (b - a)) a] using hh
  apply LipschitzOnWith.piecewise_Iic _ _ (mem_univ a) hm
  · simpa only [univ_inter] using
      (lipschitzOnWith_univ.mpr hLf).mono (show Iic a ⊆ univ from subset_univ _)
  · simp only [univ_inter]
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro x hx y hy
    have hQ := intervalTail_lipschitzOn_top p Q (sub_nonneg.mpr hab) hLQ
    have hx' : x - a ∈ Ici (0 : ℝ) := by simpa only [mem_Ici] using sub_nonneg.mpr hx
    have hy' : y - a ∈ Ici (0 : ℝ) := by simpa only [mem_Ici] using sub_nonneg.mpr hy
    have hh := hQ.norm_sub_le hx' hy'
    simpa only [sub_sub_sub_cancel_right] using hh

/-- An initial Taylor polynomial depends only on the jet through order `p`. -/
theorem initialPolynomial_congr {p : ℕ} {a b : ℕ → ℝ} (h : ∀ j ≤ p, a j = b j) :
    initialPolynomial p a = initialPolynomial p b := by
  apply jetPoly_congr
  intro j hj
  rw [h j (by omega)]

/-- A jet with zero positive-order entries gives a constant Taylor polynomial. -/
theorem initialPolynomial_of_flat {p : ℕ} {a : ℕ → ℝ}
    (h : ∀ j, 1 ≤ j → j ≤ p → a j = 0) : initialPolynomial p a = C (a 0) := by
  unfold initialPolynomial jetPoly
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    simp only [h j (by omega) (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj),
      zero_div, C_0, zero_mul]
  · simp

/-- Taylor tails agree when their jets agree through order `p`. -/
theorem taylorTail_congr {p : ℕ} {a b : ℕ → ℝ} (h : ∀ j ≤ p, a j = b j) (c : ℝ) :
    taylorTail p a c = taylorTail p b c := by
  funext t
  unfold taylorTail
  rw [initialPolynomial_congr h]

/-- A flat jet gives a constant tail on the whole line. -/
theorem taylorTail_of_flat {p : ℕ} {a : ℕ → ℝ}
    (h : ∀ j, 1 ≤ j → j ≤ p → a j = 0) (c : ℝ) :
    taylorTail p a c = fun _ => a 0 := by
  funext t
  simp only [taylorTail, initialPolynomial_of_flat h, eval_C]

/-- Every derivative of a Taylor tail is an evaluated polynomial derivative. -/
theorem taylorTail_iteratedDeriv (p : ℕ) (a : ℕ → ℝ) (b : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (taylorTail p a b) t =
      (derivative^[j] (initialPolynomial p a)).eval (t - b) := by
  unfold taylorTail
  rw [iteratedDeriv_comp_sub_const j (fun z => (initialPolynomial p a).eval z) b,
    Polynomial.iteratedDeriv_eval]

/-- After an appended interval, every derivative agrees with its terminal Taylor tail. -/
theorem extendRight_tail {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b t : ℝ}
    (hf : ContDiff ℝ p f) (hab : a < b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    {j : ℕ} (hj : j ≤ p) (ht : b ≤ t) :
    iteratedDeriv j (extendRight p f Q a b) t =
      iteratedDeriv j
        (taylorTail p (fun i => iteratedDeriv i (fun z => Q.eval z) (b - a)) b) t := by
  rw [extendRight_iteratedDeriv hf hab.le hjet hj,
    piecewise_eq_of_notMem (Iic a) _ _ (not_le_of_gt (hab.trans_le ht)),
    intervalTail_right p Q hj (sub_le_sub_right ht a),
    taylorTail_iteratedDeriv, taylorTail_iteratedDeriv]
  congr 1
  ring

/-- A finite increasing chain of polynomial intervals with matching jets, a common
highest derivative Lipschitz constant, and common bounds on all lower derivatives. -/
structure PolynomialChain (p n : ℕ) (x : ℕ → ℝ) (jets : ℕ → ℕ → ℝ)
    (Q : ℕ → ℝ[X]) (L : NNReal) (B : ℝ) : Prop where
  increasing : ∀ i j, i < j → j ≤ n → x i < x j
  left_jet : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (fun t => (Q k).eval t) 0 = jets k j
  right_jet : ∀ k < n, ∀ j ≤ p,
    iteratedDeriv j (fun t => (Q k).eval t) (x (k + 1) - x k) = jets (k + 1) j
  lipschitz : ∀ k < n, LipschitzOnWith L (iteratedDeriv p (fun t => (Q k).eval t))
    (Icc 0 (x (k + 1) - x k))
  bound : ∀ k < n, ∀ j ≤ p, ∀ t ∈ Icc 0 (x (k + 1) - x k),
    |iteratedDeriv j (fun z => (Q k).eval z) t| ≤ B

/-- Starting from a matching seed, glue every interval in a finite chain. The result
retains the prescribed jets, the prefix bounds, and the terminal Taylor tail. -/
theorem PolynomialChain.exists_prefix {p n : ℕ} {x : ℕ → ℝ} {jets : ℕ → ℕ → ℝ}
    {Q : ℕ → ℝ[X]} {L : NNReal} {B : ℝ}
    (h : PolynomialChain p n x jets Q L B) (seed : ℝ → ℝ)
    (hseed : ContDiff ℝ p seed) (hLseed : LipschitzWith L (iteratedDeriv p seed))
    (hseedj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j)
    (hseedb : ∀ j ≤ p, ∀ t ≤ x 0, |iteratedDeriv j seed t| ≤ B)
    (hseedt : ∀ j ≤ p, ∀ t, x 0 ≤ t → iteratedDeriv j seed t =
      iteratedDeriv j (taylorTail p (jets 0) (x 0)) t) :
    ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
      (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = jets k j) ∧
      (∀ j ≤ p, ∀ t ≤ x n, |iteratedDeriv j f t| ≤ B) ∧
      (∀ j ≤ p, ∀ t, x n ≤ t → iteratedDeriv j f t =
        iteratedDeriv j (taylorTail p (jets n) (x n)) t) := by
  induction n with
  | zero =>
    refine ⟨seed, hseed, hLseed, ?_, hseedb, hseedt⟩
    intro k hk j hj
    have hk0 : k = 0 := by omega
    subst k
    exact hseedj j hj
  | succ n ih =>
    have hsmall : PolynomialChain p n x jets Q L B := {
      increasing := fun i j hij hj => h.increasing i j hij (by omega)
      left_jet := fun k hk => h.left_jet k (by omega)
      right_jet := fun k hk => h.right_jet k (by omega)
      lipschitz := fun k hk => h.lipschitz k (by omega)
      bound := fun k hk => h.bound k (by omega) }
    obtain ⟨f,hf,hLf,hfj,hfb,_hft⟩ := ih hsmall
    have hab : x n < x (n + 1) := h.increasing n (n + 1) (by omega) le_rfl
    have hmatch : ∀ j ≤ p, iteratedDeriv j f (x n) =
        iteratedDeriv j (fun t => (Q n).eval t) 0 := by
      intro j hj
      exact (hfj n le_rfl j hj).trans (h.left_jet n (by omega) j hj).symm
    refine ⟨extendRight p f (Q n) (x n) (x (n + 1)),
      extendRight_contDiff hf hab.le hmatch,
      extendRight_lipschitz_top hf hab.le hmatch hLf (h.lipschitz n (by omega)), ?_, ?_, ?_⟩
    · intro k hk j hj
      by_cases hkn : k ≤ n
      · have hx : x k ≤ x n := by
          rcases lt_or_eq_of_le hkn with hlt | rfl
          · exact (h.increasing k n hlt (by omega)).le
          · exact le_rfl
        rw [extendRight_left hf hab.le hmatch hj hx]
        exact hfj k hkn j hj
      · have heq : k = n + 1 := by omega
        subst k
        rw [extendRight_interval hf hab.le hmatch hj ⟨hab.le,le_rfl⟩]
        exact h.right_jet n (by omega) j hj
    · intro j hj t ht
      by_cases hta : t ≤ x n
      · rw [extendRight_left hf hab.le hmatch hj hta]
        exact hfb j hj t hta
      · rw [extendRight_interval hf hab.le hmatch hj ⟨(lt_of_not_ge hta).le,ht⟩]
        exact h.bound n (by omega) j hj (t - x n)
          ⟨sub_nonneg.mpr (lt_of_not_ge hta).le, sub_le_sub_right ht (x n)⟩
    · intro j hj t ht
      rw [extendRight_tail hf hab hmatch hj ht,
        taylorTail_congr (h.right_jet n (by omega)) (x (n + 1))]

/-- Uniform bounds on a prefix and an appended interval give a bound on the enlarged prefix. -/
theorem extendRight_bound_prefix {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b : ℝ}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    {B : ℝ} (hfB : ∀ j ≤ p, ∀ t ≤ a, |iteratedDeriv j f t| ≤ B)
    (hQB : ∀ j ≤ p, ∀ t ∈ Icc 0 (b - a), |iteratedDeriv j (fun z => Q.eval z) t| ≤ B) :
    ∀ j ≤ p, ∀ t ≤ b, |iteratedDeriv j (extendRight p f Q a b) t| ≤ B := by
  intro j hj t ht
  by_cases hta : t ≤ a
  · rw [extendRight_left hf hab hjet hj hta]
    exact hfB j hj t hta
  · rw [extendRight_interval hf hab hjet hj ⟨(lt_of_not_ge hta).le,ht⟩]
    exact hQB j hj (t-a) ⟨sub_nonneg.mpr (lt_of_not_ge hta).le, sub_le_sub_right ht a⟩

/-- Two exterior polynomial transitions with flat outer jets turn a finite chain
into a globally bounded `C^p` interpolant with the same highest derivative Lipschitz constant. -/
theorem PolynomialChain.exists_global {p n : ℕ} {x : ℕ → ℝ}
    {jets : ℕ → ℕ → ℝ} {Q : ℕ → ℝ[X]} {L : NNReal} {B W : ℝ}
    (hB : 0 ≤ B) (hW : 0 < W) (h : PolynomialChain p n x jets Q L B)
    (P R : ℝ[X])
    (hP0 : ∀ j ≤ p, iteratedDeriv j (fun t => P.eval t) 0 =
      if j = 0 then jets 0 0 else 0)
    (hP1 : ∀ j ≤ p, iteratedDeriv j (fun t => P.eval t) W = jets 0 j)
    (hR0 : ∀ j ≤ p, iteratedDeriv j (fun t => R.eval t) 0 = jets n j)
    (hR1 : ∀ j ≤ p, iteratedDeriv j (fun t => R.eval t) W =
      if j = 0 then jets n 0 else 0)
    (hPL : LipschitzOnWith L (iteratedDeriv p (fun t => P.eval t)) (Icc 0 W))
    (hRL : LipschitzOnWith L (iteratedDeriv p (fun t => R.eval t)) (Icc 0 W))
    (hPB : ∀ j ≤ p, ∀ t ∈ Icc 0 W, |iteratedDeriv j (fun z => P.eval z) t| ≤ B)
    (hRB : ∀ j ≤ p, ∀ t ∈ Icc 0 W, |iteratedDeriv j (fun z => R.eval z) t| ≤ B) :
    ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
      (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = jets k j) ∧
      (∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  let seed := extendRight p (fun _ => jets 0 0) P (x 0-W) (x 0)
  have ha : x 0-W < x 0 := by linarith
  have hm : ∀ j ≤ p, iteratedDeriv j (fun _ : ℝ => jets 0 0) (x 0-W) =
      iteratedDeriv j (fun t => P.eval t) 0 := by
    intro j hj
    simpa only [iteratedDeriv_const] using (hP0 j hj).symm
  have hs : ContDiff ℝ p seed := extendRight_contDiff contDiff_const ha.le hm
  have hsL : LipschitzWith L (iteratedDeriv p seed) := by
    apply extendRight_lipschitz_top contDiff_const ha.le hm
    · apply lipschitzWith_iff_norm_sub_le.mpr
      intro u v
      simp only [iteratedDeriv_const, sub_self, norm_zero]
      positivity
    · simpa only [sub_sub_cancel] using hPL
  have hsj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j := by
    intro j hj
    rw [extendRight_interval contDiff_const ha.le hm hj ⟨ha.le,le_rfl⟩]
    simpa only [sub_sub_cancel] using hP1 j hj
  have hsb : ∀ j ≤ p, ∀ t ≤ x 0, |iteratedDeriv j seed t| ≤ B := by
    apply extendRight_bound_prefix contDiff_const ha.le hm
    · intro j hj t _ht
      by_cases hj0 : j = 0
      · subst j
        have hh := hPB 0 (by omega) 0 ⟨by simp,hW.le⟩
        simpa only [iteratedDeriv_zero, hP0 0 (by omega), ite_true] using hh
      · simpa only [iteratedDeriv_const, ite_eq_right hj0, abs_zero] using hB
    · simpa only [sub_sub_cancel] using hPB
  have hst : ∀ j ≤ p, ∀ t, x 0 ≤ t → iteratedDeriv j seed t =
      iteratedDeriv j (taylorTail p (jets 0) (x 0)) t := by
    intro j hj t ht
    rw [extendRight_tail contDiff_const ha hm hj ht]
    have hh : ∀ i ≤ p, iteratedDeriv i (fun z => P.eval z) (x 0-(x 0-W)) = jets 0 i := by
      simpa only [sub_sub_cancel] using hP1
    rw [taylorTail_congr hh]
  obtain ⟨f,hf,hLf,hfj,hfb,_hft⟩ := h.exists_prefix seed hs hsL hsj hsb hst
  have hb : x n < x n+W := by linarith
  have hmatch : ∀ j ≤ p, iteratedDeriv j f (x n) = iteratedDeriv j (fun t => R.eval t) 0 := by
    intro j hj
    exact (hfj n le_rfl j hj).trans (hR0 j hj).symm
  refine ⟨extendRight p f R (x n) (x n+W), extendRight_contDiff hf hb.le hmatch,
    extendRight_lipschitz_top hf hb.le hmatch hLf (by simpa using hRL), ?_, ?_⟩
  · intro k hk j hj
    have hx : x k ≤ x n := by
      rcases lt_or_eq_of_le hk with hkn | rfl
      · exact (h.increasing k n hkn le_rfl).le
      · exact le_rfl
    rw [extendRight_left hf hb.le hmatch hj hx]
    exact hfj k hk j hj
  · intro j hj t
    by_cases ht : t ≤ x n+W
    · apply extendRight_bound_prefix hf hb.le hmatch hfb (by simpa using hRB) j hj t ht
    · rw [extendRight_tail hf hb hmatch hj (lt_of_not_ge ht).le]
      have hflat : ∀ i, 1 ≤ i → i ≤ p →
          iteratedDeriv i (fun z => R.eval z) (x n+W-x n) = 0 := by
        intro i hi hip
        simpa only [add_sub_cancel_left, ite_eq_right (by omega : i ≠ 0)] using hR1 i hip
      rw [taylorTail_of_flat hflat]
      by_cases hj0 : j = 0
      · subst j
        have hh := hRB 0 (by omega) W ⟨hW.le,le_rfl⟩
        simpa only [iteratedDeriv_zero, add_sub_cancel_left] using hh
      · simpa only [iteratedDeriv_const, ite_eq_right hj0, abs_zero] using hB

/-- A finite collection of polynomial derivatives is bounded on a finite interval. -/
theorem polynomial_derivatives_bounded (p : ℕ) (Q : ℝ[X]) (s : ℝ) :
    ∃ B > 0, ∀ j ≤ p, ∀ t ∈ Icc 0 s, |iteratedDeriv j Q.eval t| ≤ B := by
  let G : ℝ → Fin (p+1) → ℝ := fun t j => iteratedDeriv j Q.eval t
  have hG : Continuous G := by
    apply continuous_pi
    intro j
    simp only [G, Polynomial.iteratedDeriv_eval]
    exact ((polynomial_contDiff (derivative^[j.val] Q) 0).continuous)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max C 0+1, by positivity, ?_⟩
  intro j hj t ht
  have hh : |iteratedDeriv j Q.eval t| ≤ ‖G t‖ := by
    simpa only [G, Real.norm_eq_abs] using norm_le_pi_norm (G t) (⟨j,by omega⟩ : Fin (p+1))
  exact hh.trans ((hC t ht).trans (by linarith [le_max_left C (0:ℝ)]))

/-- Every finite family of polynomial intervals has a common bound on its derivatives
through any fixed finite order. -/
theorem finite_polynomial_derivatives_bounded (p n : ℕ) (Q : ℕ → ℝ[X]) (s : ℕ → ℝ) :
    ∃ B > 0, ∀ k < n, ∀ j ≤ p, ∀ t ∈ Icc 0 (s k),
      |iteratedDeriv j (Q k).eval t| ≤ B := by
  choose C hCpos hC using fun k => polynomial_derivatives_bounded p (Q k) (s k)
  refine ⟨(∑ k ∈ Finset.range n, C k)+1, ?_, ?_⟩
  · have : 0 ≤ ∑ k ∈ Finset.range n, C k := Finset.sum_nonneg (fun k _ => (hCpos k).le)
    linarith
  · intro k hk j hj t ht
    have hle : C k ≤ ∑ i ∈ Finset.range n, C i :=
      Finset.single_le_sum (fun i _ => (hCpos i).le) (by simpa using hk)
    exact (hC k j hj t ht).trans (by linarith)

/-- The derivative jet of a constant function. -/
noncomputable def flatJet (a : ℝ) (j : ℕ) : ℝ := if j = 0 then a else 0

/-- The initial Taylor polynomial of a constant jet is the same constant. -/
@[simp] theorem initialPolynomial_flatJet (p : ℕ) (a : ℝ) :
    initialPolynomial p (flatJet a) = C a := by
  rw [initialPolynomial_of_flat]
  · simp [flatJet]
  · intro j hj _hjp
    simp [flatJet, show j ≠ 0 by omega]

/-- A sufficiently wide interval from a flat jet satisfies the normalized
endpoint residual bound. -/
theorem flatJet_residual {p : ℕ} {a : ℕ → ℝ} {W κ : ℝ}
    (hW : 1 ≤ W) (hκ : 1 ≤ κ) (ha : ∀ j ≤ p, |a j| ≤ κ * W) :
    ∀ j ≤ p, |a j - (derivative^[j] (initialPolynomial p (flatJet (a 0)))).eval W| ≤
      κ * W^(p-j+1) := by
  intro j hj
  rw [initialPolynomial_flatJet]
  by_cases hj0 : j = 0
  · subst j
    simp only [Function.iterate_zero, id_eq, eval_C, sub_self, abs_zero]
    positivity
  · have hz : derivative^[j] (C (a 0)) = 0 := iterate_derivative_C (by omega)
    rw [hz, eval_zero, sub_zero]
    exact (ha j hj).trans (mul_le_mul_of_nonneg_left
      (le_self_pow₀ hW (by omega)) (by linarith))

/-- Uniform Hermite interpolation on the whole real line. The constants precede
all interpolation data, including the number and positions of the nodes. -/
theorem exists_uniform_interpolant (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ B > 0, ∀ n : ℕ, 0 < n →
      ∀ x : ℕ → ℝ, ∀ a : ℕ → ℕ → ℝ,
      (∀ i j, i < j → j ≤ n → x i < x j) →
      (∀ k < n, ∀ j ≤ p,
        |a (k+1) j - (derivative^[j] (initialPolynomial p (a k))).eval (x (k+1)-x k)| ≤
          κ * (x (k+1)-x k)^(p-j+1)) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv p f) ∧
        (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = a k j) ∧
        (((∀ k < n, ∀ j ≤ p, |a k j| ≤ κ) ∧ (∀ k < n, x (k+1)-x k ≤ κ)) →
          ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  classical
  obtain ⟨L₀,hL₀,B₀,hB₀,H₀⟩ := endpointPolynomial_uniform_bounds p κ hκ
  let K := 1+κ+B₀+(p+1:ℝ)*(κ+B₀)
  have hprod : 0 ≤ (p+1:ℝ)*(κ+B₀) := by positivity
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hκK : κ ≤ K := by dsimp [K]; linarith
  have hBK : B₀ ≤ K := by dsimp [K]; linarith
  obtain ⟨L,hL,B,hB,H⟩ := endpointPolynomial_uniform_bounds p K (by linarith)
  refine ⟨L,hL,B,hB,?_⟩
  intro n hn x a hx hres
  let good : Prop := (∀ k < n, ∀ j ≤ p, |a k j| ≤ κ) ∧
    (∀ k < n, x (k+1)-x k ≤ κ)
  have hs : ∀ k < n, 0 < x (k+1)-x k := by
    intro k hk
    exact sub_pos.mpr (hx k (k+1) (by omega) (by omega))
  have hlast : good → ∀ j ≤ p, |a n j| ≤ B₀ := by
    intro hg j hj
    have hn1 : n-1 < n := by omega
    have hn2 : n-1+1 = n := by omega
    have hq := (H₀ _ (hs (n-1) hn1) (a (n-1)) (a n)
      (by simpa only [hn2] using hres (n-1) hn1)).2
      (hg.1 (n-1) hn1) (by simpa only [hn2] using hg.2 (n-1) hn1)
      j hj (x n-x (n-1))
      ⟨(by simpa only [hn2] using (hs (n-1) hn1).le),
        (by simpa only [hn2] using
          (le_rfl : x n-x (n-1) ≤ x n-x (n-1)))⟩
    simp only [hn2] at hq
    have he := endpointPolynomial_right (p := p) (s := x n-x (n-1))
      (by simpa only [hn2] using (hs (n-1) hn1).ne') (a (n-1)) (a n) hj
    simpa only [Polynomial.iteratedDeriv_eval, he] using hq
  let W := 1+∑ j ∈ Finset.range (p+1), (|a 0 j|+|a n j|)
  have hW : 1 ≤ W := by
    dsimp [W]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by positivity))
  have hWpos : 0 < W := by linarith
  have hWa : ∀ j ≤ p, |a 0 j| ≤ W ∧ |a n j| ≤ W := by
    intro j hj
    have ht : |a 0 j|+|a n j| ≤ ∑ i ∈ Finset.range (p+1), (|a 0 i|+|a n i|) :=
      Finset.single_le_sum (fun (i : ℕ) (_hi : i ∈ Finset.range (p+1)) =>
        add_nonneg (abs_nonneg (a 0 i)) (abs_nonneg (a n i)))
        (by simpa using (show j < p+1 by omega))
    constructor <;> dsimp [W] <;> linarith [abs_nonneg (a 0 j),abs_nonneg (a n j)]
  have hWK : good → W ≤ K := by
    intro hg
    have hsum : ∑ j ∈ Finset.range (p+1), (|a 0 j|+|a n j|) ≤
        (p+1:ℝ)*(κ+B₀) := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (p+1), (κ+B₀) := Finset.sum_le_sum (fun j hj =>
          add_le_add (hg.1 0 hn j (by simpa using hj)) (hlast hg j (by simpa using hj)))
        _ = _ := by simp; ring
    dsimp [W,K]
    linarith
  let P := endpointPolynomial p W (flatJet (a 0 0)) (a 0)
  let Q : ℕ → ℝ[X] := fun k => endpointPolynomial p (x (k+1)-x k) (a k) (a (k+1))
  let V := endpointPolynomial p W (flatJet (a n 0)) (fun j => (-1:ℝ)^j*a n j)
  let R := reflectPolynomial V W
  let L' : NNReal := ⟨L,hL.le⟩
  have hPa : ∀ j ≤ p, |a 0 j| ≤ K*W := by
    intro j hj
    exact (hWa j hj).1.trans (le_mul_of_one_le_left hWpos.le hK)
  have hVa : ∀ j ≤ p, |(-1:ℝ)^j*a n j| ≤ K*W := by
    intro j hj
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      (hWa j hj).2.trans (le_mul_of_one_le_left hWpos.le hK)
  have hPest := H W hWpos (flatJet (a 0 0)) (a 0) (flatJet_residual hW hK hPa)
  have hVest := H W hWpos (flatJet (a n 0)) (fun j => (-1:ℝ)^j*a n j)
    (by simpa only [pow_zero, one_mul] using flatJet_residual hW hK hVa)
  have hQest : ∀ k < n,
      (∀ u ∈ Icc 0 (x (k+1)-x k), ∀ v ∈ Icc 0 (x (k+1)-x k),
        |iteratedDeriv p (Q k).eval u - iteratedDeriv p (Q k).eval v| ≤ L*|u-v|) ∧
      ((∀ j ≤ p, |a k j| ≤ K) → x (k+1)-x k ≤ K → ∀ j ≤ p,
        ∀ t ∈ Icc 0 (x (k+1)-x k), |iteratedDeriv j (Q k).eval t| ≤ B) := by
    intro k hk
    apply H _ (hs k hk)
    intro j hj
    exact (hres k hk j hj).trans (mul_le_mul_of_nonneg_right hκK (pow_nonneg (hs k hk).le _))
  have hP0 : ∀ j ≤ p, iteratedDeriv j P.eval 0 = if j=0 then a 0 0 else 0 := by
    intro j hj
    simpa only [P, flatJet, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_zero hWpos.ne' (flatJet (a 0 0)) (a 0) hj
  have hP1 : ∀ j ≤ p, iteratedDeriv j P.eval W = a 0 j := by
    intro j hj
    simpa only [P, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_right hWpos.ne' (flatJet (a 0 0)) (a 0) hj
  have hV0 : ∀ j ≤ p, iteratedDeriv j V.eval 0 = if j=0 then a n 0 else 0 := by
    intro j hj
    simpa only [V, flatJet, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_zero hWpos.ne' (flatJet (a n 0)) (fun j => (-1:ℝ)^j*a n j) hj
  have hV1 : ∀ j ≤ p, iteratedDeriv j V.eval W = (-1:ℝ)^j*a n j := by
    intro j hj
    simpa only [V, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_right hWpos.ne' (flatJet (a n 0)) (fun j => (-1:ℝ)^j*a n j) hj
  have hRjets := reflectPolynomial_endpoint_jets hV0 hV1
  have hPL : LipschitzOnWith L' (iteratedDeriv p P.eval) (Icc 0 W) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro u hu v hv
    change ‖iteratedDeriv p P.eval u - iteratedDeriv p P.eval v‖ ≤ L*‖u-v‖
    simpa only [Real.norm_eq_abs] using hPest.1 u hu v hv
  have hVL : LipschitzOnWith L' (iteratedDeriv p V.eval) (Icc 0 W) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro u hu v hv
    change ‖iteratedDeriv p V.eval u - iteratedDeriv p V.eval v‖ ≤ L*‖u-v‖
    simpa only [Real.norm_eq_abs] using hVest.1 u hu v hv
  have hRL : LipschitzOnWith L' (iteratedDeriv p R.eval) (Icc 0 W) :=
    iteratedDeriv_reflectPolynomial_lipschitzOnWith hVL
  have hQL : ∀ k < n, LipschitzOnWith L' (iteratedDeriv p (Q k).eval)
      (Icc 0 (x (k+1)-x k)) := by
    intro k hk
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro u hu v hv
    change ‖iteratedDeriv p (Q k).eval u - iteratedDeriv p (Q k).eval v‖ ≤ L*‖u-v‖
    simpa only [Real.norm_eq_abs] using (hQest k hk).1 u hu v hv
  have hQ0 : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (Q k).eval 0 = a k j := by
    intro k hk j hj
    simpa only [Q, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_zero (hs k hk).ne' (a k) (a (k+1)) hj
  have hQ1 : ∀ k < n, ∀ j ≤ p,
      iteratedDeriv j (Q k).eval (x (k+1)-x k) = a (k+1) j := by
    intro k hk j hj
    simpa only [Q, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_right (hs k hk).ne' (a k) (a (k+1)) hj
  have hgood : good →
      (∀ k < n, ∀ j ≤ p, ∀ t ∈ Icc 0 (x (k+1)-x k),
        |iteratedDeriv j (Q k).eval t| ≤ B) ∧
      (∀ j ≤ p, ∀ t ∈ Icc 0 W, |iteratedDeriv j P.eval t| ≤ B) ∧
      (∀ j ≤ p, ∀ t ∈ Icc 0 W, |iteratedDeriv j R.eval t| ≤ B) := by
    intro hg
    refine ⟨?_,?_,?_⟩
    · intro k hk
      exact (hQest k hk).2 (fun j hj => (hg.1 k hk j hj).trans hκK) ((hg.2 k hk).trans hκK)
    · apply hPest.2 _ (hWK hg)
      intro j hj
      by_cases hj0 : j=0
      · subst j; simpa only [flatJet, ite_true] using (hg.1 0 hn 0 (by omega)).trans hκK
      · simpa only [flatJet, ite_eq_right hj0, abs_zero] using (show 0 ≤ K by linarith)
    · intro j hj
      apply abs_iteratedDeriv_reflectPolynomial_le
      apply hVest.2 _ (hWK hg) j hj
      intro i hi
      by_cases hi0 : i=0
      · subst i; simpa only [flatJet, ite_true] using (hlast hg 0 (by omega)).trans hBK
      · simpa only [flatJet, ite_eq_right hi0, abs_zero] using (show 0 ≤ K by linarith)
  by_cases hg : good
  · obtain ⟨hQB,hPB,hRB⟩ := hgood hg
    have hc : PolynomialChain p n x a Q L' B := ⟨hx,hQ0,hQ1,hQL,hQB⟩
    obtain ⟨f,hf,hLf,hfj,hfb⟩ := hc.exists_global hB.le hWpos P R hP0 hP1
      hRjets.1 hRjets.2 hPL hRL hPB hRB
    exact ⟨f,hf,hLf,hfj,fun _ => hfb⟩
  · obtain ⟨C,hC,hQC⟩ := finite_polynomial_derivatives_bounded p n Q
      (fun k => x (k+1)-x k)
    obtain ⟨D,hD,hPD⟩ := polynomial_derivatives_bounded p P W
    obtain ⟨E,hE,hRE⟩ := polynomial_derivatives_bounded p R W
    let B' := max C (max D E)
    have hc : PolynomialChain p n x a Q L' B' := {
      increasing := hx
      left_jet := hQ0
      right_jet := hQ1
      lipschitz := hQL
      bound := fun k hk j hj t ht => (hQC k hk j hj t ht).trans (le_max_left _ _) }
    obtain ⟨f,hf,hLf,hfj,_hfb⟩ := hc.exists_global
      (hC.le.trans (le_max_left _ _)) hWpos P R hP0 hP1 hRjets.1 hRjets.2 hPL hRL
      (fun j hj t ht => (hPD j hj t ht).trans ((le_max_left D E).trans (le_max_right _ _)))
      (fun j hj t ht => (hRE j hj t ht).trans ((le_max_right D E).trans (le_max_right _ _)))
    exact ⟨f,hf,hLf,hfj,fun h => (hg h).elim⟩

end Hermite
