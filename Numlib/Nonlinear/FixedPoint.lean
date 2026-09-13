import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Numlib.Stationary.Basic

/-!
# Fixed-point iterations

Glue around Mathlib's `ContractingWith` for the Banach fixed-point theorem with the a priori, a
posteriori and linear-rate bounds ([han2009theoretical] Thm 5.1.3, estimates (5.1.4)–(5.1.6);
[kress1998numerical] Thm 3.45–3.46), the `T^m`-contraction variant ([han2009theoretical] Exercise
5.1.2, [kress1998numerical] Problem 3.17), the derivative criterion `sup ‖T'‖ < 1`
([kress1998numerical] Thm 6.8; [han2009theoretical] give the scalar case in the remark following
their Thm 5.2.1), and Zarantonello's theorem for strongly monotone Lipschitz maps on Hilbert spaces
([han2009theoretical] Thm 5.1.4, the nonlinear Lax–Milgram).

Strong monotonicity is the bundle `IsStronglyMonotoneWith 𝕜 A c`, together with its restriction
`IsStronglyMonotoneOnWith 𝕜 A s c` to a set; the Zarantonello theorems take it, and so does the
existence theory for variational inequalities in `Numlib/Variational/Inequality/Basic.lean`.

The scalar and local theory of [quarteroni2000numerical] §6.3 sits in the sections `Interval` and
`Ostrowski`: the fixed-point theorem on `[a, b]` from a derivative bound `|φ'| ≤ K < 1` (Theorem
6.1), Ostrowski's theorem — local convergence from `‖φ'(α)‖ < 1` at the fixed point alone, in a
normed space and on `ℝ` (Property 6.3), its converse `|φ'(α)| > 1 ⇒` no convergence (Remark 6.2),
and the power form `∃ m, ‖φ'(α)^m‖ < 1` with its ball-invariance clause, which is what Property 7.3
(`ρ(φ'(α)) < 1` in `ℝⁿ`) reduces to. The order of convergence of these iterations is the subject of
`Numlib/Nonlinear/Order.lean`.
-/

open Filter Topology

section Metric

variable {α : Type*} [MetricSpace α]

namespace ContractingWith

variable {K : NNReal} {f : α → α}

/-- Linear rate of convergence: `dist (f^[n+1] x) x* ≤ K dist (f^[n] x) x*`, so the error is cut by
the factor `K` at every step ([han2009theoretical], (5.1.6)). -/
theorem dist_iterate_succ_fixedPoint_le [Nonempty α] [CompleteSpace α] (hf : ContractingWith K f)
    (x : α) (n : ℕ) :
    dist (f^[n + 1] x) (fixedPoint f hf) ≤ K * dist (f^[n] x) (fixedPoint f hf) := by
  rw [Function.iterate_succ_apply']
  have h := hf.dist_le_mul (f^[n] x) (fixedPoint f hf)
  rwa [hf.fixedPoint_isFixedPt] at h

/-- The fixed point of a contraction is the unique solution of `f x = x`. -/
theorem existsUnique_eq_self [Nonempty α] [CompleteSpace α] (hf : ContractingWith K f) :
    ∃! x, f x = x :=
  ⟨fixedPoint f hf, hf.fixedPoint_isFixedPt, fun _ hy => hf.fixedPoint_unique hy⟩

end ContractingWith

/-- Geometric decay of the iterates towards a point `x'` inside an invariant set, from the
one-sided contraction `dist (f x) x' ≤ K dist x x'` on the set: `dist (f^[n] x₀) x' ≤ K^n dist x₀
x'`. Neither `x' ∈ s` nor `f x' = x'` is needed; this is the estimate behind the Banach a priori
bound and behind Ostrowski's theorem, where the contraction is only known towards the fixed
point. -/
theorem dist_iterate_le_pow_mul_of_mapsTo {f : α → α} {s : Set α} (hmaps : Set.MapsTo f s s)
    {K : ℝ} (hK0 : 0 ≤ K) {x' : α} (hf : ∀ x ∈ s, dist (f x) x' ≤ K * dist x x') {x₀ : α}
    (hx₀ : x₀ ∈ s) (n : ℕ) : dist (f^[n] x₀) x' ≤ K ^ n * dist x₀ x' := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc dist (f^[n + 1] x₀) x' = dist (f (f^[n] x₀)) x' := by rw [Function.iterate_succ_apply']
      _ ≤ K * dist (f^[n] x₀) x' := hf _ (hmaps.iterate n hx₀)
      _ ≤ K * (K ^ n * dist x₀ x') := by gcongr
      _ = K ^ (n + 1) * dist x₀ x' := by ring

/-- One step controls the distance to a fixed point: `(1 - K) dist x₀ x* ≤ dist (f x₀) x₀`. -/
private theorem one_sub_mul_dist_le {f : α → α} {s : Set α} {K : ℝ}
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) {x' : α} (hx' : x' ∈ s)
    (hfix : f x' = x') {x₀ : α} (hx₀ : x₀ ∈ s) :
    (1 - K) * dist x₀ x' ≤ dist (f x₀) x₀ := by
  have hstep := hf x₀ hx₀ x' hx'
  rw [hfix] at hstep
  have htri : dist x₀ x' ≤ dist x₀ (f x₀) + dist (f x₀) x' := dist_triangle _ _ _
  rw [dist_comm x₀ (f x₀)] at htri
  linarith

/-- Banach fixed point on a closed subset mapped into itself: existence and uniqueness in the set.
This is the setting of [han2009theoretical], Thm 5.1.3, and of [kress1998numerical], Thm 3.45; the
contraction hypothesis is only required on `s`. -/
theorem exists_unique_fixedPoint_of_mapsTo [CompleteSpace α] {f : α → α} {s : Set α}
    (hs : IsClosed s) (hne : s.Nonempty) (hmaps : Set.MapsTo f s s) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < 1) (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    ∃! x, x ∈ s ∧ f x = x := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hcon : ContractingWith K.toNNReal (hmaps.restrict f s s) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [← NNReal.coe_lt_one, Real.coe_toNNReal _ hK0]; exact hK
    · rw [Real.coe_toNNReal _ hK0]; exact hf x x.2 y y.2
  obtain ⟨y, hys, hfy, -, -⟩ :=
    hcon.exists_fixedPoint' hs.isComplete hmaps hx₀ (edist_ne_top _ _)
  refine ⟨y, ⟨hys, hfy⟩, ?_⟩
  rintro z ⟨hzs, hfz⟩
  have hzy : dist z y ≤ K * dist z y := by
    have h := hf z hzs y hys
    rwa [hfz, hfy] at h
  have : dist z y = 0 := le_antisymm (by nlinarith [dist_nonneg (x := z) (y := y)]) dist_nonneg
  exact dist_eq_zero.mp this

-- `hs` is unnecessary once a fixed point `x'` in `s` is supplied: the bound follows from the
-- contraction inequality on `s` alone. It is kept to match the companion existence statement.
set_option linter.unusedVariables false in
/-- A priori bound on a closed invariant subset: `dist (f^[n] x₀) x* ≤ K^n / (1 - K) * dist (f x₀)
x₀`, so the number of iterations needed for a prescribed accuracy can be read off before iterating
([han2009theoretical], (5.1.4); [kress1998numerical], Thm 3.46). -/
theorem dist_iterate_le_of_mapsTo [CompleteSpace α] {f : α → α} {s : Set α} (hs : IsClosed s)
    (hmaps : Set.MapsTo f s s) {K : ℝ} (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) {x' : α} (hx' : x' ∈ s)
    (hfix : f x' = x') {x₀ : α} (hx₀ : x₀ ∈ s) (n : ℕ) :
    dist (f^[n] x₀) x' ≤ K ^ n / (1 - K) * dist (f x₀) x₀ := by
  have h1K : 0 < 1 - K := by linarith
  calc dist (f^[n] x₀) x' ≤ K ^ n * dist x₀ x' :=
        dist_iterate_le_pow_mul_of_mapsTo hmaps hK0
          (fun x hx => by simpa only [hfix] using hf x hx x' hx') hx₀ n
    _ ≤ K ^ n * (dist (f x₀) x₀ / (1 - K)) := by
        gcongr
        rw [le_div_iff₀ h1K, mul_comm]
        exact one_sub_mul_dist_le hf hx' hfix hx₀
    _ = K ^ n / (1 - K) * dist (f x₀) x₀ := by ring

/-- Interleaving: if for each residue `j < m` the subsequence `k ↦ T^[m k + j] x` converges to
`x'`, so does the whole orbit `n ↦ T^[n] x`. -/
theorem tendsto_iterate_of_forall_tendsto_iterate_mul_add {X : Type*} [TopologicalSpace X]
    {T : X → X} {x x' : X} {m : ℕ} (hm : 0 < m)
    (h : ∀ j < m, Tendsto (fun k => T^[m * k + j] x) atTop (𝓝 x')) :
    Tendsto (fun n => T^[n] x) atTop (𝓝 x') := by
  rw [Filter.tendsto_def]
  intro U hU
  have hall : ∀ᶠ k in atTop, ∀ j ∈ Set.Iio m, T^[m * k + j] x ∈ U :=
    (Filter.eventually_all_finite (Set.finite_Iio m)).2 fun j hj => h j hj hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hall
  refine Filter.eventually_atTop.2 ⟨m * N, fun n hn => ?_⟩
  have hdiv : N ≤ n / m := (Nat.le_div_iff_mul_le hm).2 (by rwa [mul_comm])
  have := hN (n / m) hdiv (n % m) (Nat.mod_lt n hm)
  rwa [Nat.div_add_mod] at this

-- Neither the continuity of `T` nor `0 < m` is needed for the conclusion; both are kept because
-- they belong to the textbook statement (Atkinson–Han, *Theoretical Numerical Analysis*,
-- Exercise 5.1.2).
set_option linter.unusedVariables false in
/-- [han2009theoretical], Exercise 5.1.2, and [kress1998numerical], Problem 3.17: a continuous `T`
whose iterate `T^[m]` is a contraction has a unique fixed point, and `T^[n] x → x*` for every `x`.
`T` itself need not be a contraction in any metric.

`[Nonempty α]` was added to the statement: the empty metric space is complete and every self-map of
it is a contraction, so without it the conclusion `∃! x, T x = x` is false. -/
theorem exists_unique_fixedPoint_of_iterate_contractingWith [Nonempty α] [CompleteSpace α]
    {T : α → α} (hT : Continuous T) {m : ℕ} (hm : 0 < m) {K : NNReal}
    (hK : ContractingWith K T^[m]) : ∃! x, T x = x :=
  ⟨hK.fixedPoint T^[m], hK.isFixedPt_fixedPoint_iterate,
    fun _ hy => hK.fixedPoint_unique (Function.IsFixedPt.iterate hy m)⟩

-- Continuity of `T` is again not needed: `T^[m]` already pins the limit down.
set_option linter.unusedVariables false in
/-- Convergence for the `T^[m]`-contraction criterion ([han2009theoretical], Exercise 5.1.2;
[kress1998numerical], Problem 3.17): from every starting point the whole orbit `T^[n] x` converges
to a fixed point of `T` itself, although `T` need be a contraction in no metric.  The orbit splits
into the `m` interleaved subsequences `k ↦ T^[m k + j] x`, each of which iterates the contraction
`T^[m]` and hence converges to its one fixed point; taking the largest of the `m` thresholds makes
the whole orbit converge. -/
theorem tendsto_iterate_of_iterate_contractingWith [CompleteSpace α] {T : α → α}
    (hT : Continuous T) {m : ℕ} (hm : 0 < m) {K : NNReal} (hK : ContractingWith K T^[m]) (x : α) :
    ∃ x', T x' = x' ∧ Tendsto (fun n => T^[n] x) atTop (𝓝 x') := by
  have : Nonempty α := ⟨x⟩
  refine ⟨hK.fixedPoint T^[m], hK.isFixedPt_fixedPoint_iterate, ?_⟩
  -- each of the `m` interleaved subsequences `k ↦ T^[m k + j] x` iterates the contraction `T^[m]`
  refine tendsto_iterate_of_forall_tendsto_iterate_mul_add hm fun j _ => ?_
  refine (hK.tendsto_iterate_fixedPoint (T^[j] x)).congr fun k => ?_
  rw [← Function.iterate_mul, ← Function.iterate_add_apply, add_comm]

end Metric

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative criterion for contractivity: a differentiable self-map of a convex set with `sup
‖T'‖ ≤ q` is `q`-Lipschitz there, hence a contraction when `q < 1`.  This is [kress1998numerical],
Thm 6.8; [han2009theoretical], give the scalar case in the remark following their Thm 5.2.1.
(Mathlib: `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`.) -/
theorem lipschitzOnWith_of_hasFDerivWithinAt {T : E → E} {T' : E → E →L[ℝ] E} {s : Set E}
    (hs : Convex ℝ s) (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) {q : NNReal}
    (hT' : ∀ x ∈ s, ‖T' x‖₊ ≤ q) : LipschitzOnWith q T s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hT hT'

end Derivative

section Interval

/-! ### Scalar fixed-point iterations on an interval

[quarteroni2000numerical] Theorem 6.1: a map of `[a, b]` into itself whose derivative is bounded by
`K < 1` there has a unique fixed point, and every orbit started in the interval converges to it
geometrically. The book asks `φ ∈ C¹[a, b]`; only the derivative bound within the interval is used,
so the hypotheses are `HasDerivWithinAt` on `Icc a b` and `|φ'| ≤ K`. The limit (6.18) of the error
ratios is `tendsto_sub_div_sub_of_hasDerivAt` in `Numlib/Nonlinear/Order.lean`, which needs only
differentiability at the fixed point. -/

variable {φ φ' : ℝ → ℝ} {a b K : ℝ}

/-- The derivative bound `|φ'| ≤ K` on `[a, b]` makes `φ` `K`-Lipschitz there (the mean value
inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`). -/
theorem dist_le_mul_dist_Icc_of_abs_deriv_le
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, dist (φ x) (φ y) ≤ K * dist x y := by
  intro x hx y hy
  rw [dist_comm, dist_comm x, Real.dist_eq, Real.dist_eq, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hφ
    (fun z hz => by simpa [Real.norm_eq_abs] using hK z hz) hx hy

/-- **Existence and uniqueness of the fixed point** ([quarteroni2000numerical] Theorem 6.1): if
`φ` maps `[a, b]` into itself and `|φ'| ≤ K < 1` on `[a, b]`, then `φ` has exactly one fixed point
in `[a, b]`. The Banach fixed-point theorem on the closed interval
(`exists_unique_fixedPoint_of_mapsTo`). -/
theorem exists_unique_fixedPoint_Icc_of_abs_deriv_le (hab : a ≤ b)
    (hmaps : Set.MapsTo φ (Set.Icc a b) (Set.Icc a b))
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) (hK1 : K < 1) :
    ∃! α, α ∈ Set.Icc a b ∧ φ α = α :=
  exists_unique_fixedPoint_of_mapsTo isClosed_Icc (Set.nonempty_Icc.2 hab) hmaps
    (le_trans (abs_nonneg _) (hK a (Set.left_mem_Icc.2 hab))) hK1
    (dist_le_mul_dist_Icc_of_abs_deriv_le hφ hK)

/-- **Geometric convergence on the interval** ([quarteroni2000numerical] Theorem 6.1, the estimate
`|x^{(k)} - α| ≤ K^k |x^{(0)} - α|` of its proof): with `α` the fixed point in `[a, b]`, every orbit
started in `[a, b]` stays there and `|φ^[k] x₀ - α| ≤ K ^ k * |x₀ - α|`. -/
theorem abs_iterate_sub_le_Icc_of_abs_deriv_le
    (hmaps : Set.MapsTo φ (Set.Icc a b) (Set.Icc a b))
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) {α : ℝ} (hα : α ∈ Set.Icc a b) (hfix : φ α = α)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (k : ℕ) :
    φ^[k] x₀ ∈ Set.Icc a b ∧ |φ^[k] x₀ - α| ≤ K ^ k * |x₀ - α| := by
  refine ⟨hmaps.iterate k hx₀, ?_⟩
  rw [← Real.dist_eq, ← Real.dist_eq]
  exact dist_iterate_le_pow_mul_of_mapsTo hmaps (le_trans (abs_nonneg _) (hK α hα))
    (fun x hx => by simpa only [hfix] using dist_le_mul_dist_Icc_of_abs_deriv_le hφ hK x hx α hα)
    hx₀ k

/-- **Global convergence on the interval** ([quarteroni2000numerical] Theorem 6.1): every orbit
started in `[a, b]` converges to the fixed point `α`. -/
theorem tendsto_iterate_Icc_of_abs_deriv_le
    (hmaps : Set.MapsTo φ (Set.Icc a b) (Set.Icc a b))
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) (hK1 : K < 1) {α : ℝ} (hα : α ∈ Set.Icc a b)
    (hfix : φ α = α) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK α hα)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => (abs_iterate_sub_le_Icc_of_abs_deriv_le hmaps hφ hK hα hfix hx₀ k).2) ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const |x₀ - α|

end Interval

section Ostrowski

/-! ### Ostrowski's theorem

Local convergence of a fixed-point iteration from the derivative at the fixed point alone
([quarteroni2000numerical] Property 6.3; [ortega2000iterative] 10.1.3): if `‖φ'(α)‖ < 1` then every
orbit started close enough to `α` converges to `α`, geometrically with any rate `q ∈ (‖φ'(α)‖, 1)`.
Only `HasFDerivAt` at `α` is used — the book's "continuous and differentiable in a neighbourhood"
is more than needed — and the estimate is one-sided, `‖φ x - α‖ ≤ q ‖x - α‖`, so the geometric
decay comes from `dist_iterate_le_pow_mul_of_mapsTo` rather than from a contraction.

The power form `tendsto_iterate_of_exists_norm_pow_fderiv_lt_one` (`‖φ'(α)^m‖ < 1` for some `m`)
is how [quarteroni2000numerical] Property 7.3, `ρ(φ'(α)) < 1` in `ℝⁿ`, is reached: in finite
dimension `ρ(A) < 1` is `∃ m, ‖A^m‖ < 1`, and the theorem for `φ^[m]` (whose derivative at `α` is
`φ'(α)^m` by `HasFDerivAt.iterate`) is interleaved over the `m` residues. This avoids re-norming
`ℝⁿ` with the `ε`-norm, which is only a seminorm and not a structure the mean value inequality can
use. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {φ : E → E} {φ' : E →L[𝕜] E} {α : E}

/-- Near a fixed point `α` where `φ` is differentiable, `‖φ x - α‖ ≤ q ‖x - α‖` for every
`q > ‖φ'(α)‖`: the `o(‖x - α‖)` remainder of the derivative is absorbed into the gap
`q - ‖φ'(α)‖`. -/
theorem eventually_norm_sub_le_mul_of_hasFDerivAt (hα : φ α = α) (hφ : HasFDerivAt φ φ' α)
    {q : ℝ} (hq : ‖φ'‖ < q) : ∀ᶠ x in 𝓝 α, ‖φ x - α‖ ≤ q * ‖x - α‖ := by
  have hlittle := (hasFDerivAt_iff_isLittleO.1 hφ).def (sub_pos.2 hq)
  filter_upwards [hlittle] with x hx
  calc ‖φ x - α‖ = ‖(φ x - φ α - φ' (x - α)) + φ' (x - α)‖ := by rw [hα]; congr 1; abel
    _ ≤ ‖φ x - φ α - φ' (x - α)‖ + ‖φ' (x - α)‖ := norm_add_le _ _
    _ ≤ (q - ‖φ'‖) * ‖x - α‖ + ‖φ'‖ * ‖x - α‖ := add_le_add hx (φ'.le_opNorm _)
    _ = q * ‖x - α‖ := by ring

/-- One-sided contraction on a ball around `α` with factor `q ≤ 1` keeps orbits in the ball and
makes them decay geometrically. -/
theorem norm_iterate_sub_le_pow_mul_of_ball {δ q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ x ∈ Metric.ball α δ, ‖φ x - α‖ ≤ q * ‖x - α‖) {x₀ : E} (hx₀ : x₀ ∈ Metric.ball α δ)
    (k : ℕ) : φ^[k] x₀ ∈ Metric.ball α δ ∧ ‖φ^[k] x₀ - α‖ ≤ q ^ k * ‖x₀ - α‖ := by
  have hmaps : Set.MapsTo φ (Metric.ball α δ) (Metric.ball α δ) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖φ x - α‖ ≤ q * ‖x - α‖ := h x hx
      _ ≤ 1 * ‖x - α‖ := by gcongr
      _ < δ := by rw [one_mul, ← dist_eq_norm]; exact Metric.mem_ball.1 hx
  refine ⟨hmaps.iterate k hx₀, ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact dist_iterate_le_pow_mul_of_mapsTo hmaps hq0
    (fun x hx => by rw [dist_eq_norm, dist_eq_norm]; exact h x hx) hx₀ k

/-- **Ostrowski's theorem with the rate**: if `‖φ'(α)‖ < q < 1`, there is a ball around the fixed
point `α` in which every orbit stays and satisfies `‖φ^[k] x₀ - α‖ ≤ q ^ k * ‖x₀ - α‖`. -/
theorem exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one (hα : φ α = α)
    (hφ : HasFDerivAt φ φ' α) {q : ℝ} (hq : ‖φ'‖ < q) (hq1 : q < 1) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, ∀ k,
      φ^[k] x₀ ∈ Metric.ball α δ ∧ ‖φ^[k] x₀ - α‖ ≤ q ^ k * ‖x₀ - α‖ := by
  obtain ⟨δ, hδ, h⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_norm_sub_le_mul_of_hasFDerivAt hα hφ hq)
  exact ⟨δ, hδ, fun x₀ hx₀ k => norm_iterate_sub_le_pow_mul_of_ball
    (le_trans (norm_nonneg _) hq.le) hq1.le (fun x hx => h (Metric.mem_ball.1 hx)) hx₀ k⟩

/-- **Ostrowski's theorem** ([quarteroni2000numerical] Property 6.3; [ortega2000iterative] 10.1.3)
in a normed space: if `φ α = α`, `φ` is differentiable at `α` and `‖φ'(α)‖ < 1`, then every orbit
started close enough to `α` converges to `α`. Nothing is assumed away from `α`. -/
theorem tendsto_iterate_of_norm_fderiv_lt_one (hα : φ α = α) (hφ : HasFDerivAt φ φ' α)
    (h : ‖φ'‖ < 1) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨q, hq, hq1⟩ := exists_between h
  obtain ⟨δ, hδ, hball⟩ := exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one hα hφ hq hq1
  refine ⟨δ, hδ, fun x₀ hx₀ => ?_⟩
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => (hball x₀ hx₀ k).2) ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (le_trans (norm_nonneg _) hq.le)
    hq1).mul_const ‖x₀ - α‖

/-- **Ostrowski's theorem with a power of the derivative**: if `‖φ'(α)^m‖ < 1` for some `m`, every
orbit started close enough to the fixed point `α` converges to `α`. The theorem for `φ^[m]`, whose
derivative at `α` is `φ'(α)^m`, gives the convergence of the `m` subsequences `k ↦ φ^[m k + j] x₀`
= `φ^[j] (φ^[m]^[k] x₀)` (continuity of `φ^[j]` at `α`), which are then interleaved. In finite
dimension `∃ m, ‖A^m‖ < 1` is `ρ(A) < 1`, so this is [quarteroni2000numerical] Property 7.3. -/
theorem tendsto_iterate_of_exists_norm_pow_fderiv_lt_one (hα : φ α = α)
    (hφ : HasFDerivAt φ φ' α) (h : ∃ m : ℕ, ‖φ' ^ m‖ < 1) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨m, hm⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- `‖1‖ < 1` forces `E` to be trivial, where every orbit is constant
    by_cases hE : Nontrivial E
    · rw [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id] at hm
      exact absurd hm (lt_irrefl 1)
    · have : Subsingleton E := not_nontrivial_iff_subsingleton.1 hE
      refine ⟨1, one_pos, fun x₀ _ => ?_⟩
      rw [show (fun k => φ^[k] x₀) = fun _ => α from funext fun k => Subsingleton.elim _ _]
      exact tendsto_const_nhds
  have hαm : φ^[m] α = α := Function.iterate_fixed hα m
  obtain ⟨δ, hδ, hconv⟩ := tendsto_iterate_of_norm_fderiv_lt_one hαm (hφ.iterate hα m) hm
  refine ⟨δ, hδ, fun x₀ hx₀ => tendsto_iterate_of_forall_tendsto_iterate_mul_add hm0
    fun j _ => ?_⟩
  have hcont : ContinuousAt φ^[j] α := hφ.continuousAt.iterate hα j
  have := hcont.tendsto.comp (hconv x₀ hx₀)
  rw [Function.iterate_fixed hα j] at this
  refine this.congr fun k => ?_
  simp only [Function.comp_apply, ← Function.iterate_mul, ← Function.iterate_add_apply,
    add_comm j]

/-- **The invariance clause of [quarteroni2000numerical] Property 7.3**: under the hypotheses of
`tendsto_iterate_of_exists_norm_pow_fderiv_lt_one`, every neighbourhood `D` of `α` contains a
neighbourhood `S` of `α` such that every orbit started in `S` stays in `D` for all time. The
`φ^[m]`-orbit stays in a small ball by Ostrowski's theorem, and the finitely many intermediate maps
`φ^[j]`, `j < m`, carry a smaller ball into `D` by continuity at `α`. -/
theorem exists_ball_mapsTo_iterate_of_exists_norm_pow_fderiv_lt_one (hα : φ α = α)
    (hφ : HasFDerivAt φ φ' α) (h : ∃ m : ℕ, ‖φ' ^ m‖ < 1) {D : Set E} (hD : D ∈ 𝓝 α) :
    ∃ S ∈ 𝓝 α, S ⊆ D ∧ ∀ x₀ ∈ S, ∀ k, φ^[k] x₀ ∈ D := by
  obtain ⟨m, hm⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · by_cases hE : Nontrivial E
    · rw [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id] at hm
      exact absurd hm (lt_irrefl 1)
    · have : Subsingleton E := not_nontrivial_iff_subsingleton.1 hE
      exact ⟨D, hD, subset_rfl, fun x₀ hx₀ k => by rwa [Subsingleton.elim (φ^[k] x₀) x₀]⟩
  have hαm : φ^[m] α = α := Function.iterate_fixed hα m
  -- a neighbourhood of `α` carried into `D` by every `φ^[j]`, `j < m`
  have hV : ∀ᶠ y in 𝓝 α, ∀ j ∈ Set.Iio m, φ^[j] y ∈ D :=
    (Filter.eventually_all_finite (Set.finite_Iio m)).2 fun j _ =>
      (hφ.continuousAt.iterate hα j).preimage_mem_nhds ((Function.iterate_fixed hα j).symm ▸ hD)
  obtain ⟨ρ, hρ, hρV⟩ := Metric.eventually_nhds_iff.1 hV
  -- the ball in which the `φ^[m]`-orbits stay
  obtain ⟨q, hq, hq1⟩ := exists_between hm
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_norm_sub_le_mul_of_hasFDerivAt hαm (hφ.iterate hα m) hq)
  refine ⟨Metric.ball α (min ρ δ), Metric.ball_mem_nhds α (lt_min hρ hδ), fun y hy => ?_,
    fun x₀ hx₀ k => ?_⟩
  · simpa using hρV (lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_left _ _)) 0 hm0
  · have hstay := (norm_iterate_sub_le_pow_mul_of_ball (le_trans (norm_nonneg _) hq.le) hq1.le
      (fun x hx => hball (lt_of_lt_of_le (Metric.mem_ball.1 hx) (min_le_right _ _))) hx₀
      (k / m)).1
    have := hρV (lt_of_lt_of_le (Metric.mem_ball.1 hstay) (min_le_left _ _)) (k % m)
      (Nat.mod_lt k hm0)
    rwa [← Function.iterate_mul, ← Function.iterate_add_apply, add_comm, Nat.div_add_mod] at this

end Ostrowski

section ScalarOstrowski

variable {φ : ℝ → ℝ} {φ' α : ℝ}

/-- The scalar estimate near a fixed point: `|φ x - α| ≤ q |x - α|` for `q > |φ'(α)|`. -/
theorem eventually_abs_sub_le_mul_of_hasDerivAt (hα : φ α = α) (hφ : HasDerivAt φ φ' α) {q : ℝ}
    (hq : |φ'| < q) : ∀ᶠ x in 𝓝 α, |φ x - α| ≤ q * |x - α| := by
  have := eventually_norm_sub_le_mul_of_hasFDerivAt hα hφ.hasFDerivAt
    (q := q) (by rwa [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs])
  simpa [Real.norm_eq_abs] using this

/-- **Ostrowski's theorem, scalar form, with the rate**: for `|φ'(α)| < q < 1` there is `δ > 0`
such that every orbit started within `δ` of `α` stays there and satisfies
`|φ^[k] x₀ - α| ≤ q ^ k * |x₀ - α|`. -/
theorem exists_ball_abs_iterate_sub_le_of_abs_deriv_lt_one (hα : φ α = α)
    (hφ : HasDerivAt φ φ' α) {q : ℝ} (hq : |φ'| < q) (hq1 : q < 1) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → ∀ k,
      |φ^[k] x₀ - α| < δ ∧ |φ^[k] x₀ - α| ≤ q ^ k * |x₀ - α| := by
  obtain ⟨δ, hδ, h⟩ := exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one hα hφ.hasFDerivAt
    (q := q) (by rwa [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]) hq1
  refine ⟨δ, hδ, fun x₀ hx₀ k => ?_⟩
  have := h x₀ (by rwa [Metric.mem_ball, Real.dist_eq]) k
  simpa [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using this

/-- **Ostrowski's theorem** as printed ([quarteroni2000numerical] Property 6.3): if `φ α = α`,
`φ` is differentiable at `α` and `|φ'(α)| < 1`, then there is `δ > 0` such that every orbit
started within `δ` of `α` converges to `α`. This is the local convergence theorem every one-step
scalar method (chord, Newton, Aitken, Steffensen) is reduced to. -/
theorem tendsto_iterate_of_abs_deriv_lt_one (hα : φ α = α) (hφ : HasDerivAt φ φ' α)
    (h : |φ'| < 1) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨δ, hδ, h⟩ := tendsto_iterate_of_norm_fderiv_lt_one hα hφ.hasFDerivAt
    (by rwa [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs])
  exact ⟨δ, hδ, fun x₀ hx₀ => h x₀ (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- **Repulsion estimate**: near a fixed point `α` with `q < |φ'(α)|`, `q |x - α| ≤ |φ x - α|`. -/
theorem eventually_mul_abs_sub_le_of_hasDerivAt (hα : φ α = α) (hφ : HasDerivAt φ φ' α) {q : ℝ}
    (hq : q < |φ'|) : ∀ᶠ x in 𝓝 α, q * |x - α| ≤ |φ x - α| := by
  have hslope : ∀ᶠ x in 𝓝[≠] α, q < |slope φ α x| :=
    ((hasDerivAt_iff_tendsto_slope.1 hφ).abs).eventually (eventually_gt_nhds hq)
  rw [eventually_nhdsWithin_iff] at hslope
  filter_upwards [hslope] with x hx
  by_cases hxα : x = α
  · simp [hxα, hα]
  · have h := (hx hxα).le
    rw [slope_def_field, hα, abs_div] at h
    have hpos : 0 < |x - α| := abs_pos.2 (sub_ne_zero.2 hxα)
    rwa [le_div_iff₀ hpos] at h

/-- **Remark 6.2 of [quarteroni2000numerical]: repulsion.** If `|φ'(α)| > 1` then no orbit
`x (k + 1) = φ (x k)` that never lands on `α` can converge to `α`: near `α` the error grows,
`|x (k+1) - α| ≥ q |x k - α|` with `q > 1`, so a convergent orbit would have a positive, eventually
increasing error. For `|φ'(α)| = 1` nothing can be said (the book's Example 6.6 shows both
behaviours), and the hypothesis `x k ≠ α` is necessary: an orbit that lands on `α` converges. -/
theorem not_tendsto_iterate_of_one_lt_abs_deriv (hα : φ α = α) (hφ : HasDerivAt φ φ' α)
    (h : 1 < |φ'|) {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α) :
    ¬ Tendsto x atTop (𝓝 α) := by
  intro hlim
  obtain ⟨q, hq1, hq⟩ := exists_between h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hlim.eventually (eventually_mul_abs_sub_le_of_hasDerivAt hα hφ hq))
  have hmono : ∀ k, |x N - α| ≤ |x (N + k) - α| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc |x N - α| ≤ |x (N + k) - α| := ih
        _ ≤ q * |x (N + k) - α| := le_mul_of_one_le_left (abs_nonneg _) hq1.le
        _ ≤ |φ (x (N + k)) - α| := hN _ (Nat.le_add_right N k)
        _ = |x (N + k + 1) - α| := by rw [hx]
  have hpos : 0 < |x N - α| := abs_pos.2 (sub_ne_zero.2 (hne N))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds hpos))
  have := hM (N + M) (Nat.le_add_left M N)
  rw [Real.norm_eq_abs] at this
  exact absurd (hmono M) (not_le.2 this)

end ScalarOstrowski

section StronglyMonotone

/-- **Strong monotonicity.**  `IsStronglyMonotoneWith 𝕜 A c` is `c ‖x - y‖² ≤ re ⟪A x - A y, x - y⟫`
for all `x, y`: the nonlinear counterpart of coercivity of an operator, and the hypothesis of
Zarantonello's theorem and of the existence theory for variational inequalities.  For a linear `A`
it is `LinearMap.IsCoerciveWith` (`LinearMap.IsCoerciveWith.isStronglyMonotoneWith`, in
`Numlib/Variational/Inequality/Basic.lean`).

The scalar field is an explicit argument, as in `inner 𝕜 x y`, because it is not determined by `A :
E → E`. -/
def IsStronglyMonotoneWith (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E → E) (c : ℝ) : Prop :=
  ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x - A y) (x - y))

/-- **Strong monotonicity on a set.**  `IsStronglyMonotoneOnWith 𝕜 A s c` asks for
`c ‖x - y‖² ≤ re ⟪A x - A y, x - y⟫` at points of `s` only.

The existence theory for a variational inequality over `K` never evaluates `A` outside `K`, so this
is the hypothesis it really consumes ([han2009theoretical], Remark 11.3.2), and it is what the
locally Lipschitz form of that theory needs, where the global condition is unavailable. -/
def IsStronglyMonotoneOnWith (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E → E) (s : Set E) (c : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x - A y) (x - y))

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Strong monotonicity only weakens as its constant shrinks. -/
theorem IsStronglyMonotoneWith.mono {A : E → E} {c c' : ℝ} (h : IsStronglyMonotoneWith 𝕜 A c)
    (hc : c' ≤ c) : IsStronglyMonotoneWith 𝕜 A c' := fun x y =>
  (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h x y)

/-- A strongly monotone operator is strongly monotone on every set. -/
theorem IsStronglyMonotoneWith.isStronglyMonotoneOnWith {A : E → E} {c : ℝ}
    (h : IsStronglyMonotoneWith 𝕜 A c) (s : Set E) : IsStronglyMonotoneOnWith 𝕜 A s c :=
  fun x _ y _ => h x y

/-- Strong monotonicity on a set only weakens as its constant shrinks. -/
theorem IsStronglyMonotoneOnWith.mono {A : E → E} {s : Set E} {c c' : ℝ}
    (h : IsStronglyMonotoneOnWith 𝕜 A s c) (hc : c' ≤ c) : IsStronglyMonotoneOnWith 𝕜 A s c' :=
  fun x hx y hy => (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h x hx y hy)

/-- Real spaces: strong monotonicity on a set, without `re`. -/
theorem isStronglyMonotoneOnWith_real_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F → F) (s : Set F) (c : ℝ) :
    IsStronglyMonotoneOnWith ℝ A s c ↔
      ∀ x ∈ s, ∀ y ∈ s, c * ‖x - y‖ ^ 2 ≤ inner ℝ (A x - A y) (x - y) := Iff.rfl

/-- Real spaces: strong monotonicity without `re`. -/
theorem isStronglyMonotoneWith_real_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F → F) (c : ℝ) :
    IsStronglyMonotoneWith ℝ A c ↔ ∀ x y, c * ‖x - y‖ ^ 2 ≤ inner ℝ (A x - A y) (x - y) :=
  Iff.rfl

/-- The identity is strongly monotone with constant `1`. -/
theorem isStronglyMonotoneWith_id : IsStronglyMonotoneWith 𝕜 (fun x : E => x) 1 := fun x y => by
  rw [one_mul, inner_self_eq_norm_sq]

end StronglyMonotone

section Zarantonello

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The algebraic heart of the damped iteration: `‖u - θ w‖² ≤ (1 - 2θc + θ²L²) ‖u‖²` whenever `c
‖u‖² ≤ re ⟪w, u⟫` and `‖w‖ ≤ L ‖u‖`. -/
private theorem norm_sub_smul_sq_le {u w : E} {c L θ : ℝ} (hθ : 0 ≤ θ)
    (hmono : c * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 w u)) (hw : ‖w‖ ≤ L * ‖u‖) :
    ‖u - (θ : 𝕜) • w‖ ^ 2 ≤ (1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖u‖ ^ 2 := by
  have hre : RCLike.re (inner 𝕜 u w) = RCLike.re (inner 𝕜 w u) := by
    rw [← inner_conj_symm w u, RCLike.conj_re]
  have hexp : ‖u - (θ : 𝕜) • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * θ * RCLike.re (inner 𝕜 w u) + θ ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, hre, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hθ, mul_pow]
    ring
  have hw2 : ‖w‖ ^ 2 ≤ L ^ 2 * ‖u‖ ^ 2 := by nlinarith [norm_nonneg w, norm_nonneg u]
  have h1 : 2 * θ * (c * ‖u‖ ^ 2) ≤ 2 * θ * RCLike.re (inner 𝕜 w u) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have h2 : θ ^ 2 * ‖w‖ ^ 2 ≤ θ ^ 2 * (L ^ 2 * ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hw2 (sq_nonneg θ)
  rw [hexp]
  nlinarith [h1, h2]

omit [CompleteSpace E] in
/-- **The damped iteration on a set.**  If `T` is strongly monotone with constant `c` and Lipschitz
with constant `L` *on `s`*, then `x ↦ x - θ (T x - b)` moves two points of `s` no further apart than
the factor `√(1 - 2θc + θ²L²)`.

This is the estimate `contractingWith_damped` makes globally, and it is what a fixed point argument
confined to a closed convex set needs: the iterates never leave the set, so the hypotheses on `T`
are only ever used there.  See `existsUnique_isVariationalInequalitySolution_on`. -/
theorem norm_sub_damped_le {T : E → E} {s : Set E} {c L θ : ℝ} (hθ : 0 ≤ θ)
    (hmono : IsStronglyMonotoneOnWith 𝕜 T s c)
    (hlip : ∀ x ∈ s, ∀ y ∈ s, ‖T x - T y‖ ≤ L * ‖x - y‖) (b : E) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) :
    ‖x - (θ : 𝕜) • (T x - b) - (y - (θ : 𝕜) • (T y - b))‖
      ≤ Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖x - y‖ := by
  have hsub : x - (θ : 𝕜) • (T x - b) - (y - (θ : 𝕜) • (T y - b))
      = (x - y) - (θ : 𝕜) • (T x - T y) := by
    rw [smul_sub, smul_sub, smul_sub]
    abel
  rw [hsub]
  calc ‖(x - y) - (θ : 𝕜) • (T x - T y)‖
      = Real.sqrt (‖(x - y) - (θ : 𝕜) • (T x - T y)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖x - y‖ ^ 2) :=
        Real.sqrt_le_sqrt (norm_sub_smul_sq_le hθ (hmono x hx y hy) (hlip x hx y hy))
    _ = Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖x - y‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

-- `hc` and completeness are not needed for the contraction estimate itself (only `hθ'` and
-- `hθ` are); they are kept so that the statement matches its use in Lax–Milgram.
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- The damped iteration `x ↦ x - θ (T x - b)` contracts with factor `√(1 - 2θc + θ²L²)` for `0 < θ
< 2c/L²`.  Its fixed points are exactly the solutions of `T x = b`, so this is what converts strong
monotonicity into an application of the Banach fixed-point theorem: it is the proof of
[han2009theoretical], Thm 5.1.4, and also their first proof of the Lax–Milgram lemma. -/
theorem contractingWith_damped {T : E → E} {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hmono : IsStronglyMonotoneWith 𝕜 T c) (hlip : LipschitzWith (Real.toNNReal L) T) (b : E)
    {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * c / L ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2)))
      (fun x => x - (θ : 𝕜) • (T x - b)) := by
  have hfac : 1 - 2 * θ * c + θ ^ 2 * L ^ 2 < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hθ'
    nlinarith
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · rw [← NNReal.coe_lt_one, Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.sqrt_lt' one_pos]
    simpa using hfac
  · have hw : ∀ u ∈ (Set.univ : Set E), ∀ v ∈ (Set.univ : Set E), ‖T u - T v‖ ≤ L * ‖u - v‖ := by
      intro u _ v _
      have h := hlip.dist_le_mul u v
      rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le] at h
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm, dist_eq_norm]
    exact norm_sub_damped_le (𝕜 := 𝕜) hθ.le (hmono.isStronglyMonotoneOnWith _) hw b
      (Set.mem_univ x) (Set.mem_univ y)

/-- Zarantonello's theorem ([han2009theoretical], Thm 5.1.4): a strongly monotone Lipschitz map on a
Hilbert space is bijective, with `‖x₁ - x₂‖ ≤ ‖T x₁ - T x₂‖ / c`.  It is the nonlinear counterpart
of Lax–Milgram: strong monotonicity plays the role of coercivity. -/
theorem zarantonello {T : E → E} {c L : ℝ} (hc : 0 < c) (hmono : IsStronglyMonotoneWith 𝕜 T c)
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) : ∃! x, T x = b := by
  -- replace `L` by `L' = max L 1 > 0` so that the damping parameter `θ = c / L'²` makes sense
  have hL' : (0 : ℝ) < max L 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlip' : LipschitzWith (Real.toNNReal (max L 1)) T :=
    hlip.weaken (Real.toNNReal_mono (le_max_left _ _))
  have hθ : 0 < c / max L 1 ^ 2 := by positivity
  have hθ' : c / max L 1 ^ 2 < 2 * c / max L 1 ^ 2 := by
    have h2 : 2 * c / max L 1 ^ 2 = c / max L 1 ^ 2 + c / max L 1 ^ 2 := by ring
    linarith
  have hcon := contractingWith_damped (𝕜 := 𝕜) hc hL' hmono hlip' b hθ hθ'
  have : Nonempty E := ⟨0⟩
  have hiff : ∀ y : E,
      (fun x => x - ((c / max L 1 ^ 2 : ℝ) : 𝕜) • (T x - b)) y = y ↔ T y = b := by
    intro y
    simp only [sub_eq_self, smul_eq_zero, sub_eq_zero]
    exact or_iff_right (by simpa using hθ.ne')
  obtain ⟨xstar, hfix, huniq⟩ := hcon.existsUnique_eq_self
  exact ⟨xstar, (hiff _).mp hfix, fun y hy => huniq y ((hiff y).mpr hy)⟩

set_option linter.unusedSectionVars false in
/-- Lipschitz dependence on the right-hand side: the inverse of a strongly monotone map is `1 /
c`-Lipschitz ([han2009theoretical], (5.1.11)). -/
theorem norm_sub_le_of_strongly_monotone {T : E → E} {c : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith 𝕜 T c) {x₁ x₂ b₁ b₂ : E} (h₁ : T x₁ = b₁) (h₂ : T x₂ = b₂) :
    ‖x₁ - x₂‖ ≤ ‖b₁ - b₂‖ / c := by
  have hkey : c * ‖x₁ - x₂‖ ^ 2 ≤ ‖b₁ - b₂‖ * ‖x₁ - x₂‖ := by
    calc c * ‖x₁ - x₂‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x₁ - T x₂) (x₁ - x₂)) := hmono x₁ x₂
      _ ≤ ‖inner 𝕜 (b₁ - b₂) (x₁ - x₂)‖ := by rw [h₁, h₂]; exact RCLike.re_le_norm _
      _ ≤ ‖b₁ - b₂‖ * ‖x₁ - x₂‖ := norm_inner_le_norm _ _
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg (x₁ - x₂)) with h | h
  · simp [← h]
  · refine le_of_mul_le_mul_right ?_ h
    calc ‖x₁ - x₂‖ * c * ‖x₁ - x₂‖ = c * ‖x₁ - x₂‖ ^ 2 := by ring
      _ ≤ ‖b₁ - b₂‖ * ‖x₁ - x₂‖ := hkey

end Zarantonello
