import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Numlib.LinearSolve.Stationary.Basic

/-!
# Fixed-point iterations

Glue around Mathlib's `ContractingWith` for the Banach fixed-point theorem with the a priori, a
posteriori and linear-rate bounds ([han2009theoretical] Thm 5.1.3, estimates (5.1.4)–(5.1.6);
[kress1998numerical] Thm 3.45–3.46), the `T^m`-contraction variant ([han2009theoretical] Exercise
5.1.2, [kress1998numerical] Problem 3.17), the derivative criterion `sup ‖T'‖ < 1`
([kress1998numerical] Thm 6.8; [han2009theoretical] give the scalar case in the remark following
their Thm 5.2.1), and Zarantonello's theorem for strongly monotone Lipschitz maps on Hilbert spaces
([han2009theoretical] Thm 5.1.4, the nonlinear Lax–Milgram).
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

/-- Geometric decay of the iterates towards a fixed point inside an invariant set. -/
private theorem dist_iterate_le_pow_mul {f : α → α} {s : Set α} (hmaps : Set.MapsTo f s s) {K : ℝ}
    (hK0 : 0 ≤ K) (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) {x' : α} (hx' : x' ∈ s)
    (hfix : f x' = x') {x₀ : α} (hx₀ : x₀ ∈ s) (n : ℕ) :
    dist (f^[n] x₀) x' ≤ K ^ n * dist x₀ x' := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc dist (f^[n + 1] x₀) x' = dist (f (f^[n] x₀)) (f x') := by
          rw [Function.iterate_succ_apply', hfix]
      _ ≤ K * dist (f^[n] x₀) x' := hf _ (hmaps.iterate n hx₀) _ hx'
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
        dist_iterate_le_pow_mul hmaps hK0 hf hx' hfix hx₀ n
    _ ≤ K ^ n * (dist (f x₀) x₀ / (1 - K)) := by
        gcongr
        rw [le_div_iff₀ h1K, mul_comm]
        exact one_sub_mul_dist_le hf hx' hfix hx₀
    _ = K ^ n / (1 - K) * dist (f x₀) x₀ := by ring

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
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- each of the `m` interleaved subsequences `k ↦ T^[m k + j] x` iterates the contraction `T^[m]`
  have key : ∀ j : ℕ, ∃ N, ∀ k ≥ N,
      dist ((T^[m])^[k] (T^[j] x)) (hK.fixedPoint T^[m]) < ε := fun j =>
    Metric.tendsto_atTop.mp (hK.tendsto_iterate_fixedPoint (T^[j] x)) ε hε
  choose N hN using key
  refine ⟨m * ((Finset.range m).sup N + 1), fun n hn => ?_⟩
  have hsplit : (T^[m])^[n / m] (T^[n % m] x) = T^[n] x := by
    rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.div_add_mod]
  have hqle : (Finset.range m).sup N + 1 ≤ n / m := by
    rw [Nat.le_div_iff_mul_le hm, mul_comm]
    exact hn
  rw [← hsplit]
  refine hN _ _ (le_trans (le_trans ?_ (Nat.le_succ _)) hqle)
  exact Finset.le_sup (Finset.mem_range.mpr (Nat.mod_lt _ hm))

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
    (hmono : ∀ x ∈ s, ∀ y ∈ s, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y)))
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
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y)))
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) {θ : ℝ} (hθ : 0 < θ)
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
    exact norm_sub_damped_le (𝕜 := 𝕜) hθ.le (fun u _ v _ => hmono u v) hw b (Set.mem_univ x)
      (Set.mem_univ y)

/-- Zarantonello's theorem ([han2009theoretical], Thm 5.1.4): a strongly monotone Lipschitz map on a
Hilbert space is bijective, with `‖x₁ - x₂‖ ≤ ‖T x₁ - T x₂‖ / c`.  It is the nonlinear counterpart
of Lax–Milgram: strong monotonicity plays the role of coercivity. -/
theorem zarantonello {T : E → E} {c L : ℝ} (hc : 0 < c)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y)))
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
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y))) {x₁ x₂ b₁ b₂ : E}
    (h₁ : T x₁ = b₁) (h₂ : T x₂ = b₂) : ‖x₁ - x₂‖ ≤ ‖b₁ - b₂‖ / c := by
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
