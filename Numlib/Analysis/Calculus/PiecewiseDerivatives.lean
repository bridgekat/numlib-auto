import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Piecewise
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Joining derivative chains on the real line

Functions whose jets agree at a real seam can be joined without losing derivatives.
Shared Lipschitz constants concatenate without depending on the number of seams.
-/

open Set Filter
open scoped Topology NNReal

/-- Join two functions at a real seam, using the left function at the seam. -/
noncomputable def joinAt {E : Type*} (c : ℝ) (f g : ℝ → E) (x : ℝ) : E :=
  if x ≤ c then f x else g x

@[simp] theorem joinAt_of_le {E : Type*} {c x : ℝ} (f g : ℝ → E) (hx : x ≤ c) :
    joinAt c f g x = f x := ite_eq_left hx

@[simp] theorem joinAt_of_gt {E : Type*} {c x : ℝ} (f g : ℝ → E) (hx : c < x) :
    joinAt c f g x = g x := ite_eq_right (not_le.mpr hx)

/-- Agreement at the seam lets either branch represent the joined value there. -/
theorem joinAt_of_ge {E : Type*} {c x : ℝ} {f g : ℝ → E} (h : f c = g c)
    (hx : c ≤ x) : joinAt c f g x = g x := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using h
  · exact joinAt_of_gt f g hx

/-- Matching function values and matching first derivatives give a derivative across a seam. -/
theorem hasDerivAt_joinAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c x : ℝ} {f g : ℝ → E} {f' g' : E}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : f c = g c)
    (hd : x = c → f' = g') :
    HasDerivAt (joinAt c f g) (if x ≤ c then f' else g') x := by
  rcases lt_trichotomy x c with hx | rfl | hx
  · rw [ite_eq_left hx.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact joinAt_of_le f g hy.le
  · rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (joinAt x f g) f' (Iic x) x :=
      hf.hasDerivWithinAt.congr_of_mem (fun y hy => joinAt_of_le f g hy) self_mem_Iic
    have hr : HasDerivWithinAt (joinAt x f g) f' (Ici x) x := by
      rw [hd rfl]
      exact hg.hasDerivWithinAt.congr_of_mem
        (fun y hy => joinAt_of_ge h hy) self_mem_Iic
    have hh := hl.union hr
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hh
  · rw [ite_eq_right (not_le.mpr hx)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact joinAt_of_gt f g hy

/-- Continuous branches agreeing at a real seam give a continuous join. -/
theorem Continuous.joinAt {E : Type*} [TopologicalSpace E] {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) {c : ℝ} (h : f c = g c) :
    Continuous (joinAt c f g) := by
  change Continuous ((Iic c).piecewise f g)
  apply hf.piecewise _ hg
  intro x hx
  have hx' : x = c := by simpa only [frontier_Iic, mem_singleton_iff] using hx
  simpa only [hx'] using h

/-- Joining matching derivative chains preserves all derivatives through the prescribed order. -/
theorem contDiff_joinAt_of_matching_jets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p : ℕ} {c : ℝ} {f g : ℝ → E}
    (hf : ContDiff ℝ p f) (hg : ContDiff ℝ p g)
    (h : ∀ j ≤ p, iteratedDeriv j f c = iteratedDeriv j g c) :
    ContDiff ℝ p (joinAt c f g) ∧ ∀ j ≤ p,
      iteratedDeriv j (joinAt c f g) = joinAt c (iteratedDeriv j f) (iteratedDeriv j g) := by
  let G := fun j => joinAt c (iteratedDeriv j f) (iteratedDeriv j g)
  have hc : Continuous (G p) :=
    (hf.continuous_iteratedDeriv p le_rfl).joinAt
      (hg.continuous_iteratedDeriv p le_rfl) (h p le_rfl)
  have hd : ∀ j < p, ∀ x ∈ (univ : Set ℝ), HasDerivAt (G j) (G (j + 1) x) x := by
    intro j hj x _
    exact hasDerivAt_joinAt
      (hf.contDiffOn.hasDerivAt_iteratedDeriv_of_isOpen isOpen_univ hj (mem_univ x))
      (hg.contDiffOn.hasDerivAt_iteratedDeriv_of_isOpen isOpen_univ hj (mem_univ x))
      (h j hj.le) (fun hx => hx ▸ h (j + 1) hj)
  obtain ⟨hs, heq⟩ := contDiffOn_of_hasDerivAt_chain isOpen_univ hd hc.continuousOn
  refine ⟨contDiffOn_univ.mp hs, fun j hj => funext fun x => heq j hj (mem_univ x)⟩

/-- A Lipschitz estimate across a real seam uses the same constant on both sides. -/
theorem dist_le_mul_of_lipschitz_across {E : Type*} [PseudoMetricSpace E]
    {K : ℝ≥0} {f g : ℝ → E} {c x y : ℝ} (h : f c = g c)
    (hx : x ≤ c) (hy : c ≤ y)
    (hf : dist (f x) (f c) ≤ K * dist x c)
    (hg : dist (g c) (g y) ≤ K * dist c y) :
    dist (f x) (g y) ≤ K * dist x y := by
  calc
    dist (f x) (g y) ≤ dist (f x) (f c) + dist (g c) (g y) := by
      rw [h]
      exact dist_triangle _ _ _
    _ ≤ K * dist x c + K * dist c y := add_le_add hf hg
    _ = K * dist x y := by
      rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr hy), abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]
      ring

/-- Joins preserve a common Lipschitz constant on any set containing the seam. -/
theorem LipschitzOnWith.joinAt {E : Type*} [PseudoMetricSpace E]
    {K : ℝ≥0} {s : Set ℝ} {f g : ℝ → E} {c : ℝ}
    (hf : LipschitzOnWith K f (s ∩ Iic c))
    (hg : LipschitzOnWith K g (s ∩ Ici c)) (hc : c ∈ s) (h : f c = g c) :
    LipschitzOnWith K (joinAt c f g) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxc : x ≤ c <;> by_cases hyc : y ≤ c
  · simpa only [joinAt_of_le f g hxc, joinAt_of_le f g hyc] using
      hf.dist_le_mul x ⟨hx, hxc⟩ y ⟨hy, hyc⟩
  · rw [joinAt_of_le f g hxc, joinAt_of_gt f g (lt_of_not_ge hyc)]
    exact dist_le_mul_of_lipschitz_across h hxc (le_of_not_ge hyc)
      (hf.dist_le_mul x ⟨hx, hxc⟩ c ⟨hc, self_mem_Iic⟩)
      (hg.dist_le_mul c ⟨hc, self_mem_Ici⟩ y ⟨hy, le_of_not_ge hyc⟩)
  · rw [dist_comm, dist_comm x y]
    rw [joinAt_of_le f g hyc, joinAt_of_gt f g (lt_of_not_ge hxc)]
    exact dist_le_mul_of_lipschitz_across h hyc (le_of_not_ge hxc)
      (hf.dist_le_mul y ⟨hy, hyc⟩ c ⟨hc, self_mem_Iic⟩)
      (hg.dist_le_mul c ⟨hc, self_mem_Ici⟩ x ⟨hx, le_of_not_ge hxc⟩)
  · simpa only [joinAt_of_gt f g (lt_of_not_ge hxc),
      joinAt_of_gt f g (lt_of_not_ge hyc)] using
      hg.dist_le_mul x ⟨hx, le_of_not_ge hxc⟩ y ⟨hy, le_of_not_ge hyc⟩

/-- Adjacent closed intervals concatenate without increasing the Lipschitz constant. -/
theorem LipschitzOnWith.joinAt_Icc {E : Type*} [PseudoMetricSpace E]
    {K : ℝ≥0} {f g : ℝ → E} {a c b : ℝ}
    (hf : LipschitzOnWith K f (Icc a c)) (hg : LipschitzOnWith K g (Icc c b))
    (hac : a ≤ c) (hcb : c ≤ b) (h : f c = g c) :
    LipschitzOnWith K (_root_.joinAt c f g) (Icc a b) := by
  have hl : LipschitzOnWith K f (Icc a b ∩ Iic c) :=
    hf.mono (fun x hx => ⟨hx.1.1, hx.2⟩)
  have hr : LipschitzOnWith K g (Icc a b ∩ Ici c) :=
    hg.mono (fun x hx => ⟨hx.2, hx.1.2⟩)
  exact hl.joinAt hr (show c ∈ Icc a b from ⟨hac, hcb⟩) h

/-- Joins of half-line Lipschitz functions are globally Lipschitz with the same constant. -/
theorem LipschitzWith.joinAt {E : Type*} [PseudoMetricSpace E]
    {K : ℝ≥0} {f g : ℝ → E} {c : ℝ}
    (hf : LipschitzOnWith K f (Iic c)) (hg : LipschitzOnWith K g (Ici c))
    (h : f c = g c) : LipschitzWith K (_root_.joinAt c f g) := by
  rw [← lipschitzOnWith_univ]
  exact (hf.mono inter_subset_right).joinAt (hg.mono inter_subset_right) (mem_univ c) h

/-- Joins preserve a common Lipschitz constant on an initial half-line. -/
theorem LipschitzOnWith.joinAt_Iic {E : Type*} [PseudoMetricSpace E]
    {K : ℝ≥0} {f g : ℝ → E} {a b : ℝ}
    (hf : LipschitzOnWith K f (Iic a)) (hg : LipschitzOnWith K g (Icc a b))
    (hab : a ≤ b) (h : f a = g a) :
    LipschitzOnWith K (_root_.joinAt a f g) (Iic b) := by
  have hl : LipschitzOnWith K f (Iic b ∩ Iic a) := hf.mono inter_subset_right
  have hr : LipschitzOnWith K g (Iic b ∩ Ici a) :=
    hg.mono (fun x hx => ⟨hx.2, hx.1⟩)
  exact hl.joinAt hr hab h

/-- Assemble finitely many functions using successively ordered seams. -/
noncomputable def joinFin {E : Type*} (x : ℕ → ℝ) (f : ℕ → ℝ → E) : ℕ → ℝ → E
  | 0 => f 0
  | n + 1 => joinAt (x n) (joinFin x f n) (f (n + 1))

/-- Beyond the next seam, the final branch is selected by a finite join. -/
theorem joinFin_eq_last {E : Type*} (x : ℕ → ℝ) (f : ℕ → ℝ → E) (n : ℕ)
    (hx : ∀ i < n, x i < x (i + 1)) {t : ℝ} (ht : x n ≤ t) :
    joinFin x f n t = f n t := by
  cases n with
  | zero => rfl
  | succ n => exact joinAt_of_gt _ _ ((hx n (Nat.lt_succ_self n)).trans_le ht)

/-- An early value is unchanged when a later seam is appended. -/
theorem joinFin_succ_of_le {E : Type*} (x : ℕ → ℝ) (f : ℕ → ℝ → E)
    (n : ℕ) {t : ℝ} (ht : t ≤ x n) : joinFin x f (n + 1) t = joinFin x f n t :=
  joinAt_of_le _ _ ht

/-- Finite joining commutes with all derivatives in a matching jet. -/
theorem contDiff_joinFin_of_matching_jets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p n : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hx : ∀ i < n, x i < x (i + 1)) (hf : ∀ i ≤ n, ContDiff ℝ p (f i))
    (hm : ∀ i < n, ∀ j ≤ p, iteratedDeriv j (f i) (x i) =
      iteratedDeriv j (f (i + 1)) (x i)) :
    ContDiff ℝ p (joinFin x f n) ∧ ∀ j ≤ p,
      iteratedDeriv j (joinFin x f n) = joinFin x (fun i => iteratedDeriv j (f i)) n := by
  induction n with
  | zero => exact ⟨hf 0 le_rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨hs, hd⟩ := ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))
      (fun i hi => hf i (Nat.le_succ_of_le hi))
      (fun i hi => hm i (Nat.lt_succ_of_lt hi))
    have hh : ∀ j ≤ p, iteratedDeriv j (joinFin x f n) (x n) =
        iteratedDeriv j (f (n + 1)) (x n) := by
      intro j hj
      rw [hd j hj, joinFin_eq_last x _ n (fun i hi => hx i (Nat.lt_succ_of_lt hi)) le_rfl]
      exact hm n (Nat.lt_succ_self n) j hj
    obtain ⟨hs', hd'⟩ := contDiff_joinAt_of_matching_jets hs (hf (n + 1) le_rfl) hh
    refine ⟨hs', fun j hj => ?_⟩
    simpa only [joinFin, hd j hj] using hd' j hj

/-- A common Lipschitz constant persists through arbitrarily many ordered seams. -/
theorem lipschitzOnWith_joinFin_Iic {E : Type*} [PseudoMetricSpace E]
    {K : ℝ≥0} {n : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hx : ∀ i < n, x i < x (i + 1))
    (hf : LipschitzOnWith K (f 0) (Iic (x 0)))
    (hp : ∀ i < n, LipschitzOnWith K (f (i + 1)) (Icc (x i) (x (i + 1))))
    (hm : ∀ i < n, f i (x i) = f (i + 1) (x i)) :
    LipschitzOnWith K (joinFin x f n) (Iic (x n)) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hl := ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))
      (fun i hi => hp i (Nat.lt_succ_of_lt hi))
      (fun i hi => hm i (Nat.lt_succ_of_lt hi))
    apply hl.joinAt_Iic (hp n (Nat.lt_succ_self n)) (hx n (Nat.lt_succ_self n)).le
    rw [joinFin_eq_last x f n (fun i hi => hx i (Nat.lt_succ_of_lt hi)) le_rfl]
    exact hm n (Nat.lt_succ_self n)

/-- Finitely many matching smooth pieces, including exterior pieces, give a global smooth
function with a Lipschitz highest derivative. The constant is independent of the seam count. -/
theorem contDiff_lipschitz_joinFin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : ℝ≥0} {p n : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hx : ∀ i < n, x i < x (i + 1)) (hf : ∀ i ≤ n + 1, ContDiff ℝ p (f i))
    (hm : ∀ i ≤ n, ∀ j ≤ p, iteratedDeriv j (f i) (x i) =
      iteratedDeriv j (f (i + 1)) (x i))
    (hl : LipschitzOnWith K (iteratedDeriv p (f 0)) (Iic (x 0)))
    (hp : ∀ i < n, LipschitzOnWith K (iteratedDeriv p (f (i + 1)))
      (Icc (x i) (x (i + 1))))
    (hr : LipschitzOnWith K (iteratedDeriv p (f (n + 1))) (Ici (x n))) :
    ContDiff ℝ p (joinFin x f (n + 1)) ∧
      LipschitzWith K (iteratedDeriv p (joinFin x f (n + 1))) := by
  have hprefix := contDiff_joinFin_of_matching_jets hx
    (fun i hi => hf i (Nat.le_succ_of_le hi)) (fun i hi => hm i hi.le)
  have hseam : ∀ j ≤ p, iteratedDeriv j (joinFin x f n) (x n) =
      iteratedDeriv j (f (n + 1)) (x n) := by
    intro j hj
    rw [hprefix.2 j hj, joinFin_eq_last x _ n hx le_rfl]
    exact hm n le_rfl j hj
  have hfinal := contDiff_joinAt_of_matching_jets hprefix.1 (hf _ le_rfl) hseam
  refine ⟨hfinal.1, ?_⟩
  change LipschitzWith K (iteratedDeriv p (joinAt (x n) (joinFin x f n) (f (n + 1))))
  rw [hfinal.2 p le_rfl, hprefix.2 p le_rfl]
  exact LipschitzWith.joinAt
    (lipschitzOnWith_joinFin_Iic hx hl hp
      (fun i hi => hm i hi.le p le_rfl)) hr (by
        rw [joinFin_eq_last x _ n hx le_rfl]
        exact hm n le_rfl p le_rfl)

/-- Consecutive inequalities order every pair of indices in a finite sequence. -/
theorem le_of_adjacent_le {α : Type*} [Preorder α] {x : ℕ → α} {n i j : ℕ}
    (hx : ∀ k < n, x k ≤ x (k + 1)) (hij : i ≤ j) (hjn : j ≤ n) : x i ≤ x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (Nat.le_of_succ_le hjn)).trans (hx j (by omega))

/-- A finite join at an earlier seam uses the piece immediately preceding that seam. -/
theorem joinFin_at_knot {E : Type*} {x : ℕ → ℝ} {f : ℕ → ℝ → E} {n k : ℕ}
    (hx : ∀ i < n, x i < x (i + 1)) (hk : k ≤ n) :
    joinFin x f n (x k) = f k (x k) := by
  induction n with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero hk; rfl
  | succ n ih =>
    rcases hk.eq_or_lt with rfl | hk
    · exact joinFin_eq_last x f (n + 1) hx le_rfl
    · rw [joinFin_succ_of_le x f n
        (le_of_adjacent_le (fun i hi => (hx i (by omega)).le) (by omega) le_rfl)]
      exact ih (fun i hi => hx i (by omega)) (by omega)

/-- A common norm bound on the left tail and successive intervals is preserved by joining. -/
theorem norm_joinFin_le {E : Type*} [SeminormedAddCommGroup E]
    {B : ℝ} {n : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hl : ∀ t ≤ x 0, ‖f 0 t‖ ≤ B)
    (hp : ∀ i < n, ∀ t ∈ Icc (x i) (x (i + 1)), ‖f (i + 1) t‖ ≤ B) :
    ∀ t ≤ x n, ‖joinFin x f n t‖ ≤ B := by
  induction n with
  | zero => exact hl
  | succ n ih =>
    intro t ht
    by_cases hc : t ≤ x n
    · rw [joinFin_succ_of_le x f n hc]
      exact ih (fun i hi => hp i (Nat.lt_succ_of_lt hi)) t hc
    · change ‖joinAt (x n) (joinFin x f n) (f (n + 1)) t‖ ≤ B
      rw [joinAt_of_gt _ _ (lt_of_not_ge hc)]
      exact hp n (Nat.lt_succ_self n) t ⟨le_of_not_ge hc, ht⟩

/-- Adding a bounded final tail turns uniform bounds on all pieces into a global bound. -/
theorem norm_joinFin_le_global {E : Type*} [SeminormedAddCommGroup E]
    {B : ℝ} {n : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hl : ∀ t ≤ x 0, ‖f 0 t‖ ≤ B)
    (hp : ∀ i < n, ∀ t ∈ Icc (x i) (x (i + 1)), ‖f (i + 1) t‖ ≤ B)
    (hr : ∀ t ≥ x n, ‖f (n + 1) t‖ ≤ B) :
    ∀ t, ‖joinFin x f (n + 1) t‖ ≤ B := by
  intro t
  by_cases ht : t ≤ x n
  · rw [joinFin_succ_of_le x f n ht]
    exact norm_joinFin_le hl hp t ht
  · change ‖joinAt (x n) (joinFin x f n) (f (n + 1)) t‖ ≤ B
    rw [joinAt_of_gt _ _ (lt_of_not_ge ht)]
    exact hr t (le_of_not_ge ht)

/-- Before every seam, a finite join agrees with its initial branch. -/
theorem joinFin_eq_first {E : Type*} {x : ℕ → ℝ} {f : ℕ → ℝ → E} {n : ℕ}
    (hx : ∀ i < n, x 0 ≤ x i) {t : ℝ} (ht : t ≤ x 0) :
    joinFin x f n t = f 0 t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [joinFin_succ_of_le x f n (ht.trans (hx n (Nat.lt_succ_self n)))]
    exact ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))

/-- Uniform bounds concatenate on the compact span even if the exterior branches grow. -/
theorem norm_joinFin_le_on_Icc {E : Type*} [SeminormedAddCommGroup E]
    {B : ℝ} {n : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hl : ‖f 0 (x 0)‖ ≤ B)
    (hp : ∀ i < n, ∀ t ∈ Icc (x i) (x (i + 1)), ‖f (i + 1) t‖ ≤ B) :
    ∀ t ∈ Icc (x 0) (x n), ‖joinFin x f n t‖ ≤ B := by
  induction n with
  | zero => intro t ht; obtain rfl := le_antisymm ht.2 ht.1; exact hl
  | succ n ih =>
    intro t ht
    by_cases hc : t ≤ x n
    · rw [joinFin_succ_of_le x f n hc]
      exact ih (fun i hi => hp i (Nat.lt_succ_of_lt hi)) t ⟨ht.1, hc⟩
    · change ‖joinAt (x n) (joinFin x f n) (f (n + 1)) t‖ ≤ B
      rw [joinAt_of_gt _ _ (lt_of_not_ge hc)]
      exact hp n (Nat.lt_succ_self n) t ⟨le_of_not_ge hc, ht.2⟩
