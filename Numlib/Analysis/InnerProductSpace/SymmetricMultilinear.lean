import Numlib.Analysis.Normed.Multilinear.Diagonal
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Symmetric multilinear forms on real inner product spaces

A symmetric scalar-valued continuous multilinear form on a finite-dimensional real inner
product space attains its operator norm on the diagonal. The proof chooses a unit tuple
attaining the norm whose sum has maximal norm. Two-coordinate polarization replaces any
unequal pair by a repeated unit vector, preserving norm attainment and increasing the sum
norm. This forces all coordinates to agree. Positive order includes the zero-dimensional
space in the resulting equality of the diagonal sphere supremum and the operator norm.
-/

noncomputable section

open scoped BigOperators
open Function

namespace ContinuousMultilinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ}

/-- Unit tuples suffice to bound the norm of a multilinear map. -/
theorem opNorm_le_of_unit_bound
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ v, (∀ i, ‖v i‖ = 1) → ‖T v‖ ≤ C) : ‖T‖ ≤ C := by
  classical
  apply opNorm_le_bound hC
  intro v
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [T.map_coord_zero i hi, norm_zero]
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · have hn (i) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (fun hi => hz ⟨i, hi⟩)
    let u := fun i => (‖v i‖⁻¹ : ℝ) • v i
    have hu (i) : ‖u i‖ = 1 := by simp [u, norm_smul, hn i]
    have he : v = fun i => ‖v i‖ • u i := by
      funext i
      simp [u, smul_smul, hn i]
    calc
      ‖T v‖ = (∏ i, ‖v i‖) * ‖T u‖ := by
        conv_lhs => rw [he, T.map_smul_univ]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))]
      _ ≤ (∏ i, ‖v i‖) * C := mul_le_mul_of_nonneg_left (h u hu)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = C * ∏ i, ‖v i‖ := mul_comm _ _

/-- A finite-dimensional multilinear form attains its operator norm at a unit tuple. -/
theorem exists_unit_norm_eq_norm [FiniteDimensional ℝ E] [Nontrivial E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) :
    ∃ v, (∀ i, ‖v i‖ = 1) ∧ ‖T v‖ = ‖T‖ := by
  let s : Set (Fin p → E) := Set.pi Set.univ (fun _ => Metric.sphere 0 1)
  have hs : IsCompact s := isCompact_univ_pi (fun _ => isCompact_sphere _ _)
  obtain ⟨a, ha⟩ := NormedSpace.sphere_nonempty (x := (0 : E)).mpr zero_le_one
  have hne : s.Nonempty := ⟨fun _ => a, fun _ _ => ha⟩
  obtain ⟨v, hv, hm⟩ := hs.exists_isMaxOn hne T.cont.norm.continuousOn
  have hv' (i) : ‖v i‖ = 1 := by simpa using hv i (Set.mem_univ i)
  refine ⟨v, hv', le_antisymm ?_ ?_⟩
  · simpa [hv'] using T.le_opNorm v
  · apply T.opNorm_le_of_unit_bound (norm_nonneg _)
    intro w hw
    exact hm (fun i _ => by simp [hw i])

/-- Among the unit tuples attaining the norm, one maximizes the norm of its sum. -/
theorem exists_unit_norm_eq_norm_max_sum [FiniteDimensional ℝ E] [Nontrivial E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) :
    ∃ v, (∀ i, ‖v i‖ = 1) ∧ ‖T v‖ = ‖T‖ ∧
      ∀ w, (∀ i, ‖w i‖ = 1) → ‖T w‖ = ‖T‖ → ‖∑ i, w i‖ ≤ ‖∑ i, v i‖ := by
  let s : Set (Fin p → E) := Set.pi Set.univ (fun _ => Metric.sphere 0 1)
  have hs : IsCompact s := isCompact_univ_pi (fun _ => isCompact_sphere _ _)
  have hc : IsClosed {v : Fin p → E | ‖T v‖ = ‖T‖} :=
    isClosed_eq T.cont.norm continuous_const
  obtain ⟨a, ha, hTa⟩ := T.exists_unit_norm_eq_norm
  have hne : (s ∩ {v | ‖T v‖ = ‖T‖}).Nonempty :=
    ⟨a, (fun i _ => by simp [ha i]), hTa⟩
  obtain ⟨v, ⟨hv, hTv⟩, hm⟩ := (hs.inter_right hc).exists_isMaxOn hne
    (by fun_prop : Continuous (fun v : Fin p → E => ‖∑ i, v i‖)).continuousOn
  refine ⟨v, (fun i => by simpa using hv i (Set.mem_univ i)), hTv, ?_⟩
  intro w hw hTw
  exact hm ⟨(fun i _ => by simp [hw i]), hTw⟩

/-- Symmetry permits exchanging two specified coordinates while the others stay fixed. -/
theorem IsSymmetric.update_update_swap
    {T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ} (hT : T.IsSymmetric)
    (v : Fin p → E) {i j : Fin p} (hij : i ≠ j) (x y : E) :
    T (update (update v i x) j y) = T (update (update v i y) j x) := by
  classical
  have he : (update (update v i x) j y) ∘ Equiv.swap i j =
      update (update v i y) j x := by
    funext k
    by_cases hi : k = i
    · subst k; simp [hij]
    by_cases hj : k = j
    · subst k; simp [hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
  rw [← he, hT]

/-- Two-coordinate polarization with the remaining multilinear arguments fixed. -/
theorem IsSymmetric.update_update_polarization
    {T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ} (hT : T.IsSymmetric)
    (v : Fin p → E) {i j : Fin p} (hij : i ≠ j) (x y : E) :
    T (update (update v i (x + y)) j (x + y)) -
      T (update (update v i (x - y)) j (x - y)) =
      4 * T (update (update v i x) j y) := by
  classical
  have hadd (a b c : E) :
      T (update (update v i (a + b)) j c) =
        T (update (update v i a) j c) + T (update (update v i b) j c) := by
    simp_rw [update_comm hij]
    exact T.map_update_add _ _ _ _
  have hsub (a b c : E) :
      T (update (update v i (a - b)) j c) =
        T (update (update v i a) j c) - T (update (update v i b) j c) := by
    simp_rw [update_comm hij]
    exact T.map_update_sub _ _ _ _
  rw [hadd, hsub]
  simp_rw [T.map_update_add, T.map_update_sub]
  rw [hT.update_update_swap v hij y x]
  ring

/-- Replacing two unit arguments gives the usual two-coordinate operator norm bound. -/
theorem norm_update_update_le
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    (v : Fin p → E) (hv : ∀ i, ‖v i‖ = 1) {i j : Fin p} (hij : i ≠ j) (x y : E) :
    ‖T (update (update v i x) j y)‖ ≤ ‖T‖ * (‖x‖ * ‖y‖) := by
  classical
  have he : (fun k => ‖update (update v i x) j y k‖) =
      update (update (fun k => ‖v k‖) i ‖x‖) j ‖y‖ := by
    funext k
    by_cases hkj : k = j
    · subst k; simp
    · by_cases hki : k = i <;> simp [hkj, hki, hij]
  have hp : (∏ k, ‖update (update v i x) j y k‖) = ‖x‖ * ‖y‖ := by
    rw [he, Finset.prod_update_of_mem (Finset.mem_univ j),
      Finset.prod_update_of_mem (by simp [hij])]
    simp [hv, mul_comm]
  simpa [hp] using T.le_opNorm (update (update v i x) j y)

/-- Scaling both selected coordinates scales their evaluation quadratically. -/
theorem update_update_smul
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    (v : Fin p → E) {i j : Fin p} (hij : i ≠ j) (c : ℝ) (x y : E) :
    T (update (update v i (c • x)) j (c • y)) =
      c ^ 2 * T (update (update v i x) j y) := by
  classical
  rw [T.map_update_smul, update_comm hij, T.map_update_smul, update_comm hij.symm]
  simp [sq, mul_assoc]

end ContinuousMultilinearMap

namespace ContinuousMultilinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The norm of the sum of two distinct unit vectors is strictly less than two. -/
theorem norm_add_lt_two_of_unit {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : x ≠ y) : ‖x + y‖ < 2 := by
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hh := parallelogram_law_with_norm ℝ x y
  rw [hx, hy] at hh
  nlinarith [norm_nonneg (x + y), sq_pos_of_pos hd]

/-- If a pair attains the full norm, its normalized sum also attains it whenever nonzero. -/
theorem IsSymmetric.norm_update_update_normalize_add
    {T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ} (hT : T.IsSymmetric)
    (v : Fin p → E) (hv : ∀ i, ‖v i‖ = 1) {i j : Fin p} (hij : i ≠ j)
    (hm : ‖T v‖ = ‖T‖) (hs : v i + v j ≠ 0) :
    ‖T (update (update v i ((‖v i + v j‖⁻¹ : ℝ) • (v i + v j)))
      j ((‖v i + v j‖⁻¹ : ℝ) • (v i + v j)))‖ = ‖T‖ := by
  classical
  have hp := hT.update_update_polarization v hij (v i) (v j)
  simp only [update_eq_self] at hp
  have ha := T.norm_update_update_le v hv hij (v i + v j) (v i + v j)
  have hb := T.norm_update_update_le v hv hij (v i - v j) (v i - v j)
  have hh := parallelogram_law_with_norm ℝ (v i) (v j)
  rw [hv i, hv j] at hh
  have ht : 4 * ‖T‖ ≤
      ‖T (update (update v i (v i + v j)) j (v i + v j))‖ +
      ‖T (update (update v i (v i - v j)) j (v i - v j))‖ := by
    have ht := norm_sub_le (T (update (update v i (v i + v j)) j (v i + v j)))
      (T (update (update v i (v i - v j)) j (v i - v j)))
    rw [hp, norm_mul, show ‖(4 : ℝ)‖ = 4 by norm_num, hm] at ht
    exact ht
  have he : ‖T (update (update v i (v i + v j)) j (v i + v j))‖ =
      ‖T‖ * ‖v i + v j‖ ^ 2 := by
    have hh' := congrArg (fun r : ℝ => ‖T‖ * r) hh
    nlinarith
  rw [T.update_update_smul v hij, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), he]
  have hn : ‖v i + v j‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  field_simp

/-- Expanding a vector of norm less than two to either end of a unit diameter strictly
increases its distance from any fixed point for at least one choice of sign. -/
theorem exists_sign_norm_add_lt (z u : E) (hu : ‖u‖ = 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr2 : r < 2) :
    ∃ c : ℝ, |c| = 1 ∧ ‖z + r • u‖ < ‖z + (2 * c) • u‖ := by
  have h0 := norm_add_sq_real z (r • u)
  have hp := norm_add_sq_real z ((2 : ℝ) • u)
  have hn := norm_add_sq_real z ((-2 : ℝ) • u)
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
    abs_of_nonneg hr0] at h0 hp hn
  norm_num at hp hn
  by_cases hi : 0 ≤ inner ℝ z u
  · refine ⟨1, by norm_num, ?_⟩
    have hm := mul_nonneg (le_of_lt (sub_pos.mpr hr2)) hi
    norm_num
    nlinarith [norm_nonneg (z + r • u), norm_nonneg (z + (2 : ℝ) • u)]
  · refine ⟨-1, by norm_num, ?_⟩
    have hm := mul_nonpos_of_nonneg_of_nonpos hr0 (le_of_not_ge hi)
    norm_num
    have hin : inner ℝ z u < 0 := lt_of_not_ge hi
    nlinarith [norm_nonneg (z + r • u), norm_nonneg (z + -((2 : ℝ) • u))]

omit [InnerProductSpace ℝ E] in
/-- Updating two entries changes the tuple sum by the corresponding two differences. -/
theorem sum_update_update (v : Fin p → E) {i j : Fin p} (hij : i ≠ j) (x y : E) :
    (∑ k, update (update v i x) j y k) = (∑ k, v k) - v i - v j + x + y := by
  classical
  have hs (f : Fin p → E) (k : Fin p) (a : E) :
      (∑ l, update f k a l) = (∑ l, f l) - f k + a := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
    have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)
    have hd : (Finset.univ \ {k} : Finset (Fin p)) = Finset.univ.erase k := by ext; simp
    rw [hd]
    rw [← he]
    abel
  rw [hs, hs]
  simp only [update_of_ne hij.symm]
  abel

/-- An unequal pair in a norm-attaining unit tuple has a repeated unit replacement that
still attains the norm, while its original sum has length strictly less than two. -/
theorem IsSymmetric.exists_unit_pair_replacement
    {T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ} (hT : T.IsSymmetric)
    (v : Fin p → E) (hv : ∀ i, ‖v i‖ = 1) {i j : Fin p} (hij : i ≠ j)
    (hm : ‖T v‖ = ‖T‖) (hxy : v i ≠ v j) :
    ∃ (u : E) (r : ℝ), ‖u‖ = 1 ∧ 0 ≤ r ∧ r < 2 ∧ v i + v j = r • u ∧
      ‖T (update (update v i u) j u)‖ = ‖T‖ := by
  classical
  by_cases hs : v i + v j = 0
  · have hj : v j = -v i := by
      calc
        v j = (v i + v j) - v i := by abel
        _ = -v i := by rw [hs]; simp
    refine ⟨v i, 0, hv i, le_rfl, by norm_num, by simp [hs], ?_⟩
    have he : T v = -T (update (update v i (v i)) j (v i)) := by
      simp only [update_eq_self]
      change T.toMultilinearMap v = -T.toMultilinearMap (update v j (v i))
      rw [← T.toMultilinearMap.map_update_neg, ← hj, update_eq_self]
    rw [← hm, he, norm_neg]
  · let u := (‖v i + v j‖⁻¹ : ℝ) • (v i + v j)
    have hn : ‖v i + v j‖ ≠ 0 := norm_ne_zero_iff.mpr hs
    refine ⟨u, ‖v i + v j‖, ?_, norm_nonneg _,
      norm_add_lt_two_of_unit (hv i) (hv j) hxy, ?_,
      hT.norm_update_update_normalize_add v hv hij hm hs⟩
    · change ‖(‖v i + v j‖⁻¹ : ℝ) • (v i + v j)‖ = 1
      rw [norm_smul]
      simp [hn]
    · simp [u, smul_smul, hn]

/-- A norm-attaining unit tuple with maximal sum norm has every coordinate equal. -/
theorem IsSymmetric.eq_of_max_sum
    {T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ} (hT : T.IsSymmetric)
    (v : Fin p → E) (hv : ∀ i, ‖v i‖ = 1) (hm : ‖T v‖ = ‖T‖)
    (hmax : ∀ w, (∀ i, ‖w i‖ = 1) → ‖T w‖ = ‖T‖ →
      ‖∑ i, w i‖ ≤ ‖∑ i, v i‖) (i j : Fin p) : v i = v j := by
  classical
  by_contra hxy
  have hij : i ≠ j := fun h => hxy (congrArg v h)
  obtain ⟨u, r, hu, hr0, hr2, hs, hTu⟩ :=
    hT.exists_unit_pair_replacement v hv hij hm hxy
  let z := (∑ k, v k) - v i - v j
  obtain ⟨c, hc, hlt⟩ := exists_sign_norm_add_lt z u hu hr0 hr2
  let w := update (update v i (c • u)) j (c • u)
  have hw (k) : ‖w k‖ = 1 := by
    by_cases hkj : k = j
    · subst k; simp [w, norm_smul, Real.norm_eq_abs, hc, hu]
    by_cases hki : k = i
    · subst k; simp [w, hij, norm_smul, Real.norm_eq_abs, hc, hu]
    · simp [w, hkj, hki, hv k]
  have hTw : ‖T w‖ = ‖T‖ := by
    change ‖T (update (update v i (c • u)) j (c • u))‖ = ‖T‖
    rw [T.update_update_smul v hij, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), hTu]
    have hc2 : c ^ 2 = 1 := by nlinarith [sq_abs c]
    rw [hc2, one_mul]
  have hsum : (∑ k, w k) = z + (2 * c) • u := by
    rw [show (∑ k, w k) = (∑ k, v k) - v i - v j + c • u + c • u from
      sum_update_update v hij _ _]
    rw [mul_smul, two_smul]
    dsimp [z]
    abel
  have hsumv : (∑ k, v k) = z + r • u := by rw [← hs]; dsimp [z]; abel
  have hle := hmax w hw hTw
  rw [hsum, hsumv] at hle
  exact (not_lt_of_ge hle) hlt

/-- Banach's theorem in its attained form: a symmetric scalar multilinear form on a
nontrivial finite-dimensional real inner product space attains its norm on the diagonal. -/
theorem exists_unit_norm_diagonal_eq_norm [FiniteDimensional ℝ E] [Nontrivial E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) (hp : 0 < p)
    (hT : T.IsSymmetric) : ∃ u : E, ‖u‖ = 1 ∧ ‖T.diagonal u‖ = ‖T‖ := by
  obtain ⟨v, hv, hm, hmax⟩ := T.exists_unit_norm_eq_norm_max_sum
  let i : Fin p := ⟨0, hp⟩
  have he : v = fun _ => v i := funext fun j => hT.eq_of_max_sum v hv hm hmax j i
  refine ⟨v i, hv i, ?_⟩
  rw [diagonal, ← he, hm]

/-- Banach's symmetric multilinear norm theorem over the real scalars. Positive-order
symmetric scalar forms on a finite-dimensional real inner product space have diagonal
sphere supremum equal to their operator norm. The zero-dimensional case is included. -/
theorem diagonalNorm_eq_norm_of_isSymmetric [FiniteDimensional ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) (hp : 0 < p)
    (hT : T.IsSymmetric) : T.diagonalNorm = ‖T‖ := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let : Subsingleton E := h
    have hzero : T = 0 := by
      ext v
      exact T.map_coord_zero ⟨0, hp⟩ (Subsingleton.elim _ _)
    rw [T.diagonalNorm_of_subsingleton, hzero, norm_zero]
  | inr h =>
    let : Nontrivial E := h
    obtain ⟨u, hu, hTu⟩ := T.exists_unit_norm_diagonal_eq_norm hp hT
    exact le_antisymm T.diagonalNorm_le_norm
      (hTu ▸ T.norm_diagonal_le_diagonalNorm hu)

end ContinuousMultilinearMap
