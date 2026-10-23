import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# Higher derivative differences of bilinear compositions

The Leibniz estimate controls the difference of two actual higher derivative
maps. It retains the zero-order function values separately from positive-order
derivatives, permitting affine residual bounds for least-squares objectives.
The local form works on any set with unique derivatives; an open-set corollary
controls squared Hilbert norms by the actual derivative maps of the residual.
-/

open scoped BigOperators ContDiff
universe u
variable {D E F G : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The difference of zeroth derivative maps has the original value-difference norm. -/
theorem norm_iteratedFDeriv_zero_sub (f : D → E) (x y : D) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ←map_sub,
    LinearIsometryEquiv.norm_map]

/-- Currying preserves norms of differences when a derivative is taken first. -/
theorem norm_iteratedFDeriv_fderiv_sub (f : D → E) (n : ℕ) (x y : D) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖ =
      ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  rw [←(continuousMultilinearCurryRightEquiv' ℝ n D E).symm.map_sub,
    LinearIsometryEquiv.norm_map]

/-- A bilinear value difference splits into one difference in each argument. -/
theorem ContinuousLinearMap.norm_bilinear_sub_le (B : E →L[ℝ] F →L[ℝ] G)
    (a b : E) (c d : F) :
    ‖B a c - B b d‖ ≤ ‖B‖ * (‖a - b‖ * ‖c‖ + ‖b‖ * ‖c - d‖) := by
  have he : B a c - B b d = B (a - b) c + B b (c - d) := by
    simp only [map_sub, sub_apply]
    abel
  rw [he, mul_add, ←mul_assoc, ←mul_assoc]
  exact (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))


/-- The zeroth derivative difference within a set is the original value difference. -/
theorem norm_iteratedFDerivWithin_zero_sub (f : D → E) (s : Set D) (x y : D) :
    ‖iteratedFDerivWithin ℝ 0 f s x - iteratedFDerivWithin ℝ 0 f s y‖ = ‖f x - f y‖ := by
  simp only [iteratedFDerivWithin_zero_eq, norm_iteratedFDeriv_zero_sub]

/-- On a set with unique derivatives, currying preserves higher derivative
difference norms at any two points of that set. -/
theorem norm_iteratedFDerivWithin_fderivWithin_sub (f : D → E) (n : ℕ) {s : Set D}
    (hs : UniqueDiffOn ℝ s) {x y : D} (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ n (fderivWithin ℝ f s) s x -
      iteratedFDerivWithin ℝ n (fderivWithin ℝ f s) s y‖ =
      ‖iteratedFDerivWithin ℝ (n + 1) f s x - iteratedFDerivWithin ℝ (n + 1) f s y‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx,
    iteratedFDerivWithin_succ_eq_comp_right hs hy]
  simp only [Function.comp_apply]
  rw [←(continuousMultilinearCurryRightEquiv' ℝ n D E).symm.map_sub,
    LinearIsometryEquiv.norm_map]
/-- The exact binomial sum controlling differences of bilinear higher derivatives. -/
noncomputable def jetDifferenceSumWithin (f : D → E) (g : D → F) (s : Set D)
    (n : ℕ) (x y : D) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (‖iteratedFDerivWithin ℝ i f s x - iteratedFDerivWithin ℝ i f s y‖ *
      ‖iteratedFDerivWithin ℝ (n - i) g s x‖ + ‖iteratedFDerivWithin ℝ i f s y‖ *
      ‖iteratedFDerivWithin ℝ (n - i) g s x - iteratedFDerivWithin ℝ (n - i) g s y‖)

/-- Each term in the binomial derivative difference bound is nonnegative. -/
theorem jetDifferenceSumWithin_nonneg (f : D → E) (g : D → F) (s : Set D) (n : ℕ) (x y : D) :
    0 ≤ jetDifferenceSumWithin f g s n x y := by
  unfold jetDifferenceSumWithin
  positivity

/-- The difference of actual higher derivatives of a bilinear composition is
bounded by the binomial Leibniz sum on any set with unique derivatives. -/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_sub_bilinear_le
    (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {n : ℕ} {s : Set D}
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hs : UniqueDiffOn ℝ s) {x y : D} (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ n (fun z => B (f z) (g z)) s x -
      iteratedFDerivWithin ℝ n (fun z => B (f z) (g z)) s y‖ ≤
      ‖B‖ * jetDifferenceSumWithin f g s n x y := by
  induction n generalizing E F G with
  | zero =>
    simpa only [jetDifferenceSumWithin, Finset.range_one, Finset.sum_singleton,
      Nat.choose_self, Nat.zero_add, Nat.cast_one, one_mul, Nat.sub_zero,
      norm_iteratedFDerivWithin_zero,
      norm_iteratedFDerivWithin_zero_sub] using B.norm_bilinear_sub_le (f x) (f y) (g x) (g y)
  | succ n IH =>
    have hn : (n : ℕ∞ω) + 1 ≤ n.succ := by simp
    have hfn := hf.of_le (show (n : ℕ∞ω) ≤ n.succ by exact_mod_cast Nat.le_succ n)
    have hgn := hg.of_le (show (n : ℕ∞ω) ≤ n.succ by exact_mod_cast Nat.le_succ n)
    have hfd := hf.fderivWithin hs hn
    have hgd := hg.fderivWithin hs hn
    let a := fun z => B.precompR D (f z) (fderivWithin ℝ g s z)
    let b := fun z => B.precompL D (fderivWithin ℝ f s z) (g z)
    have ha : ContDiffOn ℝ n a s :=
      (B.precompR D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfn hgd
    have hb : ContDiffOn ℝ n b s :=
      (B.precompL D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfd hgn
    have he : Set.EqOn (fderivWithin ℝ (fun z => B (f z) (g z)) s) (a + b) s := by
      intro z hz
      exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) z hz)
        (hg.differentiableOn (by positivity) z hz) (hs z hz)
    rw [←norm_iteratedFDerivWithin_fderivWithin_sub _ _ hs hx hy,
      iteratedFDerivWithin_congr he hx, iteratedFDerivWithin_congr he hy,
      iteratedFDerivWithin_add_apply (ha.contDiffWithinAt hx) (hb.contDiffWithinAt hx) hs hx,
      iteratedFDerivWithin_add_apply (ha.contDiffWithinAt hy) (hb.contDiffWithinAt hy) hs hy]
    have ha' := IH (B.precompR D) hfn hgd
    have hb' := IH (B.precompL D) hfd hgn
    have hsum : ‖iteratedFDerivWithin ℝ n a s x - iteratedFDerivWithin ℝ n a s y‖ +
        ‖iteratedFDerivWithin ℝ n b s x - iteratedFDerivWithin ℝ n b s y‖ ≤
        ‖B‖ * (jetDifferenceSumWithin f (fderivWithin ℝ g s) s n x y +
          jetDifferenceSumWithin (fderivWithin ℝ f s) g s n x y) := by
      dsimp only [a, b]
      exact (add_le_add ha' hb').trans (by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (B.norm_precompR_le D)
          (jetDifferenceSumWithin_nonneg _ _ _ _ _ _))
          (mul_le_mul_of_nonneg_right (B.norm_precompL_le D)
            (jetDifferenceSumWithin_nonneg _ _ _ _ _ _)))
    have hnorm : ‖(iteratedFDerivWithin ℝ n a s x + iteratedFDerivWithin ℝ n b s x) -
        (iteratedFDerivWithin ℝ n a s y + iteratedFDerivWithin ℝ n b s y)‖ ≤
        ‖iteratedFDerivWithin ℝ n a s x - iteratedFDerivWithin ℝ n a s y‖ +
        ‖iteratedFDerivWithin ℝ n b s x - iteratedFDerivWithin ℝ n b s y‖ := by
      have he' : (iteratedFDerivWithin ℝ n a s x + iteratedFDerivWithin ℝ n b s x) -
          (iteratedFDerivWithin ℝ n a s y + iteratedFDerivWithin ℝ n b s y) =
          (iteratedFDerivWithin ℝ n a s x - iteratedFDerivWithin ℝ n a s y) +
          (iteratedFDerivWithin ℝ n b s x - iteratedFDerivWithin ℝ n b s y) := by abel
      rw [he']; exact norm_add_le _ _
    apply hnorm.trans (hsum.trans (le_of_eq ?_))
    congr 1
    unfold jetDifferenceSumWithin
    simp_rw [norm_iteratedFDerivWithin_fderivWithin hs hx,
      norm_iteratedFDerivWithin_fderivWithin hs hy,
      norm_iteratedFDerivWithin_fderivWithin_sub _ _ hs hx hy]
    have hright : ∀ i ∈ Finset.range (n + 1), n - i + 1 = n + 1 - i := by
      intro i hi; have := Finset.mem_range.mp hi; omega
    let A := fun i j => ‖iteratedFDerivWithin ℝ i f s x - iteratedFDerivWithin ℝ i f s y‖ *
      ‖iteratedFDerivWithin ℝ j g s x‖ + ‖iteratedFDerivWithin ℝ i f s y‖ *
      ‖iteratedFDerivWithin ℝ j g s x - iteratedFDerivWithin ℝ j g s y‖
    have hchoose := Finset.sum_choose_succ_mul A n
    change _ = ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * A i (n + 1 - i)
    rw [hchoose]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hright i hi]

/-- The global Leibniz estimate for the difference of two actual higher derivatives. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_sub_bilinear_le
    (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (x y : D) :
    ‖iteratedFDeriv ℝ n (fun z => B (f z) (g z)) x -
      iteratedFDeriv ℝ n (fun z => B (f z) (g z)) y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ + ‖iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) g x - iteratedFDeriv ℝ (n - i) g y‖) := by
  simpa only [jetDifferenceSumWithin, iteratedFDerivWithin_univ] using
    B.norm_iteratedFDerivWithin_sub_bilinear_le hf.contDiffOn hg.contDiffOn
      uniqueDiffOn_univ (Set.mem_univ x) (Set.mem_univ y)

section NormSquare
variable {D₀ H : Type} [NormedAddCommGroup D₀] [NormedSpace ℝ D₀]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- The difference of actual higher derivatives of a squared Hilbert norm
is controlled by the residual derivatives on an open domain. -/
theorem norm_iteratedFDeriv_norm_sq_sub_le {f : D₀ → H} {n : ℕ} {s : Set D₀}
    (hf : ContDiffOn ℝ n f s) (hs : IsOpen s) {x y : D₀} (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) x -
      iteratedFDeriv ℝ n (fun z => ‖f z‖ ^ 2) y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖ + ‖iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) f x - iteratedFDeriv ℝ (n - i) f y‖) := by
  have hb := (innerSL ℝ (E := H)).norm_iteratedFDerivWithin_sub_bilinear_le
    hf hf hs.uniqueDiffOn hx hy
  have he : (fun z => innerSL ℝ (f z) (f z)) = fun z => ‖f z‖ ^ 2 := by
    funext z
    exact real_inner_self_eq_norm_sq (f z)
  rw [he, iteratedFDerivWithin_of_isOpen n hs hx,
    iteratedFDerivWithin_of_isOpen n hs hy] at hb
  apply hb.trans
  have hsum := jetDifferenceSumWithin_nonneg f f s n x y
  have hh := mul_le_of_le_one_left hsum (norm_innerSL_le (𝕜 := ℝ) (E := H))
  apply hh.trans_eq
  unfold jetDifferenceSumWithin
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDerivWithin_of_isOpen i hs hx, iteratedFDerivWithin_of_isOpen i hs hy,
    iteratedFDerivWithin_of_isOpen (n - i) hs hx,
    iteratedFDerivWithin_of_isOpen (n - i) hs hy]
end NormSquare
