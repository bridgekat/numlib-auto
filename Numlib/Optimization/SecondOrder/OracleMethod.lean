import Numlib.Optimization.SecondOrder.QuadraticConvergence
import Numlib.Analysis.Calculus.IteratedDeriv.Bounded
import Numlib.Approximation.Hermite.FiniteData

/-!
# Scalar second-order methods with actual finite oracle histories

A deterministic method sees only sampled objective values and actual first and
second derivatives. Its recursive execution is separate from the primitive
shifted-Newton admissibility conditions. Finite interpolation can therefore
realize an adversarial oracle history without giving the method the objective
function itself or assuming its resulting trajectory.
-/

namespace ShiftedNewton

/-- One genuine scalar second-order oracle observation. -/
structure ScalarEvaluation where
  point : ℝ
  value : ℝ
  first : ℝ
  second : ℝ

/-- The actual value and ordinary derivatives at a scalar query. -/
noncomputable def scalarOracle (f : ℝ → ℝ) (x : ℝ) : ScalarEvaluation :=
  ⟨x,f x,deriv f x,iteratedDeriv 2 f x⟩

/-- A deterministic method chooses the next scalar point from its complete finite oracle history. -/
structure ScalarMethod where
  next : (k : ℕ) → (Fin (k + 1) → ScalarEvaluation) → ℝ

/-- The actual recursive execution of a scalar method starts at zero. -/
noncomputable def ScalarMethod.iterates (M : ScalarMethod) (f : ℝ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => M.next k (fun i => scalarOracle f (M.iterates f i.val))
termination_by k => k

/-- The initialized scalar oracle execution starts at the specified origin. -/
@[simp] theorem ScalarMethod.iterates_zero (M : ScalarMethod) (f : ℝ → ℝ) :
    M.iterates f 0 = 0 := by rw [ScalarMethod.iterates]

/-- Every actual next point uses exactly the already evaluated finite history. -/
theorem ScalarMethod.iterates_succ (M : ScalarMethod) (f : ℝ → ℝ) (k : ℕ) :
    M.iterates f (k + 1) =
      M.next k (fun i => scalarOracle f (M.iterates f i.val)) := by
  rw [ScalarMethod.iterates]

/-- A finite prescribed oracle history agrees with actual observations when
all prescribed points and all three genuine scalar jets agree. -/
def ScalarMatches (f : ℝ → ℝ) (D : ℕ → ScalarEvaluation) (N : ℕ) : Prop :=
  ∀ i ≤ N, f (D i).point = (D i).value ∧ deriv f (D i).point = (D i).first ∧
    iteratedDeriv 2 f (D i).point = (D i).second

/-- Genuine matching jets give equality of the full oracle records. -/
theorem ScalarMatches.oracle_eq {f : ℝ → ℝ} {D : ℕ → ScalarEvaluation} {N : ℕ}
    (h : ScalarMatches f D N) {i : ℕ} (hi : i ≤ N) :
    scalarOracle f (D i).point = D i := by
  rcases h i hi with ⟨hv,hg,hH⟩
  cases hD : D i
  simp only [scalarOracle,hD] at *
  simp only [hv,hg,hH]

/-- A method's recursively generated prescribed history becomes its actual
execution after a genuine objective realizes every recorded jet. -/
theorem ScalarMethod.iterates_eq_of_matches (M : ScalarMethod) {f : ℝ → ℝ}
    {D : ℕ → ScalarEvaluation} {N : ℕ} (h0 : (D 0).point = 0)
    (hnext : ∀ k < N, (D (k + 1)).point = M.next k (fun i => D i.val))
    (hmatch : ScalarMatches f D N) : ∀ i ≤ N, M.iterates f i = (D i).point := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    cases i with
    | zero => simpa using h0.symm
    | succ k =>
      rw [M.iterates_succ,hnext k (by omega)]
      congr 1
      funext j
      rw [ih j.val (by have := j.isLt; omega) (by have := j.isLt; omega)]
      exact hmatch.oracle_eq (by have := j.isLt; omega)

/-- The source scalar objective class has actual continuous second derivatives,
a finite lower bound, and globally Lipschitz first and second derivatives. -/
def ScalarObjectiveClass (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ (∃ flow : ℝ, ∀ x, flow ≤ f x) ∧
    (∃ G ≥ 0, ∀ x y, |deriv f x - deriv f y| ≤ G * |x - y|) ∧
    ∃ L ≥ 0, ∀ x y, |iteratedDeriv 2 f x - iteratedDeriv 2 f y| ≤ L * |x - y|

/-- Primitive second-order admissibility at every nonterminated actual query.
The multiplier and residual are allowed to depend on the full method history;
no step bound, progress, termination time or interpolation conclusion is assumed. -/
structure IsScalarMethodClass (M : ScalarMethod) (ε κrg κrs κlambda : ℝ) : Prop where
  residual_fraction_nonneg : 0 ≤ κrg
  residual_fraction_lt_one : κrg < 1
  residual_step_pos : 0 < κrs
  spectral_gt_one : 1 < κlambda
  step : ∀ f, ScalarObjectiveClass f → ∀ k,
    ε < |deriv f (M.iterates f k)| →
    let x := M.iterates f k
    let s := M.iterates f (k + 1) - x
    ∃ lambda r : ℝ, 0 ≤ lambda ∧
      0 ≤ iteratedDeriv 2 f x + lambda ∧
      (iteratedDeriv 2 f x + lambda) * s = -deriv f x + r ∧
      |r| ≤ min (κrg * |deriv f x|) (κrs * |s| ^ 2) ∧
      iteratedDeriv 2 f x + lambda ≤
        κlambda * max |iteratedDeriv 2 f x| (Real.sqrt |deriv f x|)


/-- Actual bounded scalar jets and a Lipschitz highest derivative give exactly
the source objective class; no derivative regularity is inferred from formal jet data. -/
theorem scalarObjectiveClass_of_bounded_jets {f : ℝ → ℝ} {B : ℝ} {L : NNReal}
    (hf : ContDiff ℝ 2 f) (hB : 0 ≤ B)
    (hjets : ∀ j ≤ 2, ∀ x, |iteratedDeriv j f x| ≤ B)
    (hLip : LipschitzWith L (iteratedDeriv 2 f)) : ScalarObjectiveClass f := by
  have hcommon := norm_iteratedFDeriv_sub_le_of_bounded_jets hf hB
    (fun j hj x => by simpa only [Real.norm_eq_abs] using hjets j hj x)
    (fun x y => hLip.norm_sub_le x y)
  refine ⟨hf,⟨-B,?_⟩,⟨max B L,hB.trans (le_max_left _ _),?_⟩,
    ⟨L,L.coe_nonneg,?_⟩⟩
  · intro x
    simpa only [iteratedDeriv_zero] using (abs_le.mp (hjets 0 (by decide) x)).1
  · intro x y
    have hh := hcommon 1 (by decide) x y
    simpa only [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub,iteratedDeriv_one,
      Real.norm_eq_abs] using hh
  · intro x y
    simpa only [Real.norm_eq_abs] using hLip.norm_sub_le x y

/-- Every arbitrary finite scalar jet history at strictly increasing points is
realized by a genuine globally bounded objective in the method's source class. -/
theorem exists_scalar_objective_interpolating (n : ℕ) (hn : 0 < n)
    (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ)
    (hx : ∀ i j, i < j → j ≤ n → x i < x j) :
    ∃ f : ℝ → ℝ, ScalarObjectiveClass f ∧
      ∀ k ≤ n, ∀ j ≤ 2, iteratedDeriv j f (x k) = a k j := by
  obtain ⟨f,L,B,hB,hf,hLip,hmatch,hbound⟩ :=
    Hermite.exists_bounded_finite_interpolant 2 n hn x a hx
  exact ⟨f,scalarObjectiveClass_of_bounded_jets hf hB.le hbound hLip,hmatch⟩

/-- Arbitrary finite oracle records at strictly increasing points beginning at
zero are realized by an actual objective in the source second-order class. -/
theorem exists_objective_matches_scalar_history (D : ℕ → ScalarEvaluation) (N : ℕ)
    (hzero : (D 0).point = 0)
    (hinc : ∀ i j, i < j → j ≤ N → (D i).point < (D j).point) :
    ∃ f : ℝ → ℝ, ScalarObjectiveClass f ∧ ScalarMatches f D N := by
  let grid := fun k => if k = 0 then (-1 : ℝ) else (D (k - 1)).point
  let jets := fun k j => if k = 0 then (0 : ℝ) else
    if j = 0 then (D (k - 1)).value else if j = 1 then (D (k - 1)).first else (D (k - 1)).second
  have hnonneg : ∀ k ≤ N, 0 ≤ (D k).point := by
    intro k hk
    by_cases he : k = 0
    · simpa only [he,hzero] using (le_refl (0 : ℝ))
    · rw [←hzero]
      exact (hinc 0 k (by omega) hk).le
  have hg : ∀ i j, i < j → j ≤ N + 1 → grid i < grid j := by
    intro i j hij hj
    have hj0 : j ≠ 0 := by omega
    by_cases hi0 : i = 0
    · subst i
      simp only [grid,ite_true,ite_eq_right hj0]
      linarith [hnonneg (j - 1) (by omega)]
    · simp only [grid,ite_eq_right hi0,ite_eq_right hj0]
      exact hinc (i - 1) (j - 1) (by omega) (by omega)
  obtain ⟨f,hf,hm⟩ := exists_scalar_objective_interpolating (N + 1) (by omega) grid jets hg
  refine ⟨f,hf,?_⟩
  intro k hk
  refine ⟨?_,?_,?_⟩
  · simpa [grid,jets] using hm (k + 1) (by omega) 0 (by decide)
  · simpa [grid,jets] using hm (k + 1) (by omega) 1 (by decide)
  · simpa [grid,jets] using hm (k + 1) (by omega) 2 (by decide)

/-- One further actual method step already agrees with a realized finite
history; realizing the new endpoint's jets is not needed to determine it. -/
theorem ScalarMethod.next_eq_of_matches (M : ScalarMethod) {f : ℝ → ℝ}
    {D : ℕ → ScalarEvaluation} {N : ℕ} (h0 : (D 0).point = 0)
    (hnext : ∀ k ≤ N, (D (k + 1)).point = M.next k (fun i => D i.val))
    (hm : ScalarMatches f D N) : M.iterates f (N + 1) = (D (N + 1)).point := by
  rw [M.iterates_succ,hnext N le_rfl]
  congr 1
  funext j
  have hj : j.val ≤ N := by have := j.isLt; omega
  rw [M.iterates_eq_of_matches h0 (fun k hk => hnext k hk.le) hm j.val hj]
  exact hm.oracle_eq hj

/-- A concrete deterministic positive-shift Newton controller depends only on
the final record of its complete finite oracle history. -/
noncomputable def stabilizedScalarNewton : ScalarMethod where
  next k history :=
    let d := history (Fin.last k)
    d.point - d.first / max d.second (Real.sqrt |d.first|)

/-- The concrete positive-shift controller has a genuine actual next-point rule. -/
theorem stabilizedScalarNewton_next (f : ℝ → ℝ) (k : ℕ) :
    stabilizedScalarNewton.iterates f (k + 1) =
      let x := stabilizedScalarNewton.iterates f k
      x - deriv f x / max (iteratedDeriv 2 f x) (Real.sqrt |deriv f x|) := by
  rw [ScalarMethod.iterates_succ]
  rfl

/-- The actual second-order controller belongs to the primitive method class,
so that the universal admissible method quantifier is inhabited. -/
theorem stabilizedScalarNewton_isScalarMethodClass {ε : ℝ} (hε : 0 < ε) :
    IsScalarMethodClass stabilizedScalarNewton ε 0 1 2 := by
  refine ⟨le_rfl,by norm_num,by norm_num,by norm_num,?_⟩
  intro f _ k hfail
  dsimp only
  let x := stabilizedScalarNewton.iterates f k
  let g := deriv f x
  let H := iteratedDeriv 2 f x
  let d := max H (Real.sqrt |g|)
  have hg : 0 < |g| := hε.trans hfail
  have hd : 0 < d := (Real.sqrt_pos.mpr hg).trans_le (le_max_right _ _)
  have hshift : 0 ≤ d - H := sub_nonneg.mpr (le_max_left _ _)
  have he : H + (d - H)=d := by ring
  have hstep : stabilizedScalarNewton.iterates f (k + 1) - x = -g / d := by
    rw [stabilizedScalarNewton_next]
    dsimp [x,g,H,d]
    ring
  refine ⟨d - H,0,hshift,by rw [he];exact hd.le,?_,?_,?_⟩
  · rw [he,hstep]
    field_simp
    simp [g,x]
  · simp only [abs_zero,zero_mul,one_mul,le_min_iff]
    exact ⟨le_rfl,sq_nonneg _⟩
  · rw [he]
    have hm : d ≤ max |H| (Real.sqrt |g|) := max_le
      ((le_abs_self H).trans (le_max_left _ _)) (le_max_right _ _)
    have hmax : 0 ≤ max |H| (Real.sqrt |g|) :=
      (abs_nonneg H).trans (le_max_left _ _)
    linarith

end ShiftedNewton
