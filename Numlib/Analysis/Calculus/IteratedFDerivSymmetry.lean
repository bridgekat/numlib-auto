import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign

/-!
# Symmetry of finite-order derivatives

Finite smoothness over the reals suffices to permute the arguments of an iterated
Fréchet derivative. The proof starts with Schwarz's theorem and propagates adjacent
transpositions by differentiation. Currying also preserves norms of tensor differences.
-/

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two leading slots of an iterated derivative commute under finite smoothness. -/
theorem ContDiffAt.iteratedFDeriv_cons_cons_swap {f : E → F} {n : ℕ} {x : E}
    (hf : ContDiffAt ℝ (n + 2) f x) (v w : E) (m : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons v (Fin.cons w m)) =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons w (Fin.cons v m)) := by
  have hG : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by norm_cast; omega)
  have hsym := hG.isSymmSndFDerivAt (by simp)
  change (fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) x v) (Fin.cons w m) =
    (fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) x w) (Fin.cons v m)
  rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
  simpa using congrArg (fun A ↦ A m) (hsym v w)

/-- Permutation identities for the derivative tensors near a point persist after
adding a leading derivative direction. -/
theorem iteratedFDeriv_cons_congr_of_eventuallyEq {f : E → F} {n : ℕ} {x : E}
    (hf : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x) (v : E) (m m' : Fin n → E)
    (he : (fun y ↦ iteratedFDeriv ℝ n f y m) =ᶠ[nhds x]
      (fun y ↦ iteratedFDeriv ℝ n f y m')) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons v m) =
      iteratedFDeriv ℝ (n + 1) f x (Fin.cons v m') := by
  rw [hf.iteratedFDeriv_succ_apply_left', hf.iteratedFDeriv_succ_apply_left']
  simpa using congrArg (fun D ↦ D v) (he.fderiv_eq (𝕜 := ℝ))

/-- Any adjacent pair of slots in an iterated derivative commutes under finite smoothness. -/
theorem ContDiffAt.iteratedFDeriv_comp_adjacent_swap {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n + 1) f x) (i : Fin n) (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n + 1) f x v := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · have h := hf.iteratedFDeriv_cons_cons_swap (v 1) (v 0) (Fin.tail (Fin.tail v))
      convert h using 2
      · funext j
        refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j) j
        · simp
        · simp
        · simp [Equiv.swap_apply_def, Fin.tail, Fin.succ_ne_zero]
          rfl
      · funext j
        refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j) j <;> rfl
    · have he : (fun y ↦ iteratedFDeriv ℝ (n + 1) f y
          (Fin.tail v ∘ Equiv.swap i.castSucc i.succ)) =ᶠ[nhds x]
          (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.tail v)) := by
        filter_upwards [(hf.of_le (m := (n + 1 : ℕ))
          (by norm_cast; omega)).eventually (by simp)] with y hy
        exact ih hy i (Fin.tail v)
      have h := iteratedFDeriv_cons_congr_of_eventuallyEq
        (hf.differentiableAt_iteratedFDeriv (by norm_cast; omega)) (v 0) _ _ he
      convert h using 2
      · funext j
        refine Fin.cases ?_ (fun j ↦ ?_) j
        · simp [Function.comp_def, Equiv.swap_apply_def, Fin.succ_ne_zero, eq_comm]
        · simp only [Function.comp_def, Equiv.swap_apply_def, Fin.succ_inj, Fin.tail,
            Fin.cons_succ, ← Fin.succ_castSucc]
          split_ifs <;> congr 1
      · exact (Fin.cons_self_tail v).symm


/-- The iterated Fréchet derivative of a finitely smooth real map is symmetric. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_nat {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  cases n with
  | zero => congr 1; exact Subsingleton.elim _ _
  | succ n =>
    have hσ : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n ↦ Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    have h : ∀ v : Fin (n + 1) → E,
        iteratedFDeriv ℝ (n + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (n + 1) f x v := by
      induction hσ using Submonoid.closure_induction with
      | mem a ha =>
        rcases ha with ⟨i, rfl⟩
        exact fun v ↦ hf.iteratedFDeriv_comp_adjacent_swap i v
      | one => intro v; rfl
      | mul a b ha hb iha ihb =>
        intro v
        change iteratedFDeriv ℝ (n + 1) f x ((v ∘ a) ∘ b) = _
        rw [ihb, iha]
    exact h v

/-- Currying preserves the norm of the difference between two derivative tensors. -/
theorem norm_iteratedFDeriv_sub_eq_fderiv_sub {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : E → F) (n : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) g y‖ =
      ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ g) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]

/-- Zeroth derivatives preserve differences and their norms. -/
theorem norm_iteratedFDeriv_zero_sub {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g y‖ = ‖f x - g y‖ := by
  change ‖(continuousMultilinearCurryFin0 ℝ E F).symm (f x) -
    (continuousMultilinearCurryFin0 ℝ E F).symm (g y)‖ = _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
