/-
Upstreaming candidate: arbitrary-order Schwarz symmetry under finite smoothness.
Natural home: Mathlib.Analysis.Calculus.FDeriv.Symmetric, alongside the finite C^2 theorem.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

/-!
# Symmetry of finite-order Fréchet derivatives

A real `C^p` function has a symmetric derivative tensor at every order `n ≤ p`.
The proof uses finite smoothness only. Exchanging the first two directions reduces to
second-derivative Schwarz symmetry of the map obtained by evaluating the remaining
derivative tensor on fixed vectors. Exchanging later adjacent directions follows by
differentiating the preceding-order symmetry in a neighborhood. Adjacent transpositions
generate all finite permutations. Neither completeness nor analytic regularity is needed.
-/

open Set Function
open scoped Topology

namespace TaylorModel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- The first two directions of a finite iterated derivative can be interchanged.
The remaining directions are fixed, and only `C^(n + 2)` regularity at the point is used. -/
theorem iteratedFDeriv_swap_first_two {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n + 2 : ℕ) f x) (v w : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons v (Fin.cons w u)) =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons w (Fin.cons v u)) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F u
  let g : E → F := fun y => iteratedFDeriv ℝ n f y u
  have hg : ContDiffAt ℝ 2 g x :=
    L.contDiff.contDiffAt.comp x (hf.iteratedFDeriv_right
      (by exact_mod_cast (show 2 + n ≤ n + 2 by omega)))
  have heq (a : E) : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons a u)) =ᶠ[nhds x]
      (fun y => fderiv ℝ g y a) := by
    filter_upwards [hf.eventually (by
      intro htop
      exact ENat.natCast_ne_top (n + 2) (WithTop.coe_inj.mp htop))] with y hy
    exact (hy.differentiableAt_iteratedFDeriv
      (by exact_mod_cast (show n < n + 2 by omega))).iteratedFDeriv_succ_apply_left'
  have hid := hf.differentiableAt_iteratedFDeriv
    (by exact_mod_cast (show n + 1 < n + 2 by omega))
  have hformula (a b : E) :
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b u)) =
        fderiv ℝ (fderiv ℝ g) x a b := by
    rw [hid.iteratedFDeriv_succ_apply_left']
    simp only [Fin.tail_cons, Fin.cons_zero]
    rw [(heq b).fderiv_eq, fderiv_clm_apply
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one (differentiableAt_const b)]
    simp
  rw [hformula, hformula]
  exact (hg.isSymmSndFDerivAt (by norm_num)).eq v w

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
private theorem comp_perm_of_adjacent {n : ℕ} (A : (Fin (n + 1) → E) → F)
    (hA : ∀ i : Fin n, ∀ v, A (v ∘ Equiv.swap i.castSucc i.succ) = A v)
    (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) : A (v ∘ σ) = A v := by
  let M : Submonoid (Equiv.Perm (Fin (n + 1))) := {
    carrier := {σ | ∀ v, A (v ∘ σ) = A v}
    one_mem' := by intro v; rfl
    mul_mem' := by
      intro a b ha hb v
      exact (hb (v ∘ a)).trans (ha v) }
  have hM : Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ M := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hA i
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hM
  exact hM (by trivial : σ ∈ (⊤ : Submonoid _)) v

private theorem iteratedFDeriv_comp_perm_finite (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  induction n using Nat.twoStepInduction generalizing x with
  | zero => simp
  | one =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    simp [hσ]
  | more n _ih0 ih1 =>
    apply comp_perm_of_adjacent _ ?_ v σ
    intro i w
    refine Fin.cases ?_ (fun j => ?_) i
    · have hvec : w ∘ Equiv.swap (0 : Fin (n + 1)).castSucc (0 : Fin (n + 1)).succ =
          Fin.cons (w 1) (Fin.cons (w 0) (Fin.tail (Fin.tail w))) := by
        funext k
        refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => ?_) l) k
        · simp
        · simp
        · simp [Equiv.swap_apply_def, Fin.tail, Fin.succ_succ_ne_one]
      rw [hvec]
      have hh := iteratedFDeriv_swap_first_two hf (w 1) (w 0) (Fin.tail (Fin.tail w))
      have heta : Fin.cons (w 0) (Fin.cons (w 1) (Fin.tail (Fin.tail w))) = w := by
        change Fin.cons (w 0) (Fin.cons ((Fin.tail w) 0) (Fin.tail (Fin.tail w))) = w
        rw [Fin.cons_self_tail, Fin.cons_self_tail]
      exact hh.trans (congrArg (iteratedFDeriv ℝ (n + 2) f x) heta)
    · let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j.castSucc j.succ
      let τ' : Equiv.Perm (Fin (n + 2)) := Equiv.swap j.succ.castSucc j.succ.succ
      have hhead : (w ∘ τ') 0 = w 0 := by
        simp [τ', Equiv.swap_apply_def, Fin.ext_iff]
      have htail : Fin.tail (w ∘ τ') = Fin.tail w ∘ τ := by
        funext l
        simp only [τ', τ, Fin.tail, Function.comp_apply, Fin.castSucc_succ,
          Equiv.swap_apply_def, Fin.succ_inj]
        split_ifs <;> rfl
      have heq : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail w ∘ τ)) =ᶠ[nhds x]
          (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail w)) := by
        filter_upwards [hf.eventually (by
          intro htop
          exact ENat.natCast_ne_top (n + 2) (WithTop.coe_inj.mp htop))] with y hy
        exact ih1 (hy.of_le (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))) (Fin.tail w) τ
      have hid := hf.differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show n + 1 < n + 2 by omega))
      change iteratedFDeriv ℝ (n + 2) f x (w ∘ τ') = iteratedFDeriv ℝ (n + 2) f x w
      rw [hid.iteratedFDeriv_succ_apply_left', hid.iteratedFDeriv_succ_apply_left',
        hhead, htail, heq.fderiv_eq]

/-- The actual `n`-th Fréchet derivative of a real `C^p` map is invariant under every
permutation of its directions whenever `n ≤ p`. -/
theorem iteratedFDeriv_comp_perm {f : E → F} {p n : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hn : n ≤ p) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v :=
  iteratedFDeriv_comp_perm_finite n (hf.of_le (by exact_mod_cast hn)) v σ

/-- Permuting the domains leaves the finite derivative tensor unchanged. -/
theorem domDomCongr_iteratedFDeriv {f : E → F} {p n : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hn : n ≤ p) (σ : Equiv.Perm (Fin n)) :
    (iteratedFDeriv ℝ n f x).domDomCongr σ = iteratedFDeriv ℝ n f x := by
  ext v
  exact iteratedFDeriv_comp_perm hf hn v σ
end TaylorModel

namespace TaylorModel
universe u v

/-- Isometric postcomposition commutes with every iterated derivative, including
at points where the function is not differentiable. -/
theorem iteratedFDeriv_comp_isometryEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F ≃ₗᵢ[ℝ] G) (f : E → F) (q : ℕ) (x : E) (u : Fin q → E) :
    iteratedFDeriv ℝ q (L ∘ f) x u = L (iteratedFDeriv ℝ q f x u) := by
  change iteratedFDeriv ℝ q (L.toContinuousLinearEquiv ∘ f) x u = _
  rw [L.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
  rfl

variable {E : Type u} {F : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- The inner-order induction, in a codomain universe large enough to contain
its spaces of continuous linear maps. -/
private theorem iteratedFDeriv_iteratedFDeriv_of_universe_le
    (f : E → F) (q j : ℕ) (x : E) (u : Fin q → E) (v : Fin j → E) :
    iteratedFDeriv ℝ q (iteratedFDeriv ℝ j f) x u v =
      iteratedFDeriv ℝ (q + j) f x (Fin.append u v) := by
  induction j generalizing F q with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    have heq := iteratedFDeriv_comp_isometryEquiv
      (continuousMultilinearCurryFin0 ℝ E F).symm f q x u
    rw [heq]
    simp only [continuousMultilinearCurryFin0_symm_apply_apply, Nat.add_zero]
    congr 1
    simpa using (Fin.append_right_nil u v rfl).symm
  | succ j ih =>
    rw [show iteratedFDeriv ℝ (j + 1) f =
      (continuousMultilinearCurryRightEquiv' ℝ j E F).symm ∘
        iteratedFDeriv ℝ j (fderiv ℝ f) by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right]
    have heq := iteratedFDeriv_comp_isometryEquiv
      (continuousMultilinearCurryRightEquiv' ℝ j E F).symm (iteratedFDeriv ℝ j (fderiv ℝ f)) q x u
    rw [heq]
    change iteratedFDeriv ℝ q (iteratedFDeriv ℝ j (fderiv ℝ f)) x u (Fin.init v)
      (v (Fin.last j)) = _
    rw [ih]
    have h := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := f) (x := x)
      (Fin.snoc (Fin.append u (Fin.init v)) (v (Fin.last j)))
    simp only [Fin.init_snoc, Fin.snoc_last] at h
    simp only [← Fin.append_snoc, Fin.snoc_init_self] at h
    convert h.symm using 1
end TaylorModel
namespace TaylorModel
universe uE uF
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Canonical currying identifies the genuine iterated derivatives of a
derivative-valued map. The first block contains the outer differentiation directions.
The fixed curry isometries make this true without a smoothness hypothesis. -/
theorem iteratedFDeriv_iteratedFDeriv (f : E → F) (q j : ℕ) (x : E)
    (u : Fin q → E) (v : Fin j → E) :
    iteratedFDeriv ℝ q (iteratedFDeriv ℝ j f) x u v =
      iteratedFDeriv ℝ (q + j) f x (Fin.append u v) := by
  -- Lift only the codomain for the induction, then transport back isometrically.
  let L : F ≃ₗᵢ[ℝ] ULift.{uE} F := (LinearIsometryEquiv.ulift ℝ F).symm
  let : SeminormedAddCommGroup (E [×j]→L[ℝ] F) :=
    (inferInstance : NormedAddCommGroup (E [×j]→L[ℝ] F)).toSeminormedAddCommGroup
  let : SeminormedAddCommGroup (E [×j]→L[ℝ] ULift.{uE} F) :=
    (inferInstance : NormedAddCommGroup (E [×j]→L[ℝ] ULift.{uE} F)).toSeminormedAddCommGroup
  let K : (E [×j]→L[ℝ] F) ≃ₗᵢ[ℝ] (E [×j]→L[ℝ] ULift.{uE} F) :=
    { L.toContinuousLinearEquiv.continuousMultilinearMapCongrRight (fun _ : Fin j => E) with
      norm_map' := fun A => L.toLinearIsometry.norm_compContinuousMultilinearMap A }
  have heq : iteratedFDeriv ℝ j (L ∘ f) = K ∘ iteratedFDeriv ℝ j f := by
    funext y
    apply ContinuousMultilinearMap.ext
    intro w
    exact iteratedFDeriv_comp_isometryEquiv L f j y w
  have h := iteratedFDeriv_iteratedFDeriv_of_universe_le.{uE,uF} (L ∘ f) q j x u v
  rw [heq] at h
  have hK := iteratedFDeriv_comp_isometryEquiv K (iteratedFDeriv ℝ j f) q x u
  rw [hK, iteratedFDeriv_comp_isometryEquiv L] at h
  exact L.injective h
end TaylorModel
