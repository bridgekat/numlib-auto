/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section10
import Numlib.Analysis.InnerProductSpace.Coercive
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# An extremal property of the Bott–Duffin inverse

Section 3.8 of [benIsrael2003generalized] identifies the stationary
point of a Hermitian quadratic on a subspace. Positive definiteness
makes this point its unique minimum. The primal and dual forms give
the branch voltage and current minima in a direct-current network.

The linear term takes its real part over complex coordinates so the
objective is real valued. The network equations use the
complexification of the real incidence matrix.
-/

namespace BenIsraelGreville.Chapter03

open Matrix
open scoped ComplexOrder InnerProductSpace
open BenIsraelGreville.Chapter02 (orthogonalProjector toEuclideanLin_orthogonalProjector)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real-valued quadratic of **Equation (155)**. -/
noncomputable def bottDuffinQuadratic (A : Matrix n n ℂ)
    (v w x : EuclideanSpace ℂ n) : ℝ :=
  RCLike.re (inner ℂ (x - v) (toEuclideanLin A (x - v))) / 2 - RCLike.re (inner ℂ w x)

/-- The gradient of Equation (155) in the real inner product. -/
noncomputable def bottDuffinQuadraticGradient (A : Matrix n n ℂ)
    (v w x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  toEuclideanLin A (x - v) - w

/-- A stationary point in a subspace has zero directional derivative
along each of its vectors. -/
def IsBottDuffinStationary (L : Submodule ℂ (EuclideanSpace ℂ n))
    (A : Matrix n n ℂ) (v w x : EuclideanSpace ℂ n) : Prop :=
  x ∈ L ∧ ∀ z ∈ L, HasDerivAt
    (fun t : ℝ => bottDuffinQuadratic A v w (x + (t : ℂ) • z)) 0 0

/-- The quadratic's expansion along any real line through a point. -/
theorem bottDuffinQuadratic_line (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (v w x z : EuclideanSpace ℂ n) (t : ℝ) :
    bottDuffinQuadratic A v w (x + (t : ℂ) • z) =
      bottDuffinQuadratic A v w x +
        t * RCLike.re (inner ℂ (bottDuffinQuadraticGradient A v w x) z) +
        t ^ 2 / 2 * RCLike.re (inner ℂ z (toEuclideanLin A z)) := by
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.rclikeToReal ℂ _
  let T := (toEuclideanLin A).restrictScalars ℝ
  let u := x - v
  have hT : (toEuclideanLin A).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have h₁ : inner ℝ u (T z) = inner ℝ (T u) z :=
    congrArg RCLike.re ((hT u z).symm)
  have h₂ : inner ℝ z (T u) = inner ℝ (T u) z := real_inner_comm _ _
  have hdiff : x + t • z - v = u + t • z := by dsimp only [u]; abel
  change inner ℝ (x + t • z - v) (T (x + t • z - v)) / 2 - inner ℝ w (x + t • z) =
    inner ℝ u (T u) / 2 - inner ℝ w x +
      t * inner ℝ (T u - w) z + t ^ 2 / 2 * inner ℝ z (T z)
  simp only [hdiff, map_add, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, h₁, h₂]
  ring

/-- The directional derivative is the real inner product of the gradient
and the direction. -/
theorem bottDuffinQuadratic_hasDerivAt (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (v w x z : EuclideanSpace ℂ n) :
    HasDerivAt (fun t : ℝ => bottDuffinQuadratic A v w (x + (t : ℂ) • z))
      (RCLike.re (inner ℂ (bottDuffinQuadraticGradient A v w x) z)) 0 := by
  simp_rw [bottDuffinQuadratic_line A hA]
  let l := RCLike.re (inner ℂ (bottDuffinQuadraticGradient A v w x) z)
  let q := RCLike.re (inner ℂ z (toEuclideanLin A z))
  have h₁ : HasDerivAt (fun t : ℝ => t * l) l 0 := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const l
  have h₂ : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * q) 0 0 := by
    simpa [Pi.pow_apply] using (((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2).mul_const q
  convert ((hasDerivAt_const 0 (bottDuffinQuadratic A v w x)).add h₁).add h₂ using 1
  simp [l]

/-- Equation (157) expresses stationarity as perpendicularity of the
gradient. -/
theorem isBottDuffinStationary_iff (L : Submodule ℂ (EuclideanSpace ℂ n))
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (v w x : EuclideanSpace ℂ n) :
    IsBottDuffinStationary L A v w x ↔ x ∈ L ∧ bottDuffinQuadraticGradient A v w x ∈ Lᗮ := by
  apply and_congr_right
  intro _
  let g := bottDuffinQuadraticGradient A v w x
  constructor
  · intro h
    apply Submodule.mem_orthogonal _ _ |>.mpr
    intro z hz
    have hr : (inner ℂ g z).re = 0 :=
      (bottDuffinQuadratic_hasDerivAt A hA v w x z).unique (h z hz)
    have hi : (inner ℂ g (Complex.I • z)).re = 0 :=
      (bottDuffinQuadratic_hasDerivAt A hA v w x _).unique (h _ (L.smul_mem _ hz))
    rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, neg_eq_zero] at hi
    exact inner_eq_zero_symm.mp (Complex.ext hr hi)
  · intro hg z hz
    have he : inner ℂ g z = 0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hg z hz)
    simpa only [g, he, map_zero] using bottDuffinQuadratic_hasDerivAt A hA v w x z

private theorem bottDuffin_matrix_apply (A : Matrix n n ℂ)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (u : EuclideanSpace ℂ n) :
    toEuclideanLin (A * orthogonalProjector L + (1 - orthogonalProjector L)) u =
      toEuclideanLin A (L.starProjection u) + (u - L.starProjection u) := by
  rw [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, toEuclideanLin_sub_apply,
    toEuclideanLin_one_apply, toEuclideanLin_orthogonalProjector]
  rfl

private theorem bottDuffin_matrix_isUnit_of_surjective (A : Matrix n n ℂ)
    (L : Submodule ℂ (EuclideanSpace ℂ n))
    (h : Function.Surjective
      (toEuclideanLin (A * orthogonalProjector L + (1 - orthogonalProjector L)))) :
    IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro b
  obtain ⟨u, hu⟩ := h (WithLp.toLp 2 b)
  exact ⟨WithLp.ofLp u, congrArg WithLp.ofLp hu⟩

/-- **Theorem 13** of [benIsrael2003generalized]. The Bott–Duffin inverse
exists exactly when every shifted quadratic on the subspace has a
stationary point. Its unique stationary point is Equation (156). -/
theorem theorem_13 (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    (IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)) ↔
      ∀ v w : EuclideanSpace ℂ n, ∃ x, IsBottDuffinStationary L A v w x) ∧
    (IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)) →
      ∀ v w x, IsBottDuffinStationary L A v w x ↔
        x = toEuclideanLin (Chapter02.definition_3 A L) (toEuclideanLin A v + w)) := by
  have hsolution {v w x : EuclideanSpace ℂ n} :
      IsBottDuffinStationary L A v w x ↔
        x ∈ L ∧ ∃ y ∈ Lᗮ, toEuclideanLin A x + y = toEuclideanLin A v + w := by
    rw [isBottDuffinStationary_iff L A hA]
    apply and_congr_right
    intro _
    let b := toEuclideanLin A v + w
    have hg : bottDuffinQuadraticGradient A v w x = toEuclideanLin A x - b := by
      rw [bottDuffinQuadraticGradient, map_sub, sub_add_eq_sub_sub]
    constructor
    · intro h
      rw [hg] at h
      refine ⟨b - toEuclideanLin A x, by simpa only [neg_sub] using Lᗮ.neg_mem h, ?_⟩
      change toEuclideanLin A x + (b - toEuclideanLin A x) = b
      abel
    · rintro ⟨y, hy, he⟩
      change toEuclideanLin A x + y = b at he
      rw [hg, ← he, sub_add_cancel_left]
      exact Lᗮ.neg_mem hy
  have huniq (hu : IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)))
      (v w x : EuclideanSpace ℂ n) :
      IsBottDuffinStationary L A v w x ↔
        x = toEuclideanLin (Chapter02.definition_3 A L) (toEuclideanLin A v + w) := by
    rw [hsolution]
    have hh := (Chapter02.theorem_16 A L hu).1 (toEuclideanLin A v + w)
    constructor
    · rintro ⟨hx, y, hy, he⟩
      exact (hh.2 x hx y hy he).1
    · rintro rfl
      exact ⟨hh.1.1, _, hh.1.2.1, hh.1.2.2⟩
  refine ⟨⟨fun hu v w => ⟨_, (huniq hu v w _).mpr rfl⟩, ?_⟩, huniq⟩
  intro h
  apply bottDuffin_matrix_isUnit_of_surjective A L
  intro b
  obtain ⟨x, hx⟩ := h 0 b
  obtain ⟨hx', y, hy, hxy⟩ := hsolution.mp hx
  simp only [map_zero, zero_add] at hxy
  refine ⟨x + y, ?_⟩
  rw [bottDuffin_matrix_apply, map_add, L.starProjection_eq_self_iff.mpr hx',
    L.starProjection_apply_eq_zero_iff.mpr hy, add_zero, add_sub_cancel_left, hxy]

/-- Positivity of the matrix guarantees existence of the Bott–Duffin
inverse on any subspace. -/
theorem isUnit_bottDuffin_matrix_of_posDef (A : Matrix n n ℂ) (hA : A.PosDef)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)) := by
  apply bottDuffin_matrix_isUnit_of_surjective A L
  apply LinearMap.injective_iff_surjective.mp
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  change toEuclideanLin (A * orthogonalProjector L + (1 - orthogonalProjector L)) u = 0 at hu
  rw [bottDuffin_matrix_apply] at hu
  let x := L.starProjection u
  let y := u - x
  change toEuclideanLin A x + y = 0 at hu
  have ho : inner ℂ y x = 0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp
      (L.sub_starProjection_mem_orthogonal u) x (L.starProjection_apply_mem u))
  have h := congrArg (fun z => inner ℂ z x) hu
  rw [inner_add_left, ho, add_zero, inner_zero_left] at h
  have hx : x = 0 := by
    by_contra hne
    have hp := hA.isSymmetricCoercive_toEuclideanLin.isCoercive.inner_self_pos hne
    rw [h, map_zero] at hp
    exact (lt_irrefl _ hp)
  simpa only [x, y, hx, map_zero, zero_add, sub_zero] using hu

private theorem quadratic_form_nonneg (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (x : EuclideanSpace ℂ n) : 0 ≤ RCLike.re (inner ℂ x (toEuclideanLin A x)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change 0 ≤ RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x))
  exact (RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg _)).1

/-- A stationary point of a positive semidefinite quadratic is a
minimum, and each subspace minimum is stationary. -/
theorem isBottDuffinStationary_iff_isMinOn (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (v w x : EuclideanSpace ℂ n) :
    IsBottDuffinStationary L A v w x ↔
      x ∈ L ∧ IsMinOn (bottDuffinQuadratic A v w) (L : Set _) x := by
  constructor
  · intro h
    obtain ⟨hx, hg⟩ := (isBottDuffinStationary_iff L A hA.isHermitian v w x).mp h
    refine ⟨hx, fun y hy => ?_⟩
    have hz := L.sub_mem hy hx
    have he := bottDuffinQuadratic_line A hA.isHermitian v w x (y - x) 1
    have ho : inner ℂ (bottDuffinQuadraticGradient A v w x) (y - x) = 0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hg _ hz)
    rw [Complex.ofReal_one, one_smul, show x + (y - x) = y by abel, ho] at he
    have hp := quadratic_form_nonneg A hA (y - x)
    change bottDuffinQuadratic A v w x ≤ bottDuffinQuadratic A v w y
    rw [he, map_zero, mul_zero, add_zero, one_pow]
    linarith
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, fun z hz => ?_⟩
    let f := fun t : ℝ => bottDuffinQuadratic A v w (x + (t : ℂ) • z)
    have h₀ : IsLocalMin f 0 := Filter.Eventually.of_forall fun t => by
      change f 0 ≤ f t
      have ht : bottDuffinQuadratic A v w x ≤ f t :=
        hmin (L.add_mem hx (L.smul_mem (t : ℂ) hz))
      simpa only [f, Complex.ofReal_zero, zero_smul, add_zero] using ht
    have hd := bottDuffinQuadratic_hasDerivAt A hA.isHermitian v w x z
    have he : RCLike.re (inner ℂ (bottDuffinQuadraticGradient A v w x) z) = 0 :=
      hd.deriv.symm.trans h₀.deriv_eq_zero
    rw [he] at hd
    exact hd

/-- **Corollary 8** of [benIsrael2003generalized]. For a positive
definite weight Equation (156) gives the unique minimum. -/
theorem corollary_8 (A : Matrix n n ℂ) (hA : A.PosDef)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (v w x : EuclideanSpace ℂ n) :
    x ∈ L ∧ IsMinOn (bottDuffinQuadratic A v w) (L : Set _) x ↔
      x = toEuclideanLin (Chapter02.definition_3 A L) (toEuclideanLin A v + w) := by
  rw [← isBottDuffinStationary_iff_isMinOn A hA.posSemidef L]
  exact (theorem_13 A hA.isHermitian L).2 (isUnit_bottDuffin_matrix_of_posDef A hA L) _ _ _

/-- **Corollary 9** of [benIsrael2003generalized]. The branch voltage
and current are the unique minimizers of the two network energies.
Each vector is the negative gradient of the other energy at its
minimizer. -/
theorem corollary_9 {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m n ℝ) (a : n → ℝ) (ha : ∀ i, 0 < a i)
    (v w : EuclideanSpace ℂ n) :
    let A : Matrix n n ℂ := diagonal fun i => a i
    let K := (toEuclideanLin (M.map Complex.ofReal)).ker
    let L := LinearMap.range (toEuclideanLin (M.map Complex.ofReal)ᴴ)
    let x := toEuclideanLin (Chapter02.definition_3 A L) (toEuclideanLin A v + w)
    let y := -bottDuffinQuadraticGradient A v w x
    (∀ u, u ∈ L ∧ IsMinOn (bottDuffinQuadratic A v w) (L : Set _) u ↔ u = x) ∧
      (∀ u, u ∈ K ∧ IsMinOn (bottDuffinQuadratic A⁻¹ w v) (K : Set _) u ↔ u = y) ∧
      x = -bottDuffinQuadraticGradient A⁻¹ w v y := by
  intro A K L x y
  have hA : A.PosDef := posDef_diagonal_iff.mpr (fun i => by exact_mod_cast ha i)
  have hL : Kᗮ = L := by
    dsimp only [K, L]
    rw [LinearMap.orthogonal_ker, toEuclideanLin_conjTranspose_eq_adjoint]
  have hx := (theorem_13 A hA.isHermitian L).2
    (isUnit_bottDuffin_matrix_of_posDef A hA L) v w x |>.mpr rfl
  obtain ⟨hxL, hg⟩ := (isBottDuffinStationary_iff L A hA.isHermitian v w x).mp hx
  have hyK : y ∈ K := by
    have h := Lᗮ.neg_mem hg
    rwa [← hL, Submodule.orthogonal_orthogonal] at h
  have he : x = -bottDuffinQuadraticGradient A⁻¹ w v y := by
    have hsub : y - w = -toEuclideanLin A (x - v) := by
      dsimp only [y, bottDuffinQuadraticGradient]
      abel
    rw [bottDuffinQuadraticGradient, hsub, map_neg,
      toEuclideanLin_nonsing_inv_mul_apply hA.isUnit]
    abel
  have hy : IsBottDuffinStationary K A⁻¹ w v y := by
    apply (isBottDuffinStationary_iff K A⁻¹ hA.inv.isHermitian w v y).mpr
    refine ⟨hyK, ?_⟩
    have hn : -bottDuffinQuadraticGradient A⁻¹ w v y ∈ Kᗮ := by rw [← he, hL]; exact hxL
    simpa only [neg_neg] using Kᗮ.neg_mem hn
  have hydef := (theorem_13 A⁻¹ hA.inv.isHermitian K).2
    (isUnit_bottDuffin_matrix_of_posDef A⁻¹ hA.inv K) w v y |>.mp hy
  refine ⟨corollary_8 A hA L v w, fun u => ?_, he⟩
  rw [corollary_8 A⁻¹ hA.inv K w v, ← hydef]

/-- The constrained linear system in Equation (166). -/
def IsBottDuffinSystemSolution (A : Matrix n n ℂ) (L : Submodule ℂ (EuclideanSpace ℂ n))
    (w x : EuclideanSpace ℂ n) : Prop :=
  x ∈ L ∧ toEuclideanLin A x - w ∈ Lᗮ

private theorem bottDuffinSystem_iff_stationary (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (w x : EuclideanSpace ℂ n) :
    IsBottDuffinSystemSolution A L w x ↔ IsBottDuffinStationary L A 0 w x := by
  rw [isBottDuffinStationary_iff L A hA]
  simp only [IsBottDuffinSystemSolution, bottDuffinQuadraticGradient, sub_zero]

/-- **Exercise 82** of [benIsrael2003generalized]. The solutions of the
subspace equation are exactly the minimizers of Equation (165).
The conclusion holds for positive semidefinite matrices. -/
theorem exercise_3_82 (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (w x : EuclideanSpace ℂ n) :
    IsBottDuffinSystemSolution A L w x ↔
      x ∈ L ∧ IsMinOn (bottDuffinQuadratic A 0 w) (L : Set _) x :=
  (bottDuffinSystem_iff_stationary A hA.isHermitian L w x).trans
    (isBottDuffinStationary_iff_isMinOn A hA L 0 w x)

private theorem toEuclideanLin_eq_zero_of_inner_eq_zero (A : Matrix n n ℂ) (hA : A.PosSemidef)
    {x : EuclideanSpace ℂ n} (h : inner ℂ x (toEuclideanLin A x) = 0) :
    toEuclideanLin A x = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  have h' : star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) = 0 := h
  exact (WithLp.ofLp_injective _)
    (hA.dotProduct_mulVec_zero_iff.mp h')

private theorem bottDuffinSystem_exists_iff_kernel (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (w : EuclideanSpace ℂ n) :
    (∃ x, IsBottDuffinSystemSolution A L w x) ↔
      ∀ z ∈ L, toEuclideanLin A z = 0 → inner ℂ w z = 0 := by
  have hSym := isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  constructor
  · rintro ⟨x, _, hx⟩ z hz hAz
    have h := inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hx z hz)
    rw [inner_sub_left, hSym, hAz, inner_zero_right, zero_sub, neg_eq_zero] at h
    exact h
  · intro h
    let P := orthogonalProjector L
    let C := P * A * P
    have hC : C.IsHermitian := by
      have hP := Chapter02.isHermitian_orthogonalProjector L
      change (P * A * P)ᴴ = P * A * P
      rw [conjTranspose_mul, conjTranspose_mul, hA.isHermitian.eq, show Pᴴ = P from hP.eq,
        Matrix.mul_assoc]
    have hCa (u : EuclideanSpace ℂ n) :
        toEuclideanLin C u = L.starProjection (toEuclideanLin A (L.starProjection u)) := by
      dsimp only [C, P]
      simp only [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
      rfl
    have hproj (u v : EuclideanSpace ℂ n) :
        inner ℂ (L.starProjection u) v = inner ℂ u (L.starProjection v) :=
      L.starProjection_isSymmetric u v
    have hrange : (toEuclideanLin C).range = (toEuclideanLin C).kerᗮ := by
      rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint, hC.eq]
    have hb : L.starProjection w ∈ (toEuclideanLin C).range := by
      rw [hrange]
      apply (Submodule.mem_orthogonal _ _).mpr
      intro z hz
      let d := L.starProjection z
      have hd : d ∈ L := L.starProjection_apply_mem z
      have hCd : L.starProjection (toEuclideanLin A d) = 0 := (hCa z).symm.trans hz
      have hzero : inner ℂ d (toEuclideanLin A d) = 0 := calc
        _ = inner ℂ (L.starProjection d) (toEuclideanLin A d) := by
          rw [L.starProjection_eq_self_iff.mpr hd]
        _ = inner ℂ d (L.starProjection (toEuclideanLin A d)) := hproj d _
        _ = 0 := by rw [hCd, inner_zero_right]
      have hAz := toEuclideanLin_eq_zero_of_inner_eq_zero A hA hzero
      rw [← hproj]
      exact inner_eq_zero_symm.mp (h d hd hAz)
    obtain ⟨z, hz⟩ := hb
    refine ⟨L.starProjection z, L.starProjection_apply_mem z, ?_⟩
    rw [← L.starProjection_apply_eq_zero_iff, map_sub, ← hCa, hz, sub_self]

/-- **Exercise 83** of [benIsrael2003generalized]. Consistency,
orthogonality to the null directions, and boundedness from below are
equivalent for the positive semidefinite quadratic. -/
theorem exercise_3_83 (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) (w : EuclideanSpace ℂ n) :
    let q := bottDuffinQuadratic A 0 w
    ((∃ x, IsBottDuffinSystemSolution A L w x) ↔
      ∀ z ∈ L, toEuclideanLin A z = 0 → inner ℂ w z = 0) ∧
    ((∃ x, IsBottDuffinSystemSolution A L w x) ↔ BddBelow (q '' (L : Set _))) := by
  intro q
  have hker := bottDuffinSystem_exists_iff_kernel A hA L w
  refine ⟨hker, ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩
    refine ⟨q x, ?_⟩
    have hm := ((exercise_3_82 A hA L w x).mp hx).2
    rintro _ ⟨y, hy, rfl⟩
    exact hm hy
  · rintro ⟨m, hm⟩
    apply hker.mpr
    have hre (z : EuclideanSpace ℂ n) (hz : z ∈ L) (hAz : toEuclideanLin A z = 0) :
        RCLike.re (inner ℂ w z) = 0 := by
      by_contra hne
      let c := RCLike.re (inner ℂ w z)
      let t : ℝ := (1 - m) / c
      have ht : m ≤ q ((t : ℂ) • z) := hm ⟨_, L.smul_mem _ hz, rfl⟩
      have he : q ((t : ℂ) • z) = -(t * c) := by
        have h := bottDuffinQuadratic_line A hA.isHermitian 0 w 0 z t
        simpa only [q, c, zero_add, sub_zero, bottDuffinQuadraticGradient, map_zero, zero_sub,
          inner_neg_left, map_neg, mul_neg, hAz, inner_zero_right, mul_zero, add_zero,
          bottDuffinQuadratic, zero_div, sub_neg_eq_add] using h
      rw [he, show t * c = 1 - m from div_mul_cancel₀ _ hne] at ht
      linarith
    intro z hz hAz
    have hr : (inner ℂ w z).re = 0 := hre z hz hAz
    have hi : (inner ℂ w (Complex.I • z)).re = 0 := hre _ (L.smul_mem _ hz)
      (by rw [map_smul, hAz, smul_zero])
    rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_eq_zero] at hi
    exact Complex.ext hr hi

/-- **Exercise 84** of [benIsrael2003generalized]. Existence of the
Bott–Duffin inverse is equivalent to unique solvability for each datum,
and its action gives the solution. -/
theorem exercise_3_84 (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    (IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)) ↔
      ∀ w : EuclideanSpace ℂ n, ∃! x, IsBottDuffinSystemSolution A L w x) ∧
    (IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)) →
      ∀ w x, IsBottDuffinSystemSolution A L w x ↔
        x = toEuclideanLin (Chapter02.definition_3 A L) w) := by
  have h := theorem_13 A hA L
  have he (hu : IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L)))
      (w x : EuclideanSpace ℂ n) :
      IsBottDuffinSystemSolution A L w x ↔ x = toEuclideanLin (Chapter02.definition_3 A L) w := by
    rw [bottDuffinSystem_iff_stationary A hA, h.2 hu, map_zero, zero_add]
  refine ⟨⟨fun hu w => ⟨_, (he hu w _).mpr rfl, fun y hy => (he hu w y).mp hy⟩, ?_⟩, he⟩
  intro hs
  apply h.1.mpr
  intro v w
  obtain ⟨x, hx, _⟩ := hs (toEuclideanLin A v + w)
  refine ⟨x, (isBottDuffinStationary_iff L A hA v w x).mpr ⟨hx.1, ?_⟩⟩
  simpa only [bottDuffinQuadraticGradient, map_sub, sub_add_eq_sub_sub] using hx.2

/-- **Exercise 85** of [benIsrael2003generalized]. A consistent
subspace equation has the displayed affine family of solutions,
including when the Bott–Duffin matrix is singular. -/
theorem exercise_3_85 (A : Matrix n n ℂ) (L : Submodule ℂ (EuclideanSpace ℂ n))
    (w x₀ : EuclideanSpace ℂ n) (h₀ : IsBottDuffinSystemSolution A L w x₀)
    (x : EuclideanSpace ℂ n) :
    IsBottDuffinSystemSolution A L w x ↔
      ∃ z ∈ L, toEuclideanLin A z ∈ Lᗮ ∧ x = x₀ + z := by
  constructor
  · intro hx
    refine ⟨x - x₀, L.sub_mem hx.1 h₀.1, ?_, by abel⟩
    have h := Lᗮ.sub_mem hx.2 h₀.2
    simpa only [map_sub, sub_sub_sub_cancel_right] using h
  · rintro ⟨z, hz, hAz, rfl⟩
    refine ⟨L.add_mem h₀.1 hz, ?_⟩
    rw [map_add, add_sub_right_comm]
    exact Lᗮ.add_mem h₀.2 hAz

end BenIsraelGreville.Chapter03
