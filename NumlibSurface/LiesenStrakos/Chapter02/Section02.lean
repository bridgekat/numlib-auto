/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter02.Section01
import Numlib.Krylov.Subspace

/-!
# §2.2. Krylov subspaces and the grade

The search space of a Krylov projection process is the span of $r_0,Ar_0,\ldots,A^{n-1}r_0$.
Its dimension increases up to the grade and then stabilizes [liesen2013krylov].

## Main definitions

* `LiesenStrakos.krylovSubspace` is the span of the first $n$ Krylov vectors.
* `LiesenStrakos.krylovVectorMinimalPolynomial` is the monic vector annihilator of least degree.
* `LiesenStrakos.grade` is the dimension of the full Krylov space.

## Main results

* `LiesenStrakos.lemma_2_2_2` gives dimension and invariance properties at the grade.
* `LiesenStrakos.theorem_2_2_3` gives stabilization and finite termination.
-/

namespace LiesenStrakos

open Polynomial

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The vector minimal polynomial of $v$ for $A$ is the monic generator of the ideal of
polynomials $p$ with $p(A)v=0$. -/
noncomputable abbrev krylovVectorMinimalPolynomial (A : E →ₗ[𝕜] E) (v : E) : 𝕜[X] :=
  Krylov.minpolyVec A v

/-- The grade of $v$ for $A$ is the dimension of the full Krylov subspace. In finite dimension
it is the degree of the vector minimal polynomial. -/
noncomputable abbrev grade (A : E →ₗ[𝕜] E) (v : E) : ℕ := Krylov.grade A v

/-- The subspace in (2.2.2) is the span of $v,Av,\ldots,A^{n-1}v$ for $n>0$ and the zero
subspace for $n=0$. -/
abbrev krylovSubspace (A : E →ₗ[𝕜] E) (v : E) (n : ℕ) : Submodule 𝕜 E :=
  Krylov.subspace A v n

/-- **Lemma 2.2.2** of [liesen2013krylov].
For a vector of positive grade $d$, $\dim \mathcal K_n=n$ through step $d$.
The dimension of $A\mathcal K_d$ is between $d-1$ and $d$. If $A$ is injective, then
$A\mathcal K_d=\mathcal K_d$, and this equality implies $v \in \operatorname{range}(A)$. -/
theorem lemma_2_2_2 [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (v : E)
    (hd : 0 < grade A v) :
    (∀ n ≤ grade A v, Module.finrank 𝕜 (krylovSubspace A v n) = n) ∧
    (grade A v - 1 ≤ Module.finrank 𝕜 ((krylovSubspace A v (grade A v)).map A) ∧
      Module.finrank 𝕜 ((krylovSubspace A v (grade A v)).map A) ≤ grade A v) ∧
    (Function.Injective A →
      (krylovSubspace A v (grade A v)).map A = krylovSubspace A v (grade A v)) ∧
    ((krylovSubspace A v (grade A v)).map A = krylovSubspace A v (grade A v) →
      v ∈ LinearMap.range A) := by
  let d := grade A v
  let K := krylovSubspace A v d
  have hdK : Module.finrank 𝕜 K = d := by simp [K, Krylov.finrank_subspace, d]
  have hAK : K.map A ≤ K := by
    simpa [K, Krylov.subspace_eq_of_grade_le A v (Nat.le_succ d)] using
      Krylov.map_subspace_le A v d
  refine ⟨fun n hn => (Krylov.finrank_subspace A v n).trans (min_eq_left hn),
    ⟨?_, (Submodule.finrank_mono hAK).trans_eq hdK⟩, ?_, ?_⟩
  · have hspan : K ≤ (𝕜 ∙ v) ⊔ K.map A := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      cases hi : (i : ℕ) with
      | zero =>
        exact (le_sup_left : (𝕜 ∙ v) ≤ _) (by simp [hi])
      | succ j =>
        have hj : (A ^ j) v ∈ K := Krylov.pow_apply_mem_subspace A v (by omega)
        apply (le_sup_right : K.map A ≤ _)
        change (A ^ (i : ℕ)) v ∈ K.map A
        rw [hi, pow_succ']
        exact Submodule.mem_map_of_mem hj
    have h₁ := Submodule.finrank_mono hspan
    have h₂ := Submodule.finrank_add_le_finrank_add_finrank (𝕜 ∙ v) (K.map A)
    classical
    have h₃ : Module.finrank 𝕜 (𝕜 ∙ v) ≤ 1 := by
      simpa using finrank_span_le_card (R := 𝕜) ({v} : Set E)
    change d - 1 ≤ Module.finrank 𝕜 (K.map A)
    omega
  · intro hinj
    exact Submodule.eq_of_le_of_finrank_le hAK (by rw [LinearMap.finrank_map_of_injective A hinj])
  · intro heq
    have hv : v ∈ K.map A := by
      rw [heq]
      exact Krylov.self_mem_subspace A v hd
    obtain ⟨w, _, hw⟩ := Submodule.mem_map.1 hv
    exact ⟨w, hw⟩

section Projection

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H]

/-- **Theorem 2.2.3** of [liesen2013krylov].
The residual belongs to the first Krylov subspace when the grade is positive. The Krylov spaces
increase strictly up to the grade and stabilize there. If $A$ is injective and the grade step
is well defined, the iterate at that step has zero residual. -/
theorem theorem_2_2_3 (A : H →ₗ[𝕜] H) (b x₀ : H) :
    let r₀ := b - A x₀
    let d := grade A r₀
    (0 < d → r₀ ∈ krylovSubspace A r₀ 1) ∧
    (∀ n < d, krylovSubspace A r₀ n < krylovSubspace A r₀ (n + 1)) ∧
    (∀ j, krylovSubspace A r₀ (d + j) = krylovSubspace A r₀ d) ∧
    (∀ (C : Submodule 𝕜 H) (x : H), Function.Injective A →
      ProjectionWellDefined A (krylovSubspace A r₀ d) C →
      IsProjectionIterate A b x₀ (krylovSubspace A r₀ d) C x → b - A x = 0) := by
  dsimp only
  refine ⟨fun _ => Krylov.self_mem_subspace A _ Nat.zero_lt_one,
    fun _ hn => Krylov.subspace_strictMono_of_le_grade A _ (Nat.succ_le_of_lt hn), ?_, ?_⟩
  · intro j
    exact Krylov.subspace_eq_of_grade_le A _ (Nat.le_add_right _ _)
  · intro C x hinj hw hx
    by_cases hr : b - A x₀ = 0
    · have hz : IsProjectionIterate A b x₀ (krylovSubspace A (b - A x₀)
          (grade A (b - A x₀))) C x₀ := ⟨by simp, by simp [hr]⟩
      have hu := existsUnique_isPetrovGalerkin_of_isCompl hw hinj.injOn b x₀
      obtain ⟨y, _, hy⟩ := hu
      rw [(hy x hx).trans (hy x₀ hz).symm, hr]
    · have hd := Krylov.grade_pos_of_ne_zero A _ hr
      exact lemma_2_1_7 hw hx (Krylov.self_mem_subspace A _ hd)
        ((lemma_2_2_2 A _ hd).2.2.1 hinj)

end Projection

end LiesenStrakos
