import NumlibSurface.CartisGouldToint.Chapter14.Section01
import Numlib.Optimization.CompositeRegularization

/-!
# Chapter 14, Section 1: actual ARqpC algorithms

Outer transitions use the original nonsmooth composition in both objective and generalized
models. Rejected trials retain the full derivative cache. The detailed inner procedure records
true fraction-of-global-model-decrease provenance and requires evidence for its convexity flag.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter14.Section01
open Optimization.CompositeRegularization
open Optimization.HigherOrderApproximateRegularization (Parameters)

/-- Algorithm 14.1.1 as an actual finite execution. Calls count evaluations of `f` and `c`
separately; derivative calls count individual orders and exclude evaluations of `h`. The last
pass may still continue, so the definition includes no assumed termination conclusion. -/
abbrev algorithm_14_1_1 {n m : ℕ} (P : Parameters) (C : CompositeProblem n m P.p)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ) :=
  OuterExecution P C.f C.c C.h x σ δ N

/-- Algorithm 14.1.2 on the actual smooth parts of the composite regularized model.
The favorable flag contains actual convexity evidence; taking the conservative `false` flag
requires no decision procedure for convexity of the nonsmooth outer function. -/
abbrev algorithm_14_1_2 {n m : ℕ} (P : Parameters) (C : CompositeProblem n m P.p)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (convex : Bool)
    (hconv : convex = true → ConvexOn ℝ Set.univ C.h)
    (minimizer : EuclideanSpace ℝ (Fin n)) (N : ℕ) :=
  InnerExecution P (smoothModel C.f P.p x σ) (vectorModel C.c P.p x)
    C.h convex hconv minimizer N

end CartisGouldToint.Chapter14.Section01
