import Mathlib.Data.List.Count
import Mathlib.Basic.Real.Basic

/-!
# Exact scalar arithmetic with an operation trace

Each arithmetic primitive appends exactly its own operation to the trace. Comparisons,
index arithmetic, allocation, copying, and control flow are not scalar arithmetic operations.
-/

universe u

namespace ArithmeticTrace

/-- The four charged scalar arithmetic operations. -/
inductive Operation where
  | add | sub | mul | div
  deriving DecidableEq

/-- A computed value and the scalar operations used to obtain it. -/
structure Computation (α : Type*) where
  value : α
  trace : List Operation

instance : Monad Computation where
  pure a := ⟨a, []⟩
  bind a f := ⟨(f a.value).value, a.trace ++ (f a.value).trace⟩

/-- Addition records one scalar addition. -/
def add (a b : ℝ) : Computation ℝ := ⟨a + b, [.add]⟩

/-- Subtraction records one scalar subtraction. -/
def sub (a b : ℝ) : Computation ℝ := ⟨a - b, [.sub]⟩

/-- Multiplication records one scalar multiplication. -/
def mul (a b : ℝ) : Computation ℝ := ⟨a * b, [.mul]⟩

/-- Division records one scalar division. -/
noncomputable def div (a b : ℝ) : Computation ℝ := ⟨a / b, [.div]⟩

/-- The number of operations of one selected kind in a computation. -/
def Computation.count {α : Type*} (c : Computation α) (op : Operation) : ℕ := c.trace.count op

/-- A pure computation returns its supplied value. -/
@[simp] theorem value_pure {α : Type*} (a : α) : (pure a : Computation α).value = a := rfl

/-- A pure computation charges no arithmetic operations. -/
@[simp] theorem trace_pure {α : Type*} (a : α) : (pure a : Computation α).trace = [] := rfl

/-- Sequencing computes the continuation on the first computation's value. -/
@[simp] theorem value_bind {α β : Type u} (a : Computation α) (f : α → Computation β) :
    (a >>= f).value = (f a.value).value := rfl

/-- Sequencing concatenates the two computations' operation traces. -/
@[simp] theorem trace_bind {α β : Type u} (a : Computation α) (f : α → Computation β) :
    (a >>= f).trace = a.trace ++ (f a.value).trace := rfl

end ArithmeticTrace
