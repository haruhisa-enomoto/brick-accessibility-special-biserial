module

public import BrickAccessibility.Statement
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Quiver data inside an algebra

`PathData Q A` records vertex idempotents `e v` and arrow elements `α a` of a
ring `A`. Modules are left `A`-modules: the arrow `a` maps `e (src a) M`
to `e (tgt a) M`. For a right module over `Λ = kQ/I` this is `A = Λᵐᵒᵖ`.

A path is a start vertex `x` together with a list of arrows in traversal order;
its value `pval x l = α aₙ ⋯ α a₁ e x` is in composition order. Lists that are
not composable have value zero. The data assumes that the path values span `A`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

/-- The end vertex of a list of arrows started at `x` (the last target). -/
def Statement.FinQuiver.pend (Q : FinQuiver) : Q.V → List Q.A → Q.V
  | x, [] => x
  | _, a :: l => pend Q (Q.tgt a) l

variable (Q : FinQuiver) (A : Type*) [Ring A]

/-- Vertex idempotents and arrow elements for the quiver `Q` inside `A`. -/
structure PathData where
  /-- Vertex idempotents. -/
  e : Q.V → A
  /-- Arrow elements. -/
  α : Q.A → A
  e_mul_e : ∀ v w, e v * e w = if v = w then e v else 0
  sum_e : ∑ v, e v = 1
  α_mul_e : ∀ a, α a * e (Q.src a) = α a
  e_mul_α : ∀ a, e (Q.tgt a) * α a = α a

namespace PathData

variable {Q A} (D : PathData Q A)

/-- The value of a path, in composition order. Non-composable lists give zero. -/
def pval : Q.V → List Q.A → A
  | x, [] => D.e x
  | x, a :: l => pval (Q.tgt a) l * D.α a * D.e x

theorem e_idem (v : Q.V) : D.e v * D.e v = D.e v := by simp [D.e_mul_e]

theorem e_mul_e_of_ne {v w : Q.V} (h : v ≠ w) : D.e v * D.e w = 0 := by simp [D.e_mul_e, h]

theorem pval_mul_e (x : Q.V) (l : List Q.A) : D.pval x l * D.e x = D.pval x l := by
  cases l with
  | nil => exact D.e_idem x
  | cons a l => simp only [pval, mul_assoc, D.e_idem]

theorem e_pend_mul_pval (x : Q.V) (l : List Q.A) :
    D.e (Q.pend x l) * D.pval x l = D.pval x l := by
  induction l generalizing x with
  | nil => exact D.e_idem x
  | cons a l ih =>
      simp only [FinQuiver.pend, pval, ← mul_assoc]
      rw [ih]

/-- Concatenation multiplies values in composition order. -/
theorem pval_append (x : Q.V) (l₁ l₂ : List Q.A) :
    D.pval x (l₁ ++ l₂) = D.pval (Q.pend x l₁) l₂ * D.pval x l₁ := by
  induction l₁ generalizing x with
  | nil => simp [FinQuiver.pend, pval, D.pval_mul_e]
  | cons a l ih =>
      simp only [List.cons_append, pval, FinQuiver.pend, ih, mul_assoc]

/-- Values of non-composable paths multiply to zero. -/
theorem pval_mul_pval_of_ne {x y : Q.V} (l₁ l₂ : List Q.A) (h : y ≠ Q.pend x l₁) :
    D.pval y l₂ * D.pval x l₁ = 0 := by
  rw [← D.pval_mul_e y l₂, ← D.e_pend_mul_pval x l₁, mul_assoc, ← mul_assoc (D.e y),
    D.e_mul_e_of_ne h, zero_mul, mul_zero]

/-- The product of two path values is the value of the concatenation or zero. -/
theorem pval_mul_pval (x y : Q.V) (l₁ l₂ : List Q.A) :
    D.pval y l₂ * D.pval x l₁ = if y = Q.pend x l₁ then D.pval x (l₁ ++ l₂) else 0 := by
  split_ifs with h
  · rw [D.pval_append, h]
  · exact D.pval_mul_pval_of_ne l₁ l₂ h

theorem pval_single (x : Q.V) (a : Q.A) : D.pval x [a] = D.α a * D.e x := by
  simp only [pval, ← mul_assoc]
  rw [D.e_mul_α]

theorem pval_single_src (a : Q.A) : D.pval (Q.src a) [a] = D.α a := by
  rw [pval_single, D.α_mul_e]

/-- A path starting at a vertex different from the source of its first arrow is zero. -/
theorem pval_cons_of_ne {x : Q.V} {a : Q.A} (l : List Q.A) (h : Q.src a ≠ x) :
    D.pval x (a :: l) = 0 := by
  simp only [pval]
  rw [← D.α_mul_e a, mul_assoc (D.pval _ l), mul_assoc, D.e_mul_e_of_ne h, mul_zero, mul_zero]

end PathData

end BrickAccessibility
