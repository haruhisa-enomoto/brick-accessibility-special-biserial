module

public import BrickAccessibility.Bridge.PathAlgebra
public import BrickAccessibility.Quiver.Classes
public import Mathlib.Data.Matrix.Basis

/-!
# From an admissible presentation to path data

An admissible presentation `π : kQ → Λ` of the statement gives path data on
`A = Λᵐᵒᵖ` (right `Λ`-modules are left `A`-modules): `e v = op (π e_v)` and
`α a = op (π a)`. Path values are `op (π (e_x · w))` (`pval_eq`), they span `A`
(`span_pval`), the data is admissible (`isAdmissible`; nonvanishing of vertices
and arrows is detected by two small representations of `kQ` that kill all words
of length at least two), and the special biserial conditions transfer
(`isSpecialBiserial`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility.Statement

open MulOpposite

universe u

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]

namespace AdmissiblePresentation

variable (P : AdmissiblePresentation k Λ)

/-- The path data on `Λᵐᵒᵖ` of a presentation. -/
def toPathData : PathData P.Q Λᵐᵒᵖ where
  e v := op (P.π (P.Q.vertex k v))
  α a := op (P.π (P.Q.arrow k a))
  e_mul_e v w := by
    rw [← op_mul, ← map_mul, FinQuiver.vertex_mul_vertex]
    by_cases h : w = v
    · subst h; simp
    · simp [h, Ne.symm h]
  sum_e := by
    have : (∑ v, op (P.π (P.Q.vertex k v)) : Λᵐᵒᵖ) = op (∑ v, P.π (P.Q.vertex k v)) :=
      (map_sum (opAddEquiv : Λ ≃+ Λᵐᵒᵖ) _ _).symm
    rw [this, ← map_sum, FinQuiver.sum_vertex, map_one, op_one]
  α_mul_e a := by rw [← op_mul, ← map_mul, FinQuiver.vertex_src_mul_arrow]
  e_mul_α a := by rw [← op_mul, ← map_mul, FinQuiver.arrow_mul_vertex_tgt]

theorem pval_eq (x : P.Q.V) (l : List P.Q.A) :
    P.toPathData.pval x l = op (P.π (P.Q.vertex k x * P.Q.word k l)) := by
  induction l generalizing x with
  | nil => simp [PathData.pval, toPathData]
  | cons a l ih =>
      simp only [PathData.pval, ih]
      simp only [toPathData, ← op_mul, ← map_mul]
      congr 2
      rw [FinQuiver.word_cons, ← mul_assoc, ← mul_assoc, mul_assoc _ (P.Q.arrow k a),
        FinQuiver.arrow_mul_vertex_tgt, mul_assoc]

theorem span_pval : Submodule.span k
    (Set.range (fun p : P.Q.V × List P.Q.A ↦ P.toPathData.pval p.1 p.2)) = ⊤ := by
  let f : P.Q.PathAlgebra k →ₗ[k] Λᵐᵒᵖ := (opLinearEquiv k).toLinearMap ∘ₗ P.π.toLinearMap
  have hf : Function.Surjective f := (opLinearEquiv k).surjective.comp P.surjective
  have h := congrArg (Submodule.map f) (FinQuiver.span_vertex_mul_word k P.Q)
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hf] at h
  rw [← h]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨x, l, rfl⟩
    exact ⟨_, ⟨x, l, rfl⟩, by simp [f, pval_eq]⟩
  · rintro ⟨_, ⟨x, l, rfl⟩, rfl⟩
    exact ⟨x, l, by simp [f, pval_eq]⟩

/-- An algebra map killing all words of length at least two kills the kernel of
an admissible presentation. -/
theorem map_eq_zero_of_ker {R : Type*} [Semiring R] [Algebra k R] (φ : P.Q.PathAlgebra k →ₐ[k] R)
    (hφ : ∀ l : List P.Q.A, 2 ≤ l.length → φ (P.Q.word k l) = 0) {z : P.Q.PathAlgebra k}
    (hz : P.π z = 0) : φ z = 0 := by
  have hmem := P.ker_le_sq z hz
  clear hz
  induction hmem using Submodule.span_induction with
  | mem y hy => obtain ⟨l, hl, rfl⟩ := hy; exact hφ l hl
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem isAdmissible : P.toPathData.IsAdmissible := by
  classical
  refine ⟨fun v hv ↦ ?_, fun a ha ↦ ?_, ?_⟩
  · -- the simple representation at `v`
    let φ := FinQuiver.liftOfRelations (k := k) (Q := P.Q) (R := k)
      (fun w ↦ if w = v then 1 else 0) (fun _ ↦ 0)
      (by intro w w'; by_cases h : w = v <;> by_cases h' : w' = v <;> simp [h, h'] <;> aesop)
      (by simp) (by simp) (by simp)
    have hφ : ∀ l : List P.Q.A, 2 ≤ l.length → φ (P.Q.word k l) = 0 := by
      intro l hl
      obtain ⟨b, l', rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < l.length)
      rw [FinQuiver.word_cons, map_mul, FinQuiver.liftOfRelations_arrow, zero_mul]
    have hz : P.π (P.Q.vertex k v) = 0 := by
      have : op (P.π (P.Q.vertex k v)) = 0 := hv
      simpa using this
    have := P.map_eq_zero_of_ker φ hφ hz
    rw [FinQuiver.liftOfRelations_vertex] at this
    simp at this
  · -- a two-dimensional representation in which `a` acts nonzero
    let ev : P.Q.V → Matrix (Fin 2) (Fin 2) k := fun w ↦
      !![if w = P.Q.src a then 1 else 0, 0; 0, if w = P.Q.tgt a then 1 else 0]
    let ea : P.Q.A → Matrix (Fin 2) (Fin 2) k := fun b ↦ !![0, if b = a then 1 else 0; 0, 0]
    let φ := FinQuiver.liftOfRelations (k := k) (Q := P.Q) ev ea
      (by
        intro w w'
        by_cases h : w = w'
        · subst h
          ext i j; fin_cases i <;> fin_cases j <;> simp [ev, Matrix.mul_fin_two] <;> aesop
        · rw [if_neg h]
          ext i j; fin_cases i <;> fin_cases j <;> simp [ev, Matrix.mul_fin_two] <;> aesop)
      (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ev, Matrix.sum_apply, Finset.sum_ite_eq'])
      (by
        intro b
        ext i j; fin_cases i <;> fin_cases j <;> simp [ev, ea, Matrix.mul_fin_two] <;> aesop)
      (by
        intro b
        ext i j; fin_cases i <;> fin_cases j <;> simp [ev, ea, Matrix.mul_fin_two] <;> aesop)
    have hφ : ∀ l : List P.Q.A, 2 ≤ l.length → φ (P.Q.word k l) = 0 := by
      intro l hl
      obtain ⟨b, l', rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < l.length)
      obtain ⟨b', l'', rfl⟩ := List.exists_cons_of_length_pos (by simp at hl; omega : 0 < l'.length)
      rw [FinQuiver.word_cons, FinQuiver.word_cons, map_mul, map_mul,
        FinQuiver.liftOfRelations_arrow, FinQuiver.liftOfRelations_arrow, ← mul_assoc]
      have : ea b * ea b' = 0 := by
        simp only [ea, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
      rw [this, zero_mul]
    have hz : P.π (P.Q.arrow k a) = 0 := by
      have : op (P.π (P.Q.arrow k a)) = 0 := ha
      simpa using this
    have := P.map_eq_zero_of_ker φ hφ hz
    rw [FinQuiver.liftOfRelations_arrow] at this
    have h01 := congrFun (congrFun this 0) 1
    simp [ea] at h01
  · obtain ⟨m, _, hm⟩ := P.nilpotent
    refine ⟨m, fun x l hl ↦ ?_⟩
    rw [pval_eq]
    have : P.Q.word k l = P.Q.word k (l.take m) * P.Q.word k (l.drop m) := by
      rw [← FinQuiver.word_append, List.take_append_drop]
    rw [this, map_mul, map_mul, hm (l.take m) (by rw [List.length_take]; omega), zero_mul,
      mul_zero, op_zero]

theorem pval_pair (a b : P.Q.A) :
    P.toPathData.pval (P.Q.src a) [a, b] = op (P.arr a * P.arr b) := by
  rw [pval_eq, FinQuiver.word_cons, FinQuiver.word_cons, FinQuiver.word_nil, mul_one,
    ← mul_assoc, FinQuiver.vertex_src_mul_arrow, map_mul]
  rfl

theorem isSpecialBiserial (hP : P.IsSpecialBiserial) : P.toPathData.IsSpecialBiserial := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨h1, h2, fun a ↦ ?_, fun b ↦ ?_⟩
  · refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ ?_)) (h3 a)
    simp only [PathData.Allowed, pval_pair, ne_eq, op_eq_zero_iff]
  · refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ ?_)) (h4 b)
    simp only [PathData.Allowed, pval_pair, ne_eq, op_eq_zero_iff]
    exact and_congr_left' eq_comm

end AdmissiblePresentation

end BrickAccessibility.Statement
