module

public import BrickAccessibility.Quiver.Classes

/-!
# Path data on a quotient by a two-sided ideal

Given path data in `B` and a two-sided ideal `I`, the vertices and arrows outside
`I` form a quiver, and their images give path data in `B ⧸ I`
(`subPathData`), with path values the images of the original ones
(`subPathData_pval`). Every path outside `I` lifts (`exists_lift`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable (D : MonomialData k B) (I : Ideal B) [I.IsTwoSided]

open Classical in
/-- The quiver of vertices and arrows outside `I`. -/
@[reducible] def subQuiver : FinQuiver where
  V := {v : D.Q.V // D.e v ∉ I}
  A := {a : D.Q.A // D.α a ∉ I}
  src a := ⟨D.Q.src a.1, fun h ↦ a.2 (by
    have key : D.α a.1 = D.α a.1 * D.e (D.Q.src a.1) := (D.toPathData.α_mul_e a.1).symm
    rw [key]; exact I.mul_mem_left _ h)⟩
  tgt a := ⟨D.Q.tgt a.1, fun h ↦ a.2 (by
    have key : D.α a.1 = D.e (D.Q.tgt a.1) * D.α a.1 := (D.toPathData.e_mul_α a.1).symm
    rw [key]; exact I.mul_mem_right _ h)⟩

@[simp] theorem subQuiver_src_val (a : (D.subQuiver I).A) :
    ((D.subQuiver I).src a).1 = D.Q.src a.1 := rfl

@[simp] theorem subQuiver_tgt_val (a : (D.subQuiver I).A) :
    ((D.subQuiver I).tgt a).1 = D.Q.tgt a.1 := rfl

/-- The path data of the quotient. -/
def subPathData : PathData (D.subQuiver I) (B ⧸ I) where
  e v := Ideal.Quotient.mk I (D.e v.1)
  α a := Ideal.Quotient.mk I (D.α a.1)
  e_mul_e v w := by
    change Ideal.Quotient.mk I (D.e v.1) * Ideal.Quotient.mk I (D.e w.1) =
      if v = w then Ideal.Quotient.mk I (D.e v.1) else 0
    rw [← map_mul, D.toPathData.e_mul_e]
    by_cases h : v = w
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun h' ↦ h (Subtype.ext h')), map_zero]
  sum_e := by
    classical
    have h1 : ∑ v : D.Q.V, Ideal.Quotient.mk I (D.e v) = 1 := by
      rw [← map_sum, D.toPathData.sum_e, map_one]
    have h2 : ∑ v : {v : D.Q.V // ¬ (D.e v ∉ I)}, Ideal.Quotient.mk I (D.e v.1) = 0 :=
      Finset.sum_eq_zero fun v _ ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (not_not.mp v.2)
    have h3 := Fintype.sum_subtype_add_sum_subtype (fun v ↦ D.e v ∉ I)
      (fun v ↦ Ideal.Quotient.mk I (D.e v))
    rw [h2, add_zero, h1] at h3
    rw [← h3]
    try exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ ↦ rfl)
  α_mul_e a := by
    change Ideal.Quotient.mk I (D.α a.1) * Ideal.Quotient.mk I (D.e (D.Q.src a.1)) = _
    rw [← map_mul, D.toPathData.α_mul_e]
  e_mul_α a := by
    change Ideal.Quotient.mk I (D.e (D.Q.tgt a.1)) * Ideal.Quotient.mk I (D.α a.1) = _
    rw [← map_mul, D.toPathData.e_mul_α]

theorem subPathData_pval (x : (D.subQuiver I).V) (l : List (D.subQuiver I).A) :
    (D.subPathData I).pval x l = Ideal.Quotient.mk I (D.pval x.1 (l.map Subtype.val)) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
      simp only [PathData.pval]
      rw [ih]
      change _ * Ideal.Quotient.mk I (D.α a.1) * Ideal.Quotient.mk I (D.e x.1) = _
      rw [← map_mul, ← map_mul]
      rfl

omit [I.IsTwoSided] in
theorem pval_mem_of_vertex {x : D.Q.V} (hx : D.e x ∈ I) (l : List D.Q.A) : D.pval x l ∈ I := by
  have key : D.pval x l = D.pval x l * D.e x := (D.toPathData.pval_mul_e x l).symm
  rw [key]; exact I.mul_mem_left _ hx

/-- Paths outside `I` lift to the quotient quiver. -/
theorem exists_lift : ∀ (x : D.Q.V) (l : List D.Q.A), D.pval x l ∉ I →
    ∃ (hx : D.e x ∉ I) (l' : List (D.subQuiver I).A), l'.map Subtype.val = l := by
  intro x l
  induction l generalizing x with
  | nil => intro h; exact ⟨h, [], rfl⟩
  | cons a l ih =>
      intro h
      have hx : D.e x ∉ I := fun hx ↦ h (D.pval_mem_of_vertex I hx _)
      have hp : D.pval (D.Q.tgt a) l ∉ I := fun hp ↦ h (by
        change D.pval (D.Q.tgt a) l * D.α a * D.e x ∈ I
        exact I.mul_mem_right _ (I.mul_mem_right _ hp))
      have ha : D.α a ∉ I := fun ha ↦ h (by
        change D.pval (D.Q.tgt a) l * D.α a * D.e x ∈ I
        exact I.mul_mem_right _ (I.mul_mem_left _ ha))
      obtain ⟨-, l', hl'⟩ := ih _ hp
      refine ⟨hx, (⟨a, ha⟩ : (D.subQuiver I).A) :: l', ?_⟩
      exact congrArg (List.cons a) hl'

end MonomialData

end BrickAccessibility
