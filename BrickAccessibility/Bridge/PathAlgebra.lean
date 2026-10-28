module

public import BrickAccessibility.Statement
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# The path algebra of the statement

Basic relations in `kQ` (`Statement.FinQuiver.PathAlgebra`) and the fact that the
elements `e_x · w` (a vertex idempotent times a word of arrows) span `kQ`
(`span_vertex_mul_word`). Algebra homomorphisms out of `kQ` are built with
`liftOfRelations` from images of the generators satisfying the defining relations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility.Statement.FinQuiver

variable (k : Type*) [Field k] (Q : FinQuiver)

theorem vertex_mul_vertex (v w : Q.V) :
    Q.vertex k v * Q.vertex k w = if v = w then Q.vertex k v else 0 := by
  have := RingQuot.mkAlgHom_rel k (PathRel.idem (k := k) (Q := Q) v w)
  simp only [map_mul] at this
  unfold vertex
  rw [this]
  split_ifs <;> simp

theorem sum_vertex : ∑ v, Q.vertex k v = 1 := by
  have := RingQuot.mkAlgHom_rel k (PathRel.one (k := k) (Q := Q))
  simp only [map_sum, map_one] at this
  exact this

theorem vertex_src_mul_arrow (a : Q.A) : Q.vertex k (Q.src a) * Q.arrow k a = Q.arrow k a := by
  have := RingQuot.mkAlgHom_rel k (PathRel.src (k := k) (Q := Q) a)
  simp only [map_mul] at this
  exact this

theorem arrow_mul_vertex_tgt (a : Q.A) : Q.arrow k a * Q.vertex k (Q.tgt a) = Q.arrow k a := by
  have := RingQuot.mkAlgHom_rel k (PathRel.tgt (k := k) (Q := Q) a)
  simp only [map_mul] at this
  exact this

theorem word_append (l₁ l₂ : List Q.A) : Q.word k (l₁ ++ l₂) = Q.word k l₁ * Q.word k l₂ := by
  simp [word, List.prod_append]

@[simp] theorem word_nil : Q.word k [] = 1 := by simp [word]

theorem word_cons (a : Q.A) (l : List Q.A) : Q.word k (a :: l) = Q.arrow k a * Q.word k l := by
  simp [word]

variable {k Q}

/-- An algebra homomorphism out of `kQ` from images of the generators satisfying
the defining relations. -/
def liftOfRelations {R : Type*} [Semiring R] [Algebra k R] (ev : Q.V → R) (ea : Q.A → R)
    (h_idem : ∀ v w, ev v * ev w = if v = w then ev v else 0) (h_one : ∑ v, ev v = 1)
    (h_src : ∀ a, ev (Q.src a) * ea a = ea a) (h_tgt : ∀ a, ea a * ev (Q.tgt a) = ea a) :
    Q.PathAlgebra k →ₐ[k] R :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (Sum.elim ev ea), by
    intro x y h
    cases h with
    | idem v w =>
        simp only [map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, h_idem]
        split_ifs <;> simp
    | one => simp [map_sum, h_one]
    | src a => simp [h_src]
    | tgt a => simp [h_tgt]⟩

theorem liftOfRelations_vertex {R : Type*} [Semiring R] [Algebra k R] (ev : Q.V → R)
    (ea : Q.A → R) (h₁ h₂ h₃ h₄) (v : Q.V) :
    liftOfRelations (k := k) ev ea h₁ h₂ h₃ h₄ (Q.vertex k v) = ev v := by
  simp [liftOfRelations, vertex]

theorem liftOfRelations_arrow {R : Type*} [Semiring R] [Algebra k R] (ev : Q.V → R)
    (ea : Q.A → R) (h₁ h₂ h₃ h₄) (a : Q.A) :
    liftOfRelations (k := k) ev ea h₁ h₂ h₃ h₄ (Q.arrow k a) = ea a := by
  simp [liftOfRelations, arrow]

variable (k Q)

/-- The elements `e_x · w` span `kQ`. -/
theorem span_vertex_mul_word :
    Submodule.span k {y | ∃ (x : Q.V) (l : List Q.A), y = Q.vertex k x * Q.word k l} = ⊤ := by
  classical
  set S := Submodule.span k {y | ∃ (x : Q.V) (l : List Q.A), y = Q.vertex k x * Q.word k l}
  have harr_v : ∀ (b : Q.A) (w : Q.V),
      Q.arrow k b * Q.vertex k w = if Q.tgt b = w then Q.arrow k b else 0 := by
    intro b w
    rw [← arrow_mul_vertex_tgt k Q b, mul_assoc, vertex_mul_vertex]
    split_ifs <;> simp [arrow_mul_vertex_tgt]
  -- right multiplication by a generator preserves `S`
  have hgen : ∀ s ∈ S, ∀ g : Q.Gen, s * RingQuot.mkAlgHom k (PathRel k Q) (FreeAlgebra.ι k g) ∈ S := by
    intro s hs g
    induction hs using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨x, l, rfl⟩ := hy
        cases g with
        | inl w =>
            rcases List.eq_nil_or_concat l with rfl | ⟨l', b, rfl⟩
            · change Q.vertex k x * Q.word k [] * Q.vertex k w ∈ S
              rw [word_nil, mul_one, vertex_mul_vertex]
              split_ifs
              · exact Submodule.subset_span ⟨x, [], by simp⟩
              · exact S.zero_mem
            · rw [List.concat_eq_append]
              change Q.vertex k x * Q.word k (l' ++ [b]) * Q.vertex k w ∈ S
              rw [word_append, word_cons, word_nil, mul_one, mul_assoc, mul_assoc, harr_v]
              split_ifs
              · exact Submodule.subset_span ⟨x, l' ++ [b], by
                  rw [word_append, word_cons, word_nil, mul_one]⟩
              · simp
        | inr a =>
            change Q.vertex k x * Q.word k l * Q.arrow k a ∈ S
            exact Submodule.subset_span ⟨x, l ++ [a], by
              rw [word_append, word_cons, word_nil, mul_one, mul_assoc]⟩
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact S.add_mem hy hz
    | smul c y _ hy => rw [smul_mul_assoc]; exact S.smul_mem c hy
  have hall : ∀ f : FreeAlgebra k Q.Gen, ∀ s ∈ S, s * RingQuot.mkAlgHom k (PathRel k Q) f ∈ S := by
    intro f
    induction f using FreeAlgebra.induction with
    | grade0 c =>
        intro s hs
        rw [AlgHom.commutes, ← Algebra.commutes, ← Algebra.smul_def]
        exact S.smul_mem c hs
    | grade1 g => exact fun s hs ↦ hgen s hs g
    | mul f g hf hg =>
        intro s hs
        rw [map_mul, ← mul_assoc]
        exact hg _ (hf s hs)
    | add f g hf hg =>
        intro s hs
        rw [map_add, mul_add]
        exact S.add_mem (hf s hs) (hg s hs)
  have h1 : (1 : Q.PathAlgebra k) ∈ S := by
    rw [← sum_vertex k Q]
    exact S.sum_mem fun v _ ↦ Submodule.subset_span ⟨v, [], by simp⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨f, rfl⟩ := RingQuot.mkAlgHom_surjective k (PathRel k Q) y
  simpa using hall f 1 h1

end BrickAccessibility.Statement.FinQuiver
