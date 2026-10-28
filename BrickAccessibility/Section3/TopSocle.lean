module

public import BrickAccessibility.Section4.Counts
public import BrickAccessibility.Section4.StringLocal

/-!
# Top and socle positions of a brick string module

Equation (2.1) in combinatorial form: in the string diagram of a brick string
module of positive length, a position without incoming edges and a position
without outgoing edges lie over different vertices.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hw : w.IsString D)

theorem finrank_stringModule : finrank k (w.stringModule D hw) = w.len + 1 :=
  (Module.finrank_fin_fun k : finrank k (Fin (w.len + 1) → k) = _)

/-- Equation (2.1) for string modules. -/
theorem vtx_ne_of_top_socle (hb : IsBrick B (w.stringModule D hw)) (hn : 0 < w.len)
    (p q : Fin (w.len + 1)) (hp : ∀ a i, w.next a i ≠ some p) (hq : ∀ a, w.next a q = none) :
    w.vtx p ≠ w.vtx q := by
  classical
  set C := w.coeffQuiver D
  have hC := hw.2
  have hinj : C.InjMoves := fun a i i' j h h' ↦ w.next_injective hw.1 h h'
  have hcoef : C.CoefNe := fun _ _ _ _ ↦ one_ne_zero
  intro hpq
  set v := w.vtx p
  have h1 : 0 < finrank k (w.stringModule D hw →ₗ[B] D.simple v) := by
    rw [D.finrank_hom_to_simple, C.finrank_K0 hC hcoef]
    exact Fintype.card_pos_iff.mpr ⟨⟨p, rfl, hp⟩⟩
  have h2 : 0 < finrank k (D.simple v →ₗ[B] w.stringModule D hw) := by
    rw [D.finrank_hom_simple, C.finrank_K0' hC hinj hcoef]
    exact Fintype.card_pos_iff.mpr ⟨⟨q, hpq.symm, hq⟩⟩
  obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h1
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
  have hns : ¬ IsSimpleModule B (w.stringModule D hw) := by
    intro hs
    have hsurj : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      refine (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range f)).resolve_left fun h ↦ hf ?_
      exact LinearMap.range_eq_bot.mp h
    have := LinearMap.finrank_range_le (f.restrictScalars k)
    rw [LinearMap.range_eq_top.mpr (by exact hsurj), finrank_top, D.finrank_simple,
      w.finrank_stringModule hw] at this
    omega
  exact hg (hb.hom_eq_zero_of_ne_zero hns hf g)

end Word

end BrickAccessibility
