module

public import BrickAccessibility.Section4.Deficit

/-!
# Lemma 4.6: a positive endpoint coordinate

For a nonsimple brick string module `M(w)` over a representation-finite gentle
algebra, some vertex `v` satisfies `dim Ext¹(M, S_v) < dim Hom(S_v, M)` or
`dim Ext¹(S_v, M) < dim Hom(M, S_v)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- **Lemma 4.6**, combined with the bounds of Lemma 4.3. -/
theorem exists_positive_coordinate [IsAlgClosed k] [FiniteDimensional k B] (D : MonomialData k B)
    (hD : D.IsGentle) (hrep : IsRepFinite B) (w : Word D.Q) (hw : w.IsString D)
    (hb : IsBrick B (w.stringModule D hw)) (hns : ¬ IsSimpleModule B (w.stringModule D hw)) :
    ∃ v : D.Q.V,
      finrank k (Ext1 k B (w.stringModule D hw) (D.simple v)) <
          finrank k (D.simple v →ₗ[B] w.stringModule D hw) ∨
        finrank k (Ext1 k B (D.simple v) (w.stringModule D hw)) <
          finrank k (w.stringModule D hw →ₗ[B] D.simple v) := by
  classical
  set C := w.coeffQuiver D
  have hC := hw.2
  have hinj : C.InjMoves := fun a i i' j h h' ↦ w.next_injective hw.1 h h'
  have hcoef : C.CoefNe := fun _ _ _ _ ↦ one_ne_zero
  -- the string has positive length
  have hn : 0 < w.len := by
    by_contra h0
    apply hns
    refine isSimpleModule_of_finrank_eq_one (k := k) ?_
    show Module.finrank k (Fin (w.len + 1) → k) = 1
    rw [Module.finrank_fin_fun]
    omega
  -- no vertex carries both a top and a socle position (equation (2.1))
  have hts : ∀ p q, (∀ a i, w.next a i ≠ some p) → (∀ a, w.next a q = none) →
      w.vtx p ≠ w.vtx q := by
    intro p q hp hq hpq
    set v := w.vtx p
    have h1 : 0 < finrank k (w.stringModule D hw →ₗ[B] D.simple v) := by
      rw [D.finrank_hom_to_simple, C.finrank_K0 hC hcoef]
      exact Fintype.card_pos_iff.mpr ⟨⟨p, rfl, hp⟩⟩
    have h2 : 0 < finrank k (D.simple v →ₗ[B] w.stringModule D hw) := by
      rw [D.finrank_hom_simple, C.finrank_K0' hC hinj hcoef]
      exact Fintype.card_pos_iff.mpr ⟨⟨q, hpq.symm, hq⟩⟩
    obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h1
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
    exact hg (hb.hom_eq_zero_of_ne_zero hns hf g)
  obtain ⟨v, hv | hv⟩ := exists_ext_deficit hD hrep w hw hn hts
  · refine ⟨v, Or.inl ?_⟩
    have hineq := w.socle_ineq hD.1.2 hw hn v
    have hext := D.finrank_ext1_simple_le (w.stringModule D hw) v
    have e1 : finrank k (D.E0 (w.stringModule D hw) v) = Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} :=
      (C.finrank_E0 hC v).trans (Fintype.card_congr (Equiv.refl _))
    have e2 : finrank k (D.K0 (w.stringModule D hw) v) =
        Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} :=
      (C.finrank_K0 hC hcoef v).trans (Fintype.card_congr (Equiv.refl _))
    have e3 : ∀ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb (w.stringModule D hw) b.1) =
        Fintype.card {q : Fin (w.len + 1) // w.vtx q = D.Q.src b.1 ∧
          ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q} :=
      fun b ↦ (C.finrank_Zb hC hcoef b.1).trans (Fintype.card_congr (Equiv.refl _))
    have e4 : finrank k (D.simple v →ₗ[B] w.stringModule D hw) =
        Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} :=
      (D.finrank_hom_simple _ v).trans
        ((C.finrank_K0' hC hinj hcoef v).trans (Fintype.card_congr (Equiv.refl _)))
    rw [e1, e2, Finset.sum_congr rfl fun b _ ↦ e3 b] at hext
    rw [e4]
    omega
  · refine ⟨v, Or.inr ?_⟩
    have hineq := w.top_ineq hD.1.2 hw hn v
    have hext := D.finrank_ext1_simple_left_le (w.stringModule D hw) v
    have e1 : finrank k (D.E0' (w.stringModule D hw) v) = Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} :=
      (C.finrank_E0' hC v).trans (Fintype.card_congr (Equiv.refl _))
    have e2 : finrank k (D.K0' (w.stringModule D hw) v) =
        Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} :=
      (C.finrank_K0' hC hinj hcoef v).trans (Fintype.card_congr (Equiv.refl _))
    have e3 : ∀ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb (w.stringModule D hw) b.1) =
        Fintype.card {q : Fin (w.len + 1) // w.vtx q = D.Q.tgt b.1 ∧
          ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none} :=
      fun b ↦ (C.finrank_Yb hC hinj hcoef b.1).trans (Fintype.card_congr (Equiv.refl _))
    have e4 : finrank k (w.stringModule D hw →ₗ[B] D.simple v) =
        Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} :=
      (D.finrank_hom_to_simple _ v).trans
        ((C.finrank_K0 hC hcoef v).trans (Fintype.card_congr (Equiv.refl _)))
    rw [e1, e2, Finset.sum_congr rfl fun b _ ↦ e3 b] at hext
    rw [e4]
    omega

end BrickAccessibility
