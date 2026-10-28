module

public import BrickAccessibility.Classification.BlockWalks

/-!
# Dimensions of the pair functors on block quiver modules

`dim F_{h,h'}(P → V) = #{p : p ∈ h⁺ \ h⁻ and p ∈ h'⁺ \ h'⁻} · dim V`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
variable (C : D.BlockQuiver V) (hC : C.KillsZeroPaths)

namespace BlockQuiver

theorem blk_le_iff [Nontrivial V] {J J' : C.P → Prop} :
    C.blk hC J ≤ C.blk hC J' ↔ ∀ p, J p → J' p := by
  constructor
  · intro h p hp
    by_contra hp'
    obtain ⟨y, hy⟩ := exists_ne (0 : V)
    have := h (C.single_mem_blk hC hp y) p hp'
    simp at this
    exact hy this
  · exact C.blk_mono hC

variable (S : Signs D)

/-- Positions in `h⁺ \ h⁻`. -/
def PM (v : D.Q.V) (s : Bool) (h : HWord D.Q) (p : C.P) : Prop :=
  C.plusSet S v s h p ∧ ¬ C.minusSet S v s h p

open Classical in
theorem gr_eq [FiniteDimensional k V] {v : D.Q.V} {s : Bool} {h h' : HWord D.Q}
    (hv : S.Valid v s h) (hv' : S.Valid v (!s) h') :
    finrank k (S.pnum (C.Mod hC) v s h h') - finrank k (S.pden (C.Mod hC) v s h h') =
      (Finset.univ.filter fun p ↦ C.PM S v s h p ∧ C.PM S v (!s) h' p).card * finrank k V := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : finrank k V = 0 := finrank_zero_of_subsingleton
    have h1 : finrank k (S.pnum (C.Mod hC) v s h h') = 0 := by
      apply Submodule.finrank_eq_zero.mpr
      refine eq_bot_iff.mpr fun f _ ↦ (Submodule.mem_bot k).mpr (C.ext_val hC fun j ↦ ?_)
      exact Subsingleton.elim _ _
    rw [h1, this]; simp
  · set P := C.plusSet S v s h
    set Mi := C.minusSet S v s h
    set P' := C.plusSet S v (!s) h'
    set Mi' := C.minusSet S v (!s) h'
    have hMP : ∀ p, Mi p → P p := by
      rw [← C.blk_le_iff hC, ← C.minus_eq_blk, ← C.plus_eq_blk]
      exact S.minus_le_plus hv
    have hMP' : ∀ p, Mi' p → P' p := by
      rw [← C.blk_le_iff hC, ← C.minus_eq_blk, ← C.plus_eq_blk]
      exact S.minus_le_plus hv'
    have hnum : S.pnum (C.Mod hC) v s h h' = C.blk hC (fun p ↦ P p ∧ P' p) := by
      rw [Signs.pnum, C.plus_eq_blk, C.plus_eq_blk, C.blk_inf]
    have hden : S.pden (C.Mod hC) v s h h' =
        C.blk hC (fun p ↦ (Mi p ∧ P' p) ∨ (P p ∧ Mi' p)) := by
      rw [Signs.pden, C.plus_eq_blk, C.plus_eq_blk, C.minus_eq_blk, C.minus_eq_blk, C.blk_inf,
        C.blk_inf, C.blk_sup]
    rw [hnum, hden, C.finrank_blk, C.finrank_blk, ← Nat.sub_mul]
    congr 1
    have hsub : (Finset.univ.filter fun p ↦ (Mi p ∧ P' p) ∨ (P p ∧ Mi' p)) ⊆
        Finset.univ.filter fun p ↦ P p ∧ P' p := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hMP p h1, h2⟩
      · exact ⟨h1, hMP' p h2⟩
    rw [← Finset.card_sdiff_of_subset hsub]
    congr 1
    ext p
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    unfold PM
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      push Not at h3
      exact ⟨⟨h1, fun hm ↦ h3.1 hm h2⟩, ⟨h2, h3.2 h1⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, by push Not; exact ⟨fun hm ↦ absurd hm h2, fun _ ↦ h4⟩⟩

end BlockQuiver

end MonomialData

end BrickAccessibility
