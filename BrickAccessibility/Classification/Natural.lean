module

public import BrickAccessibility.Classification.Shift

/-!
# Naturality of the boundary subspaces

Module homomorphisms map `h⁺` into `h⁺` and `h⁻` into `h⁻`, hence the numerator
and denominator of each pair functor into the corresponding ones.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module k N] [IsScalarTower k B N]
variable (f : M →ₗ[B] N)

theorem Signs.map_Kc_le (u : D.Q.V) (n : Bool) :
    (S.Kc M u n).map (f.restrictScalars k) ≤ S.Kc N u n := by
  rintro _ ⟨x, ⟨hxv, hxK⟩, rfl⟩
  refine ⟨D.map_vsp_le f u ⟨x, hxv, rfl⟩, ?_⟩
  refine Submodule.mem_iInf _ |>.mpr fun b ↦ Submodule.mem_iInf _ |>.mpr fun hb ↦ ?_
  have := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hxK b) hb
  change D.α b • f x = 0
  rw [← f.map_smul]
  change D.α b • x = 0 at this
  rw [this, map_zero]

theorem Signs.map_Ic_le (u : D.Q.V) (n : Bool) :
    (S.Ic M u n).map (f.restrictScalars k) ≤ S.Ic N u n := by
  rw [Signs.Ic, Submodule.map_iSup]
  refine iSup_le fun d ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hd ↦ le_iSup₂_of_le d hd ?_
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨f y, by simp⟩

theorem Signs.map_plus_le (v : D.Q.V) (s : Bool) (h : HWord D.Q) :
    (S.plus M v s h).map (f.restrictScalars k) ≤ S.plus N v s h := by
  cases h with
  | fin C => exact (D.map_trs_le f C _).trans (D.trs_mono C (S.map_Kc_le f _ _))
  | inf g =>
      refine le_iInf fun n ↦ (Submodule.map_mono (iInf_le _ n)).trans ?_
      exact (D.map_trs_le f _ _).trans (D.trs_mono _ (D.map_vsp_le f _))

theorem Signs.map_minus_le (v : D.Q.V) (s : Bool) (h : HWord D.Q) :
    (S.minus M v s h).map (f.restrictScalars k) ≤ S.minus N v s h := by
  cases h with
  | fin C => exact (D.map_trs_le f C _).trans (D.trs_mono C (S.map_Ic_le f _ _))
  | inf g =>
      simp only [Signs.minus]
      rw [Submodule.map_iSup]
      refine iSup_le fun n ↦ le_iSup_of_le n ((D.map_trs_le f _ _).trans ?_)
      rw [Submodule.map_bot]

variable (M) in
theorem Signs.map_pnum_le (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) :
    (S.pnum M v s h h').map (f.restrictScalars k) ≤ S.pnum N v s h h' :=
  (Submodule.map_inf_le _).trans (inf_le_inf (S.map_plus_le f _ _ _) (S.map_plus_le f _ _ _))

variable (M) in
theorem Signs.map_pden_le (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) :
    (S.pden M v s h h').map (f.restrictScalars k) ≤ S.pden N v s h h' := by
  rw [Signs.pden, Submodule.map_sup]
  exact sup_le_sup
    ((Submodule.map_inf_le _).trans (inf_le_inf (S.map_minus_le f _ _ _) (S.map_plus_le f _ _ _)))
    ((Submodule.map_inf_le _).trans (inf_le_inf (S.map_plus_le f _ _ _) (S.map_minus_le f _ _ _)))

end MonomialData

end BrickAccessibility
