module

public import BrickAccessibility.Section4.Positive
public import BrickAccessibility.Basic.Inflation
public import BrickAccessibility.Cited.StringBricks

/-!
# Proposition 4.7: smaller bricks over representation-finite gentle algebras
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- Representation-finiteness implies brick-finiteness. -/
theorem IsRepFinite.isBrickFinite (h : IsRepFinite B) : IsBrickFinite B := by
  obtain ⟨n, Bs, hB⟩ := h
  exact ⟨n, Bs, fun M _ _ _ hM ↦ hB M ⟨hM.1, fun P R hPR ↦ hM.compl_eq_bot hPR⟩⟩

/-- **Proposition 4.7.** Every nonsimple brick over a representation-finite gentle
algebra has a brick submodule or quotient of dimension one less. -/
theorem gentle_hasSmallerBrick [IsAlgClosed k] [FiniteDimensional k B] (D : MonomialData k B)
    (hD : D.IsGentle) (hrep : IsRepFinite B) (M : Type u) [AddCommGroup M] [Module B M]
    [Module k M] [IsScalarTower k B M] [FiniteDimensional k M] (hM : IsBrick B M)
    (hns : ¬ IsSimpleModule B M) : HasSmallerBrick B M (k := k) := by
  obtain ⟨w, hw, ⟨e⟩⟩ := isString_of_isBrick D hD.1 hrep.isBrickFinite M hM
  set N := w.stringModule D hw
  have hN : IsBrick B N := hM.of_linearEquiv e
  have hNns : ¬ IsSimpleModule B N := fun h ↦ hns (IsSimpleModule.congr e)
  haveI : FiniteDimensional k N := Module.Finite.equiv (e.restrictScalars k)
  refine HasSmallerBrick.of_linearEquiv e.symm ?_
  obtain ⟨v, hv | hv⟩ := exists_positive_coordinate D hD hrep w hw hN hNns
  · right
    exact exists_brick_quotient (k := k) hN hNns (D.finrank_simple v)
      (finitelyManyQuotientsBy_of_isRepFinite (k := k) hrep N (D.simple v)) hv
  · left
    exact exists_brick_submodule (k := k) hN hNns (D.finrank_simple v)
      (finitelyManyKernelsBy_of_isRepFinite (k := k) hrep N (D.simple v)) hv

end BrickAccessibility
