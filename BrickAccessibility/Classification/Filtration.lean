module

public import BrickAccessibility.Classification.Coverage
public import BrickAccessibility.Classification.Intervals

/-!
# The functorial filtration at a vertex

The valid half-words at `(v, s)`, ordered by their codes, form an interval
family on `M_v` (`fam`). Pairing the families of the two signs gives Ringel's
functors `F_{h,h'}(M) = (h⁺ ∩ h'⁺) / (h⁻ ∩ h'⁺ + h⁺ ∩ h'⁻)` and the dimension
formula `dim M_v = Σ dim F_{h,h'}(M)` (`finrank_vsp_eq_sum`).
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

/-- Valid half-words at `(v, s)`. -/
def Signs.HW (v : D.Q.V) (s : Bool) : Type := {h : HWord D.Q // S.Valid v s h}

theorem Signs.HW.key_injective (v : D.Q.V) (s : Bool) :
    Function.Injective fun h : S.HW v s ↦ toLex h.1.code := by
  intro h h' e
  exact Subtype.ext (S.code_injective h.2 h'.2 (toLex.injective e))

noncomputable instance (v : D.Q.V) (s : Bool) : LinearOrder (S.HW v s) :=
  LinearOrder.lift' (fun h : S.HW v s ↦ toLex h.1.code) (Signs.HW.key_injective S v s)

theorem Signs.HW.lt_iff {v : D.Q.V} {s : Bool} {h h' : S.HW v s} :
    h < h' ↔ toLex h.1.code < toLex h'.1.code := Iff.rfl

variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- The interval family of half-words at `(v, s)`. -/
def Signs.fam (v : D.Q.V) (s : Bool) : IFam (D.vsp M v) (S.HW v s) where
  lo h := S.minus M v s h.1
  hi h := S.plus M v s h.1
  lo_le h := S.minus_le_plus h.2
  hi_le h := S.plus_le_vsp h.2
  sep {t t'} hlt := S.plus_le_minus_of_lt t.2 t'.2 hlt
  cover x hx hx0 := by
    obtain ⟨h, hv, h1, h2⟩ := S.exists_hword v s hx hx0
    exact ⟨⟨h, hv⟩, h1, h2⟩

/-- **The dimension formula** at a vertex. -/
theorem Signs.finrank_vsp_eq_sum [FiniteDimensional k M] (v : D.Q.V) (s : Bool) :
    finrank k (D.vsp M v) = ∑ p ∈ ((S.fam M v s).supp_finite.toFinset ×ˢ
        (S.fam M v (!s)).supp_finite.toFinset),
      (finrank k (IFam.num (S.fam M v s) (S.fam M v (!s)) p.1 p.2) -
        finrank k (IFam.den (S.fam M v s) (S.fam M v (!s)) p.1 p.2)) :=
  IFam.finrank_eq_sum _ _

end MonomialData

end BrickAccessibility
