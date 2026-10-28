module

public import BrickAccessibility.Quiver.Classes
public import BrickAccessibility.Basic.Inflation
public import BrickAccessibility.StringQuotient.Projective

/-!
# Lemma 5.3 (Wald–Waschbüsch): the string quotient of a special biserial algebra

For a special biserial algebra there is a two-sided ideal `J` (the sum of the
socles of the nonuniserial projective-injective summands) such that `A ⧸ J` is a
string algebra and every indecomposable module not killed by `J` is projective.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- **Lemma 5.3**, in the form used for Theorem 5.4. -/
theorem exists_string_quotient [IsAlgClosed k] [FiniteDimensional k A] {Q : FinQuiver}
    (D : PathData Q A)
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial) :
    ∃ (J : Ideal A) (_ : J.IsTwoSided) (D' : MonomialData k (A ⧸ J)), D'.IsStringAlgebra ∧
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
        [FiniteDimensional k M], IsIndecomposable A M → ¬ Module.IsTorsionBySet A M J →
          Module.Projective A M := by
  classical
  haveI := PathData.JI_isTwoSided (k := k) hadm hsb hspan
  refine ⟨PathData.JI (k := k) hadm hspan, inferInstance, PathData.quotData hadm hsb hspan,
    PathData.quotData_isString hadm hsb hspan, ?_⟩
  intro M _ _ _ _ _ hM hJ
  obtain ⟨x, m, hxm⟩ : ∃ (x : Q.V) (m : M), PathData.zz (k := k) hadm x • m ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hJ
    intro m j
    obtain ⟨j, hj⟩ := j
    change j ∈ PathData.Jsp (k := k) hadm at hj
    show j • m = 0
    induction hj using Submodule.span_induction with
    | mem j hj => obtain ⟨x, rfl⟩ := hj; exact hno x m
    | zero => rw [zero_smul]
    | add j j' _ _ h h' => rw [add_smul, h, h', add_zero]
    | smul μ j _ h => rw [smul_assoc, h, smul_zero]
  have hb : PathData.Bin (k := k) hadm x := by
    by_contra hb
    rw [PathData.zz_of_not hadm hb, zero_smul] at hxm
    exact hxm rfl
  obtain ⟨a, b, hab, hxa, hxb, hmem, hz⟩ := PathData.zz_spec hadm hb
  obtain ⟨y, hyz, S2⟩ := PathData.socle_op hadm hsb hspan hb
  have hzx : PathData.zz (k := k) hadm x * D.e x = PathData.zz (k := k) hadm x := by
    rw [PathData.zz_mul_e, if_pos rfl]
  have hz0 : PathData.zz (k := k) hadm x ≠ 0 := by
    rw [hz]; exact PathData.pval_Pm_ne hadm hsb hxa
  exact PathData.projective_of_socles (k := k) hzx hyz hz0 (fun w hw hw0 ↦ by
    obtain ⟨c, hc⟩ := PathData.socle hadm hsb hspan hb hxa hw hw0
    exact ⟨c, hc.trans hz.symm⟩) S2 M hM hxm

end BrickAccessibility
