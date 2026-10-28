module

public import BrickAccessibility.Section3.Walks

/-!
# Path actions on string modules (Step 1 of Proposition 3.8)

A path acts nonzero on `M(w)` exactly when it is spelled by a walk of the string
diagram (`pval_mem_annihilator_iff`), and the nonzero path actions are linearly
independent, since their matrices have nonempty disjoint supports
(`linIndep_pathAction`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

/-- The path `l` from `x` is spelled by a walk of the string diagram. -/
def Occurs (x : D.Q.V) (l : List D.Q.A) : Prop :=
  ∃ r : (w.coeffQuiver D).P, (w.coeffQuiver D).vtx r = x ∧
    ∃ s c, (w.coeffQuiver D).follow r l = some (s, c)

variable (hw : w.IsString D)
include hw

theorem pval_smul (x : D.Q.V) (l : List D.Q.A) (m : w.stringModule D hw) :
    D.pval x l • m = (w.coeffQuiver D).toPathData.pval x l m := by
  change ((w.coeffQuiver D).toRep hw.2).actL (D.pval x l) m = _
  rw [MonomialData.Rep.actL_pval]; rfl

theorem pathAction_ne_zero_iff (x : D.Q.V) (l : List D.Q.A) :
    (w.coeffQuiver D).toPathData.pval x l ≠ 0 ↔ w.Occurs x l := by
  constructor
  · intro h
    by_contra hno
    apply h
    refine LinearMap.pi_ext fun i c ↦ ?_
    rw [MonomialData.CoeffQuiver.pval_single]
    split_ifs with hx
    · cases hf : (w.coeffQuiver D).follow i l with
      | none => rfl
      | some q => exact absurd ⟨i, hx, q.1, q.2, hf⟩ hno
    · rfl
  · rintro ⟨r, hr, s, c, hf⟩ h0
    have := congrArg (fun f ↦ f (Pi.single (M := fun _ : (w.coeffQuiver D).P ↦ k) r 1) s) h0
    simp only [LinearMap.zero_apply, Pi.zero_apply] at this
    rw [MonomialData.CoeffQuiver.pval_single, if_pos hr, hf] at this
    simp only [Pi.single_eq_same, mul_one] at this
    rw [(w.follow_eq_some hw.1 hf).1] at this
    exact one_ne_zero this

theorem pval_mem_annihilator_iff (x : D.Q.V) (l : List D.Q.A) :
    D.pval x l ∈ Module.annihilator B (w.stringModule D hw) ↔ ¬ w.Occurs x l := by
  rw [Module.mem_annihilator, ← w.pathAction_ne_zero_iff hw, not_not]
  constructor
  · intro h
    refine LinearMap.ext fun m ↦ ?_
    exact (w.pval_smul hw x l m).symm.trans (h m)
  · intro h m
    rw [w.pval_smul hw, h]; rfl

/-- Step 1 of Proposition 3.8: nonzero path actions are linearly independent. -/
theorem linIndep_pathAction :
    LinearIndependent k (fun p : {p : D.Q.V × List D.Q.A //
        (w.coeffQuiver D).toPathData.pval p.1 p.2 ≠ 0} ↦
      (w.coeffQuiver D).toPathData.pval p.1.1 p.1.2) := by
  classical
  rw [linearIndependent_iff']
  intro S g hg i hi
  obtain ⟨⟨x, l⟩, hxl⟩ := i
  obtain ⟨r, hr, s, c, hf⟩ := (w.pathAction_ne_zero_iff hw x l).mp hxl
  have hc := (w.follow_eq_some hw.1 hf).1
  have := congrArg (fun f ↦ f (Pi.single (M := fun _ : (w.coeffQuiver D).P ↦ k) r 1) s) hg
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    LinearMap.zero_apply, Pi.zero_apply, smul_eq_mul] at this
  rw [Finset.sum_eq_single ⟨(x, l), hxl⟩] at this
  · simpa [MonomialData.CoeffQuiver.pval_single, hr, hf, hc] using this
  · rintro ⟨⟨x', l'⟩, h'⟩ - hne
    rw [MonomialData.CoeffQuiver.pval_single]
    split_ifs with hx'
    · cases hf' : (w.coeffQuiver D).follow r l' with
      | none => simp
      | some q =>
          obtain ⟨s', c'⟩ := q
          by_cases hs : s' = s
          · subst hs
            have := w.follow_unique hw.1 hf hf'
            subst this
            exfalso; apply hne; exact Subtype.ext (Prod.ext (hx'.symm.trans hr) rfl)
          · simp [Ne.symm hs]
    · simp
  · intro h; exact absurd hi h

end Word

end BrickAccessibility
