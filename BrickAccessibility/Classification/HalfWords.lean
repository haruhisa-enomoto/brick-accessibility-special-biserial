module

public import BrickAccessibility.Classification.Transport
public import BrickAccessibility.Classification.Signs
public import BrickAccessibility.Section4.Closed

/-!
# Finite half-words and their subspaces

A (finite) half-word at `(v, s)` is a walk `C` from `v` in which every letter
starts with the sign `nsign s` of the prefix before it: `s` for the first
letter, and the opposite of the end sign of the previous letter afterwards.
At the end `u` of `C` the next sign `n` admits at most one direct continuation
`b` (`σ b = n`) and one inverse continuation `d` (`ε d = n`), and
`C⁺ = C^*(M_u ∩ ker b)`, `C⁻ = C^*(im d)`. Then `C⁻ ≤ C⁺`, inverse
continuations lie below `C⁻`, and `C⁺` lies below direct continuations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)

/-- The sign with which a letter after `C` must start. -/
def Signs.nsign (s : Bool) (C : List (Letter D.Q)) : Bool :=
  match C.getLast? with
  | none => s
  | some l => !S.en l

@[simp] theorem Signs.nsign_nil (s : Bool) : S.nsign s [] = s := rfl

@[simp] theorem Signs.nsign_append_singleton (s : Bool) (C : List (Letter D.Q)) (l : Letter D.Q) :
    S.nsign s (C ++ [l]) = !S.en l := by
  simp [Signs.nsign]

/-- A finite half-word at `(v, s)`. -/
def Signs.IsHW (v : D.Q.V) (s : Bool) (C : List (Letter D.Q)) : Prop :=
  D.Q.IsWalk v C ∧ ∀ (i : ℕ) (hi : i < C.length), S.st C[i] = S.nsign s (C.take i)

theorem Signs.isHW_nil (v : D.Q.V) (s : Bool) : S.IsHW v s [] := ⟨trivial, fun i hi ↦ by simp at hi⟩

theorem Signs.isHW_append_singleton {v : D.Q.V} {s : Bool} {C : List (Letter D.Q)}
    (h : S.IsHW v s C) {l : Letter D.Q} (hl : l.src = D.Q.wend v C)
    (hs : S.st l = S.nsign s C) : S.IsHW v s (C ++ [l]) := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [Statement.FinQuiver.isWalk_append]
    exact ⟨h.1, by simp [Statement.FinQuiver.IsWalk, hl]⟩
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hi' : i < C.length
    · rw [List.getElem_append_left hi', List.take_append_of_le_length hi'.le]
      exact h.2 i hi'
    · obtain rfl : i = C.length := by omega
      simp [hs]

theorem Signs.IsHW.take {v : D.Q.V} {s : Bool} {C : List (Letter D.Q)} (h : S.IsHW v s C)
    (n : ℕ) : S.IsHW v s (C.take n) := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have := h.1
    rw [← List.take_append_drop n C, Statement.FinQuiver.isWalk_append] at this
    exact this.1
  · simp only [List.length_take] at hi
    rw [List.getElem_take, List.take_take, min_eq_left (by omega)]
    exact h.2 i (by omega)

/-! ### Continuations and the boundary subspaces -/

variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

variable (M) in
/-- The kernel condition at an end `u` with next sign `n`. -/
def Signs.Kc (u : D.Q.V) (n : Bool) : Submodule k M :=
  D.vsp M u ⊓ ⨅ (b : D.Q.A) (_ : D.Q.src b = u ∧ S.σ b = n), LinearMap.ker (actL (D.α b))

variable (M) in
/-- The image condition at an end `u` with next sign `n`. -/
def Signs.Ic (u : D.Q.V) (n : Bool) : Submodule k M :=
  ⨆ (d : D.Q.A) (_ : D.Q.tgt d = u ∧ S.ε d = n), LinearMap.range (actL (D.α d))

theorem Signs.Ic_le_Kc (u : D.Q.V) (n : Bool) : S.Ic M u n ≤ S.Kc M u n := by
  refine iSup₂_le fun d hd ↦ ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hd.1]; exact D.α_smul_mem_vsp d m
  · refine Submodule.mem_iInf _ |>.mpr fun b ↦ Submodule.mem_iInf _ |>.mpr fun hb ↦ ?_
    -- `d b` is a zero path: `σ b = ε d`
    have hnot : ¬ D.toPathData.Allowed d b := fun h ↦ S.hall d b h (hb.2.trans hd.2.symm)
    have hz : D.pval (D.Q.src d) [d, b] = 0 := by
      by_contra h; exact hnot ⟨hb.1.trans hd.1.symm, h⟩
    change D.α b • D.α d • m = 0
    rw [← mul_smul]
    have key : D.pval (D.Q.src d) [d, b] = D.α b * D.α d := by
      have h1 := D.toPathData.pval_append (D.Q.src d) [d] [b]
      have e1 : D.Q.pend (D.Q.src d) [d] = D.Q.src b := by
        simp [Statement.FinQuiver.pend, hb.1, hd.1]
      rw [e1, D.toPathData.pval_single_src, D.toPathData.pval_single_src] at h1
      exact h1
    rw [← key, hz, zero_smul]

theorem Signs.Kc_eq (u : D.Q.V) (n : Bool) {b : D.Q.A} (hb : D.Q.src b = u ∧ S.σ b = n) :
    S.Kc M u n = D.vsp M u ⊓ LinearMap.ker (actL (D.α b)) := by
  refine le_antisymm (inf_le_inf_left _ (iInf₂_le b hb)) (inf_le_inf_left _ ?_)
  refine le_iInf₂ fun b' hb' ↦ ?_
  have : b' = b := by
    by_contra h; exact S.hσ b' b h (hb'.1.trans hb.1.symm) (hb'.2.trans hb.2.symm)
  rw [this]

theorem Signs.Kc_eq_vsp (u : D.Q.V) (n : Bool) (h : ¬ ∃ b, D.Q.src b = u ∧ S.σ b = n) :
    S.Kc M u n = D.vsp M u := by
  refine le_antisymm inf_le_left (le_inf le_rfl (le_iInf₂ fun b hb ↦ absurd ⟨b, hb⟩ h))

theorem Signs.Ic_eq (u : D.Q.V) (n : Bool) {d : D.Q.A} (hd : D.Q.tgt d = u ∧ S.ε d = n) :
    S.Ic M u n = LinearMap.range (actL (D.α d)) := by
  refine le_antisymm (iSup₂_le fun d' hd' ↦ ?_) (le_iSup₂_of_le d hd le_rfl)
  have : d' = d := by
    by_contra h; exact S.hε d' d h (hd'.1.trans hd.1.symm) (hd'.2.trans hd.2.symm)
  rw [this]

theorem Signs.Ic_eq_bot (u : D.Q.V) (n : Bool) (h : ¬ ∃ d, D.Q.tgt d = u ∧ S.ε d = n) :
    S.Ic M u n = ⊥ :=
  eq_bot_iff.mpr (iSup₂_le fun d hd ↦ absurd ⟨d, hd⟩ h)

theorem tr_true_vsp (b : D.Q.A) : D.tr (b, true) (D.vsp M (D.Q.tgt b)) = D.vsp M (D.Q.src b) := by
  refine le_antisymm inf_le_left (le_inf le_rfl fun m _ ↦ D.α_smul_mem_vsp b m)

theorem range_α_eq_map (d : D.Q.A) :
    LinearMap.range (actL (M := M) (D.α d)) = (D.vsp M (D.Q.src d)).map (actL (D.α d)) := by
  refine le_antisymm ?_ (LinearMap.map_le_range)
  rintro _ ⟨m, rfl⟩
  refine ⟨D.e (D.Q.src d) • m, ⟨m, rfl⟩, ?_⟩
  simp only [actL_apply, ← mul_smul]
  rw [show D.α d * D.e (D.Q.src d) = D.α d from D.toPathData.α_mul_e d]

theorem tr_false_vsp (d : D.Q.A) :
    D.tr (d, false) (D.vsp M (D.Q.src d)) = LinearMap.range (actL (D.α d)) := by
  rw [range_α_eq_map]; simp [tr]

theorem tr_false_le_range (d : D.Q.A) (U : Submodule k M) :
    D.tr (d, false) U ≤ LinearMap.range (actL (D.α d)) := by
  rw [range_α_eq_map]; exact Submodule.map_mono inf_le_left

@[simp] theorem tr_false_bot (d : D.Q.A) : D.tr (d, false) (⊥ : Submodule k M) = ⊥ := by
  simp [tr]

theorem tr_true_bot (b : D.Q.A) :
    D.tr (b, true) (⊥ : Submodule k M) = D.vsp M (D.Q.src b) ⊓ LinearMap.ker (actL (D.α b)) := rfl

theorem trs_le_vsp (l : Letter D.Q) (C : List (Letter D.Q)) (U : Submodule k M) :
    D.trs (l :: C) U ≤ D.vsp M l.src := D.tr_le_vsp l _

theorem trs_bot_le (C : List (Letter D.Q)) (U : Submodule k M) : D.trs C ⊥ ≤ D.trs C U :=
  D.trs_mono C bot_le

/-! ### The boundary subspaces of a finite half-word -/

variable (M) in
/-- `C⁺`. -/
def Signs.plusF (v : D.Q.V) (s : Bool) (C : List (Letter D.Q)) : Submodule k M :=
  D.trs C (S.Kc M (D.Q.wend v C) (S.nsign s C))

variable (M) in
/-- `C⁻`. -/
def Signs.minusF (v : D.Q.V) (s : Bool) (C : List (Letter D.Q)) : Submodule k M :=
  D.trs C (S.Ic M (D.Q.wend v C) (S.nsign s C))

theorem Signs.minusF_le_plusF (v : D.Q.V) (s : Bool) (C : List (Letter D.Q)) :
    S.minusF M v s C ≤ S.plusF M v s C :=
  D.trs_mono C (S.Ic_le_Kc _ _)

theorem Signs.plusF_le_vsp {v : D.Q.V} {s : Bool} {C : List (Letter D.Q)} (h : D.Q.IsWalk v C) :
    S.plusF M v s C ≤ D.vsp M v := by
  cases C with
  | nil => exact inf_le_left
  | cons l C => exact (D.trs_le_vsp l C _).trans (by rw [h.1])

/-- A word followed by its inverse continuation lies below the word's `C⁻`. -/
theorem Signs.trs_inv_le_minusF {v : D.Q.V} {s : Bool} {E : List (Letter D.Q)} {d : D.Q.A}
    (hd : D.Q.tgt d = D.Q.wend v E ∧ S.ε d = S.nsign s E) (U : Submodule k M) :
    D.trs (E ++ [(d, false)]) U ≤ S.minusF M v s E := by
  rw [D.trs_append, Signs.minusF, S.Ic_eq _ _ hd]
  exact D.trs_mono E (D.tr_false_le_range d _)

/-- A word's `C⁺` lies below the zero transport along its direct continuation. -/
theorem Signs.plusF_le_trs_dir {v : D.Q.V} {s : Bool} {E : List (Letter D.Q)} {b : D.Q.A}
    (hb : D.Q.src b = D.Q.wend v E ∧ S.σ b = S.nsign s E) :
    S.plusF M v s E ≤ D.trs (E ++ [(b, true)]) ⊥ := by
  rw [D.trs_append, Signs.plusF, S.Kc_eq _ _ hb]
  simp only [trs_cons, trs_nil]
  rw [tr_true_bot, hb.1]

end MonomialData

end BrickAccessibility
