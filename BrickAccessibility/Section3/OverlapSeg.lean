module

public import BrickAccessibility.Section3.Overlap
public import BrickAccessibility.Quiver.Classes

/-!
# Overlapping occurrences in a brick string module (Step 2 of Proposition 3.8)

Over a special biserial algebra, if `a u` and `u b` (`u` nonempty) are spelled by
segments of the string diagram of a brick string module, then so is `a u b`.
Otherwise the occurrence of `u` inside `a u` spans a submodule, the occurrence
inside `u b` gives a quotient, and the matched map between them is a nonzero
noninvertible endomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hw : w.IsString D)
include hw

/-- Two consecutive moves spell a nonzero path. -/
theorem allowed_of_moves {x y : D.Q.A} {i j l : Fin (w.len + 1)} (h1 : w.next x i = some j)
    (h2 : w.next y j = some l) : D.toPathData.Allowed x y := by
  set C := w.coeffQuiver D
  have e1 : C.next x i = some j := h1
  have e2 : C.next y j = some l := h2
  refine ⟨(C.next_src y j l e2).symm.trans (C.next_tgt x i j e1), fun h0 ↦ ?_⟩
  have hf : C.follow i [x, y] = some (l, C.coef x i * (C.coef y j * 1)) := by
    refine C.follow_cons_eq_some.mpr ⟨j, _, e1, ?_, rfl⟩
    exact C.follow_cons_eq_some.mpr ⟨l, 1, e2, rfl, rfl⟩
  rw [hw.2 _ _ h0 i (C.next_src x i j e1)] at hf
  cases hf

theorem eq_of_allowed (hSB : D.toPathData.IsSpecialBiserial) {x y y' : D.Q.A}
    (h : D.toPathData.Allowed x y) (h' : D.toPathData.Allowed x y') : y = y' := by
  have := hSB.2.2.1 x
  rw [Finite.card_le_one_iff_subsingleton] at this
  exact congrArg Subtype.val (Subsingleton.elim (⟨y, h⟩ : {b // D.toPathData.Allowed x b}) ⟨y', h'⟩)

theorem eq_of_allowed' (hSB : D.toPathData.IsSpecialBiserial) {x x' y : D.Q.A}
    (h : D.toPathData.Allowed x y) (h' : D.toPathData.Allowed x' y) : x = x' := by
  have := hSB.2.2.2 y
  rw [Finite.card_le_one_iff_subsingleton] at this
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, h⟩ : {a // D.toPathData.Allowed a y}) ⟨x', h'⟩)

/-- Step 2 of Proposition 3.8. -/
theorem seg_of_overlap (hSB : D.toPathData.IsSpecialBiserial) (hb : IsBrick B (w.stringModule D hw))
    {a b : D.Q.A} {u : List D.Q.A} (hu : u ≠ []) {d₁ d₂ : Bool} {r₁ r₂ : ℕ}
    (h₁ : w.Seg d₁ r₁ (a :: u)) (h₂ : w.Seg d₂ r₂ (u ++ [b])) :
    ∃ d r, w.Seg d r (a :: u ++ [b]) := by
  classical
  by_contra hno
  push Not at hno
  set C := w.coeffQuiver D
  set m := u.length with hmdef
  have hm : 0 < m := List.length_pos_iff.mpr hu
  have hL₁ : (a :: u).length = m + 1 := by simp [m]
  have hL₂ : (u ++ [b]).length = m + 1 := by simp [m]
  let π₁ : Fin (m + 1) → Fin (w.len + 1) := fun i ↦ h₁.pos (i.val + 1) (by omega)
  let π₂ : Fin (m + 1) → Fin (w.len + 1) := fun i ↦ h₂.pos i.val (by omega)
  have hπ₂ : Function.Injective π₂ := fun i i' h ↦ Fin.ext (h₂.pos_injective _ _ h)
  -- the steps of the two occurrences of `u`
  have F₁ : ∀ (i : ℕ) (hi : i < m), w.next u[i] (π₁ ⟨i, by omega⟩) = some (π₁ ⟨i + 1, by omega⟩) := by
    intro i hi
    have := h₁.next hw.1 (j := i + 1) (by omega)
    simp only [List.getElem_cons_succ] at this
    exact this
  have F₂ : ∀ (i : ℕ) (hi : i < m), w.next u[i] (π₂ ⟨i, by omega⟩) = some (π₂ ⟨i + 1, by omega⟩) := by
    intro i hi
    have := h₂.next hw.1 (j := i) (by omega)
    rw [List.getElem_append_left hi] at this
    exact this
  have Fb : w.next b (π₂ ⟨m, by omega⟩) = some (h₂.pos (m + 1) (by omega)) := by
    have := h₂.next hw.1 (j := m) (by omega)
    simpa [m] using this
  have Fa : w.next a (h₁.pos 0 (by omega)) = some (π₁ ⟨0, by omega⟩) := by
    exact h₁.next hw.1 (j := 0) (by omega)
  -- internal moves
  have M₁ : ∀ (x : D.Q.A) (j j' : ℕ) (hj : j ≤ m + 1) (hj' : j' ≤ m + 1),
      w.next x (h₁.pos j (by omega)) = some (h₁.pos j' (by omega)) →
        j' = j + 1 ∧ ∃ hjm : j < m + 1, x = (a :: u)[j]'(by omega) := by
    intro x j j' hj hj' h
    obtain ⟨hjl, he, hx⟩ := h₁.move hw.1 (by omega) (by omega) h
    exact ⟨he, by omega, hx⟩
  have M₂ : ∀ (x : D.Q.A) (j j' : ℕ) (hj : j ≤ m + 1) (hj' : j' ≤ m + 1),
      w.next x (h₂.pos j (by omega)) = some (h₂.pos j' (by omega)) →
        j' = j + 1 ∧ ∃ hjm : j < m + 1, x = (u ++ [b])[j]'(by omega) := by
    intro x j j' hj hj' h
    obtain ⟨hjl, he, hx⟩ := h₂.move hw.1 (by omega) (by omega) h
    exact ⟨he, by omega, hx⟩
  refine C.false_of_matched (π₁ := π₁) hw.2 hb (Nat.succ_pos m) hπ₂ ?_ ?_ ?_ ?_
    (t := h₂.pos (m + 1) (by omega)) ?_
  · -- vertices agree
    intro i
    by_cases hi : i.val < m
    · have e1 := C.next_src _ _ _ (F₁ i.val hi)
      have e2 := C.next_src _ _ _ (F₂ i.val hi)
      exact e1.trans e2.symm
    · have hi' : i.val = m := by omega
      have e1 := C.next_tgt _ _ _ (F₁ (m - 1) (by omega))
      have e2 := C.next_tgt _ _ _ (F₂ (m - 1) (by omega))
      have hi1 : i = ⟨m - 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hi1]
      exact e1.trans e2.symm
  · -- moves out of the first occurrence stay inside it
    intro x i t ht
    change Fin (w.len + 1) at t
    change w.next x (π₁ i) = some t at ht
    have hv := w.next_val hw.1 ht
    rcases h₁.adj (j := i.val + 1) (by omega) (t := t.val) hv with
      ⟨j', hj', htj⟩ | ⟨h0, -⟩ | ⟨hend, htj⟩
    · have htj' : t = h₁.pos j' hj' := Fin.ext htj
      rw [htj'] at ht
      obtain ⟨he, hjm, hx⟩ := M₁ x (i.val + 1) j' (by omega) (by omega) ht
      have hiu : i.val < m := by omega
      simp only [List.getElem_cons_succ] at hx
      subst hx
      refine ⟨⟨i.val + 1, by omega⟩, by rw [htj']; exact Fin.ext (by simp [π₁, he]), ?_, rfl⟩
      exact F₂ i.val hiu
    · omega
    · exfalso
      have hseg := h₁.extend_right hw.1 (x := x) (t := t)
        (by have := ht; rwa [show π₁ i = h₁.pos (a :: u).length le_rfl from
          Fin.ext (by simp only [π₁, Seg.pos_val, hend])] at this) (by rw [htj, hL₁])
      -- `x = b` by uniqueness of the allowed successor of the last letter of `u`
      have hA₁ := w.allowed_of_moves hw (F₁ (m - 1) (by omega))
        (show w.next x (π₁ ⟨m - 1 + 1, by omega⟩) = some t by
          have e : (⟨m - 1 + 1, by omega⟩ : Fin (m + 1)) = i := Fin.ext (by simp; omega)
          rw [e]; exact ht)
      have hA₂ := w.allowed_of_moves hw (F₂ (m - 1) (by omega))
        (show w.next b (π₂ ⟨m - 1 + 1, by omega⟩) = some (h₂.pos (m + 1) (by omega)) by
          have e : (⟨m - 1 + 1, by omega⟩ : Fin (m + 1)) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          rw [e]; exact Fb)
      have hxb := w.eq_of_allowed hw hSB hA₁ hA₂
      subst hxb
      exact hno _ _ (by simpa using hseg)
  · -- internal moves of the second occurrence are internal moves of the first
    intro x i i' h
    obtain ⟨he, hjm, hx⟩ := M₂ x i.val i'.val (by omega) (by omega) h
    have hiu : i.val < m := by omega
    rw [List.getElem_append_left hiu] at hx
    subst hx
    have : i' = ⟨i.val + 1, by omega⟩ := Fin.ext he
    rw [this]
    exact F₁ i.val hiu
  · -- moves into the second occurrence come from inside it
    intro x s i h
    change Fin (w.len + 1) at s
    change w.next x s = some (π₂ i) at h
    have hv := w.next_val hw.1 h
    have hpv : (π₂ i).val = spos d₂ r₂ i.val := rfl
    rcases h₂.adj (j := i.val) (by omega) (t := s.val) (by omega) with
      ⟨j', hj', hsj⟩ | ⟨h0, hsj⟩ | ⟨hend, -⟩
    · by_cases hj'm : j' ≤ m
      · exact ⟨⟨j', by omega⟩, Fin.ext hsj⟩
      · exfalso
        have hs' : s = h₂.pos j' hj' := Fin.ext hsj
        rw [hs'] at h
        obtain ⟨he, -⟩ := M₂ x j' i.val (by omega) (by omega) h
        omega
    · exfalso
      have hi0 : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [hi0] at h
      have hseg := h₂.extend_left hw.1 (x := x) (t := s) h hsj
      have hA₁ := w.allowed_of_moves hw h (F₂ 0 hm)
      have hA₂ := w.allowed_of_moves hw Fa (F₁ 0 hm)
      have hxa := w.eq_of_allowed' hw hSB hA₁ hA₂
      subst hxa
      exact hno _ _ (by simpa using hseg)
    · omega
  · intro i h
    have := h₂.pos_injective (by omega) (by omega) h
    omega

end Word

end BrickAccessibility
