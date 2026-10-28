module

public import BrickAccessibility.Section4.Shapes

/-!
# Endpoint facts for Lemma 4.6

Edges at the endpoints `0` and `n` of a string of positive length, and extraction
of extending arrows from the counting inequalities.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hw : w.NoForks) (hn : 0 < w.len)
include hw hn

theorem in_zero_iff : (∃ a i, w.next a i = some 0) ↔ (w.first hn).2 = false := by
  constructor
  · rintro ⟨a, i, h⟩
    rcases w.letter_of_next_to hw h with ⟨hl, -⟩ | ⟨hl, -⟩
    · rw [w.leftL_zero hn] at hl; cases hl
    · rw [w.rightL_zero hn] at hl; rw [Option.some.inj hl]
  · intro h
    rcases hf : w.first hn with ⟨a, d⟩
    rw [hf] at h; subst h
    have := w.rightL_zero hn; rw [hf] at this
    obtain ⟨i, hi, -⟩ := w.next_to_of_rightL_inv hw this
    exact ⟨a, i, hi⟩

theorem out_zero_iff : (∃ a j, w.next a 0 = some j) ↔ (w.first hn).2 = true := by
  constructor
  · rintro ⟨a, j, h⟩
    rcases w.letter_of_next_from hw h with ⟨hl, -⟩ | ⟨hl, -⟩
    · rw [w.leftL_zero hn] at hl; cases hl
    · rw [w.rightL_zero hn] at hl; rw [Option.some.inj hl]
  · intro h
    rcases hf : w.first hn with ⟨a, d⟩
    rw [hf] at h; subst h
    have := w.rightL_zero hn; rw [hf] at this
    obtain ⟨j, hj, -⟩ := w.next_of_rightL_dir hw this
    exact ⟨a, j, hj⟩

theorem in_last_iff : (∃ a i, w.next a i = some (Fin.last _)) ↔ (w.last hn).2 = true := by
  constructor
  · rintro ⟨a, i, h⟩
    rcases w.letter_of_next_to hw h with ⟨hl, -⟩ | ⟨hl, -⟩
    · rw [w.leftL_last hn] at hl; rw [Option.some.inj hl]
    · rw [w.rightL_last hn] at hl; cases hl
  · intro h
    rcases hf : w.last hn with ⟨a, d⟩
    rw [hf] at h; subst h
    have := w.leftL_last hn; rw [hf] at this
    obtain ⟨i, hi, -⟩ := w.next_to_of_leftL_dir hw this
    exact ⟨a, i, hi⟩

theorem out_last_iff : (∃ a j, w.next a (Fin.last _) = some j) ↔ (w.last hn).2 = false := by
  constructor
  · rintro ⟨a, j, h⟩
    rcases w.letter_of_next_from hw h with ⟨hl, -⟩ | ⟨hl, -⟩
    · rw [w.leftL_last hn] at hl; rw [Option.some.inj hl]
    · rw [w.rightL_last hn] at hl; cases hl
  · intro h
    rcases hf : w.last hn with ⟨a, d⟩
    rw [hf] at h; subst h
    have := w.leftL_last hn; rw [hf] at this
    obtain ⟨j, hj, -⟩ := w.next_of_leftL_inv hw this
    exact ⟨a, j, hj⟩

theorem zero_ne_last : (0 : Fin (w.len + 1)) ≠ Fin.last _ := by
  intro h; have := congrArg Fin.val h; simp at this; omega

open Classical in
theorem socend_pos {p : Fin (w.len + 1)} (hp : p = 0 ∨ p = Fin.last _)
    (hin : ∃ a i, w.next a i = some p) : 1 ≤ w.socend (w.vtx p) := by
  unfold socend
  exact Fintype.card_pos_iff.mpr ⟨⟨p, rfl, (w.isEnd_iff p).mpr hp, hin⟩⟩

open Classical in
theorem topend_pos {p : Fin (w.len + 1)} (hp : p = 0 ∨ p = Fin.last _)
    (hout : ∃ a j, w.next a p = some j) : 1 ≤ w.topend (w.vtx p) := by
  unfold topend
  exact Fintype.card_pos_iff.mpr ⟨⟨p, rfl, (w.isEnd_iff p).mpr hp, hout⟩⟩

open Classical in
theorem socend_two (hxy : w.vtx 0 = w.vtx (Fin.last _)) (h0 : ∃ a i, w.next a i = some 0)
    (hl : ∃ a i, w.next a i = some (Fin.last _)) : 2 ≤ w.socend (w.vtx 0) := by
  unfold socend
  refine Fintype.one_lt_card_iff.mpr ⟨⟨0, rfl, (w.isEnd_iff 0).mpr (Or.inl rfl), h0⟩,
    ⟨Fin.last _, hxy.symm, (w.isEnd_iff _).mpr (Or.inr rfl), hl⟩, fun h ↦ ?_⟩
  exact w.zero_ne_last hw hn (congrArg Subtype.val h)

open Classical in
theorem topend_two (hxy : w.vtx 0 = w.vtx (Fin.last _)) (h0 : ∃ a j, w.next a 0 = some j)
    (hl : ∃ a j, w.next a (Fin.last _) = some j) : 2 ≤ w.topend (w.vtx 0) := by
  unfold topend
  refine Fintype.one_lt_card_iff.mpr ⟨⟨0, rfl, (w.isEnd_iff 0).mpr (Or.inl rfl), h0⟩,
    ⟨Fin.last _, hxy.symm, (w.isEnd_iff _).mpr (Or.inr rfl), hl⟩, fun h ↦ ?_⟩
  exact w.zero_ne_last hw hn (congrArg Subtype.val h)

omit hw hn in
open Classical in
theorem extract_out {v : D.Q.V} (h : 1 ≤ w.extout v) :
    ∃ p c, w.IsEnd p ∧ w.OutExt p c ∧ D.Q.tgt c = v := by
  unfold extout at h
  obtain ⟨⟨⟨p, c⟩, hp⟩⟩ := Fintype.card_pos_iff.mp h
  exact ⟨p, c, hp⟩

omit hw hn in
open Classical in
theorem extract_in {v : D.Q.V} (h : 1 ≤ w.extin v) :
    ∃ p c, w.IsEnd p ∧ w.InExt p c ∧ D.Q.src c = v := by
  unfold extin at h
  obtain ⟨⟨⟨p, c⟩, hp⟩⟩ := Fintype.card_pos_iff.mp h
  exact ⟨p, c, hp⟩

omit hw hn in
open Classical in
theorem extract_out_two {v : D.Q.V} (h : 2 ≤ w.extout v) :
    ∃ p c p' c', w.IsEnd p ∧ w.OutExt p c ∧ D.Q.tgt c = v ∧
      w.IsEnd p' ∧ w.OutExt p' c' ∧ D.Q.tgt c' = v ∧ (p, c) ≠ (p', c') := by
  unfold extout at h
  obtain ⟨⟨⟨p, c⟩, hp⟩, ⟨⟨p', c'⟩, hp'⟩, hne⟩ := Fintype.one_lt_card_iff.mp h
  exact ⟨p, c, p', c', hp.1, hp.2.1, hp.2.2, hp'.1, hp'.2.1, hp'.2.2,
    fun h ↦ hne (Subtype.ext h)⟩

omit hw hn in
open Classical in
theorem extract_in_two {v : D.Q.V} (h : 2 ≤ w.extin v) :
    ∃ p c p' c', w.IsEnd p ∧ w.InExt p c ∧ D.Q.src c = v ∧
      w.IsEnd p' ∧ w.InExt p' c' ∧ D.Q.src c' = v ∧ (p, c) ≠ (p', c') := by
  unfold extin at h
  obtain ⟨⟨⟨p, c⟩, hp⟩, ⟨⟨p', c'⟩, hp'⟩, hne⟩ := Fintype.one_lt_card_iff.mp h
  exact ⟨p, c, p', c', hp.1, hp.2.1, hp.2.2, hp'.1, hp'.2.1, hp'.2.2,
    fun h ↦ hne (Subtype.ext h)⟩

end Word

end BrickAccessibility
