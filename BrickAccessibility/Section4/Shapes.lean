module

public import BrickAccessibility.Section4.Closed
public import BrickAccessibility.Classification.ClosedBand

/-!
# Endpoints of a string and closed-word shapes for Lemma 4.6

For a string `w` of positive length, position `0` carries the first letter and
position `n` the last letter. Extending arrows at an endpoint are unique
(`outExt_zero_unique` and its variants). The closed words used in the proof of
Lemma 4.6 are built from `w`, its inverse and at most two extra letters; each
`shape` lemma checks that all cyclic adjacent pairs are allowed and concludes
representation-infinitude.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem isChain_append_of {α : Type*} {R : α → α → Prop} {L₁ L₂ : List α} (h₁ : L₁.IsChain R)
    (h₂ : L₂.IsChain R) (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ [])
    (hj : R (L₁.getLast hne₁) (L₂.head hne₂)) : (L₁ ++ L₂).IsChain R := by
  refine List.isChain_append.mpr ⟨h₁, h₂, fun x hx y hy ↦ ?_⟩
  rw [List.getLast?_eq_getLast hne₁, Option.mem_some_iff] at hx
  rw [List.head?_eq_head hne₂, Option.mem_some_iff] at hy
  subst hx; subst hy; exact hj

theorem invLetters_ne_nil {Q : FinQuiver} {L : List (Letter Q)} (h : L ≠ []) :
    invLetters L ≠ [] := by
  simpa [invLetters] using h

theorem head_invLetters {Q : FinQuiver} {L : List (Letter Q)} (h : L ≠ []) :
    (invLetters L).head (invLetters_ne_nil h) = (L.getLast h).inv := by
  simp [invLetters, List.head_reverse, List.getLast_map]

theorem getLast_invLetters {Q : FinQuiver} {L : List (Letter Q)} (h : L ≠ []) :
    (invLetters L).getLast (invLetters_ne_nil h) = (L.head h).inv := by
  simp [invLetters, List.getLast_reverse, List.head_map]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

/-- The first letter. -/
def first (hn : 0 < w.len) : Letter D.Q := w.letters[0]'hn
/-- The last letter. -/
def last (hn : 0 < w.len) : Letter D.Q := w.letters[w.len - 1]'(by simp only [len] at hn ⊢; omega)

variable (hn : 0 < w.len)
include hn

theorem leftL_zero : w.leftL 0 = none := w.leftL_eq_none (by simp)
theorem rightL_zero : w.rightL 0 = some (w.first hn) := by
  unfold rightL first; rw [dif_pos (by simpa using hn)]; rfl
theorem leftL_last : w.leftL (Fin.last _) = some (w.last hn) := by
  unfold leftL last; rw [dif_pos (by simpa using hn)]; rfl
theorem rightL_last : w.rightL (Fin.last _) = none := w.rightL_eq_none (by simp)

omit hn in
theorem isEnd_iff (p : Fin (w.len + 1)) : w.IsEnd p ↔ p = 0 ∨ p = Fin.last _ := by
  unfold IsEnd
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_zero, Fin.val_last]

theorem first_src : (w.first hn).src = w.vtx 0 := w.src_letter 0 hn
theorem last_tgt : (w.last hn).tgt = w.vtx (Fin.last _) := by
  have := w.tgt_letter (w.len - 1) (by simp only [len] at hn ⊢; omega)
  rw [last, this]
  congr 1; ext; simp; omega

theorem head_letters : w.letters.head (by simpa [len] using hn.ne') = w.first hn := by
  simp [first, List.head_eq_getElem]

theorem getLast_letters :
    w.letters.getLast (by simpa [len] using hn.ne') = w.last hn := by
  simp [last, List.getLast_eq_getElem, len]

theorem outExt_zero_iff (c : D.Q.A) : w.OutExt 0 c ↔ D.Q.src c = w.vtx 0 ∧
    (if (w.first hn).2 then c ≠ (w.first hn).1
      else D.pval (D.Q.src (w.first hn).1) [(w.first hn).1, c] ≠ 0) := by
  unfold OutExt
  simp only [w.leftL_zero hn, w.rightL_zero hn, reduceCtorEq, false_imp_iff, implies_true,
    Option.some.injEq, forall_eq', true_and]

theorem outExt_last_iff (c : D.Q.A) : w.OutExt (Fin.last _) c ↔ D.Q.src c = w.vtx (Fin.last _) ∧
    (if (w.last hn).2 then D.pval (D.Q.src (w.last hn).1) [(w.last hn).1, c] ≠ 0
      else c ≠ (w.last hn).1) := by
  unfold OutExt
  simp only [w.leftL_last hn, w.rightL_last hn, reduceCtorEq, false_imp_iff, implies_true,
    Option.some.injEq, forall_eq', and_true]

theorem inExt_zero_iff (c : D.Q.A) : w.InExt 0 c ↔ D.Q.tgt c = w.vtx 0 ∧
    (if (w.first hn).2 then D.pval (D.Q.src c) [c, (w.first hn).1] ≠ 0
      else c ≠ (w.first hn).1) := by
  unfold InExt
  simp only [w.leftL_zero hn, w.rightL_zero hn, reduceCtorEq, false_imp_iff, implies_true,
    Option.some.injEq, forall_eq', true_and]

theorem inExt_last_iff (c : D.Q.A) : w.InExt (Fin.last _) c ↔ D.Q.tgt c = w.vtx (Fin.last _) ∧
    (if (w.last hn).2 then c ≠ (w.last hn).1
      else D.pval (D.Q.src c) [c, (w.last hn).1] ≠ 0) := by
  unfold InExt
  simp only [w.leftL_last hn, w.rightL_last hn, reduceCtorEq, false_imp_iff, implies_true,
    Option.some.injEq, forall_eq', and_true]

section Unique

variable (hSB : D.toPathData.IsSpecialBiserial)
include hSB

theorem outExt_zero_unique {c c' : D.Q.A} (h : w.OutExt 0 c) (h' : w.OutExt 0 c') : c = c' := by
  rw [w.outExt_zero_iff hn] at h h'
  have hsrc := w.first_src hn
  rcases hf : w.first hn with ⟨a, d⟩
  rw [hf] at hsrc h h'
  by_contra hcc
  cases d
  · simp only [Letter.src, Bool.false_eq_true, if_false] at hsrc h h'
    exact Word.false_of_card_le_one (hSB.2.2.1 a) (x := c) (y := c')
      ⟨h.1.trans hsrc.symm, h.2⟩ ⟨h'.1.trans hsrc.symm, h'.2⟩ hcc
  · simp only [Letter.src, if_true] at hsrc h h'
    exact Word.false_of_card_le_two (hSB.1 (w.vtx 0)) (x := a) (y := c) (z := c') hsrc h.1 h'.1
      (Ne.symm h.2) (Ne.symm h'.2) hcc

theorem outExt_last_unique {c c' : D.Q.A} (h : w.OutExt (Fin.last _) c)
    (h' : w.OutExt (Fin.last _) c') : c = c' := by
  rw [w.outExt_last_iff hn] at h h'
  have htgt := w.last_tgt hn
  rcases hf : w.last hn with ⟨a, d⟩
  rw [hf] at htgt h h'
  by_contra hcc
  cases d
  · simp only [Letter.tgt, Bool.false_eq_true, if_false] at htgt h h'
    exact Word.false_of_card_le_two (hSB.1 (w.vtx (Fin.last _))) (x := a) (y := c) (z := c')
      htgt h.1 h'.1 (Ne.symm h.2) (Ne.symm h'.2) hcc
  · simp only [Letter.tgt, if_true] at htgt h h'
    exact Word.false_of_card_le_one (hSB.2.2.1 a) (x := c) (y := c')
      ⟨h.1.trans htgt.symm, h.2⟩ ⟨h'.1.trans htgt.symm, h'.2⟩ hcc

theorem inExt_zero_unique {c c' : D.Q.A} (h : w.InExt 0 c) (h' : w.InExt 0 c') : c = c' := by
  rw [w.inExt_zero_iff hn] at h h'
  have hsrc := w.first_src hn
  rcases hf : w.first hn with ⟨a, d⟩
  rw [hf] at hsrc h h'
  by_contra hcc
  cases d
  · simp only [Letter.src, Bool.false_eq_true, if_false] at hsrc h h'
    exact Word.false_of_card_le_two (hSB.2.1 (w.vtx 0)) (x := a) (y := c) (z := c') hsrc h.1 h'.1
      (Ne.symm h.2) (Ne.symm h'.2) hcc
  · simp only [Letter.src, if_true] at hsrc h h'
    exact Word.false_of_card_le_one (hSB.2.2.2 a) (x := c) (y := c')
      ⟨hsrc.trans h.1.symm, h.2⟩ ⟨hsrc.trans h'.1.symm, h'.2⟩ hcc

theorem inExt_last_unique {c c' : D.Q.A} (h : w.InExt (Fin.last _) c)
    (h' : w.InExt (Fin.last _) c') : c = c' := by
  rw [w.inExt_last_iff hn] at h h'
  have htgt := w.last_tgt hn
  rcases hf : w.last hn with ⟨a, d⟩
  rw [hf] at htgt h h'
  by_contra hcc
  cases d
  · simp only [Letter.tgt, Bool.false_eq_true, if_false] at htgt h h'
    exact Word.false_of_card_le_one (hSB.2.2.2 a) (x := c) (y := c')
      ⟨htgt.trans h.1.symm, h.2⟩ ⟨htgt.trans h'.1.symm, h'.2⟩ hcc
  · simp only [Letter.tgt, if_true] at htgt h h'
    exact Word.false_of_card_le_two (hSB.2.1 (w.vtx (Fin.last _))) (x := a) (y := c) (z := c')
      htgt h.1 h'.1 (Ne.symm h.2) (Ne.symm h'.2) hcc

end Unique

omit hn in
theorem isWalk_zero : D.Q.IsWalk (w.vtx 0) w.letters := by
  have : w.vtx 0 = w.start := rfl
  rw [this]; exact w.walk

omit hn in
theorem wend_zero : D.Q.wend (w.vtx 0) w.letters = w.vtx (Fin.last _) := by
  simp [vtx, len, Statement.FinQuiver.wend]

theorem letters_ne_nil : w.letters ≠ [] := by simpa [len] using hn.ne'

section Shapes

variable [IsAlgClosed k] [FiniteDimensional k B] (hD : D.IsGentle) (hs : w.IsString D)
include hD hs

/-- The closed word `w m`. -/
theorem shape_one (m : Letter D.Q) (hms : m.src = w.vtx (Fin.last _)) (hmt : m.tgt = w.vtx 0)
    (h₁ : D.AllowedPair (w.last hn) m) (h₂ : D.AllowedPair m (w.first hn)) :
    ¬ IsRepFinite B := by
  have hL := w.letters_ne_nil hn
  refine D.not_isRepFinite_of_closed hD (w.vtx 0) (w.letters ++ [m]) (by simp) ?_ ?_ ?_ ?_
  · rw [Statement.FinQuiver.isWalk_append, w.wend_zero, Statement.FinQuiver.isWalk_singleton]
    exact ⟨w.isWalk_zero, hms⟩
  · rw [Statement.FinQuiver.wend_append, w.wend_zero, Statement.FinQuiver.wend_singleton, hmt]
  · exact isChain_append_of (w.chain_allowed hs) (List.isChain_singleton m) hL (by simp)
      (by rw [w.getLast_letters hn]; exact h₁)
  · simpa [List.head_append_of_ne_nil hL, w.head_letters hn] using h₂

/-- The closed word `w⁻¹ m`, starting at the last vertex. -/
theorem shape_three (m : Letter D.Q) (hms : m.src = w.vtx 0) (hmt : m.tgt = w.vtx (Fin.last _))
    (h₁ : D.AllowedPair (w.first hn).inv m) (h₂ : D.AllowedPair m (w.last hn).inv) :
    ¬ IsRepFinite B := by
  have hL := w.letters_ne_nil hn
  obtain ⟨hwi, hwe⟩ := Statement.FinQuiver.isWalk_inv (w.vtx 0) w.letters w.isWalk_zero
  rw [w.wend_zero] at hwi hwe
  refine D.not_isRepFinite_of_closed hD (w.vtx (Fin.last _)) (invLetters w.letters ++ [m])
    (by simp) ?_ ?_ ?_ ?_
  · rw [Statement.FinQuiver.isWalk_append, hwe, Statement.FinQuiver.isWalk_singleton]
    exact ⟨hwi, hms⟩
  · rw [Statement.FinQuiver.wend_append, hwe, Statement.FinQuiver.wend_singleton, hmt]
  · refine isChain_append_of (MonomialData.isChain_invLetters (w.chain_allowed hs))
      (List.isChain_singleton m) (invLetters_ne_nil hL) (by simp) ?_
    rw [getLast_invLetters hL, w.head_letters hn]; exact h₁
  · simpa [List.head_append_of_ne_nil (invLetters_ne_nil hL), head_invLetters hL,
      w.getLast_letters hn] using h₂

/-- The closed word `w m₁ w⁻¹ m₂`. -/
theorem shape_two (m₁ m₂ : Letter D.Q) (h₁s : m₁.src = w.vtx (Fin.last _))
    (h₁t : m₁.tgt = w.vtx (Fin.last _)) (h₂s : m₂.src = w.vtx 0) (h₂t : m₂.tgt = w.vtx 0)
    (h₁ : D.AllowedPair (w.last hn) m₁) (h₂ : D.AllowedPair m₁ (w.last hn).inv)
    (h₃ : D.AllowedPair (w.first hn).inv m₂) (h₄ : D.AllowedPair m₂ (w.first hn)) :
    ¬ IsRepFinite B := by
  have hL := w.letters_ne_nil hn
  have hIL := invLetters_ne_nil hL
  obtain ⟨hwi, hwe⟩ := Statement.FinQuiver.isWalk_inv (w.vtx 0) w.letters w.isWalk_zero
  rw [w.wend_zero] at hwi hwe
  refine D.not_isRepFinite_of_closed hD (w.vtx 0)
    (w.letters ++ [m₁] ++ invLetters w.letters ++ [m₂]) (by simp) ?_ ?_ ?_ ?_
  · simp only [Statement.FinQuiver.isWalk_append, Statement.FinQuiver.wend_append, w.wend_zero,
      Statement.FinQuiver.isWalk_singleton, Statement.FinQuiver.wend_singleton, h₁t, hwe]
    exact ⟨⟨⟨w.isWalk_zero, h₁s⟩, hwi⟩, h₂s⟩
  · simp only [Statement.FinQuiver.wend_append, w.wend_zero, Statement.FinQuiver.wend_singleton,
      h₁t, hwe, h₂t]
  · refine isChain_append_of (isChain_append_of (isChain_append_of (w.chain_allowed hs)
      (List.isChain_singleton m₁) hL (by simp) ?_) (MonomialData.isChain_invLetters
        (w.chain_allowed hs)) (by simp) hIL ?_) (List.isChain_singleton m₂) (by simp) (by simp) ?_
    · rw [w.getLast_letters hn]; exact h₁
    · simpa [head_invLetters hL, w.getLast_letters hn] using h₂
    · rw [List.getLast_append_of_ne_nil (by simp) hIL, getLast_invLetters hL, w.head_letters hn]
      exact h₃
  · simpa [List.head_append_of_ne_nil hL, w.head_letters hn] using h₄

/-- The closed word `w⁻¹ m₁ w m₂`, starting at the last vertex. -/
theorem shape_five (m₁ m₂ : Letter D.Q) (h₁s : m₁.src = w.vtx 0) (h₁t : m₁.tgt = w.vtx 0)
    (h₂s : m₂.src = w.vtx (Fin.last _)) (h₂t : m₂.tgt = w.vtx (Fin.last _))
    (h₁ : D.AllowedPair (w.first hn).inv m₁) (h₂ : D.AllowedPair m₁ (w.first hn))
    (h₃ : D.AllowedPair (w.last hn) m₂) (h₄ : D.AllowedPair m₂ (w.last hn).inv) :
    ¬ IsRepFinite B := by
  have hL := w.letters_ne_nil hn
  have hIL := invLetters_ne_nil hL
  obtain ⟨hwi, hwe⟩ := Statement.FinQuiver.isWalk_inv (w.vtx 0) w.letters w.isWalk_zero
  rw [w.wend_zero] at hwi hwe
  refine D.not_isRepFinite_of_closed hD (w.vtx (Fin.last _))
    (invLetters w.letters ++ [m₁] ++ w.letters ++ [m₂]) (by simp) ?_ ?_ ?_ ?_
  · simp only [Statement.FinQuiver.isWalk_append, Statement.FinQuiver.wend_append, hwe,
      Statement.FinQuiver.isWalk_singleton, Statement.FinQuiver.wend_singleton, h₁t, w.wend_zero]
    exact ⟨⟨⟨hwi, h₁s⟩, w.isWalk_zero⟩, h₂s⟩
  · simp only [Statement.FinQuiver.wend_append, hwe, Statement.FinQuiver.wend_singleton,
      h₁t, w.wend_zero, h₂t]
  · refine isChain_append_of (isChain_append_of (isChain_append_of
      (MonomialData.isChain_invLetters (w.chain_allowed hs))
      (List.isChain_singleton m₁) hIL (by simp) ?_) (w.chain_allowed hs) (by simp) hL ?_)
      (List.isChain_singleton m₂) (by simp) (by simp) ?_
    · rw [getLast_invLetters hL, w.head_letters hn]; exact h₁
    · simpa [w.head_letters hn] using h₂
    · rw [List.getLast_append_of_ne_nil (by simp) hL, w.getLast_letters hn]
      exact h₃
  · simpa [List.head_append_of_ne_nil hIL, head_invLetters hL, w.getLast_letters hn] using h₄

end Shapes

end Word

namespace MonomialData

variable {D : MonomialData k B} [IsAlgClosed k] [FiniteDimensional k B]

/-- The closed word `m₁ m₂` of length two. -/
theorem shape_four (hD : D.IsGentle) (m₁ m₂ : Letter D.Q) (h₁₂ : m₁.tgt = m₂.src)
    (h₂₁ : m₂.tgt = m₁.src) (h₁ : D.AllowedPair m₁ m₂) (h₂ : D.AllowedPair m₂ m₁) :
    ¬ IsRepFinite B := by
  refine D.not_isRepFinite_of_closed hD m₁.src [m₁, m₂] (by simp) ?_ ?_ ?_ ?_
  · exact ⟨rfl, h₁₂.symm, trivial⟩
  · simpa [Statement.FinQuiver.wend] using h₂₁
  · simpa using h₁
  · simpa using h₂

end MonomialData

end BrickAccessibility
