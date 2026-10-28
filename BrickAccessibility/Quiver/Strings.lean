module

public import BrickAccessibility.Quiver.CoeffQuiver

/-!
# Strings and string modules (Definitions 3.4–3.6, Construction 3.5)

A letter is an arrow with a direction (`true` for a direct letter `a`, `false`
for a formal inverse `a⁻¹`). A word is a start vertex and a composable list of
letters. Its string diagram has positions `0, …, n`; letter `i` (0-based) joins
positions `i` and `i + 1`, and the arrow acts from `i` to `i + 1` for a direct
letter and from `i + 1` to `i` for an inverse letter.

The coefficient quiver of a word (`Word.coeffQuiver`) records these arrow
actions with coefficient one. A word is a string (`Word.IsString`) when no
position has two outgoing or two incoming edges with the same label (no
adjacent `a a⁻¹` or `a⁻¹ a`) and no directed walk of its diagram spells a zero
path. For monomial data this is Definition 3.4, phrased on the string diagram
(Definition 3.6): a directed walk in a diagram without such forks runs along a
direct or inverse subword. The string module (`Word.stringModule`) is the module
of Construction 3.5.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

/-- A letter: an arrow and a direction (`true` = direct). -/
abbrev Letter (Q : FinQuiver) := Q.A × Bool

namespace Letter

variable {Q : FinQuiver}

/-- The vertex where a letter starts. -/
def src (l : Letter Q) : Q.V := if l.2 then Q.src l.1 else Q.tgt l.1
/-- The vertex where a letter ends. -/
def tgt (l : Letter Q) : Q.V := if l.2 then Q.tgt l.1 else Q.src l.1
/-- The inverse letter. -/
def inv (l : Letter Q) : Letter Q := (l.1, !l.2)

@[simp] theorem src_inv (l : Letter Q) : l.inv.src = l.tgt := by
  cases l with | mk a b => cases b <;> simp [src, tgt, inv]
@[simp] theorem tgt_inv (l : Letter Q) : l.inv.tgt = l.src := by
  cases l with | mk a b => cases b <;> simp [src, tgt, inv]

end Letter

/-- The end vertex of a list of letters started at `x`. -/
def Statement.FinQuiver.wend (Q : FinQuiver) : Q.V → List (Letter Q) → Q.V
  | x, [] => x
  | _, l :: ls => wend Q l.tgt ls

/-- Composability of a list of letters started at `x`. -/
def Statement.FinQuiver.IsWalk (Q : FinQuiver) : Q.V → List (Letter Q) → Prop
  | _, [] => True
  | x, l :: ls => l.src = x ∧ IsWalk Q l.tgt ls

/-- A word: a start vertex and a composable list of letters. -/
structure Word (Q : FinQuiver) where
  /-- The start vertex. -/
  start : Q.V
  /-- The letters, in order. -/
  letters : List (Letter Q)
  walk : Q.IsWalk start letters

namespace Word

variable {Q : FinQuiver} (w : Word Q)

/-- The length of a word. -/
abbrev len : ℕ := w.letters.length

/-- The vertex of a position: the end of the first `j` letters. -/
def vtx (j : Fin (w.len + 1)) : Q.V := Q.wend w.start (w.letters.take j)

theorem isWalk_take_drop {x : Q.V} {ls : List (Letter Q)} (h : Q.IsWalk x ls) (j : ℕ) :
    Q.IsWalk (Q.wend x (ls.take j)) (ls.drop j) := by
  induction ls generalizing x j with
  | nil => simp [FinQuiver.IsWalk]
  | cons l ls ih =>
      cases j with
      | zero => simpa [FinQuiver.wend] using h
      | succ j => simpa [FinQuiver.wend] using ih h.2 j

/-- Letter `i` starts at the vertex of position `i`. -/
theorem src_letter (i : ℕ) (hi : i < w.len) :
    (w.letters[i]'hi).src = w.vtx ⟨i, by omega⟩ := by
  have h := isWalk_take_drop w.walk i
  rw [List.drop_eq_getElem_cons hi] at h
  exact h.1

theorem wend_take_succ {x : Q.V} {ls : List (Letter Q)} (i : ℕ) (hi : i < ls.length) :
    Q.wend x (ls.take (i + 1)) = (ls[i]'hi).tgt := by
  induction ls generalizing x i with
  | nil => simp at hi
  | cons l ls ih =>
      cases i with
      | zero => simp [FinQuiver.wend]
      | succ i => simpa [FinQuiver.wend] using ih i (by simpa using hi)

/-- Letter `i` ends at the vertex of position `i + 1`. -/
theorem tgt_letter (i : ℕ) (hi : i < w.len) :
    (w.letters[i]'hi).tgt = w.vtx ⟨i + 1, by omega⟩ := by
  simp only [vtx]
  rw [wend_take_succ]

/-- The arrow moves of a word: the arrow `a` sends position `i` to `i + 1` if
letter `i` is the direct letter `a`, and to `i - 1` if letter `i - 1` is the
inverse letter `a⁻¹`. -/
def next (a : Q.A) (i : Fin (w.len + 1)) : Option (Fin (w.len + 1)) :=
  if h : ∃ hi : i.val < w.letters.length, w.letters[i.val]'hi = (a, true) then
    some ⟨i.val + 1, by obtain ⟨hi, _⟩ := h; simp only [len]; omega⟩
  else if h' : ∃ hi : 0 < i.val,
      w.letters[i.val - 1]'(by have := i.isLt; simp only [len] at this; omega) = (a, false) then
    some ⟨i.val - 1, by have := i.isLt; omega⟩
  else none

/-- No position of the string diagram has two outgoing or two incoming edges with
the same label: no adjacent `a a⁻¹` or `a⁻¹ a`. -/
def NoForks : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < w.letters.length),
    ¬ ((w.letters[i]'(by omega)).1 = (w.letters[i + 1]'hi).1 ∧
      (w.letters[i]'(by omega)).2 ≠ (w.letters[i + 1]'hi).2)

theorem next_eq_some {a : Q.A} {i j : Fin (w.len + 1)} (h : w.next a i = some j) :
    (∃ hi : i.val < w.letters.length, w.letters[i.val]'hi = (a, true) ∧ j.val = i.val + 1) ∨
    (∃ hi : 0 < i.val, w.letters[i.val - 1]'(by have := i.isLt; simp only [len] at this; omega)
      = (a, false) ∧ j.val = i.val - 1) := by
  unfold next at h
  split_ifs at h with h1 h2
  · obtain ⟨hi, hl⟩ := h1
    left; refine ⟨hi, hl, ?_⟩
    cases h; rfl
  · obtain ⟨hi, hl⟩ := h2
    right; refine ⟨hi, hl, ?_⟩
    cases h; rfl

end Word

namespace Word

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] (D : MonomialData k A)

/-- The coefficient quiver of a word. -/
def coeffQuiver (w : Word D.Q) : D.CoeffQuiver where
  P := Fin (w.len + 1)
  vtx := w.vtx
  next := w.next
  coef _ _ := 1
  next_src a i j h := by
    rcases w.next_eq_some h with ⟨hi, hl, -⟩ | ⟨hi, hl, -⟩
    · have := w.src_letter i.val hi
      rw [hl] at this
      simpa [Letter.src] using this.symm
    · have := w.tgt_letter (i.val - 1) (by have := i.isLt; simp only [len] at this ⊢; omega)
      simp only [hl] at this
      have he : (⟨i.val - 1 + 1, by omega⟩ : Fin (w.len + 1)) = i := by
        ext; simp; omega
      rw [he] at this
      simpa [Letter.tgt] using this.symm
  next_tgt a i j h := by
    rcases w.next_eq_some h with ⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩
    · have := w.tgt_letter i.val hi
      simp only [hl] at this
      have he : (⟨i.val + 1, by simp only [len]; omega⟩ : Fin (w.len + 1)) = j := by
        ext; simp [hj]
      rw [he] at this
      simpa [Letter.tgt] using this.symm
    · have := w.src_letter (i.val - 1) (by have := i.isLt; simp only [len] at this ⊢; omega)
      simp only [hl] at this
      have he : (⟨i.val - 1, by omega⟩ : Fin (w.len + 1)) = j := by
        ext; simp [hj]
      rw [he] at this
      simpa [Letter.src] using this.symm

/-- Definition 3.4: a string is a word without adjacent cancellation whose
string diagram has no directed walk spelling a zero path. -/
def IsString (w : Word D.Q) : Prop := w.NoForks ∧ (w.coeffQuiver D).KillsZeroPaths

/-- Construction 3.5: the string module of a string. -/
abbrev stringModule (w : Word D.Q) (hw : w.IsString D) : Type _ :=
  ((w.coeffQuiver D).toRep hw.2).Carrier

end Word

end BrickAccessibility
