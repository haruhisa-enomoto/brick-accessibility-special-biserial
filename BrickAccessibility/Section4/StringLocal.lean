module

public import BrickAccessibility.Section4.Counts

/-!
# Local structure of string diagrams

At a position `j` of a word of length `n`, the letter `j - 1` (if `j > 0`) and the
letter `j` (if `j < n`) are the incident edges. The left letter points into `j`
when it is direct and out of `j` when it is inverse; the right letter points out
of `j` when it is direct and into `j` when it is inverse.

* `next_eq_some_iff`: arrow moves are exactly these edges (for words without
  forks).
* `injMoves`: arrow moves of a string are injective.
* `inCount`, `outCount`: numbers of incoming and outgoing edges, with
  `inCount + outCount = [j > 0] + [j < n]`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

namespace Word

variable {Q : FinQuiver} (w : Word Q)

/-- The letter to the left of position `j`. -/
def leftL (j : Fin (w.len + 1)) : Option (Letter Q) :=
  if h : 0 < j.val then some (w.letters[j.val - 1]'(by have := j.isLt; simp only [len] at this; omega))
  else none

/-- The letter to the right of position `j`. -/
def rightL (j : Fin (w.len + 1)) : Option (Letter Q) :=
  if h : j.val < w.letters.length then some (w.letters[j.val]'h) else none

/-- The number of edges pointing into `j`. -/
def inCount (j : Fin (w.len + 1)) : ℕ :=
  (match w.leftL j with | some l => if l.2 then 1 else 0 | none => 0) +
  (match w.rightL j with | some l => if l.2 then 0 else 1 | none => 0)

/-- The number of edges pointing out of `j`. -/
def outCount (j : Fin (w.len + 1)) : ℕ :=
  (match w.leftL j with | some l => if l.2 then 0 else 1 | none => 0) +
  (match w.rightL j with | some l => if l.2 then 1 else 0 | none => 0)

theorem inCount_add_outCount (j : Fin (w.len + 1)) :
    w.inCount j + w.outCount j =
      (if 0 < j.val then 1 else 0) + (if j.val < w.letters.length then 1 else 0) := by
  unfold inCount outCount leftL rightL
  split_ifs with h1 h2 h2 <;> simp <;> split_ifs <;> simp_all <;> omega

/-- For a word without forks, the arrow moves are exactly the edges. -/
theorem next_eq_some_iff (hw : w.NoForks) (a : Q.A) (i j : Fin (w.len + 1)) :
    w.next a i = some j ↔
      (∃ hi : i.val < w.letters.length, w.letters[i.val]'hi = (a, true) ∧ j.val = i.val + 1) ∨
      (∃ hi : 0 < i.val, w.letters[i.val - 1]'(by have := i.isLt; simp only [len] at this; omega)
        = (a, false) ∧ j.val = i.val - 1) := by
  constructor
  · exact w.next_eq_some
  · rintro (⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩)
    · unfold next
      rw [dif_pos ⟨hi, hl⟩]
      exact congrArg some (Fin.ext hj.symm)
    · unfold next
      rw [dif_neg, dif_pos ⟨hi, hl⟩]
      · exact congrArg some (Fin.ext hj.symm)
      · rintro ⟨hi', hl'⟩
        have := hw (i.val - 1) (by omega)
        simp only [show i.val - 1 + 1 = i.val by omega, hl, hl'] at this
        exact this (by simp)

/-- Arrow moves of a word without forks are injective. -/
theorem next_injective (hw : w.NoForks) {a : Q.A} {i i' j : Fin (w.len + 1)}
    (h : w.next a i = some j) (h' : w.next a i' = some j) : i = i' := by
  rw [w.next_eq_some_iff hw] at h h'
  rcases h with ⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩ <;> rcases h' with ⟨hi', hl', hj'⟩ | ⟨hi', hl', hj'⟩
  · exact Fin.ext (by omega)
  · -- letter `j - 1` is `a` and letter `j` is `a⁻¹`: a fork
    exfalso
    have hlt := i'.isLt
    simp only [len] at hlt
    have := hw i.val (by omega)
    simp only [show i.val + 1 = i'.val - 1 by omega] at this
    rw [hl, hl'] at this
    exact this (by simp)
  · exfalso
    have hlt := i.isLt
    simp only [len] at hlt
    have := hw i'.val (by omega)
    simp only [show i'.val + 1 = i.val - 1 by omega] at this
    rw [hl, hl'] at this
    exact this (by simp)
  · exact Fin.ext (by omega)

end Word

end BrickAccessibility
