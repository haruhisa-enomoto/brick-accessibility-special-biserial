module

public import BrickAccessibility.Classification.Realize

/-!
# Bands as block quivers

A cyclic word is a nonempty closed walk `l_0 ⋯ l_{n-1}` at `v`; position `i`
(in `Fin n`) lies over the start of `l_i`, and `l_i` joins positions `i` and
`i + 1`. Given an automorphism `φ` of a block space `V`, the band block quiver
has the moves of the letters, the identity on all moves except the one of
`l_{n-1}`, which carries `φ` (or `φ⁻¹` if `l_{n-1}` is inverse).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- A cyclic word. -/
structure CWord (Q : FinQuiver) where
  start : Q.V
  letters : List (Letter Q)
  ne : letters ≠ []
  walk : Q.IsWalk start letters
  closed : Q.wend start letters = start

namespace CWord

variable {Q : FinQuiver} (b : CWord Q)

/-- The length. -/
abbrev n : ℕ := b.letters.length

theorem n_pos : 0 < b.n := List.length_pos_iff.mpr b.ne

/-- The next position. -/
def succ (i : Fin b.n) : Fin b.n := ⟨(i.val + 1) % b.n, Nat.mod_lt _ b.n_pos⟩

/-- The previous position. -/
def pred (i : Fin b.n) : Fin b.n := ⟨(i.val + b.n - 1) % b.n, Nat.mod_lt _ b.n_pos⟩

theorem succ_val_of_lt (i : Fin b.n) (h : i.val + 1 < b.n) : (b.succ i).val = i.val + 1 :=
  Nat.mod_eq_of_lt h

theorem succ_val_of_last (i : Fin b.n) (h : i.val + 1 = b.n) : (b.succ i).val = 0 := by
  simp [succ, h]

theorem pred_val_of_pos (i : Fin b.n) (h : 0 < i.val) : (b.pred i).val = i.val - 1 := by
  simp only [pred]
  rw [show i.val + b.n - 1 = (i.val - 1) + b.n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem pred_val_of_zero (i : Fin b.n) (h : i.val = 0) : (b.pred i).val = b.n - 1 := by
  simp only [pred, h, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by have := b.n_pos; omega)

@[simp] theorem succ_pred (i : Fin b.n) : b.succ (b.pred i) = i := by
  ext
  by_cases h : i.val = 0
  · rw [succ_val_of_last _ _ (by rw [pred_val_of_zero _ _ h]; have := b.n_pos; omega), h]
  · rw [succ_val_of_lt _ _ (by rw [pred_val_of_pos _ _ (by omega)]; omega),
      pred_val_of_pos _ _ (by omega)]
    omega

@[simp] theorem pred_succ (i : Fin b.n) : b.pred (b.succ i) = i := by
  ext
  by_cases h : i.val + 1 = b.n
  · rw [pred_val_of_zero _ _ (succ_val_of_last _ _ h)]; omega
  · have h' : i.val + 1 < b.n := by have := i.isLt; omega
    rw [pred_val_of_pos _ _ (by rw [succ_val_of_lt _ _ h']; omega), succ_val_of_lt _ _ h']
    omega

theorem start_eq : (b.letters[0]'b.n_pos).src = b.start := by
  have h := b.walk
  rw [← List.cons_head_tail b.ne] at h
  rw [List.getElem_zero]
  exact h.1

/-- The letter at a position. -/
def lt (i : Fin b.n) : Letter Q := b.letters[i.val]

/-- The vertex of a position. -/
def vtx (i : Fin b.n) : Q.V := (b.lt i).src

theorem lt_tgt (i : Fin b.n) : (b.lt i).tgt = b.vtx (b.succ i) := by
  by_cases hi : i.val + 1 < b.n
  · have hw := Word.isWalk_take_drop b.walk (i.val + 1)
    simp only [vtx, lt, succ_val_of_lt _ _ hi]
    rw [List.drop_eq_getElem_cons hi] at hw
    rw [hw.1, ← Word.wend_take_succ i.val i.isLt]
  · have hlast : i.val + 1 = b.n := by have := i.isLt; omega
    simp only [vtx, lt, succ_val_of_last _ _ hlast]
    have h1 : (b.letters[i.val]).tgt = Q.wend b.start b.letters := by
      rw [← Word.wend_take_succ i.val i.isLt, List.take_of_length_le (le_of_eq hlast.symm)]
    rw [h1, b.closed]
    exact b.start_eq.symm

/-- The arrow moves of a cyclic word. -/
def next (a : Q.A) (i : Fin b.n) : Option (Fin b.n) :=
  if b.lt i = (a, true) then some (b.succ i)
  else if b.lt (b.pred i) = (a, false) then some (b.pred i) else none

/-- The last position. -/
def last : Fin b.n := ⟨b.n - 1, by have := b.n_pos; omega⟩

/-- The first position. -/
def first : Fin b.n := ⟨0, b.n_pos⟩

theorem succ_last : b.succ b.last = b.first := by
  ext; rw [succ_val_of_last _ _ (by simp [last]; have := b.n_pos; omega)]; rfl

theorem pred_first : b.pred b.first = b.last := by
  ext; rw [pred_val_of_zero _ _ rfl]; rfl

variable {D : MonomialData k B} (S : D.Signs)

/-- Cyclic sign alternation. -/
def Alt (b : CWord D.Q) : Prop := ∀ i, S.st (b.lt (b.succ i)) ≠ S.en (b.lt i)

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q)

theorem not_fork (hA : b.Alt S) (i : Fin b.n) (a : D.Q.A) (d : Bool)
    (h1 : b.lt i = (a, d)) (h2 : b.lt (b.succ i) = (a, !d)) : False := by
  have := hA i
  rw [h1, h2] at this
  cases d <;> simp at this

theorem next_src (a : D.Q.A) (i j : Fin b.n) (h : b.next a i = some j) :
    b.vtx i = D.Q.src a := by
  unfold next at h
  split_ifs at h with h1 h2
  · simp only [vtx, h1, Letter.src, if_true]
  · have := b.lt_tgt (b.pred i)
    rw [succ_pred, h2] at this
    simp only [Letter.tgt, Bool.false_eq_true, if_false] at this
    exact this.symm

theorem next_tgt (a : D.Q.A) (i j : Fin b.n) (h : b.next a i = some j) :
    b.vtx j = D.Q.tgt a := by
  unfold next at h
  split_ifs at h with h1 h2
  · cases h
    have := b.lt_tgt i
    rw [h1] at this
    simp only [Letter.tgt, if_true] at this
    exact this.symm
  · cases h
    simp only [vtx, h2, Letter.src, Bool.false_eq_true, if_false]

theorem next_inj (hA : b.Alt S) (a : D.Q.A) (i i' j : Fin b.n) (h : b.next a i = some j)
    (h' : b.next a i' = some j) : i = i' := by
  unfold next at h h'
  split_ifs at h h' with h1 h2 h3 h4 h3 h4 <;> cases h <;> simp only [Option.some.injEq] at h'
  · have := congrArg b.pred h'; simpa using this.symm
  · -- `l_i = a`, `l_{pred i'} = a⁻¹`, `succ i = pred i'`
    exfalso
    exact b.not_fork S hA i a true h1 (by rw [← h', h3]; rfl)
  · exfalso
    exact b.not_fork S hA i' a true h3 (by rw [h', h4]; rfl)
  · have := congrArg b.succ h'; simpa using this.symm

/-- The band block quiver with twist `φ`. -/
def blockQuiver (hA : b.Alt S) (V : Type u) [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V) :
    D.BlockQuiver V where
  P := Fin b.n
  vtx := b.vtx
  next := b.next
  g a i := if i = b.last ∧ b.lt b.last = (a, true) then φ
    else if i = b.first ∧ b.lt b.last = (a, false) then φ.symm else LinearEquiv.refl k V
  next_src := b.next_src
  next_tgt := b.next_tgt
  inj := b.next_inj S hA

open Classical in
/-- Following arrows through positions. -/
def followPos : Fin b.n → List D.Q.A → Option (Fin b.n)
  | i, [] => some i
  | i, a :: l => match b.next a i with
    | none => none
    | some j => followPos j l

theorem blockQuiver_follow_none (hA : b.Alt S) (V : Type u) [AddCommGroup V] [Module k V]
    (φ : V ≃ₗ[k] V) (i : Fin b.n) (l : List D.Q.A) :
    (b.blockQuiver S hA V φ).follow i l = none ↔ b.followPos i l = none := by
  induction l generalizing i with
  | nil => simp [MonomialData.BlockQuiver.follow, followPos]
  | cons a l ih =>
      simp only [MonomialData.BlockQuiver.follow, followPos]
      have e : (b.blockQuiver S hA V φ).next a i = b.next a i := rfl
      rw [e]
      cases b.next a i with
      | none => simp
      | some j => simp only [Option.map_eq_none_iff]; exact ih j

/-- No walk around the cyclic word spells a zero path. -/
def KillsZero : Prop :=
  ∀ x l, D.pval x l = 0 → ∀ i, b.vtx i = x → b.followPos i l = none

theorem blockQuiver_kills (hA : b.Alt S) (hK : b.KillsZero) (V : Type u) [AddCommGroup V]
    [Module k V] (φ : V ≃ₗ[k] V) : (b.blockQuiver S hA V φ).KillsZeroPaths := by
  intro x l hxl i hi
  exact (b.blockQuiver_follow_none S hA V φ i l).mpr (hK x l hxl i hi)

end CWord


end BrickAccessibility
