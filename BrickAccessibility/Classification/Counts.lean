module

public import BrickAccessibility.Classification.Orbits

/-!
# Each pair occurs at most once

At the positions of a primitive band (`CWord.card_eq`) or of a string
(`Word.card_eq`), a pair of half-words occurs at exactly one position if it is
in the orbit of positions, and at none otherwise. The key point is that a band
or a string is not equal to its own inverse (`leftW_ne_rightW`, `not_symm`): the
middle of a reflection would be a letter equal to its inverse or a fork.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem Letter.inv_ne {Q : FinQuiver} (l : Letter Q) : l.inv ≠ l := by
  obtain ⟨a, d⟩ := l
  cases d <;> simp [Letter.inv]

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)

theorem iter_pred_val_mod (p : Fin b.n) (m : ℕ) : ((b.pred^[m] p).val + m) % b.n = p.val := by
  have := congrArg Fin.val (b.iter_succ_pred p m)
  rwa [iter_succ_val] at this

theorem eq_of_add_mod {x y : Fin b.n} {m : ℕ} (h : (x.val + m) % b.n = (y.val + m) % b.n) :
    x = y := by
  have := Nat.ModEq.add_right_cancel' m h
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt x.2, Nat.mod_eq_of_lt y.2] at this
  exact Fin.ext this

include hA in
/-- A band is not its own inverse. -/
theorem leftW_ne_rightW (p q : Fin b.n) : b.leftW p ≠ b.rightW q := by
  intro h
  have hq : ∀ t, (b.lt (b.pred^[t + 1] p)).inv = b.lt (b.succ^[t] q) := fun t ↦ congrFun h t
  have hqa := q.isLt
  have hpc := p.isLt
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' (p.val + b.n - 1 - q.val)
  · have e : b.pred^[t + 1] p = b.succ^[t] q := by
      refine b.eq_of_add_mod (m := t + 1) ?_
      rw [iter_pred_val_mod, iter_succ_val, Nat.mod_add_mod,
        show q.val + t + (t + 1) = p.val + b.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt p.2]
    have := hq t
    rw [e] at this
    exact Letter.inv_ne _ this
  · have e : b.pred^[t + 1] p = b.succ^[t + 1] q := by
      refine b.eq_of_add_mod (m := t + 1) ?_
      rw [iter_pred_val_mod, iter_succ_val, Nat.mod_add_mod,
        show q.val + (t + 1) + (t + 1) = p.val + b.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt p.2]
    have := hq t
    rw [e, Function.iterate_succ_apply'] at this
    have h2 : b.lt (b.succ (b.succ^[t] q)) = (b.lt (b.succ^[t] q)).inv := by
      rw [← this, Letter.inv_inv']
    apply hA (b.succ^[t] q)
    rw [h2, Signs.st_inv]

include hA in
/-- At a primitive band, the halves determine the position. -/
theorem pos_unique (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) {p p' : Fin b.n}
    {s : Bool} (h1 : b.bhalf S p s = b.bhalf S p' s) (h2 : b.bhalf S p (!s) = b.bhalf S p' (!s)) :
    p = p' := by
  have key : ∀ t, b.bhalf S p t = .inf (b.rightW p) → b.bhalf S p t = b.bhalf S p' t → p = p' := by
    intro t ht he
    rw [ht] at he
    unfold bhalf at he
    split_ifs at he with h
    · exact hprim p p' (HWord.inf.inj he)
    · exact absurd (HWord.inf.inj he).symm (b.leftW_ne_rightW S hA p' p)
  by_cases hs : s = S.st (b.lt p)
  · exact key s (by rw [hs, bhalf_self]) h1
  · refine key (!s) ?_ h2
    rw [show (!s) = S.st (b.lt p) by rw [Bool.eq_not_iff.mpr hs]; simp, bhalf_self]

open Classical in
include hA in
/-- **Counting positions** of a pair at a primitive band. -/
theorem card_eq (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (P : Pair D) :
    Nat.card {p : Fin b.n // b.vtx p = P.1 ∧ P.2.2.1 = b.bhalf S p P.2.1 ∧
      P.2.2.2 = b.bhalf S p (!P.2.1)} = if P ∈ b.Pos S then 1 else 0 := by
  obtain ⟨v, s, h, h'⟩ := P
  dsimp only
  split_ifs with hP
  · obtain ⟨q, s', e⟩ := hP
    simp only [pairAt, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨⟨q, rfl, rfl, rfl⟩⟩⟩
    obtain ⟨x, -, hx1, hx2⟩ := x
    obtain ⟨y, -, hy1, hy2⟩ := y
    exact b.pos_unique S hA hprim (hx1.symm.trans hy1) (hx2.symm.trans hy2)
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨p, hv, h1, h2⟩ ↦ hP ⟨p, s, ?_⟩⟩
    simp only [pairAt, hv, h1, h2]

end CWord

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (S : D.Signs)

theorem getElem?_right (p : Fin (w.len + 1)) (j : ℕ) :
    (w.right p)[j]? = w.letters[p.val + j]? := by
  simp [right, List.getElem?_drop]

theorem getElem?_left (p : Fin (w.len + 1)) (j : ℕ) (hj : j < p.val) :
    (w.left p)[j]? = (w.letters[p.val - 1 - j]?).map Letter.inv := by
  have hp := p.isLt
  simp only [left, invLetters]
  rw [List.getElem?_reverse (by simp [Word.len] at hp ⊢; omega)]
  simp only [List.length_map, List.length_take, List.getElem?_map]
  rw [List.getElem?_take_of_lt (by simp [Word.len] at hp ⊢; omega)]
  congr 2
  simp [Word.len] at hp ⊢; omega

/-- A string with letters is not its own inverse. -/
theorem not_symm (hnf : w.NoForks) (hn : 0 < w.len) {p p' : Fin (w.len + 1)}
    (h1 : w.right p = w.left p') (h2 : w.left p = w.right p') : False := by
  have l1 := congrArg List.length h1
  have l2 := congrArg List.length h2
  rw [length_right, length_left] at l1
  rw [length_right, length_left] at l2
  have hp := p.isLt
  have sym : ∀ i (hi : i < w.len), w.letters[i]? = (w.letters[w.len - 1 - i]?).map Letter.inv := by
    intro i hi
    by_cases hpi : p.val ≤ i
    · have := congrArg (·[i - p.val]?) h1
      rw [getElem?_right, getElem?_left _ _ _ (by omega), show p.val + (i - p.val) = i by omega,
        show p'.val - 1 - (i - p.val) = w.len - 1 - i by omega] at this
      exact this
    · have := congrArg (·[p.val - 1 - i]?) h2
      rw [getElem?_right, getElem?_left _ _ _ (by omega), show p.val - 1 - (p.val - 1 - i) = i by omega,
        show p'.val + (p.val - 1 - i) = w.len - 1 - i by omega] at this
      rw [← this, Option.map_map]
      simp [Function.comp_def, Letter.inv_inv']
  have hlen : w.len = w.letters.length := rfl
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (w.len - 1)
  · have := sym m (by omega)
    rw [show w.len - 1 - m = m by omega] at this
    rw [List.getElem?_eq_getElem (by omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact Letter.inv_ne _ this.symm
  · have := sym m (by omega)
    rw [show w.len - 1 - m = m + 1 by omega] at this
    rw [List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    apply hnf m (by omega)
    rw [this]
    simp [Letter.inv]

/-- At a string, the halves determine the position. -/
theorem pos_unique (hnf : w.NoForks) {p p' : Fin (w.len + 1)} {s : Bool}
    (h1 : w.half S p s = w.half S p' s) (h2 : w.half S p (!s) = w.half S p' (!s)) : p = p' := by
  have hp := p.isLt
  have hp' := p'.isLt
  rcases Nat.eq_zero_or_pos w.len with hn | hn
  · exact Fin.ext (by omega)
  have key : ∀ t, w.half S p t = w.right p → w.half S p (!t) = w.left p →
      w.half S p t = w.half S p' t → w.half S p (!t) = w.half S p' (!t) → p = p' := by
    intro t ht ht' e1 e2
    rw [ht] at e1
    rw [ht'] at e2
    unfold half at e1 e2
    by_cases hts : t = w.sideSign S p'
    · rw [if_pos hts] at e1
      have := congrArg List.length e1
      rw [length_right, length_right] at this
      exact Fin.ext (by omega)
    · rw [if_neg hts] at e1
      rw [if_pos (by rw [Bool.eq_not_iff.mpr hts]; simp)] at e2
      exact (w.not_symm hnf hn e1 e2).elim
  by_cases hs : s = w.sideSign S p
  · exact key s (by rw [hs, half_self]) (by rw [hs, half_not]) h1 h2
  · have hs' : (!s) = w.sideSign S p := by rw [Bool.eq_not_iff.mpr hs]; simp
    refine key (!s) (by rw [hs', half_self]) (by rw [Bool.not_not, ← Bool.not_not s, hs', half_not])
      h2 (by rw [Bool.not_not]; exact h1)

open Classical in
/-- **Counting positions** of a pair at a string. -/
theorem card_eq (hnf : w.NoForks) (P : Pair D) :
    Nat.card {p : Fin (w.len + 1) // w.vtx p = P.1 ∧ P.2.2.1 = .fin (w.half S p P.2.1) ∧
      P.2.2.2 = .fin (w.half S p (!P.2.1))} = if P ∈ w.Pos S then 1 else 0 := by
  obtain ⟨v, s, h, h'⟩ := P
  dsimp only
  split_ifs with hP
  · obtain ⟨q, s', e⟩ := hP
    simp only [pairAt, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨⟨q, rfl, rfl, rfl⟩⟩⟩
    obtain ⟨x, -, hx1, hx2⟩ := x
    obtain ⟨y, -, hy1, hy2⟩ := y
    exact w.pos_unique S hnf (HWord.fin.inj (hx1.symm.trans hy1))
      (HWord.fin.inj (hx2.symm.trans hy2))
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨p, hv, h1, h2⟩ ↦ hP ⟨p, s, ?_⟩⟩
    simp only [pairAt, hv, h1, h2]

end Word

end BrickAccessibility
