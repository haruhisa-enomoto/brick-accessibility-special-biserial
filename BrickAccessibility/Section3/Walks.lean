module

public import BrickAccessibility.Section4.Inequality

/-!
# Walks in a string diagram

A directed walk in the string diagram of a word without forks runs along a
segment of consecutive letters, all direct (moving right) or all inverse (moving
left), and its coefficient is one (`follow_eq_some_iff`). Consequently the start
and end positions of a walk determine the path it spells (`follow_unique`).
These are the "directed segments" of Section 3.
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

/-- The letters `r, r + 1, …` are the direct letters of `l`. -/
def RightSeg (r : ℕ) (l : List D.Q.A) : Prop :=
  r + l.length ≤ w.len ∧ ∀ (i : ℕ) (hi : i < l.length), w.letters[r + i]? = some (l[i], true)

/-- The letters `r - 1, r - 2, …` are the inverse letters of `l`. -/
def LeftSeg (r : ℕ) (l : List D.Q.A) : Prop :=
  l.length ≤ r ∧ r ≤ w.len ∧ ∀ (i : ℕ) (hi : i < l.length),
    w.letters[r - 1 - i]? = some (l[i], false)

theorem _root_.BrickAccessibility.MonomialData.CoeffQuiver.follow_cons_eq_some
    {D : MonomialData k B} (C : D.CoeffQuiver) {i s : C.P} {a : D.Q.A} {l : List D.Q.A} {c : k} :
    C.follow i (a :: l) = some (s, c) ↔
      ∃ j c', C.next a i = some j ∧ C.follow j l = some (s, c') ∧ c = C.coef a i * c' := by
  constructor
  · intro h
    rcases hj : C.next a i with _ | j
    · simp [MonomialData.CoeffQuiver.follow, hj] at h
    · simp only [MonomialData.CoeffQuiver.follow, hj] at h
      obtain ⟨⟨s', c'⟩, hf, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨j, c', rfl, hf, rfl⟩
  · rintro ⟨j, c', hj, hf, rfl⟩
    simp [MonomialData.CoeffQuiver.follow, hj, hf]

variable (hw : w.NoForks)
include hw

/-- Walks are segments. -/
theorem follow_eq_some {r s : Fin (w.len + 1)} {l : List D.Q.A} {c : k}
    (h : (w.coeffQuiver D).follow r l = some (s, c)) :
    c = 1 ∧ ((w.RightSeg r.val l ∧ s.val = r.val + l.length) ∨
      (w.LeftSeg r.val l ∧ s.val + l.length = r.val)) := by
  induction l generalizing r c with
  | nil =>
      have hr := r.isLt
      simp only [MonomialData.CoeffQuiver.follow, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := id h
      exact ⟨rfl, Or.inl ⟨⟨by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi ↦ by simp at hi⟩, by simp⟩⟩
  | cons a l ih =>
      obtain ⟨j, c', hj, hf, rfl⟩ :=
        ((w.coeffQuiver D).follow_cons_eq_some).mp h
      obtain ⟨hc, hseg⟩ := ih hf
      have hr := r.isLt
      have hjl := j.isLt
      have e : w.len = w.letters.length := rfl
      refine ⟨by rw [hc, mul_one]; rfl, ?_⟩
      change w.next a r = some j at hj
      rcases (w.next_eq_some_iff hw a r j).mp hj with ⟨hr', hl, hjr⟩ | ⟨hr', hl, hjr⟩
      · have hl' : w.letters[r.val]? = some (a, true) := by rw [List.getElem?_eq_getElem hr', hl]
        left
        rcases hseg with ⟨⟨hlen, hseg⟩, hs⟩ | ⟨⟨hlen, hlen', hseg⟩, hs⟩
        · refine ⟨⟨by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi ↦ ?_⟩, by simp only [List.length_cons, List.length_nil] at *; omega⟩
          cases i with
          | zero => simpa using hl'
          | succ i =>
              have := hseg i (by simpa using hi)
              rw [hjr, show r.val + 1 + i = r.val + (i + 1) by omega] at this
              simpa using this
        · cases l with
          | nil =>
              refine ⟨⟨by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi ↦ ?_⟩, by simp only [List.length_cons, List.length_nil] at *; omega⟩
              cases i with
              | zero => simpa using hl'
              | succ i => simp at hi
          | cons b l =>
              exfalso
              have := hseg 0 (by simp)
              rw [hjr, show r.val + 1 - 1 - 0 = r.val by omega, hl'] at this
              simp at this
      · have hl' : w.letters[r.val - 1]? = some (a, false) := by rw [List.getElem?_eq_getElem (by omega), hl]
        right
        rcases hseg with ⟨⟨hlen, hseg⟩, hs⟩ | ⟨⟨hlen, hlen', hseg⟩, hs⟩
        · cases l with
          | nil =>
              refine ⟨⟨by simp only [List.length_cons, List.length_nil] at *; omega, by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi ↦ ?_⟩,
                by simp only [List.length_cons, List.length_nil] at *; omega⟩
              cases i with
              | zero => simpa using hl'
              | succ i => simp at hi
          | cons b l =>
              exfalso
              have := hseg 0 (by simp)
              rw [hjr, show r.val - 1 + 0 = r.val - 1 by omega, hl'] at this
              simp at this
        · refine ⟨⟨by simp only [List.length_cons, List.length_nil] at *; omega, by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi ↦ ?_⟩, by simp only [List.length_cons, List.length_nil] at *; omega⟩
          cases i with
          | zero => simpa using hl'
          | succ i =>
              have := hseg i (by simpa using hi)
              rw [hjr, show r.val - 1 - 1 - i = r.val - 1 - (i + 1) by omega] at this
              simpa using this

omit hw in
theorem next_eq_some_iff' (a : D.Q.A) (i j : Fin (w.len + 1)) (hw : w.NoForks) :
    w.next a i = some j ↔
      (w.letters[i.val]? = some (a, true) ∧ j.val = i.val + 1) ∨
      (0 < i.val ∧ w.letters[i.val - 1]? = some (a, false) ∧ j.val = i.val - 1) := by
  rw [w.next_eq_some_iff hw]
  simp only [List.getElem?_eq_some_iff]
  constructor
  · rintro (⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩)
    · exact Or.inl ⟨⟨hi, hl⟩, hj⟩
    · exact Or.inr ⟨hi, ⟨_, hl⟩, hj⟩
  · rintro (⟨⟨hi, hl⟩, hj⟩ | ⟨hi, ⟨_, hl⟩, hj⟩)
    · exact Or.inl ⟨hi, hl, hj⟩
    · exact Or.inr ⟨hi, hl, hj⟩

/-- A move changes the position by one. -/
theorem next_val {a : D.Q.A} {i j : Fin (w.len + 1)} (h : w.next a i = some j) :
    j.val = i.val + 1 ∨ j.val + 1 = i.val := by
  rcases (w.next_eq_some_iff' a i j hw).mp h with ⟨-, h⟩ | ⟨h0, -, h⟩ <;> omega

/-- Two adjacent positions are joined by at most one move. -/
theorem next_label {a b : D.Q.A} {i j : Fin (w.len + 1)} (ha : w.next a i = some j)
    (hb : w.next b i = some j) : a = b := by
  rcases (w.next_eq_some_iff' a i j hw).mp ha with ⟨ha, hj⟩ | ⟨hpa, ha, hj⟩ <;>
  rcases (w.next_eq_some_iff' b i j hw).mp hb with ⟨hb, hj'⟩ | ⟨-, hb, hj'⟩
  · rw [ha] at hb; simpa using hb
  · omega
  · omega
  · rw [ha] at hb; simpa using hb

theorem next_not_both {a b : D.Q.A} {i j : Fin (w.len + 1)} (ha : w.next a i = some j)
    (hb : w.next b j = some i) : False := by
  rcases (w.next_eq_some_iff' a i j hw).mp ha with ⟨ha, hj⟩ | ⟨hpa, ha, hj⟩ <;>
  rcases (w.next_eq_some_iff' b j i hw).mp hb with ⟨hb, hi⟩ | ⟨hpb, hb, hi⟩
  · omega
  · rw [show j.val - 1 = i.val by omega, ha] at hb; simp at hb
  · rw [show i.val - 1 = j.val by omega, hb] at ha; simp at ha
  · omega

omit hw

/-! ### Oriented segments -/

/-- A segment of the string diagram spelling `l` from position `r`, moving right
(`d = true`) or left (`d = false`). -/
def Seg : Bool → ℕ → List D.Q.A → Prop
  | true, r, l => w.RightSeg r l
  | false, r, l => w.LeftSeg r l

/-- The `j`-th position of an oriented segment from `r`. -/
def spos : Bool → ℕ → ℕ → ℕ
  | true, r, j => r + j
  | false, r, j => r - j

/-- The position just before an oriented segment from `r`. -/
def sprev : Bool → ℕ → ℕ
  | true, r => r - 1
  | false, r => r + 1

@[simp] theorem spos_zero (d : Bool) (r : ℕ) : spos d r 0 = r := by cases d <;> rfl

variable {w}

theorem Seg.le {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) {j : ℕ}
    (hj : j ≤ l.length) : spos d r j ≤ w.len := by
  cases d
  · obtain ⟨h1, h2, -⟩ := id h; simp only [spos]; omega
  · obtain ⟨h1, -⟩ := id h; simp only [spos]; omega

theorem Seg.start_le {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) : r ≤ w.len := by
  simpa using h.le (Nat.zero_le _)

/-- The positions of a segment as elements of `Fin (w.len + 1)`. -/
def Seg.pos {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (j : ℕ) (hj : j ≤ l.length) :
    Fin (w.len + 1) := ⟨spos d r j, Nat.lt_succ_of_le (h.le hj)⟩

@[simp] theorem Seg.pos_val {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (j : ℕ)
    (hj : j ≤ l.length) : (h.pos j hj).val = spos d r j := rfl

theorem Seg.pos_injective {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) {j j' : ℕ}
    (hj : j ≤ l.length) (hj' : j' ≤ l.length) (he : h.pos j hj = h.pos j' hj') : j = j' := by
  have := congrArg Fin.val he
  cases d
  · obtain ⟨h1, -⟩ := id h; simp only [Seg.pos_val, spos] at this; omega
  · simp only [Seg.pos_val, spos] at this; omega

theorem Seg.next {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (hw : w.NoForks)
    {j : ℕ} (hj : j < l.length) :
    w.next l[j] (h.pos j hj.le) = some (h.pos (j + 1) hj) := by
  rw [w.next_eq_some_iff' _ _ _ hw]
  cases d
  · obtain ⟨h1, h2, h3⟩ := id h
    right
    refine ⟨by simp only [Seg.pos_val, spos]; omega, ?_, by simp only [Seg.pos_val, spos]; omega⟩
    simp only [Seg.pos_val, spos]
    rw [show r - j - 1 = r - 1 - j by omega]; exact h3 j hj
  · obtain ⟨h1, h2⟩ := id h
    left
    exact ⟨h2 j hj, by simp only [Seg.pos_val, spos]; omega⟩

/-- A move between two positions of a segment is a step of the segment. -/
theorem Seg.move {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (hw : w.NoForks)
    {x : D.Q.A} {j j' : ℕ} (hj : j ≤ l.length) (hj' : j' ≤ l.length)
    (hm : w.next x (h.pos j hj) = some (h.pos j' hj')) :
    ∃ hjl : j < l.length, j' = j + 1 ∧ x = l[j] := by
  rw [w.next_eq_some_iff' _ _ _ hw] at hm
  simp only [Seg.pos_val] at hm
  cases d
  · obtain ⟨h1, h2, h3⟩ := id h
    simp only [spos] at hm
    rcases hm with ⟨hl, he⟩ | ⟨hpos, hl, he⟩
    · exfalso
      have := h3 (j - 1) (by omega)
      rw [show r - 1 - (j - 1) = r - j by omega, hl] at this
      simp at this
    · refine ⟨by omega, by omega, ?_⟩
      have := h3 j (by omega)
      rw [show r - 1 - j = r - j - 1 by omega, hl] at this
      simpa using this
  · obtain ⟨h1, h2⟩ := id h
    simp only [spos] at hm
    rcases hm with ⟨hl, he⟩ | ⟨hpos, hl, he⟩
    · refine ⟨by omega, by omega, ?_⟩
      have := h2 j (by omega)
      rw [hl] at this
      simpa using this
    · exfalso
      have := h2 (j - 1) (by omega)
      rw [show r + (j - 1) = r + j - 1 by omega, hl] at this
      simp at this

/-- Positions adjacent to a position of a segment. -/
theorem Seg.adj {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) {j : ℕ}
    (hj : j ≤ l.length) {t : ℕ} (ht : t = spos d r j + 1 ∨ t + 1 = spos d r j) :
    (∃ j' ≤ l.length, t = spos d r j') ∨ (j = 0 ∧ t = sprev d r) ∨
      (j = l.length ∧ t = spos d r (l.length + 1)) := by
  cases d
  · obtain ⟨h1, -⟩ := id h
    simp only [spos, sprev] at ht ⊢
    rcases ht with ht | ht
    · by_cases hj0 : j = 0
      · right; left; omega
      · left; exact ⟨j - 1, by omega, by omega⟩
    · by_cases hjL : j = l.length
      · right; right; omega
      · left; exact ⟨j + 1, by omega, by omega⟩
  · simp only [spos, sprev] at ht ⊢
    rcases ht with ht | ht
    · by_cases hjL : j = l.length
      · right; right; omega
      · left; exact ⟨j + 1, by omega, by omega⟩
    · by_cases hj0 : j = 0
      · right; left; omega
      · left; exact ⟨j - 1, by omega, by omega⟩

/-- Extending a segment by a move out of its last position. -/
theorem Seg.extend_right {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (hw : w.NoForks)
    {x : D.Q.A} {t : Fin (w.len + 1)} (hm : w.next x (h.pos l.length le_rfl) = some t)
    (ht : t.val = spos d r (l.length + 1)) : w.Seg d r (l ++ [x]) := by
  rw [w.next_eq_some_iff' _ _ _ hw] at hm
  simp only [Seg.pos_val] at hm
  have htl := t.isLt
  cases d
  · obtain ⟨h1, h2, h3⟩ := id h
    simp only [spos] at hm ht
    rcases hm with ⟨-, he⟩ | ⟨hpos, hl, -⟩
    · omega
    · refine ⟨by simp; omega, by omega, fun i hi ↦ ?_⟩
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hi' : i < l.length
      · rw [List.getElem_append_left hi']; exact h3 i hi'
      · obtain rfl : i = l.length := by omega
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        rw [show r - 1 - l.length = r - l.length - 1 by omega]; exact hl
  · obtain ⟨h1, h2⟩ := id h
    simp only [spos] at hm ht
    rcases hm with ⟨hl, -⟩ | ⟨hpos, -, he⟩
    · refine ⟨by simp; omega, fun i hi ↦ ?_⟩
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hi' : i < l.length
      · rw [List.getElem_append_left hi']; exact h2 i hi'
      · obtain rfl : i = l.length := by omega
        simpa using hl
    · omega

/-- Extending a segment by a move into its first position. -/
theorem Seg.extend_left {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (hw : w.NoForks)
    {x : D.Q.A} {t : Fin (w.len + 1)} (hm : w.next x t = some (h.pos 0 (Nat.zero_le _)))
    (ht : t.val = sprev d r) : w.Seg d t.val (x :: l) := by
  rw [w.next_eq_some_iff' _ _ _ hw] at hm
  simp only [Seg.pos_val, spos_zero] at hm
  have htl := t.isLt
  cases d
  · obtain ⟨h1, h2, h3⟩ := id h
    simp only [sprev] at ht
    rcases hm with ⟨-, he⟩ | ⟨hpos, hl, he⟩
    · omega
    · refine ⟨by simp only [List.length_cons]; omega, by omega, fun i hi ↦ ?_⟩
      cases i with
      | zero => simpa using hl
      | succ i =>
          rw [show t.val - 1 - (i + 1) = r - 1 - i by omega]
          simpa using h3 i (by simpa using hi)
  · obtain ⟨h1, h2⟩ := id h
    simp only [sprev] at ht
    rcases hm with ⟨hl, he⟩ | ⟨hpos, -, he⟩
    · refine ⟨by simp only [List.length_cons]; omega, fun i hi ↦ ?_⟩
      cases i with
      | zero => simpa using hl
      | succ i =>
          rw [show t.val + (i + 1) = r + i by omega]
          simpa using h2 i (by simpa using hi)
    · omega

theorem Seg.drop {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) {n : ℕ}
    (hn : n ≤ l.length) : w.Seg d (spos d r n) (l.drop n) := by
  cases d
  · obtain ⟨h1, h2, h3⟩ := id h
    refine ⟨by simp only [spos, List.length_drop]; omega, by simp only [spos]; omega,
      fun i hi ↦ ?_⟩
    simp only [List.length_drop] at hi
    simp only [spos, List.getElem_drop]
    rw [show r - n - 1 - i = r - 1 - (n + i) by omega]
    exact h3 (n + i) (by omega)
  · obtain ⟨h1, h2⟩ := id h
    refine ⟨by simp only [spos, List.length_drop]; omega, fun i hi ↦ ?_⟩
    simp only [List.length_drop] at hi
    simp only [spos, List.getElem_drop]
    rw [show r + n + i = r + (n + i) by omega]
    exact h2 (n + i) (by omega)

theorem Seg.take {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (n : ℕ) :
    w.Seg d r (l.take n) := by
  cases d
  · obtain ⟨h1, h2, h3⟩ := id h
    refine ⟨by simp; omega, h2, fun i hi ↦ ?_⟩
    simp only [List.length_take] at hi
    simpa using h3 i (by omega)
  · obtain ⟨h1, h2⟩ := id h
    refine ⟨by simp; omega, fun i hi ↦ ?_⟩
    simp only [List.length_take] at hi
    simpa using h2 i (by omega)

/-- Segments are walks. -/
theorem Seg.follow {d : Bool} {r : ℕ} {l : List D.Q.A} (h : w.Seg d r l) (hw : w.NoForks) :
    (w.coeffQuiver D).follow (h.pos 0 (Nat.zero_le _)) l =
      some (h.pos l.length le_rfl, 1) := by
  induction l generalizing r with
  | nil => cases d <;> rfl
  | cons a l ih =>
      have h1 := h.drop (n := 1) (by simp)
      simp only [List.drop_succ_cons, List.drop_zero] at h1
      refine ((w.coeffQuiver D).follow_cons_eq_some).mpr
        ⟨h.pos 1 (by simp), 1, ?_, ?_, by simp; rfl⟩
      · exact h.next hw (j := 0) (by simp)
      · have e1 : h1.pos 0 (Nat.zero_le _) = h.pos 1 (by simp) := by
          ext; simp [Seg.pos]
        have e2 : h1.pos l.length le_rfl = h.pos (a :: l).length le_rfl := by
          ext; cases d <;> simp [Seg.pos, spos] <;> omega
        rw [← e1, ih h1, e2]; rfl

/-- Walks are segments, in `Seg` form. -/
theorem exists_seg_of_follow (hw : w.NoForks) {r s : Fin (w.len + 1)} {l : List D.Q.A} {c : k}
    (h : (w.coeffQuiver D).follow r l = some (s, c)) :
    c = 1 ∧ ∃ d, ∃ hs : w.Seg d r.val l, hs.pos l.length le_rfl = s := by
  obtain ⟨hc, hs⟩ := w.follow_eq_some hw h
  refine ⟨hc, ?_⟩
  rcases hs with ⟨hs, e⟩ | ⟨hs, e⟩
  · have hs' : w.Seg true r.val l := hs
    exact ⟨true, hs', Fin.ext (by rw [Seg.pos_val]; simp only [spos]; omega)⟩
  · have hs' : w.Seg false r.val l := hs
    exact ⟨false, hs', Fin.ext (by rw [Seg.pos_val]; simp only [spos]; omega)⟩

/-- The start and end of a walk determine the path it spells. -/
theorem follow_unique (hw : w.NoForks) {r s : Fin (w.len + 1)} {l l' : List D.Q.A} {c c' : k}
    (h : (w.coeffQuiver D).follow r l = some (s, c))
    (h' : (w.coeffQuiver D).follow r l' = some (s, c')) : l = l' := by
  obtain ⟨-, hs⟩ := w.follow_eq_some hw h
  obtain ⟨-, hs'⟩ := w.follow_eq_some hw h'
  rcases hs with ⟨⟨h1, h2⟩, e⟩ | ⟨⟨h1, h2, h3⟩, e⟩ <;>
  rcases hs' with ⟨⟨h1', h2'⟩, e'⟩ | ⟨⟨h1', h2', h3'⟩, e'⟩
  · have hL : l.length = l'.length := by omega
    refine List.ext_getElem hL fun i hi hi' ↦ ?_
    have := (h2 i hi).symm.trans (h2' i hi')
    simpa using this
  · have hL : l.length = 0 := by omega
    have hL' : l'.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hL, List.length_eq_zero_iff.mp hL']
  · have hL : l.length = 0 := by omega
    have hL' : l'.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hL, List.length_eq_zero_iff.mp hL']
  · have hL : l.length = l'.length := by omega
    refine List.ext_getElem hL fun i hi hi' ↦ ?_
    have := (h3 i hi).symm.trans (h3' i hi')
    simpa using this

end Word

end BrickAccessibility
