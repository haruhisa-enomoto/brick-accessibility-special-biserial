module

public import BrickAccessibility.Classification.RealizeInf
public import BrickAccessibility.Classification.StringShift

/-!
# Orbits of pairs of half-words

A pair `(v, s, h, h')` of half-words shifts across the first letter `l` of `h` to
`(l.tgt, !ε l, h₁, l⁻¹ h')` (`Signs.Step`), and swaps to `(v, !s, h', h)`. The
pairs at the positions of a string or a band form exactly one orbit of the
generated equivalence (`Word.orbit_iff`, `CWord.orbit_iff`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem HWord.cons_inj {Q : FinQuiver} {l l' : Letter Q} {h h' : HWord Q}
    (e : h.cons l = h'.cons l') : l = l' ∧ h = h' := by
  cases h with
  | fin C =>
      cases h' with
      | fin C' =>
          simp only [HWord.cons, HWord.fin.injEq, List.cons.injEq] at e
          exact ⟨e.1, by rw [e.2]⟩
      | inf f' => simp [HWord.cons] at e
  | inf f =>
      cases h' with
      | fin C' => simp [HWord.cons] at e
      | inf f' =>
          simp only [HWord.cons, HWord.inf.injEq] at e
          refine ⟨congrFun e 0, ?_⟩
          congr 1; funext i; exact congrFun e (i + 1)

namespace MonomialData

variable {D : MonomialData k B} (S : D.Signs)

/-- A pair of half-words at a vertex, with the sign of the first one. -/
abbrev Pair (D : MonomialData k B) := D.Q.V × Bool × HWord D.Q × HWord D.Q

/-- Swapping the two half-words. -/
def Pair.swap (P : Pair D) : Pair D := (P.1, !P.2.1, P.2.2.2, P.2.2.1)

@[simp] theorem Pair.swap_swap (P : Pair D) : P.swap.swap = P := by
  simp [Pair.swap]

/-- The shift across the first letter of the first half-word. -/
def Signs.Step (P P' : Pair D) : Prop :=
  ∃ (l : Letter D.Q) (h₁ : HWord D.Q), l.src = P.1 ∧ S.st l = P.2.1 ∧ P.2.2.1 = h₁.cons l ∧
    P' = (l.tgt, !S.en l, h₁, P.2.2.2.cons l.inv)

/-- The orbit relation of pairs. -/
def Signs.Orbit : Pair D → Pair D → Prop :=
  Relation.EqvGen fun P P' ↦ S.Step P P' ∨ P' = P.swap

theorem Signs.Orbit.equivalence : Equivalence S.Orbit := Relation.EqvGen.is_equivalence _

/-- A set of pairs closed under shifts and swaps is a union of orbits. -/
theorem Signs.mem_of_orbit (T : Set (Pair D)) (hstep : ∀ P ∈ T, ∀ P', S.Step P P' → P' ∈ T)
    (hswap : ∀ P ∈ T, P.swap ∈ T) {P P' : Pair D} (h : S.Orbit P P') : P ∈ T ↔ P' ∈ T := by
  induction h with
  | rel P P' hr =>
      rcases hr with hr | rfl
      · refine ⟨fun hP ↦ hstep P hP P' hr, fun hP' ↦ ?_⟩
        obtain ⟨l, h₁, hsrc, hst, hh, rfl⟩ := hr
        have h1 := hswap _ hP'
        have h2 : S.Step (Pair.swap (l.tgt, !S.en l, h₁, P.2.2.2.cons l.inv))
            (l.src, !S.st l, P.2.2.2, h₁.cons l) := by
          refine ⟨l.inv, P.2.2.2, by simp [Pair.swap], by simp [Pair.swap, Signs.st_inv], rfl, ?_⟩
          simp [Pair.swap, Signs.en_inv, Letter.inv_inv']
        have h3 := hswap _ (hstep _ h1 _ h2)
        have e : Pair.swap (l.src, !S.st l, P.2.2.2, h₁.cons l) = P := by
          obtain ⟨v, s, h, h'⟩ := P
          simp only at hsrc hst hh
          simp [Pair.swap, hsrc, hst, hh]
        rwa [e] at h3
      · exact ⟨hswap P, fun h ↦ by simpa using hswap _ h⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A set closed under shifts and swaps and contained in one orbit is the orbit of each of
its members. -/
theorem Signs.orbit_iff_of_closed (T : Set (Pair D))
    (hstep : ∀ P ∈ T, ∀ P', S.Step P P' → P' ∈ T) (hswap : ∀ P ∈ T, P.swap ∈ T)
    {P₀ : Pair D} (hconn : ∀ P ∈ T, S.Orbit P₀ P) {P : Pair D} (hP : P ∈ T) (P' : Pair D) :
    S.Orbit P P' ↔ P' ∈ T := by
  constructor
  · intro h; exact (S.mem_of_orbit T hstep hswap h).mp hP
  · intro h
    exact (Signs.Orbit.equivalence S).trans ((Signs.Orbit.equivalence S).symm (hconn P hP)) (hconn P' h)

theorem Signs.step_unique {P P' P'' : Pair D} (h1 : S.Step P P') (h2 : S.Step P P'') :
    P' = P'' := by
  obtain ⟨l, h, -, -, e, rfl⟩ := h1
  obtain ⟨l', h', -, -, e', rfl⟩ := h2
  obtain ⟨rfl, rfl⟩ := HWord.cons_inj (e.symm.trans e')
  rfl

end MonomialData

open MonomialData

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hs : w.IsString D) (S : D.Signs)

/-- The pair at a position of a string, with a chosen sign. -/
def pairAt (q : Fin (w.len + 1)) (s : Bool) : Pair D :=
  (w.vtx q, s, .fin (w.half S q s), .fin (w.half S q (!s)))

/-- The pairs at the positions of a string. -/
def Pos : Set (Pair D) := {P | ∃ q s, P = w.pairAt S q s}

theorem pairAt_swap (q : Fin (w.len + 1)) (s : Bool) : (w.pairAt S q s).swap = w.pairAt S q (!s) := by
  simp [pairAt, Pair.swap]

theorem half_self (q : Fin (w.len + 1)) : w.half S q (w.sideSign S q) = w.right q := by
  simp [half]

theorem half_not (q : Fin (w.len + 1)) : w.half S q (!w.sideSign S q) = w.left q := by
  simp [half]

include hs in
theorem step_succ (q : ℕ) (hq : q < w.len) :
    S.Step (w.pairAt S ⟨q, by omega⟩ (w.sideSign S ⟨q, by omega⟩))
      (w.pairAt S ⟨q + 1, by omega⟩ (w.sideSign S ⟨q + 1, by omega⟩)) := by
  refine ⟨w.letters[q], .fin (w.right ⟨q + 1, by omega⟩), w.src_letter q hq,
    (w.sideSign_of_lt S q hq).symm, ?_, ?_⟩
  · show HWord.fin (w.half S _ _) = _
    rw [half_self, w.right_cons ⟨q, by omega⟩ hq]; rfl
  · simp only [pairAt, half_self, half_not]
    rw [w.tgt_letter q hq, w.sideSign_succ hs S q hq]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    dsimp only
    rw [w.left_cons ⟨q + 1, by omega⟩ (by simp)]
    rfl

include hs in
theorem step_pred (q : ℕ) (hq : q < w.len) :
    S.Step (w.pairAt S ⟨q + 1, by omega⟩ (!w.sideSign S ⟨q + 1, by omega⟩))
      (w.pairAt S ⟨q, by omega⟩ (!w.sideSign S ⟨q, by omega⟩)) := by
  have hl := w.left_cons ⟨q + 1, by omega⟩ (by simp)
  simp only [Nat.add_sub_cancel] at hl
  refine ⟨(w.letters[q]).inv, .fin (w.left ⟨q, by omega⟩), ?_, ?_, ?_, ?_⟩
  · rw [Letter.src_inv, w.tgt_letter q hq]; rfl
  · show S.st _ = !w.sideSign S _
    rw [Signs.st_inv]
    have := w.en_left_eq hs S ⟨q + 1, by omega⟩ (by simp)
    simpa using this
  · show HWord.fin (w.half S _ _) = _
    rw [half_not, hl]; rfl
  · simp only [pairAt, half_self, half_not, Bool.not_not]
    rw [Letter.tgt_inv, w.src_letter q hq, Signs.en_inv, w.sideSign_of_lt S q hq]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    dsimp only
    rw [w.right_cons ⟨q, by omega⟩ hq, Letter.inv_inv']
    rfl

include hs in
theorem pos_step (P : Pair D) (hP : P ∈ w.Pos S) (P' : Pair D) (h : S.Step P P') :
    P' ∈ w.Pos S := by
  obtain ⟨q, s, rfl⟩ := hP
  have h0 := h
  obtain ⟨l, h₁, -, -, e, -⟩ := h0
  by_cases hsq : s = w.sideSign S q
  · subst hsq
    by_cases hq : q.val < w.len
    · refine ⟨⟨q.val + 1, by omega⟩, _, S.step_unique h (w.step_succ hs S q.val hq)⟩
    · exfalso
      have : w.right q = [] := by simp only [right]; simp only [Word.len] at hq; simp; omega
      simp only [pairAt, half_self, this] at e
      cases h₁ <;> simp [HWord.cons] at e
  · have hsq' : s = !w.sideSign S q := Bool.eq_not_iff.mpr hsq
    subst hsq'
    by_cases hq : 0 < q.val
    · have e1 : q = ⟨(q.val - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
      have := w.step_pred hs S (q.val - 1) (by have := q.isLt; omega)
      rw [← e1] at this
      exact ⟨_, _, S.step_unique h this⟩
    · exfalso
      have hq0 : q.val = 0 := by omega
      have : w.left q = [] := by simp [left, invLetters, hq0]
      simp only [pairAt, half_not, this] at e
      cases h₁ <;> simp [HWord.cons] at e

theorem pos_swap (P : Pair D) (hP : P ∈ w.Pos S) : P.swap ∈ w.Pos S := by
  obtain ⟨q, s, rfl⟩ := hP
  exact ⟨q, !s, w.pairAt_swap S q s⟩

include hs in
theorem pos_conn (P : Pair D) (hP : P ∈ w.Pos S) : S.Orbit (w.pairAt S 0 true) P := by
  obtain ⟨q, s, rfl⟩ := hP
  have hsw : ∀ q s, S.Orbit (w.pairAt S q s) (w.pairAt S q (!s)) := fun q s ↦
    Relation.EqvGen.rel _ _ (Or.inr (w.pairAt_swap S q s).symm)
  have key : ∀ (m : ℕ) (hm : m < w.len + 1) (s : Bool),
      S.Orbit (w.pairAt S 0 true) (w.pairAt S ⟨m, hm⟩ s) := by
    intro m
    induction m with
    | zero =>
        intro hm s
        cases s
        · exact hsw 0 true
        · exact Relation.EqvGen.refl _
    | succ m ih =>
        intro hm s
        have h1 : S.Orbit (w.pairAt S 0 true) (w.pairAt S ⟨m + 1, hm⟩
            (w.sideSign S ⟨m + 1, hm⟩)) :=
          Relation.EqvGen.trans _ _ _ (ih (by omega) _)
            (Relation.EqvGen.rel _ _ (Or.inl (w.step_succ hs S m (by omega))))
        by_cases hs' : s = w.sideSign S ⟨m + 1, hm⟩
        · rw [hs']; exact h1
        · rw [Bool.eq_not_iff.mpr hs']
          exact Relation.EqvGen.trans _ _ _ h1 (hsw _ _)
  exact key q.val q.isLt s

include hs in
/-- The positions of a string form one orbit. -/
theorem orbit_iff {P : Pair D} (hP : P ∈ w.Pos S) (P' : Pair D) :
    S.Orbit P P' ↔ P' ∈ w.Pos S :=
  S.orbit_iff_of_closed (w.Pos S) (w.pos_step hs S) (w.pos_swap S) (w.pos_conn hs S) hP P'

end Word

namespace MonomialData

end MonomialData

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)

/-- The pair at a position of a band, with a chosen sign. -/
def pairAt (q : Fin b.n) (s : Bool) : Pair D := (b.vtx q, s, b.bhalf S q s, b.bhalf S q (!s))

/-- The pairs at the positions of a band. -/
def Pos : Set (Pair D) := {P | ∃ q s, P = b.pairAt S q s}

theorem pairAt_swap (q : Fin b.n) (s : Bool) : (b.pairAt S q s).swap = b.pairAt S q (!s) := by
  simp [pairAt, Pair.swap]

theorem bhalf_self (q : Fin b.n) : b.bhalf S q (S.st (b.lt q)) = .inf (b.rightW q) := by
  simp [bhalf]

theorem bhalf_not (q : Fin b.n) : b.bhalf S q (!S.st (b.lt q)) = .inf (b.leftW q) := by
  simp [bhalf]

include hA

theorem step_succ (q : Fin b.n) :
    S.Step (b.pairAt S q (S.st (b.lt q))) (b.pairAt S (b.succ q) (S.st (b.lt (b.succ q)))) := by
  refine ⟨b.lt q, .inf (b.rightW (b.succ q)), rfl, rfl, by
    show b.bhalf S q _ = _; rw [bhalf_self, rightW_cons], ?_⟩
  simp only [pairAt, bhalf_self, bhalf_not]
  rw [b.lt_tgt, b.st_succ S hA, leftW_cons]

theorem step_pred (q : Fin b.n) :
    S.Step (b.pairAt S (b.succ q) (!S.st (b.lt (b.succ q)))) (b.pairAt S q (!S.st (b.lt q))) := by
  have hen : S.en (b.lt q) = !S.st (b.lt (b.succ q)) := by rw [b.st_succ S hA]; simp
  refine ⟨(b.lt q).inv, .inf (b.leftW q), by rw [Letter.src_inv, b.lt_tgt]; rfl,
    by rw [Signs.st_inv]; exact hen, by show b.bhalf S _ _ = _; rw [bhalf_not, leftW_cons], ?_⟩
  simp only [pairAt, bhalf_self, bhalf_not, Bool.not_not]
  rw [Letter.tgt_inv, Signs.en_inv, rightW_cons, Letter.inv_inv']
  rfl

theorem pos_step (P : Pair D) (hP : P ∈ b.Pos S) (P' : Pair D) (h : S.Step P P') :
    P' ∈ b.Pos S := by
  obtain ⟨q, s, rfl⟩ := hP
  by_cases hsq : s = S.st (b.lt q)
  · subst hsq
    exact ⟨_, _, S.step_unique h (b.step_succ S hA q)⟩
  · have hsq' : s = !S.st (b.lt q) := Bool.eq_not_iff.mpr hsq
    subst hsq'
    have := b.step_pred S hA (b.pred q)
    rw [succ_pred] at this
    exact ⟨_, _, S.step_unique h this⟩

omit hA in
theorem pos_swap (P : Pair D) (hP : P ∈ b.Pos S) : P.swap ∈ b.Pos S := by
  obtain ⟨q, s, rfl⟩ := hP
  exact ⟨q, !s, b.pairAt_swap S q s⟩

theorem pos_conn (P : Pair D) (hP : P ∈ b.Pos S) : S.Orbit (b.pairAt S b.first true) P := by
  obtain ⟨q, s, rfl⟩ := hP
  have hsw : ∀ q s, S.Orbit (b.pairAt S q s) (b.pairAt S q (!s)) := fun q s ↦
    Relation.EqvGen.rel _ _ (Or.inr (b.pairAt_swap S q s).symm)
  have key : ∀ (m : ℕ) (hm : m < b.n) (s : Bool),
      S.Orbit (b.pairAt S b.first true) (b.pairAt S ⟨m, hm⟩ s) := by
    intro m
    induction m with
    | zero =>
        intro hm s
        cases s
        · exact hsw b.first true
        · exact Relation.EqvGen.refl _
    | succ m ih =>
        intro hm s
        have e : b.succ ⟨m, by omega⟩ = ⟨m + 1, hm⟩ := Fin.ext (b.succ_val_of_lt _ hm)
        have h1 : S.Orbit (b.pairAt S b.first true) (b.pairAt S ⟨m + 1, hm⟩
            (S.st (b.lt ⟨m + 1, hm⟩))) := by
          have := Relation.EqvGen.trans _ _ _ (ih (by omega) _)
            (Relation.EqvGen.rel _ _ (Or.inl (b.step_succ S hA ⟨m, by omega⟩)))
          rwa [e] at this
        by_cases hs' : s = S.st (b.lt ⟨m + 1, hm⟩)
        · rw [hs']; exact h1
        · rw [Bool.eq_not_iff.mpr hs']
          exact Relation.EqvGen.trans _ _ _ h1 (hsw _ _)
  exact key q.val q.isLt s

/-- The positions of a band form one orbit. -/
theorem orbit_iff {P : Pair D} (hP : P ∈ b.Pos S) (P' : Pair D) :
    S.Orbit P P' ↔ P' ∈ b.Pos S :=
  S.orbit_iff_of_closed (b.Pos S) (b.pos_step S hA) (b.pos_swap S) (b.pos_conn S hA) hP P'

end CWord

namespace MonomialData

end MonomialData

end BrickAccessibility
