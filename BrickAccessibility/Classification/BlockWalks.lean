module

public import BrickAccessibility.Classification.BlockSets

/-!
# Walks in block quivers

A letter `l` traverses from position `p` to `q` if `l = a` and `a` moves `p` to
`q`, or `l = a⁻¹` and `a` moves `q` to `p`. Following a list of letters from `p`
either succeeds (`walk`), or stops at a letter with no traversal: it *dies* at a
direct letter and *fails* at an inverse letter. Transports of position sets are
described by walks (`ptrs_iff`), and a position lies in `h⁺` but not in `h⁻`
exactly when the walk along `h` succeeds and cannot be continued
(`mem_plus_not_minus_fin`, `mem_plus_not_minus_inf`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
variable (C : D.BlockQuiver V)

namespace BlockQuiver

/-- A traversal of the letter `l` from `p` to `q`. -/
def Trav (p : C.P) (l : Letter D.Q) (q : C.P) : Prop :=
  if l.2 then C.next l.1 p = some q else C.next l.1 q = some p

theorem trav_tgt {p q : C.P} {l : Letter D.Q} (h : C.Trav p l q) :
    C.vtx p = l.src ∧ C.vtx q = l.tgt := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [Trav, Bool.false_eq_true, if_false] at h
    exact ⟨C.next_tgt a q p h, C.next_src a q p h⟩
  · simp only [Trav, if_true] at h
    exact ⟨C.next_src a p q h, C.next_tgt a p q h⟩

theorem trav_unique {p q q' : C.P} {l : Letter D.Q} (h : C.Trav p l q) (h' : C.Trav p l q') :
    q = q' := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [Trav, Bool.false_eq_true, if_false] at h h'
    exact C.inj a q q' p h h'
  · simp only [Trav, if_true] at h h'
    rw [h] at h'; exact Option.some.inj h'

open Classical in
/-- The end of the walk along a list of letters, if every letter traverses. -/
def walk : List (Letter D.Q) → C.P → Option C.P
  | [], p => some p
  | l :: L, p => if h : ∃ q, C.Trav p l q then walk L h.choose else none

open Classical in
/-- The walk along a list of letters stops at a direct letter. -/
def Dies : List (Letter D.Q) → C.P → Prop
  | [], _ => False
  | l :: L, p => if h : ∃ q, C.Trav p l q then Dies L h.choose else l.2 = true

theorem ptr_iff (l : Letter D.Q) (J : C.P → Prop) (p : C.P) (hp : C.vtx p = l.src) :
    C.ptr l J p ↔ (∃ q, C.Trav p l q ∧ J q) ∨ (l.2 = true ∧ ¬ ∃ q, C.Trav p l q) := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [ptr, Trav, Bool.false_eq_true, if_false, false_and, or_false]
    constructor
    · rintro ⟨i, hi, hn⟩; exact ⟨i, hn, hi⟩
    · rintro ⟨i, hn, hi⟩; exact ⟨i, hi, hn⟩
  · simp only [ptr, Trav, if_true, true_and]
    simp only [Letter.src, if_true] at hp
    constructor
    · rintro ⟨-, h⟩
      cases hq : C.next a p with
      | none => exact Or.inr (by simp)
      | some q => exact Or.inl ⟨q, rfl, h q hq⟩
    · rintro (⟨q, hq, hJ⟩ | hn)
      · refine ⟨hp, fun j hj ↦ ?_⟩
        rw [hq] at hj; cases hj; exact hJ
      · refine ⟨hp, fun j hj ↦ absurd ⟨j, hj⟩ hn⟩

theorem ptrs_iff (L : List (Letter D.Q)) (J : C.P → Prop) (p : C.P)
    (hw : D.Q.IsWalk (C.vtx p) L) :
    C.ptrs L J p ↔ (∃ e, C.walk L p = some e ∧ J e) ∨ C.Dies L p := by
  induction L generalizing p with
  | nil => simp [ptrs, walk, Dies]
  | cons l L ih =>
      obtain ⟨hl, hw'⟩ := hw
      simp only [ptrs]
      rw [C.ptr_iff l _ p hl.symm]
      by_cases h : ∃ q, C.Trav p l q
      · have hq := h.choose_spec
        have hvq := (C.trav_tgt hq).2
        simp only [walk, Dies, dif_pos h]
        rw [← ih h.choose (by rw [hvq]; exact hw')]
        constructor
        · rintro (⟨q, hq', hJ⟩ | ⟨-, hn⟩)
          · rwa [C.trav_unique hq hq']
          · exact absurd h hn
        · intro h'; exact Or.inl ⟨_, hq, h'⟩
      · simp only [walk, Dies, dif_neg h]
        constructor
        · rintro (⟨q, hq, -⟩ | ⟨hd, -⟩)
          · exact absurd ⟨q, hq⟩ h
          · exact Or.inr hd
        · rintro (⟨e, he, -⟩ | hd)
          · cases he
          · exact Or.inr ⟨hd, h⟩

theorem walk_vtx (L : List (Letter D.Q)) (p e : C.P) (h : C.walk L p = some e) :
    C.vtx e = D.Q.wend (C.vtx p) L := by
  induction L generalizing p with
  | nil => simp only [walk, Option.some.injEq] at h; rw [h]; rfl
  | cons l L ih =>
      simp only [walk] at h
      split_ifs at h with hq
      have := ih _ h
      rw [this, (C.trav_tgt hq.choose_spec).2]
      rfl

theorem not_dies_of_walk (L : List (Letter D.Q)) (p e : C.P) (h : C.walk L p = some e) :
    ¬ C.Dies L p := by
  induction L generalizing p with
  | nil => simp [Dies]
  | cons l L ih =>
      simp only [walk] at h
      split_ifs at h with hq
      simp only [Dies, dif_pos hq]
      exact ih _ h

variable (S : Signs D)

/-- A traversal from `e` with start sign `n`. -/
def TravSign (e : C.P) (n : Bool) : Prop := ∃ l q, S.st l = n ∧ C.Trav e l q

theorem Kset_iff (e : C.P) (n : Bool) :
    C.Kset S (C.vtx e) n e ↔ ¬ ∃ b q, S.σ b = n ∧ C.Trav e (b, true) q := by
  simp only [Kset, true_and, Trav, if_true, not_exists, not_and]
  constructor
  · intro h b q hb hq
    rw [h b ⟨(C.next_src b e q hq).symm, hb⟩] at hq; cases hq
  · intro h b ⟨_, hb⟩
    cases hq : C.next b e with
    | none => rfl
    | some q => exact absurd hq (h b q hb)

theorem Iset_iff (e : C.P) (n : Bool) :
    C.Iset S (C.vtx e) n e ↔ ∃ d q, S.ε d = n ∧ C.Trav e (d, false) q := by
  simp only [Iset, Trav, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨d, i, ⟨-, hd⟩, hi⟩; exact ⟨d, i, hd, hi⟩
  · rintro ⟨d, i, hd, hi⟩; exact ⟨d, i, ⟨(C.next_tgt d i e hi).symm, hd⟩, hi⟩

theorem Kset_not_Iset_iff (e : C.P) (n : Bool) :
    (C.Kset S (C.vtx e) n e ∧ ¬ C.Iset S (C.vtx e) n e) ↔ ¬ C.TravSign S e n := by
  rw [Kset_iff, Iset_iff, TravSign]
  constructor
  · rintro ⟨h1, h2⟩ ⟨⟨a, d⟩, q, hs, hq⟩
    cases d
    · exact h2 ⟨a, q, hs, hq⟩
    · exact h1 ⟨a, q, hs, hq⟩
  · intro h
    exact ⟨fun ⟨b, q, hb, hq⟩ ↦ h ⟨(b, true), q, hb, hq⟩,
      fun ⟨d, q, hd, hq⟩ ↦ h ⟨(d, false), q, hd, hq⟩⟩

/-- **Finite half-words**: `p ∈ h⁺ \ h⁻` iff the walk along `h` succeeds and stops. -/
theorem mem_plus_not_minus_fin {v : D.Q.V} {s : Bool} {L : List (Letter D.Q)}
    (hL : S.IsHW v s L) {p : C.P} (hp : C.vtx p = v) :
    (C.plusSet S v s (.fin L) p ∧ ¬ C.minusSet S v s (.fin L) p) ↔
      ∃ e, C.walk L p = some e ∧ ¬ C.TravSign S e (S.nsign s L) := by
  have hw : D.Q.IsWalk (C.vtx p) L := hp ▸ hL.1
  simp only [plusSet, minusSet]
  rw [C.ptrs_iff L _ p hw, C.ptrs_iff L _ p hw]
  constructor
  · rintro ⟨⟨e, he, hK⟩ | hd, hn⟩
    · refine ⟨e, he, ?_⟩
      have hve := C.walk_vtx L p e he
      rw [hp] at hve
      rw [← Kset_not_Iset_iff]
      rw [hve]
      exact ⟨hK, fun hI ↦ hn (Or.inl ⟨e, he, hI⟩)⟩
    · exact absurd (Or.inr hd) hn
  · rintro ⟨e, he, hT⟩
    have hve := C.walk_vtx L p e he
    rw [hp] at hve
    rw [← Kset_not_Iset_iff, hve] at hT
    refine ⟨Or.inl ⟨e, he, hT.1⟩, ?_⟩
    rintro (⟨e', he', hI⟩ | hd)
    · rw [he] at he'; cases he'; exact hT.2 hI
    · exact C.not_dies_of_walk L p e he hd

/-- **Infinite half-words**: `p ∈ h⁺ \ h⁻` iff the walk along `h` never stops. -/
theorem mem_plus_not_minus_inf {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q}
    (hf : S.Valid v s (.inf f)) {p : C.P} (hp : C.vtx p = v) :
    (C.plusSet S v s (.inf f) p ∧ ¬ C.minusSet S v s (.inf f) p) ↔
      ∀ n, C.walk (List.ofFn fun i : Fin n ↦ f i) p ≠ none := by
  have hw : ∀ n, D.Q.IsWalk (C.vtx p) (List.ofFn fun i : Fin n ↦ f i) := fun n ↦ hp ▸ (hf n).1
  simp only [plusSet, minusSet, not_exists]
  simp_rw [C.ptrs_iff _ _ p (hw _)]
  simp only [false_and, exists_false, false_or, and_false]
  constructor
  · rintro ⟨h1, h2⟩ n hn
    rcases h1 n with ⟨e, he, -⟩ | hd
    · rw [hn] at he; cases he
    · exact h2 n hd
  · intro h
    refine ⟨fun n ↦ ?_, fun n hd ↦ ?_⟩
    · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (h n)
      exact Or.inl ⟨e, he, by rw [C.walk_vtx _ p e he, hp]⟩
    · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (h n)
      exact C.not_dies_of_walk _ p e he hd

end BlockQuiver

end MonomialData

end BrickAccessibility
