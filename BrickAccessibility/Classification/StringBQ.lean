module

public import BrickAccessibility.Classification.BlockUnique
public import BrickAccessibility.Section4.Closed

/-!
# String modules as block quivers

For a string `w` and a block space `V`, the block quiver of `w` has positions
`0, …, n`, the moves of the string diagram and identity isomorphisms; for
`V = k` it is the string module, in general it is `M(w) ⊗ V`.

Along a string the signs alternate (`st_ne_en`), so each position has at most
one traversal of each sign. At position `p` the half-word in the direction of
sign `s` (`half p s`) is the maximal walk; hence the pair functors of `M(w) ⊗ V`
are counted by the positions of `w`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

/-- `omega` after unfolding word lengths. -/
local macro "womega" : tactic => `(tactic| ((try simp only [Word.len] at *) <;> omega))

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem Letter.inv_inv' {Q : FinQuiver} (l : Letter Q) : l.inv.inv = l := by
  obtain ⟨a, d⟩ := l; simp [Letter.inv]

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)

theorem Signs.st_ne_en_of_allowedPair {l l' : Letter D.Q} (h : D.AllowedPair l l')
    (hw : l.tgt = l'.src) : S.st l' ≠ S.en l := by
  obtain ⟨a, d⟩ := l; obtain ⟨b, e⟩ := l'
  cases d <;> cases e <;>
    simp only [Letter.tgt, Letter.src, Bool.false_eq_true, if_false, if_true] at hw <;>
    simp only [MonomialData.allowedPair_ff, MonomialData.allowedPair_ft,
      MonomialData.allowedPair_tf, MonomialData.allowedPair_tt] at h <;>
    simp only [Signs.st_false, Signs.st_true, Signs.en_false, Signs.en_true] <;>
    first
    | exact S.hall _ _ ⟨hw.symm, h⟩
    | exact S.hall _ _ ⟨hw, h⟩
    | exact S.hσ _ _ (Ne.symm h) hw.symm
    | exact S.hσ _ _ (Ne.symm h) hw
    | exact S.hσ _ _ h hw.symm
    | exact S.hσ _ _ h hw
    | exact S.hε _ _ (Ne.symm h) hw.symm
    | exact S.hε _ _ (Ne.symm h) hw
    | exact S.hε _ _ h hw
    | exact (S.hall _ _ ⟨hw, h⟩).symm
    | exact (S.hall _ _ ⟨hw.symm, h⟩).symm.symm
    | exact S.hε _ _ h hw
    | exact (S.hall _ _ ⟨hw, h⟩).symm
    | exact (S.hall _ _ ⟨hw.symm, h⟩).symm

end MonomialData

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

/-- Signs alternate along a string. -/
theorem st_ne_en (S : D.Signs) (hs : w.IsString D) (i : ℕ) (hi : i + 1 < w.len) :
    S.st (w.letters[i + 1]'hi) ≠ S.en (w.letters[i]'(Nat.lt_of_succ_lt hi)) := by
  have hc := List.isChain_iff_getElem.mp (w.chain_allowed hs) i hi
  refine S.st_ne_en_of_allowedPair hc ?_
  rw [w.tgt_letter i (by omega), w.src_letter (i + 1) hi]

variable (V : Type u) [AddCommGroup V] [Module k V]

/-- The block quiver of a word without forks. -/
def blockQuiver (hw : w.NoForks) : D.BlockQuiver V where
  P := Fin (w.len + 1)
  vtx := w.vtx
  next := w.next
  g _ _ := LinearEquiv.refl k V
  next_src a i j h := (w.coeffQuiver D).next_src a i j h
  next_tgt a i j h := (w.coeffQuiver D).next_tgt a i j h
  inj a i i' j h h' := w.next_injective hw h h'

theorem blockQuiver_follow (hw : w.NoForks) (i : Fin (w.len + 1)) (l : List D.Q.A) :
    (w.blockQuiver V hw).follow i l =
      ((w.coeffQuiver D).follow i l).map fun q ↦ (q.1, LinearMap.id) := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
      simp only [MonomialData.BlockQuiver.follow, MonomialData.CoeffQuiver.follow]
      have e1 : (w.blockQuiver V hw).next a i = w.next a i := rfl
      have e2 : (w.coeffQuiver D).next a i = w.next a i := rfl
      rw [e1, e2]
      cases w.next a i with
      | none => rfl
      | some j =>
          simp only [ih, Option.map_map]
          cases (w.coeffQuiver D).follow j l with
          | none => rfl
          | some q => simp [blockQuiver]; rfl

theorem blockQuiver_kills (hs : w.IsString D) : (w.blockQuiver V hs.1).KillsZeroPaths := by
  intro x l hxl i hi
  have h1 := w.blockQuiver_follow V hs.1 i l
  have h2 : (w.coeffQuiver D).follow i l = none := hs.2 x l hxl i hi
  rw [h2] at h1
  exact h1

variable {V} (hs : w.IsString D)
include hs

theorem trav_iff (p q : Fin (w.len + 1)) (l : Letter D.Q) :
    (w.blockQuiver V hs.1).Trav p l q ↔
      (∃ h : p.val < w.len, w.letters[p.val] = l ∧ q.val = p.val + 1) ∨
      (∃ h : 0 < p.val, (w.letters[p.val - 1]'(by have := p.isLt; womega)).inv = l ∧
        q.val + 1 = p.val) := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [MonomialData.BlockQuiver.Trav, Bool.false_eq_true, if_false]
    change w.next a q = some p ↔ _
    rw [w.next_eq_some_iff hs.1]
    constructor
    · rintro (⟨hq, hl, hp⟩ | ⟨hq, hl, hp⟩)
      · right
        refine ⟨by womega, ?_, by womega⟩
        have : p.val - 1 = q.val := by womega
        simp only [this, hl, Letter.inv, Bool.not_true]
      · left
        refine ⟨by have := q.isLt; womega, ?_, by womega⟩
        have : p.val = q.val - 1 := by womega
        simp only [this, hl]
    · rintro (⟨hp, hl, hq⟩ | ⟨hp, hl, hq⟩)
      · right
        refine ⟨by womega, ?_, by womega⟩
        have : q.val - 1 = p.val := by womega
        simp only [this, hl]
      · left
        have := p.isLt
        refine ⟨by womega, ?_, by womega⟩
        have e : q.val = p.val - 1 := by womega
        simp only [e]
        rw [← Letter.inv_inv' (w.letters[p.val - 1]'(by womega)), hl]
        rfl
  · simp only [MonomialData.BlockQuiver.Trav, if_true]
    change w.next a p = some q ↔ _
    rw [w.next_eq_some_iff hs.1]
    constructor
    · rintro (⟨hp, hl, hq⟩ | ⟨hp, hl, hq⟩)
      · exact Or.inl ⟨hp, hl, hq⟩
      · right
        refine ⟨hp, ?_, by womega⟩
        simp only [hl, Letter.inv, Bool.not_false]
    · rintro (⟨hp, hl, hq⟩ | ⟨hp, hl, hq⟩)
      · exact Or.inl ⟨hp, hl, hq⟩
      · right
        refine ⟨hp, ?_, by womega⟩
        rw [← Letter.inv_inv' (w.letters[p.val - 1]'(by have := p.isLt; womega)), hl]
        rfl

/-- The sign of the right half at a position. -/
def sideSign (S : D.Signs) (p : Fin (w.len + 1)) : Bool :=
  if h : p.val < w.len then S.st w.letters[p.val]
  else if h' : 0 < w.len then !S.en (w.letters[w.len - 1]'(by womega)) else true

theorem en_left_eq (S : D.Signs) (p : Fin (w.len + 1)) (hp : 0 < p.val) :
    S.en (w.letters[p.val - 1]'(by have := p.isLt; womega)) = !w.sideSign S p := by
  unfold sideSign
  by_cases h : p.val < w.len
  · rw [dif_pos h]
    have := w.st_ne_en S hs (p.val - 1) (by womega)
    have e : p.val - 1 + 1 = p.val := by womega
    simp only [e] at this
    revert this
    cases S.st w.letters[p.val] <;> cases S.en (w.letters[p.val - 1]'(by have := p.isLt; womega)) <;>
      simp
  · rw [dif_neg h, dif_pos (by have := p.isLt; womega)]
    have e : p.val - 1 = w.len - 1 := by have := p.isLt; womega
    simp only [e, Bool.not_not]

theorem signedUnique (S : D.Signs) : (w.blockQuiver V hs.1).SignedUnique S := by
  intro p l l' q q' h h' hsign
  replace h := (trav_iff (V := V) w hs p q l).mp h
  replace h' := (trav_iff (V := V) w hs p q' l').mp h'
  rcases h with ⟨hp, hl, -⟩ | ⟨hp, hl, -⟩ <;> rcases h' with ⟨hp', hl', -⟩ | ⟨hp', hl', -⟩
  · rw [← hl, ← hl']
  · exfalso
    have e1 : S.st l = w.sideSign S p := by
      rw [← hl]; unfold sideSign; rw [dif_pos hp]
    have e2 : S.st l' = !w.sideSign S p := by
      rw [← hl', MonomialData.Signs.st_inv, w.en_left_eq hs S p hp']
    rw [e1, e2] at hsign; simp at hsign
  · exfalso
    have e1 : S.st l' = w.sideSign S p := by
      rw [← hl']; unfold sideSign; rw [dif_pos hp']
    have e2 : S.st l = !w.sideSign S p := by
      rw [← hl, MonomialData.Signs.st_inv, w.en_left_eq hs S p hp]
    rw [e1, e2] at hsign; simp at hsign
  · rw [← hl, ← hl']

/-- The letters to the right of a position. -/
def right (p : Fin (w.len + 1)) : List (Letter D.Q) := w.letters.drop p.val

/-- The letters to the left of a position, read leftwards. -/
def left (p : Fin (w.len + 1)) : List (Letter D.Q) := invLetters (w.letters.take p.val)

omit hs in
theorem right_cons (p : Fin (w.len + 1)) (hp : p.val < w.len) :
    w.right p = w.letters[p.val] :: w.right ⟨p.val + 1, by womega⟩ := by
  simp only [right]
  exact List.drop_eq_getElem_cons hp

omit hs in
theorem left_cons (p : Fin (w.len + 1)) (hp : 0 < p.val) :
    w.left p = (w.letters[p.val - 1]'(by have := p.isLt; womega)).inv ::
      w.left ⟨p.val - 1, by womega⟩ := by
  simp only [left, invLetters]
  have : w.letters.take p.val = w.letters.take (p.val - 1) ++
      [w.letters[p.val - 1]'(by have := p.isLt; womega)] := by
    rw [← List.take_succ_eq_append_getElem]
    congr 1; womega
  rw [this, List.map_append, List.reverse_append]
  rfl

omit hs in
theorem right_last : w.right (Fin.last _) = [] := by simp [right]

omit hs in
theorem left_zero : w.left 0 = [] := by simp [left, invLetters]

theorem walk_right (p : Fin (w.len + 1)) :
    (w.blockQuiver V hs.1).walk (w.right p) p = some (Fin.last _) := by
  induction h : w.len - p.val generalizing p with
  | zero =>
      have hp : p = Fin.last _ := Fin.ext (by have := p.isLt; simp; womega)
      subst hp
      rw [right_last]; rfl
  | succ n ih =>
      have hp : p.val < w.len := by womega
      rw [w.right_cons p hp]
      simp only [MonomialData.BlockQuiver.walk]
      have htr : (w.blockQuiver V hs.1).Trav p w.letters[p.val] ⟨p.val + 1, by womega⟩ :=
        (trav_iff w hs p _ _).mpr (Or.inl ⟨hp, rfl, rfl⟩)
      have hex : ∃ q, (w.blockQuiver V hs.1).Trav p w.letters[p.val] q := ⟨_, htr⟩
      rw [dif_pos hex, (w.blockQuiver V hs.1).trav_unique hex.choose_spec htr]
      exact ih _ (by show w.len - (p.val + 1) = n; womega)

theorem walk_left (p : Fin (w.len + 1)) :
    (w.blockQuiver V hs.1).walk (w.left p) p = some (0 : Fin (w.len + 1)) := by
  induction h : p.val generalizing p with
  | zero =>
      have hp : p = 0 := Fin.ext h
      subst hp
      rw [left_zero]; rfl
  | succ n ih =>
      have hp : 0 < p.val := by womega
      rw [w.left_cons p hp]
      simp only [MonomialData.BlockQuiver.walk]
      have htr : (w.blockQuiver V hs.1).Trav p (w.letters[p.val - 1]'(by have := p.isLt; womega)).inv
          ⟨p.val - 1, by womega⟩ :=
        (trav_iff w hs p _ _).mpr (Or.inr ⟨hp, rfl, by simp; womega⟩)
      have hex : ∃ q, (w.blockQuiver V hs.1).Trav p
          (w.letters[p.val - 1]'(by have := p.isLt; womega)).inv q := ⟨_, htr⟩
      rw [dif_pos hex, (w.blockQuiver V hs.1).trav_unique hex.choose_spec htr]
      exact ih _ (by show p.val - 1 = n; womega)

omit hs in
theorem right_getElem (p : Fin (w.len + 1)) (i : ℕ) (hi : i < (w.right p).length) :
    (w.right p)[i] = w.letters[p.val + i]'(by simp [right] at hi; womega) := by
  simp [right]

omit hs in
theorem left_getElem (p : Fin (w.len + 1)) (i : ℕ) (hi : i < (w.left p).length) :
    (w.left p)[i] = (w.letters[p.val - 1 - i]'(by
      simp [left, invLetters] at hi; have := p.isLt; womega)).inv := by
  simp only [left, invLetters, List.getElem_reverse, List.getElem_map, List.getElem_take]
  congr 2
  simp [left, invLetters] at hi
  simp only [List.length_map, List.length_take]
  have := p.isLt
  rw [min_eq_left (by womega)]

theorem isHW_right (S : D.Signs) (p : Fin (w.len + 1)) :
    S.IsHW (w.vtx p) (w.sideSign S p) (w.right p) := by
  refine ⟨Word.isWalk_take_drop w.walk p.val, fun i hi ↦ ?_⟩
  have hi' : p.val + i < w.len := by simp [right] at hi; womega
  rw [w.right_getElem p i hi]
  cases i with
  | zero =>
      simp only [List.take_zero, MonomialData.Signs.nsign_nil, Nat.add_zero]
      unfold sideSign; rw [dif_pos (by womega)]
  | succ j =>
      rw [List.take_succ_eq_append_getElem (by omega), MonomialData.Signs.nsign_append_singleton,
        w.right_getElem p j (by omega)]
      have := w.st_ne_en S hs (p.val + j) (by womega)
      exact Bool.eq_not_iff.mpr (by simpa [Nat.add_assoc] using this)

theorem isHW_left (S : D.Signs) (p : Fin (w.len + 1)) :
    S.IsHW (w.vtx p) (!w.sideSign S p) (w.left p) := by
  have hw := w.walk
  rw [← List.take_append_drop p.val w.letters, Statement.FinQuiver.isWalk_append] at hw
  refine ⟨(Statement.FinQuiver.isWalk_inv _ _ hw.1).1, fun i hi ↦ ?_⟩
  have hip : i < p.val := by simp [left, invLetters] at hi; have := p.isLt; womega
  rw [w.left_getElem p i hi, MonomialData.Signs.st_inv]
  cases i with
  | zero =>
      simp only [List.take_zero, MonomialData.Signs.nsign_nil, Nat.sub_zero]
      exact w.en_left_eq hs S p (by omega)
  | succ j =>
      rw [List.take_succ_eq_append_getElem (by omega), MonomialData.Signs.nsign_append_singleton,
        w.left_getElem p j (by omega), MonomialData.Signs.en_inv]
      have := w.st_ne_en S hs (p.val - 1 - (j + 1)) (by have := p.isLt; womega)
      have e : p.val - 1 - (j + 1) + 1 = p.val - 1 - j := by omega
      simp only [e] at this
      exact Bool.eq_not_iff.mpr (Ne.symm this)

/-- The half of `w` at `p` in the direction of sign `s`. -/
def half (S : D.Signs) (p : Fin (w.len + 1)) (s : Bool) : List (Letter D.Q) :=
  if s = w.sideSign S p then w.right p else w.left p

theorem isHW_half (S : D.Signs) (p : Fin (w.len + 1)) (s : Bool) :
    S.IsHW (w.vtx p) s (w.half S p s) := by
  unfold half
  split_ifs with h
  · subst h; exact w.isHW_right hs S p
  · have : s = !w.sideSign S p := Bool.eq_not_iff.mpr h
    subst this; exact w.isHW_left hs S p

theorem nsign_right (S : D.Signs) (p : Fin (w.len + 1)) :
    S.nsign (w.sideSign S p) (w.right p) = w.sideSign S (Fin.last _) := by
  by_cases hp : p.val < w.len
  · have hne : w.right p ≠ [] := by
      intro h; have := congrArg List.length h; simp [right] at this; womega
    simp only [MonomialData.Signs.nsign, List.getLast?_eq_some_getLast hne]
    have hlast : (w.right p).getLast hne = w.letters[w.len - 1]'(by womega) := by
      rw [List.getLast_eq_getElem, w.right_getElem]
      congr 1; simp [right]; womega
    rw [hlast]
    have h0 : 0 < w.len := by omega
    unfold sideSign
    rw [dif_neg (by simp), dif_pos h0]
  · have : p = Fin.last _ := Fin.ext (by have := p.isLt; simp; womega)
    subst this
    rw [right_last]; rfl

theorem nsign_left (S : D.Signs) (p : Fin (w.len + 1)) :
    S.nsign (!w.sideSign S p) (w.left p) = !w.sideSign S 0 := by
  by_cases hp : 0 < p.val
  · have hne : w.left p ≠ [] := by rw [w.left_cons p hp]; simp
    have hlen : 0 < w.letters.length := by
      have := p.isLt; simp only [Word.len] at this; omega
    simp only [MonomialData.Signs.nsign, List.getLast?_eq_some_getLast hne]
    have hlast : (w.left p).getLast hne = (w.letters[0]'hlen).inv := by
      rw [List.getLast_eq_getElem, w.left_getElem]
      congr 2; simp [left, invLetters]; have := p.isLt; womega
    rw [hlast, MonomialData.Signs.en_inv]
    unfold sideSign
    rw [dif_pos (show (0 : Fin (w.len + 1)).val < w.len from hlen)]
    rfl
  · have : p = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst this
    rw [left_zero]; rfl

theorem not_travSign_last (S : D.Signs) :
    ¬ (w.blockQuiver V hs.1).TravSign S (Fin.last _) (w.sideSign S (Fin.last _)) := by
  rintro ⟨l, q, hsl, htr⟩
  rcases (trav_iff w hs _ q l).mp htr with ⟨hp, -, -⟩ | ⟨hp, hl, -⟩
  · simp at hp
  · rw [← hl, MonomialData.Signs.st_inv, w.en_left_eq hs S _ hp] at hsl
    simp at hsl

theorem not_travSign_zero (S : D.Signs) :
    ¬ (w.blockQuiver V hs.1).TravSign S (0 : Fin (w.len + 1)) (!w.sideSign S 0) := by
  rintro ⟨l, q, hsl, htr⟩
  rcases (trav_iff w hs _ q l).mp htr with ⟨hp, hl, -⟩ | ⟨hp, -, -⟩
  · rw [← hl] at hsl
    unfold sideSign at hsl
    rw [dif_pos hp] at hsl
    simp at hsl
  · simp at hp

theorem PM_half (S : D.Signs) (p : Fin (w.len + 1)) (s : Bool) :
    (w.blockQuiver V hs.1).PM S (w.vtx p) s (.fin (w.half S p s)) p := by
  unfold MonomialData.BlockQuiver.PM
  refine ((w.blockQuiver V hs.1).mem_plus_not_minus_fin S (w.isHW_half hs S p s) (p := p)
    rfl).mpr ?_
  unfold half
  split_ifs with h
  · subst h
    refine ⟨Fin.last _, w.walk_right hs p, ?_⟩
    rw [w.nsign_right hs S p]
    exact w.not_travSign_last hs S
  · have : s = !w.sideSign S p := Bool.eq_not_iff.mpr h
    subst this
    refine ⟨(0 : Fin (w.len + 1)), w.walk_left hs p, ?_⟩
    rw [w.nsign_left hs S p]
    exact w.not_travSign_zero hs S

/-- The maximal walks of a string module are its halves. -/
theorem PM_iff (S : D.Signs) (p : Fin (w.len + 1)) {s : Bool} {h : HWord D.Q}
    (hv : S.Valid (w.vtx p) s h) :
    (w.blockQuiver V hs.1).PM S (w.vtx p) s h p ↔ h = .fin (w.half S p s) := by
  constructor
  · intro hPM
    exact (w.blockQuiver V hs.1).PM_unique S (w.signedUnique hs S) hv (w.isHW_half hs S p s) rfl
      hPM (w.PM_half hs S p s)
  · rintro rfl; exact w.PM_half hs S p s

/-- **Pair functors of `M(w) ⊗ V`**: counted by the positions of `w`. -/
theorem gr_eq [FiniteDimensional k V] (S : D.Signs) {v : D.Q.V} {s : Bool} {h h' : HWord D.Q}
    (hv : S.Valid v s h) (hv' : S.Valid v (!s) h') :
    finrank k (S.pnum ((w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs)) v s h h') -
      finrank k (S.pden ((w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs)) v s h h') =
      Nat.card {p : Fin (w.len + 1) // w.vtx p = v ∧
        h = .fin (w.half S p s) ∧ h' = .fin (w.half S p (!s))} * finrank k V := by
  classical
  rw [(w.blockQuiver V hs.1).gr_eq (w.blockQuiver_kills V hs) S hv hv', ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p ↦ ?_)
  constructor
  · rintro ⟨h1, h2⟩
    have hp := (w.blockQuiver V hs.1).vtx_of_PM S hv h1
    change w.vtx p = v at hp
    subst hp
    exact ⟨rfl, (w.PM_iff hs S p hv).mp h1, (w.PM_iff hs S p hv').mp h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨w.PM_half hs S p s, w.PM_half hs S p (!s)⟩

end Word

end BrickAccessibility
