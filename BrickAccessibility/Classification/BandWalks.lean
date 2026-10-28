module

public import BrickAccessibility.Classification.BandBQ

/-!
# Maximal walks in band block quivers

In a band block quiver each position has one traversal to the right (along
`l_p`) and one to the left (along `l_{p-1}⁻¹`), with opposite signs. The maximal
walks from `p` are the two periodic half-words `rightW p`, `leftW p`, so the pair
functors of a band module are counted by its positions (`band_gr_eq`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : D.Signs)

/-- A stream of letters with a walk and sign alternation gives valid prefixes. -/
theorem Signs.isHW_ofFn {v : D.Q.V} {s : Bool} (f : ℕ → Letter D.Q) (h0 : (f 0).src = v)
    (hw : ∀ i, (f (i + 1)).src = (f i).tgt) (hs0 : S.st (f 0) = s)
    (halt : ∀ i, S.st (f (i + 1)) ≠ S.en (f i)) :
    ∀ m, S.IsHW v s (List.ofFn fun i : Fin m ↦ f i) := by
  intro m
  induction m with
  | zero => exact S.isHW_nil v s
  | succ m ih =>
      rw [List.ofFn_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last]
      refine S.isHW_append_singleton ih ?_ ?_
      · cases m with
        | zero => simpa [Statement.FinQuiver.wend] using h0
        | succ m =>
            rw [hw m]
            rw [List.ofFn_succ_last, Statement.FinQuiver.wend_append]
            simp only [Fin.val_castSucc, Fin.val_last]
            rfl
      · cases m with
        | zero => simpa using hs0
        | succ m =>
            rw [List.ofFn_succ_last, Signs.nsign_append_singleton]
            simp only [Fin.val_last]
            have := halt m
            revert this
            cases S.st (f (m + 1)) <;> cases S.en (f m) <;> simp

namespace BlockQuiver

variable {V : Type u} [AddCommGroup V] [Module k V] (C : D.BlockQuiver V)

theorem walk_ofFn_of_trav (f : ℕ → Letter D.Q) (pos : ℕ → C.P)
    (htr : ∀ i, C.Trav (pos i) (f i) (pos (i + 1))) :
    ∀ m, C.walk (List.ofFn fun i : Fin m ↦ f i) (pos 0) = some (pos m) := by
  intro m
  induction m generalizing f pos with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ]
      show C.walk (f 0 :: List.ofFn fun i : Fin m ↦ f (i + 1)) (pos 0) = some (pos (m + 1))
      have hex : ∃ q, C.Trav (pos 0) (f 0) q := ⟨_, htr 0⟩
      unfold walk
      rw [dif_pos hex, C.trav_unique hex.choose_spec (htr 0)]
      exact ih (fun i ↦ f (i + 1)) (fun i ↦ pos (i + 1)) fun i ↦ htr (i + 1)

end BlockQuiver

end MonomialData

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
variable {V : Type u} [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V)

theorem eq_succ_iff (p q : Fin b.n) : p = b.succ q ↔ q = b.pred p := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

include hA

theorem next_eq_some_iff (a : D.Q.A) (i j : Fin b.n) :
    b.next a i = some j ↔
      (b.lt i = (a, true) ∧ j = b.succ i) ∨ (b.lt (b.pred i) = (a, false) ∧ j = b.pred i) := by
  unfold next
  split_ifs with h1 h2
  · simp only [Option.some.injEq, h1, true_and]
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h | ⟨h3, -⟩)
      · exact h.symm
      · exact absurd (b.not_fork S hA (b.pred i) a false h3 (by rw [succ_pred, h1]; rfl)) id
  · simp only [Option.some.injEq, h1, h2, false_and, true_and, false_or]
    exact eq_comm
  · simp [h1, h2]

theorem trav_iff (p q : Fin b.n) (l : Letter D.Q) :
    (b.blockQuiver S hA V φ).Trav p l q ↔
      (l = b.lt p ∧ q = b.succ p) ∨ (l = (b.lt (b.pred p)).inv ∧ q = b.pred p) := by
  obtain ⟨a, d⟩ := l
  have hinv : ∀ (l : Letter D.Q) (e : Bool), (a, e) = l.inv ↔ l = (a, !e) := by
    intro l e
    obtain ⟨c, f⟩ := l
    simp only [Letter.inv, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp
  cases d
  · simp only [MonomialData.BlockQuiver.Trav, Bool.false_eq_true, if_false]
    change b.next a q = some p ↔ _
    rw [b.next_eq_some_iff S hA, b.eq_succ_iff p q, hinv]
    simp only [Bool.not_false]
    constructor
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
      · exact Or.inr ⟨h1, rfl⟩
      · exact Or.inl ⟨h1.symm, by simp⟩
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
      · exact Or.inr ⟨by simp [← h1], by simp⟩
      · exact Or.inl ⟨h1, rfl⟩
  · simp only [MonomialData.BlockQuiver.Trav, if_true]
    change b.next a p = some q ↔ _
    rw [b.next_eq_some_iff S hA, hinv]
    simp only [Bool.not_true]
    constructor
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
      · exact Or.inl ⟨h1.symm, rfl⟩
      · exact Or.inr ⟨h1, rfl⟩
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
      · exact Or.inl ⟨h1.symm, rfl⟩
      · exact Or.inr ⟨h1, rfl⟩

theorem en_pred (p : Fin b.n) : S.en (b.lt (b.pred p)) = !S.st (b.lt p) := by
  have := hA (b.pred p)
  rw [succ_pred] at this
  revert this
  cases S.st (b.lt p) <;> cases S.en (b.lt (b.pred p)) <;> simp

theorem signedUnique : (b.blockQuiver S hA V φ).SignedUnique S := by
  intro p l l' q q' h h' hs
  rcases (b.trav_iff S hA φ p q l).mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    rcases (b.trav_iff S hA φ p q' l').mp h' with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rfl
  · exfalso
    rw [MonomialData.Signs.st_inv] at hs
    have e := b.en_pred S hA p
    revert hs e
    cases S.st (b.lt p) <;> cases S.en (b.lt (b.pred p)) <;> simp
  · exfalso
    rw [MonomialData.Signs.st_inv] at hs
    have e := b.en_pred S hA p
    revert hs e
    cases S.st (b.lt p) <;> cases S.en (b.lt (b.pred p)) <;> simp
  · rfl

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
variable {V : Type u} [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V)

/-- The rightward periodic half-word at `p`. -/
def rightW (p : Fin b.n) : ℕ → Letter D.Q := fun i ↦ b.lt (b.succ^[i] p)

/-- The leftward periodic half-word at `p`. -/
def leftW (p : Fin b.n) : ℕ → Letter D.Q := fun i ↦ (b.lt (b.pred^[i + 1] p)).inv

/-- The half-word of sign `s` at `p`. -/
def bhalf (p : Fin b.n) (s : Bool) : HWord D.Q :=
  if s = S.st (b.lt p) then .inf (b.rightW p) else .inf (b.leftW p)

include hA

theorem valid_rightW (p : Fin b.n) : S.Valid (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p)) := by
  refine S.isHW_ofFn (b.rightW p) rfl (fun i ↦ ?_) rfl (fun i ↦ ?_)
  · simp only [rightW, Function.iterate_succ_apply']
    rw [b.lt_tgt]; rfl
  · simp only [rightW, Function.iterate_succ_apply']
    exact hA _

theorem valid_leftW (p : Fin b.n) :
    S.Valid (b.vtx p) (!S.st (b.lt p)) (.inf (b.leftW p)) := by
  refine S.isHW_ofFn (b.leftW p) ?_ (fun i ↦ ?_) ?_ (fun i ↦ ?_)
  · show (b.lt (b.pred p)).inv.src = b.vtx p
    rw [Letter.src_inv, b.lt_tgt, succ_pred]
  · simp only [leftW, Letter.src_inv, Letter.tgt_inv]
    rw [b.lt_tgt, Function.iterate_succ_apply' b.pred (i + 1), succ_pred]; rfl
  · show S.st (b.lt (b.pred p)).inv = !S.st (b.lt p)
    rw [MonomialData.Signs.st_inv]
    exact b.en_pred S hA p
  · simp only [leftW, MonomialData.Signs.st_inv, MonomialData.Signs.en_inv]
    rw [Function.iterate_succ_apply' b.pred (i + 1), b.en_pred S hA]
    cases S.st (b.lt (b.pred^[i + 1] p)) <;> simp

theorem PM_rightW (p : Fin b.n) :
    (b.blockQuiver S hA V φ).PM S (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p)) p := by
  unfold MonomialData.BlockQuiver.PM
  refine ((b.blockQuiver S hA V φ).mem_plus_not_minus_inf S (b.valid_rightW S hA p) (p := p)
    rfl).mpr fun m ↦ ?_
  have := (b.blockQuiver S hA V φ).walk_ofFn_of_trav (b.rightW p) (fun i ↦ b.succ^[i] p)
    (fun i ↦ (b.trav_iff S hA φ _ _ _).mpr (Or.inl ⟨rfl, by
      simp only [Function.iterate_succ_apply']⟩)) m
  exact Option.ne_none_iff_exists'.mpr ⟨_, this⟩

theorem PM_leftW (p : Fin b.n) :
    (b.blockQuiver S hA V φ).PM S (b.vtx p) (!S.st (b.lt p)) (.inf (b.leftW p)) p := by
  unfold MonomialData.BlockQuiver.PM
  refine ((b.blockQuiver S hA V φ).mem_plus_not_minus_inf S (b.valid_leftW S hA p) (p := p)
    rfl).mpr fun m ↦ ?_
  have := (b.blockQuiver S hA V φ).walk_ofFn_of_trav (b.leftW p) (fun i ↦ b.pred^[i] p)
    (fun i ↦ (b.trav_iff S hA φ _ _ _).mpr (Or.inr ⟨by
      simp only [leftW, Function.iterate_succ_apply'], by
      simp only [Function.iterate_succ_apply']⟩)) m
  exact Option.ne_none_iff_exists'.mpr ⟨_, this⟩

theorem valid_bhalf (p : Fin b.n) (s : Bool) : S.Valid (b.vtx p) s (b.bhalf S p s) := by
  unfold bhalf
  split_ifs with h
  · subst h; exact b.valid_rightW S hA p
  · have : s = !S.st (b.lt p) := Bool.eq_not_iff.mpr h
    subst this; exact b.valid_leftW S hA p

theorem PM_bhalf (p : Fin b.n) (s : Bool) :
    (b.blockQuiver S hA V φ).PM S (b.vtx p) s (b.bhalf S p s) p := by
  unfold bhalf
  split_ifs with h
  · subst h; exact b.PM_rightW S hA φ p
  · have : s = !S.st (b.lt p) := Bool.eq_not_iff.mpr h
    subst this; exact b.PM_leftW S hA φ p

theorem PM_iff (p : Fin b.n) {s : Bool} {h : HWord D.Q} (hv : S.Valid (b.vtx p) s h) :
    (b.blockQuiver S hA V φ).PM S (b.vtx p) s h p ↔ h = b.bhalf S p s := by
  constructor
  · intro hPM
    exact (b.blockQuiver S hA V φ).PM_unique S (b.signedUnique S hA φ) hv
      (b.valid_bhalf S hA p s) rfl hPM (b.PM_bhalf S hA φ p s)
  · rintro rfl; exact b.PM_bhalf S hA φ p s

/-- **Pair functors of band modules**: counted by positions. -/
theorem band_gr_eq (hK : b.KillsZero) [FiniteDimensional k V] {v : D.Q.V} {s : Bool}
    {h h' : HWord D.Q} (hv : S.Valid v s h) (hv' : S.Valid v (!s) h') :
    finrank k (S.pnum ((b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ)) v s h h') -
      finrank k (S.pden ((b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ)) v s h h') =
      Nat.card {p : Fin b.n // b.vtx p = v ∧ h = b.bhalf S p s ∧ h' = b.bhalf S p (!s)} *
        finrank k V := by
  classical
  rw [(b.blockQuiver S hA V φ).gr_eq (b.blockQuiver_kills S hA hK V φ) S hv hv',
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p ↦ ?_)
  constructor
  · rintro ⟨h1, h2⟩
    have hp := (b.blockQuiver S hA V φ).vtx_of_PM S hv h1
    change b.vtx p = v at hp
    subst hp
    exact ⟨rfl, (b.PM_iff S hA φ p hv).mp h1, (b.PM_iff S hA φ p hv').mp h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨b.PM_bhalf S hA φ p s, b.PM_bhalf S hA φ p (!s)⟩

end CWord

end BrickAccessibility
