module

public import BrickAccessibility.Classification.StringMaps

/-!
# Shifts along a string

For a string `w` and a finite-dimensional module `M`, the pair functors at
adjacent positions of `w` are isomorphic through the arrow of the letter between
them (`fiso_succ_true`, `fiso_succ_false`). A map `V → num_p` inducing an
isomorphism onto the pair functor at one position transfers to all positions
along a compatible family (`IsoOnto`).
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

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hs : w.IsString D) (S : D.Signs)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

include hs in
theorem sideSign_succ (q : ℕ) (hq : q < w.len) :
    w.sideSign S ⟨q + 1, by omega⟩ = !S.en w.letters[q] := by
  have := w.en_left_eq hs S ⟨q + 1, by omega⟩ (by simp)
  simp only [Nat.add_sub_cancel] at this
  rw [this]; simp

theorem sideSign_of_lt (q : ℕ) (hq : q < w.len) :
    w.sideSign S ⟨q, by omega⟩ = S.st w.letters[q] := by
  unfold sideSign; rw [dif_pos hq]

variable [FiniteDimensional k M]

include hs in
/-- The shift across a direct letter of `w`. -/
theorem fiso_succ_true (q : ℕ) (hq : q < w.len) (a : D.Q.A) (ha : w.letters[q] = (a, true)) :
    FIso (MonomialData.actL (D.α a))
      (w.num S M ⟨q, by omega⟩) (w.den S M ⟨q, by omega⟩)
      (w.num S M ⟨q + 1, by omega⟩) (w.den S M ⟨q + 1, by omega⟩) := by
  have hsrc : D.Q.src a = w.vtx ⟨q, by omega⟩ := by
    have := w.src_letter q hq; rw [ha] at this; simpa [Letter.src] using this
  have htgt : D.Q.tgt a = w.vtx ⟨q + 1, by omega⟩ := by
    have := w.tgt_letter q hq; rw [ha] at this; simpa [Letter.tgt] using this
  have hσ : S.σ a = w.sideSign S ⟨q, by omega⟩ := by
    rw [w.sideSign_of_lt S q hq, ha]; rfl
  have hε : (!S.ε a) = w.sideSign S ⟨q + 1, by omega⟩ := by
    rw [w.sideSign_succ hs S q hq, ha]; rfl
  have hX : S.Valid (D.Q.tgt a) (!S.ε a) (.fin (w.right ⟨q + 1, by omega⟩)) := by
    rw [htgt, hε]; exact w.isHW_right hs S _
  have hY : S.Valid (D.Q.src a) (!S.σ a) (.fin (w.left ⟨q, by omega⟩)) := by
    rw [hsrc, hσ]; exact w.isHW_left hs S _
  have h := S.shift M hX hY
  have e1 : (HWord.fin (w.right ⟨q + 1, by omega⟩)).cons (a, true) =
      .fin (w.right ⟨q, by omega⟩) := by
    simp only [HWord.cons]; rw [w.right_cons ⟨q, by omega⟩ hq, ha]
  have e2 : (HWord.fin (w.left ⟨q, by omega⟩)).cons (a, false) =
      .fin (w.left ⟨q + 1, by omega⟩) := by
    simp only [HWord.cons]
    rw [w.left_cons ⟨q + 1, by omega⟩ (by simp)]
    simp [ha, Letter.inv]
  rw [e1, e2, hsrc, hσ, htgt, hε] at h
  exact h

include hs in
/-- The shift across an inverse letter of `w`. -/
theorem fiso_succ_false (q : ℕ) (hq : q < w.len) (a : D.Q.A) (ha : w.letters[q] = (a, false)) :
    FIso (MonomialData.actL (D.α a))
      (w.num S M ⟨q + 1, by omega⟩) (w.den S M ⟨q + 1, by omega⟩)
      (w.num S M ⟨q, by omega⟩) (w.den S M ⟨q, by omega⟩) := by
  have htgt : D.Q.tgt a = w.vtx ⟨q, by omega⟩ := by
    have := w.src_letter q hq; rw [ha] at this; simpa [Letter.src] using this
  have hsrc : D.Q.src a = w.vtx ⟨q + 1, by omega⟩ := by
    have := w.tgt_letter q hq; rw [ha] at this; simpa [Letter.tgt] using this
  have hε : S.ε a = w.sideSign S ⟨q, by omega⟩ := by
    rw [w.sideSign_of_lt S q hq, ha]; rfl
  have hσ : (!S.σ a) = w.sideSign S ⟨q + 1, by omega⟩ := by
    rw [w.sideSign_succ hs S q hq, ha]; rfl
  have hX : S.Valid (D.Q.tgt a) (!S.ε a) (.fin (w.left ⟨q, by omega⟩)) := by
    rw [htgt, hε]; exact w.isHW_left hs S _
  have hY : S.Valid (D.Q.src a) (!S.σ a) (.fin (w.right ⟨q + 1, by omega⟩)) := by
    rw [hsrc, hσ]; exact w.isHW_right hs S _
  have h := S.shift M hX hY
  have e1 : (HWord.fin (w.left ⟨q, by omega⟩)).cons (a, true) =
      .fin (w.left ⟨q + 1, by omega⟩) := by
    simp only [HWord.cons]
    rw [w.left_cons ⟨q + 1, by omega⟩ (by simp)]
    simp [ha, Letter.inv]
  have e2 : (HWord.fin (w.right ⟨q + 1, by omega⟩)).cons (a, false) =
      .fin (w.right ⟨q, by omega⟩) := by
    simp only [HWord.cons]; rw [w.right_cons ⟨q, by omega⟩ hq, ha]
  rw [e1, e2] at h
  have hσ' : S.σ a = !w.sideSign S ⟨q + 1, by omega⟩ := by rw [← hσ]; simp
  have hε' : (!S.ε a) = !w.sideSign S ⟨q, by omega⟩ := by rw [hε]
  rw [hsrc, hσ', htgt, hε', S.pnum_swap, S.pden_swap, S.pnum_swap, S.pden_swap] at h
  exact h

variable {M} {V : Type u} [AddCommGroup V] [Module k V]

/-- The map from the block at position `q`. -/
def blockMap (Θ : (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs) →ₗ[B] M)
    (q : Fin (w.len + 1)) : V →ₗ[k] M :=
  (Θ.restrictScalars k).comp (((w.blockQuiver V hs.1).ofFunL (w.blockQuiver_kills V hs)).comp
    (LinearMap.single k (fun _ : (w.blockQuiver V hs.1).P ↦ V) q))

theorem blockMap_apply (Θ : (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs) →ₗ[B] M)
    (q : Fin (w.len + 1)) (y : V) :
    w.blockMap hs Θ q y = Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) := rfl

include hs in
theorem iso_succ_iff (Θ : (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs) →ₗ[B] M)
    (hmem : ∀ q y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) ∈ w.num S M q)
    (q : ℕ) (hq : q < w.len) :
    IsoOnto (w.blockMap hs Θ ⟨q, by omega⟩) (w.num S M ⟨q, by omega⟩) (w.den S M ⟨q, by omega⟩) ↔
      IsoOnto (w.blockMap hs Θ ⟨q + 1, by omega⟩) (w.num S M ⟨q + 1, by omega⟩)
        (w.den S M ⟨q + 1, by omega⟩) := by
  rcases hl : w.letters[q] with ⟨a, d⟩
  cases d
  · -- an inverse letter: `a` moves `q + 1` to `q`
    have hn : w.next a ⟨q + 1, by omega⟩ = some ⟨q, by omega⟩ :=
      (w.next_eq_some_iff hs.1 _ _ _).mpr (Or.inr ⟨by simp, by simpa using hl, by simp⟩)
    have hrel : ∀ y, MonomialData.actL (k := k) (D.α a) (w.blockMap hs Θ ⟨q + 1, by omega⟩ y) =
        w.blockMap hs Θ ⟨q, by omega⟩ y := by
      intro y
      rw [blockMap_apply, blockMap_apply, MonomialData.actL_apply, ← LinearMap.map_smul Θ (D.α a)]
      have hn' : (w.blockQuiver V hs.1).next a ⟨q + 1, by omega⟩ = some ⟨q, by omega⟩ := hn
      exact congrArg Θ (MonomialData.BlockQuiver.α_smul_single _ (w.blockQuiver_kills V hs) hn' y)
    have hF := w.fiso_succ_false hs S M q hq a hl
    have heq : (MonomialData.actL (D.α a)).comp (w.blockMap hs Θ ⟨q + 1, by omega⟩) =
        w.blockMap hs Θ ⟨q, by omega⟩ := LinearMap.ext hrel
    constructor
    · intro h; exact h.bwd hF (hmem _) hrel
    · intro h; rw [← heq]; exact h.fwd hF
  · -- a direct letter: `a` moves `q` to `q + 1`
    have hn : w.next a ⟨q, by omega⟩ = some ⟨q + 1, by omega⟩ :=
      (w.next_eq_some_iff hs.1 _ _ _).mpr (Or.inl ⟨hq, hl, rfl⟩)
    have hrel : ∀ y, MonomialData.actL (k := k) (D.α a) (w.blockMap hs Θ ⟨q, by omega⟩ y) =
        w.blockMap hs Θ ⟨q + 1, by omega⟩ y := by
      intro y
      rw [blockMap_apply, blockMap_apply, MonomialData.actL_apply, ← LinearMap.map_smul Θ (D.α a)]
      have hn' : (w.blockQuiver V hs.1).next a ⟨q, by omega⟩ = some ⟨q + 1, by omega⟩ := hn
      exact congrArg Θ (MonomialData.BlockQuiver.α_smul_single _ (w.blockQuiver_kills V hs) hn' y)
    have hF := w.fiso_succ_true hs S M q hq a hl
    have heq : (MonomialData.actL (D.α a)).comp (w.blockMap hs Θ ⟨q, by omega⟩) =
        w.blockMap hs Θ ⟨q + 1, by omega⟩ := LinearMap.ext hrel
    constructor
    · intro h; rw [← heq]; exact h.fwd hF
    · intro h; exact h.bwd hF (hmem _) hrel

include hs in
/-- A string map inducing an isomorphism at one position does so at every position. -/
theorem iso_all (Θ : (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs) →ₗ[B] M)
    (hmem : ∀ q y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) ∈ w.num S M q)
    (p : Fin (w.len + 1)) (hp : IsoOnto (w.blockMap hs Θ p) (w.num S M p) (w.den S M p))
    (q : Fin (w.len + 1)) : IsoOnto (w.blockMap hs Θ q) (w.num S M q) (w.den S M q) := by
  let P : (q : ℕ) → q < w.len + 1 → Prop := fun q h ↦
    IsoOnto (w.blockMap hs Θ ⟨q, h⟩) (w.num S M ⟨q, h⟩) (w.den S M ⟨q, h⟩)
  have hP : ∀ a b (ha : a < w.len + 1) (hb : b < w.len + 1), a = b → P a ha → P b hb := by
    intro a b ha hb e h; subst e; exact h
  have up : ∀ d q (h : q + d < w.len + 1), P q (by omega) → P (q + d) h := by
    intro d
    induction d with
    | zero => intro q h hq; exact hq
    | succ d ih =>
        intro q h hq
        exact (w.iso_succ_iff hs S Θ hmem (q + d) (by omega)).mp (ih q (by omega) hq)
  have down : ∀ d q (h : q + d < w.len + 1), P (q + d) h → P q (by omega) := by
    intro d
    induction d with
    | zero => intro q h hq; exact hq
    | succ d ih =>
        intro q h hq
        have h1 : P (q + 1 + d) (by omega) := hP _ _ _ _ (by omega) hq
        have h2 := ih (q + 1) (by omega) h1
        exact (w.iso_succ_iff hs S Θ hmem q (by omega)).mpr h2
  rcases le_total p.val q.val with hle | hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    exact hP _ _ _ _ hd.symm (up d p.val (by omega) hp)
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hp' : P (q.val + d) (by omega) := hP _ _ _ _ hd hp
    exact down d q.val (by omega) hp'

end Word

end BrickAccessibility
