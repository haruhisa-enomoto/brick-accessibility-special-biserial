module

public import BrickAccessibility.Classification.BandMaps
public import BrickAccessibility.Classification.Shift

/-!
# Shift isomorphisms along a band

Each letter of a band `b` gives an isomorphism between the pair functors at the
two adjacent positions (`fiso_true`, `fiso_false`). Hence a map from a band
module inducing an isomorphism at the first position does so at every position
(`iso_all`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- An `FIso` detects vanishing of the pair functor. -/
theorem FIso.le_iff {X : Type*} [AddCommGroup X] [Module k X] {φ : X →ₗ[k] X}
    {n₁ d₁ n₂ d₂ : Submodule k X} (h : FIso φ n₁ d₁ n₂ d₂) : n₁ ≤ d₁ ↔ n₂ ≤ d₂ := by
  constructor
  · intro hle
    exact h.surj.trans (sup_le ((Submodule.map_mono hle).trans h.map_den) le_rfl)
  · intro hle x hx
    exact h.inj x hx (hle (h.map_num ⟨x, hx, rfl⟩))

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
variable [FiniteDimensional k M]

include hA

/-- The shift across a direct letter of the band. -/
theorem fiso_true (i : Fin b.n) (a : D.Q.A) (hl : b.lt i = (a, true)) :
    FIso (MonomialData.actL (D.α a)) (b.numB S M i) (b.denB S M i)
      (b.numB S M (b.succ i)) (b.denB S M (b.succ i)) := by
  have hsrc : D.Q.src a = b.vtx i := by simp [vtx, hl, Letter.src]
  have htgt : D.Q.tgt a = b.vtx (b.succ i) := by
    rw [← b.lt_tgt, hl]; rfl
  have hσ : S.σ a = S.st (b.lt i) := by rw [hl]; rfl
  have hε : (!S.ε a) = S.st (b.lt (b.succ i)) := by
    rw [b.st_succ S hA, hl]; rfl
  have hX : S.Valid (D.Q.tgt a) (!S.ε a) (.inf (b.rightW (b.succ i))) := by
    rw [htgt, hε]; exact b.valid_rightW S hA _
  have hY : S.Valid (D.Q.src a) (!S.σ a) (.inf (b.leftW i)) := by
    rw [hsrc, hσ]; exact b.valid_leftW S hA _
  have h := S.shift M hX hY
  have e1 : (HWord.inf (b.rightW (b.succ i))).cons (a, true) = .inf (b.rightW i) := by
    rw [b.rightW_cons i, hl]
  have e2 : (HWord.inf (b.leftW i)).cons (a, false) = .inf (b.leftW (b.succ i)) := by
    rw [b.leftW_cons i, hl]; rfl
  rw [e1, e2, hsrc, hσ, htgt, hε] at h
  exact h

/-- The shift across an inverse letter of the band. -/
theorem fiso_false (i : Fin b.n) (a : D.Q.A) (hl : b.lt i = (a, false)) :
    FIso (MonomialData.actL (D.α a)) (b.numB S M (b.succ i)) (b.denB S M (b.succ i))
      (b.numB S M i) (b.denB S M i) := by
  have htgt : D.Q.tgt a = b.vtx i := by simp [vtx, hl, Letter.src]
  have hsrc : D.Q.src a = b.vtx (b.succ i) := by
    rw [← b.lt_tgt, hl]; rfl
  have hε : (!S.ε a) = !S.st (b.lt i) := by rw [hl]; rfl
  have hσ : (!S.σ a) = S.st (b.lt (b.succ i)) := by
    rw [b.st_succ S hA, hl]; rfl
  have hX : S.Valid (D.Q.tgt a) (!S.ε a) (.inf (b.leftW i)) := by
    rw [htgt, hε]; exact b.valid_leftW S hA _
  have hY : S.Valid (D.Q.src a) (!S.σ a) (.inf (b.rightW (b.succ i))) := by
    rw [hsrc, hσ]; exact b.valid_rightW S hA _
  have h := S.shift M hX hY
  have e1 : (HWord.inf (b.leftW i)).cons (a, true) = .inf (b.leftW (b.succ i)) := by
    rw [b.leftW_cons i, hl]; rfl
  have e2 : (HWord.inf (b.rightW (b.succ i))).cons (a, false) = .inf (b.rightW i) := by
    rw [b.rightW_cons i, hl]
  rw [e1, e2] at h
  have hσ' : S.σ a = !S.st (b.lt (b.succ i)) := by rw [← hσ]; simp
  rw [hsrc, hσ', htgt, hε, S.pnum_swap, S.pden_swap, S.pnum_swap, S.pden_swap] at h
  exact h

omit hA [FiniteDimensional k M] in
theorem succ_ne_first {i : Fin b.n} (hi : i.val + 1 < b.n) : b.succ i ≠ b.first := by
  intro h; have := congrArg Fin.val h; rw [b.succ_val_of_lt i hi] at this; simp [first] at this

variable {M} {V : Type u} [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V)

omit [FiniteDimensional k M] in
/-- On an edge other than the last, the band block quiver does not twist (direct). -/
theorem g_true {i : Fin b.n} (hi : i.val + 1 < b.n) {a : D.Q.A} (hl : b.lt i = (a, true))
    (y : V) : (b.blockQuiver S hA V φ).g a i y = y := by
  have h1 : ¬ (i = b.last ∧ b.lt b.last = (a, true)) := fun h' ↦ by
    have := congrArg Fin.val h'.1; simp only [last] at this; omega
  have h2 : ¬ (i = b.first ∧ b.lt b.last = (a, false)) := by
    rintro ⟨rfl, h2⟩
    exact b.not_fork S hA b.last a false h2 (by rw [succ_last]; exact hl)
  simp only [blockQuiver, if_neg h1, if_neg h2]; rfl

omit [FiniteDimensional k M] in
/-- On an edge other than the last, the band block quiver does not twist (inverse). -/
theorem g_false {i : Fin b.n} (hi : i.val + 1 < b.n) {a : D.Q.A} (hl : b.lt i = (a, false))
    (y : V) : (b.blockQuiver S hA V φ).g a (b.succ i) y = y := by
  have h1 : ¬ (b.succ i = b.last ∧ b.lt b.last = (a, true)) := by
    rintro ⟨h1, h2⟩
    rw [← h1] at h2
    exact b.not_fork S hA i a false hl h2
  have h2 : ¬ (b.succ i = b.first ∧ b.lt b.last = (a, false)) := fun h ↦
    b.succ_ne_first hi h.1
  simp only [blockQuiver, if_neg h1, if_neg h2]; rfl

variable (hK : b.KillsZero)

/-- The map from the block at position `q`. -/
def bmap (Θ : (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ) →ₗ[B] M)
    (q : Fin b.n) : V →ₗ[k] M :=
  (Θ.restrictScalars k).comp (((b.blockQuiver S hA V φ).ofFunL
    (b.blockQuiver_kills S hA hK V φ)).comp
    (LinearMap.single k (fun _ : (b.blockQuiver S hA V φ).P ↦ V) q))

omit [FiniteDimensional k M] in
theorem bmap_apply (Θ : (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ) →ₗ[B] M)
    (q : Fin b.n) (y : V) :
    b.bmap S hA φ hK Θ q y = Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) := rfl

theorem iso_succ_iff (Θ : (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ) →ₗ[B] M)
    (hmem : ∀ q y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) ∈ b.numB S M q)
    (i : Fin b.n) (hi : i.val + 1 < b.n) :
    IsoOnto (b.bmap S hA φ hK Θ i) (b.numB S M i) (b.denB S M i) ↔
      IsoOnto (b.bmap S hA φ hK Θ (b.succ i)) (b.numB S M (b.succ i))
        (b.denB S M (b.succ i)) := by
  rcases hl : b.lt i with ⟨a, d⟩
  cases d
  · have hn : (b.blockQuiver S hA V φ).next a (b.succ i) = some i :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inr ⟨by rw [pred_succ]; exact hl, by rw [pred_succ]⟩)
    have hrel : ∀ y, MonomialData.actL (k := k) (D.α a) (b.bmap S hA φ hK Θ (b.succ i) y) =
        b.bmap S hA φ hK Θ i y := by
      intro y
      rw [bmap_apply, bmap_apply, MonomialData.actL_apply, ← LinearMap.map_smul Θ (D.α a)]
      rw [MonomialData.BlockQuiver.α_smul_single _ (b.blockQuiver_kills S hA hK V φ) hn y,
        b.g_false S hA φ hi hl]
    have hF := b.fiso_false S hA M i a hl
    have heq : (MonomialData.actL (D.α a)).comp (b.bmap S hA φ hK Θ (b.succ i)) =
        b.bmap S hA φ hK Θ i := LinearMap.ext hrel
    constructor
    · intro h; exact h.bwd hF (hmem _) hrel
    · intro h; rw [← heq]; exact h.fwd hF
  · have hn : (b.blockQuiver S hA V φ).next a i = some (b.succ i) :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inl ⟨hl, rfl⟩)
    have hrel : ∀ y, MonomialData.actL (k := k) (D.α a) (b.bmap S hA φ hK Θ i y) =
        b.bmap S hA φ hK Θ (b.succ i) y := by
      intro y
      rw [bmap_apply, bmap_apply, MonomialData.actL_apply, ← LinearMap.map_smul Θ (D.α a)]
      rw [MonomialData.BlockQuiver.α_smul_single _ (b.blockQuiver_kills S hA hK V φ) hn y,
        b.g_true S hA φ hi hl]
    have hF := b.fiso_true S hA M i a hl
    have heq : (MonomialData.actL (D.α a)).comp (b.bmap S hA φ hK Θ i) =
        b.bmap S hA φ hK Θ (b.succ i) := LinearMap.ext hrel
    constructor
    · intro h; rw [← heq]; exact h.fwd hF
    · intro h; exact h.bwd hF (hmem _) hrel

/-- A band map inducing an isomorphism at the first position does so at every position. -/
theorem iso_all (Θ : (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ) →ₗ[B] M)
    (hmem : ∀ q y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) ∈ b.numB S M q)
    (h0 : IsoOnto (b.bmap S hA φ hK Θ b.first) (b.numB S M b.first) (b.denB S M b.first))
    (q : Fin b.n) : IsoOnto (b.bmap S hA φ hK Θ q) (b.numB S M q) (b.denB S M q) := by
  have key : ∀ m (hm : m < b.n), IsoOnto (b.bmap S hA φ hK Θ ⟨m, hm⟩) (b.numB S M ⟨m, hm⟩)
      (b.denB S M ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro _; exact h0
    | succ m ih =>
        intro hm
        have := (b.iso_succ_iff S hA φ hK Θ hmem ⟨m, by omega⟩ hm).mp (ih (by omega))
        have e : b.succ ⟨m, by omega⟩ = ⟨m + 1, hm⟩ := Fin.ext (b.succ_val_of_lt _ hm)
        rwa [e] at this
  exact key q.val q.2

end CWord

end BrickAccessibility
