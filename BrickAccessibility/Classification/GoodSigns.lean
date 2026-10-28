module

public import BrickAccessibility.Classification.BandBrickCrit

/-!
# Good signs for gentle algebras

For a gentle algebra there are sign functions such that a composable pair of arrows
`a b` is nonzero exactly when `σ b ≠ ε a` (`exists_good_signs`). For such signs an
adjacent pair of letters is allowed exactly when the signs alternate
(`allowedPair_iff`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B}

/-- Good signs: allowed composable pairs are exactly the sign changes. -/
def Signs.Good (S : D.Signs) : Prop :=
  ∀ a b, D.Q.tgt a = D.Q.src b → (D.toPathData.Allowed a b ↔ S.σ b ≠ S.ε a)

theorem card_le_one_elim {α : Type*} [Finite α] {P : α → Prop} (h : Nat.card {x // P x} ≤ 1)
    {x y : α} (hx : P x) (hy : P y) : x = y := by
  rw [Finite.card_le_one_iff_subsingleton] at h
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : {x // P x}) ⟨y, hy⟩)

/-- **Good signs exist** for gentle algebras. -/
theorem exists_good_signs (hD : D.IsGentle) : ∃ S : D.Signs, S.Good := by
  classical
  have hSB := hD.1.2
  have hout : ∀ x, ∃ f : D.Q.A → Bool, ∀ a b, D.Q.src a = x → D.Q.src b = x → a ≠ b → f a ≠ f b :=
    fun x ↦ exists_injOn_of_card_le_two (hSB.1 x)
  have hin : ∀ y, ∃ f : D.Q.A → Bool, ∀ a b, D.Q.tgt a = y → D.Q.tgt b = y → a ≠ b → f a ≠ f b :=
    fun y ↦ exists_injOn_of_card_le_two (hSB.2.1 y)
  choose fo hfo using hout
  choose fi hfi using hin
  let ε : D.Q.A → Bool := fun a ↦ fi (D.Q.tgt a) a
  have hεne : ∀ a a', a ≠ a' → D.Q.tgt a = D.Q.tgt a' → ε a ≠ ε a' := fun a a' h ht ↦ by
    simp only [ε]; rw [ht]; exact hfi _ a a' ht rfl h
  have hAs : ∀ a b b', D.toPathData.Allowed a b → D.toPathData.Allowed a b' → b = b' :=
    fun a _ _ h h' ↦ card_le_one_elim (hSB.2.2.1 a) h h'
  have hAp : ∀ a a' b, D.toPathData.Allowed a b → D.toPathData.Allowed a' b → a = a' :=
    fun _ _ b h h' ↦ card_le_one_elim (hSB.2.2.2 b) h h'
  have hFs : ∀ a b b', D.toPathData.Forbidden a b → D.toPathData.Forbidden a b' → b = b' :=
    fun a _ _ h h' ↦ card_le_one_elim (hD.2.2.1 a) h h'
  have hFp : ∀ a a' b, D.toPathData.Forbidden a b → D.toPathData.Forbidden a' b → a = a' :=
    fun _ _ b h h' ↦ card_le_one_elim (hD.2.2.2 b) h h'
  have hAF : ∀ a b, D.Q.tgt a = D.Q.src b → (D.toPathData.Allowed a b ∨ D.toPathData.Forbidden a b) :=
    fun a b h ↦ by
      by_cases hz : D.pval (D.Q.src a) [a, b] = 0
      · exact Or.inr ⟨h.symm, hz⟩
      · exact Or.inl ⟨h.symm, hz⟩
  let σ : D.Q.A → Bool := fun b ↦
    if h : ∃ a, D.toPathData.Allowed a b then !ε h.choose
    else if h' : ∃ a, D.Q.tgt a = D.Q.src b then ε h'.choose
    else fo (D.Q.src b) b
  have key : ∀ a b, D.Q.tgt a = D.Q.src b → (D.toPathData.Allowed a b ↔ σ b ≠ ε a) := by
    intro a b hab
    by_cases h : ∃ a', D.toPathData.Allowed a' b
    · have hσ : σ b = !ε h.choose := by simp only [σ, dif_pos h]
      rw [hσ]
      constructor
      · intro hA
        rw [hAp _ _ _ h.choose_spec hA]
        simp
      · intro hne
        by_contra hA
        have hab' : a ≠ h.choose := fun e ↦ hA (e ▸ h.choose_spec)
        have := hεne _ _ hab' (hab.trans h.choose_spec.1)
        revert hne this
        cases ε a <;> cases ε h.choose <;> simp
    · have hex : ∃ a', D.Q.tgt a' = D.Q.src b := ⟨a, hab⟩
      have hσ : σ b = ε hex.choose := by simp only [σ, dif_neg h, dif_pos hex]
      have hF : ∀ a', D.Q.tgt a' = D.Q.src b → D.toPathData.Forbidden a' b := fun a' h' ↦
        (hAF a' b h').resolve_left fun hA ↦ h ⟨a', hA⟩
      rw [hσ, hFp _ _ _ (hF _ hex.choose_spec) (hF _ hab)]
      simp only [ne_eq, not_true_eq_false, iff_false]
      exact fun hA ↦ h ⟨a, hA⟩
  refine ⟨⟨σ, ε, fun b b' hbb' hs ↦ ?_, hεne, fun a b hab ↦ (key a b hab.1.symm).mp hab⟩, key⟩
  -- injectivity of `σ` at sources
  by_cases h1 : ∃ a, D.toPathData.Allowed a b
  · obtain ⟨a1, ha1⟩ := h1
    by_cases h2 : ∃ a, D.toPathData.Allowed a b'
    · obtain ⟨a2, ha2⟩ := h2
      have ha12 : a1 ≠ a2 := fun e ↦ hbb' (hAs _ _ _ ha1 (e ▸ ha2))
      have hk1 := (key a1 b (ha1.1.symm)).mp ha1
      have hk2 := (key a2 b' (ha2.1.symm)).mp ha2
      have hε := hεne _ _ ha12 (ha1.1.symm.trans (hs.trans ha2.1))
      revert hk1 hk2 hε
      cases σ b <;> cases σ b' <;> cases ε a1 <;> cases ε a2 <;> simp
    · -- `a1` is forbidden before `b'`
      have hcomp : D.Q.tgt a1 = D.Q.src b' := ha1.1.symm.trans hs
      have hF : ¬ D.toPathData.Allowed a1 b' := fun hA ↦ h2 ⟨a1, hA⟩
      have hk1 := (key a1 b (ha1.1.symm)).mp ha1
      have hk2 : ¬ (σ b' ≠ ε a1) := fun hne ↦ hF ((key a1 b' hcomp).mpr hne)
      revert hk1 hk2
      cases σ b <;> cases σ b' <;> cases ε a1 <;> simp
  · by_cases h2 : ∃ a, D.toPathData.Allowed a b'
    · obtain ⟨a2, ha2⟩ := h2
      have hcomp : D.Q.tgt a2 = D.Q.src b := ha2.1.symm.trans hs.symm
      have hF : ¬ D.toPathData.Allowed a2 b := fun hA ↦ h1 ⟨a2, hA⟩
      have hk2 := (key a2 b' (ha2.1.symm)).mp ha2
      have hk1 : ¬ (σ b ≠ ε a2) := fun hne ↦ hF ((key a2 b hcomp).mpr hne)
      revert hk1 hk2
      cases σ b <;> cases σ b' <;> cases ε a2 <;> simp
    · -- no allowed predecessors: there are no predecessors at all
      by_cases hex : ∃ a, D.Q.tgt a = D.Q.src b
      · exfalso
        obtain ⟨a, ha⟩ := hex
        have hF1 := (hAF a b ha).resolve_left fun hA ↦ h1 ⟨a, hA⟩
        have hF2 := (hAF a b' (ha.trans hs)).resolve_left fun hA ↦ h2 ⟨a, hA⟩
        exact hbb' (hFs _ _ _ hF1 hF2)
      · have hex' : ¬ ∃ a, D.Q.tgt a = D.Q.src b' := fun ⟨a, ha⟩ ↦ hex ⟨a, ha.trans hs.symm⟩
        simp only [σ, dif_neg h1, dif_neg h2, dif_neg hex, dif_neg hex']
        rw [hs]
        exact hfo _ b b' hs rfl hbb'

/-- For good signs, an adjacent pair of letters is allowed iff the signs alternate. -/
theorem Signs.allowedPair_iff {S : D.Signs} (hS : S.Good) {l l' : Letter D.Q}
    (hw : l.tgt = l'.src) : D.AllowedPair l l' ↔ S.st l' ≠ S.en l := by
  obtain ⟨a, d⟩ := l
  obtain ⟨b, e⟩ := l'
  cases d <;> cases e <;> simp only [Letter.tgt, Letter.src, Bool.false_eq_true, if_false,
    if_true] at hw
  · rw [allowedPair_ff, show S.st (b, false) = S.ε b from rfl,
      show S.en (a, false) = S.σ a from rfl,
      show (S.ε b ≠ S.σ a) ↔ (S.σ a ≠ S.ε b) from ne_comm, ← hS b a hw.symm]
    exact ⟨fun h ↦ ⟨hw, h⟩, fun h ↦ h.2⟩
  · rw [allowedPair_ft, show S.st (b, true) = S.σ b from rfl,
      show S.en (a, false) = S.σ a from rfl]
    exact ⟨fun h ↦ S.hσ b a (Ne.symm h) hw.symm, fun h e ↦ h (by rw [e])⟩
  · rw [allowedPair_tf, show S.st (b, false) = S.ε b from rfl,
      show S.en (a, true) = S.ε a from rfl]
    exact ⟨fun h ↦ S.hε b a (Ne.symm h) hw.symm, fun h e ↦ h (by rw [e])⟩
  · rw [allowedPair_tt, show S.st (b, true) = S.σ b from rfl,
      show S.en (a, true) = S.ε a from rfl, ← hS a b hw]
    exact ⟨fun h ↦ ⟨hw.symm, h⟩, fun h ↦ h.2⟩

end MonomialData

end BrickAccessibility
