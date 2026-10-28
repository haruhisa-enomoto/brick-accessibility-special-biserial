module

public import BrickAccessibility.Quiver.Classes
public import BrickAccessibility.Section4.Extending

/-!
# Sign functions for string algebras

Butler–Ringel sign functions `σ, ε : Q₁ → Bool`: arrows with a common source
have different `σ`, arrows with a common target have different `ε`, and
`σ b ≠ ε a` whenever `ab` is a nonzero path. They exist for special biserial
path data (`exists_signs`).

A letter starts with sign `S` and ends with sign `E`; in a string consecutive
letters `l, l'` satisfy `S l' ≠ E l`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable (D : MonomialData k B)

/-- Sign functions on the arrows. -/
structure Signs where
  σ : D.Q.A → Bool
  ε : D.Q.A → Bool
  hσ : ∀ a b, a ≠ b → D.Q.src a = D.Q.src b → σ a ≠ σ b
  hε : ∀ a b, a ≠ b → D.Q.tgt a = D.Q.tgt b → ε a ≠ ε b
  hall : ∀ a b, D.toPathData.Allowed a b → σ b ≠ ε a

theorem exists_injOn_of_card_le_two {α : Type*} [Finite α] {P : α → Prop}
    (h : Nat.card {x // P x} ≤ 2) : ∃ f : α → Bool, ∀ x y, P x → P y → x ≠ y → f x ≠ f y := by
  classical
  haveI := Fintype.ofFinite α
  have h' : Fintype.card {x // P x} ≤ Fintype.card Bool := by
    rw [← Nat.card_eq_fintype_card]; simpa using h
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le h'
  refine ⟨fun x ↦ if hx : P x then g ⟨x, hx⟩ else false, fun x y hx hy hxy h ↦ hxy ?_⟩
  simp only [hx, hy, dite_true] at h
  exact congrArg Subtype.val (g.injective h)

variable {D}

/-- Sign functions exist for special biserial path data. -/
theorem exists_signs (hSB : D.toPathData.IsSpecialBiserial) : Nonempty (Signs D) := by
  classical
  -- outgoing signs
  have hout : ∀ x, ∃ f : D.Q.A → Bool, ∀ a b, D.Q.src a = x → D.Q.src b = x → a ≠ b → f a ≠ f b :=
    fun x ↦ exists_injOn_of_card_le_two (hSB.1 x)
  have hin : ∀ y, ∃ f : D.Q.A → Bool, ∀ a b, D.Q.tgt a = y → D.Q.tgt b = y → a ≠ b → f a ≠ f b :=
    fun y ↦ exists_injOn_of_card_le_two (hSB.2.1 y)
  choose fo hfo using hout
  choose fi hfi using hin
  let σ : D.Q.A → Bool := fun a ↦ fo (D.Q.src a) a
  -- the allowed successor, if any
  have hsucc : ∀ a b b', D.toPathData.Allowed a b → D.toPathData.Allowed a b' → b = b' := by
    intro a b b' h h'
    have := hSB.2.2.1 a
    rw [Finite.card_le_one_iff_subsingleton] at this
    exact congrArg Subtype.val (Subsingleton.elim (⟨b, h⟩ : {b // D.toPathData.Allowed a b}) ⟨b', h'⟩)
  have hpred : ∀ a a' b, D.toPathData.Allowed a b → D.toPathData.Allowed a' b → a = a' := by
    intro a a' b h h'
    have := hSB.2.2.2 b
    rw [Finite.card_le_one_iff_subsingleton] at this
    exact congrArg Subtype.val (Subsingleton.elim (⟨a, h⟩ : {a // D.toPathData.Allowed a b}) ⟨a', h'⟩)
  have hσne : ∀ b b', b ≠ b' → D.Q.src b = D.Q.src b' → σ b ≠ σ b' := by
    intro b b' hbb' hs
    simp only [σ]
    rw [hs]
    exact hfo _ b b' hs rfl hbb'
  let ε : D.Q.A → Bool := fun a ↦
    if h : ∃ b, D.toPathData.Allowed a b then !σ h.choose
    else if h' : ∃ a', a' ≠ a ∧ D.Q.tgt a' = D.Q.tgt a ∧ ∃ b, D.toPathData.Allowed a' b then
      σ h'.choose_spec.2.2.choose
    else fi (D.Q.tgt a) a
  refine ⟨⟨σ, ε, fun a b hab hs ↦ hσne a b hab hs, fun a a' haa' ht ↦ ?_, fun a b hab ↦ ?_⟩⟩
  · -- different targets signs
    have key : ∀ a a', a ≠ a' → D.Q.tgt a = D.Q.tgt a' → (∃ b, D.toPathData.Allowed a b) →
        ε a ≠ ε a' := by
      intro a a' haa' ht ⟨b, hb⟩
      have hεa : ε a = !σ b := by
        simp only [ε, dif_pos (⟨b, hb⟩ : ∃ b, D.toPathData.Allowed a b)]
        rw [hsucc _ _ _ (⟨b, hb⟩ : ∃ b, D.toPathData.Allowed a b).choose_spec hb]
      by_cases h' : ∃ b', D.toPathData.Allowed a' b'
      · obtain ⟨b', hb'⟩ := h'
        have hεa' : ε a' = !σ b' := by
          simp only [ε, dif_pos (⟨b', hb'⟩ : ∃ b, D.toPathData.Allowed a' b)]
          rw [hsucc _ _ _ (⟨b', hb'⟩ : ∃ b, D.toPathData.Allowed a' b).choose_spec hb']
        rw [hεa, hεa']
        have hbb' : b ≠ b' := fun h ↦ haa' (hpred _ _ _ hb (h ▸ hb'))
        have := hσne b b' hbb' (hb.1.trans (ht.trans hb'.1.symm))
        simpa using this
      · have hex : ∃ a'', a'' ≠ a' ∧ D.Q.tgt a'' = D.Q.tgt a' ∧ ∃ b, D.toPathData.Allowed a'' b :=
          ⟨a, haa', ht, b, hb⟩
        have hεa' : ε a' = σ hex.choose_spec.2.2.choose := by
          simp only [ε, dif_neg h', dif_pos hex]
        rw [hεa, hεa']
        -- the witness is `a`, since at most two arrows end at the target
        have hwit : hex.choose = a := by
          by_contra hne
          obtain ⟨h1, h2, -⟩ := hex.choose_spec
          exact Word.false_of_card_le_two (hSB.2.1 (D.Q.tgt a')) (x := hex.choose) (y := a)
            (z := a') h2 ht rfl hne h1 haa'
        set c := hex.choose with hc
        set b'' := hex.choose_spec.2.2.choose with hb''
        have hb2 : D.toPathData.Allowed c b'' := hex.choose_spec.2.2.choose_spec
        rw [hwit] at hb2
        rw [hsucc _ _ _ hb2 hb]
        simp
    by_cases ha : ∃ b, D.toPathData.Allowed a b
    · exact key a a' haa' ht ha
    by_cases ha' : ∃ b, D.toPathData.Allowed a' b
    · exact (key a' a (Ne.symm haa') ht.symm ha').symm
    · have h1 : ¬ ∃ a'', a'' ≠ a ∧ D.Q.tgt a'' = D.Q.tgt a ∧ ∃ b, D.toPathData.Allowed a'' b := by
        rintro ⟨a'', h1, h2, h3⟩
        by_cases h : a'' = a'
        · subst h; exact ha' h3
        · exact Word.false_of_card_le_two (hSB.2.1 (D.Q.tgt a)) (x := a'') (y := a) (z := a')
            h2 rfl ht.symm h1 h haa'
      have h2 : ¬ ∃ a'', a'' ≠ a' ∧ D.Q.tgt a'' = D.Q.tgt a' ∧ ∃ b, D.toPathData.Allowed a'' b := by
        rintro ⟨a'', h1, h2, h3⟩
        by_cases h : a'' = a
        · subst h; exact ha h3
        · exact Word.false_of_card_le_two (hSB.2.1 (D.Q.tgt a')) (x := a'') (y := a') (z := a)
            h2 rfl ht h1 h (Ne.symm haa')
      simp only [ε, dif_neg ha, dif_neg ha', dif_neg h1, dif_neg h2]
      rw [ht]
      exact hfi _ a a' ht rfl haa'
  · -- allowed pairs alternate
    have hεa : ε a = !σ b := by
      simp only [ε, dif_pos (⟨b, hab⟩ : ∃ b', D.toPathData.Allowed a b')]
      rw [hsucc _ _ _ (⟨b, hab⟩ : ∃ b', D.toPathData.Allowed a b').choose_spec hab]
    rw [hεa]; simp

variable (S : Signs D)

/-- The sign of a letter at its start. -/
def Signs.st (l : Letter D.Q) : Bool := if l.2 then S.σ l.1 else S.ε l.1

/-- The sign of a letter at its end. -/
def Signs.en (l : Letter D.Q) : Bool := if l.2 then S.ε l.1 else S.σ l.1

@[simp] theorem Signs.st_true (a : D.Q.A) : S.st (a, true) = S.σ a := rfl
@[simp] theorem Signs.st_false (a : D.Q.A) : S.st (a, false) = S.ε a := rfl
@[simp] theorem Signs.en_true (a : D.Q.A) : S.en (a, true) = S.ε a := rfl
@[simp] theorem Signs.en_false (a : D.Q.A) : S.en (a, false) = S.σ a := rfl

theorem Signs.st_inv (l : Letter D.Q) : S.st l.inv = S.en l := by
  obtain ⟨a, d⟩ := l; cases d <;> rfl

theorem Signs.en_inv (l : Letter D.Q) : S.en l.inv = S.st l := by
  obtain ⟨a, d⟩ := l; cases d <;> rfl

/-- Letters starting at the same vertex with the same sign and direction agree. -/
theorem Signs.letter_eq {l l' : Letter D.Q} (hs : l.src = l'.src) (hd : l.2 = l'.2)
    (hsign : S.st l = S.st l') : l = l' := by
  obtain ⟨a, d⟩ := l; obtain ⟨a', d'⟩ := l'
  simp only at hd; subst hd
  cases d
  · by_contra h
    have hne : a ≠ a' := fun h' ↦ h (by rw [h'])
    exact S.hε a a' hne hs hsign
  · by_contra h
    have hne : a ≠ a' := fun h' ↦ h (by rw [h'])
    exact S.hσ a a' hne hs hsign

end MonomialData

end BrickAccessibility
