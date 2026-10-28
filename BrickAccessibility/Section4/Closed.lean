module

public import BrickAccessibility.Section4.Inequality
public import BrickAccessibility.Basic.Finiteness

/-!
# Allowed pairs and closed words (before Lemma 4.6)

A composable pair of letters is *allowed* if it is a pair of direct arrows `ab`
with `ab ∉ I`, a pair of inverse arrows `a⁻¹b⁻¹` with `ba ∉ I`, or a mixed pair
`ab⁻¹`, `a⁻¹b` with `a ≠ b`. A closed word all of whose cyclic adjacent pairs are
allowed yields bands, so representation-infinitude
(`not_isRepFinite_of_closed`, part of Theorem 4.5; proved in `Classification/ClosedBand.lean`).

Here: adjacent pairs of a string are allowed (`chain_allowed`), inverse words
(`invLetters`), and the vanishing of the square of a loop and of two-cycles with
both pairs allowed in a gentle algebra (equation (4.l)).
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

/-- Allowed pairs of letters. -/
def AllowedPair (l₁ l₂ : Letter D.Q) : Prop :=
  if l₁.2 = l₂.2 then
    (if l₁.2 then D.pval (D.Q.src l₁.1) [l₁.1, l₂.1] ≠ 0
      else D.pval (D.Q.src l₂.1) [l₂.1, l₁.1] ≠ 0)
  else l₁.1 ≠ l₂.1

@[simp] theorem allowedPair_tt (a b : D.Q.A) :
    D.AllowedPair (a, true) (b, true) ↔ D.pval (D.Q.src a) [a, b] ≠ 0 := by
  simp [AllowedPair]
@[simp] theorem allowedPair_ff (a b : D.Q.A) :
    D.AllowedPair (a, false) (b, false) ↔ D.pval (D.Q.src b) [b, a] ≠ 0 := by
  simp [AllowedPair]
@[simp] theorem allowedPair_tf (a b : D.Q.A) : D.AllowedPair (a, true) (b, false) ↔ a ≠ b := by
  simp [AllowedPair]
@[simp] theorem allowedPair_ft (a b : D.Q.A) : D.AllowedPair (a, false) (b, true) ↔ a ≠ b := by
  simp [AllowedPair]

theorem allowedPair_inv {l₁ l₂ : Letter D.Q} :
    D.AllowedPair l₂.inv l₁.inv ↔ D.AllowedPair l₁ l₂ := by
  obtain ⟨a, d⟩ := l₁; obtain ⟨b, e⟩ := l₂
  cases d <;> cases e <;> simp [Letter.inv, eq_comm]

end MonomialData

/-- The inverse of a list of letters. -/
def invLetters {Q : FinQuiver} (l : List (Letter Q)) : List (Letter Q) :=
  (l.map Letter.inv).reverse

namespace Statement.FinQuiver

variable {Q : FinQuiver}

theorem isWalk_append (x : Q.V) (l₁ l₂ : List (Letter Q)) :
    Q.IsWalk x (l₁ ++ l₂) ↔ Q.IsWalk x l₁ ∧ Q.IsWalk (Q.wend x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => simp [IsWalk, wend]
  | cons l ls ih => simp [IsWalk, wend, ih, and_assoc]

theorem wend_append (x : Q.V) (l₁ l₂ : List (Letter Q)) :
    Q.wend x (l₁ ++ l₂) = Q.wend (Q.wend x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons l ls ih => simp [wend, ih]

theorem isWalk_singleton (x : Q.V) (l : Letter Q) : Q.IsWalk x [l] ↔ l.src = x := by
  simp [IsWalk]

theorem wend_singleton (x : Q.V) (l : Letter Q) : Q.wend x [l] = l.tgt := rfl

theorem isWalk_inv (x : Q.V) (l : List (Letter Q)) (h : Q.IsWalk x l) :
    Q.IsWalk (Q.wend x l) (invLetters l) ∧ Q.wend (Q.wend x l) (invLetters l) = x := by
  induction l generalizing x with
  | nil => simp [IsWalk, wend, invLetters]
  | cons a ls ih =>
      obtain ⟨ha, hls⟩ := h
      obtain ⟨h1, h2⟩ := ih a.tgt hls
      have e : invLetters (a :: ls) = invLetters ls ++ [a.inv] := by simp [invLetters]
      rw [e, isWalk_append, wend_append]
      simp only [wend] at h1 h2 ⊢
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · simp [h2, IsWalk, Letter.src_inv]
      · simp [h2, wend, Letter.tgt_inv, ha]

end Statement.FinQuiver

namespace MonomialData

variable {D : MonomialData k B}

theorem isChain_invLetters {l : List (Letter D.Q)} (h : l.IsChain D.AllowedPair) :
    (invLetters l).IsChain D.AllowedPair := by
  rw [invLetters, List.isChain_reverse, List.isChain_map]
  exact h.imp fun a b hab ↦ (D.allowedPair_inv (l₁ := a) (l₂ := b)).mpr hab

variable (D)

/-- A periodic path all of whose consecutive pairs are allowed is nonzero. -/
theorem pval_ofFn_ne_zero (hD : D.IsQuadratic) (f : ℕ → D.Q.A)
    (hcomp : ∀ i, D.Q.tgt (f i) = D.Q.src (f (i + 1)))
    (hall : ∀ i, D.pval (D.Q.src (f i)) [f i, f (i + 1)] ≠ 0) (m : ℕ) :
    D.pval (D.Q.src (f 0)) (List.ofFn (fun i : Fin (m + 1) ↦ f i)) ≠ 0 := by
  have hwalk : ∀ (g : ℕ → D.Q.A), (∀ i, D.Q.tgt (g i) = D.Q.src (g (i + 1))) → ∀ m,
      D.Q.IsWalk (D.Q.src (g 0)) ((List.ofFn (fun i : Fin (m + 1) ↦ g i)).map (·, true)) := by
    intro g hg m
    induction m generalizing g with
    | zero => simp [Statement.FinQuiver.IsWalk, Letter.src]
    | succ m ih =>
        rw [List.ofFn_succ, List.map_cons]
        refine ⟨by simp [Letter.src], ?_⟩
        have := ih (fun i ↦ g (i + 1)) (fun i ↦ hg (i + 1))
        simp only [Fin.val_succ] at this ⊢
        simpa [Letter.tgt, hg 0] using this
  have hw := hwalk f hcomp m
  rw [List.ofFn_succ] at hw ⊢
  simp only [Fin.val_zero] at hw ⊢
  rw [Ne, hD _ _ (by simpa using hw)]
  rintro ⟨i, hi, hforb⟩
  apply hall i
  simp only [List.length_cons, List.length_ofFn] at hi
  have e1 : (f 0 :: List.ofFn (fun j : Fin m ↦ f (j.succ : ℕ)))[i]'(by simp; omega) = f i := by
    cases i with
    | zero => rfl
    | succ i => simp
  have e2 : (f 0 :: List.ofFn (fun j : Fin m ↦ f (j.succ : ℕ)))[i + 1]'(by simp; omega) =
      f (i + 1) := by simp
  rw [e1, e2] at hforb
  exact hforb.2

/-- Equation (4.l): in a gentle algebra the square of a loop is zero. -/
theorem pval_loop_eq_zero (hD : D.IsGentle) {a : D.Q.A} (ha : D.Q.src a = D.Q.tgt a) :
    D.pval (D.Q.src a) [a, a] = 0 := by
  by_contra h
  obtain ⟨-, -, N, hN⟩ := hD.1.1
  have := D.pval_ofFn_ne_zero hD.2.1 (fun _ ↦ a) (fun _ ↦ ha.symm) (fun _ ↦ h) N
  exact this (hN _ _ (by simp))

/-- In a gentle algebra a two-cycle cannot have both of its paths nonzero. -/
theorem false_of_two_cycle (hD : D.IsGentle) {a b : D.Q.A} (hab : D.Q.tgt a = D.Q.src b)
    (hba : D.Q.tgt b = D.Q.src a) (h1 : D.pval (D.Q.src a) [a, b] ≠ 0)
    (h2 : D.pval (D.Q.src b) [b, a] ≠ 0) : False := by
  obtain ⟨-, -, N, hN⟩ := hD.1.1
  let f : ℕ → D.Q.A := fun i ↦ if i % 2 = 0 then a else b
  have hf : ∀ i, f (i + 1) = if i % 2 = 0 then b else a := by
    intro i
    by_cases h : i % 2 = 0
    · have : (i + 1) % 2 ≠ 0 := by omega
      simp [f, h, this]
    · have : (i + 1) % 2 = 0 := by omega
      simp [f, h, this]
  have := D.pval_ofFn_ne_zero hD.2.1 f
    (fun i ↦ by rw [hf]; simp only [f]; split_ifs <;> simp_all)
    (fun i ↦ by rw [hf]; simp only [f]; split_ifs <;> simp_all) N
  exact this (hN _ _ (by simp))

end MonomialData

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

/-- Adjacent pairs of a string are allowed. -/
theorem chain_allowed (hs : w.IsString D) : w.letters.IsChain D.AllowedPair := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hlen : i + 2 ≤ w.len := by simp only [len]; omega
  have hfork := hs.1 i hi
  rcases hl1 : w.letters[i] with ⟨a, d1⟩
  rcases hl2 : w.letters[i + 1] with ⟨b, d2⟩
  rw [hl1, hl2] at hfork
  cases d1 <;> cases d2
  · -- both inverse: the walk `i + 2 → i + 1 → i` spells `b a`
    have h1 : w.next b ⟨i + 2, by omega⟩ = some ⟨i + 1, by omega⟩ :=
      (w.next_eq_some_iff hs.1 _ _ _).mpr (Or.inr ⟨by simp, by simpa using hl2, by simp⟩)
    have h2 : w.next a ⟨i + 1, by omega⟩ = some ⟨i, by omega⟩ :=
      (w.next_eq_some_iff hs.1 _ _ _).mpr (Or.inr ⟨by simp, by simpa using hl1, by simp⟩)
    simpa using w.pval_pair_ne_zero hs h1 h2
  · simp only [MonomialData.allowedPair_ft]
    intro hab; exact hfork ⟨hab, by simp⟩
  · simp only [MonomialData.allowedPair_tf]
    intro hab; exact hfork ⟨hab, by simp⟩
  · -- both direct: the walk `i → i + 1 → i + 2` spells `a b`
    have h1 : w.next a ⟨i, by omega⟩ = some ⟨i + 1, by omega⟩ :=
      (w.next_eq_some_iff hs.1 _ _ _).mpr (Or.inl ⟨by simp; omega, by simpa using hl1, by simp⟩)
    have h2 : w.next b ⟨i + 1, by omega⟩ = some ⟨i + 2, by omega⟩ :=
      (w.next_eq_some_iff hs.1 _ _ _).mpr (Or.inl ⟨by simp; omega, by simpa using hl2, by simp⟩)
    simpa using w.pval_pair_ne_zero hs h1 h2

end Word

end BrickAccessibility
