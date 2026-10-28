module

public import BrickAccessibility.Quiver.Classes
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.Algebra.Operations

/-!
# Chains of nonzero paths in special biserial path data

For admissible special biserial path data, the nonzero paths starting with an arrow `a`
are the prefixes of one longest path `Pm a` (`prefix_Pm`), and nonzero paths ending with
the same arrow are suffix-comparable (`chain_suffix`). Paths of positive length span a
nilpotent subspace (`RadGe`), so a scalar plus such an element is a unit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

namespace PathData

variable {Q : FinQuiver} {A : Type*} [Ring A] (D : PathData Q A)

theorem pval_append_ne {x : Q.V} {l₁ l₂ : List Q.A} (h : D.pval x (l₁ ++ l₂) ≠ 0) :
    D.pval x l₁ ≠ 0 ∧ D.pval (Q.pend x l₁) l₂ ≠ 0 := by
  rw [D.pval_append] at h
  exact ⟨fun h' ↦ h (by rw [h', mul_zero]), fun h' ↦ h (by rw [h', zero_mul])⟩

theorem src_eq_of_ne {x : Q.V} {a : Q.A} {l : List Q.A} (h : D.pval x (a :: l) ≠ 0) :
    Q.src a = x := by
  by_contra h'
  exact h (D.pval_cons_of_ne l h')

theorem pval_tail_ne {x : Q.V} {a : Q.A} {l : List Q.A} (h : D.pval x (a :: l) ≠ 0) :
    D.pval (Q.tgt a) l ≠ 0 :=
  (D.pval_append_ne (l₁ := [a]) (l₂ := l) h).2

theorem allowed_of_ne {x : Q.V} {l₁ l₂ : List Q.A} {c d : Q.A}
    (h : D.pval x (l₁ ++ c :: d :: l₂) ≠ 0) : D.Allowed c d := by
  have h1 := (D.pval_append_ne h).2
  have hc := D.src_eq_of_ne h1
  rw [← hc] at h1
  have h2 : D.pval (Q.src c) [c, d] ≠ 0 := (D.pval_append_ne (l₁ := [c, d]) (l₂ := l₂) h1).1
  refine ⟨D.src_eq_of_ne (D.pval_tail_ne h2), h2⟩

theorem card_le_one_elim {α : Type*} [Finite α] {P : α → Prop} (h : Nat.card {x // P x} ≤ 1)
    {x y : α} (hx : P x) (hy : P y) : x = y := by
  rw [Finite.card_le_one_iff_subsingleton] at h
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : {x // P x}) ⟨y, hy⟩)

section Biserial

variable {D} (hsb : D.IsSpecialBiserial)
include hsb

theorem succ_unique {a b b' : Q.A} (h1 : D.Allowed a b) (h2 : D.Allowed a b') : b = b' :=
  card_le_one_elim (hsb.2.2.1 a) h1 h2

theorem pred_unique {a a' b : Q.A} (h1 : D.Allowed a b) (h2 : D.Allowed a' b) : a = a' :=
  card_le_one_elim (hsb.2.2.2 b) h1 h2

/-- At most two arrows start at a vertex. -/
theorem out_two {x : Q.V} {a b c : Q.A} (ha : Q.src a = x) (hb : Q.src b = x) (hc : Q.src c = x)
    (hba : b ≠ a) (hca : c ≠ a) : b = c := by
  by_contra hbc
  have h := hsb.1 x
  let f : Fin 3 → {a : Q.A // Q.src a = x} := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this h
  omega

/-- **Forward chains**: nonzero paths with the same first arrow are prefix-comparable. -/
theorem chain_prefix : ∀ (l l' : List Q.A) (x : Q.V) (a : Q.A), D.pval x (a :: l) ≠ 0 →
    D.pval x (a :: l') ≠ 0 → l.length ≤ l'.length → l <+: l' := by
  intro l
  induction l with
  | nil => intro l' _ _ _ _ _; exact List.nil_prefix
  | cons b l ih =>
      intro l' x a h1 h2 hle
      obtain ⟨b', l', rfl⟩ : ∃ b' l'', l' = b' :: l'' := by
        cases l' with
        | nil => simp at hle
        | cons b' l'' => exact ⟨b', l'', rfl⟩
      have e : b = b' := succ_unique hsb (D.allowed_of_ne (l₁ := []) h1)
        (D.allowed_of_ne (l₁ := []) h2)
      subst e
      rw [List.prefix_cons_inj]
      exact ih l' (Q.tgt a) b (D.pval_tail_ne h1) (D.pval_tail_ne h2)
        (by simp at hle; omega)

/-- **Backward chains**: nonzero paths with the same last arrow are suffix-comparable. -/
theorem chain_suffix : ∀ (l l' : List Q.A) (x x' : Q.V) (c : Q.A), D.pval x (l ++ [c]) ≠ 0 →
    D.pval x' (l' ++ [c]) ≠ 0 → l.length ≤ l'.length → ∃ W, l' = W ++ l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro l' _ _ _ _ _ _; exact ⟨l', by simp⟩
  | append_singleton l d ih =>
      intro l' x x' c h1 h2 hle
      obtain ⟨l0, d', rfl⟩ : ∃ l0 d', l' = l0 ++ [d'] := by
        rcases List.eq_nil_or_concat l' with h | ⟨L, b, h⟩
        · subst h; simp at hle
        · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
      have h1' : D.pval x (l ++ d :: c :: []) ≠ 0 := by simpa using h1
      have h2' : D.pval x' (l0 ++ d' :: c :: []) ≠ 0 := by simpa using h2
      have e : d = d' := pred_unique hsb (D.allowed_of_ne h1') (D.allowed_of_ne h2')
      subst e
      obtain ⟨W, hW⟩ := ih l0 x x' d (D.pval_append_ne h1).1 (D.pval_append_ne h2).1
        (by simp at hle; omega)
      exact ⟨W, by rw [hW, List.append_assoc]⟩

end Biserial

section Longest

variable {D} (hadm : D.IsAdmissible)
include hadm

theorem exists_tl (a : Q.A) : ∃ l, D.pval (Q.src a) (a :: l) ≠ 0 ∧
    ∀ l', D.pval (Q.src a) (a :: l') ≠ 0 → l'.length ≤ l.length := by
  classical
  obtain ⟨-, hα, N, hN⟩ := hadm
  let S : ℕ → Prop := fun m ↦ ∃ l : List Q.A, l.length = m ∧ D.pval (Q.src a) (a :: l) ≠ 0
  have h0 : S 0 := ⟨[], rfl, by rw [D.pval_single_src]; exact hα a⟩
  obtain ⟨l, hl, hne⟩ := Nat.findGreatest_spec (P := S) (Nat.zero_le N) h0
  refine ⟨l, hne, fun l' hl' ↦ ?_⟩
  have hlt : l'.length ≤ N := by
    by_contra h
    exact hl' (hN _ _ (by simp; omega))
  rw [hl]
  exact Nat.le_findGreatest hlt ⟨l', rfl, hl'⟩

/-- The tail of a longest nonzero path starting with `a`. -/
def tl (a : Q.A) : List Q.A := (exists_tl hadm a).choose

/-- A longest nonzero path starting with `a`. -/
def Pm (a : Q.A) : List Q.A := a :: tl hadm a

theorem Pm_ne (a : Q.A) : D.pval (Q.src a) (Pm hadm a) ≠ 0 := (exists_tl hadm a).choose_spec.1

theorem tl_max {a : Q.A} {l : List Q.A} (h : D.pval (Q.src a) (a :: l) ≠ 0) :
    l.length ≤ (tl hadm a).length := (exists_tl hadm a).choose_spec.2 l h

/-- Paths longer than `Pm a` that start with `a` vanish. -/
theorem pval_long {x : Q.V} {a : Q.A} {l : List Q.A} (h : (tl hadm a).length < l.length) :
    D.pval x (a :: l) = 0 := by
  by_contra hne
  have := D.src_eq_of_ne hne
  subst this
  have := tl_max hadm hne
  omega

/-- Every nonzero path starting with `a` is a prefix of `Pm a`. -/
theorem prefix_Pm (hsb : D.IsSpecialBiserial) {x : Q.V} {a : Q.A} {l : List Q.A}
    (h : D.pval x (a :: l) ≠ 0) : a :: l <+: Pm hadm a := by
  have hx := D.src_eq_of_ne h
  subst hx
  rw [Pm, List.prefix_cons_inj]
  exact chain_prefix hsb l (tl hadm a) _ a h (Pm_ne hadm a) (tl_max hadm h)

end Longest

section Rad

variable (k : Type*) [Field k] [Algebra k A]

/-- The span of paths of length at least `n`. -/
def RadGe (n : ℕ) : Submodule k A :=
  Submodule.span k {v | ∃ x l, n ≤ List.length l ∧ v = D.pval x l}

variable {k}

theorem pval_mem_radGe {n : ℕ} (x : Q.V) {l : List Q.A} (h : n ≤ l.length) :
    D.pval x l ∈ D.RadGe k n :=
  Submodule.subset_span ⟨x, l, h, rfl⟩

theorem radGe_mul (m n : ℕ) : D.RadGe k m * D.RadGe k n ≤ D.RadGe k (m + n) := by
  rw [RadGe, RadGe, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨y, l', hl', rfl⟩, _, ⟨x, l, hl, rfl⟩, rfl⟩
  show D.pval y l' * D.pval x l ∈ _
  rw [D.pval_mul_pval]
  split_ifs
  · exact D.pval_mem_radGe x (by simp; omega)
  · exact Submodule.zero_mem _

theorem mul_mem_radGe {m n : ℕ} {a b : A} (ha : a ∈ D.RadGe k m) (hb : b ∈ D.RadGe k n) :
    a * b ∈ D.RadGe k (m + n) :=
  D.radGe_mul m n (Submodule.mul_mem_mul ha hb)

theorem one_mem_radGe_zero : (1 : A) ∈ D.RadGe k 0 := by
  rw [← D.sum_e]
  exact Submodule.sum_mem _ fun v _ ↦ D.pval_mem_radGe (l := []) v le_rfl

theorem pow_mem_radGe {r : A} (hr : r ∈ D.RadGe k 1) (n : ℕ) : r ^ n ∈ D.RadGe k n := by
  induction n with
  | zero => rw [pow_zero]; exact D.one_mem_radGe_zero
  | succ n ih => rw [pow_succ]; exact D.mul_mem_radGe ih hr

variable {D}

theorem radGe_eq_bot (hadm : D.IsAdmissible) : ∃ N, D.RadGe k N = ⊥ := by
  obtain ⟨-, -, N, hN⟩ := hadm
  refine ⟨N, eq_bot_iff.mpr (Submodule.span_le.mpr ?_)⟩
  rintro _ ⟨x, l, hl, rfl⟩
  rw [hN x l hl]; exact Submodule.zero_mem _

theorem isNilpotent_of_mem (hadm : D.IsAdmissible) {r : A} (hr : r ∈ D.RadGe k 1) :
    IsNilpotent r := by
  obtain ⟨N, hN⟩ := radGe_eq_bot (k := k) hadm
  refine ⟨N, ?_⟩
  have := D.pow_mem_radGe hr N
  rw [hN] at this
  exact (Submodule.mem_bot k).mp this

/-- A nonzero scalar plus a radical element is a unit. -/
theorem isUnit_add (hadm : D.IsAdmissible) {c : k} (hc : c ≠ 0) {r : A} (hr : r ∈ D.RadGe k 1) :
    IsUnit (algebraMap k A c + r) :=
  (isNilpotent_of_mem hadm hr).isUnit_add_left_of_commute
    ((IsUnit.mk0 c hc).map (algebraMap k A)) (Algebra.commutes c r).symm

theorem e_not_mem (hadm : D.IsAdmissible) (x : Q.V) : D.e x ∉ D.RadGe k 1 := by
  intro h
  obtain ⟨n, hn⟩ := isNilpotent_of_mem hadm h
  have hp : ∀ m, D.e x ^ (m + 1) = D.e x := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one]
    | succ m ih => rw [pow_succ, ih, D.e_idem]
  apply hadm.1 x
  rcases n with _ | n
  · rw [pow_zero] at hn
    have : (1 : A) = 0 := hn
    rw [← mul_one (D.e x), this, mul_zero]
  · rw [← hp n, hn]

end Rad

end PathData

end BrickAccessibility
