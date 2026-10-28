module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Two interval families on a finite-dimensional space

An interval family on a subspace `V` indexed by a linear order `T` is a choice of
subspaces `lo t ≤ hi t ≤ V` with `hi t ≤ lo t'` for `t < t'`, such that every
nonzero vector of `V` lies in some `hi t` but not in `lo t` (Ringel's
functorial filtrations give such families). For two families `A`, `B` the
grid pieces are `num t t' = A.hi t ⊓ B.hi t'` modulo
`den t t' = A.lo t ⊓ B.hi t' ⊔ A.hi t ⊓ B.lo t'`.

* `le_of_num_le`: a subspace `W` with `num ≤ W ⊔ den` everywhere contains `V`.
* `finrank_eq_sum`: `dim V` is the sum of the grid dimensions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

variable {k : Type*} [Field k] {X : Type*} [AddCommGroup X] [Module k X]

/-- An interval family on `V`. -/
structure IFam (V : Submodule k X) (T : Type*) [LinearOrder T] where
  lo : T → Submodule k X
  hi : T → Submodule k X
  lo_le : ∀ t, lo t ≤ hi t
  hi_le : ∀ t, hi t ≤ V
  sep : ∀ {t t'}, t < t' → hi t ≤ lo t'
  cover : ∀ x ∈ V, x ≠ 0 → ∃ t, x ∈ hi t ∧ x ∉ lo t

namespace IFam

variable {V : Submodule k X} {T T' : Type*} [LinearOrder T] [LinearOrder T']

theorem lt_of_mem_lo (A : IFam V T) {t t₁ : T} {x : X} (hx : x ∈ A.lo t) (h1 : x ∈ A.hi t₁)
    (h2 : x ∉ A.lo t₁) : t₁ < t := by
  rcases lt_trichotomy t₁ t with h | rfl | h
  · exact h
  · exact absurd hx h2
  · exact absurd (A.sep h (A.lo_le t hx)) h2

variable (A : IFam V T) (B : IFam V T')

/-- The numerator of a grid piece. -/
def num (A : IFam V T) (B : IFam V T') (t : T) (t' : T') : Submodule k X := A.hi t ⊓ B.hi t'

/-- The denominator of a grid piece. -/
def den (A : IFam V T) (B : IFam V T') (t : T) (t' : T') : Submodule k X :=
  A.lo t ⊓ B.hi t' ⊔ A.hi t ⊓ B.lo t'

theorem den_le_num (t : T) (t' : T') : den A B t t' ≤ num A B t t' :=
  sup_le (inf_le_inf_right _ (A.lo_le t)) (inf_le_inf_left _ (B.lo_le t'))

variable [FiniteDimensional k X]

/-- A subspace containing every grid numerator modulo its denominator contains `V`. -/
theorem le_of_num_le (W : Submodule k X) (hW : ∀ t t', num A B t t' ≤ W ⊔ den A B t t') :
    V ≤ W := by
  -- every nonempty `A`-interval lies in `W`
  have hA : ∀ n, ∀ t, finrank k (A.hi t) = n → A.lo t < A.hi t → A.hi t ≤ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro t hn hne
    have hlo : A.lo t ≤ W := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact W.zero_mem
      obtain ⟨t₁, h1, h2⟩ := A.cover x (A.hi_le t (A.lo_le t hx)) hx0
      have hlt := A.lt_of_mem_lo hx h1 h2
      have hle : A.hi t₁ ≤ A.lo t := A.sep hlt
      have hne₁ : A.lo t₁ < A.hi t₁ := lt_of_le_of_ne (A.lo_le t₁) fun h ↦ h2 (h ▸ h1)
      have := Submodule.finrank_lt_finrank_of_lt (hle.trans_lt hne)
      exact ih _ (hn ▸ this) t₁ rfl hne₁ h1
    -- every nonempty `B`-interval meets `A.hi t` inside `W`
    have hB : ∀ m, ∀ t', finrank k (B.hi t') = m → B.lo t' < B.hi t' →
        A.hi t ⊓ B.hi t' ≤ W := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih' =>
      intro t' hm hne'
      refine (hW t t').trans (sup_le le_rfl (sup_le ((inf_le_left).trans hlo) ?_))
      intro y hy
      obtain ⟨hyA, hyB⟩ := Submodule.mem_inf.mp hy
      by_cases hy0 : y = 0
      · rw [hy0]; exact W.zero_mem
      obtain ⟨t'₁, h1, h2⟩ := B.cover y (B.hi_le t' (B.lo_le t' hyB)) hy0
      have hlt := B.lt_of_mem_lo hyB h1 h2
      have hle : B.hi t'₁ ≤ B.lo t' := B.sep hlt
      have hne₁ : B.lo t'₁ < B.hi t'₁ := lt_of_le_of_ne (B.lo_le t'₁) fun h ↦ h2 (h ▸ h1)
      have := Submodule.finrank_lt_finrank_of_lt (hle.trans_lt hne')
      exact ih' _ (hm ▸ this) t'₁ rfl hne₁ (Submodule.mem_inf.mpr ⟨hyA, h1⟩)
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact W.zero_mem
    obtain ⟨t', h1, h2⟩ := B.cover x (A.hi_le t hx) hx0
    have hne' : B.lo t' < B.hi t' := lt_of_le_of_ne (B.lo_le t') fun h ↦ h2 (h ▸ h1)
    exact hB _ t' rfl hne' (Submodule.mem_inf.mpr ⟨hx, h1⟩)
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact W.zero_mem
  obtain ⟨t, h1, h2⟩ := A.cover x hx hx0
  have hne : A.lo t < A.hi t := lt_of_le_of_ne (A.lo_le t) fun h ↦ h2 (h ▸ h1)
  exact hA _ t rfl hne h1

/-- Nonempty intervals of a family. -/
def Supp (A : IFam V T) : Set T := {t | A.lo t < A.hi t}

theorem supp_finite : A.Supp.Finite := by
  have hinj : Set.InjOn (fun t ↦ finrank k (A.hi t)) A.Supp := by
    intro t ht t' ht' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := Submodule.finrank_lt_finrank_of_lt ((A.sep hlt).trans_lt ht')
      simp only at h; omega
    · have := Submodule.finrank_lt_finrank_of_lt ((A.sep hlt).trans_lt ht)
      simp only at h; omega
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.finite_Iic (finrank k X)).subset ?_
  rintro _ ⟨t, -, rfl⟩
  exact Submodule.finrank_le _

theorem num_le_den_of_not_mem {t : T} (ht : t ∉ A.Supp) (t' : T') : num A B t t' ≤ den A B t t' := by
  have h : A.lo t = A.hi t := by
    by_contra h; exact ht (lt_of_le_of_ne (A.lo_le t) h)
  exact le_sup_of_le_left (by rw [num, h])

theorem num_le_den_of_not_mem' {t' : T'} (ht : t' ∉ B.Supp) (t : T) :
    num A B t t' ≤ den A B t t' := by
  have h : B.lo t' = B.hi t' := by
    by_contra h; exact ht (lt_of_le_of_ne (B.lo_le t') h)
  exact le_sup_of_le_right (by rw [num, h])

theorem exists_relCompl {L N : Submodule k X} (h : L ≤ N) :
    ∃ W : Submodule k X, W ⊔ L = N ∧ W ⊓ L = ⊥ := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl L
  refine ⟨q ⊓ N, ?_, ?_⟩
  · rw [sup_comm, ← sup_inf_assoc_of_le q h, hq.sup_eq_top, top_inf_eq]
  · refine eq_bot_iff.mpr ((inf_le_inf_right L inf_le_left).trans ?_)
    rw [inf_comm]; exact hq.inf_eq_bot.le

omit [FiniteDimensional k X] in
/-- The grid pieces of index lexicographically below `(t, t')` lie in
`A.lo t ⊔ A.hi t ⊓ B.lo t'`. -/
theorem num_le_of_lex_lt {t₁ t : T} {t'₁ t' : T'}
    (h : toLex (t₁, t'₁) < toLex (t, t')) :
    num A B t₁ t'₁ ≤ A.lo t ⊔ A.hi t ⊓ B.lo t' := by
  rcases Prod.Lex.lt_iff.mp h with h | ⟨rfl, h⟩
  · exact le_sup_of_le_left (inf_le_left.trans (A.sep h))
  · exact le_sup_of_le_right (inf_le_inf_left _ (B.sep h))

omit [FiniteDimensional k X] in
theorem den_aux (t : T) (t' : T') :
    (A.lo t ⊔ A.hi t ⊓ B.lo t') ⊓ num A B t t' ≤ den A B t t' := by
  have h1 : A.hi t ⊓ B.lo t' ≤ num A B t t' := inf_le_inf_left _ (B.lo_le t')
  rw [sup_comm, sup_inf_assoc_of_le _ h1]
  exact sup_le le_sup_right
    (le_sup_of_le_left (le_inf inf_le_left (inf_le_right.trans inf_le_right)))

/-- **Dimension formula** for two interval families. -/
theorem finrank_eq_sum :
    finrank k V = ∑ p ∈ (A.supp_finite.toFinset ×ˢ B.supp_finite.toFinset),
      (finrank k (num A B p.1 p.2) - finrank k (den A B p.1 p.2)) := by
  classical
  choose W hW1 hW2 using fun (p : T ×ₗ T') ↦
    exists_relCompl (den_le_num A B (ofLex p).1 (ofLex p).2)
  have hWnum : ∀ p, W p ≤ num A B (ofLex p).1 (ofLex p).2 := fun p ↦ (hW1 p) ▸ le_sup_left
  have hWdim : ∀ p, finrank k (W p) = finrank k (num A B (ofLex p).1 (ofLex p).2) -
      finrank k (den A B (ofLex p).1 (ofLex p).2) := by
    intro p
    have := Submodule.finrank_sup_add_finrank_inf_eq (W p) (den A B (ofLex p).1 (ofLex p).2)
    rw [hW1 p, hW2 p, finrank_bot] at this
    omega
  obtain ⟨P, hP⟩ : ∃ P : Finset (T ×ₗ T'),
      P = (A.supp_finite.toFinset ×ˢ B.supp_finite.toFinset).map toLex.toEmbedding := ⟨_, rfl⟩
  -- the complements over a finite set of indices are independent
  have hind : ∀ Q : Finset (T ×ₗ T'),
      finrank k ↥(⨆ p ∈ Q, W p) = ∑ p ∈ Q, finrank k (W p) := by
    intro Q
    induction Q using Finset.induction_on_max with
    | empty => simp
    | insert a Q hlt ih =>
        have ha : a ∉ Q := fun h ↦ lt_irrefl a (hlt a h)
        rw [Finset.sum_insert ha, Finset.iSup_insert, ← ih]
        have hdisj : W a ⊓ ⨆ p ∈ Q, W p = ⊥ := by
          have hle : (⨆ p ∈ Q, W p) ≤ A.lo (ofLex a).1 ⊔ A.hi (ofLex a).1 ⊓ B.lo (ofLex a).2 :=
            iSup₂_le fun p hp ↦ (hWnum p).trans (num_le_of_lex_lt A B (by
              simpa using hlt p hp))
          refine eq_bot_iff.mpr ?_
          calc W a ⊓ ⨆ p ∈ Q, W p
              ≤ W a ⊓ ((A.lo (ofLex a).1 ⊔ A.hi (ofLex a).1 ⊓ B.lo (ofLex a).2) ⊓
                  num A B (ofLex a).1 (ofLex a).2) :=
                le_inf inf_le_left (le_inf (inf_le_right.trans hle) (inf_le_left.trans (hWnum a)))
            _ ≤ W a ⊓ den A B (ofLex a).1 (ofLex a).2 := inf_le_inf_left _ (den_aux A B _ _)
            _ = ⊥ := hW2 a
        have := Submodule.finrank_sup_add_finrank_inf_eq (W a) (⨆ p ∈ Q, W p)
        rw [hdisj, finrank_bot] at this
        omega
  -- the complements span `V`
  have hspan : (⨆ p ∈ P, W p) = V := by
    refine le_antisymm (iSup₂_le fun p _ ↦
      (hWnum p).trans (inf_le_left.trans (A.hi_le _))) (le_of_num_le A B _ fun t t' ↦ ?_)
    by_cases hp : toLex (t, t') ∈ P
    · have e : W (toLex (t, t')) ⊔ den A B t t' = num A B t t' := hW1 (toLex (t, t'))
      rw [← e]
      have h1 : W (toLex (t, t')) ≤ ⨆ p ∈ P, W p := le_iSup₂ (f := fun p _ ↦ W p) _ hp
      exact sup_le_sup_right h1 _
    · refine le_sup_of_le_right ?_
      by_cases ht : t ∈ A.Supp
      · refine num_le_den_of_not_mem' A B (fun ht' ↦ hp ?_) t
        rw [hP]
        exact Finset.mem_map.mpr ⟨(t, t'), Finset.mem_product.mpr
          ⟨A.supp_finite.mem_toFinset.mpr ht, B.supp_finite.mem_toFinset.mpr ht'⟩, rfl⟩
      · exact num_le_den_of_not_mem A B ht t'
  calc finrank k V = finrank k ↥(⨆ p ∈ P, W p) := by rw [hspan]
    _ = _ := by rw [hind, hP, Finset.sum_map]; exact Finset.sum_congr rfl fun p _ ↦ hWdim _

end IFam

end BrickAccessibility
