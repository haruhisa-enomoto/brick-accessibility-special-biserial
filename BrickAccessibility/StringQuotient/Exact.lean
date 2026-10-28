module

public import BrickAccessibility.StringQuotient.Projective
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Lemma 5.3 in its exact form

For admissible special biserial path data whose arrows are independent modulo paths of
length two (`ArrInd`, true for an admissible presentation), `A e_x` is nonuniserial and
injective exactly at the binomial vertices (`bin_iff`), its socle there is the line of the
longest path (`soc_eq`), so the ideal `J` of `exists_string_quotient` is the sum of the
socles of the nonuniserial injective summands, and every indecomposable module not
annihilated by `J` is a nonuniserial projective-injective module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

/-- A module is uniserial if its submodules form a chain. -/
def IsUniserialMod (R : Type*) [Ring R] (P : Type*) [AddCommGroup P] [Module R P] : Prop :=
  ∀ N₁ N₂ : Submodule R P, N₁ ≤ N₂ ∨ N₂ ≤ N₁

/-- The socle: the sum of the simple submodules. -/
def soc (R : Type*) [Ring R] (P : Type*) [AddCommGroup P] [Module R P] : Submodule R P :=
  sSup {N : Submodule R P | IsSimpleModule R N}

namespace PathData

universe u

variable {k : Type*} [Field k] {Q : FinQuiver} {A : Type u} [Ring A] [Algebra k A]
  {D : PathData Q A}

variable (D) in
/-- The arrows are linearly independent modulo paths of length at least two. -/
def ArrInd : Prop := ∀ c : Q.A → k, ∑ b, c b • D.α b ∈ D.RadGe k 2 → c = 0

theorem decompA
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (b : A) : ∃ (c : Q.V → k) (r : A), r ∈ D.RadGe k 1 ∧ b = ∑ v, c v • D.e v + r := by
  classical
  have hb : b ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  induction hb using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨⟨y, l⟩, rfl⟩ := hb
      cases l with
      | nil =>
          refine ⟨Pi.single y 1, 0, Submodule.zero_mem _, ?_⟩
          rw [add_zero, Finset.sum_eq_single y (fun v _ hv ↦ by simp [Pi.single_eq_of_ne hv])
            (by simp)]
          simp; rfl
      | cons a l =>
          exact ⟨0, D.pval y (a :: l), D.pval_mem_radGe (k := k) (n := 1) y (by simp), by simp⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add b b' _ _ h h' =>
      obtain ⟨c, r, hr, rfl⟩ := h
      obtain ⟨c', r', hr', rfl⟩ := h'
      refine ⟨c + c', r + r', Submodule.add_mem _ hr hr', ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  | smul μ b _ h =>
      obtain ⟨c, r, hr, rfl⟩ := h
      refine ⟨μ • c, μ • r, Submodule.smul_mem _ μ hr, ?_⟩
      simp only [smul_add, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]

theorem e_mul_α_eq (v : Q.V) (a : Q.A) : D.e v * D.α a = if v = Q.tgt a then D.α a else 0 := by
  split_ifs with h
  · rw [h, D.e_mul_α]
  · rw [← D.e_mul_α a, ← mul_assoc, D.e_mul_e_of_ne h, zero_mul]

theorem lx_α {x : Q.V} {a : Q.A} (h : Q.src a = x) : D.α a ∈ D.Lx x := by
  show D.α a * D.e x = D.α a
  rw [← h, D.α_mul_e]

/-- **Two arrows make `A e_x` nonuniserial.** -/
theorem not_uniserial (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (hind : D.ArrInd (k := k)) {x : Q.V} {a b : Q.A} (hab : a ≠ b) (ha : Q.src a = x)
    (hb : Q.src b = x) : ¬ IsUniserialMod A (D.Lx x) := by
  classical
  have key : ∀ {a b : Q.A} (hab : a ≠ b) (ha : Q.src a = x) (hb : Q.src b = x),
      ¬ (Submodule.span A {(⟨D.α a, lx_α ha⟩ : D.Lx x)} ≤
        Submodule.span A {(⟨D.α b, lx_α hb⟩ : D.Lx x)}) := by
    intro a b hab ha hb hle
    have hmem := hle (Submodule.mem_span_singleton_self _)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc' : c * D.α b = D.α a := congrArg Subtype.val hc
    obtain ⟨cv, r, hr, rfl⟩ := decompA hspan c
    have hr2 : r * D.α b ∈ D.RadGe k 2 := by
      have := D.mul_mem_radGe hr (D.pval_mem_radGe (k := k) (n := 1) (Q.src b) (l := [b])
        (by simp))
      rwa [D.pval_single_src] at this
    rw [add_mul, Finset.sum_mul] at hc'
    simp only [smul_mul_assoc, e_mul_α_eq, smul_ite, smul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hc'
    set f : Q.A → k := fun d ↦ if d = a then 1 else if d = b then -cv (Q.tgt b) else 0
    have hsum : ∑ d, f d • D.α d = D.α a - cv (Q.tgt b) • D.α b := by
      rw [Finset.sum_eq_add a b hab (fun d _ hd ↦ by simp [f, hd.1, hd.2]) (by simp)
        (by simp)]
      simp [f, Ne.symm hab, sub_eq_add_neg]
    have h0 := hind f (by rw [hsum, ← hc', add_sub_cancel_left]; exact hr2)
    have := congrFun h0 a
    simp [f] at this
  intro hu
  rcases hu (Submodule.span A {⟨D.α a, lx_α ha⟩}) (Submodule.span A {⟨D.α b, lx_α hb⟩})
    with h | h
  · exact key hab ha hb h
  · exact key (Ne.symm hab) hb ha h

theorem esum_mul_pval (c : Q.V → k) (x : Q.V) (l : List Q.A) :
    (∑ v, c v • D.e v) * D.pval x l = c (Q.pend x l) • D.pval x l := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single (Q.pend x l)]
  · rw [smul_mul_assoc, D.e_pend_mul_pval]
  · intro v _ hv
    rw [smul_mul_assoc, show D.e v = D.pval v [] from rfl, D.pval_mul_pval, if_neg hv, smul_zero]
  · simp

/-- A local cyclic step: a generator whose radical multiples lie in `S` has its submodules
either containing it or inside `S`. -/
theorem chain_step (hadm : D.IsAdmissible)
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    {P : Type*} [AddCommGroup P] [Module A P] {v : P} {y : Q.V}
    (hv : ∀ c : Q.V → k, (∑ w, c w • D.e w) • v = algebraMap k A (c y) • v)
    {S : Submodule A P} (hR : ∀ r ∈ D.RadGe k 1, r • v ∈ S)
    (IH : ∀ N₁ N₂ : Submodule A P, N₁ ≤ S → N₂ ≤ S → N₁ ≤ N₂ ∨ N₂ ≤ N₁) :
    ∀ N₁ N₂ : Submodule A P, N₁ ≤ Submodule.span A {v} → N₂ ≤ Submodule.span A {v} →
      N₁ ≤ N₂ ∨ N₂ ≤ N₁ := by
  have key : ∀ N : Submodule A P, N ≤ Submodule.span A {v} →
      Submodule.span A {v} ≤ N ∨ N ≤ S := by
    intro N hN
    by_cases h : ∃ w ∈ N, w ∉ S
    · left
      obtain ⟨w, hwN, hwS⟩ := h
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp (hN hwN)
      obtain ⟨c, r, hr, rfl⟩ := decompA hspan b
      rw [add_smul, hv] at hwN hwS
      by_cases hc : c y = 0
      · exfalso; apply hwS; rw [hc, map_zero, zero_smul, zero_add]; exact hR r hr
      · obtain ⟨u, hu⟩ := isUnit_add hadm hc hr
        have hw : (algebraMap k A (c y) + r) • v ∈ N := by rw [add_smul]; exact hwN
        rw [← hu] at hw
        have := N.smul_mem (↑u⁻¹ : A) hw
        rw [smul_smul, Units.inv_mul, one_smul] at this
        rw [Submodule.span_le, Set.singleton_subset_iff]; exact this
    · right; push Not at h; exact h
  intro N₁ N₂ h₁ h₂
  rcases key N₁ h₁ with h | h
  · right; exact h₂.trans h
  · rcases key N₂ h₂ with h' | h'
    · left; exact h₁.trans h'
    · exact IH N₁ N₂ h h'

/-- A path from `x` as an element of `A e_x`. -/
def pv (x : Q.V) (l : List Q.A) : D.Lx x := ⟨D.pval x l, D.pval_mul_e x l⟩

theorem pv_hv (x : Q.V) (l : List Q.A) (c : Q.V → k) :
    (∑ w, c w • D.e w) • D.pv x l = algebraMap k A (c (Q.pend x l)) • D.pv x l := by
  apply Subtype.ext
  show (∑ w, c w • D.e w) * D.pval x l = algebraMap k A (c (Q.pend x l)) * D.pval x l
  rw [esum_mul_pval, Algebra.smul_def]

theorem lx_eq_span (x : Q.V) : Submodule.span A {D.pv x []} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  exact Submodule.mem_span_singleton.mpr ⟨w, Subtype.ext hw⟩

theorem rad_mul_e_of_none {x : Q.V} (h0 : ∀ a, Q.src a ≠ x) {r : A} (hr : r ∈ D.RadGe k 1) :
    r * D.e x = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
      obtain ⟨y, σ, hσ, rfl⟩ := hr
      rw [pval_mul_e_eq]
      split_ifs with h
      · subst h
        obtain ⟨a, σ', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hσ)
        exact D.pval_cons_of_ne σ' (h0 a)
      · rfl
  | zero => rw [zero_mul]
  | add r r' _ _ h h' => rw [add_mul, h, h', add_zero]
  | smul μ r _ h => rw [smul_mul_assoc, h, smul_zero]

variable (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial)
  (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)

theorem rad_mul_top {x : Q.V} {a : Q.A} {r : A} (hr : r ∈ D.RadGe k 1) :
    r * D.pval x (Pm hadm a) = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
      obtain ⟨y, σ, hσ, rfl⟩ := hr
      rw [D.pval_mul_pval]
      split_ifs
      · rw [Pm, List.cons_append]
        exact pval_long hadm (by simp only [List.length_append]; omega)
      · rfl
  | zero => rw [zero_mul]
  | add r r' _ _ h h' => rw [add_mul, h, h', add_zero]
  | smul μ r _ h => rw [smul_mul_assoc, h, smul_zero]

include hsb in
theorem prefix_of_one {x : Q.V} (hone : ∀ a b, Q.src a = x → Q.src b = x → a = b) {a : Q.A}
    (hxa : Q.src a = x) {l : List Q.A} (hl : l ≠ []) (h : D.pval x l ≠ 0) : l <+: Pm hadm a := by
  obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  have hb := D.src_eq_of_ne h
  obtain rfl := hone b a hb hxa
  exact prefix_Pm hadm hsb h

include hadm hsb hspan in
/-- **With at most one arrow, `A e_x` is uniserial.** -/
theorem uniserial_of_one {x : Q.V} (hone : ∀ a b, Q.src a = x → Q.src b = x → a = b) :
    IsUniserialMod A (D.Lx x) := by
  classical
  intro N₁ N₂
  have htop : ∀ N : Submodule A (D.Lx x), N ≤ Submodule.span A {D.pv x []} := fun N ↦ by
    rw [lx_eq_span]; exact le_top
  by_cases ha : ∃ a, Q.src a = x
  · obtain ⟨a, hxa⟩ := ha
    set L := (Pm hadm a).length
    let c : ℕ → D.Lx x := fun m ↦ D.pv x ((Pm hadm a).take m)
    have hR : ∀ m, m < L → ∀ r ∈ D.RadGe k 1, r • c m ∈ Submodule.span A {c (m + 1)} := by
      intro m hm r hr
      have key : ∃ b : A, r * D.pval x ((Pm hadm a).take m) =
          b * D.pval x ((Pm hadm a).take (m + 1)) := by
        induction hr using Submodule.span_induction with
        | mem r hr =>
            obtain ⟨y, σ, hσ, rfl⟩ := hr
            rw [D.pval_mul_pval]
            split_ifs with hy
            · by_cases h0 : D.pval x ((Pm hadm a).take m ++ σ) = 0
              · exact ⟨0, by rw [h0, zero_mul]⟩
              · have hσ0 : σ ≠ [] := List.ne_nil_of_length_pos hσ
                obtain ⟨b, σ', rfl⟩ := List.exists_cons_of_ne_nil hσ0
                have hpre := prefix_of_one hadm hsb hone hxa (by simp) h0
                have hpre' : (Pm hadm a).take m ++ [b] <+: Pm hadm a :=
                  (List.prefix_append _ σ').trans (by simpa using hpre)
                have hlen : ((Pm hadm a).take m ++ [b]).length = m + 1 := by
                  simp only [List.length_append, List.length_take, List.length_singleton]; omega
                have heq : (Pm hadm a).take m ++ [b] = (Pm hadm a).take (m + 1) := by
                  rw [List.prefix_iff_eq_take.mp hpre', hlen]
                refine ⟨D.pval (Q.pend x ((Pm hadm a).take m ++ [b])) σ', ?_⟩
                rw [show (Pm hadm a).take m ++ b :: σ' = ((Pm hadm a).take m ++ [b]) ++ σ' by simp,
                  D.pval_append, heq]
            · exact ⟨0, by rw [zero_mul]⟩
        | zero => exact ⟨0, by simp⟩
        | add r r' _ _ h h' =>
            obtain ⟨b, hb⟩ := h; obtain ⟨b', hb'⟩ := h'
            exact ⟨b + b', by rw [add_mul, hb, hb', add_mul]⟩
        | smul μ r _ h =>
            obtain ⟨b, hb⟩ := h
            exact ⟨μ • b, by rw [smul_mul_assoc, hb, smul_mul_assoc]⟩
      obtain ⟨b, hb⟩ := key
      exact Submodule.mem_span_singleton.mpr ⟨b, Subtype.ext hb.symm⟩
    have hQ : ∀ d, d ≤ L → ∀ M₁ M₂ : Submodule A (D.Lx x),
        M₁ ≤ Submodule.span A {c (L - d)} → M₂ ≤ Submodule.span A {c (L - d)} →
          M₁ ≤ M₂ ∨ M₂ ≤ M₁ := by
      intro d
      induction d with
      | zero =>
          intro _
          refine chain_step hadm hspan (pv_hv x _) (S := ⊥) (fun r hr ↦ ?_) ?_
          · rw [Submodule.mem_bot]
            apply Subtype.ext
            show r * D.pval x ((Pm hadm a).take (L - 0)) = 0
            rw [Nat.sub_zero, List.take_length]
            exact rad_mul_top hadm hr
          · intro M₁ M₂ h₁ h₂
            left; rw [le_bot_iff.mp h₁]; exact bot_le
      | succ d ih =>
          intro hd
          have hm : L - (d + 1) + 1 = L - d := by omega
          refine chain_step hadm hspan (pv_hv x _) (S := Submodule.span A {c (L - d)})
            (fun r hr ↦ ?_) (ih (by omega))
          have := hR (L - (d + 1)) (by omega) r hr
          rwa [hm] at this
    have h0 := hQ L le_rfl N₁ N₂
    simp only [Nat.sub_self, List.take_zero] at h0
    exact h0 (htop N₁) (htop N₂)
  · push Not at ha
    refine chain_step hadm hspan (pv_hv x []) (S := ⊥) (fun r hr ↦ ?_) ?_ N₁ N₂ (htop N₁)
      (htop N₂)
    · rw [Submodule.mem_bot]
      exact Subtype.ext (rad_mul_e_of_none ha hr)
    · intro M₁ M₂ h₁ _
      left; rw [le_bot_iff.mp h₁]; exact bot_le

include hspan in
theorem mul_top_mem (c : A) (x : Q.V) (a : Q.A) :
    c * D.pval x (Pm hadm a) ∈ Submodule.span k {D.pval x (Pm hadm a)} := by
  obtain ⟨cv, r, hr, rfl⟩ := decompA hspan c
  rw [add_mul, esum_mul_pval, rad_mul_top hadm hr, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

include hsb in
/-- At a non-binomial vertex, the coefficient of a longest path is determined. -/
theorem top_coeff {x : Q.V} (hnb : ¬ Bin (k := k) hadm x) {a : Q.A} (ha : Q.src a = x)
    (T : Finset (List Q.A)) (hT : ∀ l ∈ T, l ≠ []) (g : List Q.A → k) (g0 : k)
    (h : g0 • D.pval x (Pm hadm a) +
      ∑ l ∈ T, g l • (D.pval x (Pm hadm a) * D.pval x l) = 0) : g0 = 0 := by
  classical
  set u := D.pval x (Pm hadm a)
  set S := T.filter (fun l ↦ u * D.pval x l ≠ 0)
  have hprod : ∀ l ∈ S, u * D.pval x l = D.pval x (l ++ Pm hadm a) := by
    intro l hl
    have h1 := (Finset.mem_filter.mp hl).2
    rw [D.pval_mul_pval] at h1 ⊢
    split_ifs at h1 ⊢ with h2
    · rfl
    · exact absurd rfl h1
  let f : List Q.A → List Q.A := fun l ↦ l ++ Pm hadm a
  have hf : Set.InjOn f S := fun l _ l' _ h ↦ List.append_cancel_right h
  have hnot : Pm hadm a ∉ S.image f := by
    intro hm
    obtain ⟨l, hl, hl'⟩ := Finset.mem_image.mp hm
    have := congrArg List.length hl'
    simp only [f, List.length_append] at this
    have := List.length_pos_iff.mpr (hT l (Finset.mem_filter.mp hl).1)
    omega
  let G : List Q.A → k := fun l' ↦
    if l' = Pm hadm a then g0 else if hl : ∃ l ∈ S, f l = l' then g hl.choose else 0
  have hG : ∀ l ∈ S, G (f l) = g l := by
    intro l hl
    have hne : f l ≠ Pm hadm a := fun h ↦ hnot (Finset.mem_image.mpr ⟨l, hl, h⟩)
    have hex : ∃ l₂ ∈ S, f l₂ = f l := ⟨l, hl, rfl⟩
    simp only [G, if_neg hne, dif_pos hex]
    congr 1
    exact hf hex.choose_spec.1 hl hex.choose_spec.2
  have hsum : ∑ l' ∈ insert (Pm hadm a) (S.image f), G l' • D.pval x l' = 0 := by
    rw [Finset.sum_insert hnot, Finset.sum_image hf]
    have e1 : ∑ l ∈ T, g l • (u * D.pval x l) = ∑ l ∈ S, g l • (u * D.pval x l) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      split_ifs with h3
      · rfl
      · push Not at h3; rw [h3, smul_zero]
    rw [e1] at h
    rw [← h]
    simp only [G, if_pos rfl]
    congr 1
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    change G (f l) • D.pval x (f l) = _
    rw [hG l hl, hprod l hl]
  have hz := coeff_eq_zero hadm hsb (insert (Pm hadm a) (S.image f)) G (x := x)
    (fun l hl ↦ by
      refine ⟨?_, fun hb ↦ absurd hb hnb⟩
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact pval_Pm_ne hadm hsb ha
      · obtain ⟨l₁, hl₁, rfl⟩ := Finset.mem_image.mp hl
        rw [← hprod l₁ hl₁]
        exact (Finset.mem_filter.mp hl₁).2)
    (fun y σ _ ↦ by rw [hsum, mul_zero])
    (by rw [hsum]; exact Submodule.zero_mem _) (fun _ ↦ hsum)
  have := hz (Pm hadm a) (Finset.mem_insert_self _ _)
  simpa [G] using this

include hsb hspan in
/-- **Two arrows without a binomial relation**: `A e_x` is not injective. -/
theorem not_injective {x : Q.V} (hnb : ¬ Bin (k := k) hadm x) {a b : Q.A} (hab : a ≠ b)
    (ha : Q.src a = x) (hb : Q.src b = x) : ¬ Module.Injective A (D.Lx x) := by
  classical
  intro hinj
  set u := D.pval x (Pm hadm a)
  set v := D.pval x (Pm hadm b)
  set U := Submodule.span A {D.pv x (Pm hadm a)}
  set V := Submodule.span A {D.pv x (Pm hadm b)}
  have hsc : ∀ (c : Q.A) (s : D.Lx x), s ∈ Submodule.span A {D.pv x (Pm hadm c)} →
      ∃ μ : k, s.1 = μ • D.pval x (Pm hadm c) := by
    intro c s hs
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hs
    exact Submodule.mem_span_singleton.mp (mul_top_mem hadm hspan d x c) |>.imp fun μ h ↦ h.symm
  have hindep : ∀ μ ν : k, μ • u + ν • v = 0 → μ = 0 ∧ ν = 0 := by
    intro μ ν h
    by_cases hν : ν = 0
    · subst hν
      rw [zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right (pval_Pm_ne hadm hsb ha), rfl⟩
    · exfalso
      apply hnb
      refine ⟨b, a, Ne.symm hab, hb, ha, Submodule.mem_span_singleton.mpr ⟨-(ν⁻¹ * μ), ?_⟩⟩
      have e : μ • u = -(ν • v) := eq_neg_of_add_eq_zero_left h
      rw [neg_smul, mul_smul, e, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hν, one_smul]
  let i : U × V →ₗ[A] D.Lx x := U.subtype.coprod V.subtype
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t⟩ hst
    obtain ⟨μ, hμ⟩ := hsc a s s.2
    obtain ⟨ν, hν⟩ := hsc b t t.2
    have h1 : μ • u + ν • v = 0 := by
      rw [← hμ, ← hν]; exact congrArg Subtype.val hst
    obtain ⟨rfl, rfl⟩ := hindep μ ν h1
    ext
    · show (s : D.Lx x).1 = 0; rw [hμ, zero_smul]
    · show (t : D.Lx x).1 = 0; rw [hν, zero_smul]
  obtain ⟨h, hh⟩ := hinj.out i hi (U.subtype ∘ₗ LinearMap.fst A U V)
  have hu1 : h (D.pv x (Pm hadm a)) = D.pv x (Pm hadm a) := by
    have := hh (⟨_, Submodule.mem_span_singleton_self _⟩, 0)
    simpa [i] using this
  have hv1 : h (D.pv x (Pm hadm b)) = 0 := by
    have := hh (0, ⟨_, Submodule.mem_span_singleton_self _⟩)
    simpa [i] using this
  set t := (h (D.pv x [])).1
  have ht : ∀ w : D.Lx x, (h w).1 = w.1 * t := by
    intro w
    have hw : w = w.1 • D.pv x [] := Subtype.ext (by
      show w.1 = w.1 * D.e x; exact w.2.symm)
    conv_lhs => rw [hw]
    rw [map_smul]; rfl
  have hu : u * t = u := by
    have := ht (D.pv x (Pm hadm a)); rw [hu1] at this; exact this.symm
  have hv : v * t = 0 := by
    have := ht (D.pv x (Pm hadm b)); rw [hv1] at this; exact this.symm
  have hte : t * D.e x = t := (h (D.pv x [])).2
  obtain ⟨T, g, -, htT⟩ := exists_rep hspan hte
  set g0 : k := if [] ∈ T then g [] else 0
  have hexp : ∀ w : A, w * D.e x = w →
      w * t = g0 • w + ∑ l ∈ T.erase [], g l • (w * D.pval x l) := by
    intro w hw
    rw [htT, Finset.mul_sum]
    by_cases h0 : [] ∈ T
    · rw [← Finset.add_sum_erase T _ h0]
      simp only [g0, if_pos h0, mul_smul_comm]
      congr 1
      show g [] • (w * D.e x) = _
      rw [hw]
    · rw [Finset.erase_eq_of_notMem h0]
      simp only [g0, if_neg h0, zero_smul, zero_add, mul_smul_comm]
  have hne : ∀ l ∈ T.erase [], l ≠ [] := fun l hl ↦ Finset.ne_of_mem_erase hl
  have h1 : (g0 - 1) = 0 := by
    refine top_coeff hadm hsb hnb ha (T.erase []) hne g (g0 - 1) ?_
    have := hexp u (D.pval_mul_e x _)
    rw [hu] at this
    rw [sub_smul, one_smul, sub_add_eq_add_sub, ← this, sub_self]
  have h2 : g0 = 0 := by
    refine top_coeff hadm hsb hnb hb (T.erase []) hne g g0 ?_
    have := hexp v (D.pval_mul_e x _)
    rw [hv] at this
    exact this.symm
  rw [h2, zero_sub] at h1
  exact one_ne_zero (neg_eq_zero.mp h1)

theorem zz_mem_lx (x : Q.V) : zz (k := k) hadm x ∈ D.Lx x := by
  show zz (k := k) hadm x * D.e x = zz (k := k) hadm x
  rw [zz_mul_e, if_pos rfl]

/-- `zz x` as an element of `A e_x`. -/
def zL (x : Q.V) : D.Lx x := ⟨zz (k := k) hadm x, zz_mem_lx hadm x⟩

include hsb hspan in
/-- **The socle of `A e_x`** at a binomial vertex is the line of the longest path. -/
theorem soc_eq {x : Q.V} (hb : Bin (k := k) hadm x) :
    soc A (D.Lx x) = Submodule.span A {zL (k := k) hadm x} := by
  classical
  obtain ⟨a0, -, -, ha0, -, -, hz⟩ := zz_spec hadm hb
  have hz0 : zz (k := k) hadm x ≠ 0 := by rw [hz]; exact pval_Pm_ne hadm hsb ha0
  set Z := Submodule.span A {zL (k := k) hadm x}
  have hZ0 : Z ≠ ⊥ := by
    intro h
    have : zL (k := k) hadm x ∈ Z := Submodule.mem_span_singleton_self _
    rw [h, Submodule.mem_bot] at this
    exact hz0 (congrArg Subtype.val this)
  have hcont : ∀ N : Submodule A (D.Lx x), N ≠ ⊥ → Z ≤ N := by
    intro N hN
    obtain ⟨n, hnN, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    obtain ⟨c, hc⟩ := socle hadm hsb hspan hb ha0 n.2 (fun h ↦ hn0 (Subtype.ext h))
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have : c • n = zL (k := k) hadm x := Subtype.ext (by rw [← hz] at hc; exact hc)
    rw [← this]; exact N.smul_mem c hnN
  have hatom : IsAtom Z := ⟨hZ0, fun N hN ↦ by
    by_contra h
    exact (not_le_of_gt hN) (hcont N h)⟩
  apply le_antisymm
  · refine sSup_le fun N hN ↦ ?_
    have hNa : IsAtom N := isSimpleModule_iff_isAtom.mp hN
    have := hcont N hNa.1
    exact ((hNa.le_iff.mp this).resolve_left hZ0).ge
  · exact le_sSup (isSimpleModule_iff_isAtom.mpr hatom)

include hsb hspan in
/-- **Binomial vertices** are exactly those with `A e_x` nonuniserial and injective. -/
theorem bin_iff [FiniteDimensional k A] (hind : D.ArrInd (k := k)) (x : Q.V) :
    Bin (k := k) hadm x ↔ ¬ IsUniserialMod A (D.Lx x) ∧ Module.Injective A (D.Lx x) := by
  constructor
  · intro hb
    obtain ⟨a, b, hab, ha, hb', -, hz⟩ := zz_spec hadm hb
    refine ⟨not_uniserial hspan hind hab ha hb', ?_⟩
    obtain ⟨y, hyz, S2⟩ := socle_op hadm hsb hspan hb
    exact D.injective_of_socles (k := k) (by rw [zz_mul_e, if_pos rfl]) hyz
      (by rw [hz]; exact pval_Pm_ne hadm hsb ha)
      (fun w hw hw0 ↦ by
        obtain ⟨c, hc⟩ := socle hadm hsb hspan hb ha hw hw0
        exact ⟨c, hc.trans hz.symm⟩) S2
  · rintro ⟨hnu, hinj⟩
    by_contra hnb
    by_cases two : ∃ a b, a ≠ b ∧ Q.src a = x ∧ Q.src b = x
    · obtain ⟨a, b, hab, ha, hb⟩ := two
      exact not_injective hadm hsb hspan hnb hab ha hb hinj
    · push Not at two
      exact hnu (uniserial_of_one hadm hsb hspan fun a b ha hb ↦
        by_contra fun h ↦ (two a b h ha) hb)

variable (D) in
/-- **The paper's ideal**: the sum of the socles of the nonuniserial injective `A e_x`. -/
def socIdeal : Ideal A :=
  ⨆ (x : Q.V) (_ : ¬ IsUniserialMod A (D.Lx x) ∧ Module.Injective A (D.Lx x)),
    (soc A (D.Lx x)).map (D.Lx x).subtype

include hsb hspan in
/-- The socle sum is the ideal of `exists_string_quotient`. -/
theorem socIdeal_eq [FiniteDimensional k A] (hind : D.ArrInd (k := k)) :
    socIdeal D = JI (k := k) hadm hspan := by
  classical
  have hmap : ∀ x, Bin (k := k) hadm x →
      (soc A (D.Lx x)).map (D.Lx x).subtype = Submodule.span A {zz (k := k) hadm x} := by
    intro x hb
    rw [soc_eq hadm hsb hspan hb, Submodule.map_span, Set.image_singleton]
    rfl
  apply le_antisymm
  · refine iSup₂_le fun x hx ↦ ?_
    rw [hmap x ((bin_iff hadm hsb hspan hind x).mpr hx), Submodule.span_le,
      Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨x, rfl⟩
  · intro w hw
    have hw' : w ∈ Jsp (k := k) hadm := hw
    have hle : Jsp (k := k) hadm ≤ (socIdeal D).restrictScalars k := by
      rw [Jsp, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      by_cases hb : Bin (k := k) hadm x
      · have hx := (bin_iff hadm hsb hspan hind x).mp hb
        have : zz (k := k) hadm x ∈ (soc A (D.Lx x)).map (D.Lx x).subtype := by
          rw [hmap x hb]; exact Submodule.mem_span_singleton_self _
        exact (le_iSup₂ (f := fun x (_ : ¬ IsUniserialMod A (D.Lx x) ∧
          Module.Injective A (D.Lx x)) ↦ (soc A (D.Lx x)).map (D.Lx x).subtype) x hx) this
      · rw [zz_of_not hadm hb]; exact Submodule.zero_mem _
    exact hle hw'

include hadm hsb hspan in
/-- **Lemma 5.3**, exact form: the socle sum `J` of the nonuniserial injective summands is a
two-sided ideal with string quotient, and every indecomposable module not annihilated by `J`
is a nonuniserial projective-injective module. -/
theorem string_quotient_exact [FiniteDimensional k A] (hind : D.ArrInd (k := k)) :
    ∃ (_ : (socIdeal D).IsTwoSided) (D' : MonomialData k (A ⧸ socIdeal D)),
      D'.IsStringAlgebra ∧
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
        [FiniteDimensional k M], IsIndecomposable A M →
          ¬ Module.IsTorsionBySet A M (socIdeal D) →
            Module.Projective A M ∧ Module.Injective A M ∧ ¬ IsUniserialMod A M := by
  classical
  rw [socIdeal_eq hadm hsb hspan hind]
  have := JI_isTwoSided (k := k) hadm hsb hspan
  refine ⟨inferInstance, quotData hadm hsb hspan, quotData_isString hadm hsb hspan, ?_⟩
  intro M _ _ _ _ _ hM hJ
  obtain ⟨x, m, hxm⟩ : ∃ (x : Q.V) (m : M), zz (k := k) hadm x • m ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hJ
    intro m j
    obtain ⟨j, hj⟩ := j
    change j ∈ Jsp (k := k) hadm at hj
    show j • m = 0
    induction hj using Submodule.span_induction with
    | mem j hj => obtain ⟨x, rfl⟩ := hj; exact hno x m
    | zero => rw [zero_smul]
    | add j j' _ _ h h' => rw [add_smul, h, h', add_zero]
    | smul μ j _ h => rw [smul_assoc, h, smul_zero]
  have hb : Bin (k := k) hadm x := by
    by_contra hb
    rw [zz_of_not hadm hb, zero_smul] at hxm
    exact hxm rfl
  obtain ⟨a, -, -, hxa, -, -, hz⟩ := zz_spec hadm hb
  obtain ⟨y, hyz, S2⟩ := socle_op hadm hsb hspan hb
  obtain ⟨e⟩ := D.equiv_of_socles (k := k) (by rw [zz_mul_e, if_pos rfl]) hyz
    (by rw [hz]; exact pval_Pm_ne hadm hsb hxa)
    (fun w hw hw0 ↦ by
      obtain ⟨c, hc⟩ := socle hadm hsb hspan hb hxa hw hw0
      exact ⟨c, hc.trans hz.symm⟩) S2 M hM hxm
  obtain ⟨hnu, hinj⟩ := (bin_iff hadm hsb hspan hind x).mp hb
  have := D.lx_projective x
  refine ⟨Module.Projective.of_equiv e,
    Module.Baer.injective (Module.Baer.of_equiv e (Module.Baer.of_injective hinj)),
    fun hu ↦ hnu fun N₁ N₂ ↦ ?_⟩
  rcases hu (N₁.map e.toLinearMap) (N₂.map e.toLinearMap) with h | h
  · left; exact (Submodule.map_le_map_iff_of_injective e.injective _ _).mp h
  · right; exact (Submodule.map_le_map_iff_of_injective e.injective _ _).mp h

end PathData

end BrickAccessibility
