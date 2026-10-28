module

public import BrickAccessibility.Classification.StringShift
public import BrickAccessibility.Section3.Walks

/-!
# Realization of finite pairs by strings

If the pair functor of finite half-words `h = L` (sign `s`) and `h' = L'`
(sign `!s`) at `v` is nonzero on a module `M`, then the word `L'⁻¹ L` is a
string (`joinWord_isString`): its signs alternate, and a chain family through a
vector of `num \ den` shows that no walk spells a zero path. The pair is the
pair of halves at position `|L'|` of this string.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem invLetters_invLetters {Q : FinQuiver} (L : List (Letter Q)) :
    invLetters (invLetters L) = L := by
  simp [invLetters, List.map_reverse, Function.comp_def, Letter.inv_inv']

@[simp] theorem length_invLetters {Q : FinQuiver} (L : List (Letter Q)) :
    (invLetters L).length = L.length := by simp [invLetters]

namespace MonomialData

variable {D : MonomialData k B}
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

theorem rel_vsp {l : Letter D.Q} {x y : M} (h : Rel l x y) :
    x ∈ D.vsp M l.src ∧ y ∈ D.vsp M l.tgt := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [Rel, Bool.false_eq_true, if_false] at h
    obtain ⟨hy, rfl⟩ := h
    exact ⟨D.α_smul_mem_vsp a y, hy⟩
  · simp only [Rel, if_true] at h
    obtain ⟨hx, rfl⟩ := h
    exact ⟨hx, D.α_smul_mem_vsp a x⟩

variable (S : Signs D)

/-- Sign alternation along a list of letters. -/
def Signs.Alt (L : List (Letter D.Q)) : Prop := L.IsChain fun l l' ↦ S.st l' ≠ S.en l

theorem Signs.IsHW.alt {v : D.Q.V} {s : Bool} {L : List (Letter D.Q)} (h : S.IsHW v s L) :
    S.Alt L := by
  rw [Signs.Alt, List.isChain_iff_getElem]
  intro i hi
  have := h.2 (i + 1) hi
  rw [List.take_succ_eq_append_getElem (by omega), Signs.nsign_append_singleton] at this
  rw [this]; simp

theorem Signs.alt_invLetters {L : List (Letter D.Q)} (h : S.Alt L) : S.Alt (invLetters L) := by
  rw [Signs.Alt, invLetters, List.isChain_reverse, List.isChain_map]
  refine h.imp fun a b hab ↦ ?_
  simp only [flip, Signs.st_inv, Signs.en_inv]
  exact Ne.symm hab

theorem Signs.minus_fin_of_chain_zero {v : D.Q.V} {s : Bool} {L : List (Letter D.Q)} {x : M}
    (c : ℕ → M) (hc0 : c 0 = x) (hc : ∀ (i : ℕ) (hi : i < L.length), Rel L[i] (c i) (c (i + 1)))
    {n : ℕ} (hn : n ≤ L.length) (hcn : c n = 0) : x ∈ S.minus M v s (.fin L) := by
  have h1 : x ∈ D.trs (L.take n) (⊥ : Submodule k M) := by
    refine (mem_trs_iff _ _ _).mpr ⟨c, hc0, fun i hi ↦ ?_, ?_⟩
    · simp only [List.length_take] at hi
      have := hc i (by omega)
      simpa using this
    · simp only [List.length_take, min_eq_left hn, hcn]; exact Submodule.zero_mem _
  change x ∈ D.trs L _
  rw [← List.take_append_drop n L, D.trs_append]
  exact D.trs_mono _ bot_le h1

end MonomialData

namespace Word

variable {D : MonomialData k B}

/-- The word `L'⁻¹ L` through `v`. -/
def join (v : D.Q.V) (L L' : List (Letter D.Q)) (hL : D.Q.IsWalk v L)
    (hL' : D.Q.IsWalk v L') : Word D.Q where
  start := D.Q.wend v L'
  letters := invLetters L' ++ L
  walk := by
    rw [Statement.FinQuiver.isWalk_append]
    obtain ⟨h1, h2⟩ := Statement.FinQuiver.isWalk_inv v L' hL'
    exact ⟨h1, by rw [h2]; exact hL⟩

variable {v : D.Q.V} {L L' : List (Letter D.Q)} (hL : D.Q.IsWalk v L) (hL' : D.Q.IsWalk v L')

theorem join_len : (join v L L' hL hL').len = L'.length + L.length := by
  simp [join, len]

/-- The junction position. -/
def jpos : Fin ((join v L L' hL hL').len + 1) := ⟨L'.length, by rw [join_len]; omega⟩

theorem join_vtx_jpos : (join v L L' hL hL').vtx (jpos hL hL') = v := by
  simp only [vtx, jpos, join]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  exact (Statement.FinQuiver.isWalk_inv v L' hL').2

theorem join_right : (join v L L' hL hL').right (jpos hL hL') = L := by
  simp only [right, jpos, join]
  rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp)]
  simp

theorem join_left : (join v L L' hL hL').left (jpos hL hL') = L' := by
  simp only [left, jpos, join]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
    invLetters_invLetters]

variable (S : D.Signs) {s : Bool}

omit hL hL' in
theorem noForks_of_alt (w : Word D.Q) (h : S.Alt w.letters) : w.NoForks := by
  intro i hi ⟨h1, h2⟩
  have := (List.isChain_iff_getElem.mp h) i hi
  apply this
  generalize w.letters[i]'(by omega) = l at h1 h2 ⊢
  generalize w.letters[i + 1] = l' at h1 h2 ⊢
  obtain ⟨a, d⟩ := l
  obtain ⟨b, e⟩ := l'
  simp only at h1 h2
  subst h1
  cases d <;> cases e <;> simp_all

theorem join_alt (h1 : S.IsHW v s L) (h2 : S.IsHW v (!s) L') :
    S.Alt (join v L L' hL hL').letters := by
  simp only [join, MonomialData.Signs.Alt]
  rw [List.isChain_append]
  refine ⟨S.alt_invLetters (MonomialData.Signs.IsHW.alt S h2), MonomialData.Signs.IsHW.alt S h1,
    fun x hx y hy ↦ ?_⟩
  cases L' with
  | nil => simp [invLetters] at hx
  | cons l' L'' =>
      cases L with
      | nil => simp at hy
      | cons l L₀ =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          have hgl : (invLetters (l' :: L'')).getLast? = some l'.inv := by
            simp [invLetters]
          rw [hgl, Option.mem_def, Option.some.injEq] at hx
          subst hx; subst hy
          have hs1 := h1.2 0 (by simp)
          have hs2 := h2.2 0 (by simp)
          simp only [List.getElem_cons_zero, List.take_zero, MonomialData.Signs.nsign_nil] at hs1 hs2
          rw [MonomialData.Signs.en_inv, hs1, hs2]
          simp

theorem join_noForks (h1 : S.IsHW v s L) (h2 : S.IsHW v (!s) L') :
    (join v L L' hL hL').NoForks :=
  noForks_of_alt S _ (join_alt hL hL' S h1 h2)

variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

omit hL hL' in
/-- Along a word, a family related along every letter transforms by path values along
directed walks. -/
theorem follow_rel (w : Word D.Q) (hw : w.NoForks) (c : Fin (w.len + 1) → M)
    (hrel : ∀ (q : ℕ) (hq : q < w.len),
      MonomialData.Rel w.letters[q] (c ⟨q, by simp only [Word.len] at *; omega⟩)
        (c ⟨q + 1, by simp only [Word.len] at *; omega⟩))
    (hvsp : ∀ q, c q ∈ D.vsp M (w.vtx q)) :
    ∀ (l : List D.Q.A) (i i' : Fin (w.len + 1)) (co : k),
      (w.coeffQuiver D).follow i l = some (i', co) → c i' = D.pval (w.vtx i) l • c i := by
  have hmove : ∀ a (i i' : Fin (w.len + 1)), w.next a i = some i' → c i' = D.α a • c i := by
    intro a i i' h
    rcases (w.next_eq_some_iff hw a i i').mp h with ⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩
    · have hr := hrel i.val hi
      rw [hl] at hr
      simp only [MonomialData.Rel, if_true] at hr
      have e : i' = ⟨i.val + 1, by simp only [Word.len] at *; omega⟩ := Fin.ext hj
      rw [e]; exact hr.2
    · have hr := hrel (i.val - 1) (by have := i.isLt; simp only [Word.len] at *; omega)
      rw [hl] at hr
      simp only [MonomialData.Rel, Bool.false_eq_true, if_false] at hr
      have e : i' = ⟨i.val - 1, by have := i.isLt; omega⟩ := Fin.ext hj
      have e' : (⟨i.val - 1 + 1, by have := i.isLt; simp only [Word.len] at *; omega⟩ :
          Fin (w.len + 1)) = i := Fin.ext (by simp; omega)
      rw [e'] at hr
      rw [e]; exact hr.2
  intro l
  induction l with
  | nil =>
      intro i i' co h
      have h' := Prod.mk.inj (Option.some.inj h)
      rw [← h'.1]
      exact ((D.mem_vsp).mp (hvsp i)).symm
  | cons a l ih =>
      intro i i' co h
      obtain ⟨j, co', hj, hf, -⟩ := ((w.coeffQuiver D).follow_cons_eq_some).mp h
      rw [ih j i' co' hf, hmove a i j hj]
      have hvj : w.vtx j = D.Q.tgt a := (w.coeffQuiver D).next_tgt a i j hj
      have hvi : w.vtx i = D.Q.src a := (w.coeffQuiver D).next_src a i j hj
      rw [hvj]
      change _ = (D.pval (D.Q.tgt a) l * D.α a * D.e (w.vtx i)) • c i
      rw [mul_smul, mul_smul, (D.mem_vsp).mp (hvsp i)]

/-- **Realization of finite pairs**: a nonzero pair functor of finite half-words comes from
a string. -/
theorem join_isString (h1 : S.IsHW v s L) (h2 : S.IsHW v (!s) L')
    (hne : ¬ S.pnum M v s (.fin L) (.fin L') ≤ S.pden M v s (.fin L) (.fin L')) :
    (join v L L' hL hL').IsString D := by
  classical
  set w := join v L L' hL hL'
  have hnf := join_noForks hL hL' S h1 h2
  refine ⟨hnf, ?_⟩
  obtain ⟨x, hxn, hxd⟩ := Set.not_subset.mp hne
  obtain ⟨cR, hR0, hR, -⟩ := (MonomialData.mem_trs_iff _ _ _).mp hxn.1
  obtain ⟨cL, hL0, hLc, -⟩ := (MonomialData.mem_trs_iff _ _ _).mp hxn.2
  have hlen : w.len = L'.length + L.length := join_len hL hL'
  let m := L'.length
  let c : Fin (w.len + 1) → M := fun q ↦ if m ≤ q.val then cR (q.val - m) else cL (m - q.val)
  have hletters : w.letters = invLetters L' ++ L := rfl
  have hrel : ∀ (q : ℕ) (hq : q < w.len),
      MonomialData.Rel w.letters[q] (c ⟨q, by omega⟩) (c ⟨q + 1, by omega⟩) := by
    intro q hq
    by_cases hmq : m ≤ q
    · have hget : w.letters[q] = L[q - m]'(by omega) := by
        simp only [hletters]
        rw [List.getElem_append_right (by simp; omega)]
        simp [m]
      rw [hget]
      simp only [c, if_pos hmq, if_pos (show m ≤ q + 1 by omega)]
      have e : q + 1 - m = q - m + 1 := by omega
      rw [e]; exact hR (q - m) (by omega)
    · have hget : w.letters[q] = (L'[m - 1 - q]'(by omega)).inv := by
        simp only [hletters]
        rw [List.getElem_append_left (by simp; omega)]
        simp only [invLetters, List.getElem_reverse, List.getElem_map, List.length_map]
        rfl
      rw [hget, MonomialData.rel_inv]
      simp only [c, if_neg hmq]
      have hr := hLc (m - 1 - q) (by omega)
      have e1 : m - 1 - q + 1 = m - q := by omega
      rw [e1] at hr
      by_cases hq1 : m ≤ q + 1
      · rw [if_pos hq1]
        have e2 : q + 1 - m = 0 := by omega
        have hxL : cL (m - 1 - q) = x := by rw [show m - 1 - q = 0 by omega, hL0]
        rw [e2, hR0]
        rw [hxL] at hr
        exact hr
      · rw [if_neg hq1]
        have e2 : m - (q + 1) = m - 1 - q := by omega
        rw [e2]; exact hr
  have hvsp : ∀ q, c q ∈ D.vsp M (w.vtx q) := by
    intro q
    by_cases hq : q.val < w.len
    · have := (MonomialData.rel_vsp (hrel q.val hq)).1
      rwa [w.src_letter q.val hq] at this
    · by_cases h0 : 0 < w.len
      · have := (MonomialData.rel_vsp (hrel (w.len - 1) (by omega))).2
        rw [w.tgt_letter (w.len - 1) (by omega)] at this
        have e : (⟨w.len - 1 + 1, by omega⟩ : Fin (w.len + 1)) = q := Fin.ext (by simp; omega)
        rwa [e] at this
      · have hq0 : q.val = 0 := by omega
        have hm0 : m = 0 := by omega
        have hx : c q = x := by
          simp only [c]
          rw [if_pos (show m ≤ q.val by omega), show q.val - m = 0 by omega, hR0]
        rw [hx]
        have : w.vtx q = v := by
          have hm0' : L'.length = 0 := hm0
          have e : q = jpos hL hL' := Fin.ext (by simp only [jpos]; rw [hq0, hm0'])
          rw [e]; exact join_vtx_jpos hL hL'
        rw [this]
        exact S.plus_le_vsp (h := HWord.fin L) h1 hxn.1
  intro x' l hz i hi
  by_contra hf
  obtain ⟨⟨i', co⟩, hf⟩ := Option.ne_none_iff_exists'.mp hf
  have hc := follow_rel M w hnf c hrel hvsp l i i' co hf
  have hi' : w.vtx i = x' := hi
  rw [hi', hz, zero_smul] at hc
  apply hxd
  by_cases hmi : m ≤ i'.val
  · have h0 : cR (i'.val - m) = 0 := by simpa [c, if_pos hmi] using hc
    exact Submodule.mem_sup_left ⟨S.minus_fin_of_chain_zero cR hR0 hR (by omega) h0, hxn.2⟩
  · have h0 : cL (m - i'.val) = 0 := by simpa [c, if_neg hmi] using hc
    exact Submodule.mem_sup_right ⟨hxn.1, S.minus_fin_of_chain_zero cL hL0 hLc (by omega) h0⟩

theorem join_half (h1 : S.IsHW v s L) (h2 : S.IsHW v (!s) L') :
    (join v L L' hL hL').half S (jpos hL hL') s = L ∧
      (join v L L' hL hL').half S (jpos hL hL') (!s) = L' := by
  have hside : L ≠ [] ∨ L' ≠ [] → (join v L L' hL hL').sideSign S (jpos hL hL') = s := by
    intro hne
    cases L with
    | cons l L₀ =>
        have hs1 := h1.2 0 (by simp)
        simp only [List.getElem_cons_zero, List.take_zero, MonomialData.Signs.nsign_nil] at hs1
        unfold sideSign
        have hlt : (jpos hL hL').val < (join v (l :: L₀) L' hL hL').len := by
          simp [jpos, join_len]
        rw [dif_pos hlt]
        have : (join v (l :: L₀) L' hL hL').letters[(jpos hL hL').val] = l := by
          simp only [join, jpos]
          rw [List.getElem_append_right (by simp)]
          simp
        rw [this, hs1]
    | nil =>
        have hL'ne : L' ≠ [] := by simpa using hne
        obtain ⟨l', L'', rfl⟩ := List.exists_cons_of_ne_nil hL'ne
        have hs2 := h2.2 0 (by simp)
        simp only [List.getElem_cons_zero, List.take_zero, MonomialData.Signs.nsign_nil] at hs2
        unfold sideSign
        have hn : ¬ (jpos hL hL').val < (join v [] (l' :: L'') hL hL').len := by
          simp [jpos, join_len]
        rw [dif_neg hn, dif_pos (by simp [join_len])]
        have : (join v [] (l' :: L'') hL hL').letters[(join v [] (l' :: L'') hL hL').len - 1]'(by
            simp [join_len]) = l'.inv := by
          simp only [join, List.append_nil]
          rw [List.getElem_eq_iff, List.getElem?_eq_getElem (by simp [join_len, len])]
          simp [invLetters, join_len, len]
        rw [this, MonomialData.Signs.en_inv, hs2]
        simp
  by_cases hne : L ≠ [] ∨ L' ≠ []
  · have hs := hside hne
    unfold half
    rw [if_pos hs.symm, if_neg (by rw [hs]; simp), join_right, join_left]
    exact ⟨rfl, rfl⟩
  · push Not at hne
    obtain ⟨rfl, rfl⟩ := hne
    unfold half
    have e1 := join_right (L := []) (L' := []) hL hL'
    have e2 := join_left (L := []) (L' := []) hL hL'
    constructor <;> split_ifs <;> simp_all

end Word

end BrickAccessibility
