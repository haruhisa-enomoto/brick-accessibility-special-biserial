module

public import BrickAccessibility.Classification.HalfWords

/-!
# Finite and infinite half-words

A half-word is finite (`fin C`) or infinite (`inf f`). Its code at position `i`
is `0` for an inverse letter, `2` for a direct letter and `1` past the end; the
lexicographic order of codes orders the half-words at `(v, s)`
(`inverse continuation < end < direct continuation`). Valid half-words at
`(v, s)` are determined by their codes (`code_injective`).

For an infinite half-word, `C⁺ = ⨅ₙ (C_{<n})^* M` and `C⁻ = ⨆ₙ (C_{<n})^* 0`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- A half-word: finite or infinite. -/
inductive HWord (Q : FinQuiver) where
  | fin (C : List (Letter Q))
  | inf (f : ℕ → Letter Q)

namespace HWord

variable {Q : FinQuiver}

/-- The prefix of length `n` (or the whole word, if shorter). -/
def pre : HWord Q → ℕ → List (Letter Q)
  | fin C, n => C.take n
  | inf f, n => List.ofFn fun i : Fin n ↦ f i

/-- The direction code at position `i`. -/
def code : HWord Q → ℕ → ℕ
  | fin C, i => if h : i < C.length then (if C[i].2 then 2 else 0) else 1
  | inf f, i => if (f i).2 then 2 else 0

theorem code_le_two (h : HWord Q) (i : ℕ) : h.code i ≤ 2 := by
  cases h <;> simp only [code] <;> split_ifs <;> omega

theorem pre_succ_of_code_ne (h : HWord Q) {i : ℕ} (hi : h.code i ≠ 1) :
    ∃ l : Letter Q, h.pre (i + 1) = h.pre i ++ [l] ∧ (h.code i = 2 ↔ l.2 = true) := by
  cases h with
  | fin C =>
      by_cases h1 : i < C.length
      · exact ⟨C[i], List.take_succ_eq_append_getElem h1, by simp [code, h1]⟩
      · simp [code, h1] at hi
  | inf f =>
      refine ⟨f i, List.ofFn_succ_last, ?_⟩
      simp only [code]; split_ifs with h <;> simp [h]

theorem eq_fin_of_code_eq_one (h : HWord Q) {i : ℕ} (hi : h.code i = 1) : h = fin (h.pre i) := by
  cases h with
  | fin C =>
      by_cases h1 : i < C.length
      · simp only [code, h1, dite_true] at hi; split_ifs at hi <;> omega
      · simp only [pre, fin.injEq]
        exact (List.take_of_length_le (by omega)).symm
  | inf f => simp only [code] at hi; split_ifs at hi <;> omega

theorem pre_succ_of_code_eq_one (h : HWord Q) {i : ℕ} (hi : h.code i = 1) :
    h.pre (i + 1) = h.pre i := by
  cases h with
  | fin C =>
      by_cases h1 : i < C.length
      · simp only [code, h1, dite_true] at hi; split_ifs at hi <;> omega
      · simp only [pre]
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  | inf f => simp only [code] at hi; split_ifs at hi <;> omega

theorem pre_length_of_code_ne (h : HWord Q) {i : ℕ} (hi : ∀ j < i, h.code j ≠ 1) :
    (h.pre i).length = i := by
  cases h with
  | fin C =>
      simp only [pre, List.length_take]
      by_contra hne
      have hlt : C.length < i := by omega
      have := hi C.length hlt
      simp [code] at this
  | inf f => simp [pre]

end HWord

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)

/-- Validity of a half-word at `(v, s)`. -/
def Signs.Valid (v : D.Q.V) (s : Bool) : HWord D.Q → Prop
  | .fin C => S.IsHW v s C
  | .inf f => ∀ n, S.IsHW v s (List.ofFn fun i : Fin n ↦ f i)

theorem Signs.Valid.pre {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) (n : ℕ) :
    S.IsHW v s (h.pre n) := by
  cases h with
  | fin C => exact Signs.IsHW.take S hv n
  | inf f => exact hv n

theorem Signs.IsHW.last {v : D.Q.V} {s : Bool} {E : List (Letter D.Q)} {l : Letter D.Q}
    (h : S.IsHW v s (E ++ [l])) : l.src = D.Q.wend v E ∧ S.st l = S.nsign s E := by
  refine ⟨?_, ?_⟩
  · have := h.1
    rw [Statement.FinQuiver.isWalk_append] at this
    exact this.2.1
  · have := h.2 E.length (by simp)
    simpa using this

/-- Valid half-words with the same codes below `i` have the same prefix of length `i`. -/
theorem Signs.pre_eq_of_code_eq {v : D.Q.V} {s : Bool} {h h' : HWord D.Q}
    (hv : S.Valid v s h) (hv' : S.Valid v s h') :
    ∀ i, (∀ j < i, h.code j = h'.code j) → h.pre i = h'.pre i := by
  intro i
  induction i with
  | zero => intro _; cases h <;> cases h' <;> rfl
  | succ i ih =>
      intro hc
      have hpre := ih fun j hj ↦ hc j (by omega)
      by_cases h1 : h.code i = 1
      · have h1' : h'.code i = 1 := (hc i (by omega)).symm.trans h1
        rw [h.pre_succ_of_code_eq_one h1, h'.pre_succ_of_code_eq_one h1', hpre]
      · have h1' : h'.code i ≠ 1 := fun e ↦ h1 ((hc i (by omega)).trans e)
        obtain ⟨l, hl, hld⟩ := h.pre_succ_of_code_ne h1
        obtain ⟨l', hl', hld'⟩ := h'.pre_succ_of_code_ne h1'
        rw [hl, hl', hpre]
        congr 1
        have e1 := Signs.IsHW.last S (hl ▸ hv.pre S (i + 1))
        have e2 := Signs.IsHW.last S (hl' ▸ hv'.pre S (i + 1))
        rw [hpre] at e1
        have hdir : l.2 = l'.2 := by
          have hci := hc i (by omega)
          have b1 := h.code_le_two i
          by_cases h2 : h.code i = 2
          · rw [(hld.mp h2), (hld'.mp (hci ▸ h2))]
          · have hl2 : l.2 = false := by
              cases hb : l.2
              · rfl
              · exact absurd (hld.mpr hb) h2
            have hl2' : l'.2 = false := by
              cases hb : l'.2
              · rfl
              · exact absurd (hci ▸ hld'.mpr hb) h2
            rw [hl2, hl2']
        rw [S.letter_eq (e1.1.trans e2.1.symm) hdir (e1.2.trans e2.2.symm)]

/-- Valid half-words at `(v, s)` are determined by their codes. -/
theorem Signs.code_injective {v : D.Q.V} {s : Bool} {h h' : HWord D.Q}
    (hv : S.Valid v s h) (hv' : S.Valid v s h') (hc : h.code = h'.code) : h = h' := by
  have hpre : ∀ i, h.pre i = h'.pre i := fun i ↦ S.pre_eq_of_code_eq hv hv' i fun j _ ↦ by rw [hc]
  cases h with
  | fin C =>
      have h1 : (HWord.fin C).code C.length = 1 := by simp [HWord.code]
      rw [hc] at h1
      rw [h'.eq_fin_of_code_eq_one h1, ← hpre]
      simp [HWord.pre]
  | inf f =>
      cases h' with
      | fin C' =>
          have h1 : (HWord.fin C').code C'.length = 1 := by simp [HWord.code]
          rw [← hc] at h1
          simp only [HWord.code] at h1
          split_ifs at h1 <;> omega
      | inf f' =>
          congr 1
          funext i
          have := congrArg (fun L : List (Letter D.Q) ↦ L[i]?) (hpre (i + 1))
          simp only [HWord.pre, List.getElem?_ofFn] at this
          simpa using this

/-! ### Boundary subspaces of half-words -/

variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

variable (M) in
/-- `C⁺` of a half-word. -/
def Signs.plus (v : D.Q.V) (s : Bool) : HWord D.Q → Submodule k M
  | .fin C => S.plusF M v s C
  | .inf f => ⨅ n, D.trs (List.ofFn fun i : Fin n ↦ f i)
      (D.vsp M (D.Q.wend v (List.ofFn fun i : Fin n ↦ f i)))

variable (M) in
/-- `C⁻` of a half-word. -/
def Signs.minus (v : D.Q.V) (s : Bool) : HWord D.Q → Submodule k M
  | .fin C => S.minusF M v s C
  | .inf f => ⨆ n, D.trs (List.ofFn fun i : Fin n ↦ f i) ⊥

theorem trs_le_vsp_wend {v : D.Q.V} {C : List (Letter D.Q)} (hC : D.Q.IsWalk v C)
    {U : Submodule k M} (hU : U ≤ D.vsp M (D.Q.wend v C)) : D.trs C U ≤ D.vsp M v := by
  cases C with
  | nil => exact hU
  | cons l C => exact (D.trs_le_vsp l C _).trans (by rw [hC.1])

/-- Bounds of `C⁺`, `C⁻` by a prefix ending with an actual letter. -/
theorem Signs.plus_le_pre {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) {i : ℕ}
    {l : Letter D.Q} (hl : h.pre (i + 1) = h.pre i ++ [l]) :
    S.plus M v s h ≤ D.trs (h.pre i ++ [l]) (D.vsp M l.tgt) ∧
      D.trs (h.pre i ++ [l]) ⊥ ≤ S.minus M v s h := by
  cases h with
  | fin C =>
      have hlen : i < C.length := by
        by_contra hc
        have : (HWord.fin C).pre (i + 1) = (HWord.fin C).pre i := by
          simp only [HWord.pre]
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [this] at hl; simpa using congrArg List.length hl
      have hC : C = (C.take (i + 1)) ++ C.drop (i + 1) := (List.take_append_drop _ _).symm
      simp only [HWord.pre] at hl
      rw [hl] at hC
      set X := C.drop (i + 1)
      have hw : D.Q.IsWalk v C := hv.1
      rw [hC, Statement.FinQuiver.isWalk_append] at hw
      have hend : D.Q.wend v (C.take i ++ [l]) = l.tgt := by
        rw [Statement.FinQuiver.wend_append]; rfl
      refine ⟨?_, ?_⟩
      · change D.trs C _ ≤ _
        conv_lhs => rw [hC, D.trs_append]
        refine D.trs_mono _ ?_
        rw [← hend]
        refine trs_le_vsp_wend hw.2 ?_
        rw [← Statement.FinQuiver.wend_append, ← hC]
        exact inf_le_left
      · change _ ≤ D.trs C _
        conv_rhs => rw [hC, D.trs_append]
        exact D.trs_mono _ bot_le
  | inf f =>
      simp only [HWord.pre] at hl ⊢
      refine ⟨(iInf_le _ (i + 1)).trans ?_, le_trans ?_ (le_iSup _ (i + 1))⟩
      · rw [hl, Statement.FinQuiver.wend_append]; rfl
      · rw [hl]

theorem trs_append_bot_le {v : D.Q.V} {E R : List (Letter D.Q)} (hw : D.Q.IsWalk v (E ++ R)) :
    D.trs (E ++ R) (⊥ : Submodule k M) ≤ D.trs E (D.vsp M (D.Q.wend v E)) := by
  rw [D.trs_append]
  rw [Statement.FinQuiver.isWalk_append] at hw
  exact D.trs_mono _ (trs_le_vsp_wend hw.2 bot_le)

theorem ofFn_eq_append (f : ℕ → Letter D.Q) {a b : ℕ} (hab : a ≤ b) :
    (List.ofFn fun i : Fin b ↦ f i) =
      (List.ofFn fun i : Fin a ↦ f i) ++ List.ofFn fun i : Fin (b - a) ↦ f (a + i) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    by_cases hi : i < a
    · rw [List.getElem_append_left (by simpa using hi)]; simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn]
      congr 1; omega

theorem Signs.minus_le_plus {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) :
    S.minus M v s h ≤ S.plus M v s h := by
  cases h with
  | fin C => exact S.minusF_le_plusF v s C
  | inf f =>
      refine iSup_le fun n ↦ le_iInf fun m ↦ ?_
      rcases le_total m n with hmn | hnm
      · have hw := (hv n).1
        rw [ofFn_eq_append f hmn] at hw ⊢
        exact trs_append_bot_le hw
      · rw [ofFn_eq_append f hnm, D.trs_append]
        exact D.trs_mono _ bot_le

theorem Signs.plus_le_vsp {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) :
    S.plus M v s h ≤ D.vsp M v := by
  cases h with
  | fin C => exact S.plusF_le_vsp hv.1
  | inf f => exact (iInf_le _ 0).trans (by simp; rfl)

/-- The letter after a prefix of a valid half-word continues it with the right sign. -/
theorem Signs.cont_of_pre {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) {i : ℕ}
    {l : Letter D.Q} (hl : h.pre (i + 1) = h.pre i ++ [l]) :
    l.src = D.Q.wend v (h.pre i) ∧ S.st l = S.nsign s (h.pre i) :=
  Signs.IsHW.last S (hl ▸ hv.pre S (i + 1))

/-- **The order lemma**: lower half-words have smaller subspaces. -/
theorem Signs.plus_le_minus_of_lt {v : D.Q.V} {s : Bool} {h h' : HWord D.Q}
    (hv : S.Valid v s h) (hv' : S.Valid v s h') (hlt : toLex h.code < toLex h'.code) :
    S.plus M v s h ≤ S.minus M v s h' := by
  obtain ⟨i, hj, hi⟩ := hlt
  have hi' : h.code i < h'.code i := hi
  have hE : h.pre i = h'.pre i := S.pre_eq_of_code_eq hv hv' i hj
  have h2 := h'.code_le_two i
  -- the direct continuation of `h'` at `i`, when the code of `h'` is `2`
  have hdir : h'.code i = 2 → S.plusF M v s (h.pre i) ≤ S.minus M v s h' := by
    intro hc
    obtain ⟨l', hl', hld'⟩ := h'.pre_succ_of_code_ne (i := i) (by omega)
    obtain ⟨b, db⟩ := l'
    have hdb : db = true := hld'.mp hc
    subst hdb
    have hc' := S.cont_of_pre hv' hl'
    rw [← hE] at hc'
    refine (S.plusF_le_trs_dir (b := b) ⟨hc'.1, hc'.2⟩).trans ?_
    rw [hE]
    exact (S.plus_le_pre hv' hl').2
  rcases Nat.lt_or_ge (h.code i) 1 with h0 | h0
  · -- `h` continues with an inverse letter
    have hc0 : h.code i = 0 := by omega
    obtain ⟨l, hl, hld⟩ := h.pre_succ_of_code_ne (i := i) (by omega)
    obtain ⟨d, dd⟩ := l
    have hdd : dd = false := by
      cases dd
      · rfl
      · exact absurd (hld.mpr rfl) (by omega)
    subst hdd
    have hc := S.cont_of_pre hv hl
    have h1 : S.plus M v s h ≤ S.minusF M v s (h.pre i) :=
      (S.plus_le_pre hv hl).1.trans (S.trs_inv_le_minusF ⟨hc.1, hc.2⟩ _)
    refine h1.trans ?_
    rcases Nat.lt_or_ge (h'.code i) 2 with h3 | h3
    · have hc1 : h'.code i = 1 := by omega
      rw [h'.eq_fin_of_code_eq_one hc1, ← hE]
      exact le_rfl
    · exact (S.minusF_le_plusF _ _ _).trans (hdir (by omega))
  · have hc1 : h.code i = 1 := by omega
    have hc2 : h'.code i = 2 := by omega
    rw [h.eq_fin_of_code_eq_one hc1]
    exact hdir hc2

end MonomialData

end BrickAccessibility
