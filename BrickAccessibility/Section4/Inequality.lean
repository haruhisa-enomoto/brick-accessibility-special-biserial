module

public import BrickAccessibility.Section4.Extending

/-!
# The endpoint inequalities (Lemma 4.3, upper-bound form)

For a string `w` of positive length over special biserial monomial data and a
vertex `v`:

`Σ_{b → v} Z_b + noin_v + socend_v ≤ noout_v + n_v + extout_v`  (`socle_ineq`)

where `Z_b` counts positions over `src b` without incoming edges labelled by a
forbidden predecessor of `b`, `noin_v`/`noout_v` count positions over `v`
without incoming/outgoing edges, `n_v` counts positions over `v`, `socend_v`
counts socle endpoints over `v`, and `extout_v` counts pairs (endpoint, outgoing
extending arrow ending at `v`). Combined with the bound for `Ext¹(M, S_v)` this
gives `s_v - η_v ≥ socend_v - extout_v`, the inequality form of (4.1). The mirror
statement `top_ineq` gives (4.2) in the same form.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

open Classical in
/-- Socle endpoints over `v`. -/
def socend (v : D.Q.V) : ℕ :=
  Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ w.IsEnd p ∧ ∃ a i, w.next a i = some p}

open Classical in
/-- Top endpoints over `v`. -/
def topend (v : D.Q.V) : ℕ :=
  Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ w.IsEnd p ∧ ∃ a j, w.next a p = some j}

open Classical in
/-- Pairs of an endpoint and an outgoing extending arrow ending at `v`. -/
def extout (v : D.Q.V) : ℕ :=
  Fintype.card {x : Fin (w.len + 1) × D.Q.A // w.IsEnd x.1 ∧ w.OutExt x.1 x.2 ∧ D.Q.tgt x.2 = v}

open Classical in
/-- Pairs of an endpoint and an incoming extending arrow starting at `v`. -/
def extin (v : D.Q.V) : ℕ :=
  Fintype.card {x : Fin (w.len + 1) × D.Q.A // w.IsEnd x.1 ∧ w.InExt x.1 x.2 ∧ D.Q.src x.2 = v}

/-- An incoming edge at `p` is its left letter (direct) or right letter (inverse). -/
theorem letter_of_next_to (hw : w.NoForks) {a : D.Q.A} {i p : Fin (w.len + 1)}
    (h : w.next a i = some p) :
    w.leftL p = some (a, true) ∧ i.val + 1 = p.val ∨
      w.rightL p = some (a, false) ∧ i.val = p.val + 1 := by
  rcases (w.next_eq_some_iff hw a i p).mp h with ⟨hi, hl, hp⟩ | ⟨hi, hl, hp⟩
  · left
    refine ⟨?_, hp.symm⟩
    unfold leftL; rw [dif_pos (by omega)]
    simp only [show p.val - 1 = i.val by omega, hl]
  · right
    have hlt := i.isLt
    simp only [len] at hlt
    refine ⟨?_, by omega⟩
    unfold rightL; rw [dif_pos (by omega)]
    simp only [show p.val = i.val - 1 by omega, hl]

/-- An outgoing edge at `p` is its left letter (inverse) or right letter (direct). -/
theorem letter_of_next_from (hw : w.NoForks) {a : D.Q.A} {p j : Fin (w.len + 1)}
    (h : w.next a p = some j) :
    w.leftL p = some (a, false) ∧ j.val + 1 = p.val ∨
      w.rightL p = some (a, true) ∧ j.val = p.val + 1 := by
  rcases (w.next_eq_some_iff hw a p j).mp h with ⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩
  · right
    refine ⟨?_, hj⟩
    unfold rightL; rw [dif_pos hi]
    simp only [hl]
  · left
    refine ⟨?_, by omega⟩
    unfold leftL; rw [dif_pos hi]
    simp only [hl]

/-- Incoming slots at positions over `v`: `(p, false)` for a direct left letter and
`(p, true)` for an inverse right letter. -/
def InSlot (p : Fin (w.len + 1)) (s : Bool) : Prop :=
  if s then ∃ a, w.rightL p = some (a, false) else ∃ a, w.leftL p = some (a, true)

/-- Outgoing slots: `(p, false)` for an inverse left letter and `(p, true)` for a
direct right letter. -/
def OutSlot (p : Fin (w.len + 1)) (s : Bool) : Prop :=
  if s then ∃ a, w.rightL p = some (a, true) else ∃ a, w.leftL p = some (a, false)

section StepA

variable (hSB : D.toPathData.IsSpecialBiserial) (hs : w.IsString D)
include hSB hs

open Classical in
/-- **Step A.** `Σ_{b → v} Z_b ≤ (incoming slots over v) + extout_v`. -/
theorem sum_Z_le (v : D.Q.V) :
    ∑ b : {b : D.Q.A // D.Q.tgt b = v}, Fintype.card {q : Fin (w.len + 1) //
        w.vtx q = D.Q.src b.1 ∧ ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q} ≤
      Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.InSlot x.1 x.2} +
      w.extout v := by
  let T := {x : {b : D.Q.A // D.Q.tgt b = v} × Fin (w.len + 1) //
    w.vtx x.2 = D.Q.src x.1.1 ∧ ∀ a i, D.toPathData.Forbidden a x.1.1 → w.next a i ≠ some x.2}
  have hT : Fintype.card T = ∑ b : {b : D.Q.A // D.Q.tgt b = v}, Fintype.card {q : Fin (w.len + 1) //
      w.vtx q = D.Q.src b.1 ∧ ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (b : {b : D.Q.A // D.Q.tgt b = v}) (q : Fin (w.len + 1)) ↦
        w.vtx q = D.Q.src b.1 ∧ ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q))
  rw [← hT]
  let S := {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.InSlot x.1 x.2}
  let E := {x : Fin (w.len + 1) × D.Q.A // w.IsEnd x.1 ∧ w.OutExt x.1 x.2 ∧ D.Q.tgt x.2 = v}
  let F : T → S ⊕ E := fun x ↦
    if h : (w.next x.1.1.1 x.1.2).isSome then
      have hp : w.next x.1.1.1 x.1.2 = some ((w.next x.1.1.1 x.1.2).get h) := (Option.some_get h).symm
      Sum.inl ⟨((w.next x.1.1.1 x.1.2).get h, decide (x.1.2.val = ((w.next x.1.1.1 x.1.2).get h).val + 1)),
        by
          refine ⟨((w.coeffQuiver D).next_tgt _ _ _ hp).trans x.1.1.2, ?_⟩
          rcases w.letter_of_next_to hs.1 hp with ⟨hl, hq⟩ | ⟨hl, hq⟩
          · have hd : decide (x.1.2.val = ((w.next x.1.1.1 x.1.2).get h).val + 1) = false := by
              simp only [decide_eq_false_iff_not]; omega
            rw [hd]
            simp only [InSlot, Bool.false_eq_true, if_false]
            exact ⟨_, hl⟩
          · have hd : decide (x.1.2.val = ((w.next x.1.1.1 x.1.2).get h).val + 1) = true := by
              simp only [decide_eq_true_eq]; omega
            rw [hd]
            simp only [InSlot, if_true]
            exact ⟨_, hl⟩⟩
    else
      have hn : w.next x.1.1.1 x.1.2 = none := Option.not_isSome_iff_eq_none.mp h
      have key := w.isEnd_and_outExt hSB hs x.2.1 hn x.2.2
      Sum.inr ⟨(x.1.2, x.1.1.1), key.1, key.2, x.1.1.2⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨⟨b, hb⟩, q⟩, hq⟩ ⟨⟨⟨b', hb'⟩, q'⟩, hq'⟩ hFF
    simp only [F] at hFF
    by_cases h1 : (w.next b q).isSome <;> by_cases h2 : (w.next b' q').isSome
    · rw [dif_pos h1, dif_pos h2] at hFF
      have hFF' := Prod.ext_iff.mp (congrArg Subtype.val (Sum.inl.inj hFF))
      obtain ⟨hpp, hside⟩ := hFF'
      simp only at hpp hside
      have hp1 : w.next b q = some ((w.next b q).get h1) := (Option.some_get h1).symm
      have hp2 : w.next b' q' = some ((w.next b' q').get h2) := (Option.some_get h2).symm
      rcases w.letter_of_next_to hs.1 hp1 with ⟨hl1, hq1⟩ | ⟨hl1, hq1⟩ <;>
        rcases w.letter_of_next_to hs.1 hp2 with ⟨hl2, hq2⟩ | ⟨hl2, hq2⟩
      · rw [hpp] at hl1
        rw [hl1] at hl2
        have hbb : b = b' := by simpa using hl2
        subst hbb
        have : q = q' := Fin.ext (by rw [hpp] at hq1; omega)
        subst this
        rfl
      · exfalso
        simp only [decide_eq_decide] at hside
        rw [hpp] at hq1
        omega
      · exfalso
        simp only [decide_eq_decide] at hside
        rw [hpp] at hq1
        omega
      · rw [hpp] at hl1
        rw [hl1] at hl2
        have hbb : b = b' := by simpa using hl2
        subst hbb
        have : q = q' := Fin.ext (by rw [hpp] at hq1; omega)
        subst this
        rfl
    · rw [dif_pos h1, dif_neg h2] at hFF
      exact absurd hFF Sum.inl_ne_inr
    · rw [dif_neg h1, dif_pos h2] at hFF
      exact absurd hFF Sum.inr_ne_inl
    · rw [dif_neg h1, dif_neg h2] at hFF
      have hFF' := Prod.ext_iff.mp (congrArg Subtype.val (Sum.inr.inj hFF))
      obtain ⟨hqq, hbb⟩ := hFF'
      simp only at hqq hbb
      subst hqq; subst hbb
      rfl
  have := Fintype.card_le_of_injective F hF
  rw [Fintype.card_sum] at this
  exact this

end StepA

section StepB

variable (hw : w.NoForks)
include hw

theorem noin_iff (p : Fin (w.len + 1)) :
    (∀ a i, w.next a i ≠ some p) ↔ ¬ w.InSlot p false ∧ ¬ w.InSlot p true := by
  simp only [InSlot, Bool.false_eq_true, if_false, if_true]
  constructor
  · intro h
    refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
    · obtain ⟨i, hi, -⟩ := w.next_to_of_leftL_dir hw ha; exact h a i hi
    · obtain ⟨i, hi, -⟩ := w.next_to_of_rightL_inv hw ha; exact h a i hi
  · rintro ⟨h1, h2⟩ a i hi
    rcases w.letter_of_next_to hw hi with ⟨hl, -⟩ | ⟨hl, -⟩
    · exact h1 ⟨a, hl⟩
    · exact h2 ⟨a, hl⟩

theorem noout_iff (p : Fin (w.len + 1)) :
    (∀ a, w.next a p = none) ↔ ¬ w.OutSlot p false ∧ ¬ w.OutSlot p true := by
  simp only [OutSlot, Bool.false_eq_true, if_false, if_true]
  constructor
  · intro h
    refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
    · obtain ⟨j, hj, -⟩ := w.next_of_leftL_inv hw ha; rw [h a] at hj; cases hj
    · obtain ⟨j, hj, -⟩ := w.next_of_rightL_dir hw ha; rw [h a] at hj; cases hj
  · rintro ⟨h1, h2⟩ a
    by_contra hne
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
    rcases w.letter_of_next_from hw hj with ⟨hl, -⟩ | ⟨hl, -⟩
    · exact h1 ⟨a, hl⟩
    · exact h2 ⟨a, hl⟩

omit hw in
theorem slots_left (p : Fin (w.len + 1)) :
    ((w.InSlot p false ∨ w.OutSlot p false) ↔ 0 < p.val) ∧
      ¬ (w.InSlot p false ∧ w.OutSlot p false) := by
  simp only [InSlot, OutSlot, Bool.false_eq_true, if_false]
  rcases hl : w.leftL p with _ | ⟨a, d⟩
  · have hp : ¬ 0 < p.val := fun hp ↦ by
      obtain ⟨l, hl'⟩ := w.leftL_eq_some hp; rw [hl] at hl'; cases hl'
    simp [hp]
  · have hp : 0 < p.val := by
      by_contra hp; rw [w.leftL_eq_none (by omega)] at hl; cases hl
    cases d <;> simp [hp]

omit hw in
theorem slots_right (p : Fin (w.len + 1)) :
    ((w.InSlot p true ∨ w.OutSlot p true) ↔ p.val < w.len) ∧
      ¬ (w.InSlot p true ∧ w.OutSlot p true) := by
  simp only [InSlot, OutSlot, if_true]
  have hlt := p.isLt
  rcases hl : w.rightL p with _ | ⟨a, d⟩
  · have hp : ¬ p.val < w.len := fun hp ↦ by
      obtain ⟨l, hl'⟩ := w.rightL_eq_some hp; rw [hl] at hl'; cases hl'
    simp [hp]
  · have hp : p.val < w.len := by
      by_contra hp; rw [w.rightL_eq_none (by omega)] at hl; cases hl
    cases d <;> simp [hp]

open Classical in
/-- The per-position estimate behind Step B. -/
theorem pointwise_B (hn : 0 < w.len) (p : Fin (w.len + 1)) :
    (if w.InSlot p false then 1 else 0) + (if w.InSlot p true then 1 else 0) +
      (if (∀ a i, w.next a i ≠ some p) then 1 else 0) +
      (if w.IsEnd p ∧ ∃ a i, w.next a i = some p then 1 else 0) ≤
    (if (∀ a, w.next a p = none) then 1 else 0) + 1 := by
  have hexin : (∃ a i, w.next a i = some p) ↔ ¬ (∀ a i, w.next a i ≠ some p) := by
    push Not; exact Iff.rfl
  simp only [hexin, w.noin_iff hw p, w.noout_iff hw p]
  have hlt := p.isLt
  have hp0 : w.leftL p = none → p.val = 0 := fun h ↦ by
    by_contra hp; obtain ⟨l, hl⟩ := w.leftL_eq_some (p := p) (by omega); rw [h] at hl; cases hl
  have hp0' : ∀ l, w.leftL p = some l → 0 < p.val := fun l h ↦ by
    by_contra hp; rw [w.leftL_eq_none (by omega)] at h; cases h
  have hpn : w.rightL p = none → p.val = w.len := fun h ↦ by
    by_contra hp; obtain ⟨l, hl⟩ := w.rightL_eq_some (p := p) (by omega); rw [h] at hl; cases hl
  have hpn' : ∀ l, w.rightL p = some l → p.val < w.len := fun l h ↦ by
    by_contra hp; rw [w.rightL_eq_none (by omega)] at h; cases h
  simp only [InSlot, OutSlot, IsEnd, Bool.false_eq_true, if_false, if_true]
  rcases hL : w.leftL p with _ | ⟨a1, _ | _⟩ <;> rcases hR : w.rightL p with _ | ⟨a2, _ | _⟩
  all_goals
    (try have := hp0 hL); (try have := hp0' _ hL); (try have := hpn hR); (try have := hpn' _ hR)
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, exists_false,
    and_true, and_false, Bool.true_eq_false, Bool.false_eq_true, exists_eq', exists_eq,
    not_true_eq_false, not_false_eq_true, true_and, false_and, and_self, if_true, if_false]
  all_goals (try split_ifs) <;> omega

open Classical in
theorem card_subtype_eq_sum {α : Type} [Fintype α] (P : α → Prop) :
    Fintype.card {x // P x} = ∑ x, if P x then 1 else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter]

open Classical in
/-- **Step B.** `(incoming slots over v) + noin_v + socend_v ≤ noout_v + n_v`. -/
theorem step_B (hn : 0 < w.len) (v : D.Q.V) :
    Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.InSlot x.1 x.2} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} +
      w.socend v ≤
    Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} := by
  simp only [socend, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  have h := w.pointwise_B hw hn p
  by_cases hv : w.vtx p = v
  · simp only [hv, true_and, if_true]
    have e : ∀ x y z u : ℕ, x + y + z + u = y + x + z + u := fun _ _ _ _ ↦ by ring
    first
      | exact h
      | (rw [e]; exact h)
  · simp [hv]

end StepB

open Classical in
/-- **The socle inequality.** -/
theorem socle_ineq (hSB : D.toPathData.IsSpecialBiserial) (hs : w.IsString D) (hn : 0 < w.len)
    (v : D.Q.V) :
    ∑ b : {b : D.Q.A // D.Q.tgt b = v}, Fintype.card {q : Fin (w.len + 1) //
        w.vtx q = D.Q.src b.1 ∧ ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} +
      w.socend v ≤
    Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} + w.extout v := by
  have hA := w.sum_Z_le hSB hs v
  have hB := w.step_B hs.1 hn v
  omega

section Mirror

variable (hSB : D.toPathData.IsSpecialBiserial) (hs : w.IsString D)
include hSB hs

open Classical in
/-- **Step A'.** `Σ_{b ← v} Y_b ≤ (outgoing slots over v) + extin_v`. -/
theorem sum_Y_le (v : D.Q.V) :
    ∑ b : {b : D.Q.A // D.Q.src b = v}, Fintype.card {q : Fin (w.len + 1) //
        w.vtx q = D.Q.tgt b.1 ∧ ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none} ≤
      Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.OutSlot x.1 x.2} +
      w.extin v := by
  let T := {x : {b : D.Q.A // D.Q.src b = v} × Fin (w.len + 1) //
    w.vtx x.2 = D.Q.tgt x.1.1 ∧ ∀ c, D.toPathData.Forbidden x.1.1 c → w.next c x.2 = none}
  have hT : Fintype.card T = ∑ b : {b : D.Q.A // D.Q.src b = v}, Fintype.card {q : Fin (w.len + 1) //
      w.vtx q = D.Q.tgt b.1 ∧ ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (b : {b : D.Q.A // D.Q.src b = v}) (q : Fin (w.len + 1)) ↦
        w.vtx q = D.Q.tgt b.1 ∧ ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none))
  rw [← hT]
  let S := {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.OutSlot x.1 x.2}
  let E := {x : Fin (w.len + 1) × D.Q.A // w.IsEnd x.1 ∧ w.InExt x.1 x.2 ∧ D.Q.src x.2 = v}
  let F : T → S ⊕ E := fun x ↦
    if h : ∃ i, w.next x.1.1.1 i = some x.1.2 then
      Sum.inl ⟨(h.choose, decide (x.1.2.val = h.choose.val + 1)),
        by
          refine ⟨((w.coeffQuiver D).next_src _ _ _ h.choose_spec).trans x.1.1.2, ?_⟩
          rcases w.letter_of_next_from hs.1 h.choose_spec with ⟨hl, hq⟩ | ⟨hl, hq⟩
          · have hd : decide (x.1.2.val = h.choose.val + 1) = false := by
              simp only [decide_eq_false_iff_not]; omega
            rw [hd]
            simp only [OutSlot, Bool.false_eq_true, if_false]
            exact ⟨_, hl⟩
          · have hd : decide (x.1.2.val = h.choose.val + 1) = true := by
              simp only [decide_eq_true_eq]; omega
            rw [hd]
            simp only [OutSlot, if_true]
            exact ⟨_, hl⟩⟩
    else
      have hn : ∀ i, w.next x.1.1.1 i ≠ some x.1.2 := fun i hi ↦ h ⟨i, hi⟩
      have key := w.isEnd_and_inExt hSB hs x.2.1 hn
        (fun c j hc hj ↦ by rw [x.2.2 c hc] at hj; cases hj)
      Sum.inr ⟨(x.1.2, x.1.1.1), key.1, key.2, x.1.1.2⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨⟨b, hb⟩, q⟩, hq⟩ ⟨⟨⟨b', hb'⟩, q'⟩, hq'⟩ hFF
    simp only [F] at hFF
    by_cases h1 : ∃ i, w.next b i = some q <;> by_cases h2 : ∃ i, w.next b' i = some q'
    · rw [dif_pos h1, dif_pos h2] at hFF
      have hFF' := Prod.ext_iff.mp (congrArg Subtype.val (Sum.inl.inj hFF))
      obtain ⟨hpp, hside⟩ := hFF'
      simp only at hpp hside
      have hp1 := h1.choose_spec
      have hp2 := h2.choose_spec
      rcases w.letter_of_next_from hs.1 hp1 with ⟨hl1, hq1⟩ | ⟨hl1, hq1⟩ <;>
        rcases w.letter_of_next_from hs.1 hp2 with ⟨hl2, hq2⟩ | ⟨hl2, hq2⟩
      · rw [hpp] at hl1
        rw [hl1] at hl2
        have hbb : b = b' := by simpa using hl2
        subst hbb
        have : q = q' := Fin.ext (by rw [hpp] at hq1; omega)
        subst this
        rfl
      · exfalso
        simp only [decide_eq_decide] at hside
        rw [hpp] at hq1
        omega
      · exfalso
        simp only [decide_eq_decide] at hside
        rw [hpp] at hq1
        omega
      · rw [hpp] at hl1
        rw [hl1] at hl2
        have hbb : b = b' := by simpa using hl2
        subst hbb
        have : q = q' := Fin.ext (by rw [hpp] at hq1; omega)
        subst this
        rfl
    · rw [dif_pos h1, dif_neg h2] at hFF
      exact absurd hFF Sum.inl_ne_inr
    · rw [dif_neg h1, dif_pos h2] at hFF
      exact absurd hFF Sum.inr_ne_inl
    · rw [dif_neg h1, dif_neg h2] at hFF
      have hFF' := Prod.ext_iff.mp (congrArg Subtype.val (Sum.inr.inj hFF))
      obtain ⟨hqq, hbb⟩ := hFF'
      simp only at hqq hbb
      subst hqq; subst hbb
      rfl
  have := Fintype.card_le_of_injective F hF
  rw [Fintype.card_sum] at this
  exact this

end Mirror

section MirrorB

variable (hw : w.NoForks)
include hw

open Classical in
theorem pointwise_B' (hn : 0 < w.len) (p : Fin (w.len + 1)) :
    (if w.OutSlot p false then 1 else 0) + (if w.OutSlot p true then 1 else 0) +
      (if (∀ a, w.next a p = none) then 1 else 0) +
      (if w.IsEnd p ∧ ∃ a j, w.next a p = some j then 1 else 0) ≤
    (if (∀ a i, w.next a i ≠ some p) then 1 else 0) + 1 := by
  have hexout : (∃ a j, w.next a p = some j) ↔ ¬ (∀ a, w.next a p = none) := by
    constructor
    · rintro ⟨a, j, h⟩ h'; rw [h' a] at h; cases h
    · intro h; push Not at h; obtain ⟨a, ha⟩ := h
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp ha; exact ⟨a, j, hj⟩
  simp only [hexout, w.noin_iff hw p, w.noout_iff hw p]
  have hlt := p.isLt
  have hp0 : w.leftL p = none → p.val = 0 := fun h ↦ by
    by_contra hp; obtain ⟨l, hl⟩ := w.leftL_eq_some (p := p) (by omega); rw [h] at hl; cases hl
  have hp0' : ∀ l, w.leftL p = some l → 0 < p.val := fun l h ↦ by
    by_contra hp; rw [w.leftL_eq_none (by omega)] at h; cases h
  have hpn : w.rightL p = none → p.val = w.len := fun h ↦ by
    by_contra hp; obtain ⟨l, hl⟩ := w.rightL_eq_some (p := p) (by omega); rw [h] at hl; cases hl
  have hpn' : ∀ l, w.rightL p = some l → p.val < w.len := fun l h ↦ by
    by_contra hp; rw [w.rightL_eq_none (by omega)] at h; cases h
  simp only [InSlot, OutSlot, IsEnd, Bool.false_eq_true, if_false, if_true]
  rcases hL : w.leftL p with _ | ⟨a1, _ | _⟩ <;> rcases hR : w.rightL p with _ | ⟨a2, _ | _⟩
  all_goals
    (try have := hp0 hL); (try have := hp0' _ hL); (try have := hpn hR); (try have := hpn' _ hR)
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, exists_false,
    and_true, and_false, Bool.true_eq_false, Bool.false_eq_true, exists_eq', exists_eq,
    not_true_eq_false, not_false_eq_true, true_and, false_and, and_self, if_true, if_false]
  all_goals (try split_ifs) <;> omega

open Classical in
theorem step_B' (hn : 0 < w.len) (v : D.Q.V) :
    Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.OutSlot x.1 x.2} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} +
      w.topend v ≤
    Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} := by
  simp only [topend, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  have h := w.pointwise_B' hw hn p
  by_cases hv : w.vtx p = v
  · simp only [hv, true_and, if_true]
    have e : ∀ x y z u : ℕ, x + y + z + u = y + x + z + u := fun _ _ _ _ ↦ by ring
    first
      | exact h
      | (rw [e]; exact h)
  · simp [hv]

end MirrorB

open Classical in
/-- **The top inequality.** -/
theorem top_ineq (hSB : D.toPathData.IsSpecialBiserial) (hs : w.IsString D) (hn : 0 < w.len)
    (v : D.Q.V) :
    ∑ b : {b : D.Q.A // D.Q.src b = v}, Fintype.card {q : Fin (w.len + 1) //
        w.vtx q = D.Q.tgt b.1 ∧ ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} +
      w.topend v ≤
    Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} + w.extin v := by
  have hA := w.sum_Y_le hSB hs v
  have hB := w.step_B' hs.1 hn v
  omega

end Word

end BrickAccessibility
