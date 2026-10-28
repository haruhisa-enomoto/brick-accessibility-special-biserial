module

public import BrickAccessibility.Section4.ExtExact
public import BrickAccessibility.Section4.Positive

/-!
# Lemma 4.3: the endpoint equalities

For a gentle algebra and a string `w` of positive length, and a vertex `v`,

* `s_v - η_v = socend_v - extout_v` (`lemma_4_3_socle`, equation (4.1)),
* `t_v - θ_v = topend_v - extin_v` (`lemma_4_3_top`, equation (4.2)),

where `s_v = dim Hom(S_v, M)`, `η_v = dim Ext¹(M, S_v)`, `t_v = dim Hom(M, S_v)`,
`θ_v = dim Ext¹(S_v, M)`, `socend_v`/`topend_v` count socle/top endpoints over `v`, and
`extout_v`/`extin_v` count outgoing extending arrows ending at `v` / incoming extending
arrows starting at `v`, one for each endpoint at which they extend.

The counting inequalities of `Inequality.lean` are equalities (reverse injections in
Step A, a five-case count in Step B), and the dimension bounds for `Ext¹` are equalities
over quadratic monomial data (`ExtExact.lean`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

section StepA

variable (hs : w.IsString D)
include hs

open Classical in
/-- **Step A, reverse.** Incoming slots and outgoing extensions inject into the pairs
counted by `Σ_b Z_b`. -/
theorem sum_Z_ge (v : D.Q.V) :
    Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.InSlot x.1 x.2} +
      w.extout v ≤
    ∑ b : {b : D.Q.A // D.Q.tgt b = v}, Fintype.card {q : Fin (w.len + 1) //
        w.vtx q = D.Q.src b.1 ∧ ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q} := by
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
  -- an incoming slot is an edge `q →b p`
  have hslot : ∀ x : S, ∃ (b : D.Q.A) (q : Fin (w.len + 1)),
      w.next b q = some x.1.1 ∧ x.1.2 = decide (q.val = x.1.1.val + 1) := by
    rintro ⟨⟨p, s⟩, hv, hsl⟩
    cases s
    · obtain ⟨a, ha⟩ : ∃ a, w.leftL p = some (a, true) := by simpa [InSlot] using hsl
      obtain ⟨i, hi, hip⟩ := w.next_to_of_leftL_dir hs.1 ha
      exact ⟨a, i, hi, by symm; simp only [decide_eq_false_iff_not]; omega⟩
    · obtain ⟨a, ha⟩ : ∃ a, w.rightL p = some (a, false) := by simpa [InSlot] using hsl
      obtain ⟨i, hi, hip⟩ := w.next_to_of_rightL_inv hs.1 ha
      exact ⟨a, i, hi, by symm; simp only [decide_eq_true_eq]; omega⟩
  choose sb sq hsn hsd using hslot
  have hfree : ∀ (b : D.Q.A) (q p : Fin (w.len + 1)), w.next b q = some p →
      ∀ a i, D.toPathData.Forbidden a b → w.next a i ≠ some q := by
    intro b q p hbq a i hab hai
    exact w.pval_pair_ne_zero hs hai hbq hab.2
  let G : S ⊕ E → T
    | Sum.inl x => ⟨(⟨sb x, by rw [← (w.coeffQuiver D).next_tgt _ _ _ (hsn x)]; exact x.2.1⟩,
        sq x), (w.coeffQuiver D).next_src _ _ _ (hsn x), hfree _ _ _ (hsn x)⟩
    | Sum.inr x => ⟨(⟨x.1.2, x.2.2.2⟩, x.1.1), x.2.2.1.1.symm, by
        intro a i hab hai
        have h0 := hab.2
        rcases w.letter_of_next_to hs.1 hai with ⟨hl, -⟩ | ⟨hl, -⟩
        · have := x.2.2.1.2.1 _ hl
          simp only [if_true] at this
          exact this h0
        · have := x.2.2.1.2.2 _ hl
          simp only [Bool.false_eq_true, if_false] at this
          exact this h0⟩
  -- outgoing extending arrows do not move their endpoint
  have hnone : ∀ x : E, w.next x.1.2 x.1.1 = none := by
    intro x
    by_contra hne
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
    rcases w.letter_of_next_from hs.1 hj with ⟨hl, -⟩ | ⟨hl, -⟩
    · have := x.2.2.1.2.1 _ hl
      simp only [Bool.false_eq_true, if_false] at this
      exact this rfl
    · have := x.2.2.1.2.2 _ hl
      simp only [if_true] at this
      exact this rfl
  have hG : Function.Injective G := by
    rintro (x | x) (y | y) h
    · have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      have hx := hsn x
      rw [h1, h2, hsn y] at hx
      have hp : x.1.1 = y.1.1 := (Option.some.inj hx).symm
      have hsd' : x.1.2 = y.1.2 := by rw [hsd x, hsd y, h2, hp]
      exact congrArg Sum.inl (Subtype.ext (Prod.ext hp hsd'))
    · exfalso
      have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      have := hnone y
      rw [← h1, ← h2, hsn x] at this
      cases this
    · exfalso
      have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      have := hnone x
      rw [h1, h2, hsn y] at this
      cases this
    · have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      exact congrArg Sum.inr (Subtype.ext (Prod.ext h2 h1))
  have := Fintype.card_le_of_injective G hG
  rw [Fintype.card_sum] at this
  exact this

open Classical in
/-- **Step A', reverse.** -/
theorem sum_Y_ge (v : D.Q.V) :
    Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.OutSlot x.1 x.2} +
      w.extin v ≤
    ∑ b : {b : D.Q.A // D.Q.src b = v}, Fintype.card {q : Fin (w.len + 1) //
        w.vtx q = D.Q.tgt b.1 ∧ ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none} := by
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
  -- an outgoing slot is an edge `p →b q`
  have hslot : ∀ x : S, ∃ (b : D.Q.A) (q : Fin (w.len + 1)),
      w.next b x.1.1 = some q ∧ x.1.2 = decide (q.val = x.1.1.val + 1) := by
    rintro ⟨⟨p, s⟩, hv, hsl⟩
    cases s
    · obtain ⟨a, ha⟩ : ∃ a, w.leftL p = some (a, false) := by simpa [OutSlot] using hsl
      obtain ⟨j, hj, hjp⟩ := w.next_of_leftL_inv hs.1 ha
      exact ⟨a, j, hj, by symm; simp only [decide_eq_false_iff_not]; omega⟩
    · obtain ⟨a, ha⟩ : ∃ a, w.rightL p = some (a, true) := by simpa [OutSlot] using hsl
      obtain ⟨j, hj, hjp⟩ := w.next_of_rightL_dir hs.1 ha
      exact ⟨a, j, hj, by symm; simp only [decide_eq_true_eq]; omega⟩
  choose sb sq hsn hsd using hslot
  have hfree : ∀ (b : D.Q.A) (p q : Fin (w.len + 1)), w.next b p = some q →
      ∀ c, D.toPathData.Forbidden b c → w.next c q = none := by
    intro b p q hbq c hbc
    by_contra hne
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
    exact w.pval_pair_ne_zero hs hbq hj hbc.2
  let G : S ⊕ E → T
    | Sum.inl x => ⟨(⟨sb x, by rw [← (w.coeffQuiver D).next_src _ _ _ (hsn x)]; exact x.2.1⟩,
        sq x), (w.coeffQuiver D).next_tgt _ _ _ (hsn x), hfree _ _ _ (hsn x)⟩
    | Sum.inr x => ⟨(⟨x.1.2, x.2.2.2⟩, x.1.1), x.2.2.1.1.symm, by
        intro c hbc
        by_contra hne
        obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
        have h0 := hbc.2
        rcases w.letter_of_next_from hs.1 hj with ⟨hl, -⟩ | ⟨hl, -⟩
        · have := x.2.2.1.2.1 _ hl
          simp only [Bool.false_eq_true, if_false] at this
          exact this h0
        · have := x.2.2.1.2.2 _ hl
          simp only [if_true] at this
          exact this h0⟩
  -- incoming extending arrows do not reach their endpoint
  have hnone : ∀ (x : E) i, w.next x.1.2 i ≠ some x.1.1 := by
    intro x i hi
    rcases w.letter_of_next_to hs.1 hi with ⟨hl, -⟩ | ⟨hl, -⟩
    · have := x.2.2.1.2.1 _ hl
      simp only [if_true] at this
      exact this rfl
    · have := x.2.2.1.2.2 _ hl
      simp only [Bool.false_eq_true, if_false] at this
      exact this rfl
  have hG : Function.Injective G := by
    rintro (x | x) (y | y) h
    · have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      have hx := hsn x
      rw [h1, h2] at hx
      have hp : x.1.1 = y.1.1 := w.next_injective hs.1 hx (hsn y)
      have hsd' : x.1.2 = y.1.2 := by rw [hsd x, hsd y, h2, hp]
      exact congrArg Sum.inl (Subtype.ext (Prod.ext hp hsd'))
    · exfalso
      have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      have := hsn x
      rw [h1, h2] at this
      exact hnone y _ this
    · exfalso
      have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      have := hsn y
      rw [← h1, ← h2] at this
      exact hnone x _ this
    · have h1 := congrArg (fun z : T ↦ z.1.1.1) h
      have h2 := congrArg (fun z : T ↦ z.1.2) h
      simp only [G] at h1 h2
      exact congrArg Sum.inr (Subtype.ext (Prod.ext h2 h1))
  have := Fintype.card_le_of_injective G hG
  rw [Fintype.card_sum] at this
  exact this

end StepA

section StepB

variable (hw : w.NoForks)
include hw

open Classical in
/-- The per-position count behind Step B is exact. -/
theorem pointwise_B_eq (hn : 0 < w.len) (p : Fin (w.len + 1)) :
    (if w.InSlot p false then 1 else 0) + (if w.InSlot p true then 1 else 0) +
      (if (∀ a i, w.next a i ≠ some p) then 1 else 0) +
      (if w.IsEnd p ∧ ∃ a i, w.next a i = some p then 1 else 0) =
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
    and_true, and_false, Bool.true_eq_false, Bool.false_eq_true, exists_eq',
    not_true_eq_false, not_false_eq_true, and_self, if_true, if_false]
  all_goals (try split_ifs) <;> omega

open Classical in
theorem pointwise_B'_eq (hn : 0 < w.len) (p : Fin (w.len + 1)) :
    (if w.OutSlot p false then 1 else 0) + (if w.OutSlot p true then 1 else 0) +
      (if (∀ a, w.next a p = none) then 1 else 0) +
      (if w.IsEnd p ∧ ∃ a j, w.next a p = some j then 1 else 0) =
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
    and_true, and_false, Bool.true_eq_false, Bool.false_eq_true, exists_eq',
    not_true_eq_false, not_false_eq_true, and_self, if_true, if_false]
  all_goals (try split_ifs) <;> omega

open Classical in
theorem step_B_eq (hn : 0 < w.len) (v : D.Q.V) :
    Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.InSlot x.1 x.2} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} +
      w.socend v =
    Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} := by
  simp only [socend, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have h := w.pointwise_B_eq hw hn p
  by_cases hv : w.vtx p = v
  · simp only [hv, true_and, if_true]
    have e : ∀ x y z u : ℕ, x + y + z + u = y + x + z + u := fun _ _ _ _ ↦ by ring
    first
      | exact h
      | (rw [e]; exact h)
  · simp [hv]

open Classical in
theorem step_B'_eq (hn : 0 < w.len) (v : D.Q.V) :
    Fintype.card {x : Fin (w.len + 1) × Bool // w.vtx x.1 = v ∧ w.OutSlot x.1 x.2} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} +
      w.topend v =
    Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} +
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} := by
  simp only [topend, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have h := w.pointwise_B'_eq hw hn p
  by_cases hv : w.vtx p = v
  · simp only [hv, true_and, if_true]
    have e : ∀ x y z u : ℕ, x + y + z + u = y + x + z + u := fun _ _ _ _ ↦ by ring
    first
      | exact h
      | (rw [e]; exact h)
  · simp [hv]

end StepB

end Word

/-- **Lemma 4.3, equation (4.1):** `s - η = Σ_{socle endpoints} ε_v - Σ_{outgoing extending
arrows} ε_{v'}`, coordinatewise. -/
theorem lemma_4_3_socle [FiniteDimensional k B] (D : MonomialData k B) (hD : D.IsGentle)
    (w : Word D.Q) (hw : w.IsString D) (hn : 0 < w.len) (v : D.Q.V) :
    (finrank k (D.simple v →ₗ[B] w.stringModule D hw) : ℤ) -
        finrank k (Ext1 k B (w.stringModule D hw) (D.simple v)) =
      (w.socend v : ℤ) - w.extout v := by
  classical
  set C := w.coeffQuiver D
  have hC := hw.2
  have hinj : C.InjMoves := fun a i i' j h h' ↦ w.next_injective hw.1 h h'
  have hcoef : C.CoefNe := fun _ _ _ _ ↦ one_ne_zero
  have hext := D.finrank_ext1_simple_eq (w.stringModule D hw) hD.2.1 v
  have e1 : finrank k (D.E0 (w.stringModule D hw) v) =
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} :=
    (C.finrank_E0 hC v).trans (Fintype.card_congr (Equiv.refl _))
  have e2 : finrank k (D.K0 (w.stringModule D hw) v) =
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} :=
    (C.finrank_K0 hC hcoef v).trans (Fintype.card_congr (Equiv.refl _))
  have e3 : ∀ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb (w.stringModule D hw) b.1) =
      Fintype.card {q : Fin (w.len + 1) // w.vtx q = D.Q.src b.1 ∧
        ∀ a i, D.toPathData.Forbidden a b.1 → w.next a i ≠ some q} :=
    fun b ↦ (C.finrank_Zb hC hcoef b.1).trans (Fintype.card_congr (Equiv.refl _))
  have e4 : finrank k (D.simple v →ₗ[B] w.stringModule D hw) =
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} :=
    (D.finrank_hom_simple _ v).trans
      ((C.finrank_K0' hC hinj hcoef v).trans (Fintype.card_congr (Equiv.refl _)))
  rw [e1, e2, Finset.sum_congr rfl fun b _ ↦ e3 b] at hext
  have hA := w.sum_Z_le hD.1.2 hw v
  have hA' := w.sum_Z_ge hw v
  have hB := w.step_B_eq hw.1 hn v
  rw [e4]
  omega

/-- **Lemma 4.3, equation (4.2):** `t - θ = Σ_{top endpoints} ε_v - Σ_{incoming extending
arrows} ε_{v'}`, coordinatewise. -/
theorem lemma_4_3_top [FiniteDimensional k B] (D : MonomialData k B) (hD : D.IsGentle)
    (w : Word D.Q) (hw : w.IsString D) (hn : 0 < w.len) (v : D.Q.V) :
    (finrank k (w.stringModule D hw →ₗ[B] D.simple v) : ℤ) -
        finrank k (Ext1 k B (D.simple v) (w.stringModule D hw)) =
      (w.topend v : ℤ) - w.extin v := by
  classical
  set C := w.coeffQuiver D
  have hC := hw.2
  have hinj : C.InjMoves := fun a i i' j h h' ↦ w.next_injective hw.1 h h'
  have hcoef : C.CoefNe := fun _ _ _ _ ↦ one_ne_zero
  have hext := D.finrank_ext1_simple_left_eq (w.stringModule D hw) hD.2.1 v
  have e1 : finrank k (D.E0' (w.stringModule D hw) v) =
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v} :=
    (C.finrank_E0' hC v).trans (Fintype.card_congr (Equiv.refl _))
  have e2 : finrank k (D.K0' (w.stringModule D hw) v) =
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a, w.next a p = none} :=
    (C.finrank_K0' hC hinj hcoef v).trans (Fintype.card_congr (Equiv.refl _))
  have e3 : ∀ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb (w.stringModule D hw) b.1) =
      Fintype.card {q : Fin (w.len + 1) // w.vtx q = D.Q.tgt b.1 ∧
        ∀ c, D.toPathData.Forbidden b.1 c → w.next c q = none} :=
    fun b ↦ (C.finrank_Yb hC hinj hcoef b.1).trans (Fintype.card_congr (Equiv.refl _))
  have e4 : finrank k (w.stringModule D hw →ₗ[B] D.simple v) =
      Fintype.card {p : Fin (w.len + 1) // w.vtx p = v ∧ ∀ a i, w.next a i ≠ some p} :=
    (D.finrank_hom_to_simple _ v).trans
      ((C.finrank_K0 hC hcoef v).trans (Fintype.card_congr (Equiv.refl _)))
  rw [e1, e2, Finset.sum_congr rfl fun b _ ↦ e3 b] at hext
  have hA := w.sum_Y_le hD.1.2 hw v
  have hA' := w.sum_Y_ge hw v
  have hB := w.step_B'_eq hw.1 hn v
  rw [e4]
  omega

end BrickAccessibility
