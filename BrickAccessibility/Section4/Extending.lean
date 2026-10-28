module

public import BrickAccessibility.Section4.StringLocal

/-!
# Extending arrows (Definition 4.2)

For a string `w` over special biserial monomial data, an arrow `c` is an
*outgoing extending arrow* at a position `p` if it starts at the vertex of `p`
and is compatible with the edges at `p`: it differs from the label of every
outgoing edge, and it is an allowed successor of the label of every incoming
edge. Dually for *incoming extending arrows*. At an endpoint this is the table
of Section 4.1.

`isEnd_and_outExt` shows: a position over `src b` without an outgoing `b`-edge
and without incoming edges labelled by a forbidden predecessor of `b` is an
endpoint at which `b` is an outgoing extending arrow. An internal position would
need two incident edges, which contradicts the special biserial bounds or the
string condition. `isEnd_and_inExt` is the mirror statement.
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

/-- `p` is an endpoint of the string diagram. -/
def IsEnd (p : Fin (w.len + 1)) : Prop := p.val = 0 ∨ p.val = w.len

/-- Outgoing extending arrows at a position. -/
def OutExt (p : Fin (w.len + 1)) (c : D.Q.A) : Prop :=
  D.Q.src c = w.vtx p ∧
  (∀ l, w.leftL p = some l →
    (if l.2 then D.pval (D.Q.src l.1) [l.1, c] ≠ 0 else c ≠ l.1)) ∧
  (∀ l, w.rightL p = some l →
    (if l.2 then c ≠ l.1 else D.pval (D.Q.src l.1) [l.1, c] ≠ 0))

/-- Incoming extending arrows at a position. -/
def InExt (p : Fin (w.len + 1)) (c : D.Q.A) : Prop :=
  D.Q.tgt c = w.vtx p ∧
  (∀ l, w.leftL p = some l →
    (if l.2 then c ≠ l.1 else D.pval (D.Q.src c) [c, l.1] ≠ 0)) ∧
  (∀ l, w.rightL p = some l →
    (if l.2 then D.pval (D.Q.src c) [c, l.1] ≠ 0 else c ≠ l.1))

/-- An outgoing `a`-edge at `p` whenever the left letter is `a⁻¹`. -/
theorem next_of_leftL_inv (hw : w.NoForks) {p : Fin (w.len + 1)} {a : D.Q.A}
    (h : w.leftL p = some (a, false)) :
    ∃ j, w.next a p = some j ∧ j.val + 1 = p.val := by
  unfold leftL at h
  split_ifs at h with hp
  have hl := Option.some.inj h
  refine ⟨⟨p.val - 1, by omega⟩, (w.next_eq_some_iff hw a p _).mpr (Or.inr ⟨hp, hl, rfl⟩), by
    simp; omega⟩

theorem next_of_rightL_dir (hw : w.NoForks) {p : Fin (w.len + 1)} {a : D.Q.A}
    (h : w.rightL p = some (a, true)) :
    ∃ j, w.next a p = some j ∧ j.val = p.val + 1 := by
  unfold rightL at h
  split_ifs at h with hp
  have hl := Option.some.inj h
  exact ⟨⟨p.val + 1, by simp only [len]; omega⟩,
    (w.next_eq_some_iff hw a p _).mpr (Or.inl ⟨hp, hl, rfl⟩), rfl⟩

/-- An incoming `a`-edge at `p` whenever the left letter is `a`. -/
theorem next_to_of_leftL_dir (hw : w.NoForks) {p : Fin (w.len + 1)} {a : D.Q.A}
    (h : w.leftL p = some (a, true)) :
    ∃ i : Fin (w.len + 1), w.next a i = some p ∧ i.val + 1 = p.val := by
  unfold leftL at h
  split_ifs at h with hp
  have hl := Option.some.inj h
  have hlt := p.isLt
  simp only [len] at hlt
  refine ⟨⟨p.val - 1, by omega⟩, (w.next_eq_some_iff hw a _ p).mpr (Or.inl ⟨by simp; omega, ?_, by
    simp; omega⟩), by simp; omega⟩
  simpa using hl

theorem next_to_of_rightL_inv (hw : w.NoForks) {p : Fin (w.len + 1)} {a : D.Q.A}
    (h : w.rightL p = some (a, false)) :
    ∃ i : Fin (w.len + 1), w.next a i = some p ∧ i.val = p.val + 1 := by
  unfold rightL at h
  split_ifs at h with hp
  have hl := Option.some.inj h
  refine ⟨⟨p.val + 1, by simp only [len]; omega⟩, (w.next_eq_some_iff hw a _ p).mpr
    (Or.inr ⟨by simp, ?_, by simp⟩), rfl⟩
  simpa using hl

theorem leftL_eq_some {p : Fin (w.len + 1)} (hp : 0 < p.val) :
    ∃ l, w.leftL p = some l := by
  unfold leftL; rw [dif_pos hp]; exact ⟨_, rfl⟩

theorem rightL_eq_some {p : Fin (w.len + 1)} (hp : p.val < w.len) :
    ∃ l, w.rightL p = some l := by
  unfold rightL; rw [dif_pos hp]; exact ⟨_, rfl⟩

theorem leftL_eq_none {p : Fin (w.len + 1)} (hp : p.val = 0) : w.leftL p = none := by
  unfold leftL; rw [dif_neg (by omega)]

theorem rightL_eq_none {p : Fin (w.len + 1)} (hp : p.val = w.len) : w.rightL p = none := by
  unfold rightL; rw [dif_neg (by simp only [len] at hp; omega)]

/-- Two allowed walks give contradictions with cardinality bounds. -/
theorem false_of_card_le_one {α : Type*} {P : α → Prop} (h : Nat.card {x // P x} ≤ 1) [Finite α]
    {x y : α} (hx : P x) (hy : P y) (hxy : x ≠ y) : False := by
  have : Subsingleton {x // P x} := (Finite.card_le_one_iff_subsingleton).mp h
  exact hxy (congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : {x // P x}) ⟨y, hy⟩))

theorem false_of_card_le_two {α : Type*} {P : α → Prop} (h : Nat.card {x // P x} ≤ 2) [Finite α]
    {x y z : α} (hx : P x) (hy : P y) (hz : P z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    False := by
  have := Finite.of_injective (fun x : {x // P x} ↦ x.1) Subtype.val_injective
  let f : Fin 3 → {x // P x} := ![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, Ne.symm hxy, Ne.symm hxz,
      Ne.symm hyz]
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

section Key

variable (hSB : D.toPathData.IsSpecialBiserial) (hs : w.IsString D)
include hSB hs

omit hSB in
/-- A directed walk of length two through the diagram spells a nonzero path. -/
theorem pval_pair_ne_zero {i m j : Fin (w.len + 1)} {a c : D.Q.A}
    (h1 : w.next a i = some m) (h2 : w.next c m = some j) :
    D.pval (D.Q.src a) [a, c] ≠ 0 := by
  intro h0
  have hsrc : (w.coeffQuiver D).vtx i = D.Q.src a := (w.coeffQuiver D).next_src a i m h1
  have := hs.2 (D.Q.src a) [a, c] h0 i hsrc
  simp [MonomialData.CoeffQuiver.follow, coeffQuiver, h1, h2] at this

/-- **The key position lemma.** -/
theorem isEnd_and_outExt {b : D.Q.A} {q : Fin (w.len + 1)} (hq : w.vtx q = D.Q.src b)
    (hnb : w.next b q = none)
    (hfree : ∀ a i, D.toPathData.Forbidden a b → w.next a i ≠ some q) :
    w.IsEnd q ∧ w.OutExt q b := by
  classical
  obtain ⟨hout, hin, hsucc, hpred⟩ := hSB
  -- incoming edges are allowed predecessors of `b`
  have hinc : ∀ (a : D.Q.A) (i : Fin (w.len + 1)), w.next a i = some q →
      D.pval (D.Q.src a) [a, b] ≠ 0 := by
    intro a i h h0
    exact hfree a i ⟨hq.symm.trans ((w.coeffQuiver D).next_tgt a i q h), h0⟩ h
  -- outgoing edges have labels different from `b`
  have hout' : ∀ (a : D.Q.A) (j : Fin (w.len + 1)), w.next a q = some j → a ≠ b := by
    rintro a j h rfl; rw [hnb] at h; cases h
  have hext : w.OutExt q b := by
    refine ⟨hq.symm, fun l hl ↦ ?_, fun l hl ↦ ?_⟩
    · obtain ⟨a, d⟩ := l
      cases d
      · obtain ⟨j, hj, -⟩ := w.next_of_leftL_inv hs.1 hl
        simpa using (hout' a j hj).symm
      · obtain ⟨i, hi, -⟩ := w.next_to_of_leftL_dir hs.1 hl
        simpa using hinc a i hi
    · obtain ⟨a, d⟩ := l
      cases d
      · obtain ⟨i, hi, -⟩ := w.next_to_of_rightL_inv hs.1 hl
        simpa using hinc a i hi
      · obtain ⟨j, hj, -⟩ := w.next_of_rightL_dir hs.1 hl
        simpa using (hout' a j hj).symm
  refine ⟨?_, hext⟩
  by_contra hend
  simp only [IsEnd, not_or] at hend
  have hlt := q.isLt
  obtain ⟨⟨a1, d1⟩, h1⟩ := w.leftL_eq_some (p := q) (by omega)
  obtain ⟨⟨a2, d2⟩, h2⟩ := w.rightL_eq_some (p := q) (by omega)
  -- the two letters are different as edges at `q`
  have hfork : ¬ (a1 = a2 ∧ d1 ≠ d2) := by
    have := hs.1 (q.val - 1) (by simp only [len] at hlt hend; omega)
    unfold leftL at h1; unfold rightL at h2
    rw [dif_pos (by omega)] at h1
    rw [dif_pos (by simp only [len] at hlt hend; omega)] at h2
    have e1 := Option.some.inj h1
    have e2 := Option.some.inj h2
    simp only [show q.val - 1 + 1 = q.val by omega] at this
    rw [e1, e2] at this
    exact this
  cases d1 <;> cases d2
  · -- left inverse (outgoing `a1`), right inverse (incoming `a2`): walk `a2 a1`
    obtain ⟨j, hj, -⟩ := w.next_of_leftL_inv hs.1 h1
    obtain ⟨i, hi, -⟩ := w.next_to_of_rightL_inv hs.1 h2
    have h12 := w.pval_pair_ne_zero hs hi hj
    have hb := hinc a2 i hi
    have hne := hout' a1 j hj
    exact false_of_card_le_one (hsucc a2) (x := b) (y := a1)
      ⟨hq.symm.trans ((w.coeffQuiver D).next_tgt a2 i q hi), hb⟩
      ⟨((w.coeffQuiver D).next_src a1 q j hj).symm.trans
        ((w.coeffQuiver D).next_tgt a2 i q hi), h12⟩ (Ne.symm hne)
  · -- left inverse (outgoing `a1`), right direct (outgoing `a2`): three arrows out of `src b`
    obtain ⟨j1, hj1, -⟩ := w.next_of_leftL_inv hs.1 h1
    obtain ⟨j2, hj2, -⟩ := w.next_of_rightL_dir hs.1 h2
    have hs1 : D.Q.src a1 = D.Q.src b := ((w.coeffQuiver D).next_src a1 q j1 hj1).symm.trans hq
    have hs2 : D.Q.src a2 = D.Q.src b := ((w.coeffQuiver D).next_src a2 q j2 hj2).symm.trans hq
    have h12 : a1 ≠ a2 := fun h ↦ hfork ⟨h, by decide⟩
    exact false_of_card_le_two (hout (D.Q.src b)) (x := b) (y := a1) (z := a2) rfl hs1 hs2
      (Ne.symm (hout' a1 j1 hj1)) (Ne.symm (hout' a2 j2 hj2)) h12
  · -- left direct (incoming `a1`), right inverse (incoming `a2`): two allowed predecessors
    obtain ⟨i1, hi1, -⟩ := w.next_to_of_leftL_dir hs.1 h1
    obtain ⟨i2, hi2, -⟩ := w.next_to_of_rightL_inv hs.1 h2
    have h12 : a1 ≠ a2 := fun h ↦ hfork ⟨h, by decide⟩
    exact false_of_card_le_one (hpred b) (x := a1) (y := a2)
      ⟨hq.symm.trans ((w.coeffQuiver D).next_tgt a1 i1 q hi1), hinc a1 i1 hi1⟩
      ⟨hq.symm.trans ((w.coeffQuiver D).next_tgt a2 i2 q hi2), hinc a2 i2 hi2⟩ h12
  · -- left direct (incoming `a1`), right direct (outgoing `a2`): walk `a1 a2`
    obtain ⟨i, hi, -⟩ := w.next_to_of_leftL_dir hs.1 h1
    obtain ⟨j, hj, -⟩ := w.next_of_rightL_dir hs.1 h2
    have h12 := w.pval_pair_ne_zero hs hi hj
    exact false_of_card_le_one (hsucc a1) (x := b) (y := a2)
      ⟨hq.symm.trans ((w.coeffQuiver D).next_tgt a1 i q hi), hinc a1 i hi⟩
      ⟨((w.coeffQuiver D).next_src a2 q j hj).symm.trans
        ((w.coeffQuiver D).next_tgt a1 i q hi), h12⟩ (Ne.symm (hout' a2 j hj))

/-- **The key position lemma, mirror form.** -/
theorem isEnd_and_inExt {b : D.Q.A} {q : Fin (w.len + 1)} (hq : w.vtx q = D.Q.tgt b)
    (hnb : ∀ i, w.next b i ≠ some q)
    (hfree : ∀ c j, D.toPathData.Forbidden b c → w.next c q ≠ some j) :
    w.IsEnd q ∧ w.InExt q b := by
  classical
  obtain ⟨hout, hin, hsucc, hpred⟩ := hSB
  -- outgoing edges are allowed successors of `b`
  have houtg : ∀ (c : D.Q.A) (j : Fin (w.len + 1)), w.next c q = some j →
      D.pval (D.Q.src b) [b, c] ≠ 0 := by
    intro c j h h0
    exact hfree c j ⟨((w.coeffQuiver D).next_src c q j h).symm.trans hq, h0⟩ h
  -- incoming edges have labels different from `b`
  have hinc' : ∀ (a : D.Q.A) (i : Fin (w.len + 1)), w.next a i = some q → a ≠ b := by
    rintro a i h rfl; exact hnb i h
  have hext : w.InExt q b := by
    refine ⟨hq.symm, fun l hl ↦ ?_, fun l hl ↦ ?_⟩
    · obtain ⟨a, d⟩ := l
      cases d
      · obtain ⟨j, hj, -⟩ := w.next_of_leftL_inv hs.1 hl
        simpa using houtg a j hj
      · obtain ⟨i, hi, -⟩ := w.next_to_of_leftL_dir hs.1 hl
        simpa using (hinc' a i hi).symm
    · obtain ⟨a, d⟩ := l
      cases d
      · obtain ⟨i, hi, -⟩ := w.next_to_of_rightL_inv hs.1 hl
        simpa using (hinc' a i hi).symm
      · obtain ⟨j, hj, -⟩ := w.next_of_rightL_dir hs.1 hl
        simpa using houtg a j hj
  refine ⟨?_, hext⟩
  by_contra hend
  simp only [IsEnd, not_or] at hend
  have hlt := q.isLt
  obtain ⟨⟨a1, d1⟩, h1⟩ := w.leftL_eq_some (p := q) (by omega)
  obtain ⟨⟨a2, d2⟩, h2⟩ := w.rightL_eq_some (p := q) (by omega)
  have hfork : ¬ (a1 = a2 ∧ d1 ≠ d2) := by
    have := hs.1 (q.val - 1) (by simp only [len] at hlt hend; omega)
    unfold leftL at h1; unfold rightL at h2
    rw [dif_pos (by omega)] at h1
    rw [dif_pos (by simp only [len] at hlt hend; omega)] at h2
    have e1 := Option.some.inj h1
    have e2 := Option.some.inj h2
    simp only [show q.val - 1 + 1 = q.val by omega] at this
    rw [e1, e2] at this
    exact this
  cases d1 <;> cases d2
  · -- outgoing `a1`, incoming `a2`: walk `a2 a1`; `a1` has predecessors `b` and `a2`
    obtain ⟨j, hj, -⟩ := w.next_of_leftL_inv hs.1 h1
    obtain ⟨i, hi, -⟩ := w.next_to_of_rightL_inv hs.1 h2
    have h21 := w.pval_pair_ne_zero hs hi hj
    exact false_of_card_le_one (hpred a1) (x := b) (y := a2)
      ⟨((w.coeffQuiver D).next_src a1 q j hj).symm.trans hq, houtg a1 j hj⟩
      ⟨((w.coeffQuiver D).next_src a1 q j hj).symm.trans
        ((w.coeffQuiver D).next_tgt a2 i q hi), h21⟩ (Ne.symm (hinc' a2 i hi))
  · -- two outgoing edges: two allowed successors of `b`
    obtain ⟨j1, hj1, -⟩ := w.next_of_leftL_inv hs.1 h1
    obtain ⟨j2, hj2, -⟩ := w.next_of_rightL_dir hs.1 h2
    have h12 : a1 ≠ a2 := fun h ↦ hfork ⟨h, by decide⟩
    exact false_of_card_le_one (hsucc b) (x := a1) (y := a2)
      ⟨((w.coeffQuiver D).next_src a1 q j1 hj1).symm.trans hq, houtg a1 j1 hj1⟩
      ⟨((w.coeffQuiver D).next_src a2 q j2 hj2).symm.trans hq, houtg a2 j2 hj2⟩ h12
  · -- two incoming edges: three arrows into `tgt b`
    obtain ⟨i1, hi1, -⟩ := w.next_to_of_leftL_dir hs.1 h1
    obtain ⟨i2, hi2, -⟩ := w.next_to_of_rightL_inv hs.1 h2
    have ht1 : D.Q.tgt a1 = D.Q.tgt b := ((w.coeffQuiver D).next_tgt a1 i1 q hi1).symm.trans hq
    have ht2 : D.Q.tgt a2 = D.Q.tgt b := ((w.coeffQuiver D).next_tgt a2 i2 q hi2).symm.trans hq
    have h12 : a1 ≠ a2 := fun h ↦ hfork ⟨h, by decide⟩
    exact false_of_card_le_two (hin (D.Q.tgt b)) (x := b) (y := a1) (z := a2) rfl ht1 ht2
      (Ne.symm (hinc' a1 i1 hi1)) (Ne.symm (hinc' a2 i2 hi2)) h12
  · -- incoming `a1`, outgoing `a2`: walk `a1 a2`; `a2` has predecessors `b` and `a1`
    obtain ⟨i, hi, -⟩ := w.next_to_of_leftL_dir hs.1 h1
    obtain ⟨j, hj, -⟩ := w.next_of_rightL_dir hs.1 h2
    have h12 := w.pval_pair_ne_zero hs hi hj
    exact false_of_card_le_one (hpred a2) (x := b) (y := a1)
      ⟨((w.coeffQuiver D).next_src a2 q j hj).symm.trans hq, houtg a2 j hj⟩
      ⟨((w.coeffQuiver D).next_src a2 q j hj).symm.trans
        ((w.coeffQuiver D).next_tgt a1 i q hi), h12⟩ (Ne.symm (hinc' a1 i hi))

end Key

end Word

end BrickAccessibility
