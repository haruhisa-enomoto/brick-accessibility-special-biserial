module

public import BrickAccessibility.Section3.FaithfulData

/-!
# Proposition 3.8: gentleness of the faithful quotient

Steps 2 and 3 of the proof of Proposition 3.8 for `faithfulData`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hw : w.IsString D)
include hw

theorem faithful_isAdmissible (hD : D.IsStringAlgebra) :
    (w.faithfulData hw).toPathData.IsAdmissible := by
  obtain ⟨-, -, N, hN⟩ := hD.1
  refine ⟨(w.faithfulData hw).e_ne, fun a h ↦ a.2 (Ideal.Quotient.eq_zero_iff_mem.mp h), N,
    fun x l hl ↦ ?_⟩
  change (D.subPathData (w.ann hw)).pval x l = 0
  have e : D.pval x.1 (l.map Subtype.val) = 0 := hN _ _ (by simpa using hl)
  rw [D.subPathData_pval, e, map_zero]

theorem allowed_of_faithful {a b : (w.faithfulData hw).Q.A}
    (h : (w.faithfulData hw).toPathData.Allowed a b) : D.toPathData.Allowed a.1 b.1 := by
  refine ⟨congrArg Subtype.val h.1, fun h0 ↦ h.2 ?_⟩
  change (D.subPathData (w.ann hw)).pval _ _ = 0
  rw [D.subPathData_pval]
  have : D.pval (D.Q.src a.1) [a.1, b.1] = 0 := h0
  rw [show [a, b].map Subtype.val = [a.1, b.1] from rfl]
  change Ideal.Quotient.mk _ (D.pval (D.Q.src a.1) [a.1, b.1]) = 0
  rw [this, map_zero]

theorem faithful_isSpecialBiserial (hD : D.IsStringAlgebra) :
    (w.faithfulData hw).toPathData.IsSpecialBiserial := by
  obtain ⟨-, h1, h2, h3, h4⟩ := hD
  refine ⟨fun x ↦ ?_, fun y ↦ ?_, fun a ↦ ?_, fun b ↦ ?_⟩
  · refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (w.faithfulData hw).Q.A // (w.faithfulData hw).Q.src a = x} ↦
        (⟨a.1.1, congrArg Subtype.val a.2⟩ : {a : D.Q.A // D.Q.src a = x.1})) ?_) (h1 x.1)
    intro a a' h; exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  · refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (w.faithfulData hw).Q.A // (w.faithfulData hw).Q.tgt a = y} ↦
        (⟨a.1.1, congrArg Subtype.val a.2⟩ : {a : D.Q.A // D.Q.tgt a = y.1})) ?_) (h2 y.1)
    intro a a' h; exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  · refine le_trans (Nat.card_le_card_of_injective
      (fun b : {b // (w.faithfulData hw).toPathData.Allowed a b} ↦
        (⟨b.1.1, w.allowed_of_faithful hw b.2⟩ : {b : D.Q.A // D.toPathData.Allowed a.1 b})) ?_)
      (h3 a.1)
    intro b b' h; exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  · refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a // (w.faithfulData hw).toPathData.Allowed a b} ↦
        (⟨a.1.1, w.allowed_of_faithful hw a.2⟩ : {a : D.Q.A // D.toPathData.Allowed a b.1})) ?_)
      (h4 b.1)
    intro a a' h; exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

theorem seg_of_arrow (a : (w.faithfulData hw).Q.A) : ∃ d r, w.Seg d r [a.1] := by
  obtain ⟨i, j, h⟩ := w.exists_move hw a.2
  refine w.seg_of_occurs hw (x := D.Q.src a.1)
    ⟨i, (w.coeffQuiver D).next_src _ _ _ h, j, (w.coeffQuiver D).coef a.1 i * 1, ?_⟩
  exact (w.coeffQuiver D).follow_cons_eq_some.mpr ⟨j, 1, h, rfl, rfl⟩

/-- Step 2 of Proposition 3.8. -/
theorem faithful_isQuadratic (hD : D.IsStringAlgebra) (hb : IsBrick B (w.stringModule D hw)) :
    (w.faithfulData hw).IsQuadratic := by
  intro a l hwalk
  have hpv : (w.faithfulData hw).pval ((w.faithfulData hw).Q.src a) (a :: l) ≠ 0 ↔
      w.Occurs (D.Q.src a.1) ((a :: l).map Subtype.val) :=
    w.faithful_pval_ne_zero_iff hw _ _
  have hpair : ∀ (i : ℕ) (hi : i + 1 < (a :: l).length),
      (w.faithfulData hw).pval ((w.faithfulData hw).Q.src (a :: l)[i]) [(a :: l)[i], (a :: l)[i + 1]]
        ≠ 0 ↔ ∃ d r, w.Seg d r [((a :: l)[i]).1, ((a :: l)[i + 1]).1] := by
    intro i hi
    rw [w.faithful_pval_ne_zero_iff hw]
    constructor
    · exact w.seg_of_occurs hw
    · rintro ⟨d, r, hs⟩; exact w.occurs_of_seg hw hs
  constructor
  · intro h0
    by_contra hno
    push Not at hno
    apply (hpv.mpr ?_) h0
    have hne : (a :: l).map Subtype.val ≠ [] := by simp
    obtain ⟨d, r, hs⟩ := w.seg_of_chain hw hD.2 hb _ hne
      (fun x hx ↦ by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        exact w.seg_of_arrow hw y)
      (by
        rw [List.isChain_iff_getElem]
        intro i hi
        have hi' : i + 1 < (a :: l).length := by simpa using hi
        simp only [List.getElem_map]
        refine (hpair i hi').mp fun h ↦ hno i hi' ⟨?_, h⟩
        exact Statement.FinQuiver.isWalk_map_true hwalk i hi')
    exact w.occurs_of_seg hw (a := a.1) (l := l.map Subtype.val) hs
  · rintro ⟨i, hi, hF⟩
    by_contra h0
    replace h0 := hpv.mp h0
    obtain ⟨d, r, hs⟩ := w.seg_of_occurs hw h0
    have hiL : i + 1 < ((a :: l).map Subtype.val).length := by simpa using hi
    have h2 := (hs.drop (n := i) (by omega)).take 2
    rw [List.take_two_drop _ i hiL] at h2
    simp only [List.getElem_map] at h2
    exact (hpair i hi).mpr ⟨d, _, h2⟩ hF.2

theorem not_occurs_of_forbidden {a b : (w.faithfulData hw).Q.A}
    (h : (w.faithfulData hw).toPathData.Forbidden a b) :
    D.Q.src b.1 = D.Q.tgt a.1 ∧ ¬ w.Occurs (D.Q.src a.1) [a.1, b.1] :=
  ⟨congrArg Subtype.val h.1, fun ho ↦ (w.faithful_pval_ne_zero_iff hw _ [a, b]).mpr ho h.2⟩

/-- Step 3 of Proposition 3.8, for successors. -/
theorem faithful_forbidden_succ (hD : D.IsStringAlgebra) (hb : IsBrick B (w.stringModule D hw))
    (a : (w.faithfulData hw).Q.A) :
    Nat.card {b // (w.faithfulData hw).toPathData.Forbidden a b} ≤ 1 := by
  classical
  have hSB := hD.2
  set C := w.coeffQuiver D
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun ⟨b, hb'⟩ ⟨c, hc'⟩ ↦ Subtype.ext ?_⟩
  by_contra hbc
  obtain ⟨hbs, hbo⟩ := w.not_occurs_of_forbidden hw hb'
  obtain ⟨hcs, hco⟩ := w.not_occurs_of_forbidden hw hc'
  have hbc' : b.1 ≠ c.1 := fun h ↦ hbc (Subtype.ext h)
  obtain ⟨i, j, hij⟩ := w.exists_move hw a.2
  have hjv : w.vtx j = D.Q.tgt a.1 := C.next_tgt _ _ _ hij
  have hn := w.len_pos_of_move hw hij
  -- `j` is a socle position
  have hsoc : ∀ y, w.next y j = none := by
    intro y
    by_contra hy
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hy
    have hys : D.Q.src y = D.Q.tgt a.1 := (C.next_src _ _ _ hl).symm.trans hjv
    have hocc := w.occurs_of_moves hij hl
    by_cases hyb : y = b.1
    · subst hyb; exact hbo hocc
    by_cases hyc : y = c.1
    · subst hyc; exact hco hocc
    exact Word.false_of_card_le_two (hSB.1 (D.Q.tgt a.1)) (x := y) (y := b.1) (z := c.1)
      hys hbs hcs hyb hyc hbc'
  -- some position over the same vertex is a top position
  obtain ⟨p, hpv, hp⟩ : ∃ p, w.vtx p = D.Q.tgt a.1 ∧ ∀ y i', w.next y i' ≠ some p := by
    obtain ⟨p, q, hpq⟩ := w.exists_move hw b.2
    obtain ⟨p2, q2, hpq2⟩ := w.exists_move hw c.2
    have hpv : w.vtx p = D.Q.tgt a.1 := (C.next_src _ _ _ hpq).trans hbs
    have hp2v : w.vtx p2 = D.Q.tgt a.1 := (C.next_src _ _ _ hpq2).trans hcs
    by_contra hno
    push Not at hno
    obtain ⟨d, i1, hd⟩ := hno p hpv
    obtain ⟨d2, i2, hd2⟩ := hno p2 hp2v
    have hdt : D.Q.tgt d = D.Q.tgt a.1 := (C.next_tgt _ _ _ hd).symm.trans hpv
    have hd2t : D.Q.tgt d2 = D.Q.tgt a.1 := (C.next_tgt _ _ _ hd2).symm.trans hp2v
    have hda : d ≠ a.1 := by rintro rfl; exact hbo (w.occurs_of_moves hd hpq)
    have hd2a : d2 ≠ a.1 := by rintro rfl; exact hco (w.occurs_of_moves hd2 hpq2)
    have hdd : d = d2 := by
      by_contra hdd
      exact Word.false_of_card_le_two (hSB.2.1 (D.Q.tgt a.1)) (x := d) (y := d2) (z := a.1)
        hdt hd2t rfl hdd hda hd2a
    subst hdd
    exact hbc' (w.eq_of_allowed hw hSB (w.allowed_of_moves hw hd hpq)
      (w.allowed_of_moves hw hd2 hpq2))
  exact w.vtx_ne_of_top_socle hw hb hn p j hp hsoc (hpv.trans hjv.symm)

/-- Step 3 of Proposition 3.8, for predecessors. -/
theorem faithful_forbidden_pred (hD : D.IsStringAlgebra) (hb : IsBrick B (w.stringModule D hw))
    (b : (w.faithfulData hw).Q.A) :
    Nat.card {a // (w.faithfulData hw).toPathData.Forbidden a b} ≤ 1 := by
  classical
  have hSB := hD.2
  set C := w.coeffQuiver D
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun ⟨a, ha'⟩ ⟨c, hc'⟩ ↦ Subtype.ext ?_⟩
  by_contra hac
  obtain ⟨has, hao⟩ := w.not_occurs_of_forbidden hw ha'
  obtain ⟨hcs, hco⟩ := w.not_occurs_of_forbidden hw hc'
  have hac' : a.1 ≠ c.1 := fun h ↦ hac (Subtype.ext h)
  obtain ⟨i, j, hij⟩ := w.exists_move hw b.2
  have hiv : w.vtx i = D.Q.src b.1 := C.next_src _ _ _ hij
  have hn := w.len_pos_of_move hw hij
  -- `i` is a top position
  have htop : ∀ y s, w.next y s ≠ some i := by
    intro y s hy
    have hyt : D.Q.tgt y = D.Q.src b.1 := (C.next_tgt _ _ _ hy).symm.trans hiv
    have hocc := w.occurs_of_moves hy hij
    by_cases hya : y = a.1
    · subst hya; exact hao hocc
    by_cases hyc : y = c.1
    · subst hyc; exact hco hocc
    exact Word.false_of_card_le_two (hSB.2.1 (D.Q.src b.1)) (x := y) (y := a.1) (z := c.1)
      hyt has.symm hcs.symm hya hyc hac'
  -- some position over the same vertex is a socle position
  obtain ⟨q, hqv, hq⟩ : ∃ q, w.vtx q = D.Q.src b.1 ∧ ∀ y, w.next y q = none := by
    obtain ⟨p, q, hpq⟩ := w.exists_move hw a.2
    obtain ⟨p2, q2, hpq2⟩ := w.exists_move hw c.2
    have hqv : w.vtx q = D.Q.src b.1 := (C.next_tgt _ _ _ hpq).trans has.symm
    have hq2v : w.vtx q2 = D.Q.src b.1 := (C.next_tgt _ _ _ hpq2).trans hcs.symm
    by_contra hno
    push Not at hno
    obtain ⟨d, hd⟩ := hno q hqv
    obtain ⟨d2, hd2⟩ := hno q2 hq2v
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hd
    obtain ⟨l2, hl2⟩ := Option.ne_none_iff_exists'.mp hd2
    have hds : D.Q.src d = D.Q.src b.1 := (C.next_src _ _ _ hl).symm.trans hqv
    have hd2s : D.Q.src d2 = D.Q.src b.1 := (C.next_src _ _ _ hl2).symm.trans hq2v
    have hdb : d ≠ b.1 := by rintro rfl; exact hao (w.occurs_of_moves hpq hl)
    have hd2b : d2 ≠ b.1 := by rintro rfl; exact hco (w.occurs_of_moves hpq2 hl2)
    have hdd : d = d2 := by
      by_contra hdd
      exact Word.false_of_card_le_two (hSB.1 (D.Q.src b.1)) (x := d) (y := d2) (z := b.1)
        hds hd2s rfl hdd hdb hd2b
    subst hdd
    exact hac' (w.eq_of_allowed' hw hSB (w.allowed_of_moves hw hpq hl)
      (w.allowed_of_moves hw hpq2 hl2))
  exact w.vtx_ne_of_top_socle hw hb hn i q htop hq (hiv.trans hqv.symm)

/-- **Proposition 3.8** for `faithfulData`. -/
theorem faithful_isGentle (hD : D.IsStringAlgebra) (hb : IsBrick B (w.stringModule D hw)) :
    (w.faithfulData hw).IsGentle :=
  ⟨⟨w.faithful_isAdmissible hw hD, w.faithful_isSpecialBiserial hw hD⟩,
    w.faithful_isQuadratic hw hD hb, w.faithful_forbidden_succ hw hD hb,
    w.faithful_forbidden_pred hw hD hb⟩

end Word

end BrickAccessibility
