module

public import BrickAccessibility.Section3.SubQuiver
public import BrickAccessibility.Section3.Chains
public import BrickAccessibility.Section3.TopSocle
public import BrickAccessibility.Section4.Extending

/-!
# Proposition 3.8: the faithful quotient of a brick string module is gentle

`faithfulData` is the monomial data on `B ⧸ ann M(w)` given by the vertices and
arrows acting nonzero on `M(w)` (Step 1). Its relations are quadratic by
`seg_of_chain` (Step 2) and satisfy the gentle conditions by the top–socle
argument (Step 3, both halves done directly rather than by duality).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem Statement.FinQuiver.isWalk_map_true {Q : FinQuiver} {x : Q.V} {L : List Q.A}
    (h : Q.IsWalk x (L.map (·, true))) (i : ℕ) (hi : i + 1 < L.length) :
    Q.src L[i + 1] = Q.tgt L[i] := by
  induction L generalizing x i with
  | nil => simp at hi
  | cons a L ih =>
      obtain ⟨-, h⟩ := h
      cases i with
      | zero =>
          cases L with
          | nil => simp at hi
          | cons b L =>
              obtain ⟨hb, -⟩ := h
              simpa [Letter.src, Letter.tgt] using hb
      | succ i => exact ih h i (by simpa using hi)

theorem List.take_two_drop {α : Type*} (L : List α) (i : ℕ) (hi : i + 1 < L.length) :
    (L.drop i).take 2 = [L[i], L[i + 1]] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hi]
  rfl

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hw : w.IsString D)

/-- The annihilator of a string module. -/
abbrev ann : Ideal B := Module.annihilator B (w.stringModule D hw)

include hw

omit hw in
theorem occurs_of_moves {x y : D.Q.A} {i j l : Fin (w.len + 1)} (h1 : w.next x i = some j)
    (h2 : w.next y j = some l) : w.Occurs (D.Q.src x) [x, y] := by
  set C := w.coeffQuiver D
  have e1 : C.next x i = some j := h1
  have e2 : C.next y j = some l := h2
  refine ⟨i, C.next_src x i j e1, l, C.coef x i * (C.coef y j * 1), ?_⟩
  refine C.follow_cons_eq_some.mpr ⟨j, _, e1, ?_, rfl⟩
  exact C.follow_cons_eq_some.mpr ⟨l, 1, e2, rfl, rfl⟩

theorem exists_move {a : D.Q.A} (ha : D.α a ∉ w.ann hw) : ∃ i j, w.next a i = some j := by
  have key : D.pval (D.Q.src a) [a] = D.α a := D.toPathData.pval_single_src a
  rw [← key, w.pval_mem_annihilator_iff hw, not_not] at ha
  obtain ⟨r, -, s, c, hf⟩ := ha
  obtain ⟨j, c', hj, -, -⟩ := (w.coeffQuiver D).follow_cons_eq_some.mp hf
  exact ⟨r, j, hj⟩

theorem len_pos_of_move {a : D.Q.A} {i j : Fin (w.len + 1)} (h : w.next a i = some j) :
    0 < w.len := by
  have := w.next_val hw.1 h
  have := i.isLt; have := j.isLt
  omega

/-- Step 1 of Proposition 3.8: the monomial data of the faithful quotient. -/
@[reducible] def faithfulData : MonomialData k (B ⧸ w.ann hw) where
  Q := D.subQuiver (w.ann hw)
  toPathData := D.subPathData (w.ann hw)
  span_pval := by
    rw [eq_top_iff]
    rintro c -
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hb : b ∈ Submodule.span k (Set.range (fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2)) := by
      rw [D.span_pval]; trivial
    have := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ k (w.ann hw)).toLinearMap) hb
    rw [Submodule.map_span] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨⟨x, l⟩, rfl⟩, rfl⟩
    by_cases h : D.pval x l ∈ w.ann hw
    · have h0 : (Ideal.Quotient.mkₐ k (w.ann hw)).toLinearMap (D.pval x l) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr h
      rw [h0]; exact Submodule.zero_mem _
    · obtain ⟨hx, l', rfl⟩ := D.exists_lift _ x l h
      exact Submodule.subset_span ⟨(⟨x, hx⟩, l'), D.subPathData_pval _ _ _⟩
  linIndep := by
    set C := w.coeffQuiver D
    set R := C.toRep hw.2
    have hker : ∀ b ∈ w.ann hw, R.act b = 0 := fun b hb ↦
      LinearMap.ext fun m ↦ (Module.mem_annihilator.mp hb) (m : w.stringModule D hw)
    let φ := Ideal.Quotient.liftₐ (w.ann hw) R.act hker
    refine LinearIndependent.of_comp φ.toLinearMap ?_
    have hli := w.linIndep_pathAction hw
    let g : {p : (D.subQuiver (w.ann hw)).V × List (D.subQuiver (w.ann hw)).A //
        (D.subPathData (w.ann hw)).pval p.1 p.2 ≠ 0} →
        {p : D.Q.V × List D.Q.A // C.toPathData.pval p.1 p.2 ≠ 0} :=
      fun p ↦ ⟨(p.1.1.1, p.1.2.map Subtype.val), by
        rw [w.pathAction_ne_zero_iff hw, ← not_not (a := w.Occurs _ _),
          ← w.pval_mem_annihilator_iff hw]
        intro hmem; apply p.2
        rw [D.subPathData_pval]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem⟩
    have hg : Function.Injective g := by
      rintro ⟨⟨x, l⟩, _⟩ ⟨⟨x', l'⟩, _⟩ h
      simp only [g, Subtype.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have := (List.map_injective_iff.mpr Subtype.val_injective) h2
      exact Subtype.ext (Prod.ext (Subtype.ext h1) this)
    have hfun : (φ.toLinearMap ∘ fun p : {p : (D.subQuiver (w.ann hw)).V ×
          List (D.subQuiver (w.ann hw)).A // (D.subPathData (w.ann hw)).pval p.1 p.2 ≠ 0} ↦
          (D.subPathData (w.ann hw)).pval p.1.1 p.1.2) =
        (fun q : {p : D.Q.V × List D.Q.A // C.toPathData.pval p.1 p.2 ≠ 0} ↦
          C.toPathData.pval q.1.1 q.1.2) ∘ g := by
      funext p
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, g]
      rw [D.subPathData_pval, Ideal.Quotient.liftₐ_apply]
      exact R.actL_pval _ _
    rw [hfun]
    exact hli.comp g hg
  e_ne v h := v.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)

theorem faithful_pval_ne_zero_iff (x : (w.faithfulData hw).Q.V)
    (l : List (w.faithfulData hw).Q.A) :
    (w.faithfulData hw).pval x l ≠ 0 ↔ w.Occurs x.1 (l.map Subtype.val) := by
  have e : (w.faithfulData hw).pval x l =
      Ideal.Quotient.mk (w.ann hw) (D.pval x.1 (l.map Subtype.val)) :=
    D.subPathData_pval _ x l
  rw [e, Ne, Ideal.Quotient.eq_zero_iff_mem, w.pval_mem_annihilator_iff hw, not_not]

end Word

end BrickAccessibility
