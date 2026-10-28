module

public import BrickAccessibility.StringQuotient.Socle
public import BrickAccessibility.StringQuotient.SubQuiver

/-!
# The string quotient

`J` is the span of the longest paths at binomial vertices. It is a two-sided ideal killed
by paths of positive length on both sides, and `A ⧸ J` carries monomial data on the quiver
of arrows outside `J` (`quotData`), which is a string algebra (`quotData_isString`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

namespace PathData

variable {k : Type*} [Field k] {Q : FinQuiver} {A : Type*} [Ring A] [Algebra k A]
  {D : PathData Q A} (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial)

open Classical in
/-- The longest path at a binomial vertex, and zero elsewhere. -/
def zz (x : Q.V) : A :=
  if h : Bin (k := k) hadm x then D.pval x (Pm hadm h.choose) else 0

theorem zz_of_not {x : Q.V} (h : ¬ Bin (k := k) hadm x) : zz (k := k) hadm x = 0 := by
  rw [zz, dif_neg h]

theorem zz_spec {x : Q.V} (h : Bin (k := k) hadm x) : ∃ a b, a ≠ b ∧ Q.src a = x ∧
    Q.src b = x ∧ D.pval x (Pm hadm a) ∈ Submodule.span k {D.pval x (Pm hadm b)} ∧
    zz (k := k) hadm x = D.pval x (Pm hadm a) := by
  obtain ⟨b, h1⟩ := h.choose_spec
  exact ⟨h.choose, b, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, by rw [zz, dif_pos h]⟩

/-- The ideal spanned by the longest paths at binomial vertices. -/
def Jsp : Submodule k A := Submodule.span k (Set.range (zz (k := k) hadm))

theorem zz_mul_e (x v : Q.V) :
    zz (k := k) hadm x * D.e v = if x = v then zz (k := k) hadm x else 0 := by
  by_cases h : Bin (k := k) hadm x
  · rw [zz, dif_pos h, pval_mul_e_eq]
    split_ifs with hxv
    · subst hxv; rfl
    · rfl
  · rw [zz_of_not hadm h, zero_mul]; split_ifs <;> rfl

theorem zz_mem_rad (x : Q.V) : zz (k := k) hadm x ∈ D.RadGe k 1 := by
  by_cases h : Bin (k := k) hadm x
  · rw [zz, dif_pos h]; exact pval_mem_rad x (List.cons_ne_nil _ _)
  · rw [zz_of_not hadm h]; exact Submodule.zero_mem _

/-- Paths of positive length kill `zz` from the left. -/
theorem path_mul_zz (x y : Q.V) {σ : List Q.A} (hσ : σ ≠ []) :
    D.pval y σ * zz (k := k) hadm x = 0 := by
  by_cases h : Bin (k := k) hadm x
  · rw [zz, dif_pos h, D.pval_mul_pval]
    split_ifs
    · rw [Pm, List.cons_append]
      exact pval_long hadm (by simp only [List.length_append]; have := List.length_pos_iff.mpr hσ; omega)
    · rfl
  · rw [zz_of_not hadm h, mul_zero]

include hsb in
/-- Paths of positive length kill `zz` from the right. -/
theorem zz_mul_path (x y : Q.V) {σ : List Q.A} (hσ : σ ≠ []) :
    zz (k := k) hadm x * D.pval y σ = 0 := by
  by_cases h : Bin (k := k) hadm x
  · obtain ⟨a, b, hab, hxa, hxb, hmem, hz⟩ := zz_spec hadm h
    rw [hz, D.pval_mul_pval]
    split_ifs with hx
    · by_contra hne
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
      have h1 : D.pval y (σ ++ Pm hadm a) = μ • D.pval y (σ ++ Pm hadm b) := by
        rw [D.pval_append, D.pval_append, ← hx, ← hμ, smul_mul_assoc]
      have hne' : D.pval y (σ ++ Pm hadm b) ≠ 0 := fun h' ↦ hne (by rw [h1, h', smul_zero])
      obtain ⟨σ0, d, rfl⟩ : ∃ σ0 d, σ = σ0 ++ [d] := by
        rcases List.eq_nil_or_concat σ with h | ⟨L, c, h⟩
        · exact absurd h hσ
        · exact ⟨L, c, by rw [h, List.concat_eq_append]⟩
      have ha : D.Allowed d a := D.allowed_of_ne (l₁ := σ0) (l₂ := tl hadm a)
        (by simpa [Pm] using hne)
      have hb : D.Allowed d b := D.allowed_of_ne (l₁ := σ0) (l₂ := tl hadm b)
        (by simpa [Pm] using hne')
      exact hab (succ_unique hsb ha hb)
    · rfl
  · rw [zz_of_not hadm h, zero_mul]

theorem e_mul_zz (v x : Q.V) : D.e v * zz (k := k) hadm x ∈ Submodule.span k {zz (k := k) hadm x} := by
  by_cases h : Bin (k := k) hadm x
  · have e1 : D.e v * zz (k := k) hadm x = D.pval v [] * zz (k := k) hadm x := rfl
    rw [e1, zz, dif_pos h, D.pval_mul_pval]
    split_ifs
    · rw [List.append_nil]; exact Submodule.mem_span_singleton_self _
    · exact Submodule.zero_mem _
  · rw [zz_of_not hadm h, mul_zero]; exact Submodule.zero_mem _

variable (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
include hspan

theorem mul_zz_mem (c : A) (x : Q.V) :
    c * zz (k := k) hadm x ∈ Submodule.span k {zz (k := k) hadm x} := by
  have hc : c ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
      obtain ⟨⟨y, l⟩, rfl⟩ := hc
      cases l with
      | nil => exact e_mul_zz hadm y x
      | cons a l => rw [path_mul_zz hadm x y (List.cons_ne_nil a l)]; exact Submodule.zero_mem _
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add c c' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul μ c _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ μ h

include hsb in
theorem zz_mul_mem (c : A) (x : Q.V) :
    zz (k := k) hadm x * c ∈ Submodule.span k {zz (k := k) hadm x} := by
  have hc : c ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
      obtain ⟨⟨y, l⟩, rfl⟩ := hc
      cases l with
      | nil =>
          show zz (k := k) hadm x * D.e y ∈ _
          rw [zz_mul_e]
          split_ifs
          · exact Submodule.mem_span_singleton_self _
          · exact Submodule.zero_mem _
      | cons a l =>
          rw [zz_mul_path hadm hsb x y (List.cons_ne_nil a l)]; exact Submodule.zero_mem _
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add c c' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
  | smul μ c _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ μ h

omit hspan in
theorem span_zz_le (x : Q.V) :
    Submodule.span k {zz (k := k) hadm x} ≤ Jsp (k := k) hadm := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.subset_span ⟨x, rfl⟩

theorem mul_mem_J (c : A) {j : A} (hj : j ∈ Jsp (k := k) hadm) : c * j ∈ Jsp (k := k) hadm := by
  induction hj using Submodule.span_induction with
  | mem j hj => obtain ⟨x, rfl⟩ := hj; exact span_zz_le hadm x (mul_zz_mem hadm hspan c x)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add j j' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
  | smul μ j _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ μ h

include hsb in
theorem J_mul_mem {j : A} (hj : j ∈ Jsp (k := k) hadm) (c : A) : j * c ∈ Jsp (k := k) hadm := by
  induction hj using Submodule.span_induction with
  | mem j hj =>
      obtain ⟨x, rfl⟩ := hj; exact span_zz_le hadm x (zz_mul_mem hadm hsb hspan c x)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add j j' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul μ j _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ μ h

/-- The ideal `J`. -/
def JI : Ideal A where
  carrier := Jsp (k := k) hadm
  add_mem' := (Jsp (k := k) hadm).add_mem
  zero_mem' := (Jsp (k := k) hadm).zero_mem
  smul_mem' c _ hj := mul_mem_J hadm hspan c hj

include hsb in
theorem JI_isTwoSided : (JI (k := k) hadm hspan).IsTwoSided :=
  ⟨fun c hj ↦ J_mul_mem hadm hsb hspan hj c⟩

omit hspan

theorem J_le_rad : Jsp (k := k) hadm ≤ D.RadGe k 1 := by
  rw [Jsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact zz_mem_rad hadm x

theorem path_mul_J (y : Q.V) {σ : List Q.A} (hσ : σ ≠ []) {j : A} (hj : j ∈ Jsp (k := k) hadm) :
    D.pval y σ * j = 0 := by
  induction hj using Submodule.span_induction with
  | mem j hj => obtain ⟨x, rfl⟩ := hj; exact path_mul_zz hadm x y hσ
  | zero => rw [mul_zero]
  | add j j' _ _ h h' => rw [mul_add, h, h', add_zero]
  | smul μ j _ h => rw [mul_smul_comm, h, smul_zero]

/-- The part of `J` inside `A e_x` is the line of `zz x`. -/
theorem J_mul_e {x : Q.V} {j : A} (hj : j ∈ Jsp (k := k) hadm) :
    j * D.e x ∈ Submodule.span k {zz (k := k) hadm x} := by
  induction hj using Submodule.span_induction with
  | mem j hj =>
      obtain ⟨y, rfl⟩ := hj
      rw [zz_mul_e]
      split_ifs with h
      · subst h; exact Submodule.mem_span_singleton_self _
      · exact Submodule.zero_mem _
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add j j' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul μ j _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ μ h

section Quot

variable [(JI (k := k) hadm hspan).IsTwoSided]
include hsb hspan

/-- **The monomial data of the string quotient `A ⧸ J`.** -/
def quotData : MonomialData k (A ⧸ JI (k := k) hadm hspan) where
  Q := D.subQuiver (JI (k := k) hadm hspan)
  toPathData := D.subPathData (JI (k := k) hadm hspan)
  span_pval := by
    set J := JI (k := k) hadm hspan
    rw [eq_top_iff]
    rintro c -
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hb : b ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ k J).toLinearMap) hb
    rw [Submodule.map_span] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨⟨x, l⟩, rfl⟩, rfl⟩
    by_cases h : D.pval x l ∈ J
    · have h0 : (Ideal.Quotient.mkₐ k J).toLinearMap (D.pval x l) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr h
      rw [h0]; exact Submodule.zero_mem _
    · obtain ⟨hx, l', rfl⟩ := D.exists_lift J x l h
      exact Submodule.subset_span ⟨(⟨x, hx⟩, l'), D.subPathData_pval _ _ _⟩
  linIndep := by
    classical
    set J := JI (k := k) hadm hspan
    rw [linearIndependent_iff']
    intro s g hsum i0 hi0
    let L : {p : (D.subQuiver J).V × List (D.subQuiver J).A //
      (D.subPathData J).pval p.1 p.2 ≠ 0} → List Q.A := fun i ↦ i.1.2.map Subtype.val
    let X : {p : (D.subQuiver J).V × List (D.subQuiver J).A //
      (D.subPathData J).pval p.1 p.2 ≠ 0} → Q.V := fun i ↦ i.1.1.1
    set x := X i0
    have hlift : ∑ i ∈ s, g i • D.pval (X i) (L i) ∈ Jsp (k := k) hadm := by
      have h1 : Ideal.Quotient.mkₐ k J (∑ i ∈ s, g i • D.pval (X i) (L i)) =
          ∑ i ∈ s, g i • (D.subPathData J).pval i.1.1 i.1.2 := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_smul, D.subPathData_pval]
        rfl
      exact Ideal.Quotient.eq_zero_iff_mem.mp (h1.trans hsum)
    set S := s.filter (fun i ↦ X i = x) with hSdef
    set w := ∑ i ∈ S, g i • D.pval x (L i) with hwdef
    have hw_eq : w = (∑ i ∈ s, g i • D.pval (X i) (L i)) * D.e x := by
      rw [hwdef, hSdef, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_mul_assoc, pval_mul_e_eq]
      split_ifs with h
      · rfl
      · rw [smul_zero]
    have hw : w ∈ Jsp (k := k) hadm := by rw [hw_eq]; exact J_mul_mem hadm hsb hspan hlift _
    have hwx : w ∈ Submodule.span k {zz (k := k) hadm x} := by
      rw [hw_eq]; exact J_mul_e hadm hlift
    set T := S.image L with hTdef
    let g' : List Q.A → k := fun l ↦ ∑ i ∈ S.filter (fun i ↦ L i = l), g i
    have hw' : w = ∑ l ∈ T, g' l • D.pval x l := by
      rw [hwdef, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := L)
        (fun i hi ↦ Finset.mem_image_of_mem L hi)]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(Finset.mem_filter.mp hi).2]
    have hinj : ∀ i ∈ S, ∀ j ∈ S, L i = L j → i = j := by
      intro i hi j hj hij
      have hx : X i = X j := ((Finset.mem_filter.mp hi).2).trans (Finset.mem_filter.mp hj).2.symm
      obtain ⟨⟨xi, li⟩, _⟩ := i
      obtain ⟨⟨xj, lj⟩, _⟩ := j
      have h2 : li = lj := (List.map_injective_iff.mpr Subtype.val_injective) hij
      have h1 : xi = xj := Subtype.ext hx
      subst h1; subst h2; rfl
    have hz := coeff_eq_zero hadm hsb T g' (x := x) (fun l hl ↦ by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
        have hXi : X i = x := (Finset.mem_filter.mp hi).2
        have hnot : D.pval x (L i) ∉ J := by
          intro hm
          apply i.2
          rw [D.subPathData_pval]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [← hXi] at hm; exact hm)
        refine ⟨fun h0 ↦ hnot (by rw [h0]; exact J.zero_mem), fun hb a ha ↦ hnot ?_⟩
        have hne : D.pval x (Pm hadm a) ≠ 0 := by
          rw [← ha]; intro h0; exact hnot (by rw [h0]; exact J.zero_mem)
        obtain ⟨a0, -, -, ha0, -, -, hz0⟩ := zz_spec hadm hb
        have hmem := tops_le hadm hsb hb ha0
          (Submodule.subset_span ⟨a, D.src_eq_of_ne (l := tl hadm a) hne, rfl⟩)
        rw [← hz0, ← ha] at hmem
        exact span_zz_le hadm x hmem)
      (fun y σ hσ ↦ by rw [← hw']; exact path_mul_J hadm y hσ hw)
      (by rw [← hw']; exact J_le_rad hadm hw)
      (fun hnb ↦ by
        rw [← hw']
        rw [zz_of_not hadm hnb, Submodule.span_singleton_eq_bot.mpr rfl] at hwx
        exact (Submodule.mem_bot k).mp hwx)
    have hi0S : i0 ∈ S := Finset.mem_filter.mpr ⟨hi0, rfl⟩
    have hg'0 : g' (L i0) = g i0 := by
      refine Finset.sum_eq_single_of_mem i0 (Finset.mem_filter.mpr ⟨hi0S, rfl⟩) fun j hj hne ↦ ?_
      have hj' := Finset.mem_filter.mp hj
      exact absurd (hinj j hj'.1 i0 hi0S hj'.2) hne
    rw [← hg'0]
    exact hz (L i0) (Finset.mem_image_of_mem L hi0S)
  e_ne v h := v.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)

/-- **The string quotient is a string algebra.** -/
theorem quotData_isString : (quotData hadm hsb hspan).IsStringAlgebra := by
  set J := JI (k := k) hadm hspan
  have hval : ∀ (x : (D.subQuiver J).V) (l : List (D.subQuiver J).A),
      (quotData hadm hsb hspan).toPathData.pval x l =
        Ideal.Quotient.mk J (D.pval x.1 (l.map Subtype.val)) :=
    D.subPathData_pval J
  have hall : ∀ a b : (D.subQuiver J).A, (quotData hadm hsb hspan).toPathData.Allowed a b →
      D.Allowed a.1 b.1 := by
    rintro a b ⟨h1, h2⟩
    refine ⟨congrArg Subtype.val h1, fun h ↦ h2 ?_⟩
    show (D.subPathData J).pval ((D.subQuiver J).src a) [a, b] = 0
    rw [D.subPathData_pval]
    simp only [List.map_cons, List.map_nil]
    rw [h, map_zero]
  refine ⟨⟨fun v h ↦ v.2 (Ideal.Quotient.eq_zero_iff_mem.mp h),
    fun a h ↦ a.2 (Ideal.Quotient.eq_zero_iff_mem.mp h), ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hadm.2.2
    refine ⟨N, fun (x : (D.subQuiver J).V) (l : List (D.subQuiver J).A) hl ↦ ?_⟩
    refine (hval x l).trans ?_
    rw [hN _ _ (by rw [List.length_map]; exact hl), map_zero]
  · intro x
    refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (D.subQuiver J).A // (D.subQuiver J).src a = x} ↦
        (⟨a.1.1, congrArg Subtype.val a.2⟩ : {a : Q.A // Q.src a = x.1}))
      (fun a b h ↦ Subtype.ext (Subtype.ext (congrArg (fun c ↦ c.1) h)))) (hsb.1 x.1)
  · intro y
    refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (D.subQuiver J).A // (D.subQuiver J).tgt a = y} ↦
        (⟨a.1.1, congrArg Subtype.val a.2⟩ : {a : Q.A // Q.tgt a = y.1}))
      (fun a b h ↦ Subtype.ext (Subtype.ext (congrArg (fun c ↦ c.1) h)))) (hsb.2.1 y.1)
  · intro a
    refine le_trans (Nat.card_le_card_of_injective
      (fun b : {b // (quotData hadm hsb hspan).toPathData.Allowed a b} ↦
        (⟨b.1.1, hall a b.1 b.2⟩ : {b : Q.A // D.Allowed a.1 b}))
      (fun b c h ↦ Subtype.ext (Subtype.ext (congrArg (fun c ↦ c.1) h)))) (hsb.2.2.1 a.1)
  · intro b
    refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a // (quotData hadm hsb hspan).toPathData.Allowed a b} ↦
        (⟨a.1.1, hall a.1 b a.2⟩ : {a : Q.A // D.Allowed a b.1}))
      (fun a c h ↦ Subtype.ext (Subtype.ext (congrArg (fun c ↦ c.1) h)))) (hsb.2.2.2 b.1)

end Quot

end PathData

end BrickAccessibility
