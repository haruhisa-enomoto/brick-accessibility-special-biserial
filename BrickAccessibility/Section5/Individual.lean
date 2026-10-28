module

public import BrickAccessibility.Section5.Main
public import BrickAccessibility.Bridge.Presentation

/-!
# Remark 5.7: individual bricks

**Quotients.** Special biserial path data on `A` induce special biserial path data on every
quotient `A ⧸ J` by a two-sided ideal: keep the vertices and arrows that survive in `A ⧸ J`
(`PathData.survData`, `PathData.quot_isSpecialBiserial`).

**Individual bricks.** A nonsimple brick `M` over a special biserial algebra has a brick
submodule or quotient of dimension one less as soon as its faithful quotient is
representation-finite (`hasSmallerBrick_of_faithful`, `remark_5_7`): Theorem A applies over
the faithful quotient, which is special biserial and brick-finite, and Lemma 2.4 lifts the
result.

For right `Λ`-modules, that is left `Λᵐᵒᵖ`-modules, the faithful quotient `Λ / ann_Λ(M)` acts
through `Λᵐᵒᵖ ⧸ ann(M)`; its right modules are the left modules over this quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module Statement

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable {Q : FinQuiver} (D : PathData Q A) (J : Ideal A) [J.IsTwoSided]

namespace PathData

open Classical in
/-- The subquiver of vertices and arrows that survive in `A ⧸ J`. -/
def survQuiver : FinQuiver where
  V := {v : Q.V // Ideal.Quotient.mk J (D.e v) ≠ 0}
  A := {a : Q.A // Ideal.Quotient.mk J (D.α a) ≠ 0}
  src a := ⟨Q.src a.1, fun h ↦ a.2 (by rw [← D.α_mul_e, map_mul, h, mul_zero])⟩
  tgt a := ⟨Q.tgt a.1, fun h ↦ a.2 (by rw [← D.e_mul_α, map_mul, h, zero_mul])⟩

/-- **The path data of the quotient.** -/
def survData : PathData (D.survQuiver J) (A ⧸ J) where
  e v := Ideal.Quotient.mk J (D.e v.1)
  α a := Ideal.Quotient.mk J (D.α a.1)
  e_mul_e v w := by
    rw [← map_mul, D.e_mul_e]
    by_cases h : v = w
    · subst h; simp
    · have h' : v.1 ≠ w.1 := fun h'' ↦ h (Subtype.ext h'')
      rw [if_neg h, if_neg h', map_zero]
  sum_e := by
    classical
    have h0 : ∑ v : {v : Q.V // ¬ Ideal.Quotient.mk J (D.e v) ≠ 0}, Ideal.Quotient.mk J (D.e v.1) =
        0 := Finset.sum_eq_zero fun v _ ↦ not_not.mp v.2
    have h := Fintype.sum_subtype_add_sum_subtype (fun v : Q.V ↦ Ideal.Quotient.mk J (D.e v) ≠ 0)
      (fun v ↦ Ideal.Quotient.mk J (D.e v))
    rw [h0, add_zero, ← map_sum (Ideal.Quotient.mk J) (fun i ↦ D.e i) Finset.univ, D.sum_e,
      map_one] at h
    exact h
  α_mul_e a := by rw [← map_mul]; exact congrArg (Ideal.Quotient.mk J) (D.α_mul_e a.1)
  e_mul_α a := by rw [← map_mul]; exact congrArg (Ideal.Quotient.mk J) (D.e_mul_α a.1)

theorem survData_pval : ∀ (l : List (D.survQuiver J).A) (x : (D.survQuiver J).V),
    (D.survData J).pval x l = Ideal.Quotient.mk J (D.pval x.1 (l.map Subtype.val))
  | [], _ => rfl
  | a :: l, x => by
      show (D.survData J).pval _ l * _ * _ = _
      rw [survData_pval l]
      show _ = Ideal.Quotient.mk J (D.pval (Q.tgt a.1) (l.map Subtype.val) * D.α a.1 * D.e x.1)
      rw [map_mul, map_mul]
      rfl

/-- A path factors through each of its arrows. -/
theorem pval_factor : ∀ (x : Q.V) (l : List Q.A) (a : Q.A), a ∈ l →
    ∃ u w : A, D.pval x l = u * D.α a * w
  | _, [], _, h => absurd h (List.not_mem_nil)
  | x, b :: l, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨D.pval (Q.tgt a) l, D.e x, rfl⟩
      · obtain ⟨u, w, hw⟩ := pval_factor (Q.tgt b) l a h
        refine ⟨u, w * D.α b * D.e x, ?_⟩
        show D.pval (Q.tgt b) l * D.α b * D.e x = _
        rw [hw]; simp only [mul_assoc]

/-- The image of a path in `A ⧸ J` is zero or the image of a path of the subquiver. -/
theorem mk_pval_mem (x : Q.V) (l : List Q.A) :
    Ideal.Quotient.mk J (D.pval x l) ∈ Submodule.span k
      (Set.range fun p : (D.survQuiver J).V × List (D.survQuiver J).A ↦ (D.survData J).pval p.1 p.2) := by
  classical
  by_cases h0 : Ideal.Quotient.mk J (D.pval x l) = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hx : Ideal.Quotient.mk J (D.e x) ≠ 0 := fun h ↦ h0 (by
    rw [← D.pval_mul_e x l, map_mul, h, mul_zero])
  have hl : ∀ a ∈ l, Ideal.Quotient.mk J (D.α a) ≠ 0 := by
    intro a ha h
    obtain ⟨u, w, hw⟩ := D.pval_factor x l a ha
    exact h0 (by rw [hw, map_mul, map_mul, h, mul_zero, zero_mul])
  refine Submodule.subset_span ⟨(⟨x, hx⟩, l.attach.map fun a ↦ ⟨a.1, hl a.1 a.2⟩), ?_⟩
  have hmap : (l.attach.map fun a ↦ (⟨a.1, hl a.1 a.2⟩ : (D.survQuiver J).A)).map Subtype.val = l := by
    simp
  exact (D.survData_pval J _ ⟨x, hx⟩).trans
    (congrArg (fun l' ↦ Ideal.Quotient.mk J (D.pval x l')) hmap)

include D in
theorem survData_span
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤) :
    Submodule.span k (Set.range fun p : (D.survQuiver J).V × List (D.survQuiver J).A ↦
      (D.survData J).pval p.1 p.2) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hz : z ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨x, l⟩, rfl⟩ := hz
      exact D.mk_pval_mem J x l
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz'
  | smul c z _ hz =>
      rw [show Ideal.Quotient.mk J (c • z) = c • Ideal.Quotient.mk J z from
        map_smul (Ideal.Quotient.mkₐ k J) c z]
      exact Submodule.smul_mem _ _ hz

theorem survData_isAdmissible (hadm : D.IsAdmissible) : (D.survData J).IsAdmissible := by
  obtain ⟨-, -, N, hN⟩ := hadm
  refine ⟨fun v ↦ v.2, fun a ↦ a.2, N, fun x l hl ↦ ?_⟩
  rw [survData_pval]
  exact (congrArg (Ideal.Quotient.mk J)
    (hN x.1 _ (hl.trans (le_of_eq (List.length_map _).symm)))).trans (map_zero _)

theorem survData_isSpecialBiserial (hsb : D.IsSpecialBiserial) :
    (D.survData J).IsSpecialBiserial := by
  obtain ⟨h1, h2, h3, h4⟩ := hsb
  have hallow : ∀ a b : (D.survQuiver J).A, (D.survData J).Allowed a b → D.Allowed a.1 b.1 := by
    rintro a b ⟨hab, hne⟩
    refine ⟨congrArg Subtype.val hab, fun h0 ↦ hne ?_⟩
    rw [survData_pval]
    show Ideal.Quotient.mk J (D.pval (Q.src a.1) [a.1, b.1]) = 0
    rw [h0, map_zero]
  refine ⟨fun x ↦ ?_, fun y ↦ ?_, fun a ↦ ?_, fun b ↦ ?_⟩
  · refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (D.survQuiver J).A // (D.survQuiver J).src a = x} ↦
        (⟨a.1.1, congrArg Subtype.val a.2⟩ : {a : Q.A // Q.src a = x.1}))
      fun a b h ↦ by
        have h' := congrArg Subtype.val h; dsimp only at h'; exact Subtype.ext (Subtype.ext h')) (h1 x.1)
  · refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (D.survQuiver J).A // (D.survQuiver J).tgt a = y} ↦
        (⟨a.1.1, congrArg Subtype.val a.2⟩ : {a : Q.A // Q.tgt a = y.1}))
      fun a b h ↦ by
        have h' := congrArg Subtype.val h; dsimp only at h'; exact Subtype.ext (Subtype.ext h')) (h2 y.1)
  · refine le_trans (Nat.card_le_card_of_injective
      (fun b : {b : (D.survQuiver J).A // (D.survData J).Allowed a b} ↦
        (⟨b.1.1, hallow a b.1 b.2⟩ : {b : Q.A // D.Allowed a.1 b}))
      fun b c h ↦ by simp only [Subtype.mk.injEq] at h; exact Subtype.ext (Subtype.ext h)) (h3 a.1)
  · refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : (D.survQuiver J).A // (D.survData J).Allowed a b} ↦
        (⟨a.1.1, hallow a.1 b a.2⟩ : {a : Q.A // D.Allowed a b.1}))
      fun a c h ↦ by simp only [Subtype.mk.injEq] at h; exact Subtype.ext (Subtype.ext h)) (h4 b.1)

/-- **Quotients of special biserial algebras are special biserial**, in the path-data
form: spanning, admissible special biserial path data pass to every quotient. -/
theorem quot_isSpecialBiserial
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial) :
    ∃ (Q' : FinQuiver) (D' : PathData Q' (A ⧸ J)),
      Submodule.span k (Set.range (fun p : Q'.V × List Q'.A ↦ D'.pval p.1 p.2)) = ⊤ ∧
        D'.IsAdmissible ∧ D'.IsSpecialBiserial :=
  ⟨_, D.survData J, D.survData_span J hspan, D.survData_isAdmissible J hadm,
    D.survData_isSpecialBiserial J hsb⟩

end PathData

/-- **Remark 5.7, library form.** A nonsimple brick over a special biserial algebra whose
faithful quotient is representation-finite has a brick submodule or quotient of dimension one
less. -/
theorem hasSmallerBrick_of_faithful [IsAlgClosed k] [FiniteDimensional k A]
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial)
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] (hM : IsBrick A M) (hns : ¬ IsSimpleModule A M)
    (hrf : IsRepFinite (A ⧸ Module.annihilator A M)) : HasSmallerBrick A M (k := k) := by
  set J := Module.annihilator A M
  have hMJ : Module.IsTorsionBySet A M J := fun m a ↦ Module.mem_annihilator.mp a.2 m
  let _ : Module (A ⧸ J) M := hMJ.module
  have : IsScalarTower A (A ⧸ J) M := Module.IsTorsionBySet.isScalarTower hMJ
  have : IsScalarTower k (A ⧸ J) M := Module.IsTorsionBySet.isScalarTower hMJ
  have : FiniteDimensional k (A ⧸ J) :=
    Module.Finite.of_surjective ((Ideal.Quotient.mkₐ k J).toLinearMap) Ideal.Quotient.mk_surjective
  have h := specialBiserial_hasSmallerBrick (D.survData J) (D.survData_span J hspan)
    (D.survData_isAdmissible J hadm) (D.survData_isSpecialBiserial J hsb) hrf.isBrickFinite M
    ((isBrick_quot_iff (I := J)).mpr hM) (fun h ↦ hns ((isSimpleModule_quot_iff (I := J)).mp h))
  exact HasSmallerBrick.of_quot (I := J) h

/-- **Remark 5.7.** An individual nonsimple brick `M` over a special biserial algebra `Λ`
has a brick submodule or quotient of dimension one less whenever its faithful quotient is
representation-finite. Here `M` is a right `Λ`-module, so the faithful quotient acts as
`Λᵐᵒᵖ ⧸ ann(M)`. -/
theorem remark_5_7 (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] (hsb : Statement.IsSpecialBiserial k Λ)
    (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
    [FiniteDimensional k M] (hM : Statement.IsBrick Λᵐᵒᵖ M) (hns : ¬ IsSimpleModule Λᵐᵒᵖ M)
    (hrf : IsRepFinite (Λᵐᵒᵖ ⧸ Module.annihilator Λᵐᵒᵖ M)) : Statement.HasSmallerBrick k Λ M := by
  obtain ⟨P, hP⟩ := hsb
  have : FiniteDimensional k Λᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv k : Λ ≃ₗ[k] Λᵐᵒᵖ)
  exact hasSmallerBrick_of_faithful P.toPathData P.span_pval P.isAdmissible
    (P.isSpecialBiserial hP) M hM hns hrf

end BrickAccessibility
