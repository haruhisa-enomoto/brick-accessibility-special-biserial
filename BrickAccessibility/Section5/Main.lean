module

public import BrickAccessibility.Section3.Faithful
public import BrickAccessibility.Section4.Gentle
public import BrickAccessibility.Cited.StringBricks
public import BrickAccessibility.Cited.WaldWaschbusch

/-!
# Section 5: Proposition 5.2 and Theorem 5.4

Proposition 5.2: over a brick-finite string algebra every nonsimple brick has a
brick submodule or quotient of dimension one less (`string_hasSmallerBrick`).
Theorem 5.4 (`specialBiserial_hasSmallerBrick`): the same over a brick-finite
special biserial algebra, given by path data.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k]

section Quot

variable {A : Type u} [Ring A] {I : Ideal A} [I.IsTwoSided]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module (A ⧸ I) M] [IsScalarTower A (A ⧸ I) M]

/-- A module on which `A` acts through `A ⧸ I` is simple over `A ⧸ I` exactly when
it is simple over `A`. -/
theorem isSimpleModule_quot_iff : IsSimpleModule (A ⧸ I) M ↔ IsSimpleModule A M := by
  let e : Submodule (A ⧸ I) M ≃o Submodule A M :=
    { toFun := fun P ↦ P.restrictScalars A
      invFun := fun P ↦
        { carrier := P, add_mem' := P.add_mem, zero_mem' := P.zero_mem
          smul_mem' := fun b m hm ↦ by
            obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
            rw [mk_smul_eq]; exact P.smul_mem a hm }
      left_inv := fun P ↦ by ext; rfl
      right_inv := fun P ↦ by ext; rfl
      map_rel_iff' := Iff.rfl }
  simp only [isSimpleModule_iff]
  exact ⟨fun h ↦ by haveI := h; exact e.symm.isSimpleOrder,
    fun h ↦ by haveI := h; exact e.isSimpleOrder⟩

end Quot

/-- A nonzero finite-dimensional module over an algebra with admissible path data
has a one-dimensional submodule. -/
theorem exists_submodule_finrank_one {A : Type u} [Ring A] [Algebra k A] {Q : FinQuiver}
    (D : PathData Q A)
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (hadm : D.IsAdmissible) (M : Type u) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] [Nontrivial M] :
    ∃ L : Submodule A M, finrank k L = 1 := by
  classical
  obtain ⟨-, -, N, hN⟩ := hadm
  -- the least length from which all paths kill `M`
  have hex : ∃ j, ∀ x (l : List Q.A), j ≤ l.length → ∀ m : M, D.pval x l • m = 0 :=
    ⟨N, fun x l hl m ↦ by rw [hN x l hl, zero_smul]⟩
  set j0 := Nat.find hex
  have hj0 : j0 ≠ 0 := by
    intro h0
    have hall := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h0] at hall
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    apply hm
    rw [← one_smul A m, ← D.sum_e, Finset.sum_smul]
    exact Finset.sum_eq_zero fun v _ ↦ hall v [] (le_refl _) m
  obtain ⟨x, l, hl, m, hm⟩ : ∃ (x : Q.V) (l : List Q.A), j0 - 1 ≤ l.length ∧ ∃ m : M,
      D.pval x l • m ≠ 0 := by
    have := Nat.find_min hex (show j0 - 1 < j0 by omega)
    push Not at this
    obtain ⟨x, l, hl, m, hm⟩ := this
    exact ⟨x, l, hl, m, hm⟩
  have hlen : l.length = j0 - 1 := by
    by_contra h
    exact hm (Nat.find_spec hex x l (by omega) m)
  set y := D.pval x l • m
  have hy : ∀ a, D.α a • y = 0 := by
    intro a
    have h1 : D.α a * D.pval x l = D.pval x (l ++ [a]) := by
      rw [D.pval_append, D.pval_single, mul_assoc, D.e_pend_mul_pval]
    simp only [y, ← mul_smul, h1]
    have hj : j0 = Nat.find hex := rfl
    exact Nat.find_spec hex x _ (by simp only [List.length_append, List.length_singleton]; omega) m
  obtain ⟨v, hv⟩ : ∃ v, D.e v • y ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    change y = 0
    rw [← one_smul A y, ← D.sum_e, Finset.sum_smul]
    exact Finset.sum_eq_zero fun v _ ↦ h v
  set z := D.e v • y with hzdef
  have hz_e : ∀ w, D.e w • z = if w = v then z else 0 := by
    intro w
    rw [hzdef, ← mul_smul, D.e_mul_e]
    by_cases h : w = v <;> simp [h]
  have hz_α : ∀ a, D.α a • z = 0 := by
    intro a
    rw [hzdef, ← mul_smul]
    by_cases h : v = Q.src a
    · rw [h, D.α_mul_e]; exact hy a
    · rw [← D.α_mul_e a, mul_assoc, D.e_mul_e_of_ne (Ne.symm h), mul_zero, zero_smul]
  -- every element of `A` acts on `z` by a scalar
  have hscal : ∀ b : A, ∃ c : k, b • z = c • z := by
    intro b
    have hb : b ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
      rw [hspan]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
        obtain ⟨⟨x', l'⟩, rfl⟩ := hb
        cases l' with
        | nil =>
            simp only [PathData.pval]
            rw [hz_e]
            split_ifs
            · exact ⟨1, by simp⟩
            · exact ⟨0, by simp⟩
        | cons a l' =>
            refine ⟨0, ?_⟩
            simp only [PathData.pval, mul_smul, hz_e]
            split_ifs <;> simp [hz_α]
    | zero => exact ⟨0, by simp⟩
    | add b b' _ _ hb hb' =>
        obtain ⟨c, hc⟩ := hb; obtain ⟨c', hc'⟩ := hb'
        exact ⟨c + c', by rw [add_smul, hc, hc', add_smul]⟩
    | smul c b _ hb =>
        obtain ⟨c', hc'⟩ := hb
        exact ⟨c * c', by rw [smul_assoc, hc', smul_smul]⟩
  refine ⟨Submodule.span A {z}, ?_⟩
  have heq : (Submodule.span A {z}).restrictScalars k = Submodule.span k {z} := by
    ext w
    simp only [Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨c, hc⟩ := hscal b
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap k A c, algebraMap_smul A c z⟩
  have : finrank k (Submodule.span A {z}) = finrank k ((Submodule.span A {z}).restrictScalars k) :=
    rfl
  rw [this, heq, finrank_span_singleton hv]

variable {B : Type u} [Ring B] [Algebra k B]

/-- **Proposition 5.2.** -/
theorem string_hasSmallerBrick [IsAlgClosed k] [FiniteDimensional k B] (D : MonomialData k B)
    (hD : D.IsStringAlgebra) (hbf : IsBrickFinite B) (M : Type u) [AddCommGroup M] [Module B M]
    [Module k M] [IsScalarTower k B M] [FiniteDimensional k M] (hM : IsBrick B M)
    (hns : ¬ IsSimpleModule B M) : HasSmallerBrick B M (k := k) := by
  obtain ⟨w, hw, ⟨e⟩⟩ := isString_of_isBrick D hD hbf M hM
  set N := w.stringModule D hw
  have hN : IsBrick B N := hM.of_linearEquiv e
  have hNns : ¬ IsSimpleModule B N := fun h ↦ hns (IsSimpleModule.congr e)
  haveI : FiniteDimensional k N := Module.Finite.equiv (e.restrictScalars k)
  set I := Module.annihilator B N
  obtain ⟨D', hD'⟩ := exists_gentle_faithful_quotient D hD w hw hN
  letI : Module (B ⧸ I) N := Module.quotientAnnihilator
  haveI : IsScalarTower B (B ⧸ I) N :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator B N)
  haveI : IsScalarTower k (B ⧸ I) N :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator B N)
  haveI : FiniteDimensional k (B ⧸ I) :=
    Module.Finite.of_surjective ((Ideal.Quotient.mkₐ k I).toLinearMap)
      Ideal.Quotient.mk_surjective
  have hrep : IsRepFinite (B ⧸ I) := isRepFinite_of_isBrickFinite D' hD' hbf.quot
  have h := gentle_hasSmallerBrick D' hD' hrep N ((isBrick_quot_iff (I := I)).mpr hN)
    (fun h ↦ hNns ((isSimpleModule_quot_iff (I := I)).mp h))
  exact (HasSmallerBrick.of_quot (I := I) h).of_linearEquiv e.symm

variable {A : Type u} [Ring A] [Algebra k A]

/-- **Theorem 5.4**, for an algebra given by admissible special biserial path data. -/
theorem specialBiserial_hasSmallerBrick [IsAlgClosed k] [FiniteDimensional k A] {Q : FinQuiver}
    (D : PathData Q A)
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial) (hbf : IsBrickFinite A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] (hM : IsBrick A M) (hns : ¬ IsSimpleModule A M) :
    HasSmallerBrick A M (k := k) := by
  obtain ⟨J, hJ, D', hD', hproj⟩ := exists_string_quotient D hspan hadm hsb
  by_cases hMJ : Module.IsTorsionBySet A M J
  · letI : Module (A ⧸ J) M := hMJ.module
    haveI : IsScalarTower A (A ⧸ J) M := Module.IsTorsionBySet.isScalarTower hMJ
    haveI : IsScalarTower k (A ⧸ J) M := Module.IsTorsionBySet.isScalarTower hMJ
    haveI : FiniteDimensional k (A ⧸ J) :=
      Module.Finite.of_surjective ((Ideal.Quotient.mkₐ k J).toLinearMap)
        Ideal.Quotient.mk_surjective
    have h := string_hasSmallerBrick D' hD' hbf.quot M ((isBrick_quot_iff (I := J)).mpr hM)
      (fun h ↦ hns ((isSimpleModule_quot_iff (I := J)).mp h))
    exact HasSmallerBrick.of_quot (I := J) h
  · have hind : IsIndecomposable A M := by
      exact ⟨hM.1, fun P R hPR ↦ hM.compl_eq_bot hPR⟩
    haveI : Module.Projective A M := hproj M hind hMJ
    have := hM.1
    obtain ⟨L, hL⟩ := exists_submodule_finrank_one D hspan hadm M
    have hdim := finrank_quotient_add_finrank' (k := k) L
    have hM2 : 2 ≤ finrank k M := by
      have h0 : 0 < finrank k M := Module.finrank_pos
      by_contra h
      exact hns (isSimpleModule_of_finrank_eq_one (k := k) (by omega))
    haveI : Nontrivial (M ⧸ L) := Module.nontrivial_of_finrank_pos (R := k) (by omega)
    right
    exact ⟨L, hM.of_surjective_of_projective (k := k) L.mkQ (Submodule.mkQ_surjective L),
      by omega⟩

end BrickAccessibility
