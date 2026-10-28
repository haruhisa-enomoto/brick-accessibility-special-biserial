module

public import BrickAccessibility.Bridge.FromPathData
public import BrickAccessibility.Bridge.Presentation
public import BrickAccessibility.Section5.Main
public import BrickAccessibility.Cited.SkowronskiWaschbusch

/-!
# The principal theorems

`theoremA` proves `Statement.TheoremA` (Theorem 5.4) from the library theorem
`specialBiserial_hasSmallerBrick`, through the path data of an admissible special
biserial presentation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

universe u

/-- **Theorem 5.4 (Theorem A).** -/
theorem theoremA : Statement.TheoremA.{u} := by
  intro k _ _ Λ _ _ _ _ hbf hsb M _ _ _ _ _ hM hns
  obtain ⟨P, hP⟩ := hsb
  exact specialBiserial_hasSmallerBrick P.toPathData P.span_pval P.isAdmissible
    (P.isSpecialBiserial hP) hbf M hM hns

end BrickAccessibility

namespace BrickAccessibility

open Module Statement

universe u

theorem isBrick_of_isSimpleModule {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] : IsBrick A M :=
  ⟨IsSimpleModule.nontrivial A M, fun _ hf ↦
    (Module.End.isUnit_iff _).mpr (LinearMap.bijective_of_ne_zero hf)⟩

/-- Bricks in the same isomorphism class have the same dimension. -/
theorem finrank_eq_of_linearEquiv {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] (e : M ≃ₗ[A] N) :
    finrank k M = finrank k N :=
  (e.restrictScalars k).finrank_eq

/-- Brick accessibility and the interval of brick dimensions follow from the conclusion
of Theorem A. -/
theorem accessibility_of_smaller (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] (hbasic : Statement.IsBasic k Λ) (hbf : Statement.IsBrickFinite Λ)
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
      [FiniteDimensional k M], Statement.IsBrick Λᵐᵒᵖ M → ¬ IsSimpleModule Λᵐᵒᵖ M →
        Statement.HasSmallerBrick k Λ M) :
    (∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
      [FiniteDimensional k M], Statement.IsBrick Λᵐᵒᵖ M → IsBrickAccessible k Λ M) ∧
    (Nontrivial Λ → ∃ N : ℕ, 1 ≤ N ∧ brickDimensions k Λ = Set.Icc 1 N) := by
  -- every brick of dimension `n` is brick accessible
  have hacc : ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M]
      [IsScalarTower k Λᵐᵒᵖ M] [FiniteDimensional k M], Statement.IsBrick Λᵐᵒᵖ M →
        finrank k M = n → BrickAccessibleOfDim k Λ n M := by
    intro n
    induction n with
    | zero =>
        intro M _ _ _ _ _ hM hd
        have := hM.1
        exact absurd hd (Module.finrank_pos (R := k) (M := M)).ne'
    | succ n ih =>
        intro M _ _ _ _ _ hM hd
        refine ⟨hM, hd, ?_⟩
        by_cases hs : IsSimpleModule Λᵐᵒᵖ M
        · exact Or.inl hs
        · right
          rcases hA M hM hs with ⟨N, hN, hNd⟩ | ⟨L, hL, hLd⟩
          · exact Or.inl ⟨N, ih N hN (by omega)⟩
          · exact Or.inr ⟨L, ih (M ⧸ L) hL (by omega)⟩
  refine ⟨fun M _ _ _ _ _ hM ↦ hacc _ M hM rfl, fun hΛ ↦ ?_⟩
  -- bricks of every dimension below a given one
  have hdown : ∀ (m : ℕ) (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M]
      [IsScalarTower k Λᵐᵒᵖ M] [FiniteDimensional k M], Statement.IsBrick Λᵐᵒᵖ M →
        finrank k M = m → ∀ d, 1 ≤ d → d ≤ m → d ∈ brickDimensions k Λ := by
    intro m
    induction m with
    | zero => intro M _ _ _ _ _ _ _ d h1 h2; omega
    | succ m ih =>
        intro M _ _ _ _ _ hM hd d h1 h2
        rcases Nat.lt_or_ge d (m + 1) with hlt | hge
        · by_cases hs : IsSimpleModule Λᵐᵒᵖ M
          · have h1 : finrank k M = 1 := by
              rw [hbasic M hs]
              exact IsBrick.finrank_end (A := Λᵐᵒᵖ) hM
            omega
          · rcases hA M hM hs with ⟨N, hN, hNd⟩ | ⟨L, hL, hLd⟩
            · exact ih N hN (by omega) d h1 (by omega)
            · exact ih (M ⧸ L) hL (by omega) d h1 (by omega)
        · exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hM,
            by omega⟩
  classical
  set S := brickDimensions k Λ
  -- the brick dimensions form a finite set
  obtain ⟨n, B, hB⟩ := hbf
  let T : Fin n → Set ℕ := fun i ↦ {d | ∃ (M : Type u) (_ : AddCommGroup M)
      (_ : Module Λᵐᵒᵖ M) (_ : Module k M) (_ : IsScalarTower k Λᵐᵒᵖ M),
      FiniteDimensional k M ∧ Statement.IsBrick Λᵐᵒᵖ M ∧ finrank k M = d ∧
        Nonempty (M ≃ₗ[Λᵐᵒᵖ] B i)}
  have hT : ∀ i, ∀ d ∈ T i, ∀ d' ∈ T i, d = d' := by
    rintro i d ⟨M, _, _, _, _, _, _, rfl, ⟨e⟩⟩ d' ⟨M', _, _, _, _, _, _, rfl, ⟨e'⟩⟩
    exact finrank_eq_of_linearEquiv (k := k) (e.trans e'.symm)
  have hST : S ⊆ ⋃ i, T i := by
    rintro d ⟨M, _, _, _, _, hfd, hM, rfl⟩
    haveI : Module.Finite Λᵐᵒᵖ M := Module.Finite.of_restrictScalars_finite k Λᵐᵒᵖ M
    obtain ⟨i, ⟨e⟩⟩ := hB M hM
    exact Set.mem_iUnion.mpr ⟨i, M, inferInstance, inferInstance, inferInstance, inferInstance,
      hfd, hM, rfl, ⟨e⟩⟩
  have hfin : S.Finite := by
    refine Set.Finite.subset (Set.finite_iUnion fun i ↦ ?_) hST
    exact Set.Subsingleton.finite fun d hd d' hd' ↦ hT i d hd d' hd'
  -- a simple module is a brick
  have hnt : Nontrivial Λᵐᵒᵖ := MulOpposite.instNontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Λᵐᵒᵖ
  haveI : IsSimpleModule Λᵐᵒᵖ (Λᵐᵒᵖ ⧸ m) := (isSimpleModule_iff_isCoatom).mpr hm.out
  have hS0 : finrank k (Λᵐᵒᵖ ⧸ m) ∈ S :=
    ⟨Λᵐᵒᵖ ⧸ m, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      isBrick_of_isSimpleModule, rfl⟩
  have hne : hfin.toFinset.Nonempty := ⟨_, hfin.mem_toFinset.mpr hS0⟩
  set N := hfin.toFinset.max' hne
  have hNS : N ∈ S := hfin.mem_toFinset.mp (Finset.max'_mem _ _)
  have hpos : ∀ d ∈ S, 1 ≤ d := by
    rintro d ⟨M, _, _, _, _, _, hM, rfl⟩
    have := hM.1
    exact Module.finrank_pos
  refine ⟨N, hpos N hNS, Set.Subset.antisymm (fun d hd ↦ ⟨hpos d hd, ?_⟩) ?_⟩
  · exact Finset.le_max' _ _ (hfin.mem_toFinset.mpr hd)
  · rintro d ⟨h1, h2⟩
    obtain ⟨M, _, _, _, _, _, hM, hMd⟩ := hNS
    exact hdown N M hM hMd d h1 h2

/-- **Corollary 5.5 (Corollary B).** -/
theorem corollaryB : Statement.CorollaryB.{u} := by
  intro k _ _ Λ _ _ _ hbasic hbf hsb
  exact accessibility_of_smaller k Λ hbasic hbf (theoremA k Λ hbasic hbf hsb)

/-- A representation-finite algebra is brick-finite. -/
theorem isBrickFinite_of_isRepresentationFinite {Λ : Type u} [Ring Λ]
    (h : Statement.IsRepresentationFinite Λ) : Statement.IsBrickFinite Λ := by
  obtain ⟨n, B, hB⟩ := h
  exact ⟨n, B, fun M _ _ _ hM ↦ hB M ⟨hM.1, fun P R hPR ↦ IsBrick.compl_eq_bot (A := Λᵐᵒᵖ) hM hPR⟩⟩

/-- **Skowroński–Waschbüsch** [SW, p. 173 and Lemma 2, p. 175]: a basic
representation-finite biserial algebra over an algebraically closed field is special biserial
in the sense of Definition 3.2. -/
theorem isSpecialBiserial_of_biserial (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u)
    [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] (hbasic : Statement.IsBasic k Λ)
    (hrf : Statement.IsRepresentationFinite Λ) (hbis : Statement.IsBiserial Λ) :
    Statement.IsSpecialBiserial k Λ := by
  obtain ⟨Q, D, hspan, hadm, hsb, hind⟩ := exists_specialBiserial_pathData k Λ hbasic hrf hbis
  exact D.isSpecialBiserial_of_pathData hspan hadm hind hsb

/-- **Corollary 5.6.** As in the paper: the algebra is special biserial
(`isSpecialBiserial_of_biserial`) and brick-finite, so Theorem A and Corollary B apply. -/
theorem corollaryBiserial : Statement.CorollaryBiserial.{u} := by
  intro k _ _ Λ _ _ _ hbasic hrf hbis
  have hbf := isBrickFinite_of_isRepresentationFinite hrf
  have hsb := isSpecialBiserial_of_biserial k Λ hbasic hrf hbis
  have hA := theoremA k Λ hbasic hbf hsb
  exact ⟨hA, accessibility_of_smaller k Λ hbasic hbf hA⟩

end BrickAccessibility
