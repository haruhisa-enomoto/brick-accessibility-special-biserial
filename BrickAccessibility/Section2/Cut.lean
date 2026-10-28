module

public import BrickAccessibility.Basic.Ext
public import BrickAccessibility.Geometry.OrbitChart

/-!
# Proposition 2.1(1): a Hom–Ext inequality gives a brick quotient

Let `M` be a finite-dimensional nonsimple brick over an algebraically closed
field and `S` a one-dimensional simple module. If only finitely many quotients
`M / L` with `L ≅ S` occur up to isomorphism (Remark 2.2) and
`dim Ext¹(M, S) < dim Hom(S, M)`, then `M` has a brick quotient of dimension
`dim M - 1` (`exists_brick_quotient`).

Step 1 differs from the manuscript (owner-approved cleaner route): instead of
Chevalley's theorem and the fiber-dimension theorem, the loci of quotient classes
are covered by polynomial images (`kernel_polyCovered`), and the covering lemma
`PolyCovered.finrank_le` replaces the dimension count. It yields an embedding
`S → M` whose quotient `N` satisfies `dim End(N) + dim Hom(S, M) - 1 ≤ dim Hom(M, N)`,
which is the inequality the manuscript extracts from equation (2.2). Step 2
follows the manuscript.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

/-- Remark 2.2's finiteness hypothesis: only finitely many quotients `M / f(S)`
occur up to isomorphism. -/
def FinitelyManyQuotientsBy (A : Type*) [Ring A] (S : Type*) [AddCommGroup S] [Module A S] (M : Type*)
    [AddCommGroup M] [Module A M] : Prop :=
  ∃ T : Finset (S →ₗ[A] M), ∀ f : S →ₗ[A] M, f ≠ 0 →
    ∃ f' ∈ T, Nonempty ((M ⧸ LinearMap.range f) ≃ₗ[A] (M ⧸ LinearMap.range f'))

variable {k : Type u} [Field k] {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

section Lemmas

variable {S : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]

instance finiteDimensional_submodule [FiniteDimensional k M] (p : Submodule A M) :
    FiniteDimensional k p :=
  Module.Finite.of_injective (p.subtype.restrictScalars k) Subtype.val_injective

instance finiteDimensional_quotient [FiniteDimensional k M] (p : Submodule A M) :
    FiniteDimensional k (M ⧸ p) :=
  Module.Finite.of_surjective (p.mkQ.restrictScalars k) (Submodule.mkQ_surjective p)

/-- `dim (M / p) + dim p = dim M` for an `A`-submodule `p`. -/
theorem finrank_quotient_add_finrank' [FiniteDimensional k M] (p : Submodule A M) :
    finrank k (M ⧸ p) + finrank k p = finrank k M := by
  have h := Submodule.finrank_quotient_add_finrank (p.restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k p).finrank_eq] at h
  exact h

theorem finrank_range_of_ne_zero [IsSimpleModule A S] [FiniteDimensional k S]
    {f : S →ₗ[A] M} (hf : f ≠ 0) : finrank k (LinearMap.range f) = finrank k S :=
  ((LinearEquiv.ofInjective f (injective_of_ne_zero hf)).restrictScalars k).finrank_eq.symm

/-- A finite-dimensional module of dimension one is simple. -/
theorem isSimpleModule_of_finrank_eq_one [FiniteDimensional k M] (h : finrank k M = 1) :
    IsSimpleModule A M := by
  have : Nontrivial M := Module.nontrivial_of_finrank_eq_succ h
  refine { eq_bot_or_eq_top := fun p ↦ ?_ }
  have hp := Submodule.finrank_le (p.restrictScalars k)
  rw [h] at hp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h0 | h1
  · left
    have : p.restrictScalars k = ⊥ := Submodule.finrank_eq_zero.mp h0
    exact (Submodule.restrictScalars_eq_bot_iff k A M).mp this
  · right
    have : p.restrictScalars k = ⊤ := Submodule.eq_top_of_finrank_eq (h1.trans h.symm)
    exact (Submodule.restrictScalars_eq_top_iff k A M).mp this

/-- `End(M / L)` embeds into `Hom(M, M / L)`. -/
theorem finrank_end_le_finrank_hom [FiniteDimensional k M] (p : Submodule A M) :
    finrank k ((M ⧸ p) →ₗ[A] (M ⧸ p)) ≤ finrank k (M →ₗ[A] (M ⧸ p)) := by
  let ι : ((M ⧸ p) →ₗ[A] (M ⧸ p)) →ₗ[k] (M →ₗ[A] (M ⧸ p)) :=
    { toFun := fun g ↦ g ∘ₗ p.mkQ
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  refine LinearMap.finrank_le_finrank_of_injective (f := ι) fun g g' h ↦ ?_
  ext x
  exact LinearMap.congr_fun h x

end Lemmas

variable {S : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]

/-- **Step 1 of Proposition 2.1.** Some embedding `f : S → M` has quotient `N`
with `dim End(N) + dim Hom(S, M) - 1 ≤ dim Hom(M, N)`. -/
theorem exists_large_locus [Infinite k] [FiniteDimensional k M] [FiniteDimensional k S]
    [IsSimpleModule A S] (hS1 : finrank k S = 1) (hfin : FinitelyManyQuotientsBy A S M)
    (hr : 0 < finrank k (S →ₗ[A] M)) :
    ∃ f : S →ₗ[A] M, f ≠ 0 ∧
      finrank k ((M ⧸ LinearMap.range f) →ₗ[A] (M ⧸ LinearMap.range f)) +
        (finrank k (S →ₗ[A] M) - 1) ≤ finrank k (M →ₗ[A] (M ⧸ LinearMap.range f)) := by
  classical
  set r := finrank k (S →ₗ[A] M)
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT⟩ := hfin
  -- the evaluation at a basis vector of `S` and a left inverse
  let bS := Module.finBasisOfFinrankEq k S hS1
  let s0 := bS 0
  let ev : (S →ₗ[A] M) →ₗ[k] M :=
    { toFun := fun f ↦ f s0
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    ext s
    have hs : s = bS.repr s 0 • s0 := by
      conv_lhs => rw [← bS.sum_repr s]
      simp [s0, Fin.sum_univ_one]
    rw [hs, LinearMap.map_smul_of_tower]
    simp only [ev, LinearMap.coe_mk, AddHom.coe_mk] at hf
    simp [hf]
  obtain ⟨ρ, hρ⟩ := ev.exists_leftInverse_of_injective hev
  have hρev : ∀ f, ρ (f s0) = f := fun f ↦ LinearMap.congr_fun hρ f
  -- dimension of quotients by a line
  have hdimq : ∀ f : S →ₗ[A] M, f ≠ 0 →
      finrank k (M ⧸ LinearMap.range f) + 1 = finrank k M := by
    intro f hf
    have := finrank_quotient_add_finrank' (k := k) (LinearMap.range f)
    rwa [finrank_range_of_ne_zero hf, hS1] at this
  -- the cover of each quotient class
  have hcov : ∀ f' ∈ T, f' ≠ 0 → PolyCovered k
      {f : S →ₗ[A] M | f ≠ 0 ∧
        Nonempty ((M ⧸ LinearMap.range f) ≃ₗ[A] (M ⧸ LinearMap.range f'))} (r - 1) := by
    intro f' _ hf'
    let restr : (M →ₗ[A] (M ⧸ LinearMap.range f')) →ₗ[k] (M →ₗ[k] (M ⧸ LinearMap.range f')) :=
      { toFun := fun h ↦ h.restrictScalars k
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let restrE : ((M ⧸ LinearMap.range f') →ₗ[A] (M ⧸ LinearMap.range f')) →ₗ[k] ((M ⧸ LinearMap.range f') →ₗ[k] (M ⧸ LinearMap.range f')) :=
      { toFun := fun h ↦ h.restrictScalars k
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hrestr : Function.Injective restr := fun a b h ↦ by
      ext x; exact LinearMap.congr_fun h x
    have hrestrE : Function.Injective restrE := fun a b h ↦ by
      ext x; exact LinearMap.congr_fun h _
    let H := LinearMap.range restr
    let E := LinearMap.range restrE
    have hH : finrank k H = finrank k (M →ₗ[A] (M ⧸ LinearMap.range f')) := LinearMap.finrank_range_of_inj hrestr
    have hE : finrank k E = finrank k ((M ⧸ LinearMap.range f') →ₗ[A] (M ⧸ LinearMap.range f')) := LinearMap.finrank_range_of_inj hrestrE
    have hid : LinearMap.id ∈ E := ⟨LinearMap.id, rfl⟩
    have hEH : ∀ g ∈ E, ∀ h ∈ H, g ∘ₗ h ∈ H := by
      rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      exact ⟨g ∘ₗ h, rfl⟩
    have hK := kernel_polyCovered (hdimq f' hf') H E hid hEH
    -- the covering dimension is small
    have hsmall : finrank k H - finrank k E + 1 ≤ r - 1 := by
      have h1 := hcon f' hf'
      have h2 := finrank_end_le_finrank_hom (k := k) (LinearMap.range f')
      rw [hH, hE]
      omega
    refine ((hK.image ρ).le hsmall).mono ?_
    rintro f ⟨hf, ⟨φ⟩⟩
    refine ⟨f s0, ⟨restr (φ.toLinearMap ∘ₗ (LinearMap.range f).mkQ), ⟨_, rfl⟩, ?_, ?_⟩,
      hρev f⟩
    · intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
      exact ⟨m, rfl⟩
    · show φ ((LinearMap.range f).mkQ (f s0)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
        (LinearMap.mem_range_self f s0), map_zero]
  -- the whole space is covered
  have hall : PolyCovered k (Set.univ : Set (S →ₗ[A] M)) (r - 1) := by
    refine ((PolyCovered.zero (r - 1)).union (PolyCovered.biUnion (T.filter (· ≠ 0))
      fun f' hf' ↦ hcov f' (Finset.mem_filter.mp hf').1 (Finset.mem_filter.mp hf').2)).mono ?_
    intro f _
    by_cases hf : f = 0
    · exact Or.inl hf
    · right
      obtain ⟨f', hf'T, ⟨φ⟩⟩ := hT f hf
      have hf'0 : f' ≠ 0 := by
        rintro rfl
        have h1 := φ.restrictScalars k |>.finrank_eq
        have h2 := hdimq f hf
        have h3 := finrank_quotient_add_finrank' (k := k) (LinearMap.range (0 : S →ₗ[A] M))
        rw [LinearMap.range_zero, Module.finrank_zero_of_subsingleton (M := (⊥ : Submodule A M)),
          add_zero] at h3
        rw [LinearMap.range_zero] at h1
        omega
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hf'T, hf'0⟩) ⟨hf, ⟨φ⟩⟩
  have := hall.finrank_le
  omega

/-- **Proposition 2.1(1).** Over an algebraically closed field, let `M` be a
finite-dimensional nonsimple brick and `S` a one-dimensional simple module such
that only finitely many quotients `M / L` with `L ≅ S` occur up to isomorphism.
If `dim Ext¹(M, S) < dim Hom(S, M)`, then `M` has a brick quotient of dimension
`dim M - 1`. -/
theorem exists_brick_quotient [IsAlgClosed k] [FiniteDimensional k A] [FiniteDimensional k M]
    [FiniteDimensional k S] [IsSimpleModule A S] (hM : IsBrick A M)
    (hns : ¬ IsSimpleModule A M) (hS1 : finrank k S = 1) (hfin : FinitelyManyQuotientsBy A S M)
    (hineq : finrank k (Ext1 k A M S) < finrank k (S →ₗ[A] M)) :
    ∃ L : Submodule A M, IsBrick A (M ⧸ L) ∧ finrank k (M ⧸ L) + 1 = finrank k M := by
  obtain ⟨f, hf, hlocus⟩ := exists_large_locus hS1 hfin (by omega)
  set L := LinearMap.range f
  refine ⟨L, ?_, ?_⟩
  · have hdimq : finrank k (M ⧸ L) + 1 = finrank k M := by
      have := finrank_quotient_add_finrank' (k := k) L
      rwa [finrank_range_of_ne_zero hf, hS1] at this
    have hM2 : 2 ≤ finrank k M := by
      have := hM.1
      have h0 : 0 < finrank k M := Module.finrank_pos
      by_contra h
      exact hns (isSimpleModule_of_finrank_eq_one (k := k) (by omega))
    have : Nontrivial (M ⧸ L) := Module.nontrivial_of_finrank_pos (R := k) (by omega)
    refine isBrick_of_finrank_end_le_one (k := k) ?_
    -- Step 2
    have hle := Ext1.finrank_hom_le (k := k) M L.mkQ (Submodule.mkQ_surjective L)
    have hpost : finrank k (LinearMap.range (postcomp k A M L.mkQ :
        (M →ₗ[A] M) →ₗ[k] (M →ₗ[A] (M ⧸ L)))) ≤ 1 := by
      refine (LinearMap.finrank_range_le _).trans ?_
      rw [hM.finrank_end (k := k)]
    have hext : finrank k (Ext1 k A M (LinearMap.ker L.mkQ)) = finrank k (Ext1 k A M S) := by
      exact Ext1.finrank_congr ((LinearEquiv.ofEq _ _ (Submodule.ker_mkQ L)).trans
        (LinearEquiv.ofInjective f (injective_of_ne_zero hf)).symm)
    omega
  · have := finrank_quotient_add_finrank' (k := k) L
    rwa [finrank_range_of_ne_zero hf, hS1] at this

end BrickAccessibility
