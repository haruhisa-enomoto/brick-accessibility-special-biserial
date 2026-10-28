module

public import BrickAccessibility.Section2.Cut

/-!
# Proposition 2.1(2): the dual inequality gives a brick submodule

Let `M` be a finite-dimensional nonsimple brick over an algebraically closed
field and `S` a one-dimensional simple module such that only finitely many
kernels of epimorphisms `M → S` occur up to isomorphism (Remark 2.2). If
`dim Ext¹(S, M) < dim Hom(M, S)`, then `M` has a brick submodule of dimension
`dim M - 1` (`exists_brick_submodule`).

The manuscript deduces part (2) from part (1) by the duality `D`. Here the
argument is dualized directly: Step 1 applies `kernel_polyCovered` to the
transposes of the inclusions `ker g → M`, and Step 2 uses the contravariant
connecting inequality `Ext1.finrank_hom_sub_le`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

/-- Remark 2.2's dual finiteness hypothesis: only finitely many kernels of
nonzero maps `M → S` occur up to isomorphism. -/
def FinitelyManyKernelsBy (A : Type*) [Ring A] (M : Type*) [AddCommGroup M] [Module A M]
    (S : Type*) [AddCommGroup S] [Module A S] : Prop :=
  ∃ T : Finset (M →ₗ[A] S), ∀ g : M →ₗ[A] S, g ≠ 0 →
    ∃ g' ∈ T, Nonempty (LinearMap.ker g ≃ₗ[A] LinearMap.ker g')

variable {k : Type u} [Field k] {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable {S : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]

theorem surjective_of_ne_zero [IsSimpleModule A S] {g : M →ₗ[A] S} (hg : g ≠ 0) :
    Function.Surjective g := by
  rw [← LinearMap.range_eq_top]
  refine (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range g)).resolve_left fun h ↦ hg ?_
  exact LinearMap.range_eq_bot.mp h

theorem finrank_ker_add_one [FiniteDimensional k M] [FiniteDimensional k S] [IsSimpleModule A S]
    (hS1 : finrank k S = 1) {g : M →ₗ[A] S} (hg : g ≠ 0) :
    finrank k (LinearMap.ker g) + 1 = finrank k M := by
  have h := LinearMap.finrank_range_add_finrank_ker (g.restrictScalars k)
  have hs : Function.Surjective (g.restrictScalars k) := surjective_of_ne_zero (A := A) hg
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, hS1] at h
  have : finrank k (LinearMap.ker (g.restrictScalars k)) = finrank k (LinearMap.ker g) := rfl
  omega

/-- `End(p)` embeds into `Hom(p, M)`. -/
theorem finrank_end_le_finrank_hom_sub [FiniteDimensional k M] (p : Submodule A M) :
    finrank k (p →ₗ[A] p) ≤ finrank k (p →ₗ[A] M) := by
  let ι : (p →ₗ[A] p) →ₗ[k] (p →ₗ[A] M) :=
    { toFun := fun e ↦ p.subtype ∘ₗ e
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  refine LinearMap.finrank_le_finrank_of_injective (f := ι) fun e e' h ↦ ?_
  ext x
  have := LinearMap.congr_fun h x
  simpa [ι] using this

/-- **Step 1 of Proposition 2.1(2).** Some epimorphism `g : M → S` has kernel
`K` with `dim End(K) + dim Hom(M, S) - 1 ≤ dim Hom(K, M)`. -/
theorem exists_large_locus_dual [Infinite k] [FiniteDimensional k M] [FiniteDimensional k S]
    [IsSimpleModule A S] (hS1 : finrank k S = 1) (hfin : FinitelyManyKernelsBy A M S)
    (hr : 0 < finrank k (M →ₗ[A] S)) :
    ∃ g : M →ₗ[A] S, g ≠ 0 ∧
      finrank k (LinearMap.ker g →ₗ[A] LinearMap.ker g) + (finrank k (M →ₗ[A] S) - 1) ≤
        finrank k (LinearMap.ker g →ₗ[A] M) := by
  classical
  set r := finrank k (M →ₗ[A] S)
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT⟩ := hfin
  let bS := Module.finBasisOfFinrankEq k S hS1
  let ev : (M →ₗ[A] S) →ₗ[k] Dual k M :=
    { toFun := fun g ↦ bS.coord 0 ∘ₗ g.restrictScalars k
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    ext m
    have h1 : bS.coord 0 (g m) = 0 := LinearMap.congr_fun hg m
    have : g m = bS.repr (g m) 0 • bS 0 := by
      conv_lhs => rw [← bS.sum_repr (g m)]
      simp
    rw [this]
    simp only [Basis.coord_apply] at h1
    simp [h1]
  obtain ⟨ρ, hρ⟩ := ev.exists_leftInverse_of_injective hev
  have hρev : ∀ g, ρ (ev g) = g := fun g ↦ LinearMap.congr_fun hρ g
  have hcov : ∀ g' ∈ T, g' ≠ 0 → PolyCovered k
      {g : M →ₗ[A] S | g ≠ 0 ∧ Nonempty (LinearMap.ker g ≃ₗ[A] LinearMap.ker g')} (r - 1) := by
    intro g' _ hg'
    let tr : ((LinearMap.ker g') →ₗ[A] M) →ₗ[k] (Dual k M →ₗ[k] Dual k (LinearMap.ker g')) :=
      { toFun := fun h ↦ (h.restrictScalars k).dualMap
        map_add' := fun _ _ ↦ by ext; simp
        map_smul' := fun _ _ ↦ by ext; simp }
    let trE : ((LinearMap.ker g') →ₗ[A] (LinearMap.ker g')) →ₗ[k] (Dual k (LinearMap.ker g') →ₗ[k] Dual k (LinearMap.ker g')) :=
      { toFun := fun h ↦ (h.restrictScalars k).dualMap
        map_add' := fun _ _ ↦ by ext; simp
        map_smul' := fun _ _ ↦ by ext; simp }
    have htr : Function.Injective tr := by
      rw [injective_iff_map_eq_zero]
      intro h h0
      ext x
      refine (Module.forall_dual_apply_eq_zero_iff k (h x)).mp fun φ ↦ ?_
      have := LinearMap.congr_fun (LinearMap.congr_fun h0 φ) x
      simpa [tr] using this
    have htrE : Function.Injective trE := by
      rw [injective_iff_map_eq_zero]
      intro h h0
      ext x
      have hx : h x = 0 := (Module.forall_dual_apply_eq_zero_iff k (h x)).mp fun φ ↦ by
        have := LinearMap.congr_fun (LinearMap.congr_fun h0 φ) x
        simpa [trE] using this
      simp [hx]
    let H := LinearMap.range tr
    let E := LinearMap.range trE
    have hH : finrank k H = finrank k ((LinearMap.ker g') →ₗ[A] M) := LinearMap.finrank_range_of_inj htr
    have hE : finrank k E = finrank k ((LinearMap.ker g') →ₗ[A] (LinearMap.ker g')) := LinearMap.finrank_range_of_inj htrE
    have hid : LinearMap.id ∈ E := ⟨LinearMap.id, by ext; simp [trE]⟩
    have hEH : ∀ e ∈ E, ∀ h ∈ H, e ∘ₗ h ∈ H := by
      rintro _ ⟨e, rfl⟩ _ ⟨h, rfl⟩
      exact ⟨h ∘ₗ e, by ext; simp [tr, trE]⟩
    have hdim : finrank k (Dual k (LinearMap.ker g')) + 1 = finrank k (Dual k M) := by
      rw [Subspace.dual_finrank_eq, Subspace.dual_finrank_eq]
      exact finrank_ker_add_one hS1 hg'
    have hK := kernel_polyCovered hdim H E hid hEH
    have hsmall : finrank k H - finrank k E + 1 ≤ r - 1 := by
      have h1 := hcon g' hg'
      have h2 := finrank_end_le_finrank_hom_sub (k := k) (LinearMap.ker g')
      rw [hH, hE]
      omega
    refine ((hK.image ρ).le hsmall).mono ?_
    rintro g ⟨hg, ⟨ψ⟩⟩
    let h : (LinearMap.ker g') →ₗ[A] M := (LinearMap.ker g).subtype ∘ₗ ψ.symm.toLinearMap
    have hinj : Function.Injective (h.restrictScalars k) := by
      intro x y hxy
      apply ψ.symm.injective
      exact Subtype.val_injective hxy
    refine ⟨ev g, ⟨tr h, ⟨h, rfl⟩, LinearMap.dualMap_surjective_of_injective hinj, ?_⟩,
      hρev g⟩
    ext x
    have hx : g (h x) = 0 := (ψ.symm x).2
    simp [tr, ev, hx]
  have hall : PolyCovered k (Set.univ : Set (M →ₗ[A] S)) (r - 1) := by
    refine ((PolyCovered.zero (r - 1)).union (PolyCovered.biUnion (T.filter (· ≠ 0))
      fun g' hg' ↦ hcov g' (Finset.mem_filter.mp hg').1 (Finset.mem_filter.mp hg').2)).mono ?_
    intro g _
    by_cases hg : g = 0
    · exact Or.inl hg
    · right
      obtain ⟨g', hg'T, ⟨ψ⟩⟩ := hT g hg
      have hg'0 : g' ≠ 0 := by
        rintro rfl
        have h1 := (ψ.restrictScalars k).finrank_eq
        have h2 := finrank_ker_add_one hS1 hg
        rw [LinearMap.ker_zero] at h1
        have h3 : finrank k (⊤ : Submodule A M) = finrank k M :=
          (LinearEquiv.ofTop (⊤ : Submodule A M) rfl |>.restrictScalars k).finrank_eq
        omega
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hg'T, hg'0⟩) ⟨hg, ⟨ψ⟩⟩
  have := hall.finrank_le
  omega

/-- **Proposition 2.1(2).** Over an algebraically closed field, let `M` be a
finite-dimensional nonsimple brick and `S` a one-dimensional simple module such
that only finitely many kernels of epimorphisms `M → S` occur up to isomorphism.
If `dim Ext¹(S, M) < dim Hom(M, S)`, then `M` has a brick submodule of
dimension `dim M - 1`. -/
theorem exists_brick_submodule [IsAlgClosed k] [FiniteDimensional k A] [FiniteDimensional k M]
    [FiniteDimensional k S] [IsSimpleModule A S] (hM : IsBrick A M)
    (hns : ¬ IsSimpleModule A M) (hS1 : finrank k S = 1) (hfin : FinitelyManyKernelsBy A M S)
    (hineq : finrank k (Ext1 k A S M) < finrank k (M →ₗ[A] S)) :
    ∃ N : Submodule A M, IsBrick A N ∧ finrank k N + 1 = finrank k M := by
  obtain ⟨g, hg, hlocus⟩ := exists_large_locus_dual hS1 hfin (by omega)
  set N := LinearMap.ker g
  have hdim : finrank k N + 1 = finrank k M := finrank_ker_add_one hS1 hg
  refine ⟨N, ?_, hdim⟩
  have hM2 : 2 ≤ finrank k M := by
    have := hM.1
    have h0 : 0 < finrank k M := Module.finrank_pos
    by_contra h
    exact hns (isSimpleModule_of_finrank_eq_one (k := k) (by omega))
  have : Nontrivial N := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  refine isBrick_of_finrank_end_le_one (k := k) ?_
  have hle := Ext1.finrank_hom_sub_le (k := k) (X := M) N
  have hpre : finrank k (LinearMap.range (precomp k A M M N.subtype :
      (M →ₗ[A] M) →ₗ[k] (N →ₗ[A] M))) ≤ 1 := by
    refine (LinearMap.finrank_range_le _).trans ?_
    rw [hM.finrank_end (k := k)]
  have hext : finrank k (Ext1 k A (M ⧸ N) M) = finrank k (Ext1 k A S M) :=
    Ext1.finrank_congr_left (g.quotKerEquivOfSurjective (surjective_of_ne_zero hg))
  omega

end BrickAccessibility
