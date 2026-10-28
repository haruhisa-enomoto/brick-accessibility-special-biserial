module

public import BrickAccessibility.Classification.BandBrick
public import BrickAccessibility.Classification.BlockEnd

/-!
# Bricks among string and band modules

A brick is indecomposable, so in the decomposition it is a single piece
(`unique_of_isBrick_pi`). A block module whose blocks have dimension at least two
has a nonzero non-injective blockwise endomorphism, so a brick piece has
one-dimensional blocks (`finrank_eq_one_of_isBrick`). A band piece with
one-dimensional blocks is some `M(b, t)` (`exists_equiv_BM`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

theorem IsBrick.of_equiv {M N : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (h : IsBrick B M) (e : M ≃ₗ[B] N) : IsBrick B N := by
  have := h.1
  refine ⟨e.symm.toEquiv.nontrivial, fun f hf ↦ ?_⟩
  have hf' : (e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap) ≠ 0 := by
    intro h0; apply hf
    ext y
    have := LinearMap.congr_fun h0 (e.symm y)
    simpa using this
  obtain ⟨u, hu⟩ := h.2 _ hf'
  have hb : Function.Bijective (e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap) :=
    (Module.End.isUnit_iff _).mp (hu ▸ u.isUnit)
  refine (Module.End.isUnit_iff f).mpr ?_
  have : (f : N → N) = e ∘ (e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap) ∘ e.symm := by
    funext y; simp
  rw [this]
  exact e.bijective.comp (hb.comp e.symm.bijective)

/-- A brick product has exactly one factor. -/
theorem unique_of_isBrick_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module B (X i)] (hnt : ∀ i, Nontrivial (X i))
    (h : IsBrick B (∀ i, X i)) : Nonempty (Unique ι) := by
  have := h.1
  have hne : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (∀ i, X i)
    exact hxy (funext fun i ↦ isEmptyElim i)
  have hsub : Subsingleton ι := by
    refine ⟨fun i j ↦ ?_⟩
    by_contra hij
    let P : (∀ i, X i) →ₗ[B] (∀ i, X i) := (LinearMap.single B X i).comp (LinearMap.proj i)
    obtain ⟨x, hx⟩ := exists_ne (0 : X i)
    obtain ⟨y, hy⟩ := exists_ne (0 : X j)
    have hP : P ≠ 0 := by
      intro h0
      have := congrFun (LinearMap.congr_fun h0 (Pi.single i x)) i
      simp [P] at this
      exact hx this
    obtain ⟨u, hu⟩ := h.2 P hP
    have hinj := ((Module.End.isUnit_iff P).mp (hu ▸ u.isUnit)).1
    have h1 : P (Pi.single j y) = P 0 := by
      simp only [P, LinearMap.comp_apply, LinearMap.proj_apply, map_zero]
      rw [Pi.single_eq_of_ne hij, map_zero]
    have := congrFun (hinj h1) j
    simp at this
    exact hy this
  exact ⟨@Unique.mk' ι (Classical.inhabited_of_nonempty hne) hsub⟩

namespace MonomialData.BlockQuiver

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
  (C : D.BlockQuiver V) (hC : C.KillsZeroPaths)

/-- A nonzero non-injective blockwise endomorphism prevents a brick. -/
theorem not_isBrick_of_end [Nonempty C.P] (h : V →ₗ[k] V)
    (hcomm : ∀ a i y, h (C.g a i y) = C.g a i (h y)) (h0 : h ≠ 0)
    (hni : ¬ Function.Injective h) : ¬ IsBrick B (C.Mod hC) := by
  intro hb
  let H : C.Mod hC →ₗ[B] C.Mod hC := C.withGHom hC C.g hC h hcomm
  have hH : ∀ p y, H (C.ofFun hC (Pi.single p y)) = C.ofFun hC (Pi.single p (h y)) :=
    fun p y ↦ C.withGHom_single hC C.g hC h hcomm p y
  obtain ⟨p⟩ := ‹Nonempty C.P›
  obtain ⟨y, hy⟩ : ∃ y, h y ≠ 0 := by
    by_contra hall; push Not at hall; exact h0 (LinearMap.ext hall)
  have hH0 : H ≠ 0 := by
    intro h0
    have := LinearMap.congr_fun h0 (C.ofFun hC (Pi.single p y))
    rw [hH, LinearMap.zero_apply] at this
    have h2 : (Pi.single p (h y) : C.P → V) p = 0 := congrFun this p
    rw [Pi.single_eq_same] at h2
    exact hy h2
  obtain ⟨u, hu⟩ := hb.2 H hH0
  have hinj := ((Module.End.isUnit_iff H).mp (hu ▸ u.isUnit)).1
  obtain ⟨y1, y2, hy12, he⟩ : ∃ y1 y2, y1 ≠ y2 ∧ h y1 = h y2 := by
    by_contra hall; push Not at hall
    exact hni fun a b hab ↦ by by_contra hne; exact hall a b hne hab
  have : H (C.ofFun hC (Pi.single p y1)) = H (C.ofFun hC (Pi.single p y2)) := by
    rw [hH, hH, he]
  have h3 : (Pi.single p y1 : C.P → V) p = (Pi.single p y2 : C.P → V) p := congrFun (hinj this) p
  rw [Pi.single_eq_same, Pi.single_eq_same] at h3
  exact hy12 h3

end MonomialData.BlockQuiver

/-- A rank-one endomorphism of a space of dimension at least two. -/
theorem exists_rank_one {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : 2 ≤ finrank k V) : ∃ h : V →ₗ[k] V, h ≠ 0 ∧ ¬ Function.Injective h := by
  let bV := Module.finBasis k V
  let i0 : Fin (finrank k V) := ⟨0, by omega⟩
  let i1 : Fin (finrank k V) := ⟨1, by omega⟩
  refine ⟨(bV.coord i0).smulRight (bV i0), fun h0 ↦ ?_, fun hinj ↦ ?_⟩
  · have := LinearMap.congr_fun h0 (bV i0)
    simp [Basis.coord_apply] at this
    exact bV.ne_zero i0 this
  · have : (bV.coord i0).smulRight (bV i0) (bV i1) = (bV.coord i0).smulRight (bV i0) 0 := by
      simp [Basis.coord_apply, Finsupp.single_apply, show i0 ≠ i1 from by simp [i0, i1, Fin.ext_iff]]
    exact bV.ne_zero i1 (hinj this)

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)
variable {V : Type u} [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V)

/-- A linear map commuting with the twist commutes with all block isomorphisms. -/
theorem g_comm {h : V →ₗ[k] V} (hφ : ∀ y, h (φ y) = φ (h y)) (a : D.Q.A) (i : Fin b.n) (y : V) :
    h ((b.blockQuiver S hA V φ).g a i y) = (b.blockQuiver S hA V φ).g a i (h y) := by
  simp only [blockQuiver]
  split_ifs
  · exact hφ y
  · apply φ.injective
    rw [← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · rfl

/-- The blocks of a band brick are one-dimensional. -/
theorem finrank_eq_one_of_isBrick [IsAlgClosed k] [FiniteDimensional k V] (hV : 0 < finrank k V)
    (hb : IsBrick B ((b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ))) :
    finrank k V = 1 := by
  by_contra h1
  have h2 : 2 ≤ finrank k V := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  have : Nonempty (b.blockQuiver S hA V φ).P := ⟨b.first⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue φ.toLinearMap
  by_cases hφμ : φ.toLinearMap = μ • LinearMap.id
  · obtain ⟨h, hh0, hni⟩ := exists_rank_one (k := k) h2
    refine (b.blockQuiver S hA V φ).not_isBrick_of_end (b.blockQuiver_kills S hA hK V φ) h
      (b.g_comm S hA φ fun y ↦ ?_) hh0 hni hb
    have e := LinearMap.congr_fun hφμ
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at e
    rw [e, e, map_smul]
  · refine (b.blockQuiver S hA V φ).not_isBrick_of_end (b.blockQuiver_kills S hA hK V φ)
      (φ.toLinearMap - μ • LinearMap.id) (b.g_comm S hA φ fun y ↦ ?_) (sub_ne_zero.mpr hφμ)
      (fun hinj ↦ ?_) hb
    · simp [map_smul]
    · obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      have : (φ.toLinearMap - μ • LinearMap.id : V →ₗ[k] V) v =
          (φ.toLinearMap - μ • LinearMap.id : V →ₗ[k] V) 0 := by
        simp [hv.apply_eq_smul]
      exact hv.2 (hinj this)

/-- A band module with one-dimensional blocks is some `M(b, t)`. -/
theorem exists_equiv_BM [FiniteDimensional k V] (hV : finrank k V = 1) :
    ∃ t : kˣ, Nonempty ((b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ) ≃ₗ[B]
      b.BM S hA hK t) := by
  let e : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by rw [hV, Module.finrank_self])
  set μ := e (φ (e.symm 1))
  have hφ : ∀ y, e (φ y) = μ * e y := by
    intro y
    have hy : y = e y • e.symm 1 := by
      apply e.injective; rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    conv_lhs => rw [hy]
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  have hμ : μ ≠ 0 := by
    intro h0
    have h1 : φ (e.symm 1) = 0 := e.injective (by rw [map_zero]; exact h0)
    have h2 : e.symm 1 = 0 := φ.injective (by rw [h1, map_zero])
    exact one_ne_zero (e.symm.injective (by rw [h2, map_zero]))
  refine ⟨Units.mk0 μ hμ, ⟨(b.blockQuiver S hA V φ).withGEquiv (b.blockQuiver_kills S hA hK V φ)
    (b.blockQuiver S hA k (tw (Units.mk0 μ hμ))).g
    (b.blockQuiver_kills S hA hK k (tw (Units.mk0 μ hμ))) e fun a i y ↦ ?_⟩⟩
  simp only [blockQuiver]
  split_ifs
  · rw [hφ]; simp [tw, LinearEquiv.smulOfUnit, Units.smul_def]
  · have h1 := hφ (φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h1
    simp only [tw, LinearEquiv.smulOfUnit]
    show e (φ.symm y) = ((Units.mk0 μ hμ)⁻¹ : kˣ) • e y
    rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, h1, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hμ, one_mul]
  · rfl

end CWord

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hs : w.IsString D)
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The blocks of a string brick are one-dimensional. -/
theorem finrank_eq_one_of_isBrick [FiniteDimensional k V] (hV : 0 < finrank k V)
    (hb : IsBrick B ((w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs))) :
    finrank k V = 1 := by
  by_contra h1
  have h2 : 2 ≤ finrank k V := by omega
  have : Nonempty (w.blockQuiver V hs.1).P := ⟨(0 : Fin (w.len + 1))⟩
  obtain ⟨h, hh0, hni⟩ := exists_rank_one (k := k) h2
  exact (w.blockQuiver V hs.1).not_isBrick_of_end (w.blockQuiver_kills V hs) h
    (fun _ _ _ ↦ rfl) hh0 hni hb

end Word

end BrickAccessibility
