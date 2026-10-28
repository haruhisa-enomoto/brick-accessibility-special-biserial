module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Bricks

Library conventions: `A` is a `k`-algebra and modules are left `A`-modules
with a compatible `k`-structure. Right modules over `Λ` are modules over
`A = Λᵐᵒᵖ`.

* `IsBrick`: a nonzero module whose nonzero endomorphisms are invertible.
* Over an algebraically closed field, a finite-dimensional brick has
  endomorphisms `k · id` (`IsBrick.exists_eq_smul_id`), and conversely a nonzero
  module with at most one-dimensional endomorphism space is a brick.
* `IsBrick.hom_eq_zero_of_ne_zero`: equation (2.1) of the manuscript; a simple
  module cannot lie in both the top and the socle of a nonsimple brick.
* `IsBrick.of_surjective_of_projective`: Lemma 2.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

variable (A : Type*) [Ring A]

/-- A brick: a nonzero module whose nonzero endomorphisms are invertible. -/
def IsBrick (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  Nontrivial M ∧ ∀ f : M →ₗ[A] M, f ≠ 0 → IsUnit f

variable {A}

section Field

variable {k : Type*} [Field k] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- Over an algebraically closed field every endomorphism of a finite-dimensional
brick is a scalar. -/
theorem IsBrick.exists_eq_smul_id [IsAlgClosed k] [FiniteDimensional k M] (hM : IsBrick A M)
    (f : M →ₗ[A] M) : ∃ c : k, f = c • (LinearMap.id : M →ₗ[A] M) := by
  have := hM.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrictScalars k)
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : f - c • (LinearMap.id : M →ₗ[A] M) ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hu := hM.2 _ hne'
  have hinj : Function.Injective (f - c • (LinearMap.id : M →ₗ[A] M)) := by
    obtain ⟨g, hg⟩ := hu
    rw [← hg]
    exact (Module.End.isUnit_iff _).mp g.isUnit |>.1
  apply hv.2
  apply hinj
  have := hv.apply_eq_smul
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_zero]
  rw [show f v = c • v from this, sub_self]

/-- Linear maps between finite-dimensional modules form a finite-dimensional
space. -/
instance finiteDimensional_hom {N : Type*} [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (M →ₗ[A] N) := by
  let ι : (M →ₗ[A] N) →ₗ[k] (M →ₗ[k] N) :=
    { toFun := fun f ↦ f.restrictScalars k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_injective ι fun f g h ↦ by
    ext x; exact LinearMap.congr_fun h x

theorem IsBrick.finrank_end [IsAlgClosed k] [FiniteDimensional k M] (hM : IsBrick A M) :
    Module.finrank k (M →ₗ[A] M) = 1 := by
  have := hM.1
  have hid : (LinearMap.id : M →ₗ[A] M) ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    intro h; exact hx (by simpa using LinearMap.congr_fun h x)
  rw [finrank_eq_one_iff_of_nonzero' _ hid]
  intro f
  obtain ⟨c, hc⟩ := hM.exists_eq_smul_id (k := k) f
  exact ⟨c, hc.symm⟩

/-- A nonzero module whose endomorphism space has dimension at most one is a
brick. -/
theorem isBrick_of_finrank_end_le_one [FiniteDimensional k M] [Nontrivial M]
    (h : Module.finrank k (M →ₗ[A] M) ≤ 1) : IsBrick A M := by
  refine ⟨inferInstance, fun f hf ↦ ?_⟩
  have hid : (LinearMap.id : M →ₗ[A] M) ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    intro h; exact hx (by simpa using LinearMap.congr_fun h x)
  have h1 : Module.finrank k (M →ₗ[A] M) = 1 := by
    have : 0 < Module.finrank k (M →ₗ[A] M) := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid⟩
    omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).mp h1 f
  have hc0 : c ≠ 0 := by rintro rfl; apply hf; rw [← hc, zero_smul]
  rw [← hc]
  refine ⟨⟨c • (LinearMap.id : M →ₗ[A] M), c⁻¹ • LinearMap.id, ?_, ?_⟩, rfl⟩ <;>
    ext x <;> simp [smul_smul, hc0]

end Field

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- A brick is indecomposable. -/
theorem IsBrick.compl_eq_bot (hM : IsBrick A M) {P R : Submodule A M} (hPR : IsCompl P R) :
    P = ⊥ ∨ R = ⊥ := by
  by_contra h
  push Not at h
  obtain ⟨hP, hR⟩ := h
  let f : M →ₗ[A] M := P.projection R hPR
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hf : f ≠ 0 := by
    intro h0
    have := LinearMap.congr_fun h0 x
    rw [Submodule.projection_apply_left hPR ⟨x, hxP⟩] at this
    exact hx0 this
  obtain ⟨u, hu⟩ := hM.2 f hf
  have hinj : Function.Injective f := by
    rw [← hu]; exact ((Module.End.isUnit_iff _).mp u.isUnit).1
  obtain ⟨y, hyR, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  apply hy0
  apply hinj
  rw [map_zero]
  exact Submodule.projection_apply_right hPR ⟨y, hyR⟩

/-- A nonzero homomorphism out of a simple module is injective. -/
theorem injective_of_ne_zero {S : Type*} [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    {f : S →ₗ[A] M} (hf : f ≠ 0) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  refine (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker f)).resolve_right fun h ↦ hf ?_
  exact LinearMap.ker_eq_top.mp h

/-- Equation (2.1): a simple module cannot lie in both the socle and the top of
a nonsimple brick. -/
theorem IsBrick.hom_eq_zero_of_ne_zero (hM : IsBrick A M) (hns : ¬ IsSimpleModule A M)
    {S : Type*} [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    {f : S →ₗ[A] M} (hf : f ≠ 0) (g : M →ₗ[A] S) : g = 0 := by
  by_contra hg
  have hgsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range g)).resolve_left fun h ↦ hg ?_
    exact LinearMap.range_eq_bot.mp h
  have hfg : f ∘ₗ g ≠ 0 := by
    intro h0
    apply hf
    ext s
    obtain ⟨m, rfl⟩ := hgsurj s
    exact LinearMap.congr_fun h0 m
  obtain ⟨u, hu⟩ := hM.2 _ hfg
  have hbij : Function.Bijective (f ∘ₗ g) := by
    rw [← hu]; exact (Module.End.isUnit_iff _).mp u.isUnit
  have hginj : Function.Injective g := fun a b h ↦ hbij.1 (by simp [h])
  exact hns (IsSimpleModule.congr (LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩))

/-- Lemma 2.3: every nonzero quotient of a finite-dimensional projective brick is
a brick (over an algebraically closed field). -/
theorem IsBrick.of_surjective_of_projective {k : Type*} [Field k] [IsAlgClosed k] [Algebra k A]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] [Module.Projective A M]
    (hM : IsBrick A M) {N : Type*} [AddCommGroup N] [Module A N] [Nontrivial N]
    (q : M →ₗ[A] N) (hq : Function.Surjective q) : IsBrick A N := by
  refine ⟨inferInstance, fun f hf ↦ ?_⟩
  obtain ⟨g, hg⟩ := Module.projective_lifting_property q (f ∘ₗ q) hq
  obtain ⟨c, hc⟩ := hM.exists_eq_smul_id (k := k) g
  have hfq : ∀ m, f (q m) = (algebraMap k A c) • q m := by
    intro m
    have := LinearMap.congr_fun hg m
    simp only [LinearMap.comp_apply] at this
    rw [← this, hc, LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul A c m, map_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hf
    ext n
    obtain ⟨m, rfl⟩ := hq n
    simp [hfq]
  have hf' : ∀ n, f n = (algebraMap k A c) • n := by
    intro n
    obtain ⟨m, rfl⟩ := hq n
    exact hfq m
  obtain ⟨u, hu⟩ := (isUnit_iff_ne_zero.mpr hc0).map (algebraMap k A)
  rw [Module.End.isUnit_iff]
  constructor
  · intro n n' h
    rw [hf', hf', ← hu] at h
    rw [← Units.smul_def, ← Units.smul_def] at h
    exact (MulAction.injective u) h
  · intro n
    refine ⟨(↑u⁻¹ : A) • n, ?_⟩
    rw [hf', ← hu, ← Units.smul_def, ← Units.smul_def, smul_inv_smul]

end BrickAccessibility
