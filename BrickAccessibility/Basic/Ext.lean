module

public import BrickAccessibility.Basic.Brick
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# First extension groups as derivations modulo inner derivations

For a `k`-algebra `A` and `A`-modules `M`, `X`, we model `Ext¹_A(M, X)` as the
`k`-linear derivations `δ : A → Hom_k(M, X)`, meaning
`δ(ab)(m) = a • δ(b)(m) + δ(a)(b • m)`, modulo the inner derivations
`a ↦ (m ↦ a • φ(m) - φ(a • m))`. A derivation `δ` describes the extension
`X ⊕ M` with action `a • (x, m) = (a • x + δ(a)(m), a • m)`.

* `Ext1.finrank_hom_le`: for a surjection `q : M → N` with kernel `L`, the
  dimension of `Hom(M', N)` is at most that of the image of `Hom(M', M)` plus
  that of `Ext¹(M', L)`. This is the part of the long exact sequence used in
  Step 2 of Proposition 2.1.
* `Ext1.finrank_congr`: isomorphic second arguments give the same dimension.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

variable (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A]
variable (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable (X : Type*) [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]

/-- Postcomposition with an `A`-linear map, as a `k`-linear map on Hom spaces. -/
def postcomp {M' N : Type*} [AddCommGroup M'] [Module A M'] [Module k M'] [IsScalarTower k A M']
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] (q : M →ₗ[A] N) :
    (M' →ₗ[A] M) →ₗ[k] (M' →ₗ[A] N) where
  toFun f := q ∘ₗ f
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

/-- Precomposition with an `A`-linear map, as a `k`-linear map on Hom spaces. -/
def precomp {M' : Type*} [AddCommGroup M'] [Module A M'] [Module k M'] [IsScalarTower k A M']
    (f : M' →ₗ[A] M) : (M →ₗ[A] X) →ₗ[k] (M' →ₗ[A] X) where
  toFun g := g ∘ₗ f
  map_add' g h := by ext; simp
  map_smul' c g := by ext; simp

namespace Ext1

/-- Derivations `A → Hom_k(M, X)`. -/
def cocycles : Submodule k (A →ₗ[k] M →ₗ[k] X) where
  carrier := {δ | ∀ a b m, δ (a * b) m = a • δ b m + δ a (b • m)}
  add_mem' := by
    intro δ δ' hδ hδ' a b m
    simp only [LinearMap.add_apply, hδ a b m, hδ' a b m, smul_add]
    abel
  zero_mem' := by intro a b m; simp
  smul_mem' := by
    intro c δ hδ a b m
    simp only [LinearMap.smul_apply, hδ a b m, smul_add]
    rw [smul_comm c a]

/-- The inner derivation of a `k`-linear map. -/
def inner : (M →ₗ[k] X) →ₗ[k] (A →ₗ[k] M →ₗ[k] X) where
  toFun φ :=
    { toFun := fun a ↦
        { toFun := fun m ↦ a • φ m - φ (a • m)
          map_add' := fun m m' ↦ by simp [smul_add]; abel
          map_smul' := fun c m ↦ by
            rw [RingHom.id_apply, smul_sub, map_smul, smul_comm a c m, map_smul,
              smul_comm a c (φ m)] }
      map_add' := fun a b ↦ by ext m; simp [add_smul]; abel
      map_smul' := fun c a ↦ by ext m; simp [smul_sub, smul_assoc] }
  map_add' := fun φ ψ ↦ by ext a m; simp [smul_add]; abel
  map_smul' := fun c φ ↦ by ext a m; simp [smul_sub, smul_comm c a]

theorem inner_apply (φ : M →ₗ[k] X) (a : A) (m : M) :
    inner k A M X φ a m = a • φ m - φ (a • m) := rfl

theorem range_inner_le : LinearMap.range (inner k A M X) ≤ cocycles k A M X := by
  rintro _ ⟨φ, rfl⟩ a b m
  simp only [inner_apply, mul_smul, smul_sub]
  abel

/-- The inner derivations. -/
abbrev coboundaries : Submodule k (A →ₗ[k] M →ₗ[k] X) := LinearMap.range (inner k A M X)

end Ext1

/-- `Ext¹_A(M, X)`, modelled as the image of the derivations in the space of all
`k`-linear maps `A → Hom_k(M, X)` modulo the inner derivations. -/
def Ext1 : Submodule k ((A →ₗ[k] M →ₗ[k] X) ⧸ Ext1.coboundaries k A M X) :=
  (Ext1.cocycles k A M X).map (Ext1.coboundaries k A M X).mkQ

namespace Ext1

variable {k A M X}

/-- Isomorphic second arguments give isomorphic `Ext¹`. -/
theorem finrank_congr {X' : Type*} [AddCommGroup X'] [Module A X'] [Module k X']
    [IsScalarTower k A X'] (e : X ≃ₗ[A] X') :
    Module.finrank k (Ext1 k A M X) = Module.finrank k (Ext1 k A M X') := by
  let ek : X ≃ₗ[k] X' := e.restrictScalars k
  let P : (A →ₗ[k] M →ₗ[k] X) ≃ₗ[k] (A →ₗ[k] M →ₗ[k] X') :=
    LinearEquiv.congrRight (LinearEquiv.congrRight ek)
  have hP : ∀ δ a m, P δ a m = e (δ a m) := fun _ _ _ ↦ rfl
  have hPZ : (cocycles k A M X).map P.toLinearMap = cocycles k A M X' := by
    ext δ'
    constructor
    · rintro ⟨δ, hδ, rfl⟩ a b m
      simp only [LinearEquiv.coe_coe, hP, hδ a b m, map_add, map_smul]
    · intro hδ'
      refine ⟨P.symm δ', ?_, by simp⟩
      intro a b m
      apply e.injective
      have h1 : ∀ c n, e (P.symm δ' c n) = δ' c n := fun c n ↦ by
        rw [← hP, LinearEquiv.apply_symm_apply]
      rw [map_add, map_smul, h1, h1, h1]
      exact hδ' a b m
  have hPB : (coboundaries k A M X).map P.toLinearMap = coboundaries k A M X' := by
    ext δ'
    constructor
    · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
      refine ⟨ek.toLinearMap ∘ₗ φ, ?_⟩
      ext a m
      simp only [hP, inner_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ek,
        LinearEquiv.restrictScalars_apply, map_sub, map_smul]
    · rintro ⟨φ', rfl⟩
      refine ⟨inner k A M X (ek.symm.toLinearMap ∘ₗ φ'), ⟨_, rfl⟩, ?_⟩
      ext a m
      simp only [LinearEquiv.coe_coe, hP, inner_apply, LinearMap.comp_apply, ek,
        LinearEquiv.restrictScalars_symm_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]
  let Q := Submodule.Quotient.equiv _ _ P hPB
  have hcomp : Q.toLinearMap ∘ₗ (coboundaries k A M X).mkQ =
      (coboundaries k A M X').mkQ ∘ₗ P.toLinearMap := by
    ext δ; simp [Q, Submodule.Quotient.equiv_apply]
  have hQ : (Ext1 k A M X).map Q.toLinearMap = Ext1 k A M X' := by
    rw [Ext1, Ext1, ← Submodule.map_comp, hcomp, Submodule.map_comp, hPZ]
  rw [← hQ]
  exact (Q.submoduleMap (Ext1 k A M X)).finrank_eq

/-- Isomorphic first arguments give isomorphic `Ext¹`. -/
theorem finrank_congr_left {M' : Type*} [AddCommGroup M'] [Module A M'] [Module k M']
    [IsScalarTower k A M'] (e : M ≃ₗ[A] M') :
    Module.finrank k (Ext1 k A M X) = Module.finrank k (Ext1 k A M' X) := by
  let ek : M ≃ₗ[k] M' := e.restrictScalars k
  let P : (A →ₗ[k] M →ₗ[k] X) ≃ₗ[k] (A →ₗ[k] M' →ₗ[k] X) :=
    LinearEquiv.congrRight (LinearEquiv.congrLeft X k ek)
  have hP : ∀ δ a m', P δ a m' = δ a (e.symm m') := fun _ _ _ ↦ rfl
  have hPZ : (cocycles k A M X).map P.toLinearMap = cocycles k A M' X := by
    ext δ'
    constructor
    · rintro ⟨δ, hδ, rfl⟩ a b m'
      simp only [LinearEquiv.coe_coe, hP, hδ a b (e.symm m'), map_smul]
    · intro hδ'
      refine ⟨P.symm δ', ?_, by simp⟩
      intro a b m
      have h1 : ∀ c n, P.symm δ' c n = δ' c (e n) := fun c n ↦ by
        rw [← e.symm_apply_apply n, ← hP, LinearEquiv.apply_symm_apply, e.symm_apply_apply]
      rw [h1, h1, h1, map_smul]
      exact hδ' a b (e m)
  have hPB : (coboundaries k A M X).map P.toLinearMap = coboundaries k A M' X := by
    ext δ'
    constructor
    · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
      refine ⟨φ ∘ₗ ek.symm.toLinearMap, ?_⟩
      ext a m'
      simp only [hP, inner_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ek,
        LinearEquiv.restrictScalars_symm_apply, LinearEquiv.coe_coe, map_smul]
    · rintro ⟨φ', rfl⟩
      refine ⟨inner k A M X (φ' ∘ₗ ek.toLinearMap), ⟨_, rfl⟩, ?_⟩
      ext a m'
      simp only [LinearEquiv.coe_coe, hP, inner_apply, LinearMap.comp_apply, ek,
        LinearEquiv.restrictScalars_apply, map_smul, LinearEquiv.apply_symm_apply]
  let Q := Submodule.Quotient.equiv _ _ P hPB
  have hcomp : Q.toLinearMap ∘ₗ (coboundaries k A M X).mkQ =
      (coboundaries k A M' X).mkQ ∘ₗ P.toLinearMap := by
    ext δ; simp [Q, Submodule.Quotient.equiv_apply]
  have hQ : (Ext1 k A M X).map Q.toLinearMap = Ext1 k A M' X := by
    rw [Ext1, Ext1, ← Submodule.map_comp, hcomp, Submodule.map_comp, hPZ]
  rw [← hQ]
  exact (Q.submoduleMap (Ext1 k A M X)).finrank_eq

section Connecting

variable {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- **Long exact sequence, the part used in Proposition 2.1.** For a surjection
`q : M → N` and any module `M'`, a homomorphism `M' → N` whose connecting class
in `Ext¹(M', ker q)` vanishes lifts through `q`; consequently
`dim Hom(M', N) ≤ dim (q ∘ Hom(M', M)) + dim Ext¹(M', ker q)`. -/
theorem finrank_hom_le [FiniteDimensional k A] (M' : Type*) [AddCommGroup M'] [Module A M']
    [Module k M'] [IsScalarTower k A M'] [FiniteDimensional k M'] [FiniteDimensional k M]
    [FiniteDimensional k N] (q : M →ₗ[A] N) (hq : Function.Surjective q) :
    Module.finrank k (M' →ₗ[A] N) ≤
      Module.finrank k (LinearMap.range (postcomp k A M q : (M' →ₗ[A] M) →ₗ[k] (M' →ₗ[A] N))) +
      Module.finrank k (Ext1 k A M' (LinearMap.ker q)) := by
  classical
  haveI : FiniteDimensional k (LinearMap.ker q) :=
    Module.Finite.of_injective ((LinearMap.ker q).subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨σ, hσ⟩ := (q.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hq)
  have hqσ : ∀ n, q (σ n) = n := fun n ↦ LinearMap.congr_fun hσ n
  have hmem : ∀ (φ : M' →ₗ[A] N) (a : A) (m : M'),
      a • σ (φ m) - σ (φ (a • m)) ∈ LinearMap.ker q := by
    intro φ a m
    simp [LinearMap.mem_ker, hqσ]
  let D : (M' →ₗ[A] N) →ₗ[k] (A →ₗ[k] M' →ₗ[k] LinearMap.ker q) :=
    { toFun := fun φ ↦
        { toFun := fun a ↦
            { toFun := fun m ↦ ⟨a • σ (φ m) - σ (φ (a • m)), hmem φ a m⟩
              map_add' := fun m m' ↦ by
                apply Subtype.ext; simp [smul_add]; abel
              map_smul' := fun c m ↦ by
                apply Subtype.ext
                show a • σ (φ (c • m)) - σ (φ (a • c • m)) =
                  c • (a • σ (φ m) - σ (φ (a • m)))
                rw [smul_comm a c m, LinearMap.map_smul_of_tower φ c,
                  LinearMap.map_smul_of_tower φ c, map_smul σ, map_smul σ, smul_comm a c,
                  smul_sub] }
          map_add' := fun a b ↦ by
            ext m; simp [add_smul]; abel
          map_smul' := fun c a ↦ by
            ext m; simp [smul_sub, smul_assoc] }
      map_add' := fun φ ψ ↦ by
        ext a m; simp [smul_add]; abel
      map_smul' := fun c φ ↦ by
        ext a m; simp [smul_sub, smul_comm c a]; rw [smul_comm a c, map_smul] }
  have hD : ∀ φ a m, (D φ a m : M) = a • σ (φ m) - σ (φ (a • m)) := fun _ _ _ ↦ rfl
  have hDZ : ∀ φ, D φ ∈ cocycles k A M' (LinearMap.ker q) := by
    intro φ a b m
    apply Subtype.ext
    simp only [hD, Submodule.coe_add, SetLike.val_smul, mul_smul, smul_sub, map_smul]
    abel
  let δ : (M' →ₗ[A] N) →ₗ[k] _ :=
    { toFun := fun φ ↦ (coboundaries k A M' (LinearMap.ker q)).mkQ (D φ)
      map_add' := fun φ ψ ↦ by rw [map_add, map_add]
      map_smul' := fun c φ ↦ by rw [map_smul, map_smul]; rfl }
  have hrange : LinearMap.range δ ≤ Ext1 k A M' (LinearMap.ker q) := by
    rintro _ ⟨φ, rfl⟩
    exact ⟨D φ, hDZ φ, rfl⟩
  have hker : LinearMap.ker δ ≤ LinearMap.range (postcomp k A M q :
      (M' →ₗ[A] M) →ₗ[k] (M' →ₗ[A] N)) := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ
    change (coboundaries k A M' (LinearMap.ker q)).mkQ (D φ) = 0 at hφ
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hφ
    obtain ⟨χ, hχ⟩ := hφ
    have hχ' : ∀ (a : A) (m : M'), a • (χ m : M) - (χ (a • m) : M) = a • σ (φ m) - σ (φ (a • m)) := by
      intro a m
      have := congrArg (fun f : A →ₗ[k] M' →ₗ[k] LinearMap.ker q ↦ (f a m : M)) hχ
      simp only [inner_apply, Submodule.coe_sub, Submodule.coe_smul] at this
      rw [this, hD]
    let ψ : M' →ₗ[A] M :=
      { toFun := fun m ↦ σ (φ m) - χ m
        map_add' := fun m m' ↦ by simp; abel
        map_smul' := fun a m ↦ by
          have := hχ' a m
          simp only [RingHom.id_apply, smul_sub]
          calc σ (φ (a • m)) - (χ (a • m) : M)
              = (a • (χ m : M) - (χ (a • m) : M)) + σ (φ (a • m)) - a • (χ m : M) := by abel
            _ = (a • σ (φ m) - σ (φ (a • m))) + σ (φ (a • m)) - a • (χ m : M) := by rw [this]
            _ = a • σ (φ m) - a • (χ m : M) := by abel }
    refine ⟨ψ, ?_⟩
    ext m
    simp [postcomp, ψ, hqσ]
  have h1 := LinearMap.finrank_range_add_finrank_ker δ
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  omega

set_option maxHeartbeats 1000000 in
/-- **Contravariant connecting inequality.** For a submodule `p ⊆ M` and any
module `X`, `dim Hom(p, X) ≤ dim (Hom(M, X) ∘ incl) + dim Ext¹(M / p, X)`. -/
theorem finrank_hom_sub_le [FiniteDimensional k A] [FiniteDimensional k M]
    [FiniteDimensional k X] (p : Submodule A M) [FiniteDimensional k p] :
    Module.finrank k (p →ₗ[A] X) ≤
      Module.finrank k (LinearMap.range (precomp k A M X p.subtype :
        (M →ₗ[A] X) →ₗ[k] (p →ₗ[A] X))) +
      Module.finrank k (Ext1 k A (M ⧸ p) X) := by
  classical
  have : FiniteDimensional k (M ⧸ p) :=
    Module.Finite.of_surjective (p.mkQ.restrictScalars k) (Submodule.mkQ_surjective p)
  obtain ⟨τ, hτ⟩ := (p.subtype.restrictScalars k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hτp : ∀ x : p, τ x = x := fun x ↦ LinearMap.congr_fun hτ x
  obtain ⟨σ, hσ⟩ := (p.mkQ.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective p))
  have hσq : ∀ x, p.mkQ (σ x) = x := fun x ↦ LinearMap.congr_fun hσ x
  -- the inner derivation of `φ ∘ τ`, which kills `p`
  let d : (p →ₗ[A] X) → A → M → X := fun φ a m ↦ a • φ (τ m) - φ (τ (a • m))
  have hdp : ∀ φ a (m : M), m ∈ p → d φ a m = 0 := by
    intro φ a m hm
    have h1 : τ m = ⟨m, hm⟩ := by rw [← hτp ⟨m, hm⟩]
    have h2 : τ (a • m) = a • (⟨m, hm⟩ : p) := by rw [← hτp (a • ⟨m, hm⟩)]; rfl
    simp only [d, h1, h2, map_smul, sub_self]
  have hdadd : ∀ φ a (m m' : M), d φ a (m + m') = d φ a m + d φ a m' := by
    intro φ a m m'; simp only [d, smul_add, map_add]; abel
  have hdq : ∀ φ a (m : M), d φ a (σ (p.mkQ m)) = d φ a m := by
    intro φ a m
    have hmem : σ (p.mkQ m) - m ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
      exact hσq (p.mkQ m)
    have := hdadd φ a (σ (p.mkQ m) - m) m
    rw [sub_add_cancel, hdp φ a _ hmem, zero_add] at this
    exact this
  let D : (p →ₗ[A] X) →ₗ[k] (A →ₗ[k] (M ⧸ p) →ₗ[k] X) :=
    { toFun := fun φ ↦
        { toFun := fun a ↦
            { toFun := fun x ↦ d φ a (σ x)
              map_add' := fun x x' ↦ by rw [map_add, hdadd]
              map_smul' := fun c x ↦ by
                show a • φ (τ (σ (c • x))) - φ (τ (a • σ (c • x))) =
                  c • (a • φ (τ (σ x)) - φ (τ (a • σ x)))
                rw [map_smul σ, map_smul τ, LinearMap.map_smul_of_tower φ,
                  smul_comm a c (σ x), map_smul τ, LinearMap.map_smul_of_tower φ,
                  smul_comm a c, smul_sub] }
          map_add' := fun a b ↦ by
            ext x
            show (a + b) • φ (τ (σ x)) - φ (τ ((a + b) • σ x)) =
              (a • φ (τ (σ x)) - φ (τ (a • σ x))) + (b • φ (τ (σ x)) - φ (τ (b • σ x)))
            rw [add_smul, add_smul, map_add, map_add]; abel
          map_smul' := fun c a ↦ by
            ext x
            show (c • a) • φ (τ (σ x)) - φ (τ ((c • a) • σ x)) =
              c • (a • φ (τ (σ x)) - φ (τ (a • σ x)))
            rw [smul_assoc, smul_assoc, map_smul τ, LinearMap.map_smul_of_tower φ, smul_sub] }
      map_add' := fun φ ψ ↦ by
        ext a x
        show a • (φ + ψ) (τ (σ x)) - (φ + ψ) (τ (a • σ x)) =
          (a • φ (τ (σ x)) - φ (τ (a • σ x))) + (a • ψ (τ (σ x)) - ψ (τ (a • σ x)))
        rw [LinearMap.add_apply, LinearMap.add_apply, smul_add]; abel
      map_smul' := fun c φ ↦ by
        ext a x
        show a • (c • φ) (τ (σ x)) - (c • φ) (τ (a • σ x)) =
          c • (a • φ (τ (σ x)) - φ (τ (a • σ x)))
        rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_comm a c, smul_sub] }
  have hD : ∀ φ a m, D φ a (p.mkQ m) = d φ a m := fun φ a m ↦ hdq φ a m
  have hDZ : ∀ φ, D φ ∈ cocycles k A (M ⧸ p) X := by
    intro φ a b x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective p x
    have hb : b • p.mkQ m = p.mkQ (b • m) := (p.mkQ.map_smul b m).symm
    rw [hb, hD, hD, hD]
    simp only [d, mul_smul, smul_sub, map_smul]
    abel
  let δ : (p →ₗ[A] X) →ₗ[k] _ :=
    { toFun := fun φ ↦ (coboundaries k A (M ⧸ p) X).mkQ (D φ)
      map_add' := fun φ ψ ↦ by rw [map_add, map_add]
      map_smul' := fun c φ ↦ by rw [map_smul, map_smul]; rfl }
  have hrange : LinearMap.range δ ≤ Ext1 k A (M ⧸ p) X := by
    rintro _ ⟨φ, rfl⟩
    exact ⟨D φ, hDZ φ, rfl⟩
  have hker : LinearMap.ker δ ≤ LinearMap.range (precomp k A M X p.subtype :
      (M →ₗ[A] X) →ₗ[k] (p →ₗ[A] X)) := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ
    change (coboundaries k A (M ⧸ p) X).mkQ (D φ) = 0 at hφ
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hφ
    obtain ⟨χ, hχ⟩ := hφ
    have hχ' : ∀ (a : A) (m : M), a • χ (p.mkQ m) - χ (a • p.mkQ m) = d φ a m := by
      intro a m
      have := LinearMap.congr_fun (LinearMap.congr_fun hχ a) (p.mkQ m)
      rw [inner_apply] at this
      rw [this, hD]
    let ψ : M →ₗ[A] X :=
      { toFun := fun m ↦ φ (τ m) - χ (p.mkQ m)
        map_add' := fun m m' ↦ by simp only [map_add]; abel
        map_smul' := fun a m ↦ by
          have := hχ' a m
          simp only [d] at this
          simp only [RingHom.id_apply, smul_sub, map_smul]
          calc φ (τ (a • m)) - χ (a • p.mkQ m)
              = (a • χ (p.mkQ m) - χ (a • p.mkQ m)) + φ (τ (a • m)) - a • χ (p.mkQ m) := by
                abel
            _ = (a • φ (τ m) - φ (τ (a • m))) + φ (τ (a • m)) - a • χ (p.mkQ m) := by
                rw [this]
            _ = a • φ (τ m) - a • χ (p.mkQ m) := by abel }
    refine ⟨ψ, ?_⟩
    ext x
    have hx : (Submodule.Quotient.mk (x : M) : M ⧸ p) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr x.2
    simp [precomp, ψ, hτp, hx]
  have h1 := LinearMap.finrank_range_add_finrank_ker δ
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  omega

end Connecting

end Ext1

end BrickAccessibility
