module

public import BrickAccessibility.Quiver.PathData
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Monomial algebras and their representations

`MonomialData k A` is path data whose path values span `A` and whose nonzero
path values are linearly independent; equivalently `A ≅ kQ/I` with `I` spanned
by the paths it contains. This is the setting of string algebras.

A representation (`Rep`) of the quiver on a `k`-vector space in which the zero
paths act as zero becomes an `A`-module (`Rep.Carrier`), with `e v` and `α a`
acting by the given maps. A `k`-linear map between `A`-modules commuting with
the vertex and arrow actions is `A`-linear (`linearMap_of_commute`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

variable (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A]

/-- Path data for which the nonzero path values form a basis. -/
structure MonomialData where
  /-- The quiver. -/
  Q : FinQuiver
  /-- The path data. -/
  toPathData : PathData Q A
  span_pval : Submodule.span k
    (Set.range (fun p : Q.V × List Q.A ↦ toPathData.pval p.1 p.2)) = ⊤
  linIndep : LinearIndependent k
    (fun p : {p : Q.V × List Q.A // toPathData.pval p.1 p.2 ≠ 0} ↦ toPathData.pval p.1.1 p.1.2)
  e_ne : ∀ v, toPathData.e v ≠ 0

namespace MonomialData

variable {k A} (D : MonomialData k A)

/-- Vertex idempotents. -/
abbrev e := D.toPathData.e
/-- Arrow elements. -/
abbrev α := D.toPathData.α
/-- Path values. -/
abbrev pval := D.toPathData.pval

/-- The nonzero paths. -/
abbrev NZPath := {p : D.Q.V × List D.Q.A // D.pval p.1 p.2 ≠ 0}

theorem span_nz : Submodule.span k (Set.range (fun p : D.NZPath ↦ D.pval p.1.1 p.1.2)) = ⊤ := by
  rw [eq_top_iff, ← D.span_pval]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, rfl⟩
  by_cases h : D.pval p.1 p.2 = 0
  · simp [h]
  · exact Submodule.subset_span ⟨⟨p, h⟩, rfl⟩

/-- The basis of nonzero paths. -/
def basis : Module.Basis D.NZPath k A :=
  Module.Basis.mk D.linIndep (by rw [D.span_nz])

theorem basis_apply (p : D.NZPath) : D.basis p = D.pval p.1.1 p.1.2 := by
  simp [basis]

/-! ### Representations -/

/-- A representation of the quiver on `V` in which zero paths act as zero. -/
structure Rep (V : Type*) [AddCommGroup V] [Module k V] where
  /-- The vertex and arrow maps. -/
  toPathData : PathData D.Q (Module.End k V)
  zero : ∀ x l, D.pval x l = 0 → toPathData.pval x l = 0

namespace Rep

variable {D} {V : Type*} [AddCommGroup V] [Module k V] (R : D.Rep V)

/-- The action of `A` on `V`, defined on the basis of nonzero paths. -/
def actL : A →ₗ[k] Module.End k V :=
  D.basis.constr k (fun p ↦ R.toPathData.pval p.1.1 p.1.2)

theorem actL_pval (x : D.Q.V) (l : List D.Q.A) :
    R.actL (D.pval x l) = R.toPathData.pval x l := by
  by_cases h : D.pval x l = 0
  · rw [h, map_zero, R.zero x l h]
  · have := D.basis.constr_basis k (fun p : D.NZPath ↦ R.toPathData.pval p.1.1 p.1.2) ⟨(x, l), h⟩
    rw [basis_apply] at this
    exact this

theorem actL_mul_pval (x y : D.Q.V) (l₁ l₂ : List D.Q.A) :
    R.actL (D.pval y l₂ * D.pval x l₁) = R.actL (D.pval y l₂) * R.actL (D.pval x l₁) := by
  rw [R.actL_pval, R.actL_pval, D.toPathData.pval_mul_pval, R.toPathData.pval_mul_pval]
  split_ifs
  · exact R.actL_pval x _
  · exact map_zero _

theorem actL_mul (a b : A) : R.actL (a * b) = R.actL a * R.actL b := by
  have hspan := D.span_pval
  have ha : a ∈ Submodule.span k (Set.range (fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  have hb : b ∈ Submodule.span k (Set.range (fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨⟨y, l₂⟩, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨⟨x, l₁⟩, rfl⟩ := hb
          exact R.actL_mul_pval x y l₁ l₂
      | zero => simp
      | add b c _ _ hb hc => simp only [mul_add, map_add, hb, hc]
      | smul c b _ hb => simp only [mul_smul_comm, map_smul, hb]
  | zero => simp
  | add a c _ _ ha hc => simp only [add_mul, map_add, ha, hc]
  | smul c a _ ha => simp only [smul_mul_assoc, map_smul, ha]

theorem actL_one : R.actL 1 = 1 := by
  rw [← D.toPathData.sum_e, ← R.toPathData.sum_e, map_sum]
  exact Finset.sum_congr rfl fun v _ ↦ R.actL_pval v []

/-- The action as an algebra homomorphism. -/
def act : A →ₐ[k] Module.End k V :=
  AlgHom.ofLinearMap R.actL R.actL_one R.actL_mul

/-- The underlying space of a representation, as an `A`-module. -/
def Carrier (_R : D.Rep V) : Type _ := V

instance : AddCommGroup R.Carrier := inferInstanceAs (AddCommGroup V)
instance : Module k R.Carrier := inferInstanceAs (Module k V)
instance : Module A R.Carrier := Module.compHom V R.act.toRingHom
instance [FiniteDimensional k V] : FiniteDimensional k R.Carrier :=
  inferInstanceAs (FiniteDimensional k V)

theorem smul_def (a : A) (v : R.Carrier) : a • v = R.act a v := rfl

instance : IsScalarTower k A R.Carrier where
  smul_assoc c a v := by
    rw [smul_def, smul_def, map_smul]
    rfl

theorem e_smul (v : D.Q.V) (m : R.Carrier) : D.e v • m = R.toPathData.e v m := by
  rw [smul_def]
  have := R.actL_pval v []
  simp only [PathData.pval] at this
  exact LinearMap.congr_fun this m

theorem α_smul (a : D.Q.A) (m : R.Carrier) : D.α a • m = R.toPathData.α a m := by
  rw [smul_def]
  have := R.actL_pval (D.Q.src a) [a]
  have h1 : D.pval (D.Q.src a) [a] = D.α a := D.toPathData.pval_single_src a
  rw [h1, R.toPathData.pval_single_src] at this
  exact LinearMap.congr_fun this m

/-- The `k`-linear identification of the carrier with `V`. -/
def equivV : R.Carrier ≃ₗ[k] V := LinearEquiv.refl k V

end Rep

/-! ### Homomorphisms -/

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- A `k`-linear map commuting with the vertex and arrow actions is `A`-linear. -/
def linearMap_of_commute (f : M →ₗ[k] N) (he : ∀ v m, f (D.e v • m) = D.e v • f m)
    (hα : ∀ a m, f (D.α a • m) = D.α a • f m) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro a m
    have hp : ∀ x l m, f (D.pval x l • m) = D.pval x l • f m := by
      intro x l
      induction l generalizing x with
      | nil => exact he x
      | cons b l ih =>
          intro m
          simp only [PathData.pval, mul_smul]
          rw [ih, hα, he]
    have ha : a ∈ Submodule.span k (Set.range (fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2)) := by
      rw [D.span_pval]; trivial
    induction ha using Submodule.span_induction generalizing m with
    | mem a ha =>
        obtain ⟨⟨x, l⟩, rfl⟩ := ha
        exact hp x l m
    | zero => simp
    | add a b _ _ ha hb => simp only [add_smul, map_add, ha, hb, RingHom.id_apply]
    | smul c a _ ha =>
        simp only [RingHom.id_apply] at ha ⊢
        rw [smul_assoc, LinearMap.map_smul_of_tower, ha, smul_assoc]

@[simp] theorem linearMap_of_commute_apply (f : M →ₗ[k] N) (he hα) (m : M) :
    D.linearMap_of_commute f he hα m = f m := rfl

end MonomialData

end BrickAccessibility
