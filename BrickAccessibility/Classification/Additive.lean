module

public import BrickAccessibility.Classification.Natural

/-!
# Additivity of the pair functors

For a finite product `Π i, N i` of modules, `h⁺` and `h⁻` are computed
componentwise (`mem_plus_pi`, `mem_minus_pi`), hence so are the numerators and
denominators of the pair functors, and their dimensions add up
(`finrank_pnum_pi`, `finrank_pden_pi`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module B (N i)] [∀ i, Module k (N i)] [∀ i, IsScalarTower k B (N i)]

theorem mem_plus_pi (v : D.Q.V) (s : Bool) (h : HWord D.Q) (x : ∀ i, N i) :
    x ∈ S.plus (∀ i, N i) v s h ↔ ∀ i, x i ∈ S.plus (N i) v s h := by
  constructor
  · intro hx i
    exact S.map_plus_le (LinearMap.proj (R := B) (φ := N) i) v s h ⟨x, hx, rfl⟩
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    exact S.map_plus_le (LinearMap.single B N i) v s h ⟨x i, hx i, rfl⟩

theorem mem_minus_pi (v : D.Q.V) (s : Bool) (h : HWord D.Q) (x : ∀ i, N i) :
    x ∈ S.minus (∀ i, N i) v s h ↔ ∀ i, x i ∈ S.minus (N i) v s h := by
  constructor
  · intro hx i
    exact S.map_minus_le (LinearMap.proj (R := B) (φ := N) i) v s h ⟨x, hx, rfl⟩
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    exact S.map_minus_le (LinearMap.single B N i) v s h ⟨x i, hx i, rfl⟩

theorem mem_pnum_pi (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) (x : ∀ i, N i) :
    x ∈ S.pnum (∀ i, N i) v s h h' ↔ ∀ i, x i ∈ S.pnum (N i) v s h h' := by
  simp only [Signs.pnum, Submodule.mem_inf, mem_plus_pi S N]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

theorem mem_pden_pi (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) (x : ∀ i, N i) :
    x ∈ S.pden (∀ i, N i) v s h h' ↔ ∀ i, x i ∈ S.pden (N i) v s h h' := by
  constructor
  · intro hx i
    exact S.map_pden_le _ (LinearMap.proj (R := B) (φ := N) i) v s h h' ⟨x, hx, rfl⟩
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    exact S.map_pden_le _ (LinearMap.single B N i) v s h h' ⟨x i, hx i, rfl⟩

omit [DecidableEq ι] in
/-- A submodule of a product given componentwise has the sum of the dimensions. -/
theorem finrank_of_components [∀ i, FiniteDimensional k (N i)] (P : Submodule k (∀ i, N i))
    (Q : ∀ i, Submodule k (N i)) (hPQ : ∀ x, x ∈ P ↔ ∀ i, x i ∈ Q i) :
    finrank k P = ∑ i, finrank k (Q i) := by
  let e : P ≃ₗ[k] (∀ i, Q i) :=
    { toFun := fun x i ↦ ⟨x.1 i, (hPQ x.1).mp x.2 i⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun y ↦ ⟨fun i ↦ (y i).1, (hPQ _).mpr fun i ↦ (y i).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

theorem finrank_pnum_pi [∀ i, FiniteDimensional k (N i)] (v : D.Q.V) (s : Bool)
    (h h' : HWord D.Q) :
    finrank k (S.pnum (∀ i, N i) v s h h') = ∑ i, finrank k (S.pnum (N i) v s h h') :=
  finrank_of_components N _ _ (mem_pnum_pi S N v s h h')

theorem finrank_pden_pi [∀ i, FiniteDimensional k (N i)] (v : D.Q.V) (s : Bool)
    (h h' : HWord D.Q) :
    finrank k (S.pden (∀ i, N i) v s h h') = ∑ i, finrank k (S.pden (N i) v s h h') :=
  finrank_of_components N _ _ (mem_pden_pi S N v s h h')

end MonomialData

end BrickAccessibility
