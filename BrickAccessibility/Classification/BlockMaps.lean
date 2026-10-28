module

public import BrickAccessibility.Classification.BlockTransport

/-!
# Maps out of block quiver modules

A family of linear maps `ψ j : V → M_{vtx j}` that intertwines the moves
(`a ψ_i = ψ_j ∘ g a i` when `a` moves `i` to `j`) and is killed by arrows without
a move gives a module homomorphism `f ↦ Σ_j ψ_j (f j)` (`Compat.toHom`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
variable (C : D.BlockQuiver V) (hC : C.KillsZeroPaths)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

namespace BlockQuiver

/-- A compatible family of maps from the blocks into `M`. -/
structure Compat where
  ψ : C.P → V →ₗ[k] M
  mem_vsp : ∀ j y, ψ j y ∈ D.vsp M (C.vtx j)
  move : ∀ a i j y, C.next a i = some j → D.α a • ψ i y = ψ j (C.g a i y)
  kill : ∀ a i y, C.next a i = none → D.α a • ψ i y = 0

variable {C M}

theorem e_smul_of_mem_vsp {v w : D.Q.V} {x : M} (hx : x ∈ D.vsp M w) :
    D.e v • x = if w = v then x else 0 := by
  rw [D.mem_vsp] at hx
  rw [← hx, ← mul_smul, D.toPathData.e_mul_e]
  split_ifs with h1 h2 h2
  · subst h1; rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact zero_smul _ _

/-- The underlying linear map. -/
def Compat.toLin (F : C.Compat M) : C.Mod hC →ₗ[k] M where
  toFun f := ∑ j, F.ψ j (C.val hC f j)
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum]

theorem Compat.toLin_apply (F : C.Compat M) (f : C.Mod hC) :
    F.toLin hC f = ∑ j, F.ψ j (C.val hC f j) := rfl

theorem Compat.toLin_e (F : C.Compat M) (v : D.Q.V) (f : C.Mod hC) :
    F.toLin hC (D.e v • f) = D.e v • F.toLin hC f := by
  simp only [Compat.toLin_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [e_smul_val, e_smul_of_mem_vsp (F.mem_vsp j _)]
  split_ifs <;> simp

theorem Compat.toLin_α (F : C.Compat M) (a : D.Q.A) (f : C.Mod hC) :
    F.toLin hC (D.α a • f) = D.α a • F.toLin hC f := by
  classical
  simp only [Compat.toLin_apply, Finset.smul_sum, α_smul_val, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases h : C.next a i with
  | none =>
      rw [F.kill a i _ h]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp
  | some j =>
      rw [F.move a i j _ h, Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'; simp [Ne.symm hj']
      · simp

/-- The module homomorphism of a compatible family. -/
def Compat.toHom (F : C.Compat M) : C.Mod hC →ₗ[B] M :=
  D.linearMap_of_commute (F.toLin hC) (F.toLin_e hC) (F.toLin_α hC)

theorem Compat.toHom_single (F : C.Compat M) (j : C.P) (y : V) :
    F.toHom hC (C.ofFun hC (Pi.single j y)) = F.ψ j y := by
  change F.toLin hC _ = _
  rw [Compat.toLin_apply, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; simp [Ne.symm hj']
  · simp

end BlockQuiver

end MonomialData

end BrickAccessibility
