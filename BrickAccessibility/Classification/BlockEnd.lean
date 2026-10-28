module

public import BrickAccessibility.Classification.BandIndec

/-!
# Maps between block modules with the same positions

`C.withG V' g'` is the block quiver with the positions and moves of `C` and blocks
`V'` with isomorphisms `g'`. A linear map `e : V → V'` intertwining `g` and `g'`
gives a module map `withG_hom` acting blockwise; an intertwining equivalence gives an
isomorphism (`withG_equiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData.BlockQuiver

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]

/-- The block quiver with the same positions and moves and new blocks. -/
abbrev withG (C : D.BlockQuiver V) (V' : Type u) [AddCommGroup V'] [Module k V']
    (g' : D.Q.A → C.P → V' ≃ₗ[k] V') : D.BlockQuiver V' where
  P := C.P
  vtx := C.vtx
  next := C.next
  g := g'
  next_src := C.next_src
  next_tgt := C.next_tgt
  inj := C.inj

variable (C : D.BlockQuiver V) (hC : C.KillsZeroPaths)

theorem α_smul_single_none {a : D.Q.A} {i : C.P} (h : C.next a i = none) (y : V) :
    D.α a • C.ofFun hC (Pi.single i y) = 0 := by
  classical
  refine C.ext_val hC fun j ↦ ?_
  rw [α_smul_val, Finset.sum_eq_single i]
  · simp [h]
  · intro i' _ hi'; simp [hi']
  · simp

/-- Module maps out of a block module are determined by the block vectors. -/
theorem hom_ext {N : Type*} [AddCommGroup N] [Module B N] {f f' : C.Mod hC →ₗ[B] N}
    (h : ∀ j y, f (C.ofFun hC (Pi.single j y)) = f' (C.ofFun hC (Pi.single j y))) : f = f' := by
  classical
  ext x
  have hx := C.mem_blk_iff_sum hC (J := fun _ ↦ True) x (fun j hj ↦ absurd trivial hj)
  rw [hx, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ h j _

variable {V' : Type u} [AddCommGroup V'] [Module k V'] (g' : D.Q.A → C.P → V' ≃ₗ[k] V')
  (hC' : (C.withG V' g').KillsZeroPaths)

/-- The compatible family of a blockwise map. -/
def withGCompat (e : V →ₗ[k] V') (he : ∀ a i y, e (C.g a i y) = g' a i (e y)) :
    C.Compat ((C.withG V' g').Mod hC') where
  ψ j := ((C.withG V' g').ofFunL hC').comp ((LinearMap.single k (fun _ : C.P ↦ V') j).comp e)
  mem_vsp j y := (C.withG V' g').single_mem_vsp hC' (j : C.P) (e y)
  move a i j y h := by
    show D.α a • (C.withG V' g').ofFun hC' (Pi.single i (e y)) =
      (C.withG V' g').ofFun hC' (Pi.single j (e (C.g a i y)))
    rw [α_smul_single (C.withG V' g') hC' (i := i) (j := j) h, he]
  kill a i y h := α_smul_single_none (C.withG V' g') hC' (i := i) h (e y)

/-- **The blockwise map** of an intertwining linear map. -/
def withGHom (e : V →ₗ[k] V') (he : ∀ a i y, e (C.g a i y) = g' a i (e y)) :
    C.Mod hC →ₗ[B] (C.withG V' g').Mod hC' :=
  (C.withGCompat g' hC' e he).toHom hC

theorem withGHom_single (e : V →ₗ[k] V') (he : ∀ a i y, e (C.g a i y) = g' a i (e y))
    (j : C.P) (y : V) :
    C.withGHom hC g' hC' e he (C.ofFun hC (Pi.single j y)) =
      (C.withG V' g').ofFun hC' (Pi.single j (e y)) :=
  (C.withGCompat g' hC' e he).toHom_single hC j y

/-- **The blockwise isomorphism** of an intertwining equivalence. -/
def withGEquiv (e : V ≃ₗ[k] V') (he : ∀ a i y, e (C.g a i y) = g' a i (e y)) :
    C.Mod hC ≃ₗ[B] (C.withG V' g').Mod hC' := by
  have he' : ∀ a i y, e.symm (g' a i y) = C.g a i (e.symm y) := fun a i y ↦ by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine LinearEquiv.ofLinear (C.withGHom hC g' hC' e.toLinearMap he)
    ((C.withG V' g').withGHom hC' C.g hC e.symm.toLinearMap he') ?_ ?_
  · refine (C.withG V' g').hom_ext hC' fun j y ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
    have h1 : (C.withG V' g').withGHom hC' C.g hC e.symm.toLinearMap he'
        ((C.withG V' g').ofFun hC' (Pi.single j y)) = C.ofFun hC (Pi.single j (e.symm y)) :=
      (C.withG V' g').withGHom_single hC' C.g hC _ he' j y
    rw [h1, C.withGHom_single hC g' hC' _ he j]
    simp
  · refine C.hom_ext hC fun j y ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
    rw [C.withGHom_single hC g' hC' _ he j y]
    have h1 : (C.withG V' g').withGHom hC' C.g hC e.symm.toLinearMap he'
        ((C.withG V' g').ofFun hC' (Pi.single j ((e : V →ₗ[k] V') y))) =
          C.ofFun hC (Pi.single j (e.symm (e y))) :=
      (C.withG V' g').withGHom_single hC' C.g hC _ he' j (e y)
    rw [h1]
    simp

end MonomialData.BlockQuiver

/-- Representations with equal path data are isomorphic. -/
theorem MonomialData.Rep.equiv_of_eq {D : MonomialData k B} {V : Type*} [AddCommGroup V]
    [Module k V] {R₁ R₂ : D.Rep V} (h : R₁.toPathData = R₂.toPathData) :
    Nonempty (R₁.Carrier ≃ₗ[B] R₂.Carrier) := by
  obtain ⟨P₁, z₁⟩ := R₁
  obtain ⟨P₂, z₂⟩ := R₂
  simp only at h
  subst h
  exact ⟨LinearEquiv.refl B _⟩

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

/-- The string module is the string block module with blocks `k`. -/
theorem stringModule_equiv (hs : w.IsString D) :
    Nonempty (w.stringModule D hs ≃ₗ[B] (w.blockQuiver k hs.1).Mod (w.blockQuiver_kills k hs)) := by
  refine MonomialData.Rep.equiv_of_eq ?_
  show (w.coeffQuiver D).toPathData = (w.blockQuiver k hs.1).toPathData
  have he : ∀ v, (w.coeffQuiver D).eMap v = (w.blockQuiver k hs.1).eMap v := fun v ↦
    LinearMap.ext fun f ↦ funext fun j ↦ rfl
  have hα : ∀ a, (w.coeffQuiver D).αMap a = (w.blockQuiver k hs.1).αMap a := fun a ↦ by
    refine LinearMap.ext fun f ↦ funext fun j ↦ ?_
    simp only [MonomialData.CoeffQuiver.αMap, MonomialData.BlockQuiver.αMap, LinearMap.coe_mk,
      AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with h1 h2 h2
    · show (1 : k) * f i = f i
      rw [one_mul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  unfold MonomialData.CoeffQuiver.toPathData MonomialData.BlockQuiver.toPathData
  congr 1
  exact funext hα

variable {V V' : Type u} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- String block modules with isomorphic blocks are isomorphic. -/
def blockEquiv (hs : w.IsString D) (e : V ≃ₗ[k] V') :
    (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs) ≃ₗ[B]
      (w.blockQuiver V' hs.1).Mod (w.blockQuiver_kills V' hs) :=
  (w.blockQuiver V hs.1).withGEquiv (w.blockQuiver_kills V hs) (fun _ _ ↦ LinearEquiv.refl k V')
    (w.blockQuiver_kills V' hs) e (fun _ _ _ ↦ rfl)

end Word

namespace MonomialData.BlockQuiver

end MonomialData.BlockQuiver

end BrickAccessibility
