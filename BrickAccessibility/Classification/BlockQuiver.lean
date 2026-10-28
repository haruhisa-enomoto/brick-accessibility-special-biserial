module

public import BrickAccessibility.Quiver.Monomial

/-!
# Block quivers

A block quiver over monomial data `D` with block space `V` is a finite set of
positions over vertices, partial injective arrow moves between positions, and a
linear isomorphism of `V` on each move. The arrow `a` sends the block `V` at
position `i` to the block at `next a i` through `g a i`. If no directed walk
spells a zero path, `P → V` is a representation (`toRep`). String modules
(`V = k`) and band modules (`V` with an automorphism on one move) are block
quivers.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

namespace MonomialData

variable (D : MonomialData k A) (V : Type u) [AddCommGroup V] [Module k V]

/-- A block quiver with block space `V`. -/
structure BlockQuiver where
  /-- Positions. -/
  P : Type
  [fin : Fintype P]
  [dec : DecidableEq P]
  /-- The vertex of a position. -/
  vtx : P → D.Q.V
  /-- Where an arrow sends a position, if anywhere. -/
  next : D.Q.A → P → Option P
  /-- The isomorphism on a move. -/
  g : D.Q.A → P → V ≃ₗ[k] V
  next_src : ∀ a i j, next a i = some j → vtx i = D.Q.src a
  next_tgt : ∀ a i j, next a i = some j → vtx j = D.Q.tgt a
  inj : ∀ a i i' j, next a i = some j → next a i' = some j → i = i'

attribute [instance] BlockQuiver.fin BlockQuiver.dec

namespace BlockQuiver

variable {D V} (C : D.BlockQuiver V)

/-- Following a list of arrows, with the composite of the isomorphisms. -/
def follow : C.P → List D.Q.A → Option (C.P × (V →ₗ[k] V))
  | i, [] => some (i, LinearMap.id)
  | i, a :: l =>
      match C.next a i with
      | none => none
      | some j => (follow j l).map fun q ↦ (q.1, q.2 ∘ₗ (C.g a i).toLinearMap)

/-- No directed walk spells a zero path. -/
def KillsZeroPaths : Prop :=
  ∀ x l, D.pval x l = 0 → ∀ i, C.vtx i = x → C.follow i l = none

/-- The vertex projection on `P → V`. -/
def eMap (v : D.Q.V) : Module.End k (C.P → V) where
  toFun f j := if C.vtx j = v then f j else 0
  map_add' f g := by funext j; by_cases h : C.vtx j = v <;> simp [h]
  map_smul' c f := by funext j; by_cases h : C.vtx j = v <;> simp [h]

/-- The arrow map on `P → V`. -/
def αMap (a : D.Q.A) : Module.End k (C.P → V) where
  toFun f j := ∑ i, if C.next a i = some j then C.g a i (f i) else 0
  map_add' f g := by
    ext j; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  map_smul' c f := by
    ext j; simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp

theorem eMap_single (v : D.Q.V) (i : C.P) (x : V) :
    C.eMap v (Pi.single i x) = if C.vtx i = v then Pi.single i x else 0 := by
  ext j
  simp only [eMap, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hij : j = i
  · subst hij; split_ifs <;> simp
  · split_ifs <;> simp [Pi.single_apply, hij]

theorem αMap_single (a : D.Q.A) (i : C.P) (x : V) :
    C.αMap a (Pi.single i x) =
      match C.next a i with
      | none => 0
      | some j => Pi.single j (C.g a i x) := by
  ext j
  simp only [αMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · cases h : C.next a i with
    | none => simp
    | some j' =>
        by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_apply, Ne.symm hj, hj]
  · intro i' _ hi'; simp [Pi.single_apply, hi']
  · simp

/-- The path data of the block quiver inside `End (P → V)`. -/
def toPathData : PathData D.Q (Module.End k (C.P → V)) where
  e := C.eMap
  α := C.αMap
  e_mul_e v w := by
    refine LinearMap.ext fun f ↦ funext fun j ↦ ?_
    simp only [eMap, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hv : v = w
    · subst hv; by_cases h : C.vtx j = v <;> simp [h]
    · by_cases h1 : C.vtx j = v <;> by_cases h2 : C.vtx j = w
      · exact absurd (h1.symm.trans h2) hv
      all_goals simp [h1, h2, hv, Ne.symm hv]
  sum_e := by
    refine LinearMap.ext fun f ↦ funext fun j ↦ ?_
    simp only [LinearMap.sum_apply, Finset.sum_apply, eMap, LinearMap.coe_mk, AddHom.coe_mk,
      Module.End.one_apply]
    rw [Finset.sum_eq_single (C.vtx j)]
    · simp
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  α_mul_e a := by
    refine LinearMap.ext fun f ↦ funext fun j ↦ ?_
    simp only [αMap, eMap, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h1 : C.next a i = some j
    · simp [h1, C.next_src a i j h1]
    · simp [h1]
  e_mul_α a := by
    refine LinearMap.ext fun f ↦ funext fun j ↦ ?_
    simp only [αMap, eMap, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases h : C.vtx j = D.Q.tgt a
    · simp [h]
    · simp only [h, if_false]
      symm
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      by_cases h1 : C.next a i = some j
      · exact absurd (C.next_tgt a i j h1) h
      · simp [h1]

/-- Path values of the block quiver on blocks. -/
theorem pval_single (x : D.Q.V) (l : List D.Q.A) (i : C.P) (y : V) :
    C.toPathData.pval x l (Pi.single i y) =
      if C.vtx i = x then
        (match C.follow i l with
          | none => 0
          | some q => Pi.single q.1 (q.2 y))
      else 0 := by
  induction l generalizing x i y with
  | nil =>
      simp only [PathData.pval, follow]
      exact C.eMap_single x i y
  | cons a l ih =>
      simp only [PathData.pval, Module.End.mul_apply]
      change C.toPathData.pval (D.Q.tgt a) l (C.αMap a (C.eMap x (Pi.single i y))) = _
      rw [C.eMap_single]
      by_cases hx : C.vtx i = x
      · simp only [hx, if_true, C.αMap_single]
        simp only [follow]
        cases h : C.next a i with
        | none => simp
        | some j =>
            simp only
            rw [ih]
            rw [if_pos (C.next_tgt a i j h)]
            cases C.follow j l with
            | none => simp
            | some q => simp
      · simp [hx]

/-- A block quiver killing zero paths gives a representation. -/
def toRep (hC : C.KillsZeroPaths) : D.Rep (C.P → V) where
  toPathData := C.toPathData
  zero x l hxl := by
    refine LinearMap.pi_ext fun i y ↦ ?_
    rw [C.pval_single]
    split_ifs with hx
    · rw [hC x l hxl i hx]; rfl
    · rfl

end BlockQuiver

end MonomialData

end BrickAccessibility
