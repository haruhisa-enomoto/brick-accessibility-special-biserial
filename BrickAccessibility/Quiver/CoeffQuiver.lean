module

public import BrickAccessibility.Quiver.Monomial

/-!
# Coefficient-quiver representations

A coefficient quiver over monomial data `D` is a finite set of positions, each
lying over a vertex, together with, for every arrow `a`, a partial map `next a`
on positions and nonzero coefficients: the arrow sends the basis vector of
position `i` to `coef a i` times the basis vector of `next a i`.

If no directed walk in the coefficient quiver spells a zero path
(`KillsZeroPaths`), the induced representation on `P → k` is a representation
of `D` (`toRep`), hence an `A`-module. String modules and the one-dimensional
band modules are of this form.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

namespace MonomialData

variable (D : MonomialData k A)

/-- A coefficient quiver: positions over vertices and arrow moves with scalars. -/
structure CoeffQuiver where
  /-- Positions. -/
  P : Type
  [fin : Fintype P]
  [dec : DecidableEq P]
  /-- The vertex of a position. -/
  vtx : P → D.Q.V
  /-- Where an arrow sends a position, if anywhere. -/
  next : D.Q.A → P → Option P
  /-- The coefficient of an arrow move. -/
  coef : D.Q.A → P → k
  next_src : ∀ a i j, next a i = some j → vtx i = D.Q.src a
  next_tgt : ∀ a i j, next a i = some j → vtx j = D.Q.tgt a

attribute [instance] CoeffQuiver.fin CoeffQuiver.dec

namespace CoeffQuiver

variable {D} (C : D.CoeffQuiver)

/-- Following a list of arrows from a position, with the product of
coefficients (in traversal order). -/
def follow : C.P → List D.Q.A → Option (C.P × k)
  | i, [] => some (i, 1)
  | i, a :: l =>
      match C.next a i with
      | none => none
      | some j => (follow j l).map fun q ↦ (q.1, C.coef a i * q.2)

/-- No directed walk spells a zero path. -/
def KillsZeroPaths : Prop :=
  ∀ x l, D.pval x l = 0 → ∀ i, C.vtx i = x → C.follow i l = none

/-- The vertex projection on `P → k`. -/
def eMap (v : D.Q.V) : Module.End k (C.P → k) where
  toFun f j := if C.vtx j = v then f j else 0
  map_add' f g := by funext j; by_cases h : C.vtx j = v <;> simp [h]
  map_smul' c f := by funext j; by_cases h : C.vtx j = v <;> simp [h]

/-- The arrow map on `P → k`. -/
def αMap (a : D.Q.A) : Module.End k (C.P → k) where
  toFun f j := ∑ i, if C.next a i = some j then C.coef a i * f i else 0
  map_add' f g := by
    ext j; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  map_smul' c f := by
    ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring

theorem eMap_single (v : D.Q.V) (i : C.P) (c : k) :
    C.eMap v (Pi.single i c) = if C.vtx i = v then Pi.single i c else 0 := by
  ext j
  simp only [eMap, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hij : j = i
  · subst hij; split_ifs <;> simp
  · split_ifs <;> simp [Pi.single_apply, hij]

theorem αMap_single (a : D.Q.A) (i : C.P) (c : k) :
    C.αMap a (Pi.single i c) =
      match C.next a i with
      | none => 0
      | some j => Pi.single j (C.coef a i * c) := by
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

/-- The path data of the coefficient quiver inside `End (P → k)`. -/
def toPathData : PathData D.Q (Module.End k (C.P → k)) where
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

/-- Path values of the coefficient quiver on basis vectors. -/
theorem pval_single (x : D.Q.V) (l : List D.Q.A) (i : C.P) (c : k) :
    C.toPathData.pval x l (Pi.single i c) =
      if C.vtx i = x then
        (match C.follow i l with
          | none => 0
          | some q => Pi.single q.1 (q.2 * c))
      else 0 := by
  induction l generalizing x i c with
  | nil =>
      simp only [PathData.pval, follow, one_mul]
      exact C.eMap_single x i c
  | cons a l ih =>
      simp only [PathData.pval, Module.End.mul_apply]
      change C.toPathData.pval (D.Q.tgt a) l (C.αMap a (C.eMap x (Pi.single i c))) = _
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
            | some q => simp [mul_assoc, mul_comm (C.coef a i)]
      · simp [hx]

/-- A coefficient quiver killing zero paths gives a representation. -/
def toRep (hC : C.KillsZeroPaths) : D.Rep (C.P → k) where
  toPathData := C.toPathData
  zero x l hxl := by
    refine LinearMap.pi_ext fun i c ↦ ?_
    rw [C.pval_single]
    split_ifs with hx
    · rw [hC x l hxl i hx]; rfl
    · rfl

end CoeffQuiver

end MonomialData

end BrickAccessibility
