module

public import BrickAccessibility.Quiver.Strings

/-!
# Transport of subspaces along letters and words

For a module `M` over an algebra with path data, the vertex space `M_v` is the
image of `e_v`. A direct letter `a` pulls a subspace `U` back to the vectors of
`M_{s a}` that `a` maps into `U`; an inverse letter `a⁻¹` pushes `U ∩ M_{s a}`
forward along `a`. Composing along a list `C` of letters gives `C^* U`: the
vectors with a chain along `C` ending in `U` (Ringel's linear relations).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable (D : MonomialData k B)
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- The action of `b` as a `k`-linear map. -/
def actL (b : B) : M →ₗ[k] M where
  toFun m := b • m
  map_add' := smul_add b
  map_smul' c m := by
    simp only [RingHom.id_apply]
    exact smul_algebra_smul_comm c b m

@[simp] theorem actL_apply (b : B) (m : M) : actL (k := k) (M := M) b m = b • m := rfl

variable (M) in
/-- The vertex space `M_v = e_v M`. -/
def vsp (v : D.Q.V) : Submodule k M := LinearMap.range (actL (M := M) (D.e v))

theorem mem_vsp {v : D.Q.V} {m : M} : m ∈ D.vsp M v ↔ D.e v • m = m := by
  constructor
  · rintro ⟨m', rfl⟩
    simp only [actL_apply, ← mul_smul, D.toPathData.e_idem]
  · intro h; exact ⟨m, h⟩

theorem α_smul_mem_vsp (a : D.Q.A) (m : M) : D.α a • m ∈ D.vsp M (D.Q.tgt a) := by
  rw [mem_vsp, ← mul_smul]
  have key : D.e (D.Q.tgt a) * D.α a = D.α a := D.toPathData.e_mul_α a
  rw [key]

theorem α_smul_of_mem_vsp {a : D.Q.A} {v : D.Q.V} (hv : v ≠ D.Q.src a) {m : M}
    (hm : m ∈ D.vsp M v) : D.α a • m = 0 := by
  rw [mem_vsp] at hm
  rw [← hm, ← mul_smul]
  have key : D.α a = D.α a * D.e (D.Q.src a) := (D.toPathData.α_mul_e a).symm
  rw [key, mul_assoc, D.toPathData.e_mul_e_of_ne (Ne.symm hv), mul_zero, zero_smul]

/-- Transport of a subspace back along one letter. -/
def tr : Letter D.Q → Submodule k M → Submodule k M
  | (a, true), U => D.vsp M (D.Q.src a) ⊓ U.comap (actL (D.α a))
  | (a, false), U => (D.vsp M (D.Q.src a) ⊓ U).map (actL (D.α a))

/-- Transport along a list of letters. -/
def trs : List (Letter D.Q) → Submodule k M → Submodule k M
  | [], U => U
  | l :: C, U => D.tr l (trs C U)

@[simp] theorem trs_nil (U : Submodule k M) : D.trs [] U = U := rfl

@[simp] theorem trs_cons (l : Letter D.Q) (C : List (Letter D.Q)) (U : Submodule k M) :
    D.trs (l :: C) U = D.tr l (D.trs C U) := rfl

theorem mem_tr_true {a : D.Q.A} {U : Submodule k M} {m : M} :
    m ∈ D.tr (a, true) U ↔ m ∈ D.vsp M (D.Q.src a) ∧ D.α a • m ∈ U := Iff.rfl

theorem mem_tr_false {a : D.Q.A} {U : Submodule k M} {m : M} :
    m ∈ D.tr (a, false) U ↔ ∃ m', m' ∈ D.vsp M (D.Q.src a) ∧ m' ∈ U ∧ D.α a • m' = m := by
  simp only [tr, Submodule.mem_map, Submodule.mem_inf, actL_apply, and_assoc]

theorem tr_mono (l : Letter D.Q) {U U' : Submodule k M} (h : U ≤ U') : D.tr l U ≤ D.tr l U' := by
  obtain ⟨a, d⟩ := l
  cases d
  · exact Submodule.map_mono (inf_le_inf_left _ h)
  · exact inf_le_inf_left _ (Submodule.comap_mono h)

theorem trs_mono (C : List (Letter D.Q)) {U U' : Submodule k M} (h : U ≤ U') :
    D.trs C U ≤ D.trs C U' := by
  induction C with
  | nil => exact h
  | cons l C ih => exact D.tr_mono l ih

theorem trs_append (C C' : List (Letter D.Q)) (U : Submodule k M) :
    D.trs (C ++ C') U = D.trs C (D.trs C' U) := by
  induction C with
  | nil => rfl
  | cons l C ih => simp [ih]

/-- The transport along a letter lies in the vertex space of its start. -/
theorem tr_le_vsp (l : Letter D.Q) (U : Submodule k M) : D.tr l U ≤ D.vsp M l.src := by
  obtain ⟨a, d⟩ := l
  cases d
  · rintro _ ⟨m, -, rfl⟩
    exact D.α_smul_mem_vsp a m
  · exact inf_le_left

theorem zero_mem_trs (C : List (Letter D.Q)) (U : Submodule k M) : (0 : M) ∈ D.trs C U :=
  Submodule.zero_mem _

/-! ### Naturality -/

variable {N : Type*} [AddCommGroup N] [Module B N] [Module k N] [IsScalarTower k B N]

theorem map_vsp_le (f : M →ₗ[B] N) (v : D.Q.V) :
    (D.vsp M v).map (f.restrictScalars k) ≤ D.vsp N v := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hn
  have hm' := (D.mem_vsp).mp hm
  refine (D.mem_vsp).mpr ?_
  simp only [LinearMap.coe_restrictScalars]
  rw [← f.map_smul, hm']

theorem map_tr_le (f : M →ₗ[B] N) (l : Letter D.Q) (U : Submodule k M) :
    (D.tr l U).map (f.restrictScalars k) ≤ D.tr l (U.map (f.restrictScalars k)) := by
  obtain ⟨a, d⟩ := l
  cases d
  · intro n hn
    obtain ⟨_, hm, rfl⟩ := Submodule.mem_map.mp hn
    obtain ⟨m, ⟨hv, hU⟩, rfl⟩ := Submodule.mem_map.mp hm
    refine Submodule.mem_map.mpr ⟨f m, ⟨D.map_vsp_le f _ ⟨m, hv, rfl⟩, ⟨m, hU, rfl⟩⟩, ?_⟩
    simp
  · intro n hn
    obtain ⟨m, ⟨hv, hU⟩, rfl⟩ := Submodule.mem_map.mp hn
    refine ⟨D.map_vsp_le f _ ⟨m, hv, rfl⟩, ?_⟩
    change D.α a • f m ∈ U.map (f.restrictScalars k)
    rw [← f.map_smul]; exact ⟨_, hU, rfl⟩

theorem map_trs_le (f : M →ₗ[B] N) (C : List (Letter D.Q)) (U : Submodule k M) :
    (D.trs C U).map (f.restrictScalars k) ≤ D.trs C (U.map (f.restrictScalars k)) := by
  induction C with
  | nil => exact le_rfl
  | cons l C ih => exact (D.map_tr_le f l _).trans (D.tr_mono l ih)

end MonomialData

end BrickAccessibility
