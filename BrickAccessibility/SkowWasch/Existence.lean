module

public import BrickAccessibility.SkowWasch.Basic
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Basic data of a basic algebra

Over an algebraically closed field, if every simple module has the dimension of its
endomorphism ring (the basic condition), then every simple module is one-dimensional,
`A / J` is commutative, the Wedderburn blocks are `1 × 1`, and lifting the block
idempotents gives `BasicData` with `R = J` (`exists_basicData`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

open Module

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Schur over an algebraically closed field. -/
theorem finrank_end_simple (S : Type*) [AddCommGroup S] [Module A S] [Module k S]
    [IsScalarTower k A S] [FiniteDimensional k S] [IsSimpleModule A S] :
    finrank k (S →ₗ[A] S) = 1 := by
  classical
  have : FiniteDimensional k (S →ₗ[A] S) := FiniteDimensional.of_injective
    (LinearMap.restrictScalarsₗ k A S S k) (LinearMap.restrictScalars_injective k)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Module.End A S)
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap k (Module.End A S)) hb).finrank_eq,
    finrank_self]

variable (hbasic : ∀ (S : Type u) [AddCommGroup S] [Module A S] [Module k S]
  [IsScalarTower k A S], IsSimpleModule A S → finrank k S = finrank k (S →ₗ[A] S))
include hbasic

/-- Commutators lie in the Jacobson radical of a basic algebra. -/
theorem comm_mem_jacobson (a b : A) : a * b - b * a ∈ Ring.jacobson A := by
  rw [Ring.jacobson, Module.jacobson, Submodule.mem_sInf]
  intro m hm
  have : IsSimpleModule A (A ⧸ m) := isSimpleModule_iff_isCoatom.mpr hm
  have hfd : FiniteDimensional k (A ⧸ m) :=
    Module.Finite.of_surjective (m.mkQ.restrictScalars k) (Submodule.mkQ_surjective _)
  have h1 : finrank k (A ⧸ m) = 1 := by
    rw [hbasic _ inferInstance, finrank_end_simple]
  set s0 : A ⧸ m := Submodule.Quotient.mk 1
  have hs0 : s0 ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact hm.1 (eq_top_iff.mpr fun x _ ↦ by simpa using m.smul_mem x h)
  have hsc : ∀ a : A, ∃ c : k, a • s0 = c • s0 := fun a ↦ by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s0 hs0).mp h1 (a • s0)
    exact ⟨c, hc.symm⟩
  obtain ⟨ca, ha⟩ := hsc a
  obtain ⟨cb, hb⟩ := hsc b
  have key : (a * b - b * a) • s0 = 0 := by
    rw [sub_smul, mul_smul, mul_smul, hb, ha, smul_comm a cb, ha, smul_comm b ca, hb,
      smul_smul, smul_smul, mul_comm, sub_self]
  have e1 : (a * b - b * a) • s0 = Submodule.Quotient.mk (a * b - b * a) := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  rw [e1] at key
  exact (Submodule.Quotient.mk_eq_zero _).mp key

/-- **Basic data exist** for a basic algebra over an algebraically closed field. -/
theorem exists_basicData : Nonempty (BasicData k A) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  set J := Ring.jacobson A
  obtain ⟨m, d, hd, ⟨φ⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ J)
  have hcomm : ∀ x y : A ⧸ J, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact comm_mem_jacobson hbasic a b
  have hd1 : ∀ i, d i = 1 := by
    intro i
    by_contra hne
    have hpos := (hd i).ne
    have h2 : 1 < d i := by omega
    let i0 : Fin (d i) := ⟨0, by omega⟩
    let i1 : Fin (d i) := ⟨1, h2⟩
    let X : (j : Fin m) → Matrix (Fin (d j)) (Fin (d j)) k := Pi.single i (Matrix.single i0 i1 1)
    let Y : (j : Fin m) → Matrix (Fin (d j)) (Fin (d j)) k := Pi.single i (Matrix.single i1 i0 1)
    have h := hcomm (φ.symm X) (φ.symm Y)
    rw [← map_mul, ← map_mul] at h
    have h' := congrFun (φ.symm.injective h) i
    simp only [X, Y, Pi.mul_apply, Pi.single_eq_same, Matrix.single_mul_single_same,
      mul_one] at h'
    have := congrFun (congrFun h' i0) i0
    simp [i0, i1, Matrix.single_apply] at this
  -- block idempotents and their lifts
  let E : Fin m → A ⧸ J := fun i ↦ φ.symm (Pi.single i 1)
  have hE : CompleteOrthogonalIdempotents E :=
    (CompleteOrthogonalIdempotents.single (fun j ↦ Matrix (Fin (d j)) (Fin (d j)) k)).map
      φ.symm.toRingHom
  have hnil : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk J), IsNilpotent x := by
    intro x hx
    rw [Ideal.mk_ker] at hx
    obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := A)
    exact ⟨N, by have := Ideal.pow_mem_pow hx N; rw [hN] at this; simpa using this⟩
  obtain ⟨e, he, hfe⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (Ideal.Quotient.mk J) hnil hE (fun i ↦ Ideal.Quotient.mk_surjective _)
  have hmk : ∀ i, Ideal.Quotient.mk J (e i) = E i := fun i ↦ congrFun hfe i
  -- the radical as a `k`-submodule
  let R : Submodule k A := J.restrictScalars k
  have hpow : ∀ n : ℕ, R ^ (n + 1) ≤ (J ^ (n + 1)).restrictScalars k := by
    intro n
    induction n with
    | zero => rw [pow_one, Submodule.pow_one]
    | succ n ih =>
        rw [pow_succ, Submodule.mul_le]
        intro x hx y hy
        show x * y ∈ J ^ (n + 1 + 1)
        rw [Submodule.pow_succ]
        exact Submodule.mul_mem_mul (ih hx) hy
  refine ⟨{
    n := m
    e := e
    e_mul_e := fun v w ↦ by
      split_ifs with h
      · subst h; exact he.idem v
      · exact he.ortho h
    sum_e := he.complete
    R := R
    mul_mem_left := fun a r hr ↦ J.mul_mem_left a hr
    mul_mem_right := fun r a hr ↦ J.mul_mem_right a hr
    pow_eq_bot := by
      obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := A)
      have hN' : J ^ (N + 1) = 0 := by rw [Submodule.pow_succ, hN, zero_mul]
      refine ⟨N + 1, eq_bot_iff.mpr ((hpow N).trans ?_)⟩
      intro x hx
      have : x ∈ J ^ (N + 1) := hx
      rw [hN'] at this
      exact (Submodule.mem_bot k).mpr ((Submodule.mem_bot A).mp this)
    decomp := fun a ↦ by
      let c : Fin m → k := fun i ↦ φ (Ideal.Quotient.mk J a) i ⟨0, by rw [hd1 i]; omega⟩
        ⟨0, by rw [hd1 i]; omega⟩
      refine ⟨c, ?_⟩
      show a - ∑ v, c v • e v ∈ J
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 : Ideal.Quotient.mk J (a - ∑ v, c v • e v) =
          Ideal.Quotient.mk J a - ∑ v, c v • E v := by
        rw [← Ideal.Quotient.mkₐ_eq_mk k, map_sub, map_sum]
        simp only [map_smul, Ideal.Quotient.mkₐ_eq_mk, hmk]
      rw [h1, sub_eq_zero]
      apply φ.injective
      rw [map_sum]
      funext j
      ext r s
      have hr : r = ⟨0, by rw [hd1 j]; omega⟩ :=
        Fin.ext (by have := r.isLt; have := hd1 j; simp only; omega)
      have hs : s = ⟨0, by rw [hd1 j]; omega⟩ :=
        Fin.ext (by have := s.isLt; have := hd1 j; simp only; omega)
      subst hr; subst hs
      simp only [map_smul, E, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply,
        Matrix.sum_apply, Matrix.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp [c]
      · intro b _ hb; simp [Pi.single_eq_of_ne' hb]
      · simp
    e_not_mem := fun v hv ↦ by
      have h1 : Ideal.Quotient.mk J (e v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hv
      rw [hmk] at h1
      have h2 := congrFun (φ.symm.injective (h1.trans (map_zero φ.symm).symm)) v
      simp only [Pi.single_eq_same, Pi.zero_apply] at h2
      have : NeZero (d v) := hd v
      exact one_ne_zero h2 }⟩

end SkowWasch

end BrickAccessibility
