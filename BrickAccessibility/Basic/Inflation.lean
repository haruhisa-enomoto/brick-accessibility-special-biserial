module

public import BrickAccessibility.Basic.Finiteness
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lemma 2.4: modules over a quotient algebra

Let `I` be a two-sided ideal of `A` and `B = A ⧸ I`. For modules on which `A`
acts through `B` (`IsScalarTower A B M`), `A`-linear and `B`-linear maps
coincide, so bricks, submodules and the smaller-brick conclusion agree over `A`
and `B` (`isBrick_quot_iff`, `HasSmallerBrick.of_quot`). Brick-finiteness and
representation-finiteness pass from `A` to `B` (`IsBrickFinite.quot`,
`IsRepFinite.quot`).

An `A`-module killed by `I` becomes a `B`-module through
`Module.IsTorsionBySet.module`, with the required scalar tower.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable {A : Type u} [Ring A] {I : Ideal A} [I.IsTwoSided]

section Linear

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module (A ⧸ I) M] [IsScalarTower A (A ⧸ I) M]
  [AddCommGroup N] [Module A N] [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N]

omit [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] in
theorem mk_smul_eq (a : A) (m : M) : (Ideal.Quotient.mk I a : A ⧸ I) • m = a • m := by
  rw [← smul_one_smul (A ⧸ I) a m]
  congr 1
  rw [← map_one (Ideal.Quotient.mk I)]
  show Submodule.Quotient.mk a = a • Submodule.Quotient.mk (1 : A)
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

/-- An `A`-linear map between modules on which `A` acts through `A ⧸ I` is
`A ⧸ I`-linear. -/
def toQuotLinear (f : M →ₗ[A] N) : M →ₗ[A ⧸ I] N where
  toFun := f
  map_add' := f.map_add
  map_smul' b m := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [mk_smul_eq, map_smul, RingHom.id_apply, mk_smul_eq]

@[simp] theorem toQuotLinear_apply (f : M →ₗ[A] N) (m : M) :
    toQuotLinear (I := I) f m = f m := rfl

/-- **Lemma 2.4, Hom spaces**: `Hom_{A/I}(M, N) = Hom_A(M, N)`. -/
def homQuotEquiv : (M →ₗ[A ⧸ I] N) ≃+ (M →ₗ[A] N) where
  toFun f := f.restrictScalars A
  invFun f := toQuotLinear (I := I) f
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' _ _ := rfl

omit [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] in
/-- **Lemma 2.4, endomorphism rings** agree over `A ⧸ I` and `A`. -/
def endQuotEquiv : Module.End (A ⧸ I) M ≃+* Module.End A M where
  toFun f := f.restrictScalars A
  invFun f := toQuotLinear (I := I) f
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] in
/-- **Lemma 2.4, submodules** agree over `A ⧸ I` and `A`. -/
def submoduleQuotOrderIso : Submodule (A ⧸ I) M ≃o Submodule A M where
  toFun P := P.restrictScalars A
  invFun P :=
    { carrier := P, add_mem' := P.add_mem, zero_mem' := P.zero_mem
      smul_mem' := fun b m hm ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [mk_smul_eq]; exact P.smul_mem a hm }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

omit [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] in
/-- **Lemma 2.4, quotients**: the quotient by a submodule is the same over `A ⧸ I` and `A`. -/
def quotQuotEquiv (P : Submodule (A ⧸ I) M) :
    (M ⧸ P) ≃ₗ[A] (M ⧸ P.restrictScalars A) :=
  (Submodule.Quotient.restrictScalarsEquiv A P).symm

theorem isBrick_quot_iff : IsBrick (A ⧸ I) M ↔ IsBrick A M := by
  constructor
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun f hf ↦ ?_⟩
    have hf' : toQuotLinear (I := I) f ≠ 0 := fun h0 ↦ hf (by ext m; exact LinearMap.congr_fun h0 m)
    rw [Module.End.isUnit_iff]
    have := (Module.End.isUnit_iff _).mp (h _ hf')
    exact this
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun f hf ↦ ?_⟩
    have hf' : f.restrictScalars A ≠ 0 := fun h0 ↦ hf (by ext m; exact LinearMap.congr_fun h0 m)
    have := (Module.End.isUnit_iff (f.restrictScalars A)).mp (h _ hf')
    rw [Module.End.isUnit_iff]
    exact this

end Linear

section Smaller

variable {k : Type*} [Field k] [Algebra k A]
variable {M : Type u} [AddCommGroup M] [Module A M] [Module (A ⧸ I) M] [IsScalarTower A (A ⧸ I) M]
  [Module k M] [IsScalarTower k A M] [IsScalarTower k (A ⧸ I) M]

/-- A smaller brick over `A ⧸ I` is a smaller brick over `A`. -/
theorem HasSmallerBrick.of_quot (h : HasSmallerBrick (A ⧸ I) M (k := k)) :
    HasSmallerBrick A M (k := k) := by
  rcases h with ⟨P, hP, hPd⟩ | ⟨L, hL, hLd⟩
  · left
    refine ⟨P.restrictScalars A, ?_, hPd⟩
    exact (isBrick_quot_iff (I := I) (M := P)).mp hP
  · right
    refine ⟨L.restrictScalars A, ?_, ?_⟩
    · exact ((isBrick_quot_iff (I := I) (M := M ⧸ L)).mp hL).of_linearEquiv
        (Submodule.Quotient.restrictScalarsEquiv A L).symm
    · rw [← hLd, ((Submodule.Quotient.restrictScalarsEquiv A L).restrictScalars k).finrank_eq]

end Smaller

section Finite

variable {A' : Type u} [Ring A']

/-- Modules over `A ⧸ I` regarded as `A`-modules. -/
@[reducible] def inflateModule (M : Type*) [AddCommGroup M] [Module (A ⧸ I) M] : Module A M :=
  Module.compHom M (Ideal.Quotient.mk I)

theorem inflate_isScalarTower (M : Type*) [AddCommGroup M] [Module (A ⧸ I) M] :
    letI := inflateModule (I := I) M
    IsScalarTower A (A ⧸ I) M := by
  letI := inflateModule (I := I) M
  refine ⟨fun a b m ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  show (a • Ideal.Quotient.mk I b) • m = Ideal.Quotient.mk I a • Ideal.Quotient.mk I b • m
  rw [← mul_smul]
  congr 1

/-- Finiteness of isomorphism classes passes from `A` to `A ⧸ I` for any property
that inflation preserves. -/
theorem FinitelyManyIso.quot
    (p : ∀ (M : Type u) [AddCommGroup M] [Module (A ⧸ I) M], Prop)
    (q : ∀ (M : Type u) [AddCommGroup M] [Module A M], Prop)
    (hpq : ∀ (M : Type u) [AddCommGroup M] [Module (A ⧸ I) M], p M →
      @q M _ (inflateModule (I := I) M))
    (hA : FinitelyManyIso A q) : FinitelyManyIso (A ⧸ I) p := by
  classical
  obtain ⟨n, Bs, hB⟩ := hA
  -- for each class, choose a module over `A ⧸ I` in it, if there is one
  have hchoice : ∀ i : Fin n, ∃ N : ModuleCat.{u} (A ⧸ I),
      (∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (A ⧸ I) M), p M ∧
        Nonempty (@LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ M (Bs i) _ _
          (inflateModule (I := I) M) _)) →
      (p N ∧ Nonempty (@LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ N (Bs i) _ _
          (inflateModule (I := I) N) _)) := by
    intro i
    by_cases h : ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (A ⧸ I) M), p M ∧
        Nonempty (@LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ M (Bs i) _ _
          (inflateModule (I := I) M) _)
    · obtain ⟨M, _, _, hp, he⟩ := h
      exact ⟨ModuleCat.of (A ⧸ I) M, fun _ ↦ ⟨hp, he⟩⟩
    · exact ⟨ModuleCat.of (A ⧸ I) PUnit, fun h' ↦ absurd h' h⟩
  choose Ns hNs using hchoice
  refine ⟨n, Ns, fun M _ _ _ hp ↦ ?_⟩
  letI := inflateModule (I := I) M
  haveI := inflate_isScalarTower (I := I) M
  haveI : Module.Finite A M := by
    obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule (A ⧸ I) M).FG)
    refine ⟨⟨S, ?_⟩⟩
    let P : Submodule (A ⧸ I) M :=
      { carrier := Submodule.span A (S : Set M)
        add_mem' := (Submodule.span A (S : Set M)).add_mem
        zero_mem' := (Submodule.span A (S : Set M)).zero_mem
        smul_mem' := fun b m hm ↦ by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
          rw [mk_smul_eq]
          exact (Submodule.span A (S : Set M)).smul_mem a hm }
    have hle : Submodule.span (A ⧸ I) (S : Set M) ≤ P :=
      Submodule.span_le.mpr fun x hx ↦ Submodule.subset_span hx
    rw [hS] at hle
    rw [eq_top_iff]
    intro x _
    exact hle (Submodule.mem_top (x := x))
  obtain ⟨i, ⟨e⟩⟩ := hB M (hpq M hp)
  obtain ⟨_, ⟨e'⟩⟩ := hNs i ⟨M, _, _, hp, ⟨e⟩⟩
  refine ⟨i, ⟨?_⟩⟩
  letI := inflateModule (I := I) (Ns i)
  haveI := inflate_isScalarTower (I := I) (Ns i)
  let f : M ≃ₗ[A] Ns i := e.trans e'.symm
  exact
    { toFun := f
      invFun := f.symm
      left_inv := f.left_inv
      right_inv := f.right_inv
      map_add' := f.map_add
      map_smul' := fun b m ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [mk_smul_eq, f.map_smul, RingHom.id_apply, mk_smul_eq] }

/-- Brick-finiteness passes to quotient algebras. -/
theorem IsBrickFinite.quot (hA : IsBrickFinite A) : IsBrickFinite (A ⧸ I) := by
  refine FinitelyManyIso.quot (I := I) _ _ (fun M _ _ hM ↦ ?_) hA
  letI := inflateModule (I := I) M
  haveI := inflate_isScalarTower (I := I) M
  exact (isBrick_quot_iff (I := I)).mp hM

/-- Representation-finiteness passes to quotient algebras. -/
theorem IsRepFinite.quot (hA : IsRepFinite A) : IsRepFinite (A ⧸ I) := by
  refine FinitelyManyIso.quot (I := I) _ _ (fun M _ _ hM ↦ ?_) hA
  letI := inflateModule (I := I) M
  haveI := inflate_isScalarTower (I := I) M
  refine ⟨hM.1, fun P R hPR ↦ ?_⟩
  let P' : Submodule (A ⧸ I) M :=
    { carrier := P, add_mem' := P.add_mem, zero_mem' := P.zero_mem
      smul_mem' := fun b m hm ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [mk_smul_eq]; exact P.smul_mem a hm }
  let R' : Submodule (A ⧸ I) M :=
    { carrier := R, add_mem' := R.add_mem, zero_mem' := R.zero_mem
      smul_mem' := fun b m hm ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [mk_smul_eq]; exact R.smul_mem a hm }
  have hc : IsCompl P' R' := by
    constructor
    · rw [disjoint_iff_inf_le]
      intro x hx
      exact (Submodule.disjoint_def.mp hPR.disjoint) x hx.1 hx.2 ▸ Submodule.zero_mem _
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hx : x ∈ P ⊔ R := hPR.codisjoint.eq_top ▸ Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      exact Submodule.add_mem_sup hy hz
  rcases hM.2 P' R' hc with h | h
  · left; ext x; exact (SetLike.ext_iff.mp h x)
  · right; ext x; exact (SetLike.ext_iff.mp h x)

end Finite

end BrickAccessibility
