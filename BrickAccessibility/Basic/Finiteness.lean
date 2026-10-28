module

public import BrickAccessibility.Section2.CutDual
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import BrickAccessibility.Statement

/-!
# Finiteness conditions and the smaller-brick conclusion

Library versions, for left modules over `A`, of representation-finiteness and
brick-finiteness (`IsRepFinite`, `IsBrickFinite`), the conclusion of Theorem A
(`HasSmallerBrick`), and the consequence of Krull–Schmidt used in
Proposition 4.7: over a representation-finite algebra only finitely many
quotients by a simple submodule, and finitely many kernels of maps onto a
simple module, occur up to isomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable (A : Type u) [Ring A]

/-- Finitely many isomorphism classes of finitely generated modules satisfying `p`. -/
def FinitelyManyIso (p : ∀ (M : Type u) [AddCommGroup M] [Module A M], Prop) : Prop :=
  ∃ (n : ℕ) (B : Fin n → ModuleCat.{u} A),
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      p M → ∃ i, Nonempty (M ≃ₗ[A] B i)

/-- Representation-finiteness. -/
def IsRepFinite : Prop := FinitelyManyIso A (fun M _ _ ↦ Statement.IsIndecomposable A M)

/-- Brick-finiteness. -/
def IsBrickFinite : Prop := FinitelyManyIso A (fun M _ _ ↦ IsBrick A M)

variable {k : Type*} [Field k] [Algebra k A]

/-- The conclusion of Theorem A for one module. -/
def HasSmallerBrick (M : Type u) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] : Prop :=
  (∃ N : Submodule A M, IsBrick A N ∧ finrank k N + 1 = finrank k M) ∨
  (∃ L : Submodule A M, IsBrick A (M ⧸ L) ∧ finrank k (M ⧸ L) + 1 = finrank k M)

variable {A}

theorem IsBrick.of_linearEquiv {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (e : M ≃ₗ[A] N) (hM : IsBrick A M) : IsBrick A N := by
  have := hM.1
  refine ⟨e.symm.toEquiv.nontrivial, fun f hf ↦ ?_⟩
  have hf' : e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap ≠ 0 := by
    intro h; apply hf; ext n
    have := LinearMap.congr_fun h (e.symm n)
    simpa using congrArg e this
  obtain ⟨u, hu⟩ := hM.2 _ hf'
  have hbij : Function.Bijective (e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap) := by
    rw [← hu]; exact (Module.End.isUnit_iff _).mp u.isUnit
  rw [Module.End.isUnit_iff]
  have : (f : N → N) = e ∘ (e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap) ∘ e.symm := by
    funext n; simp
  rw [this]
  exact e.bijective.comp (hbij.comp e.symm.bijective)

/-- `HasSmallerBrick` is invariant under isomorphism. -/
theorem HasSmallerBrick.of_linearEquiv {M N : Type u} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    (e : M ≃ₗ[A] N) (h : HasSmallerBrick A M (k := k)) : HasSmallerBrick A N (k := k) := by
  have hdim : finrank k M = finrank k N := (e.restrictScalars k).finrank_eq
  rcases h with ⟨P, hP, hPd⟩ | ⟨L, hL, hLd⟩
  · left
    refine ⟨P.map e.toLinearMap, hP.of_linearEquiv (e.submoduleMap P), ?_⟩
    rw [← hdim, ← hPd, ((e.submoduleMap P).restrictScalars k).finrank_eq]
  · right
    refine ⟨L.map e.toLinearMap, hL.of_linearEquiv (Submodule.Quotient.equiv L _ e rfl), ?_⟩
    rw [← hdim, ← hLd, ((Submodule.Quotient.equiv L _ e rfl).restrictScalars k).finrank_eq]

section KrullSchmidt

variable [FiniteDimensional k A] {n0 : ℕ} (Bs : Fin n0 → ModuleCat.{u} A)

/-- A decomposition of `X` into a product of members of the list `Bs`. -/
structure Decomp (X : Type u) [AddCommGroup X] [Module A X] where
  /-- The index set of the summands. -/
  ι : Type
  [fin : Fintype ι]
  /-- The class of each summand. -/
  c : ι → Fin n0
  /-- The isomorphism with the product. -/
  e : X ≃ₗ[A] ((j : ι) → Bs (c j))

attribute [instance] Decomp.fin

variable {Bs}

/-- The multiplicity vector of a decomposition. -/
def Decomp.mult {X : Type u} [AddCommGroup X] [Module A X] (d : Decomp Bs X) (i : Fin n0) : ℕ :=
  Fintype.card {j : d.ι // d.c j = i}

/-- Decompositions with equal multiplicities have isomorphic modules. -/
theorem Decomp.nonempty_equiv {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (d : Decomp Bs X) (d' : Decomp Bs Y) (h : d.mult = d'.mult) :
    Nonempty (X ≃ₗ[A] Y) := by
  classical
  have hf : ∀ i, {j : d.ι // d.c j = i} ≃ {j : d'.ι // d'.c j = i} := fun i ↦
    Fintype.equivOfCardEq (congrFun h i)
  let σ : d.ι ≃ d'.ι := Equiv.ofFiberEquiv hf
  have hσ : ∀ j, d'.c (σ j) = d.c j := Equiv.ofFiberEquiv_map hf
  have cast : ∀ {i i' : Fin n0}, i = i' → (Bs i ≃ₗ[A] Bs i') := by
    intro i i' h; subst h; exact LinearEquiv.refl A _
  let e1 : ((j : d.ι) → Bs (d.c j)) ≃ₗ[A] ((j : d.ι) → Bs (d'.c (σ j))) :=
    LinearEquiv.piCongrRight fun j ↦ cast (hσ j).symm
  let e2 : ((j : d.ι) → Bs (d'.c (σ j))) ≃ₗ[A] ((j' : d'.ι) → Bs (d'.c j')) :=
    LinearEquiv.piCongrLeft A (fun j' ↦ Bs (d'.c j')) σ
  exact ⟨d.e.trans (e1.trans (e2.trans d'.e.symm))⟩

variable (Bs)

/-- Over a representation-finite algebra with representatives `Bs`, every
finite-dimensional module decomposes into at most `dim X` summands from `Bs`. -/
theorem exists_decomp
    (hB : ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      Statement.IsIndecomposable A M → ∃ i, Nonempty (M ≃ₗ[A] Bs i)) :
    ∀ (n : ℕ) (X : Type u) [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]
      [FiniteDimensional k X], finrank k X ≤ n →
        ∃ d : Decomp Bs X, Fintype.card d.ι ≤ finrank k X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ _ _ _ hX
    by_cases hnt : Nontrivial X
    · by_cases hind : Statement.IsIndecomposable A X
      · haveI : Module.Finite A X := Module.Finite.of_restrictScalars_finite k A X
        obtain ⟨i, ⟨e⟩⟩ := hB X hind
        refine ⟨⟨Unit, fun _ ↦ i, e.trans (LinearEquiv.funUnique Unit A (Bs i)).symm⟩, ?_⟩
        simp only [Fintype.card_unit]
        exact Module.finrank_pos
      · have : ∃ P R : Submodule A X, IsCompl P R ∧ P ≠ ⊥ ∧ R ≠ ⊥ := by
          by_contra hc
          push Not at hc
          exact hind ⟨hnt, fun P R hPR ↦ by
            by_cases hP : P = ⊥
            · exact Or.inl hP
            · exact Or.inr (hc P R hPR hP)⟩
        obtain ⟨P, R, hPR, hP, hR⟩ := this
        have hsum : finrank k P + finrank k R = finrank k X := by
          have := ((Submodule.prodEquivOfIsCompl P R hPR).restrictScalars k).finrank_eq
          rw [← this, Module.finrank_prod]
        have hPpos : 0 < finrank k P := by
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
          haveI : Nontrivial P := ⟨⟨⟨x, hx⟩, 0, fun h ↦ hx0 (congrArg Subtype.val h)⟩⟩
          exact Module.finrank_pos
        have hRpos : 0 < finrank k R := by
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
          haveI : Nontrivial R := ⟨⟨⟨x, hx⟩, 0, fun h ↦ hx0 (congrArg Subtype.val h)⟩⟩
          exact Module.finrank_pos
        obtain ⟨dP, hdP⟩ := ih (finrank k P) (by omega) P le_rfl
        obtain ⟨dR, hdR⟩ := ih (finrank k R) (by omega) R le_rfl
        let e : X ≃ₗ[A] ((j : dP.ι ⊕ dR.ι) → Bs (Sum.elim dP.c dR.c j)) :=
          (Submodule.prodEquivOfIsCompl P R hPR).symm.trans
            ((dP.e.prodCongr dR.e).trans
              (LinearEquiv.sumPiEquivProdPi A dP.ι dR.ι
                (fun j ↦ Bs (Sum.elim dP.c dR.c j))).symm)
        refine ⟨⟨dP.ι ⊕ dR.ι, Sum.elim dP.c dR.c, e⟩, ?_⟩
        simp only [Fintype.card_sum]
        omega
    · rw [not_nontrivial_iff_subsingleton] at hnt
      refine ⟨⟨Empty, Empty.elim, LinearEquiv.ofSubsingleton _ _⟩, by simp⟩

/-- Over a representation-finite algebra, the finite-dimensional modules of
dimension at most `n` fall into finitely many isomorphism classes, in the form
needed below: there is a finite map to multiplicity vectors that detects
isomorphism. -/
theorem exists_classifier (hA : IsRepFinite A) (n : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (cl : ∀ (X : Type u) [AddCommGroup X] [Module A X] [Module k X]
        [IsScalarTower k A X] [FiniteDimensional k X], finrank k X ≤ n → κ),
      ∀ (X Y : Type u) [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]
        [FiniteDimensional k X] [AddCommGroup Y] [Module A Y] [Module k Y]
        [IsScalarTower k A Y] [FiniteDimensional k Y] (hX : finrank k X ≤ n)
        (hY : finrank k Y ≤ n), cl X hX = cl Y hY → Nonempty (X ≃ₗ[A] Y) := by
  classical
  obtain ⟨n0, Bs, hB⟩ := hA
  have hdec := exists_decomp (k := k) Bs hB
  refine ⟨Fin n0 → Fin (n + 1), inferInstance, fun X _ _ _ _ _ hX i ↦
    ⟨(hdec n X hX).choose.mult i, ?_⟩, ?_⟩
  · have h1 := (hdec n X hX).choose_spec
    have h2 : (hdec n X hX).choose.mult i ≤ Fintype.card (hdec n X hX).choose.ι :=
      Fintype.card_subtype_le _
    omega
  · intro X Y _ _ _ _ _ _ _ _ _ _ hX hY h
    refine Decomp.nonempty_equiv (hdec n X hX).choose (hdec n Y hY).choose (funext fun i ↦ ?_)
    have := congrArg Fin.val (congrFun h i)
    exact this

end KrullSchmidt

/-- **Krull–Schmidt consequence.** Over a representation-finite finite-dimensional
algebra, only finitely many quotients `M / f(S)` occur up to isomorphism. -/
theorem finitelyManyQuotientsBy_of_isRepFinite [FiniteDimensional k A] (hA : IsRepFinite A)
    (M S : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] [AddCommGroup S] [Module A S] :
    FinitelyManyQuotientsBy A S M := by
  classical
  obtain ⟨κ, _, cl, hcl⟩ := exists_classifier (k := k) hA (finrank k M)
  have hle : ∀ f : S →ₗ[A] M, finrank k (M ⧸ LinearMap.range f) ≤ finrank k M := fun f ↦ by
    have := finrank_quotient_add_finrank' (k := k) (LinearMap.range f); omega
  let rep : κ → (S →ₗ[A] M) := fun c ↦
    if h : ∃ f : S →ₗ[A] M, f ≠ 0 ∧ cl (M ⧸ LinearMap.range f) (hle f) = c then h.choose else 0
  refine ⟨Finset.univ.image rep, fun f hf ↦ ?_⟩
  set c := cl (M ⧸ LinearMap.range f) (hle f)
  have hex : ∃ f : S →ₗ[A] M, f ≠ 0 ∧ cl (M ⧸ LinearMap.range f) (hle f) = c := ⟨f, hf, rfl⟩
  refine ⟨rep c, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hrep : rep c = hex.choose := dif_pos hex
  have hspec := hex.choose_spec
  rw [hrep]
  exact hcl _ _ (hle f) (hle hex.choose) hspec.2.symm

/-- **Krull–Schmidt consequence, dual form.** -/
theorem finitelyManyKernelsBy_of_isRepFinite [FiniteDimensional k A] (hA : IsRepFinite A)
    (M S : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] [AddCommGroup S] [Module A S] :
    FinitelyManyKernelsBy A M S := by
  classical
  obtain ⟨κ, _, cl, hcl⟩ := exists_classifier (k := k) hA (finrank k M)
  have hle : ∀ g : M →ₗ[A] S, finrank k (LinearMap.ker g) ≤ finrank k M := fun g ↦
    Submodule.finrank_le ((LinearMap.ker g).restrictScalars k)
  let rep : κ → (M →ₗ[A] S) := fun c ↦
    if h : ∃ g : M →ₗ[A] S, g ≠ 0 ∧ cl (LinearMap.ker g) (hle g) = c then h.choose else 0
  refine ⟨Finset.univ.image rep, fun g hg ↦ ?_⟩
  set c := cl (LinearMap.ker g) (hle g)
  have hex : ∃ g : M →ₗ[A] S, g ≠ 0 ∧ cl (LinearMap.ker g) (hle g) = c := ⟨g, hg, rfl⟩
  refine ⟨rep c, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hrep : rep c = hex.choose := dif_pos hex
  have hspec := hex.choose_spec
  rw [hrep]
  exact hcl _ _ (hle g) (hle hex.choose) hspec.2.symm

end BrickAccessibility
