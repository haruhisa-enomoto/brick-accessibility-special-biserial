module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Statements of the brick-accessibility theorems

This file uses only Mathlib. It fixes the vocabulary of the frozen manuscript
*Brick accessibility for brick-finite special biserial algebras* and states its
three principal results:

* `TheoremA` (Theorem 5.4): over a basic finite-dimensional brick-finite
  special biserial algebra over an algebraically closed field, every nonsimple
  brick has a brick submodule or a brick quotient of dimension one less;
* `CorollaryB` (Corollary 5.5): every brick is brick accessible, and the brick
  dimensions of a nonzero such algebra form an interval `{1, …, N}`;
* `CorollaryBiserial` (Corollary 5.6): both conclusions for
  representation-finite biserial algebras.

Conventions follow the manuscript. Modules are right modules, that is, modules
over `Λᵐᵒᵖ`. Paths are multiplied in traversal order: for arrows `a : x → y`
and `b : y → z` the path `ab` goes from `x` to `z`, and the arrow `a` maps
`M e_x` to `M e_y` on a right module `M`. All modules in the statements are
finite-dimensional.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility.Statement

universe u

/-! ### Quivers and path algebras -/

/-- A finite quiver: finite sets of vertices and arrows with source and target
maps. -/
structure FinQuiver where
  /-- Vertices. -/
  V : Type
  /-- Arrows. -/
  A : Type
  [finV : Fintype V]
  [decV : DecidableEq V]
  [finA : Fintype A]
  [decA : DecidableEq A]
  /-- The source of an arrow. -/
  src : A → V
  /-- The target of an arrow. -/
  tgt : A → V

attribute [instance] FinQuiver.finV FinQuiver.decV FinQuiver.finA FinQuiver.decA

namespace FinQuiver

variable (k : Type u) [Field k] (Q : FinQuiver)

/-- Generators of the path algebra: one per vertex and one per arrow. -/
abbrev Gen := Q.V ⊕ Q.A

/-- The defining relations of the path algebra: the vertex idempotents are
orthogonal and sum to one, and each arrow is fixed by the idempotents of its
source (on the left) and target (on the right). -/
inductive PathRel : FreeAlgebra k Q.Gen → FreeAlgebra k Q.Gen → Prop
  | idem (v w : Q.V) :
      PathRel (FreeAlgebra.ι k (Sum.inl v) * FreeAlgebra.ι k (Sum.inl w))
        (if v = w then FreeAlgebra.ι k (Sum.inl v) else 0)
  | one : PathRel (∑ v, FreeAlgebra.ι k (Sum.inl v)) 1
  | src (a : Q.A) :
      PathRel (FreeAlgebra.ι k (Sum.inl (Q.src a)) * FreeAlgebra.ι k (Sum.inr a))
        (FreeAlgebra.ι k (Sum.inr a))
  | tgt (a : Q.A) :
      PathRel (FreeAlgebra.ι k (Sum.inr a) * FreeAlgebra.ι k (Sum.inl (Q.tgt a)))
        (FreeAlgebra.ι k (Sum.inr a))

/-- The path algebra `kQ`, presented by its vertex idempotents and arrows.
Its paths (stationary paths and composable words of arrows, multiplied in
traversal order) form a `k`-basis. -/
abbrev PathAlgebra := RingQuot (PathRel k Q)

/-- The vertex idempotent `e_v` in `kQ`. -/
def vertex (v : Q.V) : PathAlgebra k Q :=
  RingQuot.mkAlgHom k (PathRel k Q) (FreeAlgebra.ι k (Sum.inl v))

/-- The arrow `a` in `kQ`. -/
def arrow (a : Q.A) : PathAlgebra k Q :=
  RingQuot.mkAlgHom k (PathRel k Q) (FreeAlgebra.ι k (Sum.inr a))

/-- The product of a word of arrows in traversal order. A word that is not
composable gives zero. -/
def word (l : List Q.A) : PathAlgebra k Q :=
  (l.map (arrow k Q)).prod

end FinQuiver

/-! ### Bound quiver presentations -/

section Presentations

variable (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ]

/-- An admissible bound quiver presentation `Λ ≅ kQ/I`: a surjective algebra
homomorphism `π : kQ → Λ` whose kernel `I` is admissible, that is,
`R^m ⊆ I ⊆ R²` for some `m ≥ 2`, where `R` is the arrow ideal. Here `R^m`
is spanned by words of `m` arrows and `R²` is the span of the words of at
least two arrows. -/
structure AdmissiblePresentation where
  /-- The quiver. -/
  Q : FinQuiver
  /-- The quotient map `kQ → Λ`. -/
  π : Q.PathAlgebra k →ₐ[k] Λ
  surjective : Function.Surjective π
  /-- Some power of the arrow ideal lies in `I`. -/
  nilpotent : ∃ m : ℕ, 2 ≤ m ∧ ∀ l : List Q.A, l.length = m → π (Q.word k l) = 0
  /-- `I` lies in the square of the arrow ideal. -/
  ker_le_sq : ∀ z : Q.PathAlgebra k, π z = 0 →
    z ∈ Submodule.span k {y | ∃ l : List Q.A, 2 ≤ l.length ∧ y = Q.word k l}

namespace AdmissiblePresentation

variable {k Λ} (P : AdmissiblePresentation k Λ)

/-- The image of an arrow in `Λ`. -/
def arr (a : P.Q.A) : Λ := P.π (P.Q.arrow k a)

/-- The special biserial conditions on a presentation (Definition 3.2): at most
two arrows start and at most two arrows end at each vertex, and for every arrow
`a` there is at most one arrow `b` with `ab ∉ I` and at most one arrow `c`
with `ca ∉ I`. -/
def IsSpecialBiserial : Prop :=
  (∀ x : P.Q.V, Nat.card {a : P.Q.A // P.Q.src a = x} ≤ 2) ∧
  (∀ y : P.Q.V, Nat.card {a : P.Q.A // P.Q.tgt a = y} ≤ 2) ∧
  (∀ a : P.Q.A, Nat.card {b : P.Q.A // P.Q.src b = P.Q.tgt a ∧ P.arr a * P.arr b ≠ 0} ≤ 1) ∧
  (∀ a : P.Q.A, Nat.card {c : P.Q.A // P.Q.tgt c = P.Q.src a ∧ P.arr c * P.arr a ≠ 0} ≤ 1)

end AdmissiblePresentation

/-- Definition 3.2: `Λ` is special biserial if it has an admissible bound quiver
presentation satisfying the special biserial conditions. -/
def IsSpecialBiserial : Prop :=
  ∃ P : AdmissiblePresentation k Λ, P.IsSpecialBiserial

end Presentations

/-! ### Modules -/

section Modules

variable (R : Type u) [Ring R]

/-- A module is indecomposable if it is nonzero and has no nontrivial direct
sum decomposition. -/
def IsIndecomposable (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ A B : Submodule R M, IsCompl A B → A = ⊥ ∨ B = ⊥

/-- A brick: a nonzero module whose endomorphism ring is a division ring, that
is, every nonzero endomorphism is invertible. -/
def IsBrick (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ f : M →ₗ[R] M, f ≠ 0 → IsUnit f

/-- The radical of a module: the intersection of its maximal submodules. -/
def radical (M : Type u) [AddCommGroup M] [Module R M] : Submodule R M :=
  sInf {N : Submodule R M | IsCoatom N}

/-- A submodule is uniserial if its submodules form a chain. The zero
submodule is uniserial. -/
def IsUniserialSubmodule {M : Type u} [AddCommGroup M] [Module R M]
    (U : Submodule R M) : Prop :=
  ∀ A B : Submodule R M, A ≤ U → B ≤ U → A ≤ B ∨ B ≤ A

/-- The biserial condition for one indecomposable projective module (Definition
3.1): its radical is the sum of at most two uniserial submodules whose
intersection is zero or simple. Allowing a zero summand covers "at most two". -/
def HasBiserialRadical (P : Type u) [AddCommGroup P] [Module R P] : Prop :=
  ∃ U₁ U₂ : Submodule R P, U₁ ⊔ U₂ = radical R P ∧
    IsUniserialSubmodule R U₁ ∧ IsUniserialSubmodule R U₂ ∧
    (U₁ ⊓ U₂ = ⊥ ∨ IsSimpleModule R (U₁ ⊓ U₂ : Submodule R P))

/-- All finitely generated indecomposable projective modules over `R` have a
biserial radical. -/
def ProjectivesHaveBiserialRadical : Prop :=
  ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P],
    IsIndecomposable R P → HasBiserialRadical R P

end Modules

section Algebras

variable (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ]

/-- Definition 3.1: `Λ` is biserial if the radical of each indecomposable
projective module, on either side, is the sum of at most two uniserial
submodules whose intersection is zero or simple. -/
def IsBiserial : Prop :=
  ProjectivesHaveBiserialRadical Λᵐᵒᵖ ∧ ProjectivesHaveBiserialRadical Λ

/-- Finitely many isomorphism classes of finitely generated right modules
satisfying `p`. -/
def FinitelyManyClasses
    (p : ∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M], Prop) : Prop :=
  ∃ (n : ℕ) (B : Fin n → ModuleCat.{u} Λᵐᵒᵖ),
    ∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module.Finite Λᵐᵒᵖ M],
      p M → ∃ i, Nonempty (M ≃ₗ[Λᵐᵒᵖ] B i)

/-- `Λ` is representation-finite: finitely many isomorphism classes of
finite-dimensional indecomposable right modules. -/
def IsRepresentationFinite : Prop :=
  FinitelyManyClasses Λ (fun M _ _ ↦ IsIndecomposable Λᵐᵒᵖ M)

/-- `Λ` is brick-finite: finitely many isomorphism classes of bricks. -/
def IsBrickFinite : Prop :=
  FinitelyManyClasses Λ (fun M _ _ ↦ IsBrick Λᵐᵒᵖ M)

/-- `Λ` is basic: every simple right module `S` occurs exactly once in the top
of `Λ`, equivalently `dim_k S = dim_k End(S)`. -/
def IsBasic : Prop :=
  ∀ (S : Type u) [AddCommGroup S] [Module Λᵐᵒᵖ S] [Module k S] [IsScalarTower k Λᵐᵒᵖ S],
    IsSimpleModule Λᵐᵒᵖ S →
      Module.finrank k S = Module.finrank k (S →ₗ[Λᵐᵒᵖ] S)

/-- A brick of dimension `n` is brick accessible if it is simple, or it has a
brick accessible brick submodule or brick quotient of dimension `n - 1`. -/
def BrickAccessibleOfDim :
    ℕ → ∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M]
      [IsScalarTower k Λᵐᵒᵖ M], Prop
  | 0, _, _, _, _, _ => False
  | n + 1, M, _, _, _, _ =>
      IsBrick Λᵐᵒᵖ M ∧ Module.finrank k M = n + 1 ∧
        (IsSimpleModule Λᵐᵒᵖ M ∨
          (∃ N : Submodule Λᵐᵒᵖ M, BrickAccessibleOfDim n N) ∨
          (∃ L : Submodule Λᵐᵒᵖ M, BrickAccessibleOfDim n (M ⧸ L)))

/-- A brick is brick accessible if it can be reduced to a simple module by
successively passing to a brick submodule or a brick quotient of dimension one
less. -/
def IsBrickAccessible (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M]
    [IsScalarTower k Λᵐᵒᵖ M] : Prop :=
  BrickAccessibleOfDim k Λ (Module.finrank k M) M

/-- The dimensions of the bricks of `Λ`. -/
def brickDimensions : Set ℕ :=
  {d | ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module Λᵐᵒᵖ M) (_ : Module k M)
      (_ : IsScalarTower k Λᵐᵒᵖ M), FiniteDimensional k M ∧ IsBrick Λᵐᵒᵖ M ∧
        Module.finrank k M = d}

/-- The conclusion of Theorem A for one module: a nonsimple brick has a brick
submodule or a brick quotient of dimension one less. -/
def HasSmallerBrick (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M]
    [IsScalarTower k Λᵐᵒᵖ M] : Prop :=
  (∃ N : Submodule Λᵐᵒᵖ M, IsBrick Λᵐᵒᵖ N ∧ Module.finrank k N + 1 = Module.finrank k M) ∨
  (∃ L : Submodule Λᵐᵒᵖ M,
    IsBrick Λᵐᵒᵖ (M ⧸ L) ∧ Module.finrank k (M ⧸ L) + 1 = Module.finrank k M)

/-- The two conclusions shared by Theorem A, Corollary B and Corollary 5.6. -/
def AccessibilityConclusions : Prop :=
  (∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
      [FiniteDimensional k M], IsBrick Λᵐᵒᵖ M → ¬ IsSimpleModule Λᵐᵒᵖ M →
        HasSmallerBrick k Λ M) ∧
  (∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
      [FiniteDimensional k M], IsBrick Λᵐᵒᵖ M → IsBrickAccessible k Λ M) ∧
  (Nontrivial Λ → ∃ N : ℕ, 1 ≤ N ∧ brickDimensions k Λ = Set.Icc 1 N)

end Algebras

/-! ### The principal statements -/

/-- Theorem 5.4 (Theorem A). -/
def TheoremA : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ], IsBasic k Λ → IsBrickFinite Λ → IsSpecialBiserial k Λ →
    ∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
      [FiniteDimensional k M], IsBrick Λᵐᵒᵖ M → ¬ IsSimpleModule Λᵐᵒᵖ M →
        HasSmallerBrick k Λ M

/-- Corollary 5.5 (Corollary B). -/
def CorollaryB : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ], IsBasic k Λ → IsBrickFinite Λ → IsSpecialBiserial k Λ →
    (∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
      [FiniteDimensional k M], IsBrick Λᵐᵒᵖ M → IsBrickAccessible k Λ M) ∧
    (Nontrivial Λ → ∃ N : ℕ, 1 ≤ N ∧ brickDimensions k Λ = Set.Icc 1 N)

/-- Corollary 5.6: the conclusions of Theorem A and Corollary B for basic
representation-finite biserial algebras. -/
def CorollaryBiserial : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ], IsBasic k Λ → IsRepresentationFinite Λ → IsBiserial Λ →
    AccessibilityConclusions k Λ

end BrickAccessibility.Statement
