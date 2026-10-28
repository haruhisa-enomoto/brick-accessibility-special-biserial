module

public import BrickAccessibility.MainTheorems

@[expose] public section

universe u

/-- **Theorem A** (Theorem 5.4). Over a basic finite-dimensional brick-finite special
biserial algebra over an algebraically closed field, every nonsimple brick has a brick
submodule or a brick quotient of dimension one less. -/
theorem BrickAccessibility.Challenge.theoremA : BrickAccessibility.Statement.TheoremA.{u} :=
  BrickAccessibility.theoremA

/-- **Corollary B** (Corollary 5.5). Every brick over such an algebra is brick accessible,
and the brick dimensions of a nonzero such algebra form an interval `{1, …, N}`. -/
theorem BrickAccessibility.Challenge.corollaryB : BrickAccessibility.Statement.CorollaryB.{u} :=
  BrickAccessibility.corollaryB

/-- **Corollary 5.6.** The conclusions of Theorem A and Corollary B hold for basic
representation-finite biserial algebras. -/
theorem BrickAccessibility.Challenge.corollaryBiserial :
    BrickAccessibility.Statement.CorollaryBiserial.{u} :=
  BrickAccessibility.corollaryBiserial
