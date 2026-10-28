module

public import BrickAccessibility.Quiver.Classes
public import BrickAccessibility.Section2.CutDual

/-!
# The simple modules `S_v`

For monomial data, the simple module at a vertex `v` is the coefficient quiver
with a single position over `v` and no arrow moves. It is one-dimensional and
simple.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable (D : MonomialData k B)

/-- The coefficient quiver of the simple module at `v`. -/
def simpleCQ (v : D.Q.V) : D.CoeffQuiver where
  P := Unit
  vtx _ := v
  next _ _ := none
  coef _ _ := 0
  next_src _ _ _ h := by cases h
  next_tgt _ _ _ h := by cases h

theorem simpleCQ_kills (v : D.Q.V) : (D.simpleCQ v).KillsZeroPaths := by
  intro x l hxl i hi
  cases l with
  | nil =>
      exfalso
      simp only [simpleCQ] at hi
      rw [← hi] at hxl
      exact D.e_ne v hxl
  | cons a l => simp [CoeffQuiver.follow, simpleCQ]

/-- The simple module `S_v`. -/
abbrev simple (v : D.Q.V) : Type u := ((D.simpleCQ v).toRep (D.simpleCQ_kills v)).Carrier

theorem finrank_simple (v : D.Q.V) : finrank k (D.simple v) = 1 := by
  show finrank k (Unit → k) = 1
  simp

instance (v : D.Q.V) : FiniteDimensional k (D.simple v) :=
  Module.finite_of_finrank_eq_succ (D.finrank_simple v)

instance (v : D.Q.V) : IsSimpleModule B (D.simple v) :=
  isSimpleModule_of_finrank_eq_one (k := k) (D.finrank_simple v)

end MonomialData

end BrickAccessibility
