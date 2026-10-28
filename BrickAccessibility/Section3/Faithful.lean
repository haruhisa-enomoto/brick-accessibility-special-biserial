module

public import BrickAccessibility.Section3.FaithfulGentle
public import BrickAccessibility.Basic.Inflation

/-!
# Proposition 3.8: the faithful quotient of a brick string module is gentle

For a string algebra and a string `w` whose string module `M(w)` is a brick, the
quotient `B ⧸ ann(M(w))` carries gentle monomial data.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- **Proposition 3.8.** -/
theorem exists_gentle_faithful_quotient (D : MonomialData k B) (hD : D.IsStringAlgebra)
    (w : Word D.Q) (hw : w.IsString D) (hb : IsBrick B (w.stringModule D hw)) :
    ∃ D' : MonomialData k (B ⧸ Module.annihilator B (w.stringModule D hw)), D'.IsGentle :=
  ⟨w.faithfulData hw, w.faithful_isGentle hw hD hb⟩

end BrickAccessibility
