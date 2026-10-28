module

public import BrickAccessibility.Quiver.Classes
public import BrickAccessibility.Basic.Inflation
public import BrickAccessibility.Classification.BrickPieces
public import BrickAccessibility.Classification.Plamondon

/-!
# Cited inputs on bricks over string and gentle algebras

* `isString_of_isBrick`: over a brick-finite string algebra, every brick is a
  string module (Butler–Ringel's string–band classification, Theorem 4.5, with
  the exclusion of band bricks recalled before Proposition 5.2).
* `isRepFinite_of_isBrickFinite`: Lemma 5.1, a brick-finite gentle algebra is
  representation-finite (Plamondon's band bricks, proved in `Classification.Plamondon`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- Over a brick-finite string algebra over an algebraically closed field, every
finite-dimensional brick is isomorphic to a string module. -/
theorem isString_of_isBrick [IsAlgClosed k] [FiniteDimensional k B] (D : MonomialData k B)
    (hD : D.IsStringAlgebra) (hbf : IsBrickFinite B) (M : Type u) [AddCommGroup M] [Module B M]
    [Module k M] [IsScalarTower k B M] [FiniteDimensional k M] (hM : IsBrick B M) :
    ∃ (w : Word D.Q) (hw : w.IsString D), Nonempty (M ≃ₗ[B] w.stringModule D hw) := by
  classical
  obtain ⟨S⟩ := MonomialData.exists_signs (D := D) hD.2
  obtain ⟨ι, hι, hιd, pc, ⟨e⟩⟩ := exists_decomposition S M
  have hX : IsBrick B (∀ i, (pc i).X) := hM.of_equiv e.symm
  obtain ⟨hU⟩ := unique_of_isBrick_pi (fun i ↦ (pc i).nontriv) hX
  set i₀ : ι := default
  have e₁ : M ≃ₗ[B] (pc i₀).X := e.symm.trans (LinearEquiv.piUnique B fun i ↦ (pc i).X)
  have hXb : IsBrick B (pc i₀).X := hM.of_equiv e₁
  rcases (pc i₀).kind with ⟨w, hs, V, _, _, _, hd, ⟨e₂⟩⟩ |
      ⟨b, hA, hK, hprim, V, _, _, _, φ, hd, ⟨e₂⟩⟩
  · have hV1 := w.finrank_eq_one_of_isBrick hs (hd ▸ (pc i₀).d_pos) (hXb.of_equiv e₂)
    let eV : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by rw [hV1, Module.finrank_self])
    obtain ⟨e₃⟩ := w.stringModule_equiv hs
    exact ⟨w, hs, ⟨e₁.trans (e₂.trans ((w.blockEquiv hs eV).trans e₃.symm))⟩⟩
  · exfalso
    have hV1 := b.finrank_eq_one_of_isBrick S hA hK φ (hd ▸ (pc i₀).d_pos) (hXb.of_equiv e₂)
    obtain ⟨t, ⟨e₃⟩⟩ := b.exists_equiv_BM S hA hK φ hV1
    exact b.not_isBrickFinite S hA hK hprim t ((hXb.of_equiv e₂).of_equiv e₃) hbf

/-- **Lemma 5.1.** A brick-finite gentle algebra over an algebraically closed field
is representation-finite. -/
theorem isRepFinite_of_isBrickFinite [IsAlgClosed k] [FiniteDimensional k B]
    (D : MonomialData k B) (hD : D.IsGentle) (hbf : IsBrickFinite B) : IsRepFinite B :=
  isRepFinite_of_not_hasClosed D hD.1 fun h ↦ D.not_isBrickFinite_of_hasClosed hD h hbf

end BrickAccessibility
