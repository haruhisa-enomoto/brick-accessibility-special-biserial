module

public import BrickAccessibility.Classification.BandJordan
public import BrickAccessibility.Classification.RepFinite

/-!
# Theorem 4.5: the string and band classification

Over an algebraically closed field `k`, for monomial data `D` with a sign choice `S` (a
string algebra):

* every indecomposable finite-dimensional module is a string module `M(w)` or a band module
  `M(ω, μ, n)` (`string_or_band`);
* for a band `ω` and `n ≥ 1`, the band modules `M(ω, μ, n)`, `μ ∈ kˣ`, are indecomposable and
  pairwise nonisomorphic (`isIndecomposable_bandModule`, `eq_of_bandModule_equiv`);
* a representation-finite string algebra has no bands (`not_isRepFinite_of_band`), and every
  indecomposable module is a string module (`string_of_isRepFinite`).

Here a band is a cyclic word that alternates for `S`, kills zero paths, and is primitive
(`CWord.Alt`, `CWord.KillsZero`, injectivity of `CWord.rightW`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

variable [IsAlgClosed k] {D : MonomialData k B} (S : D.Signs)

/-- **Theorem 4.5, first part.** Over an algebraically closed field, every indecomposable
finite-dimensional module over a string algebra is a string module or a band module
`M(ω, μ, n)`. -/
theorem string_or_band (M : Type u) [AddCommGroup M] [Module B M] [Module k M]
    [IsScalarTower k B M] [FiniteDimensional k M] (hM : IsIndecomposable B M) :
    (∃ (w : Word D.Q) (hs : w.IsString D), Nonempty (M ≃ₗ[B] w.stringModule D hs)) ∨
    (∃ (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)
      (_ : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (n : ℕ) (_ : 0 < n) (μ : kˣ),
        Nonempty (M ≃ₗ[B] b.bandModule S hA hK n μ)) := by
  classical
  obtain ⟨ι, _, _, pc, ⟨e⟩⟩ := exists_decomposition S M
  have hpi := isIndecomposable_of_equiv e.symm hM
  obtain ⟨hu⟩ := unique_of_isIndecomposable_pi (fun i ↦ (pc i).nontriv) hpi
  set i0 : ι := default
  let e0 : M ≃ₗ[B] (pc i0).X := e.symm.trans (LinearEquiv.piUnique B fun i ↦ (pc i).X)
  have hX : IsIndecomposable B (pc i0).X := isIndecomposable_of_equiv e0 hM
  rcases (pc i0).kind with ⟨w, hs, V, _, _, _, hd, ⟨eX⟩⟩ | ⟨b, hA, hK, hprim, V, _, _, _, φ, hd, ⟨eX⟩⟩
  · left
    have hV : finrank k V = 1 := w.finrank_eq_one_of_isIndecomposable hs
      (by rw [hd]; exact (pc i0).d_pos) (isIndecomposable_of_equiv eX hX)
    let eV : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by rw [hV, Module.finrank_self])
    obtain ⟨es⟩ := w.stringModule_equiv hs
    exact ⟨w, hs, ⟨e0.trans (eX.trans ((w.blockEquiv hs eV).trans es.symm))⟩⟩
  · right
    obtain ⟨n, hn, μ, ⟨eB⟩⟩ := b.exists_equiv_bandModule S hA hK φ (isIndecomposable_of_equiv eX hX)
    exact ⟨b, hA, hK, hprim, n, hn, μ, ⟨e0.trans (eX.trans eB)⟩⟩

/-- **Theorem 4.5, last part.** A representation-finite string algebra has no bands: the band
modules `M(ω, μ, 1)`, `μ ∈ kˣ`, are infinitely many pairwise nonisomorphic indecomposables. -/
theorem not_isRepFinite_of_band (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)
    (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) : ¬ IsRepFinite B := by
  classical
  rintro ⟨N, Bs, hB⟩
  have hfin : ∀ μ : kˣ, Module.Finite B (b.bandModule S hA hK 1 μ) := fun μ ↦
    Module.Finite.of_restrictScalars_finite k B _
  have hcls : ∀ μ : kˣ, ∃ i, Nonempty (b.bandModule S hA hK 1 μ ≃ₗ[B] Bs i) := fun μ ↦
    hB _ (b.isIndecomposable_bandModule S hA hK hprim one_pos μ)
  choose cls hcls using hcls
  let F : k → Option (Fin N) := fun x ↦ if h : x = 0 then none else some (cls (Units.mk0 x h))
  obtain ⟨x, y, hxy, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · exact hxy (hx.trans hy.symm)
    · simp [F, hx, hy] at hF
  · by_cases hy : y = 0
    · simp [F, hx, hy] at hF
    · simp only [F, dif_neg hx, dif_neg hy, Option.some.injEq] at hF
      obtain ⟨e1⟩ := hcls (Units.mk0 x hx)
      obtain ⟨e2⟩ := hcls (Units.mk0 y hy)
      rw [hF] at e1
      have := b.eq_of_bandModule_equiv S hA hK hprim one_pos (e1.trans e2.symm)
      exact hxy (by simpa using congrArg Units.val this)

include S in
/-- **Theorem 4.5, last part.** Over a representation-finite string algebra every
indecomposable module is a string module. -/
theorem string_of_isRepFinite (hrf : IsRepFinite B) (M : Type u) [AddCommGroup M] [Module B M]
    [Module k M] [IsScalarTower k B M] [FiniteDimensional k M] (hM : IsIndecomposable B M) :
    ∃ (w : Word D.Q) (hs : w.IsString D), Nonempty (M ≃ₗ[B] w.stringModule D hs) := by
  rcases string_or_band S M hM with h | ⟨b, hA, hK, hprim, -⟩
  · exact h
  · exact absurd hrf (not_isRepFinite_of_band S b hA hK hprim)

end BrickAccessibility
