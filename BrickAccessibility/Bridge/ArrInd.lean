module

public import BrickAccessibility.Bridge.Presentation
public import BrickAccessibility.StringQuotient.Exact

/-!
# Arrows of an admissible presentation are independent modulo `R²`

Since the kernel of an admissible presentation lies in the square of the arrow ideal, the
images of the arrows are linearly independent modulo paths of length at least two
(`arrInd`). For each arrow `a`, a two-dimensional representation of `kQ` in which only `a`
acts nonzero and all words of length two vanish detects the coefficient of `a`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility.Statement

open MulOpposite

universe u

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]

namespace AdmissiblePresentation

variable (P : AdmissiblePresentation k Λ)

/-- A representation of `kQ` in which only the arrow `a` acts nonzero. -/
theorem exists_arrow_rep (a : P.Q.A) : ∃ φ : P.Q.PathAlgebra k →ₐ[k] Matrix (Fin 2) (Fin 2) k,
    (∀ l : List P.Q.A, 2 ≤ l.length → φ (P.Q.word k l) = 0) ∧
      ∀ b, φ (P.Q.arrow k b) = !![0, if b = a then 1 else 0; 0, 0] := by
  classical
  let ev : P.Q.V → Matrix (Fin 2) (Fin 2) k := fun w ↦
    !![if w = P.Q.src a then 1 else 0, 0; 0, if w = P.Q.tgt a then 1 else 0]
  let ea : P.Q.A → Matrix (Fin 2) (Fin 2) k := fun b ↦ !![0, if b = a then 1 else 0; 0, 0]
  let φ := FinQuiver.liftOfRelations (k := k) (Q := P.Q) ev ea
    (by
      intro w w'
      by_cases h : w = w'
      · subst h
        ext i j; fin_cases i <;> fin_cases j <;> simp [ev, Matrix.mul_fin_two] <;> aesop
      · rw [if_neg h]
        ext i j; fin_cases i <;> fin_cases j <;> simp [ev, Matrix.mul_fin_two] <;> aesop)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ev, Matrix.sum_apply, Finset.sum_ite_eq'])
    (by
      intro b
      ext i j; fin_cases i <;> fin_cases j <;> simp [ev, ea, Matrix.mul_fin_two] <;> aesop)
    (by
      intro b
      ext i j; fin_cases i <;> fin_cases j <;> simp [ev, ea, Matrix.mul_fin_two] <;> aesop)
  refine ⟨φ, fun l hl ↦ ?_, fun b ↦ FinQuiver.liftOfRelations_arrow _ _ _ _ _ _ b⟩
  obtain ⟨b, l', rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < l.length)
  obtain ⟨b', l'', rfl⟩ := List.exists_cons_of_length_pos (by simp at hl; omega : 0 < l'.length)
  rw [FinQuiver.word_cons, FinQuiver.word_cons, map_mul, map_mul,
    FinQuiver.liftOfRelations_arrow, FinQuiver.liftOfRelations_arrow, ← mul_assoc]
  have : ea b * ea b' = 0 := by
    simp only [ea, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, zero_mul]

/-- **Arrows are independent modulo `R²`.** -/
theorem arrInd : P.toPathData.ArrInd (k := k) := by
  classical
  intro c hc
  funext a
  obtain ⟨φ, hφ, hφa⟩ := P.exists_arrow_rep a
  -- elements of `Λᵐᵒᵖ` all of whose preimages are killed by `φ`
  let G : Submodule k Λᵐᵒᵖ :=
    { carrier := {y | ∀ z, op (P.π z) = y → φ z = 0}
      add_mem' := by
        intro y₁ y₂ h₁ h₂ z hz
        obtain ⟨z₁, hz₁⟩ := P.surjective y₁.unop
        have e1 : op (P.π z₁) = y₁ := by rw [hz₁]; rfl
        have e2 : op (P.π (z - z₁)) = y₂ := by
          rw [map_sub, op_sub, hz, e1, add_sub_cancel_left]
        have := h₂ _ e2
        rw [map_sub, h₁ _ e1, sub_zero] at this
        exact this
      zero_mem' := by
        intro z hz
        exact P.map_eq_zero_of_ker φ hφ (by simpa using hz)
      smul_mem' := by
        intro μ y h z hz
        obtain ⟨z₁, hz₁⟩ := P.surjective y.unop
        have e1 : op (P.π z₁) = y := by rw [hz₁]; rfl
        have e2 : P.π (z - μ • z₁) = 0 := by
          apply op_injective
          rw [map_sub, op_sub, map_smul, op_smul, e1, hz, sub_self, op_zero]
        have := P.map_eq_zero_of_ker φ hφ e2
        rw [map_sub, map_smul, h _ e1, smul_zero, sub_zero] at this
        exact this }
  have hle : P.toPathData.RadGe k 2 ≤ G := by
    rw [PathData.RadGe, Submodule.span_le]
    rintro _ ⟨x, l, hl, rfl⟩ z hz
    rw [pval_eq] at hz
    have h1 : P.π (z - P.Q.vertex k x * P.Q.word k l) = 0 := by
      rw [map_sub, sub_eq_zero]; exact op_injective hz
    have := P.map_eq_zero_of_ker φ hφ h1
    rw [map_sub, map_mul, hφ l hl, mul_zero, sub_zero] at this
    exact this
  have hz : op (P.π (∑ b, c b • P.Q.arrow k b)) = ∑ b, c b • P.toPathData.α b := by
    rw [map_sum, show op (∑ b, P.π (c b • P.Q.arrow k b)) = ∑ b, op (P.π (c b • P.Q.arrow k b))
      from map_sum (opAddEquiv : Λ ≃+ Λᵐᵒᵖ) _ _]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [map_smul, op_smul]; rfl
  have h0 := hle hc _ hz
  rw [map_sum] at h0
  simp only [map_smul, hφa] at h0
  have := congrFun (congrFun h0 0) 1
  simpa [Matrix.sum_apply, Finset.sum_ite_eq'] using this

/-- **Lemma 5.3** for `Λ = kQ/I` special biserial: with `J` the sum of the socles of the
nonuniserial injective summands `e_iΛ` (right modules, as left `Λᵐᵒᵖ`-modules), `J` is a
two-sided ideal, `Λ/J` is a string algebra, and every indecomposable right module not
annihilated by `J` is a nonuniserial projective-injective module. -/
theorem stringQuotient_exact [FiniteDimensional k Λ] (hP : P.IsSpecialBiserial) :
    ∃ (_ : (PathData.socIdeal P.toPathData).IsTwoSided)
      (D' : MonomialData k (Λᵐᵒᵖ ⧸ PathData.socIdeal P.toPathData)), D'.IsStringAlgebra ∧
      ∀ (M : Type u) [AddCommGroup M] [Module Λᵐᵒᵖ M] [Module k M] [IsScalarTower k Λᵐᵒᵖ M]
        [FiniteDimensional k M], IsIndecomposable Λᵐᵒᵖ M →
          ¬ Module.IsTorsionBySet Λᵐᵒᵖ M (PathData.socIdeal P.toPathData) →
            Module.Projective Λᵐᵒᵖ M ∧ Module.Injective Λᵐᵒᵖ M ∧ ¬ IsUniserialMod Λᵐᵒᵖ M := by
  have : FiniteDimensional k Λᵐᵒᵖ := Module.Finite.equiv (opLinearEquiv k : Λ ≃ₗ[k] Λᵐᵒᵖ)
  exact PathData.string_quotient_exact P.isAdmissible (P.isSpecialBiserial hP) P.span_pval
    P.arrInd

end AdmissiblePresentation

end BrickAccessibility.Statement
