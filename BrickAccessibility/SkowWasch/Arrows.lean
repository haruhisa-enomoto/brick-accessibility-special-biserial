module

public import BrickAccessibility.SkowWasch.Kupisch

/-!
# Arrows and their representatives

An arrow `i → j` is a pair with `e_j R e_i ⊄ R²` (`Arr`). A choice of representatives
`ρ i j ∈ e_j R e_i \ R²` (`Valid`) spans the radical: every `y ∈ e_j R` is a combination of
`ρ i j · w` (`mem_span_right`), and every `y ∈ R e_j` of `w · ρ j k` (`mem_span_left`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] (B : BasicData k A)

/-- An arrow `i → j`. -/
def Arr (i j : Fin B.n) : Prop := ∃ g ∈ B.Mk i j, g ∉ B.R * B.R

/-- Representatives of the arrows. -/
def Valid (ρ : Fin B.n → Fin B.n → A) : Prop :=
  ∀ i j, B.Arr i j → ρ i j ∈ B.Mk i j ∧ ρ i j ∉ B.R * B.R

theorem exists_valid : ∃ ρ : Fin B.n → Fin B.n → A, B.Valid ρ := by
  classical
  refine ⟨fun i j ↦ if h : B.Arr i j then h.choose else 0, fun i j h ↦ ?_⟩
  simp only [dif_pos h]
  exact h.choose_spec

theorem mem_sq_of_not_arr {i j : Fin B.n} (h : ¬ B.Arr i j) {y : A} (hy : y ∈ B.Mk i j) :
    y ∈ B.R * B.R := by
  by_contra hy'
  exact h ⟨y, hy, hy'⟩

/-- The right radical `e_j R`. -/
def eR (j : Fin B.n) : Submodule k A where
  carrier := {y | B.e j * y = y ∧ y ∈ B.R}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [mul_add, ha, hb], B.R.add_mem ha' hb'⟩
  zero_mem' := ⟨by simp, B.R.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨by rw [mul_smul_comm, ha], B.R.smul_mem c ha'⟩

/-- The left radical `R e_j`. -/
def Re (j : Fin B.n) : Submodule k A where
  carrier := {y | y * B.e j = y ∧ y ∈ B.R}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [add_mul, ha, hb], B.R.add_mem ha' hb'⟩
  zero_mem' := ⟨by simp, B.R.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨by rw [smul_mul_assoc, ha], B.R.smul_mem c ha'⟩

/-- Right multiples of the arrows ending at `j`. -/
def Sright (ρ : Fin B.n → Fin B.n → A) (j : Fin B.n) : Submodule k A :=
  Submodule.span k {x | ∃ i w, B.Arr i j ∧ x = ρ i j * w}

/-- Left multiples of the arrows starting at `j`. -/
def Sleft (ρ : Fin B.n → Fin B.n → A) (j : Fin B.n) : Submodule k A :=
  Submodule.span k {x | ∃ l w, B.Arr j l ∧ x = w * ρ j l}

variable {B}

theorem e_mul_sq {j : Fin B.n} {x : A} (hx : x ∈ B.R * B.R) : B.e j * x ∈ B.eR j * B.R :=
  Submodule.mul_induction_on hx
    (fun r hr s hs ↦ by
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul ⟨by rw [← mul_assoc, B.e_idem], B.mul_mem_left _ _ hr⟩ hs)
    (fun x y h h' ↦ by rw [mul_add]; exact Submodule.add_mem _ h h')

theorem sq_mul_e {j : Fin B.n} {x : A} (hx : x ∈ B.R * B.R) : x * B.e j ∈ B.R * B.Re j :=
  Submodule.mul_induction_on hx
    (fun r hr s hs ↦ by
      rw [mul_assoc]
      exact Submodule.mul_mem_mul hr ⟨by rw [mul_assoc, B.e_idem], B.mul_mem_right _ _ hs⟩)
    (fun x y h h' ↦ by rw [add_mul]; exact Submodule.add_mem _ h h')

variable (hX : B.ChainX)
include hX

/-- **Right spanning**: `e_j R` is spanned by right multiples of arrows ending at `j`. -/
theorem eR_le {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) (j : Fin B.n) :
    B.eR j ≤ B.Sright ρ j := by
  classical
  refine B.le_of_le_sup_right ?_ ?_
  · rw [Submodule.mul_le]
    intro x hx r _
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, w, hi, rfl⟩ := hx
        rw [mul_assoc]; exact Submodule.subset_span ⟨i, w * r, hi, rfl⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  · intro y ⟨hy, hyR⟩
    have hsum : y = ∑ v, y * B.e v := by rw [← Finset.mul_sum, B.sum_e, mul_one]
    rw [hsum]
    refine Submodule.sum_mem _ fun v _ ↦ ?_
    have hyv : y * B.e v ∈ B.Mk v j :=
      ⟨by rw [← mul_assoc, hy, mul_assoc, B.e_idem], B.mul_mem_right _ _ hyR⟩
    have hsq : ∀ x ∈ B.R * B.R, B.e j * x ∈ B.Sright ρ j ⊔ B.eR j * B.R :=
      fun x hx ↦ Submodule.mem_sup_right (e_mul_sq hx)
    have hej : y * B.e v = B.e j * (y * B.e v) := by rw [← mul_assoc, hy]
    by_cases hv : B.Arr v j
    · have h := B.mem_span_sq hX (hρ v j hv).1 (hρ v j hv).2 hyv
      obtain ⟨u, hu, s, hs, hus⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [hej, ← hus, mul_add, mul_smul_comm, B.e_left (hρ v j hv).1]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ c ?_)) (hsq s hs)
      exact Submodule.subset_span ⟨v, 1, hv, by rw [mul_one]⟩
    · rw [hej]; exact hsq _ (B.mem_sq_of_not_arr hv hyv)

/-- **Left spanning**: `R e_j` is spanned by left multiples of arrows starting at `j`. -/
theorem Re_le {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) (j : Fin B.n) :
    B.Re j ≤ B.Sleft ρ j := by
  classical
  refine B.le_of_le_sup_left ?_ ?_
  · rw [Submodule.mul_le]
    intro r _ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨l, w, hl, rfl⟩ := hx
        rw [← mul_assoc]; exact Submodule.subset_span ⟨l, r * w, hl, rfl⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul c x _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  · intro y ⟨hy, hyR⟩
    have hsum : y = ∑ v, B.e v * y := by rw [← Finset.sum_mul, B.sum_e, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ fun v _ ↦ ?_
    have hyv : B.e v * y ∈ B.Mk j v := ⟨by rw [← mul_assoc, B.e_idem, mul_assoc, hy],
      B.mul_mem_left _ _ hyR⟩
    have hsq : ∀ x ∈ B.R * B.R, x * B.e j ∈ B.Sleft ρ j ⊔ B.R * B.Re j :=
      fun x hx ↦ Submodule.mem_sup_right (sq_mul_e hx)
    have hej : B.e v * y = B.e v * y * B.e j := by rw [mul_assoc, hy]
    by_cases hv : B.Arr j v
    · have h := B.mem_span_sq hX (hρ j v hv).1 (hρ j v hv).2 hyv
      obtain ⟨u, hu, s, hs, hus⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [hej, ← hus, add_mul, smul_mul_assoc, B.e_right (hρ j v hv).1]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ c ?_)) (hsq s hs)
      exact Submodule.subset_span ⟨v, 1, hv, by rw [one_mul]⟩
    · rw [hej]; exact hsq _ (B.mem_sq_of_not_arr hv hyv)

end BasicData

end SkowWasch

end BrickAccessibility
