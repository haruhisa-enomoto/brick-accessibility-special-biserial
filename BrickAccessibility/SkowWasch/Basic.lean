module

public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basic algebras: idempotents and a nilpotent radical

`BasicData k A` records a complete set of orthogonal idempotents `e v` and a nilpotent
two-sided ideal `R` such that `A = ⊕ k e_v ⊕ R`. Every corner `e_i a e_j` with `i ≠ j` lies
in `R`, and `e_i a e_i` is a scalar plus an element of `R` (`corner`). A scalar plus an
element of `R` is a unit (`isUnit_add`), and Nakayama's lemma holds for ideals
(`le_of_le_sup`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

variable (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A]

/-- Orthogonal idempotents complemented by a nilpotent two-sided ideal. -/
structure BasicData where
  n : ℕ
  e : Fin n → A
  e_mul_e : ∀ v w, e v * e w = if v = w then e v else 0
  sum_e : ∑ v, e v = 1
  R : Submodule k A
  mul_mem_left : ∀ (a r : A), r ∈ R → a * r ∈ R
  mul_mem_right : ∀ (r a : A), r ∈ R → r * a ∈ R
  pow_eq_bot : ∃ N : ℕ, R ^ N = ⊥
  decomp : ∀ a : A, ∃ c : Fin n → k, a - ∑ v, c v • e v ∈ R
  e_not_mem : ∀ v, e v ∉ R

namespace BasicData

variable {k A} (B : BasicData k A)

theorem e_idem (v : Fin B.n) : B.e v * B.e v = B.e v := by simp [B.e_mul_e]

theorem e_mul_e_of_ne {v w : Fin B.n} (h : v ≠ w) : B.e v * B.e w = 0 := by
  simp [B.e_mul_e, h]

theorem e_ne (v : Fin B.n) : B.e v ≠ 0 := fun h ↦ B.e_not_mem v (h ▸ B.R.zero_mem)

theorem pow_mem {r : A} (hr : r ∈ B.R) (m : ℕ) (hm : 0 < m) : r ^ m ∈ B.R ^ m := by
  exact Submodule.pow_mem_pow B.R hr m

theorem isNilpotent {r : A} (hr : r ∈ B.R) : IsNilpotent r := by
  obtain ⟨N, hN⟩ := B.pow_eq_bot
  refine ⟨N, ?_⟩
  have := Submodule.pow_mem_pow B.R hr N
  rw [hN] at this
  exact (Submodule.mem_bot k).mp this

/-- A nonzero scalar plus a radical element is a unit. -/
theorem isUnit_add {c : k} (hc : c ≠ 0) {r : A} (hr : r ∈ B.R) :
    IsUnit (algebraMap k A c + r) :=
  (B.isNilpotent hr).isUnit_add_left_of_commute ((IsUnit.mk0 c hc).map (algebraMap k A))
    (Algebra.commutes c r).symm

theorem isUnit_one_sub {r : A} (hr : r ∈ B.R) : IsUnit (1 - r) := by
  have := B.isUnit_add one_ne_zero (B.R.neg_mem hr)
  rwa [map_one, ← sub_eq_add_neg] at this

/-- An element fixed by left multiplication with a radical element vanishes. -/
theorem eq_zero_of_eq_mul_left {r x : A} (hr : r ∈ B.R) (h : x = r * x) : x = 0 := by
  have h1 : (1 - r) * x = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact ((B.isUnit_one_sub hr).mul_right_eq_zero).mp h1

theorem eq_zero_of_eq_mul_right {r x : A} (hr : r ∈ B.R) (h : x = x * r) : x = 0 := by
  have h1 : x * (1 - r) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  exact ((B.isUnit_one_sub hr).mul_left_eq_zero).mp h1

/-- Off-diagonal corners lie in the radical. -/
theorem corner_mem {i j : Fin B.n} (hij : i ≠ j) (a : A) : B.e i * a * B.e j ∈ B.R := by
  obtain ⟨c, hc⟩ := B.decomp a
  have key : B.e i * a * B.e j = B.e i * (a - ∑ v, c v • B.e v) * B.e j := by
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    have : ∑ v, B.e i * (c v • B.e v) * B.e j = 0 := by
      refine Finset.sum_eq_zero fun v _ ↦ ?_
      rw [mul_smul_comm, smul_mul_assoc, B.e_mul_e, ite_mul, zero_mul]
      split_ifs with h
      · subst h; rw [B.e_mul_e_of_ne hij, smul_zero]
      · rw [smul_zero]
    rw [this, sub_zero]
  rw [key]
  exact B.mul_mem_right _ _ (B.mul_mem_left _ _ hc)

/-- Diagonal corners are a scalar plus a radical element of the corner. -/
theorem corner (i : Fin B.n) (a : A) :
    ∃ (c : k) (r : A), r ∈ B.R ∧ B.e i * r * B.e i = r ∧
      B.e i * a * B.e i = c • B.e i + r := by
  obtain ⟨c, hc⟩ := B.decomp a
  set r := B.e i * (a - ∑ v, c v • B.e v) * B.e i
  refine ⟨c i, r, B.mul_mem_right _ _ (B.mul_mem_left _ _ hc), ?_, ?_⟩
  · simp only [r, ← mul_assoc, B.e_idem]
    rw [mul_assoc (B.e i * _ ), mul_assoc, B.e_idem, ← mul_assoc]
  · simp only [r, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    have : ∑ v, B.e i * (c v • B.e v) * B.e i = c i • B.e i := by
      rw [Finset.sum_eq_single i]
      · rw [mul_smul_comm, smul_mul_assoc, B.e_idem, B.e_idem]
      · intro v _ hv
        rw [mul_smul_comm, smul_mul_assoc, B.e_mul_e_of_ne (Ne.symm hv), zero_mul, smul_zero]
      · simp
    rw [this]; abel

/-- **Nakayama's lemma** for ideals: `X ≤ Y + R X + X R` forces `X ≤ Y`. -/
theorem le_of_le_sup {X Y : Submodule k A} (hXR : X ≤ B.R) (hY1 : B.R * Y ≤ Y)
    (hY2 : Y * B.R ≤ Y) (h : X ≤ Y ⊔ B.R * X ⊔ X * B.R) : X ≤ Y := by
  have key : ∀ m : ℕ, X ≤ Y ⊔ B.R ^ (m + 1) := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one]; exact le_sup_of_le_right hXR
    | succ m ih =>
        refine h.trans (sup_le (sup_le le_sup_left ?_) ?_)
        · refine (mul_le_mul' le_rfl ih).trans ?_
          rw [Submodule.mul_sup]
          refine sup_le (hY1.trans le_sup_left) (le_sup_of_le_right ?_)
          rw [← pow_succ']
        · refine (mul_le_mul' ih le_rfl).trans ?_
          rw [Submodule.sup_mul]
          refine sup_le (hY2.trans le_sup_left) (le_sup_of_le_right ?_)
          rw [← pow_succ]
  obtain ⟨N, hN⟩ := B.pow_eq_bot
  have := key N
  have hN' : B.R ^ (N + 1) = ⊥ := by rw [pow_succ, hN, Submodule.bot_mul]
  rwa [hN', sup_bot_eq] at this

end BasicData

end SkowWasch

end BrickAccessibility
