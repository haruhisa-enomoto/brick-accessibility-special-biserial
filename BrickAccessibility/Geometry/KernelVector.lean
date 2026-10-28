module

public import BrickAccessibility.Geometry.PolyFun
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A polynomial kernel vector

For an `n × (n+1)` matrix `X` and a column `J`, the vector with `J`-th entry
`det B` and remaining entries `-(adj B) c`, where `B` is `X` without column `J`
and `c` is column `J`, lies in the kernel of `X`. If `X` has rank `n`, some
column gives a nonzero vector, which then spans the kernel.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Matrix

variable {k : Type*} [Field k]

/-- The matrix without column `J`. -/
def dropCol {n : ℕ} (X : Matrix (Fin n) (Fin (n + 1)) k) (J : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) k :=
  X.submatrix id J.succAbove

/-- The polynomial kernel vector attached to column `J`. -/
def kernelVec {n : ℕ} (X : Matrix (Fin n) (Fin (n + 1)) k) (J : Fin (n + 1)) :
    Fin (n + 1) → k :=
  Fin.insertNth J (dropCol X J).det (-((dropCol X J).adjugate *ᵥ fun i ↦ X i J))

theorem mulVec_kernelVec {n : ℕ} (X : Matrix (Fin n) (Fin (n + 1)) k) (J : Fin (n + 1)) :
    X *ᵥ kernelVec X J = 0 := by
  funext i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [Fin.sum_univ_succAbove _ J]
  simp only [kernelVec, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have h := congrFun (congrArg (fun Y ↦ Y *ᵥ (fun i ↦ X i J)) (mul_adjugate (dropCol X J))) i
  simp only [← mulVec_mulVec, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul] at h
  have h2 : ∑ x, X i (J.succAbove x) * -((dropCol X J).adjugate *ᵥ fun i ↦ X i J) x =
      -((dropCol X J) *ᵥ ((dropCol X J).adjugate *ᵥ fun i ↦ X i J)) i := by
    simp [mulVec, dotProduct, dropCol, Finset.sum_neg_distrib]
  simp only [Pi.neg_apply] at h2 ⊢
  rw [h2, h]
  ring

theorem kernelVec_ne_zero {n : ℕ} (X : Matrix (Fin n) (Fin (n + 1)) k) (J : Fin (n + 1))
    (h : (dropCol X J).det ≠ 0) : kernelVec X J ≠ 0 := by
  intro h0
  apply h
  have := congrFun h0 J
  simpa [kernelVec] using this

/-- A matrix of rank `n` has a column whose removal leaves an invertible matrix. -/
theorem exists_det_dropCol_ne_zero {n : ℕ} (X : Matrix (Fin n) (Fin (n + 1)) k)
    (hX : Function.Surjective X.mulVecLin) : ∃ J, (dropCol X J).det ≠ 0 := by
  classical
  have hrank := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  rw [LinearMap.range_eq_top.mpr hX, finrank_top] at hrank
  simp only [Module.finrank_fin_fun] at hrank
  have hker : Module.finrank k (LinearMap.ker X.mulVecLin) = 1 := by omega
  obtain ⟨u, hu0, hu⟩ : ∃ u ∈ LinearMap.ker X.mulVecLin, u ≠ 0 := by
    by_contra hc
    push Not at hc
    have : LinearMap.ker X.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]; exact hc
    rw [this, finrank_bot] at hker
    exact zero_ne_one hker
  obtain ⟨J, hJ⟩ : ∃ J, u J ≠ 0 := by
    by_contra hc; push Not at hc; exact hu (funext hc)
  refine ⟨J, ?_⟩
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro y z hyz
  rw [← sub_eq_zero]
  set w := y - z
  have hw : (dropCol X J) *ᵥ w = 0 := by
    simp [w, mulVec_sub, hyz]
  have hmem : (Fin.insertNth J 0 w : Fin (n + 1) → k) ∈ LinearMap.ker X.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [Fin.sum_univ_succAbove _ J]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, mul_zero, zero_add]
    have := congrFun hw i
    simpa [mulVec, dotProduct, dropCol] using this
  -- the kernel is spanned by `u`
  have hspan : ∀ v ∈ LinearMap.ker X.mulVecLin, ∃ c : k, v = c • u := by
    intro v hv
    have hu' : (⟨u, hu0⟩ : LinearMap.ker X.mulVecLin) ≠ 0 := by
      intro h; apply hu; simpa using congrArg Subtype.val h
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hu').mp hker ⟨v, hv⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  obtain ⟨c, hc⟩ := hspan _ hmem
  have hcJ := congrFun hc J
  simp only [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul] at hcJ
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hcJ.symm with h | h
    · exact h
    · exact absurd h hJ
  funext j
  have := congrFun hc (J.succAbove j)
  simpa [Fin.insertNth_apply_succAbove, hc0] using this

/-- If removing column `J` leaves an invertible matrix, every kernel vector is a
multiple of `kernelVec X J`. -/
theorem exists_eq_smul_kernelVec {n : ℕ} (X : Matrix (Fin n) (Fin (n + 1)) k)
    (J : Fin (n + 1)) (hJ : (dropCol X J).det ≠ 0) (v : Fin (n + 1) → k)
    (hv : X *ᵥ v = 0) : ∃ t : k, v = t • kernelVec X J := by
  have hunit : IsUnit (dropCol X J) := by
    rw [isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hJ
  set t := v J / (dropCol X J).det
  refine ⟨t, ?_⟩
  set w := v - t • kernelVec X J
  have hwJ : w J = 0 := by
    simp [w, t, kernelVec, div_mul_cancel₀ _ hJ]
  have hw : X *ᵥ w = 0 := by
    simp [w, mulVec_sub, mulVec_smul, hv, mulVec_kernelVec]
  have hdrop : (dropCol X J) *ᵥ (fun j ↦ w (J.succAbove j)) = 0 := by
    funext i
    have := congrFun hw i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this ⊢
    rw [Fin.sum_univ_succAbove _ J, hwJ, mul_zero, zero_add] at this
    simpa [dropCol] using this
  have hinj := (mulVec_injective_iff_isUnit).mpr hunit
  have h0 : (fun j ↦ w (J.succAbove j)) = 0 := hinj (by rw [hdrop, mulVec_zero])
  have : w = 0 := by
    funext i
    rcases Fin.eq_self_or_eq_succAbove J i with rfl | ⟨j, rfl⟩
    · exact hwJ
    · exact congrFun h0 j
  rw [← sub_eq_zero]
  exact this

/-- Entries of `kernelVec` are polynomial in polynomial matrix entries. -/
theorem IsPolyFun.kernelVec {σ : Type*} {n : ℕ} {F : (σ → k) → Matrix (Fin n) (Fin (n + 1)) k}
    (hF : ∀ i j, IsPolyFun (fun x ↦ F x i j)) (J : Fin (n + 1)) (i : Fin (n + 1)) :
    IsPolyFun (fun x ↦ BrickAccessibility.kernelVec (F x) J i) := by
  have hD : ∀ a b, IsPolyFun (fun x ↦ dropCol (F x) J a b) := fun a b ↦ by
    simpa [dropCol] using hF a (J.succAbove b)
  rcases Fin.eq_self_or_eq_succAbove J i with rfl | ⟨j, rfl⟩
  · simpa [BrickAccessibility.kernelVec] using IsPolyFun.det hD
  · simp only [BrickAccessibility.kernelVec, Fin.insertNth_apply_succAbove, Pi.neg_apply,
      mulVec, dotProduct]
    exact (IsPolyFun.sum _ fun b _ ↦ (IsPolyFun.adjugate hD j b).mul (hF b J)).neg

end BrickAccessibility
