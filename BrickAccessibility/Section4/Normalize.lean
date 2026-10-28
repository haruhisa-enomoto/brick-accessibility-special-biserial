module

public import BrickAccessibility.Section4.Simple
public import BrickAccessibility.Basic.Ext

/-!
# Normalized derivations

For path data on `B`, every derivation `δ : B → Hom_k(M, X)` differs by an inner
derivation from one vanishing on all vertex idempotents
(`exists_normalized`), and a normalized derivation vanishing on all arrows is
zero (`eq_zero_of_normalized`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
variable {X : Type*} [AddCommGroup X] [Module B X] [Module k X] [IsScalarTower k B X]

namespace MonomialData

variable (D : MonomialData k B)

/-- Every derivation is cohomologous to one vanishing on the vertex idempotents. -/
theorem exists_normalized (δ : B →ₗ[k] M →ₗ[k] X) (hδ : δ ∈ Ext1.cocycles k B M X) :
    ∃ φ : M →ₗ[k] X, ∀ v, (δ - Ext1.inner k B M X φ) (D.e v) = 0 := by
  classical
  have hL : ∀ a b m, δ (a * b) m = a • δ b m + δ a (b • m) := hδ
  -- `φ m = Σ_w e_w • δ(e_w)(m)`
  let φ : M →ₗ[k] X := ∑ w, (DistribSMul.toLinearMap k X (D.e w)) ∘ₗ δ (D.e w)
  have hφ : ∀ m, φ m = ∑ w, D.e w • δ (D.e w) m := fun m ↦ by
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply]; rfl
  have hee : ∀ w m, D.e w • δ (D.e w) (D.e w • m) = 0 := by
    intro w m
    have h1 := hL (D.e w) (D.e w) (D.e w • m)
    rw [D.toPathData.e_idem, ← mul_smul, D.toPathData.e_idem] at h1
    have h2 := hL (D.e w) (D.e w) m
    rw [D.toPathData.e_idem] at h2
    -- `e_w • δ(e_w)(e_w m) = e_w • (e_w • δ(e_w)(e_w m) + δ(e_w)(e_w m))`
    have h3 := congrArg (fun x ↦ D.e w • x) h1
    simp only [smul_add, ← mul_smul, D.toPathData.e_idem] at h3
    have : D.e w • δ (D.e w) (D.e w • m) + D.e w • δ (D.e w) (D.e w • m) =
        D.e w • δ (D.e w) (D.e w • m) := by rw [← h3]
    simpa using this
  have hne : ∀ w v, w ≠ v → ∀ m, D.e w • δ (D.e w) (D.e v • m) = - D.e w • δ (D.e v) m := by
    intro w v hwv m
    have h1 := hL (D.e w) (D.e v) m
    rw [D.toPathData.e_mul_e_of_ne hwv, map_zero, LinearMap.zero_apply] at h1
    have h2 := congrArg (fun x ↦ D.e w • x) h1
    simp only [smul_zero, smul_add, ← mul_smul, D.toPathData.e_idem] at h2
    rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h2.symm
  refine ⟨φ, fun v ↦ ?_⟩
  ext m
  simp only [LinearMap.sub_apply, Ext1.inner_apply, hφ, LinearMap.zero_apply]
  rw [Finset.smul_sum, Finset.sum_eq_single v, ← mul_smul, D.toPathData.e_idem]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), hee]
    have hrest : ∑ w ∈ Finset.univ.erase v, D.e w • δ (D.e w) (D.e v • m) =
        ∑ w ∈ Finset.univ.erase v, -(D.e w • δ (D.e v) m) := by
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [hne w v (Finset.ne_of_mem_erase hw), neg_smul]
    rw [hrest, Finset.sum_neg_distrib, zero_add]
    -- `δ(e_v) m = e_v • δ(e_v) m + Σ_{w ≠ v} e_w • δ(e_v) m`
    have hsum : δ (D.e v) m = D.e v • δ (D.e v) m +
        ∑ w ∈ Finset.univ.erase v, D.e w • δ (D.e v) m := by
      rw [Finset.add_sum_erase _ (fun w ↦ D.e w • δ (D.e v) m) (Finset.mem_univ v),
        ← Finset.sum_smul, D.toPathData.sum_e, one_smul]
    rw [sub_neg_eq_add, ← hsum, sub_self]
  · intro w _ hw
    rw [← mul_smul, D.toPathData.e_mul_e_of_ne (Ne.symm hw), zero_smul]
  · simp

omit [IsScalarTower k B M] in
/-- A derivation vanishing on vertices and arrows is zero. -/
theorem eq_zero_of_normalized (δ : B →ₗ[k] M →ₗ[k] X) (hδ : δ ∈ Ext1.cocycles k B M X)
    (he : ∀ v, δ (D.e v) = 0) (hα : ∀ a, δ (D.α a) = 0) : δ = 0 := by
  have hL : ∀ a b m, δ (a * b) m = a • δ b m + δ a (b • m) := hδ
  have hp : ∀ x l, δ (D.pval x l) = 0 := by
    intro x l
    induction l generalizing x with
    | nil => exact he x
    | cons a l ih =>
        ext m
        simp only [PathData.pval]
        change δ (D.pval (D.Q.tgt a) l * D.α a * D.e x) m = 0
        rw [hL, hL, ih, he, hα]
        simp
  refine LinearMap.ext fun b ↦ ?_
  have hb : b ∈ Submodule.span k (Set.range (fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2)) := by
    rw [D.span_pval]; trivial
  induction hb using Submodule.span_induction with
  | mem b hb => obtain ⟨⟨x, l⟩, rfl⟩ := hb; simpa using hp x l
  | zero => simp
  | add b c _ _ hb hc => simp [hb, hc]
  | smul c b _ hb => simp [hb]

end MonomialData

end BrickAccessibility
