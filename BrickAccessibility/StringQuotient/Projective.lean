module

public import BrickAccessibility.StringQuotient.Opposite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Modules not killed by `J` are projective

If `z ∈ e_y A e_x` generates the socles of both `A e_x` and `e_y A`, then the pairing
`(t, w) ↦ ξ (t w)` makes `A e_x` the `k`-dual of `e_y A`. An indecomposable module `M` with
`z m ≠ 0` then receives `A e_x` as a direct summand, so `M ≅ A e_x` is projective
(`projective_of_socles`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

namespace PathData

universe u

variable {k : Type*} [Field k] {Q : FinQuiver} {A : Type u} [Ring A] [Algebra k A]
  {D : PathData Q A}

variable (D) in
/-- The left ideal `A e_x`. -/
def Lx (x : Q.V) : Submodule A A where
  carrier := {w | w * D.e x = w}
  add_mem' {a b} ha hb := by
    show (a + b) * D.e x = a + b
    rw [add_mul, show a * D.e x = a from ha, show b * D.e x = b from hb]
  zero_mem' := zero_mul _
  smul_mem' c w hw := by
    show c * w * D.e x = c * w
    rw [mul_assoc, show w * D.e x = w from hw]

variable (k D) in
/-- The subspace `e_y A`. -/
def Ry (y : Q.V) : Submodule k A where
  carrier := {t | D.e y * t = t}
  add_mem' {a b} ha hb := by
    show D.e y * (a + b) = a + b
    rw [mul_add, show D.e y * a = a from ha, show D.e y * b = b from hb]
  zero_mem' := mul_zero _
  smul_mem' c t ht := by
    show D.e y * (c • t) = c • t
    rw [mul_smul_comm, show D.e y * t = t from ht]

theorem mem_Lx {x : Q.V} {w : A} : w ∈ D.Lx x ↔ w * D.e x = w := Iff.rfl

theorem mem_Ry {y : Q.V} {t : A} : t ∈ Ry k D y ↔ D.e y * t = t := Iff.rfl

/-- **The pairing** `(t, w) ↦ ξ (t w)` identifies `A e_x` with the dual of `e_y A`. -/
theorem exists_pairing [FiniteDimensional k A] {x y : Q.V} {z : A}
    (hzx : z * D.e x = z) (hyz : D.e y * z = z) (hz0 : z ≠ 0)
    (S1 : ∀ w, w * D.e x = w → w ≠ 0 → ∃ c, c * w = z)
    (S2 : ∀ t, D.e y * t = t → t ≠ 0 → ∃ c, t * c = z) :
    ∃ (ξ : Module.Dual k A) (Φ : D.Lx x →ₗ[k] Module.Dual k (Ry k D y)),
      ξ z ≠ 0 ∧ Function.Bijective Φ ∧ ∀ w t, Φ w t = ξ (t.1 * w.1) := by
  classical
  set L := D.Lx x
  set R := Ry k D y
  have : FiniteDimensional k L :=
    FiniteDimensional.of_injective (L.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨ξ, hξ⟩ := Module.Projective.exists_dual_ne_zero k hz0
  let Φ : L →ₗ[k] Module.Dual k R := LinearMap.mk₂ k (fun w t ↦ ξ (t.1 * w.1))
    (fun w₁ w₂ t ↦ by simp [mul_add])
    (fun c w t ↦ by simp)
    (fun w t₁ t₂ ↦ by simp [add_mul])
    (fun c w t ↦ by simp)
  let Ψ : R →ₗ[k] Module.Dual k L := LinearMap.mk₂ k (fun t w ↦ ξ (t.1 * w.1))
    (fun t₁ t₂ w ↦ by simp [add_mul])
    (fun c t w ↦ by simp)
    (fun t w₁ w₂ ↦ by simp [mul_add])
    (fun c t w ↦ by simp)
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hw0
    have hw0' : w.1 ≠ 0 := fun h ↦ hw0 (Subtype.ext h)
    obtain ⟨c, hc⟩ := S1 w.1 w.2 hw0'
    have ht : D.e y * c ∈ R := by
      show D.e y * (D.e y * c) = D.e y * c
      rw [← mul_assoc, D.e_idem]
    have h1 := LinearMap.congr_fun hw ⟨_, ht⟩
    simp only [Φ, LinearMap.mk₂_apply, LinearMap.zero_apply] at h1
    rw [mul_assoc, hc, hyz] at h1
    exact hξ h1
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    by_contra ht0
    have ht0' : t.1 ≠ 0 := fun h ↦ ht0 (Subtype.ext h)
    obtain ⟨c, hc⟩ := S2 t.1 t.2 ht0'
    have hw : c * D.e x ∈ L := by
      show c * D.e x * D.e x = c * D.e x
      rw [mul_assoc, D.e_idem]
    have h1 := LinearMap.congr_fun ht ⟨_, hw⟩
    simp only [Ψ, LinearMap.mk₂_apply, LinearMap.zero_apply] at h1
    rw [← mul_assoc, hc, hzx] at h1
    exact hξ h1
  have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
  have h2 := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Subspace.dual_finrank_eq] at h1 h2
  have hΦs : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq]; omega)).mp hΦ
  exact ⟨ξ, Φ, hξ, ⟨hΦ, hΦs⟩, fun w t ↦ rfl⟩

/-- **The exceptional module**: an indecomposable `M` with `z m ≠ 0` is `A e_x`. -/
theorem equiv_of_socles [FiniteDimensional k A] {x y : Q.V} {z : A}
    (hzx : z * D.e x = z) (hyz : D.e y * z = z) (hz0 : z ≠ 0)
    (S1 : ∀ w, w * D.e x = w → w ≠ 0 → ∃ c, c * w = z)
    (S2 : ∀ t, D.e y * t = t → t ≠ 0 → ∃ c, t * c = z)
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] (hM : IsIndecomposable A M) {m : M} (hm : z • m ≠ 0) :
    Nonempty (D.Lx x ≃ₗ[A] M) := by
  classical
  set L := D.Lx x
  set R := Ry k D y
  have : FiniteDimensional k L :=
    FiniteDimensional.of_injective (L.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨ξ, Φ, -, ⟨hΦ, hΦs⟩, hΦd⟩ := D.exists_pairing (k := k) hzx hyz hz0 S1 S2
  let Φe := LinearEquiv.ofBijective Φ ⟨hΦ, hΦs⟩
  -- the module side
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_ne_zero k hm
  let G : M →ₗ[k] Module.Dual k R := LinearMap.mk₂ k (fun n t ↦ χ (t.1 • n))
    (fun n₁ n₂ t ↦ by simp [smul_add])
    (fun c n t ↦ by simp [smul_comm (t.1 : A) c n])
    (fun n t₁ t₂ ↦ by simp [add_smul])
    (fun c n t ↦ by simp [smul_assoc])
  let ρ0 : M →ₗ[k] L := Φe.symm.toLinearMap ∘ₗ G
  have hρ0 : ∀ n, Φ (ρ0 n) = G n := fun n ↦ Φe.apply_symm_apply (G n)
  have hlin : ∀ (c : A) (n : M), ρ0 (c • n) = c • ρ0 n := by
    intro c n
    apply hΦ
    rw [hρ0]
    ext t
    have htc : t.1 * c ∈ R := by
      show D.e y * (t.1 * c) = t.1 * c
      rw [← mul_assoc, show D.e y * t.1 = t.1 from t.2]
    have h3 := LinearMap.congr_fun (hρ0 n) ⟨_, htc⟩
    rw [hΦd] at h3
    simp only [G, LinearMap.mk₂_apply] at h3 ⊢
    rw [hΦd, Submodule.coe_smul, smul_eq_mul, ← mul_assoc, h3, mul_smul]
  let ρ : M →ₗ[A] L :=
    { toFun := ρ0, map_add' := ρ0.map_add, map_smul' := hlin }
  let f : L →ₗ[A] M := (LinearMap.toSpanSingleton A M (D.e x • m)) ∘ₗ L.subtype
  have hzL : z ∈ L := hzx
  have hfz : f ⟨z, hzL⟩ = z • m := by
    show z • D.e x • m = z • m
    rw [smul_smul, hzx]
  have hρz : ρ (z • m) ≠ 0 := by
    intro h
    have h3 := LinearMap.congr_fun (hρ0 (z • m)) ⟨D.e y, D.e_idem y⟩
    change Φ (ρ (z • m)) _ = _ at h3
    rw [h, map_zero] at h3
    simp only [G, LinearMap.mk₂_apply, LinearMap.zero_apply, smul_smul, hyz] at h3
    exact hχ h3.symm
  set h := ρ ∘ₗ f
  have hinj : Function.Injective h := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hw0
    have hw0' : w.1 ≠ 0 := fun h' ↦ hw0 (Subtype.ext h')
    obtain ⟨c, hc⟩ := S1 w.1 w.2 hw0'
    have h3 : h (c • w) = 0 := by rw [map_smul, hw, smul_zero]
    have hcw : c • w = ⟨z, hzL⟩ := Subtype.ext hc
    rw [hcw] at h3
    apply hρz
    rw [← hfz]
    exact h3
  have hsurj : Function.Surjective h :=
    LinearMap.injective_iff_surjective (f := h.restrictScalars k) |>.mp hinj
  let hinv := LinearEquiv.ofBijective h ⟨hinj, hsurj⟩
  let g : M →ₗ[A] L := hinv.symm.toLinearMap ∘ₗ ρ
  have hgf : ∀ w, g (f w) = w := fun w ↦ hinv.symm_apply_apply w
  have hcompl : IsCompl (LinearMap.range f) (LinearMap.ker g) := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro v ⟨w, rfl⟩ hv
      rw [LinearMap.mem_ker, hgf] at hv
      rw [hv, map_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      rw [Submodule.mem_sup]
      refine ⟨f (g v), ⟨g v, rfl⟩, v - f (g v), ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hgf, sub_self]
  rcases hM.2 _ _ hcompl with h0 | h0
  · exfalso
    apply hm
    rw [← hfz]
    have : f ⟨z, hzL⟩ ∈ LinearMap.range f := ⟨_, rfl⟩
    rw [h0] at this
    exact (Submodule.mem_bot A).mp this
  · have hgi : Function.Injective g := LinearMap.ker_eq_bot.mp h0
    have hfs : Function.Surjective f := fun v ↦ ⟨g v, hgi (hgf (g v))⟩
    have hfi : Function.Injective f := fun w w' hww ↦ by rw [← hgf w, ← hgf w', hww]
    exact ⟨LinearEquiv.ofBijective f ⟨hfi, hfs⟩⟩

theorem lx_projective (x : Q.V) : Module.Projective A (D.Lx x) := by
  let s : A →ₗ[A] D.Lx x := LinearMap.codRestrict (D.Lx x) (LinearMap.toSpanSingleton A A (D.e x))
    (fun c ↦ show c • D.e x * D.e x = c • D.e x by rw [smul_eq_mul, mul_assoc, D.e_idem])
  exact Module.Projective.of_split (D.Lx x).subtype s (by ext w; exact w.2)

/-- **Projectivity from two socles.** -/
theorem projective_of_socles [FiniteDimensional k A] {x y : Q.V} {z : A}
    (hzx : z * D.e x = z) (hyz : D.e y * z = z) (hz0 : z ≠ 0)
    (S1 : ∀ w, w * D.e x = w → w ≠ 0 → ∃ c, c * w = z)
    (S2 : ∀ t, D.e y * t = t → t ≠ 0 → ∃ c, t * c = z)
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] (hM : IsIndecomposable A M) {m : M} (hm : z • m ≠ 0) :
    Module.Projective A M := by
  obtain ⟨e⟩ := D.equiv_of_socles (k := k) hzx hyz hz0 S1 S2 M hM hm
  have := D.lx_projective x
  exact Module.Projective.of_equiv e

/-- **Injectivity from two socles**: `A e_x` is the dual of the projective `e_y A`. -/
theorem injective_of_socles [FiniteDimensional k A] {x y : Q.V} {z : A}
    (hzx : z * D.e x = z) (hyz : D.e y * z = z) (hz0 : z ≠ 0)
    (S1 : ∀ w, w * D.e x = w → w ≠ 0 → ∃ c, c * w = z)
    (S2 : ∀ t, D.e y * t = t → t ≠ 0 → ∃ c, t * c = z) :
    Module.Injective A (D.Lx x) := by
  classical
  obtain ⟨ξ, Φ, -, ⟨hΦ, hΦs⟩, hΦd⟩ := D.exists_pairing (k := k) hzx hyz hz0 S1 S2
  let Φe := LinearEquiv.ofBijective Φ ⟨hΦ, hΦs⟩
  have hrm : ∀ (t : Ry k D y) (a : A), t.1 * a ∈ Ry k D y := fun t a ↦ by
    show D.e y * (t.1 * a) = t.1 * a
    rw [← mul_assoc, show D.e y * t.1 = t.1 from t.2]
  let rmul : A → Ry k D y →ₗ[k] Ry k D y := fun a ↦
    { toFun := fun t ↦ ⟨t.1 * a, hrm t a⟩
      map_add' := fun t t' ↦ Subtype.ext (add_mul _ _ _)
      map_smul' := fun c t ↦ Subtype.ext (smul_mul_assoc _ _ _) }
  have hΦa : ∀ (a : A) (w : D.Lx x) (t : Ry k D y), Φ (a • w) t = Φ w (rmul a t) := by
    intro a w t
    rw [hΦd, hΦd]
    show ξ (t.1 * (a * w.1)) = ξ (t.1 * a * w.1)
    rw [mul_assoc]
  have hey : D.e y ∈ Ry k D y := D.e_idem y
  refine Module.Baer.injective fun I g ↦ ?_
  let W : Submodule k (Ry k D y) := (I.restrictScalars k).comap (Ry k D y).subtype
  let ψ : W →ₗ[k] k :=
    { toFun := fun t ↦ Φ (g ⟨t.1.1, t.2⟩) ⟨D.e y, hey⟩
      map_add' := fun t t' ↦ by
        show Φ (g (⟨t.1.1, t.2⟩ + ⟨t'.1.1, t'.2⟩)) _ = _
        rw [map_add, map_add, LinearMap.add_apply]
      map_smul' := fun c t ↦ by
        have e1 : (⟨(c • t).1.1, (c • t).2⟩ : I) = algebraMap k A c • ⟨t.1.1, t.2⟩ :=
          Subtype.ext (by simp [Algebra.smul_def])
        show Φ (g ⟨(c • t).1.1, (c • t).2⟩) _ = _
        rw [e1, map_smul, algebraMap_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply,
          smul_eq_mul] }
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ψ
  let g'k : A → D.Lx x := fun a ↦ Φe.symm (φ ∘ₗ rmul a)
  have hg' : ∀ a, Φ (g'k a) = φ ∘ₗ rmul a := fun a ↦ Φe.apply_symm_apply _
  let g' : A →ₗ[A] D.Lx x :=
    { toFun := g'k
      map_add' := fun a b ↦ by
        apply hΦ
        rw [map_add, hg', hg', hg']
        ext t
        simp only [LinearMap.comp_apply, LinearMap.add_apply]
        rw [← map_add]
        congr 1
        exact Subtype.ext (mul_add _ _ _)
      map_smul' := fun b a ↦ by
        apply hΦ
        ext t
        rw [RingHom.id_apply, hΦa, hg', hg']
        simp only [LinearMap.comp_apply]
        congr 1
        exact Subtype.ext (by simp [rmul, smul_eq_mul, mul_assoc]) }
  refine ⟨g', fun l hl ↦ ?_⟩
  apply hΦ
  ext t
  show Φ (g'k l) t = _
  rw [hg']
  have htl : t.1 * l ∈ I := I.mul_mem_left _ hl
  have hW : (rmul l t) ∈ W := htl
  have h1 : φ (rmul l t) = ψ ⟨rmul l t, hW⟩ := by
    rw [← hφ]; rfl
  rw [LinearMap.comp_apply, h1]
  show Φ (g ⟨t.1 * l, htl⟩) ⟨D.e y, hey⟩ = Φ (g ⟨l, hl⟩) t
  have h2 : (⟨t.1 * l, htl⟩ : I) = t.1 • (⟨l, hl⟩ : I) := rfl
  rw [h2, map_smul, hΦa]
  congr 1
  exact Subtype.ext (show D.e y * t.1 = t.1 from t.2)

end PathData

end BrickAccessibility
