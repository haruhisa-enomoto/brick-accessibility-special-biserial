module

public import BrickAccessibility.Section4.ExtBound

/-!
# An upper bound for `Ext¹(S_v, M)`

The mirror of `finrank_ext1_simple_le`: a normalized derivation
`B → Hom_k(S_v, M)` is determined by the vectors `χ_b = δ(α_b)(s₀)` for the arrows
`b` starting at `v`; each `χ_b` lies in `e_{tgt b} M` and is killed by every
forbidden successor of `b`. Inner derivations of vectors `u ∈ e_v M` give
`(α_b u)_b`. Hence `dim Ext¹(S_v, M) + dim E₀' ≤ Σ_b dim Y_b + dim K₀'`
(`finrank_ext1_simple_left_le`), where `E₀' = e_v M`, `K₀' ⊆ E₀'` is killed by the
arrows out of `v`, and `Y_b` is the space above.
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
variable (M : Type u) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- Vectors supported at `v`. -/
def E0' (v : D.Q.V) : Submodule k M where
  carrier := {u | D.e v • u = u}
  add_mem' {a b} ha hb := by
    show D.e v • (a + b) = a + b
    rw [smul_add, show D.e v • a = a from ha, show D.e v • b = b from hb]
  zero_mem' := by simp
  smul_mem' c u hu := by
    show D.e v • (c • u) = c • u
    rw [smul_comm, show D.e v • u = u from hu]

/-- Vectors supported at `v` killed by the arrows out of `v`. -/
def K0' (v : D.Q.V) : Submodule k M where
  carrier := {u | D.e v • u = u ∧ ∀ b, D.Q.src b = v → D.α b • u = 0}
  add_mem' hu hu' := ⟨by simp [smul_add, hu.1, hu'.1], fun b hb ↦ by simp [smul_add, hu.2 b hb, hu'.2 b hb]⟩
  zero_mem' := ⟨by simp, fun b _ ↦ by simp⟩
  smul_mem' c u hu := ⟨by simp [smul_comm (D.e v) c u, hu.1],
    fun b hb ↦ by simp [smul_comm (D.α b) c u, hu.2 b hb]⟩

/-- The space containing `δ(α_b)(s₀)` for a normalized derivation. -/
def Yb (b : D.Q.A) : Submodule k M where
  carrier := {χ | D.e (D.Q.tgt b) • χ = χ ∧ ∀ c, D.toPathData.Forbidden b c → D.α c • χ = 0}
  add_mem' hu hu' := ⟨by simp [smul_add, hu.1, hu'.1], fun c hc ↦ by simp [smul_add, hu.2 c hc, hu'.2 c hc]⟩
  zero_mem' := ⟨by simp, fun c _ ↦ by simp⟩
  smul_mem' a u hu := ⟨by simp [smul_comm (D.e _) a u, hu.1],
    fun c hc ↦ by simp [smul_comm (D.α c) a u, hu.2 c hc]⟩

theorem α_mul_α_of_forbidden {a b : D.Q.A} (hab : D.toPathData.Forbidden a b) :
    D.α b * D.α a = 0 := by
  have h := hab.2
  have e1 : D.toPathData.pval (D.Q.src a) [a, b] = D.toPathData.α b * D.toPathData.α a := by
    rw [show [a, b] = [a] ++ [b] from rfl, D.toPathData.pval_append,
      D.toPathData.pval_single_src, D.toPathData.pval_single]
    simp only [Statement.FinQuiver.pend]
    rw [mul_assoc, D.toPathData.e_mul_α]
  rw [e1] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **Upper bound for `Ext¹(S_v, M)`.** -/
theorem finrank_ext1_simple_left_le [FiniteDimensional k B] [FiniteDimensional k M]
    (v : D.Q.V) :
    finrank k (Ext1 k B (D.simple v) M) + finrank k (D.E0' M v) ≤
      ∑ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb M b.1) + finrank k (D.K0' M v) := by
  classical
  set S := D.simple v
  set Z := Ext1.cocycles k B S M
  set Bd := Ext1.coboundaries k B S M
  have hL : ∀ δ ∈ Z, ∀ a b s, δ (a * b) s = a • δ b s + δ a (b • s) := fun δ hδ ↦ hδ
  let Nz : Submodule k (B →ₗ[k] S →ₗ[k] M) :=
    { carrier := {δ | ∀ w, δ (D.e w) = 0}
      add_mem' := fun hδ hδ' w ↦ by simp [hδ w, hδ' w]
      zero_mem' := fun w ↦ by simp
      smul_mem' := fun c δ hδ w ↦ by simp [hδ w] }
  let N := Z ⊓ Nz
  have hExt : Ext1 k B S M = N.map Bd.mkQ := by
    apply le_antisymm
    · rintro _ ⟨δ, hδ, rfl⟩
      obtain ⟨φ, hφ⟩ := D.exists_normalized δ hδ
      refine ⟨δ - Ext1.inner k B S M φ, ⟨Z.sub_mem hδ (Ext1.range_inner_le k B S M ⟨φ, rfl⟩),
        hφ⟩, ?_⟩
      rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero Bd).mpr ⟨φ, rfl⟩, sub_zero]
    · exact Submodule.map_mono inf_le_left
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := k) (V := N)
    (V₂ := (B →ₗ[k] S →ₗ[k] M) ⧸ Bd) (Bd.mkQ.domRestrict N)
  rw [LinearMap.range_domRestrict, ← hExt, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hrn
  have hαe : ∀ δ ∈ N, ∀ b s, D.e (D.Q.tgt b) • δ (D.α b) s = δ (D.α b) s := by
    intro δ hδ b s
    have := hL δ hδ.1 (D.e (D.Q.tgt b)) (D.α b) s
    rw [D.toPathData.e_mul_α, hδ.2, LinearMap.zero_apply, add_zero] at this
    exact this.symm
  have hαα : ∀ δ ∈ N, ∀ b c, D.toPathData.Forbidden b c → ∀ s, D.α c • δ (D.α b) s = 0 := by
    intro δ hδ b c hbc s
    have := hL δ hδ.1 (D.α c) (D.α b) s
    rw [D.α_mul_α_of_forbidden hbc, map_zero, LinearMap.zero_apply, D.α_smul_simple,
      map_zero, add_zero] at this
    exact this.symm
  have hαv : ∀ δ ∈ N, ∀ b, D.Q.src b ≠ v → δ (D.α b) = 0 := by
    intro δ hδ b hb
    ext s
    have := hL δ hδ.1 (D.α b) (D.e (D.Q.src b)) s
    rw [D.toPathData.α_mul_e, hδ.2, LinearMap.zero_apply, smul_zero, zero_add,
      D.e_smul_simple, if_neg hb, map_zero] at this
    exact this
  let Θ : N →ₗ[k] ((b : {b : D.Q.A // D.Q.src b = v}) → D.Yb M b.1) :=
    { toFun := fun δ b ↦ ⟨δ.1 (D.α b.1) (D.s0 v), hαe δ.1 δ.2 b.1 _,
        fun c hc ↦ hαα δ.1 δ.2 b.1 c hc _⟩
      map_add' := fun δ δ' ↦ by
        funext b; apply Subtype.ext
        show (δ.1 + δ'.1) (D.α b.1) (D.s0 v) = δ.1 (D.α b.1) (D.s0 v) + δ'.1 (D.α b.1) (D.s0 v)
        rw [LinearMap.add_apply, LinearMap.add_apply]
      map_smul' := fun c δ ↦ by
        funext b; apply Subtype.ext
        show (c • δ.1) (D.α b.1) (D.s0 v) = c • δ.1 (D.α b.1) (D.s0 v)
        rw [LinearMap.smul_apply, LinearMap.smul_apply] }
  have hΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro δ hδ
    apply Subtype.ext
    refine D.eq_zero_of_normalized δ.1 δ.2.1 δ.2.2 fun b ↦ ?_
    by_cases hb : D.Q.src b = v
    · ext s
      have := congrArg Subtype.val (congrFun hδ ⟨b, hb⟩)
      change δ.1 (D.α b) (D.s0 v) = 0 at this
      rw [D.eq_coord_smul v s, map_smul, this, smul_zero]
      rfl
    · exact hαv δ.1 δ.2 b hb
  have hN : finrank k N ≤ ∑ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb M b.1) := by
    rw [← Module.finrank_pi_fintype]
    exact LinearMap.finrank_le_finrank_of_injective hΘ
  let L : D.E0' M v → (S →ₗ[k] M) := fun u ↦ LinearMap.smulRight (D.coord v) u.1
  have hinnerN : ∀ u : D.E0' M v, Ext1.inner k B S M (L u) ∈ N := by
    intro u
    refine ⟨Ext1.range_inner_le k B S M ⟨_, rfl⟩, fun w ↦ ?_⟩
    ext s
    simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, LinearMap.zero_apply]
    rw [D.e_smul_simple, smul_comm]
    have hu : D.e w • u.1 = if w = v then u.1 else 0 := by
      rw [← u.2, ← mul_smul, D.toPathData.e_mul_e]
      by_cases h : w = v
      · subst h; simp [u.2]
      · simp [h, Ne.symm h]
    rw [hu]
    split_ifs <;> simp
  let ι : D.E0' M v →ₗ[k] N :=
    { toFun := fun u ↦ ⟨Ext1.inner k B S M (L u), hinnerN u⟩
      map_add' := fun u u' ↦ by
        apply Subtype.ext
        show Ext1.inner k B S M (L (u + u')) = Ext1.inner k B S M (L u) + Ext1.inner k B S M (L u')
        rw [← map_add]; congr 1; ext s; simp [L, smul_add]
      map_smul' := fun c u ↦ by
        apply Subtype.ext
        show Ext1.inner k B S M (L (c • u)) = c • Ext1.inner k B S M (L u)
        rw [← map_smul]; congr 1; ext s; simp [L, smul_comm c] }
  have hker : finrank k (LinearMap.ker ι) ≤ finrank k (D.K0' M v) := by
    have hmem : ∀ u ∈ LinearMap.ker ι, (u : M) ∈ D.K0' M v := by
      intro u hu
      refine ⟨u.2, fun b hb ↦ ?_⟩
      have h1 := congrArg (fun x : N ↦ (x.1 (D.α b) (D.s0 v))) hu
      change Ext1.inner k B S M (L u) (D.α b) (D.s0 v) = 0 at h1
      simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, D.α_smul_simple,
        map_zero, zero_smul, sub_zero] at h1
      rw [D.coord_s0, one_smul] at h1
      exact h1
    let j : LinearMap.ker ι →ₗ[k] D.K0' M v :=
      { toFun := fun u ↦ ⟨u.1.1, hmem u.1 u.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := j) fun u u' h ↦ ?_
    have h' := congrArg (fun x : D.K0' M v ↦ (x : M)) h
    exact Subtype.ext (Subtype.ext h')
  have hι := LinearMap.finrank_range_add_finrank_ker (K := k) (V := D.E0' M v) (V₂ := N) ι
  have hrange : finrank k (LinearMap.range ι) ≤ finrank k (Bd.comap N.subtype) := by
    refine Submodule.finrank_mono ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  have e1 : finrank k (Ext1 k B (D.simple v) M) + finrank k (Bd.comap N.subtype) =
      finrank k N := hrn
  have e2 : finrank k (LinearMap.range ι) + finrank k (LinearMap.ker ι) =
      finrank k (D.E0' M v) := hι
  have e5 : finrank k N ≤ ∑ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb M b.1) := hN
  omega

end MonomialData

end BrickAccessibility
