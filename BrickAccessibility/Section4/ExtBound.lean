module

public import BrickAccessibility.Section4.Normalize

/-!
# An upper bound for `Ext¹(M, S_v)`

For monomial data and any finite-dimensional module `M`, a normalized derivation
`B → Hom_k(M, S_v)` is determined by the functionals `ψ_b = δ(α_b)` for the
arrows `b` ending at `v`; each `ψ_b` is supported on `e_{src b} M` and vanishes
on the image of every forbidden predecessor of `b`. Inner derivations of
functionals supported at `v` give the vectors `(φ ∘ α_b)_b`. Hence
`dim Ext¹(M, S_v) + dim E₀ ≤ Σ_b dim Z_b + dim K₀`
(`finrank_ext1_simple_le`), where `E₀` is the space of functionals supported at
`v`, `K₀ ⊆ E₀` those vanishing on all `α_b M`, and `Z_b` the space above.
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

section SimpleFacts

theorem e_smul_simple (v w : D.Q.V) (s : D.simple v) :
    D.e w • s = if w = v then s else 0 := by
  rw [Rep.e_smul]
  funext i
  change (if v = w then s i else 0) = _
  by_cases h : w = v
  · subst h; simp
  · simp only [h, Ne.symm h, if_false]; rfl

theorem α_smul_simple (v : D.Q.V) (a : D.Q.A) (s : D.simple v) : D.α a • s = 0 := by
  rw [Rep.α_smul]
  funext i
  show (D.simpleCQ v).αMap a s i = (0 : Unit → k) i
  simp [CoeffQuiver.αMap, simpleCQ]
  rfl

/-- The coordinate of `S_v`. -/
def coord (v : D.Q.V) : D.simple v →ₗ[k] k := LinearMap.proj (R := k) (φ := fun _ : Unit ↦ k) ()

/-- The basis vector of `S_v`. -/
def s0 (v : D.Q.V) : D.simple v := fun _ ↦ (1 : k)

theorem coord_s0 (v : D.Q.V) : D.coord v (D.s0 v) = 1 := rfl

theorem eq_coord_smul (v : D.Q.V) (s : D.simple v) : s = D.coord v s • D.s0 v := by
  funext i; cases i
  change s () = (s ()) • (1 : k)
  simp

end SimpleFacts

variable (M : Type u) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- Linear functionals, as a subspace of all functions `M → k`. (Subspaces of
`M →ₗ[k] k` hit an instance mismatch at this Mathlib version.) -/
def linFun : Submodule k (M → k) where
  carrier := {φ | (∀ x y, φ (x + y) = φ x + φ y) ∧ ∀ (c : k) x, φ (c • x) = c * φ x}
  add_mem' hφ hψ := ⟨fun x y ↦ by simp [hφ.1, hψ.1]; ring, fun c x ↦ by simp [hφ.2, hψ.2]; ring⟩
  zero_mem' := ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩
  smul_mem' c φ hφ := ⟨fun x y ↦ by simp [hφ.1]; ring, fun c' x ↦ by simp [hφ.2]; ring⟩

theorem linFun_eq_range : linFun (k := k) M = LinearMap.range (LinearMap.ltoFun k M k k) := by
  ext φ
  constructor
  · intro hφ
    exact ⟨⟨⟨φ, hφ.1⟩, fun c x ↦ by simpa using hφ.2 c x⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩

instance [FiniteDimensional k M] : FiniteDimensional k (linFun (k := k) M) := by
  rw [linFun_eq_range]
  infer_instance

/-- The linear map of a functional in `linFun`. -/
def toLin {M : Type u} [AddCommGroup M] [Module k M] (φ : M → k) (hφ : φ ∈ linFun (k := k) M) :
    M →ₗ[k] k where
  toFun := φ
  map_add' := hφ.1
  map_smul' := hφ.2

/-- Functionals supported at `v`. -/
def E0 (v : D.Q.V) : Submodule k (M → k) where
  carrier := {φ | φ ∈ linFun (k := k) M ∧ ∀ m, φ (D.e v • m) = φ m}
  add_mem' hφ hψ := ⟨(linFun M).add_mem hφ.1 hψ.1, fun m ↦ by simp [hφ.2 m, hψ.2 m]⟩
  zero_mem' := ⟨(linFun M).zero_mem, fun m ↦ by simp⟩
  smul_mem' c φ hφ := ⟨(linFun M).smul_mem c hφ.1, fun m ↦ by simp [hφ.2 m]⟩

/-- Functionals supported at `v` vanishing on the images of the arrows into `v`. -/
def K0 (v : D.Q.V) : Submodule k (M → k) where
  carrier := {φ | φ ∈ linFun (k := k) M ∧ (∀ m, φ (D.e v • m) = φ m) ∧
    ∀ b, D.Q.tgt b = v → ∀ m, φ (D.α b • m) = 0}
  add_mem' hφ hψ := ⟨(linFun M).add_mem hφ.1 hψ.1, fun m ↦ by simp [hφ.2.1 m, hψ.2.1 m],
    fun b hb m ↦ by simp [hφ.2.2 b hb m, hψ.2.2 b hb m]⟩
  zero_mem' := ⟨(linFun M).zero_mem, fun m ↦ by simp, fun b _ m ↦ by simp⟩
  smul_mem' c φ hφ := ⟨(linFun M).smul_mem c hφ.1, fun m ↦ by simp [hφ.2.1 m],
    fun b hb m ↦ by simp [hφ.2.2 b hb m]⟩

/-- The space containing `δ(α_b)` for a normalized derivation. -/
def Zb (b : D.Q.A) : Submodule k (M → k) where
  carrier := {ψ | ψ ∈ linFun (k := k) M ∧ (∀ m, ψ (D.e (D.Q.src b) • m) = ψ m) ∧
    ∀ a, D.toPathData.Forbidden a b → ∀ m, ψ (D.α a • m) = 0}
  add_mem' hφ hψ := ⟨(linFun M).add_mem hφ.1 hψ.1, fun m ↦ by simp [hφ.2.1 m, hψ.2.1 m],
    fun a ha m ↦ by simp [hφ.2.2 a ha m, hψ.2.2 a ha m]⟩
  zero_mem' := ⟨(linFun M).zero_mem, fun m ↦ by simp, fun a _ m ↦ by simp⟩
  smul_mem' c φ hφ := ⟨(linFun M).smul_mem c hφ.1, fun m ↦ by simp [hφ.2.1 m],
    fun a ha m ↦ by simp [hφ.2.2 a ha m]⟩

instance [FiniteDimensional k M] (v : D.Q.V) : FiniteDimensional k (D.E0 M v) :=
  Submodule.finiteDimensional_of_le (fun _ h ↦ h.1 : D.E0 M v ≤ linFun M)
instance [FiniteDimensional k M] (v : D.Q.V) : FiniteDimensional k (D.K0 M v) :=
  Submodule.finiteDimensional_of_le (fun _ h ↦ h.1 : D.K0 M v ≤ linFun M)
instance [FiniteDimensional k M] (b : D.Q.A) : FiniteDimensional k (D.Zb M b) :=
  Submodule.finiteDimensional_of_le (fun _ h ↦ h.1 : D.Zb M b ≤ linFun M)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **Upper bound for `Ext¹(M, S_v)`.** -/
theorem finrank_ext1_simple_le [FiniteDimensional k B] [FiniteDimensional k M] (v : D.Q.V) :
    finrank k (Ext1 k B M (D.simple v)) + finrank k (D.E0 M v) ≤
      ∑ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb M b.1) + finrank k (D.K0 M v) := by
  classical
  set S := D.simple v
  set Z := Ext1.cocycles k B M S
  set Bd := Ext1.coboundaries k B M S
  have hL : ∀ δ ∈ Z, ∀ a b m, δ (a * b) m = a • δ b m + δ a (b • m) := fun δ hδ ↦ hδ
  let Nz : Submodule k (B →ₗ[k] M →ₗ[k] S) :=
    { carrier := {δ | ∀ w, δ (D.e w) = 0}
      add_mem' := fun hδ hδ' w ↦ by simp [hδ w, hδ' w]
      zero_mem' := fun w ↦ by simp
      smul_mem' := fun c δ hδ w ↦ by simp [hδ w] }
  let N := Z ⊓ Nz
  have hExt : Ext1 k B M S = N.map Bd.mkQ := by
    apply le_antisymm
    · rintro _ ⟨δ, hδ, rfl⟩
      obtain ⟨φ, hφ⟩ := D.exists_normalized δ hδ
      refine ⟨δ - Ext1.inner k B M S φ, ⟨Z.sub_mem hδ (Ext1.range_inner_le k B M S ⟨φ, rfl⟩),
        hφ⟩, ?_⟩
      rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero Bd).mpr ⟨φ, rfl⟩, sub_zero]
    · exact Submodule.map_mono inf_le_left
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := k) (V := N)
    (V₂ := (B →ₗ[k] M →ₗ[k] S) ⧸ Bd) (Bd.mkQ.domRestrict N)
  rw [LinearMap.range_domRestrict, ← hExt, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hrn
  have hαe : ∀ δ ∈ N, ∀ b m, δ (D.α b) (D.e (D.Q.src b) • m) = δ (D.α b) m := by
    intro δ hδ b m
    have := hL δ hδ.1 (D.α b) (D.e (D.Q.src b)) m
    rw [D.toPathData.α_mul_e, hδ.2, LinearMap.zero_apply, smul_zero, zero_add] at this
    exact this.symm
  have hαα : ∀ δ ∈ N, ∀ a b, D.toPathData.Forbidden a b → ∀ m, δ (D.α b) (D.α a • m) = 0 := by
    intro δ hδ a b hab m
    have h0 : D.α b * D.α a = 0 := by
      have h := hab.2
      have e1 : D.toPathData.pval (D.Q.src a) [a, b] = D.toPathData.α b * D.toPathData.α a := by
        rw [show [a, b] = [a] ++ [b] from rfl, D.toPathData.pval_append,
          D.toPathData.pval_single_src, D.toPathData.pval_single]
        simp only [Statement.FinQuiver.pend]
        rw [mul_assoc, D.toPathData.e_mul_α]
      rw [e1] at h
      exact h
    have := hL δ hδ.1 (D.α b) (D.α a) m
    rw [h0, map_zero, LinearMap.zero_apply, D.α_smul_simple, zero_add] at this
    exact this.symm
  have hαv : ∀ δ ∈ N, ∀ b, D.Q.tgt b ≠ v → δ (D.α b) = 0 := by
    intro δ hδ b hb
    ext m
    have := hL δ hδ.1 (D.e (D.Q.tgt b)) (D.α b) m
    rw [D.toPathData.e_mul_α, hδ.2, LinearMap.zero_apply, add_zero, D.e_smul_simple,
      if_neg hb] at this
    exact this
  -- the injection into the product of the spaces `Z_b`
  let Θ : N →ₗ[k] ((b : {b : D.Q.A // D.Q.tgt b = v}) → D.Zb M b.1) :=
    { toFun := fun δ b ↦ ⟨fun m ↦ D.coord v (δ.1 (D.α b.1) m),
        ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩,
        fun m ↦ by
          show D.coord v (δ.1 (D.α b.1) (D.e _ • m)) = D.coord v (δ.1 (D.α b.1) m)
          rw [hαe δ.1 δ.2],
        fun a hab m ↦ by
          show D.coord v (δ.1 (D.α b.1) (D.α a • m)) = 0
          rw [hαα δ.1 δ.2 a b.1 hab, map_zero]⟩
      map_add' := fun δ δ' ↦ by
        funext b; apply Subtype.ext; funext m
        show D.coord v ((δ.1 + δ'.1) (D.α b.1) m) =
          D.coord v (δ.1 (D.α b.1) m) + D.coord v (δ'.1 (D.α b.1) m)
        rw [LinearMap.add_apply, LinearMap.add_apply, map_add]
      map_smul' := fun c δ ↦ by
        funext b; apply Subtype.ext; funext m
        show D.coord v ((c • δ.1) (D.α b.1) m) = c * D.coord v (δ.1 (D.α b.1) m)
        rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, smul_eq_mul] }
  have hΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro δ hδ
    apply Subtype.ext
    refine D.eq_zero_of_normalized δ.1 δ.2.1 δ.2.2 fun b ↦ ?_
    by_cases hb : D.Q.tgt b = v
    · ext m
      have := congrFun (congrArg Subtype.val (congrFun hδ ⟨b, hb⟩)) m
      change D.coord v (δ.1 (D.α b) m) = 0 at this
      rw [D.eq_coord_smul v (δ.1 (D.α b) m), this, zero_smul]
      rfl
    · exact hαv δ.1 δ.2 b hb
  have hN : finrank k N ≤ ∑ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb M b.1) := by
    rw [← Module.finrank_pi_fintype]
    exact LinearMap.finrank_le_finrank_of_injective hΘ
  -- inner derivations of functionals supported at `v`
  let L : D.E0 M v → (M →ₗ[k] S) := fun φ ↦ LinearMap.smulRight (toLin φ.1 φ.2.1) (D.s0 v)
  have hinnerN : ∀ φ : D.E0 M v, Ext1.inner k B M S (L φ) ∈ N := by
    intro φ
    refine ⟨Ext1.range_inner_le k B M S ⟨_, rfl⟩, fun w ↦ ?_⟩
    ext m
    simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, LinearMap.zero_apply, toLin,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_comm, D.e_smul_simple]
    have hφw : φ.1 (D.e w • m) = if w = v then φ.1 m else 0 := by
      rw [← φ.2.2 (D.e w • m), ← mul_smul, D.toPathData.e_mul_e]
      by_cases h : w = v
      · subst h; simp [φ.2.2 m]
      · have h0 : φ.1 0 = 0 := (toLin φ.1 φ.2.1).map_zero
        simp [h, Ne.symm h, h0]
    rw [hφw]
    split_ifs <;> simp
  have hL_add : ∀ φ ψ : D.E0 M v, L (φ + ψ) = L φ + L ψ := by
    intro φ ψ; ext m; simp [L, toLin, add_smul]
  have hL_smul : ∀ (c : k) (φ : D.E0 M v), L (c • φ) = c • L φ := by
    intro c φ; ext m; simp [L, toLin, smul_smul]
  let ι : D.E0 M v →ₗ[k] N :=
    { toFun := fun φ ↦ ⟨Ext1.inner k B M S (L φ), hinnerN φ⟩
      map_add' := fun φ ψ ↦ by
        apply Subtype.ext
        show Ext1.inner k B M S (L (φ + ψ)) = Ext1.inner k B M S (L φ) + Ext1.inner k B M S (L ψ)
        rw [hL_add, map_add]
      map_smul' := fun c φ ↦ by
        apply Subtype.ext
        show Ext1.inner k B M S (L (c • φ)) = c • Ext1.inner k B M S (L φ)
        rw [hL_smul, map_smul] }
  have hker : finrank k (LinearMap.ker ι) ≤ finrank k (D.K0 M v) := by
    have hmem : ∀ φ ∈ LinearMap.ker ι, (φ : M → k) ∈ D.K0 M v := by
      intro φ hφ
      refine ⟨φ.2.1, φ.2.2, fun b hb m ↦ ?_⟩
      have h1 := congrArg (fun x : N ↦ (x.1 (D.α b) m)) hφ
      change Ext1.inner k B M S (L φ) (D.α b) m = 0 at h1
      simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, D.α_smul_simple, zero_sub,
        toLin, LinearMap.coe_mk, AddHom.coe_mk] at h1
      have h2 := congrArg (D.coord v) h1
      rw [map_neg, map_smul, D.coord_s0, map_zero, smul_eq_mul, mul_one] at h2
      exact neg_eq_zero.mp h2
    let j : LinearMap.ker ι →ₗ[k] D.K0 M v :=
      { toFun := fun φ ↦ ⟨φ.1.1, hmem φ.1 φ.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := j) fun φ ψ h ↦ ?_
    have h' := congrArg (fun x : D.K0 M v ↦ (x : M → k)) h
    exact Subtype.ext (Subtype.ext h')
  have hι := LinearMap.finrank_range_add_finrank_ker (K := k) (V := D.E0 M v) (V₂ := N) ι
  have hrange : finrank k (LinearMap.range ι) ≤ finrank k (Bd.comap N.subtype) := by
    refine Submodule.finrank_mono ?_
    rintro _ ⟨φ, rfl⟩
    exact ⟨_, rfl⟩
  have e1 : finrank k (Ext1 k B M (D.simple v)) + finrank k (Bd.comap N.subtype) =
      finrank k N := hrn
  have e2 : finrank k (LinearMap.range ι) + finrank k (LinearMap.ker ι) =
      finrank k (D.E0 M v) := hι
  have e3 : finrank k (LinearMap.ker ι) ≤ finrank k (D.K0 M v) := hker
  have e4 : finrank k (LinearMap.range ι) ≤ finrank k (Bd.comap N.subtype) := hrange
  have e5 : finrank k N ≤ ∑ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb M b.1) := hN
  omega

end MonomialData

end BrickAccessibility
