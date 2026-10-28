module

public import BrickAccessibility.Section4.ExtBoundDual

/-!
# Dimension counts for coefficient-quiver modules

For a coefficient quiver with nonzero coefficients and injective arrow moves (for
instance a string module), the spaces of `ExtBound` and `ExtBoundDual` are
coordinate subspaces, so their dimensions are numbers of positions:

* `E₀`, `E₀'`: positions over `v`;
* `K₀`: positions over `v` with no incoming edge (the top at `v`);
* `K₀'`: positions over `v` with no outgoing edge (the socle at `v`);
* `Z_b`: positions over `src b` with no incoming edge labelled by a forbidden
  predecessor of `b`;
* `Y_b`: positions over `tgt b` with no outgoing edge labelled by a forbidden
  successor of `b`.

Also `dim Hom(S_v, M) = dim K₀'` and `dim Hom(M, S_v) = dim K₀` for every module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- Functions vanishing outside a predicate. -/
def coordSub {P : Type} (T : P → Prop) : Submodule k (P → k) where
  carrier := {f | ∀ p, ¬ T p → f p = 0}
  add_mem' hf hg p hp := by simp [hf p hp, hg p hp]
  zero_mem' p _ := rfl
  smul_mem' c f hf p hp := by simp [hf p hp]

theorem finrank_coordSub {P : Type} [Fintype P] (T : P → Prop) [DecidablePred T] :
    finrank k (coordSub (k := k) T) = Fintype.card {p // T p} := by
  classical
  let e : coordSub (k := k) T ≃ₗ[k] ({p // T p} → k) :=
    { toFun := fun f p ↦ f.1 p
      invFun := fun g ↦ ⟨fun p ↦ if h : T p then g ⟨p, h⟩ else 0, fun p hp ↦ by simp [hp]⟩
      left_inv := fun f ↦ by
        apply Subtype.ext; funext p
        by_cases h : T p
        · simp [h]
        · simp [h, f.2 p h]
      right_inv := fun g ↦ by funext p; simp [p.2]
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]

namespace MonomialData

variable (D : MonomialData k B)

section Hom

variable (M : Type u) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- `Hom(S_v, M)` is the socle of `M` at `v`. -/
theorem finrank_hom_simple [FiniteDimensional k M] (v : D.Q.V) :
    finrank k (D.simple v →ₗ[B] M) = finrank k (D.K0' M v) := by
  classical
  have hs0e : D.e v • D.s0 v = D.s0 v := by rw [D.e_smul_simple, if_pos rfl]
  have hu : ∀ u ∈ D.K0' M v, ∀ w, D.e w • u = if w = v then u else 0 := by
    intro u hu w
    rw [← hu.1, ← mul_smul, D.toPathData.e_mul_e]
    by_cases h : w = v
    · subst h; simp [hu.1]
    · simp [h, Ne.symm h]
  have huα : ∀ u ∈ D.K0' M v, ∀ a, D.α a • u = 0 := by
    intro u hu' a
    by_cases h : D.Q.src a = v
    · exact hu'.2 a h
    · have key : D.α a = D.α a * D.e (D.Q.src a) := (D.toPathData.α_mul_e a).symm
      rw [key, mul_smul, hu u hu', if_neg h, smul_zero]
  let g : D.K0' M v → (D.simple v →ₗ[B] M) := fun u ↦
    D.linearMap_of_commute (LinearMap.smulRight (D.coord v) u.1)
      (fun w s ↦ by
        simp only [LinearMap.smulRight_apply]
        rw [D.e_smul_simple, smul_comm, hu u.1 u.2]
        split_ifs <;> simp)
      (fun a s ↦ by
        simp only [LinearMap.smulRight_apply]
        rw [D.α_smul_simple, map_zero, zero_smul, smul_comm, huα u.1 u.2, smul_zero])
  let e : (D.simple v →ₗ[B] M) ≃ₗ[k] D.K0' M v :=
    { toFun := fun f ↦ ⟨f (D.s0 v), by rw [← map_smul, hs0e],
        fun b _ ↦ by rw [← map_smul, D.α_smul_simple, map_zero]⟩
      invFun := g
      left_inv := fun f ↦ by
        ext s
        simp only [g, linearMap_of_commute_apply, LinearMap.smulRight_apply]
        conv_rhs => rw [D.eq_coord_smul v s]
        rw [LinearMap.map_smul_of_tower]
      right_inv := fun u ↦ by
        apply Subtype.ext
        simp [g, D.coord_s0]
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e.finrank_eq

/-- `Hom(M, S_v)` is the top of `M` at `v`. -/
theorem finrank_hom_to_simple [FiniteDimensional k M] (v : D.Q.V) :
    finrank k (M →ₗ[B] D.simple v) = finrank k (D.K0 M v) := by
  classical
  have hφe : ∀ φ ∈ D.K0 M v, ∀ w m, φ (D.e w • m) = if w = v then φ m else 0 := by
    intro φ hφ w m
    rw [← hφ.2.1 (D.e w • m), ← mul_smul, D.toPathData.e_mul_e]
    by_cases h : w = v
    · subst h; simp [hφ.2.1 m]
    · have h0 : φ 0 = 0 := (toLin φ hφ.1).map_zero
      simp [h, Ne.symm h, h0]
  have hφα : ∀ φ ∈ D.K0 M v, ∀ a m, φ (D.α a • m) = 0 := by
    intro φ hφ a m
    by_cases h : D.Q.tgt a = v
    · exact hφ.2.2 a h m
    · have key : D.α a = D.e (D.Q.tgt a) * D.α a := (D.toPathData.e_mul_α a).symm
      rw [key, mul_smul, hφe φ hφ, if_neg h]
  let g : D.K0 M v → (M →ₗ[B] D.simple v) := fun φ ↦
    D.linearMap_of_commute (LinearMap.smulRight (toLin φ.1 φ.2.1) (D.s0 v))
      (fun w m ↦ by
        simp only [LinearMap.smulRight_apply, toLin, LinearMap.coe_mk, AddHom.coe_mk]
        rw [hφe φ.1 φ.2, smul_comm, D.e_smul_simple]
        split_ifs <;> simp)
      (fun a m ↦ by
        simp only [LinearMap.smulRight_apply, toLin, LinearMap.coe_mk, AddHom.coe_mk]
        rw [hφα φ.1 φ.2, zero_smul, smul_comm, D.α_smul_simple, smul_zero])
  let e : (M →ₗ[B] D.simple v) ≃ₗ[k] D.K0 M v :=
    { toFun := fun f ↦ ⟨fun m ↦ D.coord v (f m),
        ⟨fun x y ↦ by simp, fun c x ↦ by simp [LinearMap.map_smul_of_tower]⟩,
        fun m ↦ by simp only; rw [map_smul, D.e_smul_simple, if_pos rfl],
        fun b _ m ↦ by simp only; rw [map_smul, D.α_smul_simple, map_zero]⟩
      invFun := g
      left_inv := fun f ↦ by
        ext m
        simp only [g, linearMap_of_commute_apply, LinearMap.smulRight_apply, toLin,
          LinearMap.coe_mk, AddHom.coe_mk]
        exact (D.eq_coord_smul v (f m)).symm
      right_inv := fun φ ↦ by
        apply Subtype.ext
        funext m
        simp [g, toLin, D.coord_s0]
      map_add' := fun _ _ ↦ by apply Subtype.ext; funext m; simp
      map_smul' := fun _ _ ↦ by apply Subtype.ext; funext m; simp }
  exact e.finrank_eq

end Hom

/-- A linear functional on `P → k` is determined by its values on the basis. -/
theorem linFun_expand {P : Type} [Fintype P] [DecidableEq P] (φ : (P → k) → k)
    (hφ : φ ∈ linFun (k := k) (P → k)) (f : P → k) :
    φ f = ∑ p, f p * φ (Pi.single p 1) := by
  have := map_sum (toLin φ hφ) (fun p ↦ f p • Pi.single p (1 : k)) Finset.univ
  simp only [toLin, LinearMap.coe_mk, AddHom.coe_mk] at this
  conv_lhs => rw [show f = ∑ p, f p • Pi.single p (1 : k) by
    funext q; simp [Finset.sum_apply, Pi.single_apply]]
  rw [this]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [hφ.2]

/-- A subspace of `P → k` cut out by vanishing outside `T`. -/
theorem finrank_eq_card_of_mem_iff {P : Type} [Fintype P] (S : Submodule k (P → k))
    (T : P → Prop) [DecidablePred T] (h : ∀ f, f ∈ S ↔ ∀ p, ¬ T p → f p = 0) :
    finrank k S = Fintype.card {p // T p} := by
  have : S = coordSub T := by ext f; exact h f
  rw [this, finrank_coordSub]

/-- A space of functionals on `P → k` cut out by vanishing of the coordinates
outside `T`. -/
theorem finrank_eq_card_of_mem_iff_dual {P : Type} [Fintype P] [DecidableEq P]
    (S : Submodule k ((P → k) → k)) (hS : S ≤ linFun (k := k) (P → k))
    (T : P → Prop) [DecidablePred T]
    (h : ∀ φ ∈ linFun (k := k) (P → k), φ ∈ S ↔ ∀ p, ¬ T p → φ (Pi.single p 1) = 0) :
    finrank k S = Fintype.card {p // T p} := by
  classical
  -- coordinates of a linear functional
  have hexp : ∀ φ ∈ linFun (k := k) (P → k), ∀ f : P → k, φ f = ∑ p, f p * φ (Pi.single p 1) := by
    intro φ hφ f
    have := map_sum (toLin φ hφ) (fun p ↦ f p • Pi.single p (1 : k)) Finset.univ
    simp only [toLin, LinearMap.coe_mk, AddHom.coe_mk] at this
    conv_lhs => rw [show f = ∑ p, f p • Pi.single p (1 : k) by
      funext q; simp [Finset.sum_apply, Pi.single_apply]]
    rw [this]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [hφ.2]
  let e : S ≃ₗ[k] coordSub (k := k) T :=
    { toFun := fun φ ↦ ⟨fun p ↦ φ.1 (Pi.single p 1), (h φ.1 (hS φ.2)).mp φ.2⟩
      invFun := fun c ↦ ⟨fun f ↦ ∑ p, f p * c.1 p, by
        refine (h _ ⟨fun x y ↦ ?_, fun a x ↦ ?_⟩).mpr fun p hp ↦ ?_
        · simp [add_mul, Finset.sum_add_distrib]
        · simp [Finset.mul_sum, mul_assoc]
        · rw [Finset.sum_eq_single p]
          · simp [c.2 p hp]
          · intro q _ hq; simp [Pi.single_apply, hq]
          · simp⟩
      left_inv := fun φ ↦ by
        apply Subtype.ext; funext f
        exact (hexp φ.1 (hS φ.2) f).symm
      right_inv := fun c ↦ by
        apply Subtype.ext; funext p
        simp only
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq; simp [Pi.single_apply, Ne.symm hq]
        · simp
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  rw [e.finrank_eq, finrank_coordSub]

namespace CoeffQuiver

variable {D} (C : D.CoeffQuiver) (hC : C.KillsZeroPaths)

/-- The module of a coefficient quiver. -/
abbrev Mod := (C.toRep hC).Carrier

/-- The coordinates of an element of the module. -/
def val (f : C.Mod hC) : C.P → k := f

/-- The element with given coordinates. -/
def ofFun (f : C.P → k) : C.Mod hC := f

@[simp] theorem val_ofFun (f : C.P → k) : C.val hC (C.ofFun hC f) = f := rfl

theorem ext_val {f g : C.Mod hC} (h : ∀ p, C.val hC f p = C.val hC g p) : f = g := funext h

@[simp] theorem val_zero : C.val hC 0 = 0 := rfl

theorem val_smul_k (c : k) (f : C.Mod hC) : C.val hC (c • f) = c • C.val hC f := rfl

theorem e_smul_apply (w : D.Q.V) (f : C.Mod hC) (p : C.P) :
    C.val hC (D.e w • f) p = if C.vtx p = w then C.val hC f p else 0 := by
  rw [Rep.e_smul]; rfl

theorem α_smul_apply (a : D.Q.A) (f : C.Mod hC) (j : C.P) :
    C.val hC (D.α a • f) j =
      ∑ i, if C.next a i = some j then C.coef a i * C.val hC f i else 0 := by
  rw [Rep.α_smul]; rfl

theorem e_smul_single (w : D.Q.V) (p : C.P) :
    D.e w • C.ofFun hC (Pi.single p 1) =
      if C.vtx p = w then C.ofFun hC (Pi.single p 1) else 0 := by
  rw [Rep.e_smul]; exact C.eMap_single w p 1

theorem α_smul_single (a : D.Q.A) (i : C.P) :
    D.α a • C.ofFun hC (Pi.single i 1) =
      match C.next a i with
      | none => 0
      | some j => C.ofFun hC (Pi.single j (C.coef a i * 1)) := by
  rw [Rep.α_smul]; exact C.αMap_single a i 1

/-- Injective arrow moves. -/
def InjMoves : Prop := ∀ a i i' j, C.next a i = some j → C.next a i' = some j → i = i'

/-- Nonzero coefficients on the arrow moves. -/
def CoefNe : Prop := ∀ a i j, C.next a i = some j → C.coef a i ≠ 0

variable {C hC}

theorem α_smul_apply_of_inj (hinj : C.InjMoves) {a : D.Q.A} {i j : C.P}
    (hij : C.next a i = some j) (f : C.Mod hC) :
    C.val hC (D.α a • f) j = C.coef a i * C.val hC f i := by
  rw [α_smul_apply, Finset.sum_eq_single i]
  · simp [hij]
  · intro i' _ hi'
    rw [if_neg]
    intro h
    exact hi' (hinj a i' i j h hij)
  · simp

variable (C hC)

theorem finrank_sub (S : Submodule k (C.Mod hC)) (T : C.P → Prop) [DecidablePred T]
    (h : ∀ f, f ∈ S ↔ ∀ p, ¬ T p → C.val hC f p = 0) :
    finrank k S = Fintype.card {p // T p} :=
  finrank_eq_card_of_mem_iff (P := C.P) S T h

theorem finrank_sub_dual (S : Submodule k (C.Mod hC → k)) (hS : S ≤ linFun (k := k) (C.Mod hC))
    (T : C.P → Prop) [DecidablePred T]
    (h : ∀ φ ∈ linFun (k := k) (C.Mod hC),
      φ ∈ S ↔ ∀ p, ¬ T p → φ (C.ofFun hC (Pi.single p 1)) = 0) :
    finrank k S = Fintype.card {p // T p} :=
  finrank_eq_card_of_mem_iff_dual (P := C.P) S hS T h

theorem linFun_expand' (φ : C.Mod hC → k) (hφ : φ ∈ linFun (k := k) (C.Mod hC)) (f : C.Mod hC) :
    φ f = ∑ p, C.val hC f p * φ (C.ofFun hC (Pi.single p 1)) :=
  linFun_expand (P := C.P) φ hφ f

theorem finrank_E0' (v : D.Q.V) :
    finrank k (D.E0' (C.Mod hC) v) = Fintype.card {p // C.vtx p = v} := by
  classical
  refine C.finrank_sub hC (D.E0' (C.Mod hC) v) _ fun f ↦ ?_
  change D.e v • f = f ↔ _
  constructor
  · intro h p hp
    have := congrArg (fun g ↦ C.val hC g p) h
    simp only [e_smul_apply, if_neg hp] at this
    exact this.symm
  · intro h
    refine C.ext_val hC fun p ↦ ?_
    rw [e_smul_apply]
    split_ifs with hp
    · rfl
    · exact (h p hp).symm

theorem finrank_K0' (hinj : C.InjMoves) (hcoef : C.CoefNe) (v : D.Q.V) :
    finrank k (D.K0' (C.Mod hC) v) =
      Fintype.card {p // C.vtx p = v ∧ ∀ a, C.next a p = none} := by
  classical
  refine C.finrank_sub hC (D.K0' (C.Mod hC) v) _ fun f ↦ ?_
  change (D.e v • f = f ∧ ∀ b, D.Q.src b = v → D.α b • f = 0) ↔ _
  constructor
  · rintro ⟨h1, h2⟩ p hp
    by_cases hv : C.vtx p = v
    · push Not at hp
      obtain ⟨a, ha⟩ := hp hv
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp ha
      have hsrc : D.Q.src a = v := (C.next_src a p j hj).symm.trans hv
      have := congrArg (fun g ↦ C.val hC g j) (h2 a hsrc)
      simp only [α_smul_apply_of_inj hinj hj, val_zero, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (hcoef a p j hj)
    · have := congrArg (fun g ↦ C.val hC g p) h1
      simp only [e_smul_apply, if_neg hv] at this
      exact this.symm
  · intro h
    have hoff : ∀ p, C.vtx p ≠ v → C.val hC f p = 0 := fun p hp ↦ h p fun h' ↦ hp h'.1
    refine ⟨C.ext_val hC fun p ↦ ?_, fun b _ ↦ C.ext_val hC fun j ↦ ?_⟩
    · rw [e_smul_apply]
      split_ifs with hp
      · rfl
      · exact (hoff p hp).symm
    · rw [α_smul_apply, val_zero, Pi.zero_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs with hij
      · have hi0 : C.val hC f i = 0 := h i fun hi ↦ by rw [hi.2 b] at hij; cases hij
        rw [hi0, mul_zero]
      · rfl

open Classical in
theorem finrank_Yb (hinj : C.InjMoves) (hcoef : C.CoefNe) (b : D.Q.A) :
    finrank k (D.Yb (C.Mod hC) b) =
      Fintype.card {q // C.vtx q = D.Q.tgt b ∧
        ∀ c, D.toPathData.Forbidden b c → C.next c q = none} := by
  refine C.finrank_sub hC (D.Yb (C.Mod hC) b) _ fun f ↦ ?_
  change (D.e (D.Q.tgt b) • f = f ∧ ∀ c, D.toPathData.Forbidden b c → D.α c • f = 0) ↔ _
  constructor
  · rintro ⟨h1, h2⟩ q hq
    by_cases hv : C.vtx q = D.Q.tgt b
    · push Not at hq
      obtain ⟨c, hc, hcq⟩ := hq hv
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hcq
      have := congrArg (fun g ↦ C.val hC g j) (h2 c hc)
      simp only [α_smul_apply_of_inj hinj hj, val_zero, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (hcoef c q j hj)
    · have := congrArg (fun g ↦ C.val hC g q) h1
      simp only [e_smul_apply, if_neg hv] at this
      exact this.symm
  · intro h
    have hoff : ∀ p, C.vtx p ≠ D.Q.tgt b → C.val hC f p = 0 := fun p hp ↦ h p fun h' ↦ hp h'.1
    refine ⟨C.ext_val hC fun p ↦ ?_, fun c hc ↦ C.ext_val hC fun j ↦ ?_⟩
    · rw [e_smul_apply]
      split_ifs with hp
      · rfl
      · exact (hoff p hp).symm
    · rw [α_smul_apply, val_zero, Pi.zero_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs with hij
      · have hi0 : C.val hC f i = 0 := h i fun hi ↦ by rw [hi.2 c hc] at hij; cases hij
        rw [hi0, mul_zero]
      · rfl

theorem finrank_E0 (v : D.Q.V) :
    finrank k (D.E0 (C.Mod hC) v) = Fintype.card {p // C.vtx p = v} := by
  classical
  refine C.finrank_sub_dual hC (D.E0 (C.Mod hC) v) (fun _ h ↦ h.1) _ fun φ hφ ↦ ?_
  change (φ ∈ linFun (C.Mod hC) ∧ ∀ m, φ (D.e v • m) = φ m) ↔ _
  have hφ0 : φ 0 = 0 := (toLin φ hφ).map_zero
  constructor
  · rintro ⟨-, h⟩ p hp
    have := h (C.ofFun hC (Pi.single p 1))
    rw [e_smul_single, if_neg hp, hφ0] at this
    exact this.symm
  · intro h
    refine ⟨hφ, fun m ↦ ?_⟩
    rw [C.linFun_expand' hC φ hφ, C.linFun_expand' hC φ hφ m]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [e_smul_apply]
    split_ifs with hp
    · rfl
    · rw [h p hp]; simp

theorem single_eq_smul (j : C.P) (c : k) :
    C.ofFun hC (Pi.single j c) = c • C.ofFun hC (Pi.single j 1) := by
  refine C.ext_val hC fun p ↦ ?_
  simp [val_smul_k, Pi.single_apply]

theorem finrank_K0 (hcoef : C.CoefNe) (v : D.Q.V) :
    finrank k (D.K0 (C.Mod hC) v) =
      Fintype.card {p // C.vtx p = v ∧ ∀ a i, C.next a i ≠ some p} := by
  classical
  refine C.finrank_sub_dual hC (D.K0 (C.Mod hC) v) (fun _ h ↦ h.1) _ fun φ hφ ↦ ?_
  change (φ ∈ linFun (C.Mod hC) ∧ (∀ m, φ (D.e v • m) = φ m) ∧
    ∀ b, D.Q.tgt b = v → ∀ m, φ (D.α b • m) = 0) ↔ _
  have hφ0 : φ 0 = 0 := (toLin φ hφ).map_zero
  constructor
  · rintro ⟨-, h1, h2⟩ p hp
    by_cases hv : C.vtx p = v
    · push Not at hp
      obtain ⟨a, i, hi⟩ := hp hv
      have htgt : D.Q.tgt a = v := (C.next_tgt a i p hi).symm.trans hv
      have := h2 a htgt (C.ofFun hC (Pi.single i 1))
      rw [α_smul_single, hi] at this
      simp only at this
      rw [mul_one, single_eq_smul, hφ.2] at this
      exact (mul_eq_zero.mp this).resolve_left (hcoef a i p hi)
    · have := h1 (C.ofFun hC (Pi.single p 1))
      rw [e_smul_single, if_neg hv, hφ0] at this
      exact this.symm
  · intro h
    have hoff : ∀ p, C.vtx p ≠ v → φ (C.ofFun hC (Pi.single p 1)) = 0 :=
      fun p hp ↦ h p fun h' ↦ hp h'.1
    refine ⟨hφ, fun m ↦ ?_, fun b _ m ↦ ?_⟩
    · rw [C.linFun_expand' hC φ hφ, C.linFun_expand' hC φ hφ m]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [e_smul_apply]
      split_ifs with hp
      · rfl
      · rw [hoff p hp]; simp
    · rw [C.linFun_expand' hC φ hφ]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [α_smul_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs with hij
      · rw [h j fun hj ↦ hj.2 b i hij, mul_zero]
      · simp

open Classical in
theorem finrank_Zb (hcoef : C.CoefNe) (b : D.Q.A) :
    finrank k (D.Zb (C.Mod hC) b) =
      Fintype.card {q // C.vtx q = D.Q.src b ∧
        ∀ a i, D.toPathData.Forbidden a b → C.next a i ≠ some q} := by
  refine C.finrank_sub_dual hC (D.Zb (C.Mod hC) b) (fun _ h ↦ h.1) _ fun φ hφ ↦ ?_
  change (φ ∈ linFun (C.Mod hC) ∧ (∀ m, φ (D.e (D.Q.src b) • m) = φ m) ∧
    ∀ a, D.toPathData.Forbidden a b → ∀ m, φ (D.α a • m) = 0) ↔ _
  have hφ0 : φ 0 = 0 := (toLin φ hφ).map_zero
  constructor
  · rintro ⟨-, h1, h2⟩ p hp
    by_cases hv : C.vtx p = D.Q.src b
    · push Not at hp
      obtain ⟨a, i, hab, hi⟩ := hp hv
      have := h2 a hab (C.ofFun hC (Pi.single i 1))
      rw [α_smul_single, hi] at this
      simp only at this
      rw [mul_one, single_eq_smul, hφ.2] at this
      exact (mul_eq_zero.mp this).resolve_left (hcoef a i p hi)
    · have := h1 (C.ofFun hC (Pi.single p 1))
      rw [e_smul_single, if_neg hv, hφ0] at this
      exact this.symm
  · intro h
    have hoff : ∀ p, C.vtx p ≠ D.Q.src b → φ (C.ofFun hC (Pi.single p 1)) = 0 :=
      fun p hp ↦ h p fun h' ↦ hp h'.1
    refine ⟨hφ, fun m ↦ ?_, fun a hab m ↦ ?_⟩
    · rw [C.linFun_expand' hC φ hφ, C.linFun_expand' hC φ hφ m]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [e_smul_apply]
      split_ifs with hp
      · rfl
      · rw [hoff p hp]; simp
    · rw [C.linFun_expand' hC φ hφ]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [α_smul_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs with hij
      · rw [h j fun hj ↦ hj.2 a i hab hij, mul_zero]
      · simp

end CoeffQuiver

end MonomialData

end BrickAccessibility
