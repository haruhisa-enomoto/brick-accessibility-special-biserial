module

public import BrickAccessibility.Classification.Cons

/-!
# Shift isomorphisms of the pair functors

For a pair `(h, h')` of half-words at `v` with signs `s`, `!s`, write
`num = h⁺ ∩ h'⁺` and `den = h⁻ ∩ h'⁺ + h⁺ ∩ h'⁻`; the pair functor is
`num / den`. If `h = a X` starts with a direct letter `a : v → u`, then `a`
induces an isomorphism from the functor of `(a X, Y)` at `v` to that of
`(X, a⁻¹ Y)` at `u` (`shift`). We record isomorphisms without quotient types
(`FIso`). The functor is symmetric in the two half-words.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- A linear map inducing an isomorphism `num₁ / den₁ ≅ num₂ / den₂`. -/
structure FIso {k X : Type*} [Field k] [AddCommGroup X] [Module k X] (φ : X →ₗ[k] X)
    (num₁ den₁ num₂ den₂ : Submodule k X) : Prop where
  map_num : num₁.map φ ≤ num₂
  map_den : den₁.map φ ≤ den₂
  surj : num₂ ≤ num₁.map φ ⊔ den₂
  inj : ∀ x ∈ num₁, φ x ∈ den₂ → x ∈ den₁

/-- `φ` induces an isomorphism `V ≅ num / den`. -/
structure IsoOnto {k X V : Type*} [Field k] [AddCommGroup X] [Module k X] [AddCommGroup V]
    [Module k V] (φ : V →ₗ[k] X) (num den : Submodule k X) : Prop where
  mem : ∀ y, φ y ∈ num
  inj : ∀ y, φ y ∈ den → y = 0
  surj : num ≤ LinearMap.range φ ⊔ den

section IsoOnto

variable {k X V : Type*} [Field k] [AddCommGroup X] [Module k X] [AddCommGroup V] [Module k V]
  {φ : V →ₗ[k] X} {α : X →ₗ[k] X} {n₁ d₁ n₂ d₂ : Submodule k X}

theorem IsoOnto.fwd (h : IsoOnto φ n₁ d₁) (hα : FIso α n₁ d₁ n₂ d₂) : IsoOnto (α ∘ₗ φ) n₂ d₂ := by
  refine ⟨fun y ↦ hα.map_num ⟨φ y, h.mem y, rfl⟩, fun y hy ↦ h.inj y (hα.inj _ (h.mem y) hy),
    fun x hx ↦ ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, d, hd, rfl⟩ := Submodule.mem_sup.mp (hα.surj hx)
  obtain ⟨_, ⟨y, rfl⟩, d', hd', rfl⟩ := Submodule.mem_sup.mp (h.surj hz)
  refine Submodule.mem_sup.mpr ⟨α (φ y), ⟨y, rfl⟩, α d' + d,
    Submodule.add_mem _ (hα.map_den ⟨d', hd', rfl⟩) hd, ?_⟩
  rw [map_add]; abel

theorem IsoOnto.bwd (h : IsoOnto φ n₂ d₂) (hα : FIso α n₁ d₁ n₂ d₂) {ψ : V →ₗ[k] X}
    (hψ : ∀ y, ψ y ∈ n₁) (hrel : ∀ y, α (ψ y) = φ y) : IsoOnto ψ n₁ d₁ := by
  refine ⟨hψ, fun y hy ↦ h.inj y (hrel y ▸ hα.map_den ⟨ψ y, hy, rfl⟩), fun x hx ↦ ?_⟩
  obtain ⟨_, ⟨y, rfl⟩, d, hd, hsum⟩ :=
    Submodule.mem_sup.mp (h.surj (hα.map_num ⟨x, hx, rfl⟩))
  have hdiff : α (x - ψ y) ∈ d₂ := by
    rw [map_sub, hrel, ← hsum]; simpa using hd
  have := hα.inj _ (Submodule.sub_mem _ hx (hψ y)) hdiff
  refine Submodule.mem_sup.mpr ⟨ψ y, ⟨y, rfl⟩, x - ψ y, this, by abel⟩

theorem IsoOnto.finrank_eq [FiniteDimensional k X] (h : IsoOnto φ n₁ d₁) (hdn : d₁ ≤ n₁) :
    finrank k n₁ = finrank k (LinearMap.range φ) + finrank k d₁ := by
  have hsup : LinearMap.range φ ⊔ d₁ = n₁ :=
    le_antisymm (sup_le (by rintro _ ⟨y, rfl⟩; exact h.mem y) hdn) h.surj
  have hinf : LinearMap.range φ ⊓ d₁ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨⟨y, rfl⟩, hy⟩ := Submodule.mem_inf.mp hx
    rw [h.inj y hy, map_zero]; exact Submodule.zero_mem _
  have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range φ) d₁
  rw [hsup, hinf, finrank_bot] at this
  omega

theorem IsoOnto.injective (h : IsoOnto φ n₁ d₁) : Function.Injective φ := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  exact h.inj y (by rw [LinearMap.mem_ker.mp hy]; exact Submodule.zero_mem _)

end IsoOnto

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- The numerator of a pair functor. -/
def Signs.pnum (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) : Submodule k M :=
  S.plus M v s h ⊓ S.plus M v (!s) h'

/-- The denominator of a pair functor. -/
def Signs.pden (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) : Submodule k M :=
  S.minus M v s h ⊓ S.plus M v (!s) h' ⊔ S.plus M v s h ⊓ S.minus M v (!s) h'

theorem Signs.pnum_swap (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) :
    S.pnum M v (!s) h' h = S.pnum M v s h h' := by
  simp [Signs.pnum, inf_comm]

theorem Signs.pden_swap (v : D.Q.V) (s : Bool) (h h' : HWord D.Q) :
    S.pden M v (!s) h' h = S.pden M v s h h' := by
  simp only [Signs.pden, Bool.not_not]
  rw [sup_comm, inf_comm (S.plus M v (!s) h'), inf_comm (S.minus M v (!s) h')]

theorem Signs.pden_le_pnum {v : D.Q.V} {s : Bool} {h h' : HWord D.Q} (hv : S.Valid v s h)
    (hv' : S.Valid v (!s) h') : S.pden M v s h h' ≤ S.pnum M v s h h' :=
  sup_le (inf_le_inf_right _ (S.minus_le_plus hv)) (inf_le_inf_left _ (S.minus_le_plus hv'))

/-- **The shift isomorphism** across a direct letter. -/
theorem Signs.shift [FiniteDimensional k M] {a : D.Q.A} {X Y : HWord D.Q}
    (hX : S.Valid (D.Q.tgt a) (!S.ε a) X) (hY : S.Valid (D.Q.src a) (!S.σ a) Y) :
    FIso (actL (D.α a))
      (S.pnum M (D.Q.src a) (S.σ a) (X.cons (a, true)) Y)
      (S.pden M (D.Q.src a) (S.σ a) (X.cons (a, true)) Y)
      (S.pnum M (D.Q.tgt a) (!S.ε a) X (Y.cons (a, false)))
      (S.pden M (D.Q.tgt a) (!S.ε a) X (Y.cons (a, false))) := by
  have hPh : S.plus M (D.Q.src a) (S.σ a) (X.cons (a, true)) =
      D.tr (a, true) (S.plus M (D.Q.tgt a) (!S.ε a) X) := S.plus_cons rfl hX
  have hMh : S.minus M (D.Q.src a) (S.σ a) (X.cons (a, true)) =
      D.tr (a, true) (S.minus M (D.Q.tgt a) (!S.ε a) X) := S.minus_cons _ _ _ _
  have hPY : S.plus M (D.Q.tgt a) (S.ε a) (Y.cons (a, false)) =
      D.tr (a, false) (S.plus M (D.Q.src a) (!S.σ a) Y) := S.plus_cons rfl hY
  have hMY : S.minus M (D.Q.tgt a) (S.ε a) (Y.cons (a, false)) =
      D.tr (a, false) (S.minus M (D.Q.src a) (!S.σ a) Y) := S.minus_cons _ _ _ _
  simp only [Signs.pnum, Signs.pden, hPh, hMh, hPY, hMY, Bool.not_not] at *
  set PX := S.plus M (D.Q.tgt a) (!S.ε a) X
  set MX := S.minus M (D.Q.tgt a) (!S.ε a) X
  set PY := S.plus M (D.Q.src a) (!S.σ a) Y
  set MY := S.minus M (D.Q.src a) (!S.σ a) Y
  have hMYPY : MY ≤ PY := S.minus_le_plus hY
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, ⟨⟨hxv, hxX⟩, hxY⟩, rfl⟩
    exact ⟨hxX, (D.mem_tr_false).mpr ⟨x, hxv, hxY, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨⟨hx1v, hx1X⟩, hx1Y⟩ := hx1
    obtain ⟨⟨hx2v, hx2X⟩, hx2Y⟩ := hx2
    rw [map_add]
    refine Submodule.add_mem_sup ⟨hx1X, (D.mem_tr_false).mpr ⟨x1, hx1v, hx1Y, rfl⟩⟩
      ⟨hx2X, (D.mem_tr_false).mpr ⟨x2, hx2v, hx2Y, rfl⟩⟩
  · rintro y ⟨hyX, hyY⟩
    obtain ⟨x, hxv, hxY, rfl⟩ := (D.mem_tr_false).mp hyY
    exact Submodule.mem_sup_left ⟨x, ⟨⟨hxv, hyX⟩, hxY⟩, rfl⟩
  · rintro x ⟨⟨hxv, hxX⟩, hxY⟩ hden
    obtain ⟨y1, hy1, y2, hy2, hsum⟩ := Submodule.mem_sup.mp hden
    obtain ⟨hy1X, hy1Y⟩ := hy1
    obtain ⟨hy2X, hy2Y⟩ := hy2
    obtain ⟨x1, hx1v, hx1Y, rfl⟩ := (D.mem_tr_false).mp hy1Y
    obtain ⟨x2, hx2v, hx2Y, rfl⟩ := (D.mem_tr_false).mp hy2Y
    -- `x = x1 + x2 + x'` with `a x' = 0`
    have hx' : D.α a • (x - x1 - x2) = 0 := by
      have hsum' : D.α a • x1 + D.α a • x2 = D.α a • x := hsum
      rw [smul_sub, smul_sub, ← hsum']; abel
    have h1 : x1 ∈ D.tr (a, true) MX ⊓ PY := ⟨⟨hx1v, hy1X⟩, hx1Y⟩
    have h2 : x2 ∈ D.tr (a, true) PX ⊓ MY := ⟨⟨hx2v, hy2X⟩, hx2Y⟩
    have h3 : x - x1 - x2 ∈ D.tr (a, true) MX ⊓ PY := by
      refine ⟨⟨Submodule.sub_mem _ (Submodule.sub_mem _ hxv hx1v) hx2v, ?_⟩, ?_⟩
      · change D.α a • (x - x1 - x2) ∈ MX
        rw [hx']; exact MX.zero_mem
      · exact Submodule.sub_mem _ (Submodule.sub_mem _ hxY hx1Y) (hMYPY hx2Y)
    have : x = (x - x1 - x2) + x1 + x2 := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left h3)
      (Submodule.mem_sup_left h1)) (Submodule.mem_sup_right h2)

end MonomialData

end BrickAccessibility
