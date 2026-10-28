module

public import BrickAccessibility.Classification.BandScalar

/-!
# Band modules are indecomposable

At a primitive band, an idempotent endomorphism of `M(b, t)` that is zero on the
one-dimensional pair functor at `first` is zero on every pair functor (shift
isomorphisms and position counts), hence zero (spanning lemma). As the functor at
`first` is one-dimensional, one of the two projections of a decomposition has this
property (`isIndecomposable`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- An endomorphism commuting with a shift isomorphism kills the pair functor on one side
iff on the other. -/
theorem FIso.kill_iff {X : Type*} [AddCommGroup X] [Module k X] {α g : X →ₗ[k] X}
    {n₁ d₁ n₂ d₂ : Submodule k X} (hF : FIso α n₁ d₁ n₂ d₂) (hcomm : ∀ x, g (α x) = α (g x))
    (hn₁ : ∀ x ∈ n₁, g x ∈ n₁) (hd₂ : ∀ x ∈ d₂, g x ∈ d₂) :
    (∀ x ∈ n₁, g x ∈ d₁) ↔ (∀ x ∈ n₂, g x ∈ d₂) := by
  constructor
  · intro h x hx
    obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp (hF.surj hx)
    rw [map_add]
    refine Submodule.add_mem _ ?_ (hd₂ z hz)
    rw [hcomm]
    exact hF.map_den ⟨g y, h y hy, rfl⟩
  · intro h x hx
    refine hF.inj (g x) (hn₁ x hx) ?_
    rw [← hcomm]
    exact h _ (hF.map_num ⟨x, hx, rfl⟩)

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)

section
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
  [FiniteDimensional k M]

include hA in
/-- An endomorphism killing the pair functor at `first` kills it at every position. -/
theorem kill_all (g : M →ₗ[B] M)
    (h0 : ∀ x ∈ b.numB S M b.first, g x ∈ b.denB S M b.first) (q : Fin b.n) :
    ∀ x ∈ b.numB S M q, g x ∈ b.denB S M q := by
  have hn : ∀ i : Fin b.n, ∀ x ∈ b.numB S M i, g x ∈ b.numB S M i := fun i x hx ↦
    S.map_pnum_le _ g _ _ _ _ ⟨x, hx, rfl⟩
  have hd : ∀ i : Fin b.n, ∀ x ∈ b.denB S M i, g x ∈ b.denB S M i := fun i x hx ↦
    S.map_pden_le M g _ _ _ _ ⟨x, hx, rfl⟩
  have hcomm : ∀ (a : D.Q.A) (x : M), (g.restrictScalars k) (MonomialData.actL (k := k) (D.α a) x) =
      MonomialData.actL (k := k) (D.α a) ((g.restrictScalars k) x) := fun a x ↦ by
    simp [MonomialData.actL_apply]
  have key : ∀ m (hm : m < b.n), ∀ x ∈ b.numB S M ⟨m, hm⟩, g x ∈ b.denB S M ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro _; exact h0
    | succ m ih =>
        intro hm
        have e : b.succ ⟨m, by omega⟩ = ⟨m + 1, hm⟩ := Fin.ext (b.succ_val_of_lt _ hm)
        rw [← e]
        rcases hl : b.lt ⟨m, by omega⟩ with ⟨a, d⟩
        cases d
        · have hF := b.fiso_false S hA M ⟨m, by omega⟩ a hl
          exact ((hF.kill_iff (hcomm a) (hn _) (hd _)).mpr (ih (by omega)))
        · have hF := b.fiso_true S hA M ⟨m, by omega⟩ a hl
          exact ((hF.kill_iff (hcomm a) (hn _) (hd _)).mp (ih (by omega)))
  exact key q.val q.isLt
end

include hA in
/-- At a primitive band, an idempotent endomorphism of `M(b, t)` killing the pair functor at
`first` is zero. -/
theorem eq_zero_of_kill (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (t : kˣ)
    (g : b.BM S hA hK t →ₗ[B] b.BM S hA hK t) (hidem : ∀ x, g (g x) = g x)
    (h0 : ∀ x ∈ b.numB S (b.BM S hA hK t) b.first, g x ∈ b.denB S (b.BM S hA hK t) b.first) :
    g = 0 := by
  classical
  set X := b.BM S hA hK t
  have hall := b.kill_all S hA g h0
  have hpair : ∀ (v : D.Q.V) (t1 : S.HW v true) (t2 : S.HW v (!true)),
      S.pnum X v true t1.1 t2.1 ≤ LinearMap.ker (g.restrictScalars k) ⊔ S.pden X v true t1.1 t2.1 := by
    intro v t1 t2 x hx
    have hgx : g x ∈ S.pden X v true t1.1 t2.1 := by
      by_cases hle : S.pnum X v true t1.1 t2.1 ≤ S.pden X v true t1.1 t2.1
      · exact hle (S.map_pnum_le _ g _ _ _ _ ⟨x, hx, rfl⟩)
      · have h := b.band_gr_eq S hA (tw t) hK t1.2 t2.2
        have hc := b.card_eq S hA hprim (v, true, t1.1, t2.1)
        simp only at hc
        rw [hc] at h
        have hlt : finrank k (S.pden X v true t1.1 t2.1) < finrank k (S.pnum X v true t1.1 t2.1) :=
          Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (S.pden_le_pnum X t1.2 t2.2)
            fun e ↦ hle e.ge)
        split_ifs at h with hP
        · obtain ⟨q, s', e⟩ := hP
          simp only [pairAt, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl, h1, h2⟩ := e
          have hx' : x ∈ b.numB S X q := by
            rw [b.numB_eq_half S X q true, ← h1, ← h2]; exact hx
          have := hall q x hx'
          rwa [b.denB_eq_half S X q true, ← h1, ← h2] at this
        · simp only [zero_mul] at h
          change finrank k (S.pnum X v true t1.1 t2.1) - finrank k (S.pden X v true t1.1 t2.1) = 0
            at h
          omega
    refine Submodule.mem_sup.mpr ⟨x - g x, ?_, g x, hgx, by abel⟩
    simp [hidem]
  have hv : ∀ v, D.vsp X v ≤ LinearMap.ker (g.restrictScalars k) := fun v ↦
    IFam.le_of_num_le (S.fam X v true) (S.fam X v (!true)) _ fun t1 t2 ↦ hpair v t1 t2
  ext x
  rw [← one_smul B x, ← D.toPathData.sum_e, Finset.sum_smul, map_sum]
  refine Finset.sum_eq_zero fun v _ ↦ ?_
  exact hv v ⟨x, rfl⟩

include hA in
/-- **Band modules are indecomposable** (at a primitive band). -/
theorem isIndecomposable (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (t : kˣ) :
    IsIndecomposable B (b.BM S hA hK t) := by
  set X := b.BM S hA hK t
  have hx0 := b.x0_mem_numB S hA hK t
  have hx0d := b.x0_not_mem_denB S hA hK t
  refine ⟨⟨⟨(b.x0 S hA hK t), 0, fun h ↦ hx0d (by rw [h]; exact Submodule.zero_mem _)⟩⟩, fun A A' hc ↦ ?_⟩
  set g := A.projection A' hc
  have hidem : ∀ x, g (g x) = g x := fun x ↦
    Submodule.projection_apply_of_mem_left hc (Submodule.projection_apply_mem hc x)
  have hnat : ∀ x ∈ b.numB S X b.first, g x ∈ b.numB S X b.first := fun x hx ↦
    S.map_pnum_le _ g _ _ _ _ ⟨x, hx, rfl⟩
  have hden : ∀ x ∈ b.denB S X b.first, g x ∈ b.denB S X b.first := fun x hx ↦
    S.map_pden_le X g _ _ _ _ ⟨x, hx, rfl⟩
  obtain ⟨w, hw, d, hd, hgx⟩ := Submodule.mem_sup.mp (b.numB_le_span S hA hK hprim t (hnat (b.x0 S hA hK t) hx0))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  -- `c` is idempotent
  have hcc : (c - c * c) • (b.x0 S hA hK t) ∈ b.denB S X b.first := by
    have e1 : g (g (b.x0 S hA hK t)) = c • g (b.x0 S hA hK t) + g d := by
      rw [← hgx, map_add, g.map_smul_of_tower, hgx]
    rw [hidem] at e1
    have e2 : (c - c * c) • (b.x0 S hA hK t) = c • d + g d - d := by
      have h' : c • b.x0 S hA hK t + d = c • (c • b.x0 S hA hK t) + c • d + g d := by
        rw [hgx, e1, ← hgx, smul_add]
      rw [sub_smul, mul_smul]
      calc c • b.x0 S hA hK t - c • (c • b.x0 S hA hK t)
          = (c • b.x0 S hA hK t + d) - d - c • (c • b.x0 S hA hK t) := by abel
        _ = (c • (c • b.x0 S hA hK t) + c • d + g d) - d - c • (c • b.x0 S hA hK t) := by rw [h']
        _ = c • d + g d - d := by abel
    rw [e2]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hd) (hden d hd)) hd
  have hc01 : c = 0 ∨ c = 1 := by
    by_contra hne
    push_neg at hne
    have : c - c * c ≠ 0 := by
      rw [show c - c * c = c * (1 - c) by ring]
      exact mul_ne_zero hne.1 (sub_ne_zero.mpr (Ne.symm hne.2))
    exact hx0d ((Submodule.smul_mem_iff _ this).mp hcc)
  have hspan : ∀ (h : X →ₗ[B] X), h (b.x0 S hA hK t) ∈ b.denB S X b.first →
      (∀ x ∈ b.denB S X b.first, h x ∈ b.denB S X b.first) →
      ∀ x ∈ b.numB S X b.first, h x ∈ b.denB S X b.first := by
    intro h hx0' hd' x hx
    obtain ⟨w', hw', d', hd'', rfl⟩ := Submodule.mem_sup.mp (b.numB_le_span S hA hK hprim t hx)
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hw'
    rw [map_add, h.map_smul_of_tower]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx0') (hd' d' hd'')
  rcases hc01 with rfl | rfl
  · left
    have hg0 : g = 0 := b.eq_zero_of_kill S hA hK hprim t g hidem
      (hspan g (by rw [← hgx, zero_smul, zero_add]; exact hd) hden)
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    rw [Submodule.mem_bot, ← Submodule.projection_apply_of_mem_left hc hx]
    change g x = 0
    rw [hg0]; rfl
  · right
    set g' : X →ₗ[B] X := LinearMap.id - g
    have hidem' : ∀ x, g' (g' x) = g' x := fun x ↦ by
      simp only [g', LinearMap.sub_apply, LinearMap.id_apply, map_sub, hidem]; abel
    have hg'0 : g' = 0 := b.eq_zero_of_kill S hA hK hprim t g' hidem'
      (hspan g' (by
        simp only [g', LinearMap.sub_apply, LinearMap.id_apply]
        rw [← hgx, one_smul, sub_add_cancel_left]
        exact Submodule.neg_mem _ hd)
        (fun x hx ↦ by
          simp only [g', LinearMap.sub_apply, LinearMap.id_apply]
          exact Submodule.sub_mem _ hx (hden x hx)))
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    have h1 : g x = 0 := Submodule.projection_apply_of_mem_right hc hx
    have h2 : g' x = 0 := by rw [hg'0]; rfl
    simp only [g', LinearMap.sub_apply, LinearMap.id_apply, h1, sub_zero] at h2
    exact (Submodule.mem_bot B).mpr h2

end CWord

end BrickAccessibility
