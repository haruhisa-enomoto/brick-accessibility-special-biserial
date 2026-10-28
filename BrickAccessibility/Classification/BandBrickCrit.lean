module

public import BrickAccessibility.Classification.RepFinite

/-!
# A criterion for band bricks

If no position `p ≠ q` of a primitive band lies in both plus sets of the halves of
`q`, then every band module `M(b, t)` is a brick (`isBrick_of_plusSets`). An
endomorphism minus a scalar kills the pair functor at `first`, hence at every
position, so it sends each block vector `x_q` into the denominator at `q`, whose
positions are excluded by the hypothesis. A band through pairwise distinct vertices
satisfies the criterion (`isBrick_of_vtx_injective`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)

/-- The plus-set condition at a pair of positions. -/
def PlusBoth (p q : Fin b.n) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V),
    (b.blockQuiver S hA V φ).plusSet S (b.vtx q) (S.st (b.lt q)) (.inf (b.rightW q)) p ∧
      (b.blockQuiver S hA V φ).plusSet S (b.vtx q) (!S.st (b.lt q)) (.inf (b.leftW q)) p

include hA in
/-- **Band brick criterion.** -/
theorem isBrick_of_plusSets (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q)
    (t : kˣ) (hN : ∀ p q : Fin b.n, p ≠ q →
      ¬ ((b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (S.st (b.lt q)) (.inf (b.rightW q)) p ∧
        (b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (!S.st (b.lt q)) (.inf (b.leftW q)) p)) :
    IsBrick B (b.BM S hA hK t) := by
  classical
  have hnt := b.nontrivial_BM S hA hK t
  refine ⟨hnt, fun f hf ↦ ?_⟩
  -- the scalar of `f` at `first`
  have hfn : f (b.x0 S hA hK t) ∈ b.numB S (b.BM S hA hK t) b.first :=
    S.map_pnum_le _ f _ _ _ _ ⟨_, b.x0_mem_numB S hA hK t, rfl⟩
  obtain ⟨w, hw, d, hd, hfx⟩ := Submodule.mem_sup.mp (b.numB_le_span S hA hK hprim t hfn)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  set g : (b.BM S hA hK t) →ₗ[B] (b.BM S hA hK t) := f - c • LinearMap.id
  have hden : ∀ x ∈ b.denB S (b.BM S hA hK t) b.first, g x ∈ b.denB S (b.BM S hA hK t) b.first := fun x hx ↦
    S.map_pden_le (b.BM S hA hK t) g _ _ _ _ ⟨x, hx, rfl⟩
  have hg0 : ∀ x ∈ b.numB S (b.BM S hA hK t) b.first, g x ∈ b.denB S (b.BM S hA hK t) b.first := by
    intro x hx
    obtain ⟨w', hw', d', hd', rfl⟩ := Submodule.mem_sup.mp (b.numB_le_span S hA hK hprim t hx)
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hw'
    rw [map_add, g.map_smul_of_tower]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (hden d' hd')
    show f (b.x0 S hA hK t) - c • b.x0 S hA hK t ∈ _
    rw [← hfx, add_sub_cancel_left]; exact hd
  have hall := b.kill_all S hA g hg0
  -- `g` kills every block vector
  have hgx : ∀ q, g (b.xs S hA hK t q) = 0 := by
    intro q
    have hxq : b.xs S hA hK t q ∈ b.numB S (b.BM S hA hK t) q :=
      (b.blockQuiver S hA k (tw t)).single_mem_pnum (b.blockQuiver_kills S hA hK k (tw t)) S (b.PM_rightW S hA (tw t) q) (b.PM_leftW S hA (tw t) q) 1
    have h1 := hall q _ hxq
    have h2 := b.denB_le_numB S (b.BM S hA hK t) hA q h1
    refine (b.blockQuiver S hA k (tw t)).ext_val (b.blockQuiver_kills S hA hK k (tw t)) fun p ↦ ?_
    by_cases hpq : p = q
    · subst hpq
      simp only [denB, Signs.pden, (b.blockQuiver S hA k (tw t)).plus_eq_blk (b.blockQuiver_kills S hA hK k (tw t)), (b.blockQuiver S hA k (tw t)).minus_eq_blk (b.blockQuiver_kills S hA hK k (tw t)), (b.blockQuiver S hA k (tw t)).blk_inf (b.blockQuiver_kills S hA hK k (tw t)),
        (b.blockQuiver S hA k (tw t)).blk_sup (b.blockQuiver_kills S hA hK k (tw t))] at h1
      refine h1 p ?_
      rintro (⟨hm, -⟩ | ⟨-, hm⟩)
      · exact (b.PM_rightW S hA (tw t) p).2 hm
      · exact (b.PM_leftW S hA (tw t) p).2 hm
    · simp only [numB_eq_pnum, Signs.pnum, (b.blockQuiver S hA k (tw t)).plus_eq_blk (b.blockQuiver_kills S hA hK k (tw t)), (b.blockQuiver S hA k (tw t)).blk_inf (b.blockQuiver_kills S hA hK k (tw t))] at h2
      exact h2 p fun h ↦ hN p q hpq h
  have hg : g = 0 := (b.blockQuiver S hA k (tw t)).hom_ext (b.blockQuiver_kills S hA hK k (tw t)) fun j y ↦ by
    have : (b.blockQuiver S hA k (tw t)).ofFun (b.blockQuiver_kills S hA hK k (tw t)) (Pi.single j y) = y • b.xs S hA hK t j := by
      show Pi.single j y = y • Pi.single j (1 : k)
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, g.map_smul_of_tower]
    have h0 : g (b.xs S hA hK t j) = 0 := hgx j
    rw [h0, smul_zero, LinearMap.zero_apply]
  have hfc : f = c • LinearMap.id := sub_eq_zero.mp hg
  have hc0 : c ≠ 0 := by rintro rfl; apply hf; rw [hfc, zero_smul]
  rw [hfc]
  exact ⟨⟨c • LinearMap.id, c⁻¹ • LinearMap.id, by ext x; simp [smul_smul, hc0],
    by ext x; simp [smul_smul, hc0]⟩, rfl⟩

include hA in
/-- A band through pairwise distinct vertices gives band bricks. -/
theorem isBrick_of_vtx_injective (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q)
    (hv : Function.Injective b.vtx) (t : kˣ) : IsBrick B (b.BM S hA hK t) := by
  refine b.isBrick_of_plusSets S hA hK hprim t (fun p q hpq h ↦ hpq (hv ?_))
  exact h.1 0

end CWord



namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)

theorem iter_pred_eq_succ (x : Fin b.n) (m : ℕ) : b.pred^[m] x = b.succ^[b.n * m - m] x := by
  have hle : m ≤ b.n * m := Nat.le_mul_of_pos_left _ b.n_pos
  conv_rhs => rw [← b.iter_succ_pred x m]
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle, Nat.mul_comm, b.iter_succ_mul]

theorem leftW_eq_of_rightW_eq {p q : Fin b.n} (h : b.rightW p = b.rightW q) :
    b.leftW p = b.leftW q := by
  funext t
  simp only [leftW]
  rw [b.iter_pred_eq_succ p, b.iter_pred_eq_succ q]
  exact congrArg Letter.inv (congrFun h _)

include hA in
/-- The plus-set condition forces primitivity. -/
theorem prim_of_plusSets (t : kˣ) (hN : ∀ p q : Fin b.n, p ≠ q →
      ¬ ((b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (S.st (b.lt q)) (.inf (b.rightW q)) p ∧
        (b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (!S.st (b.lt q)) (.inf (b.leftW q)) p)) :
    ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q := by
  intro p q h
  by_contra hpq
  apply hN p q hpq
  have h0 : b.lt p = b.lt q := by
    have := congrFun h 0; simpa [rightW] using this
  have hv : b.vtx q = b.vtx p := by simp [vtx, h0]
  rw [hv, ← h0, ← h, ← b.leftW_eq_of_rightW_eq h]
  exact ⟨(b.PM_rightW S hA (tw t) p).1, (b.PM_leftW S hA (tw t) p).1⟩

include hA in
/-- **Band brick criterion**, without assuming primitivity. -/
theorem isBrick_of_plusSets' (t : kˣ) (hN : ∀ p q : Fin b.n, p ≠ q →
      ¬ ((b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (S.st (b.lt q)) (.inf (b.rightW q)) p ∧
        (b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (!S.st (b.lt q)) (.inf (b.leftW q)) p)) :
    IsBrick B (b.BM S hA hK t) :=
  b.isBrick_of_plusSets S hA hK (b.prim_of_plusSets S hA t hN) t hN

include hA in
/-- **Refutation by codes**: if the half of `q` is smaller than the half of `p` with the same
sign, then `p` is not in the plus set of `q`'s half. -/
theorem not_plusSet_of_lt {V : Type u} [AddCommGroup V] [Module k V] [Nontrivial V]
    (φ : V ≃ₗ[k] V) (hK' : (b.blockQuiver S hA V φ).KillsZeroPaths) {p q : Fin b.n}
    (hv : b.vtx p = b.vtx q) (s : Bool)
    (hlt : toLex (b.bhalf S q s).code < toLex (b.bhalf S p s).code) :
    ¬ (b.blockQuiver S hA V φ).plusSet S (b.vtx q) s (b.bhalf S q s) p := by
  intro hp
  set C := b.blockQuiver S hA V φ
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  have hvq : S.Valid (b.vtx q) s (b.bhalf S q s) := b.valid_bhalf S hA q s
  have hvp : S.Valid (b.vtx q) s (b.bhalf S p s) := hv ▸ b.valid_bhalf S hA p s
  have hle := S.plus_le_minus_of_lt (M := C.Mod hK') hvq hvp hlt
  have hx : C.ofFun hK' (Pi.single p y) ∈ S.plus (C.Mod hK') (b.vtx q) s (b.bhalf S q s) := by
    rw [C.plus_eq_blk hK']; exact C.single_mem_blk hK' hp y
  have hm := hle hx
  rw [C.minus_eq_blk hK'] at hm
  have hPM := b.PM_bhalf S hA φ p s
  rw [hv] at hPM
  have := hm p hPM.2
  have h2 : (Pi.single p y : Fin b.n → V) p = 0 := this
  rw [Pi.single_eq_same] at h2
  exact hy h2

end CWord

/-- **An allowed closed word through distinct vertices** over a gentle algebra gives
infinitely many bricks. -/
theorem MonomialData.not_isBrickFinite_of_closed_injective [IsAlgClosed k] [FiniteDimensional k B]
    (D : MonomialData k B) (hD : D.IsGentle)
    (x : D.Q.V) (ω : List (Letter D.Q)) (hne : ω ≠ []) (hwalk : D.Q.IsWalk x ω)
    (hend : D.Q.wend x ω = x) (hchain : ω.IsChain D.AllowedPair)
    (hcyc : D.AllowedPair (ω.getLast hne) (ω.head hne))
    (hinj : ∀ (i j : ℕ) (hi : i < ω.length) (hj : j < ω.length), (ω[i]).src = (ω[j]).src → i = j) :
    ¬ IsBrickFinite B := by
  obtain ⟨S⟩ := MonomialData.exists_signs (D := D) hD.1.2
  obtain ⟨b, hA, hK, hprim, hbL, hlt⟩ := D.exists_band_of_closed hD S x ω hne hwalk hend hchain hcyc
  have hv : Function.Injective b.vtx := by
    intro p q h
    have hp : p.val < ω.length := by have := p.isLt; omega
    have hq : q.val < ω.length := by have := q.isLt; omega
    have h' : (b.lt p).src = (b.lt q).src := h
    rw [hlt p hp, hlt q hq] at h'
    exact Fin.ext (hinj _ _ hp hq h')
  exact b.not_isBrickFinite S hA hK hprim 1 (b.isBrick_of_vtx_injective S hA hK hprim hv 1)

end BrickAccessibility
