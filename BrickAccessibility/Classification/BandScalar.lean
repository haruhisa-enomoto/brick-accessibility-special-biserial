module

public import BrickAccessibility.Classification.Decompose

/-!
# Band modules with a scalar twist

For a band `b` and `t ∈ kˣ`, the band module `M(b, t)` has `V = k` and twist `t`.
The vector `x₀ = single first 1` lies in the numerator but not the denominator of
the pair at `first`, and its chain around the band returns to `t • x₀`
(`chain_x0`). At a primitive band the pair functor at `first` is one-dimensional
(`finrank_F_first`), spanned by `x₀`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData.BlockQuiver

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
  (C : D.BlockQuiver V) (hC : C.KillsZeroPaths) (S : D.Signs)

/-- A block vector at a position whose maximal walks are `h`, `h'` lies in the numerator
but not in the denominator. -/
theorem single_mem_pnum {v : D.Q.V} {s : Bool} {h h' : HWord D.Q} {p : C.P}
    (h1 : C.PM S v s h p) (h2 : C.PM S v (!s) h' p) (y : V) :
    C.ofFun hC (Pi.single p y) ∈ S.pnum (C.Mod hC) v s h h' := by
  simp only [Signs.pnum, C.plus_eq_blk hC, C.blk_inf hC]
  exact C.single_mem_blk hC ⟨h1.1, h2.1⟩ y

theorem single_not_mem_pden {v : D.Q.V} {s : Bool} {h h' : HWord D.Q} {p : C.P}
    (h1 : C.PM S v s h p) (h2 : C.PM S v (!s) h' p) {y : V} (hy : y ≠ 0) :
    C.ofFun hC (Pi.single p y) ∉ S.pden (C.Mod hC) v s h h' := by
  classical
  simp only [Signs.pden, C.plus_eq_blk hC, C.minus_eq_blk hC, C.blk_inf hC, C.blk_sup hC]
  intro hm
  have := hm p (by
    rintro (⟨hm1, -⟩ | ⟨-, hm2⟩)
    · exact h1.2 hm1
    · exact h2.2 hm2)
  have h0 : (Pi.single p y : C.P → V) p = 0 := this
  simp at h0
  exact hy h0

theorem single_mem_vsp (p : C.P) (y : V) : C.ofFun hC (Pi.single p y) ∈ D.vsp (C.Mod hC) (C.vtx p) := by
  rw [vsp_eq]; exact C.single_mem_blk hC (J := fun j ↦ C.vtx j = C.vtx p) rfl y

end MonomialData.BlockQuiver

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)

/-- The scalar twist. -/
def tw (t : kˣ) : k ≃ₗ[k] k := LinearEquiv.smulOfUnit t

/-- The band module `M(b, t)`. -/
abbrev BM (t : kˣ) : Type u :=
  (b.blockQuiver S hA k (tw t)).Mod (b.blockQuiver_kills S hA hK k (tw t))

/-- The vector `1` at the first position. -/
def x0 (t : kˣ) : b.BM S hA hK t :=
  (b.blockQuiver S hA k (tw t)).ofFun (b.blockQuiver_kills S hA hK k (tw t)) (Pi.single b.first 1)

/-- The vector `1` at a position. -/
def xs (t : kˣ) (p : Fin b.n) : b.BM S hA hK t :=
  (b.blockQuiver S hA k (tw t)).ofFun (b.blockQuiver_kills S hA hK k (tw t)) (Pi.single p 1)

theorem xs_mem_vsp (t : kˣ) (p : Fin b.n) : b.xs S hA hK t p ∈ D.vsp (b.BM S hA hK t) (b.vtx p) :=
  (b.blockQuiver S hA k (tw t)).single_mem_vsp (b.blockQuiver_kills S hA hK k (tw t)) p 1

include hA in
/-- One step of the chain of block vectors. -/
theorem rel_xs (t : kˣ) (q : ℕ) (hq : q < b.n) :
    MonomialData.Rel (b.lt ⟨q, hq⟩) (b.xs S hA hK t ⟨q, hq⟩)
      (if h : q + 1 < b.n then b.xs S hA hK t ⟨q + 1, h⟩ else (t : k) • b.x0 S hA hK t) := by
  set C := b.blockQuiver S hA k (tw t)
  set hC := b.blockQuiver_kills S hA hK k (tw t)
  rcases hl : b.lt ⟨q, hq⟩ with ⟨a, d⟩
  cases d
  · -- an inverse letter: `a` moves `q + 1` to `q`
    have hn : C.next a (b.succ ⟨q, hq⟩) = some ⟨q, hq⟩ :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inr ⟨by rw [pred_succ]; exact hl, by rw [pred_succ]⟩)
    have hsrc : D.Q.src a = b.vtx (b.succ ⟨q, hq⟩) := by rw [← b.lt_tgt, hl]; rfl
    simp only [MonomialData.Rel, Bool.false_eq_true, if_false]
    split_ifs with h
    · have e : b.succ ⟨q, hq⟩ = ⟨q + 1, h⟩ := Fin.ext (b.succ_val_of_lt _ h)
      rw [e] at hn hsrc
      refine ⟨hsrc ▸ b.xs_mem_vsp S hA hK t _, ?_⟩
      have := MonomialData.BlockQuiver.α_smul_single C hC hn 1
      rw [show C.g a ⟨q + 1, h⟩ 1 = 1 by
        have := b.g_false S hA (tw t) (i := ⟨q, hq⟩) h hl 1
        rwa [e] at this] at this
      exact this.symm
    · have hql : (⟨q, hq⟩ : Fin b.n) = b.last := Fin.ext (by simp only [last]; omega)
      have hl' : b.lt b.last = (a, false) := by rw [← hql]; exact hl
      have e : b.succ ⟨q, hq⟩ = b.first := by rw [hql, succ_last]
      rw [e] at hn hsrc
      refine ⟨hsrc ▸ Submodule.smul_mem _ _ (b.xs_mem_vsp S hA hK t _), ?_⟩
      rw [x0, smul_comm, MonomialData.BlockQuiver.α_smul_single C hC hn 1]
      have hg : C.g a b.first 1 = (t : k)⁻¹ := by
        have h1 : ¬ (b.first = b.last ∧ b.lt b.last = (a, true)) := by
          rintro ⟨-, h'⟩; rw [hl'] at h'; simp at h'
        simp only [C, blockQuiver]
        rw [if_neg h1, if_pos ⟨trivial, hl'⟩]
        simp [tw, LinearEquiv.smulOfUnit, Units.smul_def]
      rw [hg, xs, hql]
      show Pi.single b.last 1 = (t : k) • Pi.single b.last (t : k)⁻¹
      rw [← Pi.single_smul, smul_eq_mul, mul_inv_cancel₀ t.ne_zero]
  · -- a direct letter: `a` moves `q` to `q + 1`
    have hn : C.next a ⟨q, hq⟩ = some (b.succ ⟨q, hq⟩) :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inl ⟨hl, rfl⟩)
    have hsrc : D.Q.src a = b.vtx ⟨q, hq⟩ := by simp [vtx, hl, Letter.src]
    simp only [MonomialData.Rel, if_true]
    refine ⟨hsrc ▸ b.xs_mem_vsp S hA hK t _, ?_⟩
    rw [xs, MonomialData.BlockQuiver.α_smul_single C hC hn 1]
    split_ifs with h
    · have e : b.succ ⟨q, hq⟩ = ⟨q + 1, h⟩ := Fin.ext (b.succ_val_of_lt _ h)
      rw [e, b.g_true S hA (tw t) h hl]; rfl
    · have hql : (⟨q, hq⟩ : Fin b.n) = b.last := Fin.ext (by simp only [last]; omega)
      have hl' : b.lt b.last = (a, true) := by rw [← hql]; exact hl
      have hg : C.g a ⟨q, hq⟩ 1 = (t : k) := by
        simp only [C, blockQuiver]
        rw [if_pos ⟨hql, hl'⟩]
        simp [tw, LinearEquiv.smulOfUnit, Units.smul_def]
      rw [hg, hql, succ_last, x0]
      show (t : k) • Pi.single b.first (1 : k) = Pi.single b.first (t : k)
      rw [← Pi.single_smul, smul_eq_mul, mul_one]

include hA in
/-- The chain of `x₀` around the band returns to `t • x₀`. -/
theorem chain_x0 (t : kˣ) :
    b.Ch (b.BM S hA hK t) b.first b.n (b.x0 S hA hK t) ((t : k) • b.x0 S hA hK t) := by
  let c : ℕ → b.BM S hA hK t := fun q ↦
    if h : q < b.n then b.xs S hA hK t ⟨q, h⟩ else (t : k) • b.x0 S hA hK t
  have h := b.ch_of_fun (b.BM S hA hK t) c (p := b.first) (i := 0) (m := b.n) (fun q _ hq ↦ by
    have hq' : q < b.n := by omega
    rw [b.iter_first q hq']
    have := b.rel_xs S hA hK t q hq'
    simp only [c, dif_pos hq']
    exact this)
  have h0 : c 0 = b.x0 S hA hK t := by simp only [c, dif_pos b.n_pos]; rfl
  have hn : c b.n = (t : k) • b.x0 S hA hK t := by simp [c]
  simp only [Nat.zero_add, Function.iterate_zero, id] at h
  rwa [h0, hn] at h

include hA in
theorem x0_mem_numB (t : kˣ) : b.x0 S hA hK t ∈ b.numB S (b.BM S hA hK t) b.first :=
  (b.blockQuiver S hA k (tw t)).single_mem_pnum (b.blockQuiver_kills S hA hK k (tw t)) S
    (b.PM_rightW S hA (tw t) b.first) (b.PM_leftW S hA (tw t) b.first) 1

include hA in
theorem x0_not_mem_denB (t : kˣ) : b.x0 S hA hK t ∉ b.denB S (b.BM S hA hK t) b.first :=
  (b.blockQuiver S hA k (tw t)).single_not_mem_pden (b.blockQuiver_kills S hA hK k (tw t)) S
    (b.PM_rightW S hA (tw t) b.first) (b.PM_leftW S hA (tw t) b.first) one_ne_zero

include hA in
/-- At a primitive band, the pair functor of `M(b, t)` at `first` is one-dimensional. -/
theorem finrank_F_first (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (t : kˣ) :
    finrank k (b.numB S (b.BM S hA hK t) b.first) -
      finrank k (b.denB S (b.BM S hA hK t) b.first) = 1 := by
  classical
  have h := b.band_gr_eq S hA (tw t) hK (b.valid_rightW S hA b.first) (b.valid_leftW S hA b.first)
  have hc := b.card_eq S hA hprim (b.vtx b.first, S.st (b.lt b.first), .inf (b.rightW b.first),
    .inf (b.leftW b.first))
  simp only at hc
  rw [hc, if_pos ⟨b.first, S.st (b.lt b.first), by simp [pairAt, bhalf_self, bhalf_not]⟩] at h
  rw [numB_eq_pnum, denB]
  simpa using h

include hA in
/-- At a primitive band, the numerator at `first` is spanned by `x₀` modulo the
denominator. -/
theorem numB_le_span (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (t : kˣ) :
    b.numB S (b.BM S hA hK t) b.first ≤
      Submodule.span k {b.x0 S hA hK t} ⊔ b.denB S (b.BM S hA hK t) b.first := by
  have h2 := b.finrank_F_first S hA hK hprim t
  have h3 := Submodule.finrank_mono (b.denB_le_numB S (b.BM S hA hK t) hA b.first)
  set N := b.numB S (b.BM S hA hK t) b.first
  set Dn := b.denB S (b.BM S hA hK t) b.first
  have hle : Submodule.span k {b.x0 S hA hK t} ⊔ Dn ≤ N :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (b.x0_mem_numB S hA hK t))
      (b.denB_le_numB S (b.BM S hA hK t) hA b.first)
  have hinf : Submodule.span k {b.x0 S hA hK t} ⊓ Dn = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((Submodule.smul_mem_iff _ hc).mp hx2) (b.x0_not_mem_denB S hA hK t)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span k {b.x0 S hA hK t}) Dn
  rw [hinf, finrank_bot, finrank_span_singleton (fun h ↦ b.x0_not_mem_denB S hA hK t
    (by rw [h]; exact Submodule.zero_mem _))] at h1
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
  omega

section Maps

variable {M N : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
  [AddCommGroup N] [Module B N] [Module k N] [IsScalarTower k B N]

omit hA hK in
theorem rel_map (f : M →ₗ[B] N) {l : Letter D.Q} {x y : M} (h : MonomialData.Rel l x y) :
    MonomialData.Rel l (f x) (f y) := by
  have hv : ∀ {v : D.Q.V} {m : M}, m ∈ D.vsp M v → f m ∈ D.vsp N v := fun hm ↦ by
    rw [D.mem_vsp] at hm ⊢; rw [← map_smul, hm]
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [MonomialData.Rel, Bool.false_eq_true, if_false] at h ⊢
    exact ⟨hv h.1, by rw [h.2, map_smul]⟩
  · simp only [MonomialData.Rel, if_true] at h ⊢
    exact ⟨hv h.1, by rw [h.2, map_smul]⟩

omit hA hK in
theorem ch_map (f : M →ₗ[B] N) {p : Fin b.n} {m : ℕ} {x y : M} (h : b.Ch M p m x y) :
    b.Ch N p m (f x) (f y) := by
  induction m generalizing p x with
  | zero => exact (ch_zero_len b N).mpr (by rw [(ch_zero_len b M).mp h])
  | succ m ih =>
      obtain ⟨z, hz, hr⟩ := h
      exact ⟨f z, rel_map f hz, ih hr⟩

end Maps

include hA in
/-- **Band modules with different twists are not isomorphic.** -/
theorem eq_of_equiv (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) {t t' : kˣ}
    (e : b.BM S hA hK t ≃ₗ[B] b.BM S hA hK t') : t = t' := by
  set M' := b.BM S hA hK t'
  set y := e (b.x0 S hA hK t)
  have hy : b.Ch M' b.first b.n y ((t : k) • y) := by
    have := b.ch_map e.toLinearMap (b.chain_x0 S hA hK t)
    simpa [y] using this
  have hyn : y ∈ b.numB S M' b.first :=
    S.map_pnum_le _ e.toLinearMap _ _ _ _ ⟨_, b.x0_mem_numB S hA hK t, rfl⟩
  have hyd : y ∉ b.denB S M' b.first := by
    intro h
    apply b.x0_not_mem_denB S hA hK t
    have := S.map_pden_le M' e.symm.toLinearMap _ _ _ _ ⟨y, h, rfl⟩
    simp only [y, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at this
    exact this
  obtain ⟨w, hw, d, hd, hyd'⟩ := Submodule.mem_sup.mp (b.numB_le_span S hA hK hprim t' hyn)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hc : c ≠ 0 := by
    rintro rfl
    apply hyd
    rw [← hyd', zero_smul, zero_add]; exact hd
  set x0' := b.x0 S hA hK t'
  have hdn : d ∈ b.numB S M' b.first := b.denB_le_numB S M' hA b.first hd
  obtain ⟨d', hd'n, hdd'⟩ := b.bandRel_dom S hA M' b.first d hdn
  have hdK : d ∈ Split.Kinf (bandRel M' b.first) (b.numB S M' b.first) := by
    rw [← b.denB_eq S hA M' b.first]; exact hd
  have hd'K := Split.fwd_mem (b.bandRel_dom S hA M' b.first) (b.bandRel_ran S hA M' b.first)
    hdK hd'n hdd'
  -- two chains from `y`
  have h1 : b.Ch M' b.first b.n y (c • ((t' : k) • x0') + d') := by
    rw [← hyd']
    exact b.ch_add M' (b.ch_smul M' c (b.chain_x0 S hA hK t')) hdd'
  have h0 : b.Ch M' b.first (1 * b.n) 0 ((t : k) • y - (c • ((t' : k) • x0') + d')) := by
    rw [one_mul]
    have := b.ch_add M' hy (b.ch_smul M' (-1 : k) h1)
    have e1 : y + (-1 : k) • y = 0 := by simp
    have e2 : (t : k) • y + (-1 : k) • (c • ((t' : k) • x0') + d') =
        (t : k) • y - (c • ((t' : k) • x0') + d') := by simp [sub_eq_add_neg]; abel
    rwa [e1, e2] at this
  have hz : (t : k) • y - (c • ((t' : k) • x0') + d') ∈ b.numB S M' b.first :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hyn) (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (b.x0_mem_numB S hA hK t'))) hd'n)
  have hzK := b.Kinf_of_ch_zero S hA M' hz h0
  rw [← b.denB_eq S hA M' b.first] at hzK hd'K
  -- conclude
  by_contra hne
  have htt : (t : k) - (t' : k) ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (Units.ext h)
  have : (c * ((t : k) - (t' : k))) • x0' ∈ b.denB S M' b.first := by
    have e2 : (c * ((t : k) - (t' : k))) • x0' =
        ((t : k) • y - (c • ((t' : k) • x0') + d')) - (t : k) • d + d' := by
      rw [← hyd']
      simp only [smul_add, smul_smul, sub_smul, mul_sub]
      abel_nf
      rw [mul_comm c (t : k)]
      abel
    rw [e2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ hzK (Submodule.smul_mem _ _ hd)) hd'K
  exact b.x0_not_mem_denB S hA hK t' ((Submodule.smul_mem_iff _ (mul_ne_zero hc htt)).mp this)

end CWord

end BrickAccessibility
