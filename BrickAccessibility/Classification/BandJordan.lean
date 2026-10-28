module

public import BrickAccessibility.Classification.BrickPieces
public import BrickAccessibility.Classification.Jordan

/-!
# Band modules of every rank

For a band `b` (alternating, killing zero paths, primitive), a multiplicity space `V` and a
twist `φ ∈ GL(V)`, `b.BMV S hA hK φ` is the band block module. The band module
`M(ω, μ, n)` of the paper is `b.bandModule S hA hK n μ`, the block module with twist the
Jordan block `J_n(μ)` (`jordanEquiv`).

At the first position, the numerator of the pair functor splits as `ι(V) ⊕ denB`
(`exists_unique_split`), where `ι` places a vector in the first block. A module map `g`
between band block modules therefore induces `hat g : V → V'`, which intertwines the twists
(`hat_comm`, by following the chain around the band) and is functorial (`hat_comp`). This
gives:

* `isIndecomposable_BMV`: `M(V, φ)` is indecomposable if `φ` has no nontrivial commuting
  idempotent; in particular every `M(ω, μ, n)` is indecomposable (`isIndecomposable_bandModule`);
* `conj_of_equiv`: isomorphic band block modules have similar twists; in particular
  `M(ω, μ, n) ≅ M(ω, μ', n)` forces `μ = μ'` (`eq_of_bandModule_equiv`);
* `exists_equiv_bandModule`: over an algebraically closed field every indecomposable band
  block module is some `M(ω, μ, n)`.
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

section Block

variable {V : Type u} [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] V)

/-- The band block module with multiplicity space `V` and twist `φ`. -/
abbrev BMV : Type u := (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ)

/-- A vector `y` placed at position `p`. -/
def xv (p : Fin b.n) (y : V) : b.BMV S hA hK φ :=
  (b.blockQuiver S hA V φ).ofFun (b.blockQuiver_kills S hA hK V φ) (Pi.single p y)

/-- The first block. -/
def ι : V →ₗ[k] b.BMV S hA hK φ :=
  ((b.blockQuiver S hA V φ).ofFunL (b.blockQuiver_kills S hA hK V φ)).comp
    (LinearMap.single k (fun _ : Fin b.n ↦ V) b.first)

theorem ι_apply (y : V) : b.ι S hA hK φ y = b.xv S hA hK φ b.first y := rfl

theorem xv_mem_vsp (p : Fin b.n) (y : V) : b.xv S hA hK φ p y ∈ D.vsp (b.BMV S hA hK φ) (b.vtx p) :=
  (b.blockQuiver S hA V φ).single_mem_vsp (b.blockQuiver_kills S hA hK V φ) p y

theorem ι_injective : Function.Injective (b.ι S hA hK φ) := by
  intro y y' h
  have h' : (Pi.single b.first y : Fin b.n → V) b.first =
      (Pi.single b.first y' : Fin b.n → V) b.first := congrFun h b.first
  simpa using h'

include hA in
/-- One step of the chain of a block vector. -/
theorem rel_xv (y : V) (q : ℕ) (hq : q < b.n) :
    MonomialData.Rel (b.lt ⟨q, hq⟩) (b.xv S hA hK φ ⟨q, hq⟩ y)
      (if h : q + 1 < b.n then b.xv S hA hK φ ⟨q + 1, h⟩ y else b.ι S hA hK φ (φ y)) := by
  set C := b.blockQuiver S hA V φ
  set hC := b.blockQuiver_kills S hA hK V φ
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
      refine ⟨hsrc ▸ b.xv_mem_vsp S hA hK φ _ y, ?_⟩
      have := MonomialData.BlockQuiver.α_smul_single C hC hn y
      rw [show C.g a ⟨q + 1, h⟩ y = y by
        have := b.g_false S hA φ (i := ⟨q, hq⟩) h hl y
        rwa [e] at this] at this
      exact this.symm
    · have hql : (⟨q, hq⟩ : Fin b.n) = b.last := Fin.ext (by simp only [last]; omega)
      have hl' : b.lt b.last = (a, false) := by rw [← hql]; exact hl
      have e : b.succ ⟨q, hq⟩ = b.first := by rw [hql, succ_last]
      rw [e] at hn hsrc
      refine ⟨hsrc ▸ b.xv_mem_vsp S hA hK φ _ (φ y), ?_⟩
      show C.ofFun hC (Pi.single ⟨q, hq⟩ y) = D.α a • C.ofFun hC (Pi.single b.first (φ y))
      rw [MonomialData.BlockQuiver.α_smul_single C hC hn (φ y)]
      have hg : C.g a b.first (φ y) = y := by
        have h1 : ¬ (b.first = b.last ∧ b.lt b.last = (a, true)) := by
          rintro ⟨-, h'⟩; rw [hl'] at h'; simp at h'
        simp only [C, blockQuiver]
        rw [if_neg h1, if_pos ⟨trivial, hl'⟩]
        simp
      rw [hg, hql]
  · -- a direct letter: `a` moves `q` to `q + 1`
    have hn : C.next a ⟨q, hq⟩ = some (b.succ ⟨q, hq⟩) :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inl ⟨hl, rfl⟩)
    have hsrc : D.Q.src a = b.vtx ⟨q, hq⟩ := by simp [vtx, hl, Letter.src]
    simp only [MonomialData.Rel, if_true]
    refine ⟨hsrc ▸ b.xv_mem_vsp S hA hK φ _ y, ?_⟩
    rw [xv, MonomialData.BlockQuiver.α_smul_single C hC hn y]
    split_ifs with h
    · have e : b.succ ⟨q, hq⟩ = ⟨q + 1, h⟩ := Fin.ext (b.succ_val_of_lt _ h)
      rw [e, b.g_true S hA φ h hl]; rfl
    · have hql : (⟨q, hq⟩ : Fin b.n) = b.last := Fin.ext (by simp only [last]; omega)
      have hl' : b.lt b.last = (a, true) := by rw [← hql]; exact hl
      have hg : C.g a ⟨q, hq⟩ y = φ y := by
        simp only [C, blockQuiver]
        rw [if_pos ⟨hql, hl'⟩]
      rw [hg, hql, succ_last]
      rfl

include hA in
/-- **The chain of `ι y` around the band returns to `ι (φ y)`.** -/
theorem chain_ι (y : V) :
    b.Ch (b.BMV S hA hK φ) b.first b.n (b.ι S hA hK φ y) (b.ι S hA hK φ (φ y)) := by
  let c : ℕ → b.BMV S hA hK φ := fun q ↦
    if h : q < b.n then b.xv S hA hK φ ⟨q, h⟩ y else b.ι S hA hK φ (φ y)
  have h := b.ch_of_fun (b.BMV S hA hK φ) c (p := b.first) (i := 0) (m := b.n) (fun q _ hq ↦ by
    have hq' : q < b.n := by omega
    rw [b.iter_first q hq']
    have := b.rel_xv S hA hK φ y q hq'
    simp only [c, dif_pos hq']
    exact this)
  have h0 : c 0 = b.ι S hA hK φ y := by simp only [c, dif_pos b.n_pos]; rfl
  have hn : c b.n = b.ι S hA hK φ (φ y) := by simp [c]
  simp only [Nat.zero_add, Function.iterate_zero, id] at h
  rwa [h0, hn] at h

include hA in
theorem ι_mem_numB (y : V) : b.ι S hA hK φ y ∈ b.numB S (b.BMV S hA hK φ) b.first :=
  (b.blockQuiver S hA V φ).single_mem_pnum (b.blockQuiver_kills S hA hK V φ) S
    (b.PM_rightW S hA φ b.first) (b.PM_leftW S hA φ b.first) y

include hA in
theorem ι_mem_denB_iff {y : V} : b.ι S hA hK φ y ∈ b.denB S (b.BMV S hA hK φ) b.first ↔ y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]; exact Submodule.zero_mem _⟩
  by_contra hy
  exact (b.blockQuiver S hA V φ).single_not_mem_pden (b.blockQuiver_kills S hA hK V φ) S
    (b.PM_rightW S hA φ b.first) (b.PM_leftW S hA φ b.first) hy h

variable [FiniteDimensional k V]

include hA in
/-- At a primitive band, the pair functor at `first` has the dimension of `V`. -/
theorem finrank_F_first_V (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) :
    finrank k (b.numB S (b.BMV S hA hK φ) b.first) -
      finrank k (b.denB S (b.BMV S hA hK φ) b.first) = finrank k V := by
  classical
  have h := b.band_gr_eq S hA φ hK (b.valid_rightW S hA b.first) (b.valid_leftW S hA b.first)
  have hc := b.card_eq S hA hprim (b.vtx b.first, S.st (b.lt b.first), .inf (b.rightW b.first),
    .inf (b.leftW b.first))
  simp only at hc
  rw [hc, if_pos ⟨b.first, S.st (b.lt b.first), by simp [pairAt, bhalf_self, bhalf_not]⟩] at h
  rw [numB_eq_pnum, denB]
  simpa using h

include hA in
/-- At a primitive band, the numerator at `first` is `ι(V)` modulo the denominator. -/
theorem numB_le_sup (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) :
    b.numB S (b.BMV S hA hK φ) b.first ≤
      LinearMap.range (b.ι S hA hK φ) ⊔ b.denB S (b.BMV S hA hK φ) b.first := by
  have h2 := b.finrank_F_first_V S hA hK φ hprim
  have h3 := Submodule.finrank_mono (b.denB_le_numB S (b.BMV S hA hK φ) hA b.first)
  set N := b.numB S (b.BMV S hA hK φ) b.first
  set Dn := b.denB S (b.BMV S hA hK φ) b.first
  have hle : LinearMap.range (b.ι S hA hK φ) ⊔ Dn ≤ N :=
    sup_le (by rintro _ ⟨y, rfl⟩; exact b.ι_mem_numB S hA hK φ y)
      (b.denB_le_numB S (b.BMV S hA hK φ) hA b.first)
  have hinf : LinearMap.range (b.ι S hA hK φ) ⊓ Dn = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨⟨y, rfl⟩, hx2⟩ := Submodule.mem_inf.mp hx
    rw [(b.ι_mem_denB_iff S hA hK φ).mp hx2, map_zero]
    exact Submodule.zero_mem _
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (b.ι S hA hK φ)) Dn
  rw [hinf, finrank_bot, LinearMap.finrank_range_of_inj (b.ι_injective S hA hK φ)] at h1
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
  omega

include hA in
/-- **The splitting** `numB = ι(V) ⊕ denB` at `first`. -/
theorem exists_unique_split (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q)
    {x : b.BMV S hA hK φ} (hx : x ∈ b.numB S (b.BMV S hA hK φ) b.first) :
    ∃! y : V, x - b.ι S hA hK φ y ∈ b.denB S (b.BMV S hA hK φ) b.first := by
  obtain ⟨_, ⟨y, rfl⟩, d, hd, rfl⟩ := Submodule.mem_sup.mp (b.numB_le_sup S hA hK φ hprim hx)
  refine ⟨y, by simpa using hd, fun y' hy' ↦ ?_⟩
  have : b.ι S hA hK φ (y - y') ∈ b.denB S (b.BMV S hA hK φ) b.first := by
    have e : b.ι S hA hK φ (y - y') = (b.ι S hA hK φ y + d - b.ι S hA hK φ y') - d := by
      rw [map_sub]; abel
    rw [e]; exact Submodule.sub_mem _ hy' hd
  exact (sub_eq_zero.mp ((b.ι_mem_denB_iff S hA hK φ).mp this)).symm

end Block

section Hat

variable {V V' V'' : Type u} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
  [AddCommGroup V''] [Module k V''] [FiniteDimensional k V'']
  (φ : V ≃ₗ[k] V) (φ' : V' ≃ₗ[k] V') (φ'' : V'' ≃ₗ[k] V'')
  (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q)

omit [FiniteDimensional k V'] in
theorem map_numB (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') {x : b.BMV S hA hK φ}
    (hx : x ∈ b.numB S (b.BMV S hA hK φ) b.first) : g x ∈ b.numB S (b.BMV S hA hK φ') b.first :=
  S.map_pnum_le _ g _ _ _ _ ⟨x, hx, rfl⟩

omit [FiniteDimensional k V'] in
theorem map_denB (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') {x : b.BMV S hA hK φ}
    (hx : x ∈ b.denB S (b.BMV S hA hK φ) b.first) : g x ∈ b.denB S (b.BMV S hA hK φ') b.first :=
  S.map_pden_le _ g _ _ _ _ ⟨x, hx, rfl⟩

/-- The value of the induced map on multiplicity spaces. -/
def hatF (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') (y : V) : V' :=
  (b.exists_unique_split S hA hK φ' hprim
    (b.map_numB S hA hK φ φ' g (b.ι_mem_numB S hA hK φ y))).exists.choose

theorem hatF_spec (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') (y : V) :
    g (b.ι S hA hK φ y) - b.ι S hA hK φ' (b.hatF S hA hK φ φ' hprim g y) ∈
      b.denB S (b.BMV S hA hK φ') b.first :=
  (b.exists_unique_split S hA hK φ' hprim
    (b.map_numB S hA hK φ φ' g (b.ι_mem_numB S hA hK φ y))).exists.choose_spec

theorem hatF_eq (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') {y : V} {y' : V'}
    (h : g (b.ι S hA hK φ y) - b.ι S hA hK φ' y' ∈ b.denB S (b.BMV S hA hK φ') b.first) :
    b.hatF S hA hK φ φ' hprim g y = y' :=
  (b.exists_unique_split S hA hK φ' hprim
    (b.map_numB S hA hK φ φ' g (b.ι_mem_numB S hA hK φ y))).unique
    (b.hatF_spec S hA hK φ φ' hprim g y) h

/-- **The map induced on multiplicity spaces** by a map of band block modules. -/
def hat (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') : V →ₗ[k] V' where
  toFun := b.hatF S hA hK φ φ' hprim g
  map_add' y z := by
    refine b.hatF_eq S hA hK φ φ' hprim g ?_
    have e : g (b.ι S hA hK φ (y + z)) - b.ι S hA hK φ' (b.hatF S hA hK φ φ' hprim g y +
        b.hatF S hA hK φ φ' hprim g z) =
        (g (b.ι S hA hK φ y) - b.ι S hA hK φ' (b.hatF S hA hK φ φ' hprim g y)) +
        (g (b.ι S hA hK φ z) - b.ι S hA hK φ' (b.hatF S hA hK φ φ' hprim g z)) := by
      simp only [map_add]; abel
    rw [e]
    exact Submodule.add_mem _ (b.hatF_spec S hA hK φ φ' hprim g y)
      (b.hatF_spec S hA hK φ φ' hprim g z)
  map_smul' c y := by
    rw [RingHom.id_apply]
    refine b.hatF_eq S hA hK φ φ' hprim g ?_
    have e : g (b.ι S hA hK φ (c • y)) - b.ι S hA hK φ' (c • b.hatF S hA hK φ φ' hprim g y) =
        c • (g (b.ι S hA hK φ y) - b.ι S hA hK φ' (b.hatF S hA hK φ φ' hprim g y)) := by
      rw [map_smul, g.map_smul_of_tower, map_smul, smul_sub]
    rw [e]
    exact Submodule.smul_mem _ _ (b.hatF_spec S hA hK φ φ' hprim g y)

theorem hat_spec (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') (y : V) :
    g (b.ι S hA hK φ y) - b.ι S hA hK φ' (b.hat S hA hK φ φ' hprim g y) ∈
      b.denB S (b.BMV S hA hK φ') b.first :=
  b.hatF_spec S hA hK φ φ' hprim g y

theorem hat_eq (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') {y : V} {y' : V'}
    (h : g (b.ι S hA hK φ y) - b.ι S hA hK φ' y' ∈ b.denB S (b.BMV S hA hK φ') b.first) :
    b.hat S hA hK φ φ' hprim g y = y' :=
  b.hatF_eq S hA hK φ φ' hprim g h

/-- **The induced map intertwines the twists**, by following the chain around the band. -/
theorem hat_comm (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') (y : V) :
    b.hat S hA hK φ φ' hprim g (φ y) = φ' (b.hat S hA hK φ φ' hprim g y) := by
  set M' := b.BMV S hA hK φ'
  set z := b.hat S hA hK φ φ' hprim g y
  set d := g (b.ι S hA hK φ y) - b.ι S hA hK φ' z
  have hd : d ∈ b.denB S M' b.first := b.hat_spec S hA hK φ φ' hprim g y
  have hdn : d ∈ b.numB S M' b.first := b.denB_le_numB S M' hA b.first hd
  obtain ⟨d', hd'n, hdd'⟩ := b.bandRel_dom S hA M' b.first d hdn
  have hdK : d ∈ Split.Kinf (bandRel M' b.first) (b.numB S M' b.first) := by
    rw [← b.denB_eq S hA M' b.first]; exact hd
  have hd'K := Split.fwd_mem (b.bandRel_dom S hA M' b.first) (b.bandRel_ran S hA M' b.first)
    hdK hd'n hdd'
  rw [← b.denB_eq S hA M' b.first] at hd'K
  have h1 : b.Ch M' b.first b.n (g (b.ι S hA hK φ y)) (g (b.ι S hA hK φ (φ y))) :=
    b.ch_map g (b.chain_ι S hA hK φ y)
  have h2 : b.Ch M' b.first b.n (g (b.ι S hA hK φ y)) (b.ι S hA hK φ' (φ' z) + d') := by
    have e : g (b.ι S hA hK φ y) = b.ι S hA hK φ' z + d := by simp [d]
    rw [e]
    exact b.ch_add M' (b.chain_ι S hA hK φ' z) hdd'
  have h0 : b.Ch M' b.first (1 * b.n) 0
      (g (b.ι S hA hK φ (φ y)) - (b.ι S hA hK φ' (φ' z) + d')) := by
    rw [one_mul]
    have := b.ch_add M' h1 (b.ch_smul M' (-1 : k) h2)
    have e1 : g (b.ι S hA hK φ y) + (-1 : k) • g (b.ι S hA hK φ y) = 0 := by simp
    have e2 : g (b.ι S hA hK φ (φ y)) + (-1 : k) • (b.ι S hA hK φ' (φ' z) + d') =
        g (b.ι S hA hK φ (φ y)) - (b.ι S hA hK φ' (φ' z) + d') := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rwa [e1, e2] at this
  have hz : g (b.ι S hA hK φ (φ y)) - (b.ι S hA hK φ' (φ' z) + d') ∈ b.numB S M' b.first :=
    Submodule.sub_mem _ (b.map_numB S hA hK φ φ' g (b.ι_mem_numB S hA hK φ _))
      (Submodule.add_mem _ (b.ι_mem_numB S hA hK φ' _) hd'n)
  have hzK := b.Kinf_of_ch_zero S hA M' hz h0
  rw [← b.denB_eq S hA M' b.first] at hzK
  refine b.hat_eq S hA hK φ φ' hprim g ?_
  have e : g (b.ι S hA hK φ (φ y)) - b.ι S hA hK φ' (φ' z) =
      (g (b.ι S hA hK φ (φ y)) - (b.ι S hA hK φ' (φ' z) + d')) + d' := by abel
  rw [e]
  exact Submodule.add_mem _ hzK hd'K

theorem hat_comp (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ')
    (h : b.BMV S hA hK φ' →ₗ[B] b.BMV S hA hK φ'') :
    b.hat S hA hK φ φ'' hprim (h ∘ₗ g) =
      b.hat S hA hK φ' φ'' hprim h ∘ₗ b.hat S hA hK φ φ' hprim g := by
  refine LinearMap.ext fun y ↦ b.hat_eq S hA hK φ φ'' hprim _ ?_
  set z := b.hat S hA hK φ φ' hprim g y
  show h (g (b.ι S hA hK φ y)) - b.ι S hA hK φ'' (b.hat S hA hK φ' φ'' hprim h z) ∈ _
  have e : h (g (b.ι S hA hK φ y)) - b.ι S hA hK φ'' (b.hat S hA hK φ' φ'' hprim h z) =
      h (g (b.ι S hA hK φ y) - b.ι S hA hK φ' z) +
        (h (b.ι S hA hK φ' z) - b.ι S hA hK φ'' (b.hat S hA hK φ' φ'' hprim h z)) := by
    simp only [map_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (b.map_denB S hA hK φ' φ'' h (b.hat_spec S hA hK φ φ' hprim g y))
    (b.hat_spec S hA hK φ' φ'' hprim h z)

theorem hat_id [FiniteDimensional k V] : b.hat S hA hK φ φ hprim LinearMap.id = LinearMap.id :=
  LinearMap.ext fun y ↦ b.hat_eq S hA hK φ φ hprim _ (by simp)

theorem hat_sub (g h : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ') :
    b.hat S hA hK φ φ' hprim (g - h) =
      b.hat S hA hK φ φ' hprim g - b.hat S hA hK φ φ' hprim h := by
  refine LinearMap.ext fun y ↦ b.hat_eq S hA hK φ φ' hprim _ ?_
  have e : (g - h) (b.ι S hA hK φ y) - b.ι S hA hK φ' ((b.hat S hA hK φ φ' hprim g -
      b.hat S hA hK φ φ' hprim h) y) =
      (g (b.ι S hA hK φ y) - b.ι S hA hK φ' (b.hat S hA hK φ φ' hprim g y)) -
        (h (b.ι S hA hK φ y) - b.ι S hA hK φ' (b.hat S hA hK φ φ' hprim h y)) := by
    simp only [LinearMap.sub_apply, map_sub]; abel
  rw [e]
  exact Submodule.sub_mem _ (b.hat_spec S hA hK φ φ' hprim g y)
    (b.hat_spec S hA hK φ φ' hprim h y)

/-- A map with vanishing induced map kills the pair functor at `first`. -/
theorem kill_of_hat [FiniteDimensional k V] (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ')
    (h0 : b.hat S hA hK φ φ' hprim g = 0) :
    ∀ x ∈ b.numB S (b.BMV S hA hK φ) b.first, g x ∈ b.denB S (b.BMV S hA hK φ') b.first := by
  intro x hx
  obtain ⟨_, ⟨y, rfl⟩, d, hd, rfl⟩ := Submodule.mem_sup.mp (b.numB_le_sup S hA hK φ hprim hx)
  rw [map_add]
  refine Submodule.add_mem _ ?_ (b.map_denB S hA hK φ φ' g hd)
  have := b.hat_spec S hA hK φ φ' hprim g y
  rwa [h0, LinearMap.zero_apply, map_zero, sub_zero] at this

end Hat

section Indec

variable {V V' : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
  (φ : V ≃ₗ[k] V) (φ' : V' ≃ₗ[k] V')
  (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q)

include hA hprim in
/-- An idempotent endomorphism of `M(V, φ)` killing the pair functor at `first` is zero. -/
theorem eq_zero_of_kill_V (g : b.BMV S hA hK φ →ₗ[B] b.BMV S hA hK φ) (hidem : ∀ x, g (g x) = g x)
    (h0 : ∀ x ∈ b.numB S (b.BMV S hA hK φ) b.first, g x ∈ b.denB S (b.BMV S hA hK φ) b.first) :
    g = 0 := by
  classical
  set X := b.BMV S hA hK φ
  have hall := b.kill_all S hA g h0
  have hpair : ∀ (v : D.Q.V) (t1 : S.HW v true) (t2 : S.HW v (!true)),
      S.pnum X v true t1.1 t2.1 ≤ LinearMap.ker (g.restrictScalars k) ⊔ S.pden X v true t1.1 t2.1 := by
    intro v t1 t2 x hx
    have hgx : g x ∈ S.pden X v true t1.1 t2.1 := by
      by_cases hle : S.pnum X v true t1.1 t2.1 ≤ S.pden X v true t1.1 t2.1
      · exact hle (S.map_pnum_le _ g _ _ _ _ ⟨x, hx, rfl⟩)
      · have h := b.band_gr_eq S hA φ hK t1.2 t2.2
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

include hprim in
/-- **A band block module is indecomposable** when its twist has no nontrivial commuting
idempotent. -/
theorem isIndecomposable_BMV [Nontrivial V] (hind : IdemIndec φ.toLinearMap) :
    IsIndecomposable B (b.BMV S hA hK φ) := by
  set X := b.BMV S hA hK φ
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  refine ⟨⟨⟨b.ι S hA hK φ y, 0, fun h ↦ hy (b.ι_injective S hA hK φ (by rw [h, map_zero]))⟩⟩,
    fun A A' hc ↦ ?_⟩
  set g := A.projection A' hc
  have hidem : ∀ x, g (g x) = g x := fun x ↦
    Submodule.projection_apply_of_mem_left hc (Submodule.projection_apply_mem hc x)
  have hgg : g ∘ₗ g = g := LinearMap.ext hidem
  have hidemH : IsIdempotentElem (b.hat S hA hK φ φ hprim g) := by
    show b.hat S hA hK φ φ hprim g ∘ₗ b.hat S hA hK φ φ hprim g = _
    rw [← b.hat_comp, hgg]
  have hcommH : b.hat S hA hK φ φ hprim g ∘ₗ φ.toLinearMap =
      φ.toLinearMap ∘ₗ b.hat S hA hK φ φ hprim g :=
    LinearMap.ext fun y ↦ b.hat_comm S hA hK φ φ hprim g y
  rcases hind _ hcommH hidemH with h0 | h1
  · left
    have hg0 : g = 0 := b.eq_zero_of_kill_V S hA hK φ hprim g hidem
      (b.kill_of_hat S hA hK φ φ hprim g h0)
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    rw [Submodule.mem_bot, ← Submodule.projection_apply_of_mem_left hc hx]
    change g x = 0
    rw [hg0]; rfl
  · right
    set g' : X →ₗ[B] X := LinearMap.id - g
    have hidem' : ∀ x, g' (g' x) = g' x := fun x ↦ by
      simp only [g', LinearMap.sub_apply, LinearMap.id_apply, map_sub, hidem]; abel
    have hH' : b.hat S hA hK φ φ hprim g' = 0 := by
      rw [b.hat_sub, b.hat_id, h1]; exact sub_self _
    have hg'0 : g' = 0 := b.eq_zero_of_kill_V S hA hK φ hprim g' hidem'
      (b.kill_of_hat S hA hK φ φ hprim g' hH')
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    have h1 : g x = 0 := Submodule.projection_apply_of_mem_right hc hx
    have h2 : g' x = 0 := by rw [hg'0]; rfl
    simp only [g', LinearMap.sub_apply, LinearMap.id_apply, h1, sub_zero] at h2
    exact (Submodule.mem_bot B).mpr h2

include hprim in
/-- **Isomorphic band block modules have similar twists.** -/
theorem conj_of_equiv (e : b.BMV S hA hK φ ≃ₗ[B] b.BMV S hA hK φ') :
    ∃ ψ : V ≃ₗ[k] V', ∀ y, ψ (φ y) = φ' (ψ y) := by
  have h1 : b.hat S hA hK φ' φ hprim e.symm.toLinearMap ∘ₗ b.hat S hA hK φ φ' hprim e.toLinearMap =
      LinearMap.id := by
    rw [← b.hat_comp, show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from
      LinearMap.ext fun x ↦ e.symm_apply_apply x, b.hat_id]
  have h2 : b.hat S hA hK φ φ' hprim e.toLinearMap ∘ₗ b.hat S hA hK φ' φ hprim e.symm.toLinearMap =
      LinearMap.id := by
    rw [← b.hat_comp, show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from
      LinearMap.ext fun x ↦ e.apply_symm_apply x, b.hat_id]
  exact ⟨LinearEquiv.ofLinearMap _ _ h2 h1, fun y ↦ b.hat_comm S hA hK φ φ' hprim e.toLinearMap y⟩

omit [FiniteDimensional k V] in
/-- If `M(V, φ)` is indecomposable, `φ` has no nontrivial commuting idempotent. -/
theorem idemIndec_of_isIndecomposable (hind : IsIndecomposable B (b.BMV S hA hK φ)) :
    IdemIndec φ.toLinearMap := by
  intro ε hc hε
  set C := b.blockQuiver S hA V φ
  set hC := b.blockQuiver_kills S hA hK V φ
  have hcomm : ∀ y, ε (φ y) = φ (ε y) := fun y ↦ LinearMap.congr_fun hc y
  set H : C.Mod hC →ₗ[B] C.Mod hC := C.withGHom hC C.g hC ε (b.g_comm S hA φ hcomm)
  have hH : ∀ p y, H (C.ofFun hC (Pi.single p y)) = C.ofFun hC (Pi.single p (ε y)) :=
    fun p y ↦ C.withGHom_single hC C.g hC ε (b.g_comm S hA φ hcomm) p y
  have hHH : IsIdempotentElem H := by
    refine C.hom_ext hC fun p y ↦ ?_
    show H (H _) = H _
    rw [hH, hH]
    congr 2
    exact LinearMap.congr_fun hε.eq y
  have hval : ∀ y y', C.ofFun hC (Pi.single b.first y) = C.ofFun hC (Pi.single b.first y') →
      y = y' := fun y y' h ↦ by
    have h' : (Pi.single b.first y : Fin b.n → V) b.first =
        (Pi.single b.first y' : Fin b.n → V) b.first := congrFun h b.first
    simpa using h'
  rcases hind.2 _ _ (LinearMap.IsIdempotentElem.isCompl hHH) with h0 | h0
  · left
    refine LinearMap.ext fun y ↦ hval _ _ ?_
    refine (hH b.first y).symm.trans ?_
    have : H (C.ofFun hC (Pi.single b.first y)) ∈ LinearMap.range H := ⟨_, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    rw [this]
    show (0 : C.Mod hC) = C.ofFun hC (Pi.single b.first 0)
    exact (congrArg (C.ofFun hC) (Pi.single_zero (M := fun _ : Fin b.n ↦ V) b.first)).symm
  · right
    refine LinearMap.ext fun y ↦ hval _ _ ?_
    refine (hH b.first y).symm.trans ?_
    have hinj : Function.Injective H := LinearMap.ker_eq_bot.mp h0
    apply hinj
    rw [← Module.End.mul_apply, hHH.eq]
    rfl

end Indec

section Jordan

variable (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q)

/-- **The band module** `M(ω, μ, n)`: the twist is the Jordan block `J_n(μ)`. -/
abbrev bandModule (n : ℕ) (μ : kˣ) : Type u := b.BMV S hA hK (jordanEquiv n μ)

theorem jordanEquiv_toLinearMap (n : ℕ) (μ : kˣ) :
    (jordanEquiv n μ).toLinearMap = jordan (k := k) n (μ : k) :=
  LinearMap.ext fun _ ↦ rfl

include hprim in
/-- **Band modules are indecomposable**, for every `n ≥ 1`. -/
theorem isIndecomposable_bandModule {n : ℕ} (hn : 0 < n) (μ : kˣ) :
    IsIndecomposable B (b.bandModule S hA hK n μ) := by
  have : Nontrivial (Fin n → k) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  refine b.isIndecomposable_BMV S hA hK _ hprim ?_
  rw [jordanEquiv_toLinearMap]
  exact idemIndec_jordan n (μ : k)

include hprim in
/-- **Band modules with different parameters are not isomorphic.** -/
theorem eq_of_bandModule_equiv {n : ℕ} (hn : 0 < n) {μ μ' : kˣ}
    (e : b.bandModule S hA hK n μ ≃ₗ[B] b.bandModule S hA hK n μ') : μ = μ' := by
  obtain ⟨ψ, hψ⟩ := b.conj_of_equiv S hA hK _ _ hprim e
  exact Units.ext (eq_of_jordan_conj n hn ψ hψ)

/-- **Every indecomposable band block module is a band module** `M(ω, μ, n)`, over an
algebraically closed field. -/
theorem exists_equiv_bandModule [IsAlgClosed k] {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (φ : V ≃ₗ[k] V) (hind : IsIndecomposable B (b.BMV S hA hK φ)) :
    ∃ (n : ℕ) (_ : 0 < n) (μ : kˣ), Nonempty (b.BMV S hA hK φ ≃ₗ[B] b.bandModule S hA hK n μ) := by
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨⟨x, y, hxy⟩, -⟩ := hind
    apply hxy
    exact funext fun p ↦ Subsingleton.elim _ _
  obtain ⟨n, μ, ψ, hψ⟩ := exists_jordan φ (b.idemIndec_of_isIndecomposable S hA hK φ hind)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      exact hx (ψ.injective (Subsingleton.elim _ _))
    · exact h
  refine ⟨n, hn, μ, ⟨(b.blockQuiver S hA V φ).withGEquiv (b.blockQuiver_kills S hA hK V φ)
    (b.blockQuiver S hA (Fin n → k) (jordanEquiv n μ)).g
    (b.blockQuiver_kills S hA hK (Fin n → k) (jordanEquiv n μ)) ψ fun a i y ↦ ?_⟩⟩
  simp only [blockQuiver]
  split_ifs
  · exact hψ y
  · apply (jordanEquiv n μ).injective
    rw [LinearEquiv.apply_symm_apply, jordanEquiv_apply, ← hψ, LinearEquiv.apply_symm_apply]
  · rfl

end Jordan

end CWord

end BrickAccessibility
