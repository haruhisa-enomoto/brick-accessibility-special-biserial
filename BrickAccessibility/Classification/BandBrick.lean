module

public import BrickAccessibility.Classification.ClosedBand
public import BrickAccessibility.Classification.Semicont
public import BrickAccessibility.Basic.Brick

/-!
# A band brick gives infinitely many bricks

On the common space `X = k^n`, the endomorphisms of `M(b, t)` are the kernel of the
commutator map with the vertex and arrow actions. After multiplying the arrow
part by `t`, this map is polynomial in `t` (`T_eq`). By semicontinuity, if
`M(b, λ)` is a brick then so is `M(b, t)` for all but finitely many `t`
(`finite_not_isBrick`). These are pairwise non-isomorphic, so a primitive band
brick contradicts brick-finiteness (`not_isBrickFinite`).
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

/-- The power of `t` on a move after multiplying the arrow action by `t`. -/
def deg (a : D.Q.A) (i : Fin b.n) : ℕ :=
  if i = b.last ∧ b.lt b.last = (a, true) then 2
  else if i = b.first ∧ b.lt b.last = (a, false) then 0 else 1

theorem deg_lt (a : D.Q.A) (i : Fin b.n) : b.deg a i < 3 := by
  unfold deg; split_ifs <;> omega

/-- The degree `m` part of the arrow action. -/
def Pm (m : ℕ) (a : D.Q.A) : Module.End k (Fin b.n → k) where
  toFun f j := ∑ i, if b.next a i = some j ∧ b.deg a i = m then f i else 0
  map_add' f g := by
    funext j; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  map_smul' c f := by
    funext j; simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp

/-- The vertex projection. -/
def eM (v : D.Q.V) : Module.End k (Fin b.n → k) where
  toFun f j := if b.vtx j = v then f j else 0
  map_add' f g := by funext j; by_cases h : b.vtx j = v <;> simp [h]
  map_smul' c f := by funext j; by_cases h : b.vtx j = v <;> simp [h]

/-- The commutator map, degree `m` part. -/
def Qm (m : ℕ) : Module.End k (Fin b.n → k) →ₗ[k]
    ((D.Q.V → Module.End k (Fin b.n → k)) × (D.Q.A → Module.End k (Fin b.n → k))) where
  toFun F := (fun v ↦ if m = 0 then F * b.eM v - b.eM v * F else 0,
    fun a ↦ F * b.Pm m a - b.Pm m a * F)
  map_add' F G := by
    refine Prod.ext (funext fun v ↦ ?_) (funext fun a ↦ ?_)
    · simp only [Prod.fst_add, Pi.add_apply]
      split_ifs
      · simp only [add_mul, mul_add]; abel
      · simp
    · simp only [Prod.snd_add, Pi.add_apply, add_mul, mul_add]; abel
  map_smul' c F := by
    refine Prod.ext (funext fun v ↦ ?_) (funext fun a ↦ ?_)
    · simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
      split_ifs
      · simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
      · simp
    · simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_mul_assoc, mul_smul_comm,
        smul_sub]

/-- The polynomial commutator family. -/
def Tfam (s : k) := polyFam (b.Qm) 3 s

include hA in
/-- **The arrow action of `M(b, t)` times `t` is polynomial in `t`.** -/
theorem t_smul_α (t : kˣ) (a : D.Q.A) (f : b.BM S hA hK t) (j : Fin b.n) :
    (t : k) * (b.blockQuiver S hA k (tw t)).val (b.blockQuiver_kills S hA hK k (tw t))
      (D.α a • f) j =
      ∑ m ∈ Finset.range 3, (t : k) ^ m *
        b.Pm m a ((b.blockQuiver S hA k (tw t)).val (b.blockQuiver_kills S hA hK k (tw t)) f) j := by
  classical
  have h := MonomialData.BlockQuiver.α_smul_val (b.blockQuiver S hA k (tw t))
    (b.blockQuiver_kills S hA hK k (tw t)) a f j
  refine (congrArg (fun x ↦ (t : k) * x) h).trans ?_
  simp only [Pm, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hg : ∀ y : k, (t : k) * (b.blockQuiver S hA k (tw t)).g a i y = (t : k) ^ b.deg a i * y := by
    intro y
    simp only [blockQuiver, deg]
    split_ifs with h1 h2
    · simp [tw, LinearEquiv.smulOfUnit, Units.smul_def]; ring
    · simp [tw, LinearEquiv.smulOfUnit, Units.smul_def]
    · simp
  rw [Finset.sum_eq_single (b.deg a i)]
  · split_ifs with h1 h2 h2
    · exact hg _
    · exact (h2 ⟨h1, rfl⟩).elim
    · exact (h1 h2.1).elim
    · simp
  · intro m _ hm; rw [if_neg (fun h ↦ hm h.2.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (b.deg_lt a i)) h

/-- The coordinates of `M(b, t)`, as a linear map. -/
def coordL (t : kˣ) : b.BM S hA hK t →ₗ[k] (Fin b.n → k) where
  toFun x := (b.blockQuiver S hA k (tw t)).val (b.blockQuiver_kills S hA hK k (tw t)) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse of `coordL`. -/
def ofCoordL (t : kˣ) : (Fin b.n → k) →ₗ[k] b.BM S hA hK t :=
  (b.blockQuiver S hA k (tw t)).ofFunL (b.blockQuiver_kills S hA hK k (tw t))

omit hA in
theorem polyFam_apply (s : k) (F : Module.End k (Fin b.n → k)) :
    b.Tfam s F = (fun v ↦ F * b.eM v - b.eM v * F,
      fun a ↦ F * (∑ m ∈ Finset.range 3, s ^ m • b.Pm m a) -
        (∑ m ∈ Finset.range 3, s ^ m • b.Pm m a) * F) := by
  simp only [Tfam, polyFam, LinearMap.sum_apply, LinearMap.smul_apply, Qm, LinearMap.coe_mk,
    AddHom.coe_mk]
  refine Prod.ext (funext fun v ↦ ?_) (funext fun a ↦ ?_)
  · simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm; simp [hm]
    · simp
  · simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum,
      Finset.sum_mul, ← Finset.sum_sub_distrib, mul_smul_comm, smul_mul_assoc, smul_sub]

include hA in
theorem sumP_apply (t : kˣ) (a : D.Q.A) (f : Fin b.n → k) :
    (∑ m ∈ Finset.range 3, (t : k) ^ m • b.Pm m a) f =
      (t : k) • b.coordL S hA hK t (D.α a • b.ofCoordL S hA hK t f) := by
  funext j
  rw [LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have := b.t_smul_α S hA hK t a (b.ofCoordL S hA hK t f) j
  refine Eq.trans ?_ this.symm
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rfl

include hA in
theorem eM_apply (t : kˣ) (v : D.Q.V) (f : Fin b.n → k) :
    b.eM v f = b.coordL S hA hK t (D.e v • b.ofCoordL S hA hK t f) := by
  funext j
  exact (MonomialData.BlockQuiver.e_smul_val (b.blockQuiver S hA k (tw t))
    (b.blockQuiver_kills S hA hK k (tw t)) v (b.ofCoordL S hA hK t f) j).symm

include hA in
/-- An endomorphism of `M(b, t)` in coordinates lies in the kernel of the commutator map. -/
def endToKer (t : kˣ) : (b.BM S hA hK t →ₗ[B] b.BM S hA hK t) →ₗ[k]
    LinearMap.ker (b.Tfam (t : k)) where
  toFun φ := ⟨(b.coordL S hA hK t).comp ((φ.restrictScalars k).comp (b.ofCoordL S hA hK t)), by
    rw [LinearMap.mem_ker, polyFam_apply]
    refine Prod.ext (funext fun v ↦ ?_) (funext fun a ↦ ?_)
    · refine LinearMap.ext fun f ↦ ?_
      simp only [Prod.fst_zero, Pi.zero_apply, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
      rw [b.eM_apply S hA hK t v, b.eM_apply S hA hK t v, sub_eq_zero]
      have e1 : b.ofCoordL S hA hK t (b.coordL S hA hK t (D.e v • b.ofCoordL S hA hK t f)) =
        D.e v • b.ofCoordL S hA hK t f := rfl
      have e2 : b.ofCoordL S hA hK t (b.coordL S hA hK t (φ (b.ofCoordL S hA hK t f))) =
        φ (b.ofCoordL S hA hK t f) := rfl
      rw [e1, e2, map_smul]
    · refine LinearMap.ext fun f ↦ ?_
      simp only [Prod.snd_zero, Pi.zero_apply, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
      rw [b.sumP_apply S hA hK t, b.sumP_apply S hA hK t, sub_eq_zero]
      have e2 : b.ofCoordL S hA hK t (b.coordL S hA hK t (φ (b.ofCoordL S hA hK t f))) =
        φ (b.ofCoordL S hA hK t f) := rfl
      rw [e2, map_smul, show b.ofCoordL S hA hK t (b.coordL S hA hK t (D.α a • b.ofCoordL S hA hK t f)) =
        D.α a • b.ofCoordL S hA hK t f from rfl, LinearMap.map_smul_of_tower, map_smul φ (D.α a),
        map_smul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hA in
theorem endToKer_injective (t : kˣ) : Function.Injective (b.endToKer S hA hK t) := by
  intro φ ψ h
  ext x
  have := LinearMap.congr_fun (congrArg Subtype.val h) (b.coordL S hA hK t x)
  exact this

include hA in
/-- A kernel element gives an endomorphism of `M(b, t)`. -/
def kerToEnd (t : kˣ) : LinearMap.ker (b.Tfam (t : k)) →ₗ[k]
    (b.BM S hA hK t →ₗ[B] b.BM S hA hK t) where
  toFun F := by
    have hF := LinearMap.mem_ker.mp F.2
    rw [polyFam_apply] at hF
    have hFe : ∀ v, (F : Module.End k (Fin b.n → k)) * b.eM v = b.eM v * F := fun v ↦
      sub_eq_zero.mp (congrFun (congrArg Prod.fst hF) v)
    have hFa : ∀ a, (F : Module.End k (Fin b.n → k)) * (∑ m ∈ Finset.range 3, (t : k) ^ m • b.Pm m a) =
        (∑ m ∈ Finset.range 3, (t : k) ^ m • b.Pm m a) * F := fun a ↦
      sub_eq_zero.mp (congrFun (congrArg Prod.snd hF) a)
    refine D.linearMap_of_commute ((b.ofCoordL S hA hK t).comp ((F : Module.End k _).comp
      (b.coordL S hA hK t))) (fun v x ↦ ?_) (fun a x ↦ ?_)
    · have := LinearMap.congr_fun (hFe v) (b.coordL S hA hK t x)
      simp only [Module.End.mul_apply] at this
      rw [b.eM_apply S hA hK t, b.eM_apply S hA hK t] at this
      exact congrArg (b.ofCoordL S hA hK t) this
    · have := LinearMap.congr_fun (hFa a) (b.coordL S hA hK t x)
      simp only [Module.End.mul_apply] at this
      rw [b.sumP_apply S hA hK t, b.sumP_apply S hA hK t] at this
      have h' := congrArg (b.ofCoordL S hA hK t) this
      rw [map_smul, map_smul] at h'
      exact smul_right_injective _ t.ne_zero h'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hA in
theorem kerToEnd_injective (t : kˣ) : Function.Injective (b.kerToEnd S hA hK t) := by
  intro F G h
  refine Subtype.ext (LinearMap.ext fun f ↦ ?_)
  have := LinearMap.congr_fun h (b.ofCoordL S hA hK t f)
  exact congrArg (b.coordL S hA hK t) this

include hA in
theorem nontrivial_BM (t : kˣ) : Nontrivial (b.BM S hA hK t) :=
  ⟨⟨b.x0 S hA hK t, 0, fun h ↦ b.x0_not_mem_denB S hA hK t (by rw [h]; exact Submodule.zero_mem _)⟩⟩

include hA in
/-- **A band brick is a brick for all but finitely many twists.** -/
theorem finite_not_isBrick [IsAlgClosed k] (l : kˣ) (hl : IsBrick B (b.BM S hA hK l)) :
    {t : kˣ | ¬ IsBrick B (b.BM S hA hK t)}.Finite := by
  have h1 : finrank k (b.BM S hA hK l →ₗ[B] b.BM S hA hK l) = 1 := hl.finrank_end (k := k)
  have h2 : finrank k (LinearMap.ker (b.Tfam (l : k))) ≤ 1 := by
    rw [← h1]
    exact LinearMap.finrank_le_finrank_of_injective (b.kerToEnd_injective S hA hK l)
  have hfin := finite_lt_finrank_ker (b.Qm) 3 (l : k)
  refine (hfin.preimage Units.val_injective.injOn).subset fun t ht ↦ ?_
  by_contra hlt
  apply ht
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_lt] at hlt
  have h3 : finrank k (b.BM S hA hK t →ₗ[B] b.BM S hA hK t) ≤
      finrank k (LinearMap.ker (b.Tfam (t : k))) :=
    LinearMap.finrank_le_finrank_of_injective (b.endToKer_injective S hA hK t)
  have := b.nontrivial_BM S hA hK t
  refine isBrick_of_finrank_end_le_one (k := k) ?_
  change finrank k (LinearMap.ker (polyFam b.Qm 3 (t : k))) ≤ _ at hlt
  exact h3.trans ((hlt.trans h2))

theorem infinite_units [Infinite k] : Infinite kˣ := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  have : Finite {x : k // x ≠ 0} := Finite.of_equiv _ unitsEquivNeZero
  have hinj : Function.Injective fun x : k ↦ if h : x = 0 then (none : Option {x : k // x ≠ 0})
      else some ⟨x, h⟩ := by
    intro x y e
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all
  have : Finite k := Finite.of_injective _ hinj
  exact not_finite k

include hA in
/-- **A primitive band brick contradicts brick-finiteness.** -/
theorem not_isBrickFinite [IsAlgClosed k] [FiniteDimensional k B]
    (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (l : kˣ)
    (hl : IsBrick B (b.BM S hA hK l)) : ¬ IsBrickFinite B := by
  classical
  rintro ⟨n, Ms, hMs⟩
  have hG : {t : kˣ | IsBrick B (b.BM S hA hK t)}.Infinite := by
    have := infinite_units (k := k)
    have h := (b.finite_not_isBrick S hA hK l hl).infinite_compl
    have e : {t : kˣ | ¬ IsBrick B (b.BM S hA hK t)}ᶜ = {t : kˣ | IsBrick B (b.BM S hA hK t)} := by
      ext t; simp
    rwa [e] at h
  have hex : ∀ t : {t : kˣ // IsBrick B (b.BM S hA hK t)}, ∃ i,
      Nonempty (b.BM S hA hK t.1 ≃ₗ[B] Ms i) := fun t ↦ by
    have : Module.Finite B (b.BM S hA hK t.1) := Module.Finite.of_restrictScalars_finite k B _
    exact hMs _ t.2
  choose idx hidx using hex
  have hinj : Function.Injective idx := by
    intro t t' e
    obtain ⟨e1⟩ := hidx t
    obtain ⟨e2⟩ := hidx t'
    rw [e] at e1
    exact Subtype.ext (b.eq_of_equiv S hA hK hprim (e1.trans e2.symm))
  have : Finite {t : kˣ // IsBrick B (b.BM S hA hK t)} := Finite.of_injective idx hinj
  exact hG (Set.finite_coe_iff.mp this)

end CWord

end BrickAccessibility
