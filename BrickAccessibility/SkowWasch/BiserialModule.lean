module

public import BrickAccessibility.SkowWasch.Biserial
public import BrickAccessibility.SkowWasch.Local
public import Mathlib.Algebra.Module.Projective

/-!
# From biserial projectives to their element form

The left ideal `A e_i` is an indecomposable projective whose radical is `R e_i`
(`radical_Pe`). A uniserial submodule of a finite-dimensional module is cyclic, generated
by an element fixed by some `e_s` (`exists_gen`). Hence the biserial condition on left
projectives gives `BisAt i` for every vertex (`bisAt_of_biserial`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

open Module

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
  (B : BasicData k A)

/-- The left ideal `A e_i`. -/
def Pe (i : Fin B.n) : Submodule A A where
  carrier := {w | w * B.e i = w}
  add_mem' {a b} ha hb := by
    show (a + b) * B.e i = a + b
    rw [add_mul, show a * B.e i = a from ha, show b * B.e i = b from hb]
  zero_mem' := zero_mul _
  smul_mem' c w hw := by
    show c * w * B.e i = c * w
    rw [mul_assoc, show w * B.e i = w from hw]

/-- The generator `e_i`. -/
def pe (i : Fin B.n) : B.Pe i := ⟨B.e i, B.e_idem i⟩

theorem pe_gen (i : Fin B.n) : Submodule.span A {B.pe i} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  refine Submodule.mem_span_singleton.mpr ⟨w, Subtype.ext ?_⟩
  show w * B.e i = w
  exact hw

theorem pe_ej (i : Fin B.n) : B.e i • B.pe i = B.pe i := Subtype.ext (B.e_idem i)

theorem pe_ne (i : Fin B.n) : B.pe i ≠ 0 := fun h ↦ B.e_ne i (congrArg Subtype.val h)

instance (i : Fin B.n) : FiniteDimensional k (B.Pe i) :=
  FiniteDimensional.of_injective ((B.Pe i).subtype.restrictScalars k) Subtype.val_injective

theorem pe_finite (i : Fin B.n) : Module.Finite A (B.Pe i) := by
  refine ⟨⟨{B.pe i}, ?_⟩⟩
  rw [Finset.coe_singleton, B.pe_gen]

theorem pe_projective (i : Fin B.n) : Module.Projective A (B.Pe i) := by
  let s : A →ₗ[A] B.Pe i := LinearMap.codRestrict (B.Pe i)
    (LinearMap.toSpanSingleton A A (B.e i))
    (fun c ↦ show c • B.e i * B.e i = c • B.e i by rw [smul_eq_mul, mul_assoc, B.e_idem])
  exact Module.Projective.of_split (B.Pe i).subtype s (by ext w; exact w.2)

theorem pe_indec (i : Fin B.n) : Statement.IsIndecomposable A (B.Pe i) := by
  have : Nontrivial (B.Pe i) := ⟨⟨_, _, B.pe_ne i⟩⟩
  exact B.isIndecomposable_of_gen (B.pe_gen i) (B.pe_ej i)

/-- The radical part of `A e_i`. -/
def N0 (i : Fin B.n) : Submodule A (B.Pe i) where
  carrier := {x | (x : A) ∈ B.R}
  add_mem' := fun ha hb ↦ B.R.add_mem ha hb
  zero_mem' := B.R.zero_mem
  smul_mem' := fun c x hx ↦ B.mul_mem_left c _ hx

/-- An element of `A e_i` outside the radical generates. -/
theorem span_eq_top_of_not_mem {i : Fin B.n} {x : B.Pe i} (hx : (x : A) ∉ B.R) :
    Submodule.span A {x} = ⊤ := by
  obtain ⟨c, r, hr, hre, hc⟩ := B.corner i (x : A)
  have hxe : (x : A) * B.e i = x := x.2
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx
    have hsum : (x : A) = ∑ v, B.e v * x := by rw [← Finset.sum_mul, B.sum_e, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ fun v _ ↦ ?_
    by_cases hv : v = i
    · subst hv
      rw [← hxe, ← mul_assoc, hc, zero_smul, zero_add]; exact hr
    · rw [← hxe, ← mul_assoc]; exact B.corner_mem hv _
  obtain ⟨u, hu⟩ := B.isUnit_add hc0 hr
  have hre' : r * B.e i = r := by rw [← hre, mul_assoc, B.e_idem]
  have hpe : B.pe i ∈ Submodule.span A {x} := by
    refine Submodule.mem_span_singleton.mpr ⟨(↑u⁻¹ : A) * B.e i, Subtype.ext ?_⟩
    show (↑u⁻¹ : A) * B.e i * x = B.e i
    have : B.e i * (x : A) = (algebraMap k A c + r) * B.e i := by
      rw [← hxe, ← mul_assoc, hc, add_mul, hre', ← Algebra.smul_def]
    rw [mul_assoc, this, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [eq_top_iff, ← B.pe_gen i, Submodule.span_le, Set.singleton_subset_iff]
  exact hpe

/-- **The radical of `A e_i`.** -/
theorem radical_Pe (i : Fin B.n) : Statement.radical A (B.Pe i) = B.N0 i := by
  have hle : ∀ N : Submodule A (B.Pe i), N ≠ ⊤ → N ≤ B.N0 i := by
    intro N hN x hx
    by_contra h
    apply hN
    rw [eq_top_iff, ← B.span_eq_top_of_not_mem h, Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  have hco : IsCoatom (B.N0 i) := by
    refine ⟨fun h ↦ ?_, fun N hN ↦ ?_⟩
    · have : B.pe i ∈ B.N0 i := by rw [h]; trivial
      exact B.e_not_mem i this
    · by_contra hN'
      exact (not_le_of_gt hN) (hle N hN')
  refine le_antisymm (sInf_le hco) (le_sInf fun N hN ↦ ?_)
  rcases eq_or_lt_of_le (hle N hN.1) with h | h
  · rw [h]
  · exact absurd (hN.2 _ h) hco.1

section Uniserial

variable {B} {P : Type u} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
  [FiniteDimensional k P]

omit [FiniteDimensional k A] in
theorem le_of_comparable {S T : Submodule A P} (h : S ≤ T ∨ T ≤ S)
    (hf : finrank k S ≤ finrank k T) : S ≤ T := by
  rcases h with h | h
  · exact h
  · have h1 : T.restrictScalars k ≤ S.restrictScalars k := h
    have h2 : finrank k (S.restrictScalars k) ≤ finrank k (T.restrictScalars k) := hf
    have := Submodule.eq_of_le_of_finrank_le h1 h2
    exact (Submodule.restrictScalars_injective k A P this).ge

omit [FiniteDimensional k A] in
/-- **A uniserial submodule is cyclic**, with a generator fixed by an idempotent. -/
theorem exists_gen (U : Submodule A P) (hU : Statement.IsUniserialSubmodule A U)
    (i0 : Fin B.n) : ∃ (x : P) (s : Fin B.n), x ∈ U ∧ U = Submodule.span A {x} ∧
      B.e s • x = x := by
  classical
  have hspanU : ∀ y ∈ U, Submodule.span A {y} ≤ U := fun y hy ↦ by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy
  -- a generator of maximal dimension
  let S : Set ℕ := {m | ∃ x ∈ U, finrank k (Submodule.span A {x}) = m}
  have hS : S.Nonempty := ⟨_, 0, U.zero_mem, rfl⟩
  have hSb : BddAbove S := ⟨finrank k P, by
    rintro _ ⟨x, -, rfl⟩
    exact Submodule.finrank_le ((Submodule.span A {x}).restrictScalars k)⟩
  obtain ⟨x0, hx0U, hx0⟩ := Nat.sSup_mem hS hSb
  have hmax : ∀ y ∈ U, Submodule.span A {y} ≤ Submodule.span A {x0} := fun y hy ↦
    le_of_comparable (hU _ _ (hspanU y hy) (hspanU x0 hx0U))
      (hx0 ▸ le_csSup hSb ⟨y, hy, rfl⟩)
  have hUx : U = Submodule.span A {x0} := le_antisymm
    (fun y hy ↦ hmax y hy (Submodule.mem_span_singleton_self y)) (hspanU x0 hx0U)
  -- a homogeneous generator
  have hmem : ∀ v, B.e v • x0 ∈ U := fun v ↦ U.smul_mem _ hx0U
  obtain ⟨v0, -, hv0⟩ := Finset.exists_max_image Finset.univ
    (fun v ↦ finrank k (Submodule.span A {B.e v • x0})) ⟨i0, Finset.mem_univ _⟩
  have hle : ∀ v, Submodule.span A {B.e v • x0} ≤ Submodule.span A {B.e v0 • x0} := fun v ↦
    le_of_comparable (hU _ _ (hspanU _ (hmem v)) (hspanU _ (hmem v0)))
      (hv0 v (Finset.mem_univ _))
  have hx0mem : x0 ∈ Submodule.span A {B.e v0 • x0} := by
    have hsum : x0 = ∑ v, B.e v • x0 := by rw [← Finset.sum_smul, B.sum_e, one_smul]
    have h := Submodule.sum_mem (Submodule.span A {B.e v0 • x0})
      (t := Finset.univ) (f := fun v ↦ B.e v • x0)
      fun v _ ↦ hle v (Submodule.mem_span_singleton_self _)
    rwa [← hsum] at h
  refine ⟨B.e v0 • x0, v0, hmem v0, le_antisymm ?_ (hspanU _ (hmem v0)), ?_⟩
  · rw [hUx, Submodule.span_le, Set.singleton_subset_iff]; exact hx0mem
  · rw [smul_smul, B.e_idem]

end Uniserial

/-- **Biserial left projectives in element form.** -/
theorem bisAt_of_biserial (hbis : Statement.ProjectivesHaveBiserialRadical A) (i : Fin B.n) :
    B.BisAt i := by
  have := B.pe_finite i
  have := B.pe_projective i
  obtain ⟨U₁, U₂, hU, h1, h2, -⟩ := hbis (B.Pe i) (B.pe_indec i)
  rw [radical_Pe] at hU
  obtain ⟨x₁, s₁, hx₁U, hU₁, he₁⟩ := exists_gen (B := B) U₁ h1 i
  obtain ⟨x₂, s₂, hx₂U, hU₂, he₂⟩ := exists_gen (B := B) U₂ h2 i
  have hRe : ∀ {x : B.Pe i}, x ∈ U₁ ⊔ U₂ → (x : A) ∈ B.Re i := fun {x} hx ↦
    ⟨x.2, by rw [hU] at hx; exact hx⟩
  have hch : ∀ {U : Submodule A (B.Pe i)} {x : B.Pe i}, Statement.IsUniserialSubmodule A U →
      x ∈ U → LChain (x : A) := by
    intro U x hU hx p q
    have hp : Submodule.span A {p • x} ≤ U := by
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact U.smul_mem p hx
    have hq : Submodule.span A {q • x} ≤ U := by
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact U.smul_mem q hx
    rcases hU _ _ hp hq with h | h
    · obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp (h (Submodule.mem_span_singleton_self _))
      left
      exact ⟨w, (congrArg Subtype.val hw).symm⟩
    · obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp (h (Submodule.mem_span_singleton_self _))
      right
      exact ⟨w, (congrArg Subtype.val hw).symm⟩
  refine ⟨x₁, x₂, s₁, s₂, congrArg Subtype.val he₁, congrArg Subtype.val he₂,
    hRe (Submodule.mem_sup_left hx₁U), hRe (Submodule.mem_sup_right hx₂U),
    hch h1 hx₁U, hch h2 hx₂U, ?_⟩
  intro y hy
  have hyN : (⟨y, hy.1⟩ : B.Pe i) ∈ U₁ ⊔ U₂ := by rw [hU]; exact hy.2
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hyN
  rw [hU₁] at ha
  rw [hU₂] at hb
  obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.mp hb
  exact ⟨c₁, c₂, (congrArg Subtype.val hab).symm⟩

end BasicData

end SkowWasch

end BrickAccessibility
