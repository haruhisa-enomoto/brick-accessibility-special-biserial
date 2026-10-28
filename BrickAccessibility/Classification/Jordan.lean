module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Jordan blocks

The `n × n` Jordan block `J_n(μ)` with eigenvalue `μ` (`jordanMatrix`), acting on `kⁿ` by
`(J x)_i = μ x_i + x_{i+1}` (`jordan_apply`). We prove:

* `J_n(μ)` admits no nontrivial commuting idempotent (`idemIndec_jordan`);
* `J_n(μ)` and `J_n(μ')` are not similar for `μ ≠ μ'` (`eq_of_jordan_conj`);
* over an algebraically closed field, an automorphism of a nonzero finite-dimensional space
  without nontrivial commuting idempotents is similar to a single Jordan block
  (`exists_jordan`): Fitting's decomposition makes it unipotent up to a scalar, and a cyclic
  vector of the nilpotent part has an invariant complement.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

variable {k : Type*} [Field k]

/-- An endomorphism without nontrivial commuting idempotents. -/
def IdemIndec {V : Type*} [AddCommGroup V] [Module k V] (f : V →ₗ[k] V) : Prop :=
  ∀ ε : V →ₗ[k] V, ε ∘ₗ f = f ∘ₗ ε → IsIdempotentElem ε → ε = 0 ∨ ε = 1

section Shift

variable (n : ℕ)

/-- The nilpotent part of a Jordan block: `(N x)_i = x_{i+1}`. -/
def shiftN : (Fin n → k) →ₗ[k] (Fin n → k) where
  toFun x i := if h : i.val + 1 < n then x ⟨i.val + 1, h⟩ else 0
  map_add' x y := by funext i; by_cases h : i.val + 1 < n <;> simp [h]
  map_smul' c x := by funext i; by_cases h : i.val + 1 < n <;> simp [h]

theorem shiftN_apply (x : Fin n → k) (i : Fin n) :
    shiftN n x i = if h : i.val + 1 < n then x ⟨i.val + 1, h⟩ else 0 := rfl

theorem shiftN_pow_apply (m : ℕ) (x : Fin n → k) (i : Fin n) :
    (shiftN n ^ m) x i = if h : i.val + m < n then x ⟨i.val + m, h⟩ else 0 := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      by_cases h : i.val + (m + 1) < n
      · rw [dif_pos (by omega), shiftN_apply, dif_pos h]
        split_ifs with h2
        · congr 1
        · exfalso; simp only at h2; omega
      · rw [dif_neg h]
        split_ifs with h1
        · rw [shiftN_apply, dif_neg (by simp only; omega)]
        · rfl

theorem shiftN_pow_self : shiftN (k := k) n ^ n = 0 := by
  refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
  rw [shiftN_pow_apply, dif_neg (by omega)]
  rfl

/-- The `n × n` Jordan block with eigenvalue `μ`: `μ` on the diagonal, `1` just above it. -/
def jordanMatrix (μ : k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j ↦ if i = j then μ else if j.val = i.val + 1 then 1 else 0

/-- The Jordan block acting on `kⁿ`. -/
def jordan (μ : k) : (Fin n → k) →ₗ[k] (Fin n → k) := Matrix.toLin' (jordanMatrix n μ)

theorem jordan_apply (μ : k) (x : Fin n → k) (i : Fin n) :
    jordan n μ x i = μ * x i + shiftN n x i := by
  classical
  simp only [jordan, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, jordanMatrix,
    Matrix.of_apply]
  have e : ∀ j : Fin n, (if i = j then μ else if j.val = i.val + 1 then (1 : k) else 0) * x j =
      (if i = j then μ * x j else 0) + (if j.val = i.val + 1 then x j else 0) := by
    intro j
    by_cases h1 : i = j
    · subst h1; simp
    · by_cases h2 : j.val = i.val + 1 <;> simp [h1, h2]
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, shiftN_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Fin.ext hj')
    · simp
  · refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [if_neg]
    intro hj
    have := j.isLt
    omega

theorem jordan_eq (μ : k) : jordan n μ = μ • LinearMap.id + shiftN n := by
  refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
  rw [jordan_apply]
  rfl

/-- `c + N` is injective for `c ≠ 0`: look at the last nonzero coordinate. -/
theorem eq_zero_of_smul_add_shiftN {c : k} (hc : c ≠ 0) {x : Fin n → k}
    (h : c • x + shiftN n x = 0) : x = 0 := by
  classical
  by_contra hx
  have hne : (Finset.univ.filter fun i ↦ x i ≠ 0).Nonempty := by
    by_contra h0
    apply hx
    funext i
    by_contra hi
    exact h0 ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  set i := (Finset.univ.filter fun i ↦ x i ≠ 0).max' hne
  have hi : x i ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hmax : ∀ j : Fin n, i < j → x j = 0 := by
    intro j hj
    by_contra hj'
    exact absurd (Finset.le_max' _ j (by simp [hj'])) (not_le.mpr hj)
  have := congrFun h i
  rw [Pi.add_apply, Pi.smul_apply, shiftN_apply, smul_eq_mul, Pi.zero_apply] at this
  split_ifs at this with h1
  · rw [hmax ⟨i.val + 1, h1⟩ (by rw [Fin.lt_def]; simp), add_zero] at this
    exact mul_ne_zero hc hi this
  · rw [add_zero] at this
    exact mul_ne_zero hc hi this

/-- For `μ ≠ 0` the Jordan block is invertible. -/
def jordanEquiv (μ : kˣ) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofInjectiveEndo (jordan n (μ : k)) fun x y hxy ↦ by
    rw [← sub_eq_zero]
    refine eq_zero_of_smul_add_shiftN n μ.ne_zero ?_
    have := congrArg (fun z ↦ z) hxy
    rw [← sub_eq_zero, ← map_sub, jordan_eq] at this
    simpa using this

theorem jordanEquiv_apply (μ : kˣ) (x : Fin n → k) : jordanEquiv n μ x = jordan n (μ : k) x := rfl

/-- The first basis vector `e₀`. -/
def e0 (hn : 0 < n) : Fin n → k := Pi.single ⟨0, hn⟩ 1

theorem shiftN_eq_zero_iff {x : Fin n → k} : shiftN n x = 0 ↔ ∀ j : Fin n, 0 < j.val → x j = 0 := by
  constructor
  · intro h j hj
    have hj1 : (⟨j.val - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
    have := congrFun h ⟨j.val - 1, by omega⟩
    rw [shiftN_apply, dif_pos hj1] at this
    have e : (⟨(⟨j.val - 1, by omega⟩ : Fin n).val + 1, hj1⟩ : Fin n) = j :=
      Fin.ext (by simp only; omega)
    rw [e] at this
    exact this
  · intro h
    funext i
    rw [shiftN_apply]
    split_ifs with h1
    · exact h _ (by simp only; omega)
    · rfl

/-- A nonzero shift-invariant subspace contains `e₀`. -/
theorem e0_mem (hn : 0 < n) (U : Submodule k (Fin n → k)) (hU : ∀ x ∈ U, shiftN n x ∈ U)
    (hne : U ≠ ⊥) : e0 n hn ∈ U := by
  classical
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hex : ∃ j, (shiftN n ^ (j + 1)) u = 0 := ⟨n, by
    rw [pow_succ', Module.End.mul_apply, shiftN_pow_self, LinearMap.zero_apply, map_zero]⟩
  set j := Nat.find hex
  have hj : (shiftN n ^ (j + 1)) u = 0 := Nat.find_spec hex
  have hj' : (shiftN n ^ j) u ≠ 0 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero]; exact hu0
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rwa [show j - 1 + 1 = j by omega] at this
  have hmem : ∀ m, (shiftN n ^ m) u ∈ U := by
    intro m
    induction m with
    | zero => simpa using huU
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hU _ ih
  set y := (shiftN n ^ j) u
  have hy : shiftN n y = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hj
  have hyk := (shiftN_eq_zero_iff n).mp hy
  have hy0 : y ⟨0, hn⟩ ≠ 0 := by
    intro h0
    apply hj'
    funext i
    by_cases hi : i.val = 0
    · rw [show i = ⟨0, hn⟩ from Fin.ext hi]; exact h0
    · exact hyk i (by omega)
  have hye : y = y ⟨0, hn⟩ • e0 n hn := by
    funext i
    by_cases hi : i.val = 0
    · rw [show i = ⟨0, hn⟩ from Fin.ext hi]; simp [e0]
    · rw [hyk i (by omega)]
      simp [e0, show i ≠ ⟨0, hn⟩ from fun h ↦ hi (by rw [h])]
  have : e0 n hn = (y ⟨0, hn⟩)⁻¹ • y := by
    calc e0 n hn = ((y ⟨0, hn⟩)⁻¹ * y ⟨0, hn⟩) • e0 n hn := by rw [inv_mul_cancel₀ hy0, one_smul]
      _ = (y ⟨0, hn⟩)⁻¹ • (y ⟨0, hn⟩ • e0 n hn) := by rw [smul_smul]
      _ = (y ⟨0, hn⟩)⁻¹ • y := by rw [← hye]
  rw [this]
  exact U.smul_mem _ (hmem j)

/-- **A Jordan block has no nontrivial commuting idempotent.** -/
theorem idemIndec_jordan (μ : k) : IdemIndec (jordan n μ) := by
  intro ε hc hε
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · left
    subst h0
    exact LinearMap.ext fun x ↦ Subsingleton.elim _ _
  have hcs : ∀ x, ε (shiftN n x) = shiftN n (ε x) := by
    intro x
    have h1 := LinearMap.congr_fun hc x
    simp only [LinearMap.comp_apply, jordan_eq, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul] at h1
    exact add_left_cancel h1
  by_contra hne
  push Not at hne
  have hR : e0 n hn ∈ LinearMap.range ε := e0_mem n hn _ (by
    rintro _ ⟨z, rfl⟩; exact ⟨shiftN n z, hcs z⟩)
    (fun h ↦ hne.1 (LinearMap.range_eq_bot.mp h))
  have hK : e0 n hn ∈ LinearMap.ker ε := e0_mem n hn _ (by
    intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [hcs, hx, map_zero])
    (fun h ↦ hne.2 (by
      refine LinearMap.ext fun x ↦ ?_
      have : ε x - x ∈ LinearMap.ker ε := by
        rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, hε.eq, sub_self]
      rw [h, Submodule.mem_bot, sub_eq_zero] at this
      exact this))
  obtain ⟨z, hz⟩ := hR
  have h1 : ε (e0 n hn) = e0 n hn := by rw [← hz, ← Module.End.mul_apply, hε.eq]
  rw [LinearMap.mem_ker, h1] at hK
  have := congrFun hK ⟨0, hn⟩
  simp [e0] at this

/-- **Jordan blocks with different eigenvalues are not similar.** -/
theorem eq_of_jordan_conj (hn : 0 < n) {μ μ' : k} (ψ : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (hψ : ∀ x, ψ (jordan n μ x) = jordan n μ' (ψ x)) : μ = μ' := by
  by_contra hne
  have hz : shiftN n (e0 (k := k) n hn) = 0 :=
    (shiftN_eq_zero_iff n).mpr fun j hj ↦ by
      simp [e0, show j ≠ ⟨0, hn⟩ from fun h ↦ by rw [h] at hj; exact lt_irrefl _ hj]
  have h1 : jordan n μ (e0 n hn) = μ • e0 n hn := by rw [jordan_eq]; simp [hz]
  set y := ψ (e0 n hn)
  have hy : (μ' - μ) • y + shiftN n y = 0 := by
    have := hψ (e0 n hn)
    rw [h1, map_smul, jordan_eq] at this
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [sub_smul, sub_add_eq_add_sub, ← this]
    simp [y]
  have := eq_zero_of_smul_add_shiftN n (sub_ne_zero.mpr (Ne.symm hne)) hy
  have he0 : e0 (k := k) n hn ≠ 0 := by
    intro h; have := congrFun h ⟨0, hn⟩; simp [e0] at this
  exact he0 (ψ.injective (by rw [map_zero]; exact this))

end Shift

section Exists

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Without nontrivial commuting idempotents, there is no decomposition into two nonzero
invariant complementary subspaces. -/
theorem IdemIndec.compl {f : V →ₗ[k] V} (hf : IdemIndec f) {U W : Submodule k V}
    (hc : IsCompl U W) (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) : U = ⊥ ∨ W = ⊥ := by
  set ε : V →ₗ[k] V := U.projection W hc
  have hεU : ∀ x ∈ U, ε x = x := fun x hx ↦ Submodule.projection_apply_of_mem_left hc hx
  have hεW : ∀ x ∈ W, ε x = 0 := fun x hx ↦ Submodule.projection_apply_of_mem_right hc hx
  have hdec : ∀ x, ∃ u ∈ U, ∃ w ∈ W, u + w = x := fun x ↦
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top)
  have hcomm : ε ∘ₗ f = f ∘ₗ ε := LinearMap.ext fun x ↦ by
    obtain ⟨u, hu, w, hw, rfl⟩ := hdec x
    simp only [LinearMap.comp_apply, map_add, hεU u hu, hεW w hw, hεU _ (hU u hu),
      hεW _ (hW w hw), add_zero, map_zero]
  have hid : IsIdempotentElem ε := LinearMap.ext fun x ↦ by
    show ε (ε x) = ε x
    exact hεU _ (Submodule.projection_apply_mem hc x)
  rcases hf ε hcomm hid with h | h
  · left
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    rw [Submodule.mem_bot, ← hεU x hx, h]; rfl
  · right
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    have := hεW x hx
    rw [h] at this
    exact (Submodule.mem_bot k).mpr this

/-- **Cyclic vector.** A nilpotent endomorphism admitting no decomposition into two nonzero
invariant complementary subspaces is a single shift in suitable coordinates. -/
theorem exists_cyclic [FiniteDimensional k V] [Nontrivial V] (N : V →ₗ[k] V) (hnil : IsNilpotent N)
    (hind : ∀ U W : Submodule k V, IsCompl U W → (∀ x ∈ U, N x ∈ U) → (∀ x ∈ W, N x ∈ W) →
      U = ⊥ ∨ W = ⊥) :
    ∃ (n : ℕ) (ψ : V ≃ₗ[k] (Fin n → k)), ∀ x, ψ (N x) = shiftN n (ψ x) := by
  classical
  have hex : ∃ r, N ^ r = 0 := hnil
  set r := Nat.find hex
  have hr0 : N ^ r = 0 := Nat.find_spec hex
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      rw [h, pow_zero] at hr0
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      exact hx (by simpa using LinearMap.congr_fun hr0 x)
    · exact h
  have hne : N ^ (r - 1) ≠ 0 := Nat.find_min hex (by omega)
  obtain ⟨v, hv⟩ : ∃ v, (N ^ (r - 1)) v ≠ 0 := by
    by_contra h; push Not at h; exact hne (LinearMap.ext h)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k V, f ((N ^ (r - 1)) v) ≠ 0 := by
    by_contra h; push Not at h; exact hv ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  have hpow : ∀ m, r ≤ m → ∀ x, (N ^ m) x = 0 := fun m hm x ↦ by
    rw [show m = (m - r) + r by omega, pow_add, Module.End.mul_apply, hr0, LinearMap.zero_apply,
      map_zero]
  let fam : Fin r → V := fun j ↦ (N ^ j.val) v
  let T : V →ₗ[k] (Fin r → k) := LinearMap.pi fun i : Fin r ↦ f ∘ₗ (N ^ i.val)
  have hT : ∀ x (i : Fin r), T x i = f ((N ^ i.val) x) := fun _ _ ↦ rfl
  -- triangularity of `T` on the family
  have tri : ∀ c : Fin r → k, T (∑ j, c j • fam j) = 0 → c = 0 := by
    intro c hc
    by_contra hc0
    have hne' : (Finset.univ.filter fun j ↦ c j ≠ 0).Nonempty := by
      by_contra h0
      apply hc0
      funext j
      by_contra hj
      exact h0 ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    set j0 := (Finset.univ.filter fun j ↦ c j ≠ 0).min' hne'
    have hj0 : c j0 ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hne')).2
    have hmin : ∀ j, j < j0 → c j = 0 := by
      intro j hj
      by_contra hj'
      exact absurd (Finset.min'_le _ j (by simp [hj'])) (not_le.mpr hj)
    have h1 := congrFun hc ⟨r - 1 - j0.val, by have := j0.isLt; omega⟩
    rw [hT, map_sum, map_sum, Finset.sum_eq_single j0] at h1
    · rw [map_smul, map_smul, ← Module.End.mul_apply, ← pow_add,
        show r - 1 - j0.val + j0.val = r - 1 by omega, smul_eq_mul] at h1
      exact mul_ne_zero hj0 hf h1
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hmin j h, zero_smul, map_zero, map_zero]
      · have h' : j0.val < j.val := h
        rw [map_smul, map_smul, ← Module.End.mul_apply, ← pow_add,
          hpow _ (show r ≤ r - 1 - j0.val + j.val by have := j.isLt; have := j0.isLt; omega),
          map_zero,
          smul_zero]
    · simp
  have hli : LinearIndependent k fam := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have := tri c (by rw [hc, map_zero])
    intro j; rw [this]; rfl
  set U := Submodule.span k (Set.range fam)
  set W := LinearMap.ker T
  have hUW : U ⊓ W = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hxU
    rw [tri c hxW]
    simp
  have hdimU : finrank k U = r := by rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hdimW : finrank k V ≤ r + finrank k W := by
    have h1 : finrank k (LinearMap.range T) + finrank k (LinearMap.ker T) = finrank k V :=
      LinearMap.finrank_range_add_finrank_ker T
    have h2 : finrank k (LinearMap.range T) ≤ r :=
      (Submodule.finrank_le _).trans (Module.finrank_fin_fun k).le
    have h3 : finrank k W = finrank k (LinearMap.ker T) := rfl
    omega
  have hsup : U ⊔ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hUW, finrank_bot] at this
    have := Submodule.finrank_le (U ⊔ W)
    omega
  have hUinv : ∀ x ∈ U, N x ∈ U := by
    have : U ≤ U.comap N := Submodule.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      show N ((N ^ j.val) v) ∈ U
      rw [← Module.End.mul_apply, ← pow_succ']
      by_cases h : j.val + 1 < r
      · exact Submodule.subset_span ⟨⟨j.val + 1, h⟩, rfl⟩
      · rw [hpow _ (by omega)]; exact U.zero_mem)
    exact fun x hx ↦ this hx
  have hWinv : ∀ x ∈ W, N x ∈ W := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext i
    rw [hT, ← Module.End.mul_apply, ← pow_succ, Pi.zero_apply]
    by_cases h : i.val + 1 < r
    · have := congrFun hx ⟨i.val + 1, h⟩
      rwa [hT] at this
    · rw [hpow _ (by omega)]; exact map_zero f
  have hcompl : IsCompl U W := ⟨disjoint_iff.mpr hUW, codisjoint_iff.mpr hsup⟩
  have hU0 : U ≠ ⊥ := by
    intro h
    have : fam ⟨0, hrpos⟩ ∈ U := Submodule.subset_span ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at this
    apply hv
    have hv0 : v = 0 := by simpa [fam] using this
    rw [hv0, map_zero]
  have hW0 : W = ⊥ := (hind U W hcompl hUinv hWinv).resolve_left hU0
  have hUtop : U = ⊤ := by rw [← hsup, hW0, sup_bot_eq]
  -- the basis `b_j = N^{r-1-j} v`
  let bfam : Fin r → V := fun j ↦ fam (Fin.rev j)
  have hli' : LinearIndependent k bfam := hli.comp _ Fin.rev_injective
  have hsp : ⊤ ≤ Submodule.span k (Set.range bfam) := by
    rw [show Set.range bfam = Set.range fam from Fin.rev_surjective.range_comp fam]
    exact hUtop.ge
  let bs := Basis.mk hli' hsp
  have hbs : ∀ j' : Fin r, bs j' = (N ^ (r - 1 - j'.val)) v := fun j' ↦ by
    rw [Basis.mk_apply]; simp only [bfam, fam, Fin.val_rev]; congr 2; omega
  have hself : ∀ j' : Fin r, bs.equivFun (bs j') = Pi.single j' 1 := fun j' ↦ funext fun i ↦ by
    rw [Basis.equivFun_self, Pi.single_apply]
    by_cases h : i = j'
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  refine ⟨r, bs.equivFun, fun x ↦ ?_⟩
  have key : bs.equivFun.toLinearMap ∘ₗ N = shiftN r ∘ₗ bs.equivFun.toLinearMap := by
    refine bs.ext fun j ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    show bs.equivFun (N (bs j)) = shiftN r (bs.equivFun (bs j))
    rw [hself]
    funext i
    rw [shiftN_apply]
    by_cases hj : j.val = 0
    · have hN : N (bs j) = 0 := by
        rw [hbs, ← Module.End.mul_apply, ← pow_succ', hpow _ (by omega)]
      rw [hN, map_zero, Pi.zero_apply]
      split_ifs with h
      · rw [Pi.single_apply, if_neg]; intro h'; rw [Fin.ext_iff] at h'; simp only at h'; omega
      · rfl
    · have hN : N (bs j) = bs ⟨j.val - 1, by have := j.isLt; omega⟩ := by
        rw [hbs, hbs, ← Module.End.mul_apply, ← pow_succ']; congr 2; simp only; omega
      rw [hN, hself]
      split_ifs with h
      · by_cases hij : i.val + 1 = j.val
        · rw [Pi.single_apply, Pi.single_apply, if_pos (Fin.ext (by simp only; omega)),
            if_pos (Fin.ext (by simp only; omega))]
        · rw [Pi.single_apply, Pi.single_apply,
            if_neg (fun h' ↦ hij (by rw [Fin.ext_iff] at h'; simp only at h'; omega)),
            if_neg (fun h' ↦ hij (by rw [Fin.ext_iff] at h'; simp only at h'; omega))]
      · rw [Pi.single_apply, if_neg]
        intro h'; rw [Fin.ext_iff] at h'; simp only at h'; have := j.isLt; omega
  exact LinearMap.congr_fun key x

/-- **Jordan normal form of an indecomposable automorphism.** Over an algebraically closed
field, an automorphism of a nonzero finite-dimensional space without nontrivial commuting
idempotents is similar to a single Jordan block `J_n(μ)`, `μ ≠ 0`. -/
theorem exists_jordan [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (φ : V ≃ₗ[k] V)
    (hind : IdemIndec φ.toLinearMap) :
    ∃ (n : ℕ) (μ : kˣ) (ψ : V ≃ₗ[k] (Fin n → k)), ∀ y, ψ (φ y) = jordan n (μ : k) (ψ y) := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue φ.toLinearMap
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hφv : φ v = μ • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hv0
    apply φ.injective
    rw [map_zero, hφv, h0, zero_smul]
  set N : V →ₗ[k] V := φ.toLinearMap - μ • LinearMap.id
  have hφN : ∀ y, φ y = μ • y + N y := fun y ↦ by simp [N]
  -- invariance under `N` is invariance under `φ`
  have hinv : ∀ U : Submodule k V, (∀ x ∈ U, N x ∈ U) → ∀ x ∈ U, φ x ∈ U := fun U hU x hx ↦ by
    rw [hφN]; exact U.add_mem (U.smul_mem _ hx) (hU x hx)
  have hindN : ∀ U W : Submodule k V, IsCompl U W → (∀ x ∈ U, N x ∈ U) → (∀ x ∈ W, N x ∈ W) →
      U = ⊥ ∨ W = ⊥ := fun U W hc hU hW ↦ hind.compl hc (hinv U hU) (hinv W hW)
  -- Fitting decomposition
  obtain ⟨m, hm1, hm⟩ := ((Filter.eventually_ge_atTop 1).and
    (LinearMap.eventually_isCompl_ker_pow_range_pow N)).exists
  have hcomm : ∀ x, N ((N ^ m) x) = (N ^ m) (N x) := fun x ↦ by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
  have hK : ∀ x ∈ LinearMap.ker (N ^ m), N x ∈ LinearMap.ker (N ^ m) := fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢; rw [← hcomm, hx, map_zero]
  have hR : ∀ x ∈ LinearMap.range (N ^ m), N x ∈ LinearMap.range (N ^ m) := by
    rintro _ ⟨y, rfl⟩; exact ⟨N y, (hcomm y).symm⟩
  have hNv : N v = 0 := by simp [N, hφv]
  have hker : LinearMap.ker (N ^ m) ≠ ⊥ := by
    intro h
    have : v ∈ LinearMap.ker (N ^ m) := by
      rw [LinearMap.mem_ker, show m = (m - 1) + 1 by omega, pow_succ, Module.End.mul_apply, hNv,
        map_zero]
    rw [h, Submodule.mem_bot] at this
    exact hv0 this
  have hran := (hindN _ _ hm hK hR).resolve_left hker
  have hnil : IsNilpotent N := ⟨m, LinearMap.range_eq_bot.mp hran⟩
  obtain ⟨n, ψ, hψ⟩ := exists_cyclic N hnil hindN
  refine ⟨n, Units.mk0 μ hμ0, ψ, fun y ↦ ?_⟩
  rw [hφN, map_add, map_smul, hψ, jordan_eq]
  rfl

end Exists

end BrickAccessibility
