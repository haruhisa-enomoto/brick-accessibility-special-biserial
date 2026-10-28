module

public import BrickAccessibility.Geometry.KernelVector
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Determinant

/-!
# Kernels of surjections in a stable family are polynomially covered

Let `H` be a space of linear maps `M → N` with `dim N + 1 = dim M`, and let
`E` be a space of endomorphisms of `N` containing the identity with `E H ⊆ H`.
The kernel vectors of the surjective maps in `H` are covered by finitely many
images of polynomial maps from `k^(dim H - dim E + 1)`
(`kernel_polyCovered`).

The proof slices the free action of the invertible elements of `E` by affine
coordinate charts of `H`. For a surjective `h`, the map `g ↦ g h` embeds `E`
into `H`; some coordinate projection onto `dim E` coordinates is bijective on
its image. Prescribing those coordinates from a finite grid determines
`g`, and a grid point with `det g ≠ 0` exists because the determinant is a
nonzero polynomial of bounded degree. The kernel line of the resulting
surjection is read off by `kernelVec`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open MvPolynomial Module Matrix

universe u

variable {k : Type u} [Field k]

/-! ### Polynomial covers -/

/-- A set is covered by finitely many images of polynomial maps from `k^e`. -/
def PolyCovered (k : Type u) [Field k] {W : Type*} [AddCommGroup W] [Module k W] (S : Set W) (e : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (P : ι → (Fin e → k) → W),
    (∀ i, IsPolyMap (P i)) ∧ S ⊆ ⋃ i, Set.range (P i)

namespace PolyCovered

variable {W : Type*} [AddCommGroup W] [Module k W]

theorem mono {S S' : Set W} {e : ℕ} (h : PolyCovered k S e) (hS : S' ⊆ S) :
    PolyCovered k S' e := by
  obtain ⟨ι, hι, P, hP, hcov⟩ := h
  exact ⟨ι, hι, P, hP, hS.trans hcov⟩

/-- Reindex a cover whose sources are finite coordinate types. -/
theorem of_fintype {S : Set W} {ι : Type} [Finite ι] {σ : ι → Type} [∀ i, Fintype (σ i)]
    {e : ℕ} (hσ : ∀ i, Fintype.card (σ i) = e) (P : ∀ i, (σ i → k) → W)
    (hP : ∀ i, IsPolyMap (P i)) (hcov : S ⊆ ⋃ i, Set.range (P i)) : PolyCovered k S e := by
  classical
  let eqv : ∀ i, σ i ≃ Fin e := fun i ↦ (Fintype.equivFin (σ i)).trans (finCongr (hσ i))
  refine ⟨ι, inferInstance, fun i x ↦ P i (fun j ↦ x (eqv i j)), fun i φ ↦ ?_, ?_⟩
  · exact (hP i φ).comp_affine _ fun j ↦ IsPolyFun.var _
  · intro v hv
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hcov hv)
    refine Set.mem_iUnion.mpr ⟨i, fun j ↦ x ((eqv i).symm j), ?_⟩
    simp

theorem le {S : Set W} {e e' : ℕ} (h : PolyCovered k S e) (hle : e ≤ e') : PolyCovered k S e' := by
  obtain ⟨ι, hι, P, hP, hcov⟩ := h
  refine ⟨ι, hι, fun i x ↦ P i (fun j ↦ x (Fin.castLE hle j)), fun i φ ↦ ?_, ?_⟩
  · exact (hP i φ).comp_affine _ fun j ↦ IsPolyFun.var _
  · intro v hv
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hcov hv)
    refine Set.mem_iUnion.mpr ⟨i, fun j ↦ if h : (j : ℕ) < e then x ⟨j, h⟩ else 0, ?_⟩
    simp only
    congr 1
    funext j
    simp [Fin.castLE, j.2]

theorem image {W' : Type*} [AddCommGroup W'] [Module k W'] {S : Set W} {e : ℕ}
    (h : PolyCovered k S e) (L : W →ₗ[k] W') : PolyCovered k (L '' S) e := by
  obtain ⟨ι, hι, P, hP, hcov⟩ := h
  refine ⟨ι, hι, fun i x ↦ L (P i x), fun i ↦ (hP i).comp_linear L, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hcov hv)
  exact Set.mem_iUnion.mpr ⟨i, x, rfl⟩

theorem zero (e : ℕ) : PolyCovered k ({0} : Set W) e := by
  refine ⟨Unit, inferInstance, fun _ _ ↦ 0, fun _ φ ↦ ?_, ?_⟩
  · simpa using IsPolyFun.const (σ := Fin e) (0 : k)
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact Set.mem_iUnion.mpr ⟨(), fun _ ↦ 0, rfl⟩

theorem union {S S' : Set W} {e : ℕ} (h : PolyCovered k S e) (h' : PolyCovered k S' e) :
    PolyCovered k (S ∪ S') e := by
  obtain ⟨ι, hι, P, hP, hcov⟩ := h
  obtain ⟨ι', hι', P', hP', hcov'⟩ := h'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim P P', fun i ↦ ?_, ?_⟩
  · cases i <;> simp [hP, hP']
  · rintro v (hv | hv)
    · obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hcov hv)
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, x, rfl⟩
    · obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hcov' hv)
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, x, rfl⟩

theorem biUnion {α : Type*} (T : Finset α) {S : α → Set W} {e : ℕ}
    (h : ∀ a ∈ T, PolyCovered k (S a) e) : PolyCovered k (⋃ a ∈ T, S a) e := by
  classical
  induction T using Finset.induction_on with
  | empty => exact (zero e).mono (by simp)
  | insert a T ha ih =>
      rw [Finset.set_biUnion_insert]
      exact (h a (Finset.mem_insert_self a T)).union
        (ih fun b hb ↦ h b (Finset.mem_insert_of_mem hb))

/-- A covered space has dimension at most the covering dimension. -/
theorem finrank_le [Infinite k] [FiniteDimensional k W] {e : ℕ}
    (h : PolyCovered k (Set.univ : Set W) e) : finrank k W ≤ e := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ι, hι, P, hP, hcov⟩ := h
  exact not_univ_subset_iUnion_range (fun _ : ι ↦ Fin e) P hP (fun _ ↦ by simpa using hlt) hcov

end PolyCovered

/-! ### Coordinate charts -/

/-- An injective linear map into `k^d` is injective on some set of `dim E`
coordinates. -/
theorem exists_coord_chart {E : Type*} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    {d : ℕ} (T : E →ₗ[k] (Fin d → k)) (hT : Function.Injective T) :
    ∃ s : Finset (Fin d), s.card = finrank k E ∧
      Function.Injective (fun g : E ↦ fun i : s ↦ T g i) := by
  classical
  let ℓ : Fin d → Module.Dual k E := fun i ↦ LinearMap.proj i ∘ₗ T
  have hspan : Submodule.span k (Set.range ℓ) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz ↦ ?_
    have : T z ≠ 0 := fun h ↦ hz (hT (by rw [h, map_zero]))
    obtain ⟨i, hi⟩ : ∃ i, T z i ≠ 0 := by
      by_contra hc; push Not at hc; exact this (funext hc)
    exact ⟨ℓ i, ⟨i, rfl⟩, by simpa [ℓ] using hi⟩
  obtain ⟨b, hb, hbspan, hbli⟩ := exists_linearIndependent k (Set.range ℓ)
  have hbfin : b.Finite := (Set.finite_range ℓ).subset hb
  have := hbfin.fintype
  choose idx hidx using fun φ : b ↦ hb φ.2
  have hidx_inj : Function.Injective idx := by
    intro φ ψ h
    apply Subtype.ext
    rw [← hidx φ, ← hidx ψ, h]
  refine ⟨Finset.univ.image idx, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hidx_inj, Finset.card_univ]
    have h1 := finrank_span_eq_card hbli
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan, hspan, finrank_top,
      Subspace.dual_finrank_eq] at h1
    exact h1.symm
  · let R : E →ₗ[k] ((Finset.univ.image idx) → k) :=
      LinearMap.pi fun i ↦ LinearMap.proj (i : Fin d) ∘ₗ T
    change Function.Injective R
    rw [injective_iff_map_eq_zero]
    intro g hg
    have hvan : ∀ φ ∈ b, φ g = 0 := by
      intro φ hφ
      have hmem : idx ⟨φ, hφ⟩ ∈ Finset.univ.image idx := Finset.mem_image_of_mem _ (by simp)
      have := congrFun hg ⟨_, hmem⟩
      simp only [R, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Pi.zero_apply] at this
      have h2 := hidx ⟨φ, hφ⟩
      simp only at h2
      rw [← h2]
      simpa [ℓ] using this
    have hall : ∀ φ : Module.Dual k E, φ g = 0 := by
      intro φ
      have hφ : φ ∈ Submodule.span k b := by rw [hbspan, hspan]; trivial
      induction hφ using Submodule.span_induction with
      | mem x hx => exact hvan x hx
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    exact (Module.forall_dual_apply_eq_zero_iff k g).mp hall

/-! ### The determinant as a polynomial -/

theorem totalDegree_intCast {σ : Type*} (z : ℤ) :
    ((z : MvPolynomial σ k)).totalDegree = 0 := by
  rw [← map_intCast (C : k →+* MvPolynomial σ k)]
  exact totalDegree_C _

/-- The determinant of a linear family of endomorphisms is a polynomial of total
degree at most the dimension. -/
theorem exists_det_poly {N : Type*} [AddCommGroup N] [Module k N] [FiniteDimensional k N]
    {σ : Type*} [Fintype σ] [DecidableEq σ] (φ : (σ → k) →ₗ[k] (N →ₗ[k] N)) :
    ∃ P : MvPolynomial σ k, P.totalDegree ≤ finrank k N ∧
      ∀ c, eval c P = LinearMap.det (φ c) := by
  classical
  let b := Module.finBasis k N
  let m := finrank k N
  let Mp : Matrix (Fin m) (Fin m) (MvPolynomial σ k) := fun a a' ↦
    ∑ i, X i * C (LinearMap.toMatrix b b (φ (Pi.single i 1)) a a')
  refine ⟨Mp.det, ?_, fun c ↦ ?_⟩
  · rw [Matrix.det_apply']
    refine totalDegree_finsetSum_le fun τ _ ↦ ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_intCast, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, (Mp (τ i) i).totalDegree ≤ ∑ _i : Fin m, 1 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          refine totalDegree_finsetSum_le fun j _ ↦ ?_
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, add_zero, totalDegree_X]
      _ = m := by simp
  · have hc : φ c = ∑ i, c i • φ (Pi.single i 1) := by
      have : c = ∑ i, c i • (Pi.single i (1 : k) : σ → k) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [this]
      simp [map_sum, map_smul]
    rw [RingHom.map_det, ← LinearMap.det_toMatrix b, hc]
    congr 1
    ext a a'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [Mp, map_sum, Matrix.sum_apply]

/-! ### The kernel cover -/

/-- **Kernel cover.** Kernel vectors of surjections in `H` are covered by
polynomial images from `k^(dim H - dim E + 1)`. -/
theorem kernel_polyCovered [Infinite k] {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [FiniteDimensional k M] [FiniteDimensional k N]
    (hdim : finrank k N + 1 = finrank k M)
    (H : Submodule k (M →ₗ[k] N)) (E : Submodule k (N →ₗ[k] N)) (hid : LinearMap.id ∈ E)
    (hEH : ∀ g ∈ E, ∀ h ∈ H, g ∘ₗ h ∈ H) :
    PolyCovered k {v : M | ∃ h ∈ H, Function.Surjective h ∧ h v = 0}
      (finrank k H - finrank k E + 1) := by
  classical
  set n := finrank k N with hn
  set d := finrank k H
  set e := finrank k E
  let bM : Basis (Fin (n + 1)) k M := Module.finBasisOfFinrankEq k M hdim.symm
  let bN : Basis (Fin n) k N := Module.finBasis k N
  let bH : Basis (Fin d) k H := Module.finBasis k H
  obtain ⟨T, hTcard⟩ := Infinite.exists_subset_card_eq k (n + 1)
  let tEq : Fin (n + 1) ≃ T := (finCongr hTcard.symm).trans T.equivFin.symm
  -- index data
  let ι : Type := Σ s : {s : Finset (Fin d) // s.card = e}, (s.1 → Fin (n + 1)) × Fin (n + 1)
  let σ : ι → Type := fun i ↦ Option {j : Fin d // j ∉ i.1.1}
  let coef : (i : ι) → ({j : Fin d // j ∉ i.1.1} → k) → Fin d → k := fun i w j ↦
    if h : j ∈ i.1.1 then (tEq (i.2.1 ⟨j, h⟩) : k) else w ⟨j, h⟩
  let hval : (i : ι) → ({j : Fin d // j ∉ i.1.1} → k) → (M →ₗ[k] N) := fun i w ↦
    ∑ j, coef i w j • (bH j : M →ₗ[k] N)
  let Xm : (i : ι) → ({j : Fin d // j ∉ i.1.1} → k) → Matrix (Fin n) (Fin (n + 1)) k :=
    fun i w ↦ LinearMap.toMatrix bM bN (hval i w)
  let P : (i : ι) → (σ i → k) → M := fun i x ↦
    x none • ∑ l, kernelVec (Xm i (fun j ↦ x (some j))) i.2.2 l • bM l
  have hcoef : ∀ i (j : Fin d), IsPolyFun (fun w : {j : Fin d // j ∉ i.1.1} → k ↦ coef i w j) := by
    intro i j
    by_cases h : j ∈ i.1.1
    · simpa [coef, h] using IsPolyFun.const _
    · simpa [coef, h] using IsPolyFun.var (⟨j, h⟩ : {j : Fin d // j ∉ i.1.1})
  have hXm : ∀ i a b, IsPolyFun (fun w ↦ Xm i w a b) := by
    intro i a b
    have : ∀ w, Xm i w a b = ∑ j, coef i w j * LinearMap.toMatrix bM bN (bH j) a b := by
      intro w
      simp [Xm, hval, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp_rw [this]
    exact IsPolyFun.sum _ fun j _ ↦ (hcoef i j).mul (IsPolyFun.const _)
  have hP : ∀ i, IsPolyMap (P i) := by
    intro i
    exact IsPolyMap.option_smul (k := k)
      (F := fun w ↦ ∑ l, kernelVec (Xm i w) i.2.2 l • bM l)
      (IsPolyMap.sum_smul _ (fun l ↦ IsPolyFun.kernelVec (hXm i) _ l) _)
  refine PolyCovered.of_fintype (σ := σ) (fun i ↦ ?_) P hP ?_
  · simp only [σ, Fintype.card_option]
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, i.1.2]
  -- the covering
  rintro v ⟨h, hH, hsurj, hv⟩
  -- the orbit map `g ↦ g h`
  let Φ : E →ₗ[k] H :=
    { toFun := fun g ↦ ⟨g.1 ∘ₗ h, hEH _ g.2 _ hH⟩
      map_add' := fun g g' ↦ by ext; simp
      map_smul' := fun c g ↦ by ext; simp }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have := congrArg (fun f : H ↦ (f : M →ₗ[k] N) x) hg
    simpa [Φ] using this
  let Tc : E →ₗ[k] (Fin d → k) := bH.equivFun.toLinearMap ∘ₗ Φ
  have hTc : Function.Injective Tc := bH.equivFun.injective.comp hΦ
  obtain ⟨s, hscard, hsinj⟩ := exists_coord_chart Tc hTc
  let R : E →ₗ[k] (s → k) := LinearMap.pi fun j ↦ LinearMap.proj (j : Fin d) ∘ₗ Tc
  have hRinj : Function.Injective R := hsinj
  have hRbij : Function.Bijective R := by
    refine ⟨hRinj, ?_⟩
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hRinj
    · simp [hscard, e]
  let A : E ≃ₗ[k] (s → k) := LinearEquiv.ofBijective R hRbij
  let φ : (s → k) →ₗ[k] (N →ₗ[k] N) := E.subtype ∘ₗ A.symm.toLinearMap
  obtain ⟨Pd, hPdeg, hPev⟩ := exists_det_poly φ
  have hPne : Pd ≠ 0 := by
    intro h0
    have := hPev (A ⟨LinearMap.id, hid⟩)
    simp [h0, φ] at this
  -- a grid point with nonzero determinant
  obtain ⟨c, hcT, hc⟩ : ∃ c : s → k, (∀ j, c j ∈ T) ∧ eval c Pd ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hPne
    refine eq_zero_of_eval_zero_at_prod_finset Pd (fun _ ↦ T) (fun j ↦ ?_) hcon
    calc Pd.degreeOf j ≤ Pd.totalDegree := degreeOf_le_totalDegree _ _
      _ ≤ n := hPdeg
      _ < T.card := by omega
  set g := A.symm c with hg
  have hdet : LinearMap.det (g : N →ₗ[k] N) ≠ 0 := by
    intro h0; apply hc; rw [hPev c]; exact h0
  have hgunit : IsUnit (g : N →ₗ[k] N) := by
    rw [LinearMap.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hdet
  have hgbij : Function.Bijective (g : N →ₗ[k] N) := (Module.End.isUnit_iff _).mp hgunit
  set h' : H := Φ g with hh'
  have hh'coe : (h' : M →ₗ[k] N) = (g : N →ₗ[k] N) ∘ₗ h := rfl
  have hsurj' : Function.Surjective (h' : M →ₗ[k] N) := by
    rw [hh'coe, LinearMap.coe_comp]; exact hgbij.2.comp hsurj
  have hv' : (h' : M →ₗ[k] N) v = 0 := by rw [hh'coe, LinearMap.comp_apply, hv, map_zero]
  -- the chart index
  let tc : s → Fin (n + 1) := fun j ↦ tEq.symm ⟨c j, hcT j⟩
  let i : ι := ⟨⟨s, hscard⟩, tc, 0⟩
  let w : {j : Fin d // j ∉ s} → k := fun j ↦ bH.equivFun h' j
  have hcoord : ∀ j : s, bH.equivFun h' j = c j := by
    intro j
    have := congrFun (A.apply_symm_apply c) j
    show bH.equivFun h' j = c j
    rw [← this]
    rfl
  have hhval : ∀ J, hval ⟨⟨s, hscard⟩, tc, J⟩ w = (h' : M →ₗ[k] N) := by
    intro J
    conv_rhs => rw [← bH.sum_equivFun h']
    simp only [hval, coef, Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j ∈ s
    · simp only [hj, dite_true]
      rw [hcoord ⟨j, hj⟩]
      simp [tc]
    · simp [hj, w]
  -- the matrix and its column
  let Xh := LinearMap.toMatrix bM bN (h' : M →ₗ[k] N)
  have hXsurj : Function.Surjective Xh.mulVecLin := by
    intro y
    obtain ⟨z, hz⟩ := hsurj' (bN.equivFun.symm y)
    refine ⟨bM.repr z, ?_⟩
    rw [Matrix.mulVecLin_apply, LinearMap.toMatrix_mulVec_repr, hz]
    ext j; simp [Finsupp.single_apply]
  obtain ⟨J, hJ⟩ := exists_det_dropCol_ne_zero Xh hXsurj
  have hker : Xh *ᵥ (bM.repr v) = 0 := by
    rw [LinearMap.toMatrix_mulVec_repr, hv']; simp
  obtain ⟨t, ht⟩ := exists_eq_smul_kernelVec Xh J hJ _ hker
  refine Set.mem_iUnion.mpr ⟨⟨⟨s, hscard⟩, tc, J⟩, fun o ↦ o.elim t w, ?_⟩
  simp only [P, Option.elim]
  have hX : Xm ⟨⟨s, hscard⟩, tc, J⟩ w = Xh :=
    congrArg (LinearMap.toMatrix bM bN) (hhval J)
  rw [hX]
  conv_rhs => rw [← bM.sum_repr v]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [smul_smul]
  congr 1
  have := congrFun ht l
  simpa using this.symm

end BrickAccessibility
