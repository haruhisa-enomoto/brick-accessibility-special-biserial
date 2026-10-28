module

public import BrickAccessibility.Classification.Intervals
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Splitting the regular part of a linear relation

Let `R ⊆ X × X` be a linear relation on a finite-dimensional space and `N ≤ X` a
subspace in which every vector has an `R`-successor and an `R`-predecessor. Let
`K ≤ N` consist of the vectors of `N` with a chain in `N` to `0` (`Kinf`). Then
`K` is closed under successors (`fwd_mem`), and `N = U ⊕ K` for a subspace `U` on
which `R` restricts to the graph of an automorphism (`exists_split`).

The proof chooses a section of `R` that is nilpotent on `K` (it lowers the
length of the chain to `0`) and solves a Sylvester equation by a finite Neumann
series.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

namespace Split

variable {k X : Type*} [Field k] [AddCommGroup X] [Module k X]
variable (R : Submodule k (X × X)) (N : Submodule k X)

/-- Vectors of `N` with a chain of length `j` in `N` ending at `0`. -/
def Kd : ℕ → Submodule k X
  | 0 => ⊥
  | j + 1 => N ⊓ (R ⊓ (⊤ : Submodule k X).prod (Kd j)).map (LinearMap.fst k X X)

theorem mem_Kd_succ {j : ℕ} {x : X} : x ∈ Kd R N (j + 1) ↔ x ∈ N ∧ ∃ y ∈ Kd R N j, (x, y) ∈ R := by
  simp only [Kd, Submodule.mem_inf, Submodule.mem_map, LinearMap.fst_apply, Prod.exists,
    Submodule.mem_prod, Submodule.mem_top, true_and, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨hx, y, hR, hy⟩; exact ⟨hx, y, hy, hR⟩
  · rintro ⟨hx, y, hy, hR⟩; exact ⟨hx, y, hR, hy⟩

theorem Kd_le_N (j : ℕ) : Kd R N j ≤ N := by
  cases j with
  | zero => exact bot_le
  | succ j => exact inf_le_left

theorem Kd_mono : Monotone (Kd R N) := by
  refine monotone_nat_of_le_succ fun j ↦ ?_
  induction j with
  | zero => exact bot_le
  | succ j ih =>
      intro x hx
      obtain ⟨hxN, y, hy, hR⟩ := (mem_Kd_succ R N).mp hx
      exact (mem_Kd_succ R N).mpr ⟨hxN, y, ih hy, hR⟩

/-- Vectors of `N` with a chain in `N` to `0`. -/
def Kinf : Submodule k X := ⨆ j, Kd R N j

theorem Kd_le_Kinf (j : ℕ) : Kd R N j ≤ Kinf R N := le_iSup (Kd R N) j

theorem Kinf_le_N : Kinf R N ≤ N := iSup_le (Kd_le_N R N)

variable [FiniteDimensional k X]

theorem exists_stable : ∃ J, Kinf R N = Kd R N J := by
  obtain ⟨J, hJ⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨Kd R N, Kd_mono R N⟩
  refine ⟨J, le_antisymm (iSup_le fun j ↦ ?_) (Kd_le_Kinf R N J)⟩
  rcases le_total j J with h | h
  · exact Kd_mono R N h
  · exact (hJ j h).symm.le

theorem mem_Kinf_iff {x : X} : x ∈ Kinf R N ↔ ∃ j, x ∈ Kd R N j := by
  obtain ⟨J, hJ⟩ := exists_stable R N
  constructor
  · intro hx; exact ⟨J, hJ ▸ hx⟩
  · rintro ⟨j, hj⟩; exact Kd_le_Kinf R N j hj

theorem pred_mem {x y : X} (hx : x ∈ N) (hy : y ∈ Kinf R N) (hR : (x, y) ∈ R) : x ∈ Kinf R N := by
  obtain ⟨j, hj⟩ := (mem_Kinf_iff R N).mp hy
  exact (mem_Kinf_iff R N).mpr ⟨j + 1, (mem_Kd_succ R N).mpr ⟨hx, y, hj, hR⟩⟩

theorem zero_succ_mem {x : X} (hx : x ∈ N) (hR : (x, 0) ∈ R) : x ∈ Kinf R N :=
  pred_mem R N hx (Submodule.zero_mem _) hR

variable {R N}

theorem exists_pred_section (hran : ∀ y ∈ N, ∃ x ∈ N, (x, y) ∈ R) :
    ∃ π : N →ₗ[k] X, ∀ y : N, π y ∈ N ∧ (π y, (y : X)) ∈ R := by
  set G : Submodule k (X × X) := R ⊓ N.prod N
  let f : G →ₗ[k] N :=
    { toFun := fun g ↦ ⟨g.1.2, (Submodule.mem_prod.mp (Submodule.mem_inf.mp g.2).2).2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hR⟩ := hran y hy
    exact ⟨⟨(x, y), Submodule.mem_inf.mpr ⟨hR, Submodule.mem_prod.mpr ⟨hx, hy⟩⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨(LinearMap.fst k X X).comp (G.subtype.comp s), fun y ↦ ⟨?_, ?_⟩⟩
  · exact (Submodule.mem_prod.mp (Submodule.mem_inf.mp (s y).2).2).1
  · have h1 := (Submodule.mem_inf.mp (s y).2).1
    have h2 : ((s y : X × X)).2 = y := congrArg Subtype.val (LinearMap.congr_fun hs y)
    have : (((s y : X × X)).1, ((s y : X × X)).2) ∈ R := h1
    rw [h2] at this
    exact this

theorem exists_succ_section (hdom : ∀ x ∈ N, ∃ y ∈ N, (x, y) ∈ R) :
    ∃ A : N →ₗ[k] X, ∀ x : N, A x ∈ N ∧ ((x : X), A x) ∈ R := by
  set G : Submodule k (X × X) := R ⊓ N.prod N
  let f : G →ₗ[k] N :=
    { toFun := fun g ↦ ⟨g.1.1, (Submodule.mem_prod.mp (Submodule.mem_inf.mp g.2).2).1⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hR⟩ := hdom x hx
    exact ⟨⟨(x, y), Submodule.mem_inf.mpr ⟨hR, Submodule.mem_prod.mpr ⟨hx, hy⟩⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨(LinearMap.snd k X X).comp (G.subtype.comp s), fun x ↦ ⟨?_, ?_⟩⟩
  · exact (Submodule.mem_prod.mp (Submodule.mem_inf.mp (s x).2).2).2
  · have h1 := (Submodule.mem_inf.mp (s x).2).1
    have h2 : ((s x : X × X)).1 = x := congrArg Subtype.val (LinearMap.congr_fun hs x)
    have : (((s x : X × X)).1, ((s x : X × X)).2) ∈ R := h1
    rw [h2] at this
    exact this

/-- `K` is closed under successors. -/
theorem fwd_mem (hdom : ∀ x ∈ N, ∃ y ∈ N, (x, y) ∈ R) (hran : ∀ y ∈ N, ∃ x ∈ N, (x, y) ∈ R)
    {x y : X} (hx : x ∈ Kinf R N) (hy : y ∈ N) (hR : (x, y) ∈ R) : y ∈ Kinf R N := by
  obtain ⟨π, hπ⟩ := exists_pred_section hran
  -- `π` induces a surjection, hence a bijection, of `N / K`
  let πN : N →ₗ[k] N := LinearMap.codRestrict N π fun y ↦ (hπ y).1
  set KN : Submodule k N := (Kinf R N).comap N.subtype
  set Z : Submodule k N := KN.comap πN
  have hKZ : KN ≤ Z := fun z hz ↦ pred_mem R N (hπ z).1 hz (hπ z).2
  have hsurj : LinearMap.range πN ⊔ KN = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨w, hw, hR'⟩ := hdom z z.2
    have hd : (z : X) - π ⟨w, hw⟩ ∈ Kinf R N := by
      refine zero_succ_mem R N (Submodule.sub_mem _ z.2 (hπ _).1) ?_
      have := Submodule.sub_mem _ hR' (hπ ⟨w, hw⟩).2
      simpa using this
    refine Submodule.mem_sup.mpr ⟨πN ⟨w, hw⟩, ⟨_, rfl⟩, z - πN ⟨w, hw⟩, hd, by abel⟩
  have hker : LinearMap.ker πN ≤ Z := fun z hz ↦ by
    change πN z ∈ KN
    rw [LinearMap.mem_ker.mp hz]; exact Submodule.zero_mem _
  have hmap : Z.map πN ≤ LinearMap.range πN ⊓ KN :=
    le_inf (LinearMap.map_le_range) (Submodule.map_comap_le _ _)
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range πN) KN
  rw [hsurj, finrank_top] at d1
  have d2 := LinearMap.finrank_range_add_finrank_ker πN
  have d3 := LinearMap.finrank_range_add_finrank_ker (πN.domRestrict Z)
  have d4 : finrank k (LinearMap.ker (πN.domRestrict Z)) = finrank k (LinearMap.ker πN) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hker).finrank_eq
  have d5 : finrank k (LinearMap.range (πN.domRestrict Z)) ≤
      finrank k ↥(LinearMap.range πN ⊓ KN) := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.finrank_mono hmap
  have hZ : Z = KN := le_antisymm (Submodule.eq_of_le_of_finrank_le hKZ (by omega)).ge hKZ
  -- now `π y ∈ K`
  have hπy : π ⟨y, hy⟩ ∈ Kinf R N := by
    have hd : x - π ⟨y, hy⟩ ∈ Kinf R N := by
      have hxN := Kinf_le_N R N hx
      refine zero_succ_mem R N (Submodule.sub_mem _ hxN (hπ _).1) ?_
      have := Submodule.sub_mem _ hR (hπ ⟨y, hy⟩).2
      simpa using this
    have := Submodule.sub_mem _ hx hd
    simpa using this
  have hyZ : (⟨y, hy⟩ : N) ∈ Z := hπy
  rw [hZ] at hyZ
  exact hyZ

variable (R N) in
/-- A section of `R` lowering the length of chains to `0`, up to level `j`. -/
theorem exists_lowering (j : ℕ) :
    ∃ A : X →ₗ[k] X, ∀ i < j, ∀ x ∈ Kd R N (i + 1), A x ∈ Kd R N i ∧ (x, A x) ∈ R := by
  induction j with
  | zero => exact ⟨0, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
      obtain ⟨A, hA⟩ := ih
      obtain ⟨C, hC1, hC2⟩ := IFam.exists_relCompl (Kd_mono R N (Nat.le_succ j))
      obtain ⟨E, hE⟩ := Submodule.exists_isCompl (Kd R N (j + 1))
      -- `C` is complementary to `Kd j ⊔ E`
      have hCW : IsCompl C (Kd R N j ⊔ E) := by
        constructor
        · rw [disjoint_iff, eq_bot_iff]
          intro x hx
          obtain ⟨hxC, hxW⟩ := Submodule.mem_inf.mp hx
          obtain ⟨y, hy, e, he, rfl⟩ := Submodule.mem_sup.mp hxW
          have hCle : C ≤ Kd R N (j + 1) := hC1 ▸ le_sup_left
          have heK : e ∈ Kd R N (j + 1) := by
            have : e = (y + e) - y := by abel
            rw [this]
            exact Submodule.sub_mem _ (hCle hxC) (Kd_mono R N (Nat.le_succ j) hy)
          have he0 : e = 0 := by
            have := hE.inf_eq_bot
            exact (Submodule.mem_bot k).mp (this ▸ Submodule.mem_inf.mpr ⟨heK, he⟩)
          subst he0
          rw [add_zero] at hxC ⊢
          exact hC2 ▸ Submodule.mem_inf.mpr ⟨hxC, hy⟩
        · rw [codisjoint_iff, ← sup_assoc, hC1]
          exact hE.sup_eq_top
      -- a successor map on `C` into `Kd j`
      set G : Submodule k (X × X) := R ⊓ C.prod (Kd R N j)
      let f : G →ₗ[k] C :=
        { toFun := fun g ↦ ⟨g.1.1, (Submodule.mem_prod.mp (Submodule.mem_inf.mp g.2).2).1⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      have hf : Function.Surjective f := by
        rintro ⟨x, hx⟩
        have hxK : x ∈ Kd R N (j + 1) := (hC1 ▸ le_sup_left : C ≤ _) hx
        obtain ⟨-, y, hy, hR⟩ := (mem_Kd_succ R N).mp hxK
        exact ⟨⟨(x, y), Submodule.mem_inf.mpr ⟨hR, Submodule.mem_prod.mpr ⟨hx, hy⟩⟩⟩, rfl⟩
      obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
      let Bm : C →ₗ[k] X := (LinearMap.snd k X X).comp (G.subtype.comp s)
      have hB : ∀ c : C, Bm c ∈ Kd R N j ∧ ((c : X), Bm c) ∈ R := by
        intro c
        refine ⟨(Submodule.mem_prod.mp (Submodule.mem_inf.mp (s c).2).2).2, ?_⟩
        have h1 := (Submodule.mem_inf.mp (s c).2).1
        have h2 : ((s c : X × X)).1 = c := congrArg Subtype.val (LinearMap.congr_fun hs c)
        have : (((s c : X × X)).1, ((s c : X × X)).2) ∈ R := h1
        rw [h2] at this
        exact this
      let pC := Submodule.projectionOnto C (Kd R N j ⊔ E) hCW
      let A' : X →ₗ[k] X := A + (Bm - A.comp C.subtype).comp pC
      have hA'K : ∀ x ∈ Kd R N j, A' x = A x := by
        intro x hx
        have : pC x = 0 :=
          Submodule.projectionOnto_apply_of_mem_right hCW (Submodule.mem_sup_left hx)
        simp [A', this]
      have hA'C : ∀ c : C, A' c = Bm c := by
        intro c
        have : pC c = c := Submodule.projectionOnto_apply_left hCW c
        simp [A', this]
      refine ⟨A', fun i hi x hx ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hA'K x (Kd_mono R N (by omega) hx)]
        exact hA i hi x hx
      · -- `x = c + y` with `c ∈ C`, `y ∈ Kd j`
        rw [← hC1] at hx
        obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
        rw [map_add, hA'C ⟨c, hc⟩, hA'K y hy]
        have hyA : A y ∈ Kd R N i ∧ (y, A y) ∈ R := by
          cases i with
          | zero =>
              have : y = 0 := (Submodule.mem_bot k).mp hy
              subst this
              refine ⟨by simp, ?_⟩
              rw [map_zero]
              exact R.zero_mem
          | succ i =>
              have := hA i (by omega) y hy
              exact ⟨Kd_mono R N (Nat.le_succ i) this.1, this.2⟩
        obtain ⟨hB1, hB2⟩ := hB ⟨c, hc⟩
        refine ⟨Submodule.add_mem _ hB1 hyA.1, ?_⟩
        have := Submodule.add_mem _ hB2 hyA.2
        simpa using this

omit [FiniteDimensional k X] in
theorem telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel

/-- **The splitting lemma.** -/
theorem exists_split (hdom : ∀ x ∈ N, ∃ y ∈ N, (x, y) ∈ R)
    (hran : ∀ y ∈ N, ∃ x ∈ N, (x, y) ∈ R) :
    ∃ (U : Submodule k X) (τ : U ≃ₗ[k] U), U ≤ N ∧ U ⊓ Kinf R N = ⊥ ∧ U ⊔ Kinf R N = N ∧
      ∀ u : U, ((u : X), (τ u : X)) ∈ R := by
  classical
  obtain ⟨J, hJ⟩ := exists_stable R N
  obtain ⟨A, hA⟩ := exists_lowering R N J
  have hAK : ∀ x ∈ Kinf R N, A x ∈ Kinf R N ∧ (x, A x) ∈ R := by
    intro x hx
    rw [hJ] at hx
    cases J with
    | zero =>
        have : x = 0 := (Submodule.mem_bot k).mp hx
        subst this
        exact ⟨by rw [map_zero]; exact Submodule.zero_mem _, by rw [map_zero]; exact R.zero_mem⟩
    | succ J =>
        obtain ⟨h1, h2⟩ := hA J (Nat.lt_succ_self J) x hx
        exact ⟨Kd_le_Kinf R N J h1, h2⟩
  have hnil : ∀ j ≤ J, ∀ x ∈ Kd R N j, (A ^ j) x = 0 := by
    intro j
    induction j with
    | zero => intro _ x hx; simpa using (Submodule.mem_bot k).mp hx
    | succ j ih =>
        intro hj x hx
        rw [pow_succ, Module.End.mul_apply]
        exact ih (by omega) _ (hA j (by omega) x hx).1
  have hnilK : ∀ x ∈ Kinf R N, (A ^ J) x = 0 := fun x hx ↦ hnil J le_rfl x (hJ ▸ hx)
  have hpowK : ∀ i, ∀ x ∈ Kinf R N, (A ^ i) x ∈ Kinf R N := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih =>
        intro x hx
        rw [pow_succ, Module.End.mul_apply]
        exact ih _ (hAK x hx).1
  obtain ⟨Ag, hAg⟩ := exists_succ_section hdom
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (Kinf R N)
  let p : X →ₗ[k] C' := Submodule.projectionOnto C' (Kinf R N) hC'.symm
  have hpK : ∀ x, x - (p x : X) ∈ Kinf R N := by
    intro x
    rw [← Submodule.ker_projectionOnto hC'.symm, LinearMap.mem_ker, map_sub]
    have : p (p x : X) = p x := Submodule.projectionOnto_apply_left hC'.symm (p x)
    rw [this, sub_self]
  have hpN : ∀ x ∈ N, (p x : X) ∈ N := by
    intro x hx
    have := Submodule.sub_mem _ hx (Kinf_le_N R N (hpK x))
    simpa using this
  set C : Submodule k X := C' ⊓ N
  have hCK : ∀ c ∈ C, c ∈ Kinf R N → c = 0 := by
    intro c hc hK
    have := hC'.inf_eq_bot
    exact (Submodule.mem_bot k).mp (this ▸ Submodule.mem_inf.mpr ⟨hK, hc.1⟩)
  -- the induced map on `C`
  let agC : C →ₗ[k] X := Ag.comp (Submodule.inclusion inf_le_right)
  have hagC : ∀ c : C, agC c ∈ N ∧ ((c : X), agC c) ∈ R := fun c ↦ hAg _
  let t : C →ₗ[k] C :=
    { toFun := fun c ↦ ⟨p (agC c), (p (agC c)).2, hpN _ (hagC c).1⟩
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  have ht : Function.Injective t := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    have h0 : (p (agC c) : X) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hc)
    have hK : agC c ∈ Kinf R N := by have := hpK (agC c); rwa [h0, sub_zero] at this
    have hcK : (c : X) ∈ Kinf R N := pred_mem R N c.2.2 hK (hagC c).2
    exact (Submodule.mem_bot k).mpr (Subtype.ext (hCK c c.2 hcK))
  let te : C ≃ₗ[k] C := LinearEquiv.ofInjectiveEndo t ht
  let κ : C →ₗ[k] X := agC - C.subtype.comp t
  have hκ : ∀ c, κ c ∈ Kinf R N := fun c ↦ hpK (agC c)
  let Sm : Module.End k C := te.symm.toLinearMap
  let μ : C →ₗ[k] X := ∑ i ∈ Finset.range J, (A ^ i).comp (κ.comp (Sm ^ (i + 1)))
  have hμK : ∀ c, μ c ∈ Kinf R N := by
    intro c
    simp only [μ, LinearMap.sum_apply, LinearMap.comp_apply]
    exact Submodule.sum_mem _ fun i _ ↦ hpowK i _ (hκ _)
  have hSt : ∀ (i : ℕ) (c : C), (Sm ^ (i + 1)) (t c) = (Sm ^ i) c := by
    intro i c
    rw [pow_succ, Module.End.mul_apply]
    congr 1
    exact te.symm_apply_apply c
  -- the Sylvester equation `μ t - A μ = κ`
  have heq : ∀ c, μ (t c) - A (μ c) = κ c := by
    intro c
    let f : ℕ → X := fun i ↦ (A ^ i) (κ ((Sm ^ i) c))
    have h1 : μ (t c) = ∑ i ∈ Finset.range J, f i := by
      simp only [μ, LinearMap.sum_apply, LinearMap.comp_apply, hSt, f]
    have h2 : A (μ c) = ∑ i ∈ Finset.range J, f (i + 1) := by
      simp only [μ, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, f]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Module.End.mul_apply, ← pow_succ']
    rw [h1, h2, ← Finset.sum_sub_distrib, telescope]
    simp only [f, pow_zero, Module.End.one_apply]
    rw [hnilK _ (hκ _), sub_zero]
  -- the subspace `U`
  let e : C →ₗ[k] X := C.subtype + μ
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    have h0 : (c : X) + μ c = 0 := LinearMap.mem_ker.mp hc
    have hcK : (c : X) ∈ Kinf R N := by
      have : (c : X) = -μ c := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact Submodule.neg_mem _ (hμK c)
    exact (Submodule.mem_bot k).mpr (Subtype.ext (hCK c c.2 hcK))
  let eU : C ≃ₗ[k] LinearMap.range e := LinearEquiv.ofInjective e he
  refine ⟨LinearMap.range e, eU.symm.trans (te.trans eU), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact Submodule.add_mem _ c.2.2 (Kinf_le_N R N (hμK c))
  · refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨⟨c, rfl⟩, hK⟩ := Submodule.mem_inf.mp hx
    have hcK : (c : X) ∈ Kinf R N := by
      have := Submodule.sub_mem _ hK (hμK c)
      simpa [e] using this
    have := hCK c c.2 hcK
    simp [e, show c = 0 from Subtype.ext this]
  · refine le_antisymm (sup_le ?_ (Kinf_le_N R N)) fun n hn ↦ ?_
    · rintro _ ⟨c, rfl⟩
      exact Submodule.add_mem _ c.2.2 (Kinf_le_N R N (hμK c))
    · let c : C := ⟨p n, (p n).2, hpN n hn⟩
      refine Submodule.mem_sup.mpr ⟨e c, ⟨c, rfl⟩, n - e c, ?_, by abel⟩
      have : n - e c = (n - (p n : X)) - μ c := by
        show n - ((c : X) + μ c) = _
        abel
      rw [this]
      exact Submodule.sub_mem _ (hpK n) (hμK c)
  · intro u
    obtain ⟨c, hc⟩ := eU.surjective u
    rw [← hc]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    change (e c, e (te c)) ∈ R
    have hte : te c = t c := rfl
    rw [hte]
    -- the successor `agC c + A (μ c)` of `e c` equals `e (t c)`
    have hsum : (e c, agC c + A (μ c)) ∈ R := by
      have := Submodule.add_mem _ (hagC c).2 (hAK _ (hμK c)).2
      simpa [e] using this
    have hval : agC c + A (μ c) = e (t c) := by
      have := heq c
      simp only [e, LinearMap.add_apply, Submodule.subtype_apply]
      have hκc : κ c = agC c - (t c : X) := rfl
      rw [hκc, sub_eq_iff_eq_add] at this
      rw [this]; abel
    rwa [hval] at hsum

end Split

end BrickAccessibility
