module

public import BrickAccessibility.Classification.BlockQuiver
public import BrickAccessibility.Classification.Natural

/-!
# Transports on block quiver modules

On the module `P → V` of a block quiver, the subspaces supported on a set of
positions (`blk J`) are closed under the transports along letters, with
explicit position sets (`tr_true_blk`, `tr_false_blk`). Hence every boundary
subspace of a half-word is a `blk` of an explicit set of positions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
variable (C : D.BlockQuiver V) (hC : C.KillsZeroPaths)

namespace BlockQuiver

/-- The module of a block quiver. -/
abbrev Mod := (C.toRep hC).Carrier

/-- Coordinates. -/
def val (f : C.Mod hC) : C.P → V := f

/-- The element with given coordinates. -/
def ofFun (f : C.P → V) : C.Mod hC := f

@[simp] theorem val_ofFun (f : C.P → V) : C.val hC (C.ofFun hC f) = f := rfl
@[simp] theorem ofFun_val (f : C.Mod hC) : C.ofFun hC (C.val hC f) = f := rfl

/-- `ofFun` as a linear map. -/
def ofFunL : (C.P → V) →ₗ[k] C.Mod hC where
  toFun := C.ofFun hC
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ofFunL_apply (f : C.P → V) : C.ofFunL hC f = C.ofFun hC f := rfl

theorem ext_val {f f' : C.Mod hC} (h : ∀ j, C.val hC f j = C.val hC f' j) : f = f' := funext h

@[simp] theorem val_add (f f' : C.Mod hC) : C.val hC (f + f') = C.val hC f + C.val hC f' := rfl
@[simp] theorem val_zero : C.val hC 0 = 0 := rfl
@[simp] theorem val_smul (c : k) (f : C.Mod hC) : C.val hC (c • f) = c • C.val hC f := rfl
@[simp] theorem val_sub (f f' : C.Mod hC) : C.val hC (f - f') = C.val hC f - C.val hC f' := rfl
@[simp] theorem val_sum {ι : Type*} (s : Finset ι) (f : ι → C.Mod hC) :
    C.val hC (∑ i ∈ s, f i) = ∑ i ∈ s, C.val hC (f i) := rfl

theorem e_smul_val (v : D.Q.V) (f : C.Mod hC) (j : C.P) :
    C.val hC (D.e v • f) j = if C.vtx j = v then C.val hC f j else 0 := by
  rw [Rep.e_smul]; rfl

theorem α_smul_val (a : D.Q.A) (f : C.Mod hC) (j : C.P) :
    C.val hC (D.α a • f) j = ∑ i, if C.next a i = some j then C.g a i (C.val hC f i) else 0 := by
  rw [Rep.α_smul]; rfl

theorem α_smul_val_of {a : D.Q.A} {i j : C.P} (h : C.next a i = some j) (f : C.Mod hC) :
    C.val hC (D.α a • f) j = C.g a i (C.val hC f i) := by
  rw [α_smul_val, Finset.sum_eq_single i]
  · simp [h]
  · intro i' _ hi'
    rw [if_neg]
    intro h'; exact hi' (C.inj a i' i j h' h)
  · simp

theorem α_smul_val_of_none {a : D.Q.A} {j : C.P} (h : ∀ i, C.next a i ≠ some j) (f : C.Mod hC) :
    C.val hC (D.α a • f) j = 0 := by
  rw [α_smul_val]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [if_neg (h i)]

theorem α_smul_single {a : D.Q.A} {i j : C.P} (h : C.next a i = some j) (y : V) :
    D.α a • C.ofFun hC (Pi.single i y) = C.ofFun hC (Pi.single j (C.g a i y)) := by
  classical
  refine C.ext_val hC fun j' ↦ ?_
  rw [α_smul_val, Finset.sum_eq_single i]
  · by_cases hj : j' = j
    · subst hj; simp [h]
    · rw [if_neg (by rw [h]; exact fun e ↦ hj (Option.some.inj e).symm)]
      simp [hj]
  · intro i' _ hi'; simp [hi']
  · simp

/-- The subspace supported on a set of positions. -/
def blk (J : C.P → Prop) : Submodule k (C.Mod hC) where
  carrier := {f | ∀ j, ¬ J j → C.val hC f j = 0}
  add_mem' hf hf' j hj := by simp [hf j hj, hf' j hj]
  zero_mem' j _ := rfl
  smul_mem' c f hf j hj := by simp [hf j hj]

theorem mem_blk {J : C.P → Prop} {f : C.Mod hC} :
    f ∈ C.blk hC J ↔ ∀ j, ¬ J j → C.val hC f j = 0 := Iff.rfl

theorem blk_mono {J J' : C.P → Prop} (h : ∀ j, J j → J' j) : C.blk hC J ≤ C.blk hC J' :=
  fun _ hf j hj ↦ hf j fun h' ↦ hj (h j h')

theorem blk_inf (J J' : C.P → Prop) :
    C.blk hC J ⊓ C.blk hC J' = C.blk hC (fun j ↦ J j ∧ J' j) := by
  ext f
  simp only [Submodule.mem_inf, mem_blk, not_and_or]
  constructor
  · rintro ⟨h1, h2⟩ j (h | h)
    · exact h1 j h
    · exact h2 j h
  · intro h; exact ⟨fun j hj ↦ h j (Or.inl hj), fun j hj ↦ h j (Or.inr hj)⟩

theorem blk_bot : C.blk hC (fun _ ↦ False) = ⊥ := by
  ext f
  simp only [mem_blk, not_false_eq_true, forall_const, Submodule.mem_bot]
  constructor
  · intro h; exact C.ext_val hC h
  · rintro rfl j; rfl

theorem blk_iInf {ι : Type*} (J : ι → C.P → Prop) :
    (⨅ i, C.blk hC (J i)) = C.blk hC (fun j ↦ ∀ i, J i j) := by
  ext f
  simp only [Submodule.mem_iInf, mem_blk, not_forall]
  constructor
  · rintro h j ⟨i, hi⟩; exact h i j hi
  · intro h i j hj; exact h j ⟨i, hj⟩

theorem single_mem_blk {J : C.P → Prop} {j : C.P} (hj : J j) (y : V) :
    C.ofFun hC (Pi.single j y) ∈ C.blk hC J := by
  intro j' hj'
  have : j' ≠ j := fun h ↦ hj' (h ▸ hj)
  simp [this]

theorem mem_blk_iff_sum {J : C.P → Prop} [DecidablePred J] (f : C.Mod hC) (hf : f ∈ C.blk hC J) :
    f = ∑ j ∈ Finset.univ.filter J, C.ofFun hC (Pi.single j (C.val hC f j)) := by
  refine C.ext_val hC fun j ↦ ?_
  rw [val_sum, Finset.sum_apply]
  by_cases hj : J j
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'; rw [val_ofFun, Pi.single_eq_of_ne (Ne.symm hj')]
    · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩) h
  · rw [hf j hj]
    symm
    refine Finset.sum_eq_zero fun j' hj' ↦ ?_
    have : j ≠ j' := fun h ↦ hj (h ▸ (Finset.mem_filter.mp hj').2)
    rw [val_ofFun, Pi.single_eq_of_ne this]

theorem blk_iSup {ι : Type*} (J : ι → C.P → Prop) :
    (⨆ i, C.blk hC (J i)) = C.blk hC (fun j ↦ ∃ i, J i j) := by
  classical
  apply le_antisymm
  · exact iSup_le fun i ↦ C.blk_mono hC fun j hj ↦ ⟨i, hj⟩
  · intro f hf
    rw [C.mem_blk_iff_sum hC f hf]
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hj).2
    exact Submodule.mem_iSup_of_mem i (C.single_mem_blk hC hi _)

/-! ### Transports of block subspaces -/

theorem vsp_eq (v : D.Q.V) : D.vsp (C.Mod hC) v = C.blk hC (fun j ↦ C.vtx j = v) := by
  ext f
  rw [D.mem_vsp, mem_blk]
  constructor
  · intro h j hj
    rw [← h, e_smul_val, if_neg hj]
  · intro h
    refine C.ext_val hC fun j ↦ ?_
    rw [e_smul_val]
    split_ifs with hj
    · rfl
    · exact (h j hj).symm

theorem tr_true_blk (a : D.Q.A) (J : C.P → Prop) :
    D.tr (a, true) (C.blk hC J) =
      C.blk hC (fun i ↦ C.vtx i = D.Q.src a ∧ ∀ j, C.next a i = some j → J j) := by
  ext f
  rw [D.mem_tr_true, vsp_eq, mem_blk, mem_blk, mem_blk]
  constructor
  · rintro ⟨hv, hα⟩ i hi
    rw [not_and_or] at hi
    rcases hi with hi | hi
    · exact hv i hi
    · push Not at hi
      obtain ⟨j, hj, hJ⟩ := hi
      have := hα j hJ
      rw [α_smul_val_of C hC hj] at this
      exact (C.g a i).map_eq_zero_iff.mp this
  · intro h
    refine ⟨fun i hi ↦ h i fun h' ↦ hi h'.1, fun j hj ↦ ?_⟩
    rw [α_smul_val]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    split_ifs with hij
    · rw [h i fun h' ↦ hj (h'.2 j hij), map_zero]
    · rfl

theorem tr_false_blk (a : D.Q.A) (J : C.P → Prop) :
    D.tr (a, false) (C.blk hC J) = C.blk hC (fun j ↦ ∃ i, J i ∧ C.next a i = some j) := by
  classical
  ext x
  rw [D.mem_tr_false, mem_blk]
  constructor
  · rintro ⟨f, hfv, hfJ, rfl⟩ j hj
    by_cases hi : ∃ i, C.next a i = some j
    · obtain ⟨i, hi⟩ := hi
      rw [α_smul_val_of C hC hi, hfJ i fun h' ↦ hj ⟨i, h', hi⟩, map_zero]
    · push Not at hi
      exact α_smul_val_of_none C hC hi f
  · intro hx
    -- pull `x` back block by block
    let f : C.P → V := fun i ↦
      if h : J i ∧ ∃ j, C.next a i = some j then (C.g a i).symm (C.val hC x h.2.choose) else 0
    refine ⟨C.ofFun hC f, ?_, ?_, ?_⟩
    · rw [vsp_eq, mem_blk]
      intro i hi
      simp only [val_ofFun, f]
      rw [dif_neg]
      rintro ⟨-, j, hj⟩
      exact hi (C.next_src a i j hj)
    · rw [mem_blk]
      intro i hi
      simp only [val_ofFun, f]
      rw [dif_neg]
      exact fun h ↦ hi h.1
    · refine C.ext_val hC fun j ↦ ?_
      by_cases hj : ∃ i, C.next a i = some j
      · obtain ⟨i, hi⟩ := hj
        rw [α_smul_val_of C hC hi]
        simp only [val_ofFun, f]
        by_cases hJ : J i
        · have hex : J i ∧ ∃ j, C.next a i = some j := ⟨hJ, j, hi⟩
          rw [dif_pos hex]
          have : hex.2.choose = j := Option.some.inj (hex.2.choose_spec.symm.trans hi)
          rw [this, LinearEquiv.apply_symm_apply]
        · rw [dif_neg (fun h ↦ hJ h.1), map_zero]
          refine (hx j ?_).symm
          rintro ⟨i', hi', hi'j⟩
          exact hJ (C.inj a i' i j hi'j hi ▸ hi')
      · push Not at hj
        rw [α_smul_val_of_none C hC hj]
        refine (hx j ?_).symm
        rintro ⟨i, -, hi⟩; exact hj i hi

theorem ker_eq_blk (b : D.Q.A) :
    D.vsp (C.Mod hC) (D.Q.src b) ⊓ LinearMap.ker (actL (D.α b)) =
      C.blk hC (fun i ↦ C.vtx i = D.Q.src b ∧ C.next b i = none) := by
  have := C.tr_true_blk hC b (fun _ ↦ False)
  rw [blk_bot] at this
  rw [← tr_true_bot, this]
  congr 1
  funext i
  simp only [imp_false, eq_iff_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases h : C.next b i with
    | none => rfl
    | some j => exact absurd h (h2 j)
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj ↦ by rw [h2] at hj; cases hj⟩

theorem range_eq_blk (d : D.Q.A) :
    LinearMap.range (actL (M := C.Mod hC) (D.α d)) =
      C.blk hC (fun j ↦ ∃ i, C.next d i = some j) := by
  rw [← tr_false_vsp, vsp_eq, tr_false_blk]
  congr 1
  funext j
  simp only [eq_iff_iff]
  constructor
  · rintro ⟨i, -, hi⟩; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, C.next_src d i j hi, hi⟩

end BlockQuiver

end MonomialData

end BrickAccessibility
