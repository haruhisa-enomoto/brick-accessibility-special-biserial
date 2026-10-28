module

public import BrickAccessibility.Classification.BlockTransport

/-!
# Boundary subspaces on block quiver modules as position sets

The transports along letters act on position sets (`ptr`, `ptrs`), and for every
half-word `h` the subspaces `h⁺`, `h⁻` of a block quiver module are supported on
explicit position sets (`plus_eq_blk`, `minus_eq_blk`). The pair functors are
then supported on explicit sets and have dimension `|num \ den| · dim V`.
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

/-- Transport of a position set along a letter. -/
def ptr : Letter D.Q → (C.P → Prop) → C.P → Prop
  | (a, true), J => fun i ↦ C.vtx i = D.Q.src a ∧ ∀ j, C.next a i = some j → J j
  | (a, false), J => fun j ↦ ∃ i, J i ∧ C.next a i = some j

/-- Transport of a position set along a list of letters. -/
def ptrs : List (Letter D.Q) → (C.P → Prop) → C.P → Prop
  | [], J => J
  | l :: L, J => C.ptr l (ptrs L J)

theorem tr_blk (l : Letter D.Q) (J : C.P → Prop) :
    D.tr l (C.blk hC J) = C.blk hC (C.ptr l J) := by
  obtain ⟨a, d⟩ := l
  cases d
  · exact C.tr_false_blk hC a J
  · exact C.tr_true_blk hC a J

theorem trs_blk (L : List (Letter D.Q)) (J : C.P → Prop) :
    D.trs L (C.blk hC J) = C.blk hC (C.ptrs L J) := by
  induction L with
  | nil => rfl
  | cons l L ih => simp only [trs_cons, ih, C.tr_blk hC]; rfl

theorem blk_sup (J J' : C.P → Prop) :
    C.blk hC J ⊔ C.blk hC J' = C.blk hC (fun j ↦ J j ∨ J' j) := by
  have := C.blk_iSup hC (fun b : Bool ↦ if b then J else J')
  rw [iSup_bool_eq] at this
  simp only [if_true, Bool.false_eq_true, if_false] at this
  rw [this]
  congr 1
  funext j
  simp only [eq_iff_iff]
  constructor
  · rintro ⟨b, hb⟩; cases b <;> simp_all
  · rintro (h | h)
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩

theorem ker_eq_blk' (b : D.Q.A) :
    LinearMap.ker (actL (M := C.Mod hC) (D.α b)) = C.blk hC (fun i ↦ C.next b i = none) := by
  ext f
  rw [LinearMap.mem_ker, mem_blk]
  constructor
  · intro h i hi
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hi
    have := congrFun (congrArg (C.val hC) h) j
    rw [actL_apply, α_smul_val_of C hC hj] at this
    exact (C.g b i).map_eq_zero_iff.mp this
  · intro h
    refine C.ext_val hC fun j ↦ ?_
    rw [actL_apply, α_smul_val]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    split_ifs with hij
    · rw [h i (by rw [hij]; simp), map_zero]
    · rfl

variable (S : Signs D)

/-- The kernel position set. -/
def Kset (u : D.Q.V) (n : Bool) : C.P → Prop :=
  fun i ↦ C.vtx i = u ∧ ∀ b, (D.Q.src b = u ∧ S.σ b = n) → C.next b i = none

/-- The image position set. -/
def Iset (u : D.Q.V) (n : Bool) : C.P → Prop :=
  fun j ↦ ∃ d i, (D.Q.tgt d = u ∧ S.ε d = n) ∧ C.next d i = some j

theorem Kc_eq_blk (u : D.Q.V) (n : Bool) : S.Kc (C.Mod hC) u n = C.blk hC (C.Kset S u n) := by
  apply le_antisymm
  · rintro f ⟨hv, hK⟩ j hj
    simp only [Kset, not_and_or, not_forall] at hj
    rcases hj with hj | ⟨b, hb, hne⟩
    · rw [vsp_eq] at hv; exact hv j hj
    · have h1 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hK b) hb
      have e := C.ker_eq_blk' hC b
      rw [e] at h1
      exact h1 j hne
  · intro f hf
    refine ⟨?_, ?_⟩
    · rw [vsp_eq]; exact C.blk_mono hC (fun j hj ↦ hj.1) hf
    · refine (Submodule.mem_iInf _).mpr fun b ↦ (Submodule.mem_iInf _).mpr fun hb ↦ ?_
      have e := C.ker_eq_blk' hC b
      rw [e]
      exact C.blk_mono hC (fun j hj ↦ hj.2 b hb) hf

theorem Ic_eq_blk (u : D.Q.V) (n : Bool) : S.Ic (C.Mod hC) u n = C.blk hC (C.Iset S u n) := by
  apply le_antisymm
  · refine iSup₂_le fun d hd ↦ ?_
    have e := C.range_eq_blk hC d
    rw [e]
    exact C.blk_mono hC fun j ⟨i, hi⟩ ↦ ⟨d, i, hd, hi⟩
  · intro f hf
    classical
    rw [C.mem_blk_iff_sum hC f hf]
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    obtain ⟨d, i, hd, hi⟩ := (Finset.mem_filter.mp hj).2
    refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd ?_)
    have e := C.range_eq_blk hC d
    rw [e]
    exact C.single_mem_blk hC ⟨i, hi⟩ _

/-- The position set of `h⁺`. -/
def plusSet (v : D.Q.V) (s : Bool) : HWord D.Q → C.P → Prop
  | .fin L => C.ptrs L (C.Kset S (D.Q.wend v L) (S.nsign s L))
  | .inf f => fun j ↦ ∀ n, C.ptrs (List.ofFn fun i : Fin n ↦ f i)
      (fun i ↦ C.vtx i = D.Q.wend v (List.ofFn fun i : Fin n ↦ f i)) j

/-- The position set of `h⁻`. -/
def minusSet (v : D.Q.V) (s : Bool) : HWord D.Q → C.P → Prop
  | .fin L => C.ptrs L (C.Iset S (D.Q.wend v L) (S.nsign s L))
  | .inf f => fun j ↦ ∃ n, C.ptrs (List.ofFn fun i : Fin n ↦ f i) (fun _ ↦ False) j

theorem plus_eq_blk (v : D.Q.V) (s : Bool) (h : HWord D.Q) :
    S.plus (C.Mod hC) v s h = C.blk hC (C.plusSet S v s h) := by
  cases h with
  | fin L => simp only [Signs.plus, Signs.plusF, C.Kc_eq_blk hC, C.trs_blk hC]; rfl
  | inf f =>
      simp only [Signs.plus]
      simp_rw [vsp_eq, C.trs_blk hC, C.blk_iInf hC]
      rfl

theorem minus_eq_blk (v : D.Q.V) (s : Bool) (h : HWord D.Q) :
    S.minus (C.Mod hC) v s h = C.blk hC (C.minusSet S v s h) := by
  cases h with
  | fin L => simp only [Signs.minus, Signs.minusF, C.Ic_eq_blk hC, C.trs_blk hC]; rfl
  | inf f =>
      simp only [Signs.minus]
      simp_rw [← C.blk_bot hC, C.trs_blk hC, C.blk_iSup hC]
      rfl

/-- Dimension of a block subspace. -/
theorem finrank_blk [FiniteDimensional k V] (J : C.P → Prop) [DecidablePred J] :
    finrank k (C.blk hC J) = (Finset.univ.filter J).card * finrank k V := by
  classical
  let e : C.blk hC J ≃ₗ[k] ({j // J j} → V) :=
    { toFun := fun f j ↦ C.val hC f.1 j.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun g ↦ ⟨C.ofFun hC fun j ↦ if h : J j then g ⟨j, h⟩ else 0, fun j hj ↦ by
        simp [hj]⟩
      left_inv := fun f ↦ by
        ext1
        refine C.ext_val hC fun j ↦ ?_
        by_cases hj : J j
        · simp [hj]
        · simp [hj, f.2 j hj]
      right_inv := fun g ↦ by funext j; simp [j.2] }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_subtype]

end BlockQuiver

end MonomialData

end BrickAccessibility
