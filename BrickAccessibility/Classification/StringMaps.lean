module

public import BrickAccessibility.Classification.StringBQ
public import BrickAccessibility.Classification.BlockMaps
public import BrickAccessibility.Classification.Chains

/-!
# Maps from string modules

For a string `w` and a module `M`, the chain space of `w` in `M` consists of
families `(c_q)` related along the letters of `w` and satisfying the end
conditions. Every entry `c_q` lies in the numerator `num_q` of the pair functor
at position `q` (`mem_num_of_chain`), and every vector of `num_p` starts a chain
(`exists_chain`). A linear map `φ : V → num_p` therefore lifts to a compatible
family on the block quiver `M(w) ⊗ V`, hence to a module map `M(w) ⊗ V → M`
(`stringHom`) with `z_p ⊗ y ↦ φ y`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

/-- `omega` after unfolding word lengths. -/
local macro "womega" : tactic => `(tactic| ((try simp only [Word.len] at *) <;> omega))

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hs : w.IsString D) (S : D.Signs)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

omit hs in
theorem wend_right (q : Fin (w.len + 1)) :
    D.Q.wend (w.vtx q) (w.right q) = w.vtx (Fin.last _) := by
  simp only [vtx, right, Fin.val_last]
  rw [← Statement.FinQuiver.wend_append, List.take_append_drop, List.take_of_length_le le_rfl]

omit hs in
theorem wend_left (q : Fin (w.len + 1)) : D.Q.wend (w.vtx q) (w.left q) = w.vtx 0 := by
  have hw := w.walk
  rw [← List.take_append_drop q.val w.letters, Statement.FinQuiver.isWalk_append] at hw
  have := (Statement.FinQuiver.isWalk_inv _ _ hw.1).2
  simp only [vtx, left, Fin.val_zero, List.take_zero]
  exact this

/-- The numerator of the pair functor at a position of `w`. -/
def num (q : Fin (w.len + 1)) : Submodule k M :=
  S.pnum M (w.vtx q) (w.sideSign S q) (.fin (w.right q)) (.fin (w.left q))

/-- The denominator of the pair functor at a position of `w`. -/
def den (q : Fin (w.len + 1)) : Submodule k M :=
  S.pden M (w.vtx q) (w.sideSign S q) (.fin (w.right q)) (.fin (w.left q))

/-- The chain space of `w` in `M`. -/
def chainSp : Submodule k (Fin (w.len + 1) → M) where
  carrier := {c | (∀ (q : ℕ) (hq : q < w.len),
      MonomialData.Rel w.letters[q] (c ⟨q, by womega⟩) (c ⟨q + 1, by womega⟩)) ∧
    c (Fin.last _) ∈ S.Kc M (w.vtx (Fin.last _)) (w.sideSign S (Fin.last _)) ∧
    c 0 ∈ S.Kc M (w.vtx 0) (!w.sideSign S 0)}
  add_mem' {c c'} hc hc' := ⟨fun q hq ↦ MonomialData.rel_add (hc.1 q hq) (hc'.1 q hq),
    Submodule.add_mem _ hc.2.1 hc'.2.1, Submodule.add_mem _ hc.2.2 hc'.2.2⟩
  zero_mem' := ⟨fun q hq ↦ MonomialData.rel_zero _, Submodule.zero_mem _, Submodule.zero_mem _⟩
  smul_mem' a c hc := ⟨fun q hq ↦ MonomialData.rel_smul a (hc.1 q hq),
    Submodule.smul_mem _ a hc.2.1, Submodule.smul_mem _ a hc.2.2⟩

omit hs in
theorem length_right (q : Fin (w.len + 1)) : (w.right q).length = w.len - q.val := by
  simp [right]

omit hs in
theorem length_left (q : Fin (w.len + 1)) : (w.left q).length = q.val := by
  simp only [left, invLetters, List.length_reverse, List.length_map, List.length_take]
  have := q.isLt; womega

include hs in
theorem mem_plus_right_iff (q : Fin (w.len + 1)) (x : M) :
    x ∈ S.plus M (w.vtx q) (w.sideSign S q) (.fin (w.right q)) ↔
      x ∈ D.trs (w.right q) (S.Kc M (w.vtx (Fin.last _)) (w.sideSign S (Fin.last _))) := by
  simp only [MonomialData.Signs.plus, MonomialData.Signs.plusF]
  rw [w.wend_right, w.nsign_right hs]

include hs in
theorem mem_plus_left_iff (q : Fin (w.len + 1)) (x : M) :
    x ∈ S.plus M (w.vtx q) (!w.sideSign S q) (.fin (w.left q)) ↔
      x ∈ D.trs (w.left q) (S.Kc M (w.vtx 0) (!w.sideSign S 0)) := by
  simp only [MonomialData.Signs.plus, MonomialData.Signs.plusF]
  rw [w.wend_left, w.nsign_left hs]

include hs in
/-- Chain entries lie in the numerators. -/
theorem mem_num_of_chain {c : Fin (w.len + 1) → M} (hc : c ∈ w.chainSp S M)
    (q : Fin (w.len + 1)) : c q ∈ w.num S M q := by
  refine ⟨(w.mem_plus_right_iff hs S M q _).mpr ?_, (w.mem_plus_left_iff hs S M q _).mpr ?_⟩
  · refine (MonomialData.mem_trs_iff _ _ _).mpr
      ⟨fun i ↦ if h : q.val + i ≤ w.len then c ⟨q.val + i, by womega⟩ else 0, ?_, ?_, ?_⟩
    · beta_reduce; rw [dif_pos (by have := q.isLt; womega)]; rfl
    · intro i hi
      have hi' : i < w.len - q.val := w.length_right q ▸ hi
      rw [w.right_getElem q i hi]
      beta_reduce
      rw [dif_pos (by womega), dif_pos (by womega)]
      have := hc.1 (q.val + i) (by womega)
      simpa [Nat.add_assoc] using this
    · rw [w.length_right]; beta_reduce; rw [dif_pos (by womega)]
      have e : (⟨q.val + (w.len - q.val), by womega⟩ : Fin (w.len + 1)) = Fin.last _ := by
        ext; simp; womega
      rw [e]; exact hc.2.1
  · refine (MonomialData.mem_trs_iff _ _ _).mpr
      ⟨fun i ↦ if h : i ≤ q.val then c ⟨q.val - i, by womega⟩ else 0, ?_, ?_, ?_⟩
    · beta_reduce; rw [dif_pos (Nat.zero_le _)]; rfl
    · intro i hi
      have hq := q.isLt
      have hlen : w.len = w.letters.length := rfl
      have hi' : i < q.val := w.length_left q ▸ hi
      rw [w.left_getElem q i hi, MonomialData.rel_inv]
      beta_reduce
      rw [dif_pos (by omega), dif_pos (by omega)]
      have := hc.1 (q.val - 1 - i) (by omega)
      have e1 : (⟨q.val - 1 - i, by omega⟩ : Fin (w.len + 1)) = ⟨q.val - (i + 1), by omega⟩ := by
        ext; simp only; omega
      have e2 : (⟨q.val - 1 - i + 1, by omega⟩ : Fin (w.len + 1)) = ⟨q.val - i, by omega⟩ := by
        ext; simp only; omega
      rw [e1, e2] at this
      exact this
    · rw [w.length_left]; beta_reduce; rw [dif_pos le_rfl]
      have e : (⟨q.val - q.val, by womega⟩ : Fin (w.len + 1)) = 0 := by ext; simp
      rw [e]; exact hc.2.2

include hs in
/-- Every vector of a numerator starts a chain. -/
theorem exists_chain {p : Fin (w.len + 1)} {x : M} (hx : x ∈ w.num S M p) :
    ∃ c ∈ w.chainSp S M, c p = x := by
  classical
  have hlen : w.len = w.letters.length := rfl
  have hp := p.isLt
  obtain ⟨cR, hR0, hR, hRe⟩ :=
    (MonomialData.mem_trs_iff _ _ _).mp ((w.mem_plus_right_iff hs S M p x).mp hx.1)
  obtain ⟨cL, hL0, hL, hLe⟩ :=
    (MonomialData.mem_trs_iff _ _ _).mp ((w.mem_plus_left_iff hs S M p x).mp hx.2)
  rw [w.length_right] at hRe
  rw [w.length_left] at hLe
  let c : Fin (w.len + 1) → M := fun q ↦ if p.val ≤ q.val then cR (q.val - p.val)
    else cL (p.val - q.val)
  refine ⟨c, ⟨fun q hq ↦ ?_, ?_, ?_⟩, ?_⟩
  · by_cases hpq : p.val ≤ q
    · have h1 := hR (q - p.val) (by rw [w.length_right]; omega)
      rw [w.right_getElem] at h1
      simp only [c, if_pos hpq, if_pos (show p.val ≤ q + 1 by omega)]
      have e1 : p.val + (q - p.val) = q := by omega
      have e2 : q + 1 - p.val = q - p.val + 1 := by omega
      simp only [e1] at h1
      rw [e2]; exact h1
    · have h1 := hL (p.val - q - 1) (by rw [w.length_left]; omega)
      rw [w.left_getElem, MonomialData.rel_inv] at h1
      have e1 : p.val - 1 - (p.val - q - 1) = q := by omega
      simp only [e1] at h1
      simp only [c, if_neg hpq]
      by_cases hq1 : p.val ≤ q + 1
      · have hpq1 : p.val = q + 1 := by omega
        rw [if_pos hq1]
        have e2 : p.val - q - 1 + 1 = p.val - q := by omega
        rw [e2] at h1
        have e3 : q + 1 - p.val = 0 := by omega
        have hxL : cL (p.val - q - 1) = x := by rw [show p.val - q - 1 = 0 by omega, hL0]
        rw [e3, hR0]
        rw [hxL] at h1
        exact h1
      · rw [if_neg hq1]
        have e2 : p.val - q - 1 + 1 = p.val - q := by omega
        have e3 : p.val - (q + 1) = p.val - q - 1 := by omega
        rw [e2] at h1
        rw [e3]
        exact h1
  · simp only [c, Fin.val_last, if_pos (show p.val ≤ w.len by omega)]
    exact hRe
  · simp only [c]
    split_ifs with h0
    · have hp0 : p.val = 0 := by simpa using h0
      have e : (0 : Fin (w.len + 1)).val - p.val = 0 := by simp
      rw [e, hR0]
      have hx2 := hx.2
      have hp0' : p = 0 := Fin.ext hp0
      subst hp0'
      rw [w.left_zero] at hx2
      simp only [MonomialData.Signs.plus, MonomialData.Signs.plusF, MonomialData.trs_nil,
        MonomialData.Signs.nsign_nil] at hx2
      exact hx2
    · have e : p.val - (0 : Fin (w.len + 1)).val = p.val := by simp
      rw [e]
      exact hLe
  · simp only [c, le_refl, if_true, Nat.sub_self, hR0]

/-- Evaluation of chains at a position. -/
def evalAt (q : Fin (w.len + 1)) : w.chainSp S M →ₗ[k] M :=
  (LinearMap.proj q).comp (w.chainSp S M).subtype

include hs in
theorem range_evalAt (q : Fin (w.len + 1)) : LinearMap.range (w.evalAt S M q) = w.num S M q := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩; exact w.mem_num_of_chain hs S M c.2 q
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := w.exists_chain hs S M hx
    exact ⟨⟨c, hc⟩, rfl⟩

variable {M} {V : Type u} [AddCommGroup V] [Module k V]

include hs in
theorem exists_lift (p : Fin (w.len + 1)) (φ : V →ₗ[k] M) (hφ : ∀ y, φ y ∈ w.num S M p) :
    ∃ σ : V →ₗ[k] w.chainSp S M, ∀ y, (σ y).1 p = φ y := by
  have hg : ∀ y, φ y ∈ LinearMap.range (w.evalAt S M p) := fun y ↦ by
    rw [w.range_evalAt hs S M p]; exact hφ y
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (w.evalAt S M p).rangeRestrict
    (φ.codRestrict _ hg) (LinearMap.surjective_rangeRestrict _)
  refine ⟨σ, fun y ↦ ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hσ y)

include hs in
/-- The compatible family on `M(w) ⊗ V` lifting `φ`. -/
def compat (σ : V →ₗ[k] w.chainSp S M) :
    (w.blockQuiver V hs.1).Compat M where
  ψ q := (w.evalAt S M q).comp σ
  mem_vsp q y := by
    have h := w.mem_num_of_chain hs S M (σ y).2 q
    exact S.plusF_le_vsp (w.isHW_right hs S q).1 h.1
  move a i j y h := by
    show D.α a • (σ y).1 i = (σ ((w.blockQuiver V hs.1).g a i y)).1 j
    have hg : (w.blockQuiver V hs.1).g a i y = y := rfl
    rw [hg]
    change w.next a i = some j at h
    have hc := (σ y).2.1
    rcases (w.next_eq_some_iff hs.1 a i j).mp h with ⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩
    · have hr := hc i.val hi
      rw [hl] at hr
      simp only [MonomialData.Rel, if_true] at hr
      have e : j = ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := Fin.ext hj
      rw [e]; exact hr.2.symm
    · have hr := hc (i.val - 1) (by have := i.isLt; simp only [Word.len] at *; omega)
      rw [hl] at hr
      simp only [MonomialData.Rel, Bool.false_eq_true, if_false] at hr
      have e : j = ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ := Fin.ext hj
      have e' : (⟨i.val - 1 + 1, by have := i.isLt; simp only [Word.len] at *; omega⟩ :
          Fin (w.len + 1)) = i := Fin.ext (by simp; omega)
      rw [e'] at hr
      rw [e]; exact hr.2.symm
  kill a i y h := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change w.next a i = none at h
    have hx := w.mem_num_of_chain hs S M (σ y).2 i
    by_cases hsrc : D.Q.src a = w.vtx i
    · by_cases hσ : S.σ a = w.sideSign S i
      · refine S.α_smul_eq_zero_of_mem_plus (w.isHW_right hs S i) hsrc hσ ?_ hx.1
        intro hh
        have hi : i.val < w.len := by
          by_contra hn
          have : w.right i = [] := by simp [right]; simp only [Word.len] at hn; omega
          rw [this] at hh; cases hh
        rw [show w.right i = w.letters[i.val] :: w.right ⟨i.val + 1, by omega⟩ from
          w.right_cons i hi] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        have : w.next a i = some ⟨i.val + 1, by omega⟩ :=
          (w.next_eq_some_iff hs.1 a i _).mpr (Or.inl ⟨hi, hh, rfl⟩)
        rw [h] at this; cases this
      · have hσ' : S.σ a = !w.sideSign S i := Bool.eq_not_iff.mpr hσ
        refine S.α_smul_eq_zero_of_mem_plus (w.isHW_left hs S i) hsrc hσ' ?_ hx.2
        intro hh
        have hi : 0 < i.val := by
          by_contra hn
          have hi0 : i.val = 0 := by omega
          have : w.left i = [] := by simp [left, invLetters, hi0]
          rw [this] at hh; cases hh
        rw [w.left_cons i hi] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        have hl : w.letters[i.val - 1]'(by have := i.isLt; simp only [Word.len] at *; omega) =
            (a, false) := by
          rw [← Letter.inv_inv' (w.letters[i.val - 1]'_), hh]; rfl
        have : w.next a i = some ⟨i.val - 1, by have := i.isLt; omega⟩ :=
          (w.next_eq_some_iff hs.1 a i _).mpr (Or.inr ⟨hi, hl, rfl⟩)
        rw [h] at this; cases this
    · exact D.α_smul_of_mem_vsp (Ne.symm hsrc)
        (S.plusF_le_vsp (w.isHW_right hs S i).1 hx.1)

include hs in
/-- **Maps from string modules.** -/
theorem exists_stringHom (p : Fin (w.len + 1)) (φ : V →ₗ[k] M) (hφ : ∀ y, φ y ∈ w.num S M p) :
    ∃ Θ : (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs) →ₗ[B] M,
      (∀ y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single p y)) = φ y) ∧
      (∀ q y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) ∈ w.num S M q) := by
  obtain ⟨σ, hσ⟩ := w.exists_lift hs S p φ hφ
  refine ⟨(w.compat hs S σ).toHom _, fun y ↦ ?_, fun q y ↦ ?_⟩
  · exact ((w.compat hs S σ).toHom_single (w.blockQuiver_kills V hs) p y).trans (hσ y)
  · have e := (w.compat hs S σ).toHom_single (w.blockQuiver_kills V hs) q y
    exact (congrArg (fun x ↦ x ∈ w.num S M q) e).mpr (w.mem_num_of_chain hs S M (σ y).2 q)

end Word

end BrickAccessibility
