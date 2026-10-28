module

public import BrickAccessibility.Classification.HalfWords

/-!
# Chains along words

`Rel l x y` says that `y` follows `x` along the letter `l`: `y = a x` for a
direct letter `a`, and `x = a y` for an inverse letter `a⁻¹` (with `x`, resp.
`y`, in the source vertex space of `a`). A vector lies in `L^* U` exactly when
it starts a chain along `L` ending in `U` (`mem_trs_iff`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B}
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- `y` follows `x` along the letter `l`. -/
def Rel (l : Letter D.Q) (x y : M) : Prop :=
  if l.2 then x ∈ D.vsp M (D.Q.src l.1) ∧ y = D.α l.1 • x
  else y ∈ D.vsp M (D.Q.src l.1) ∧ x = D.α l.1 • y

theorem rel_inv (l : Letter D.Q) (x y : M) : Rel l.inv x y ↔ Rel l y x := by
  obtain ⟨a, d⟩ := l
  cases d <;> simp [Rel, Letter.inv]

theorem rel_add {l : Letter D.Q} {x y x' y' : M} (h : Rel l x y) (h' : Rel l x' y') :
    Rel l (x + x') (y + y') := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [Rel, Bool.false_eq_true, if_false] at h h' ⊢
    exact ⟨Submodule.add_mem _ h.1 h'.1, by rw [h.2, h'.2, smul_add]⟩
  · simp only [Rel, if_true] at h h' ⊢
    exact ⟨Submodule.add_mem _ h.1 h'.1, by rw [h.2, h'.2, smul_add]⟩

theorem rel_smul {l : Letter D.Q} {x y : M} (c : k) (h : Rel l x y) : Rel l (c • x) (c • y) := by
  obtain ⟨a, d⟩ := l
  cases d
  · simp only [Rel, Bool.false_eq_true, if_false] at h ⊢
    exact ⟨Submodule.smul_mem _ c h.1, by rw [h.2, smul_comm]⟩
  · simp only [Rel, if_true] at h ⊢
    exact ⟨Submodule.smul_mem _ c h.1, by rw [h.2, smul_comm]⟩

theorem rel_zero (l : Letter D.Q) : Rel l (0 : M) 0 := by
  obtain ⟨a, d⟩ := l
  cases d <;> simp [Rel, Submodule.zero_mem]

theorem mem_tr_iff (l : Letter D.Q) (U : Submodule k M) (x : M) :
    x ∈ D.tr l U ↔ ∃ y, Rel l x y ∧ y ∈ U := by
  obtain ⟨a, d⟩ := l
  cases d
  · rw [D.mem_tr_false]
    simp only [Rel, Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨y, hv, hU, rfl⟩; exact ⟨y, ⟨hv, rfl⟩, hU⟩
    · rintro ⟨y, ⟨hv, rfl⟩, hU⟩; exact ⟨y, hv, hU, rfl⟩
  · rw [D.mem_tr_true]
    simp only [Rel, if_true]
    constructor
    · rintro ⟨hv, hU⟩; exact ⟨_, ⟨hv, rfl⟩, hU⟩
    · rintro ⟨y, ⟨hv, rfl⟩, hU⟩; exact ⟨hv, hU⟩

/-- A vector lies in `L^* U` iff it starts a chain along `L` ending in `U`. -/
theorem mem_trs_iff (L : List (Letter D.Q)) (U : Submodule k M) (x : M) :
    x ∈ D.trs L U ↔ ∃ c : ℕ → M, c 0 = x ∧
      (∀ (i : ℕ) (hi : i < L.length), Rel L[i] (c i) (c (i + 1))) ∧ c L.length ∈ U := by
  induction L generalizing x with
  | nil =>
      simp only [trs_nil, List.length_nil, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
        true_and]
      exact ⟨fun h ↦ ⟨fun _ ↦ x, rfl, h⟩, fun ⟨c, hc, h⟩ ↦ hc ▸ h⟩
  | cons l L ih =>
      rw [trs_cons, mem_tr_iff]
      constructor
      · rintro ⟨y, hxy, hy⟩
        obtain ⟨c, hc0, hc, hcL⟩ := (ih y).mp hy
        refine ⟨fun i ↦ Nat.casesOn i x c, rfl, fun i hi ↦ ?_, ?_⟩
        · cases i with
          | zero => simpa [hc0] using hxy
          | succ i => simpa using hc i (by simpa using hi)
        · simpa using hcL
      · rintro ⟨c, hc0, hc, hcL⟩
        have h0 : Rel l (c 0) (c 1) := hc 0 (by simp)
        rw [hc0] at h0
        refine ⟨c 1, h0, (ih (c 1)).mpr ⟨fun i ↦ c (i + 1), rfl,
          fun i hi ↦ hc (i + 1) (by simpa using hi), by simpa using hcL⟩⟩

omit [Module k M] [IsScalarTower k B M] in
/-- `α_a α_c = 0` when `c a` is a composable zero path. -/
theorem α_smul_α_smul_eq_zero {a c : D.Q.A} (hca : D.Q.tgt c = D.Q.src a)
    (hz : ¬ D.toPathData.Allowed c a) (m : M) : D.α a • D.α c • m = 0 := by
  have h0 : D.pval (D.Q.src c) [c, a] = 0 := by
    by_contra h; exact hz ⟨hca.symm, h⟩
  have h1 := D.toPathData.pval_append (D.Q.src c) [c] [a]
  have e1 : D.Q.pend (D.Q.src c) [c] = D.Q.src a := by simp [Statement.FinQuiver.pend, hca]
  rw [e1, D.toPathData.pval_single_src, D.toPathData.pval_single_src] at h1
  rw [← mul_smul]
  change (D.α a * D.α c) • m = 0
  rw [← h1]
  change D.pval (D.Q.src c) [c, a] • m = 0
  rw [h0, zero_smul]

variable (S : Signs D)

/-- Arrows of the sign of a finite half-word kill its `h⁺`, unless the half-word
starts with that arrow. -/
theorem Signs.α_smul_eq_zero_of_mem_plus {v : D.Q.V} {s : Bool} {L : List (Letter D.Q)}
    (hL : S.IsHW v s L) {a : D.Q.A} (ha : D.Q.src a = v) (hσ : S.σ a = s)
    (hhead : L.head? ≠ some (a, true)) {x : M} (hx : x ∈ S.plusF M v s L) :
    D.α a • x = 0 := by
  cases L with
  | nil =>
      have := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx.2 a) ⟨ha, hσ⟩
      exact this
  | cons l L =>
      obtain ⟨b, d⟩ := l
      have hs := hL.2 0 (by simp)
      simp only [List.getElem_cons_zero, List.take_zero, Signs.nsign_nil] at hs
      have hsrc := hL.1.1
      cases d
      · -- an inverse first letter: `x` lies in the image of `b`
        simp only [Letter.src, Bool.false_eq_true, if_false] at hsrc
        simp only [Signs.st_false] at hs
        simp only [Signs.plusF, trs_cons] at hx
        obtain ⟨y, -, -, rfl⟩ := (D.mem_tr_false).mp hx
        exact α_smul_α_smul_eq_zero (hsrc.trans ha.symm)
          (fun h ↦ S.hall b a h (hσ.trans hs.symm)) y
      · -- a direct first letter with the same sign is `a` itself
        exfalso
        simp only [Letter.src, if_true] at hsrc
        simp only [Signs.st_true] at hs
        have : b = a := by
          by_contra hne
          exact S.hσ b a hne (hsrc.trans ha.symm) (hs.trans hσ.symm)
        subst this
        exact hhead rfl

end MonomialData

end BrickAccessibility
