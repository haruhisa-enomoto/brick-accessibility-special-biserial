module

public import BrickAccessibility.Section3.Actions
public import BrickAccessibility.Section4.Counts

/-!
# Maps between occurrences of a common substring (Step 2 of Proposition 3.8)

If an interval `π₁` of the string diagram has no outgoing boundary edges, an
interval `π₂` has no incoming boundary edges, and the two intervals are matched
compatibly with vertices and internal edges, then sending the basis vector at
`π₂ i` to the basis vector at `π₁ i` (and the others to zero) is an endomorphism
of `M(w)` [Crawley-Boevey, pp. 260--261]. It is nonzero and, when `π₂` misses a
position, not injective; so a brick admits no such pair (`false_of_matched`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData.CoeffQuiver

variable {D : MonomialData k B} (C : D.CoeffQuiver) {n : ℕ} (π₁ π₂ : Fin n → C.P)

/-- The map sending the basis vector at `π₂ i` to the one at `π₁ i`. -/
def matchMap : (C.P → k) →ₗ[k] (C.P → k) :=
  ∑ i, LinearMap.single k (fun _ ↦ k) (π₁ i) ∘ₗ LinearMap.proj (π₂ i)

variable {π₂}

theorem matchMap_single_of_eq (hπ : Function.Injective π₂) (i : Fin n) (c : k) :
    C.matchMap π₁ π₂ (Pi.single (π₂ i) c) = Pi.single (π₁ i) c := by
  simp only [matchMap, LinearMap.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_proj, Function.eval]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, if_neg (fun h ↦ hj (hπ h)), LinearMap.single_apply, Pi.single_zero]
  · simp

theorem matchMap_single_of_ne {s : C.P} (hs : ∀ i, π₂ i ≠ s) (c : k) :
    C.matchMap π₁ π₂ (Pi.single s c) = 0 := by
  simp only [matchMap, LinearMap.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_proj, Function.eval]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Pi.single_apply, if_neg (hs i), LinearMap.single_apply, Pi.single_zero]

variable (hC : C.KillsZeroPaths)

/-- The matched map is a module homomorphism. -/
def matchHom (hπ : Function.Injective π₂) (hv : ∀ i, C.vtx (π₁ i) = C.vtx (π₂ i))
    (h1 : ∀ a i t, C.next a (π₁ i) = some t →
      ∃ i', t = π₁ i' ∧ C.next a (π₂ i) = some (π₂ i') ∧ C.coef a (π₁ i) = C.coef a (π₂ i))
    (h2 : ∀ a i i', C.next a (π₂ i) = some (π₂ i') → C.next a (π₁ i) = some (π₁ i'))
    (h3 : ∀ a s i, C.next a s = some (π₂ i) → ∃ i', s = π₂ i') :
    C.Mod hC →ₗ[B] C.Mod hC := by
  classical
  refine D.linearMap_of_commute (M := C.Mod hC) (N := C.Mod hC) (C.matchMap π₁ π₂)
    (fun v m ↦ ?_) (fun a m ↦ ?_)
  · rw [Rep.e_smul, Rep.e_smul]
    change (C.matchMap π₁ π₂ ∘ₗ C.eMap v) m = (C.eMap v ∘ₗ C.matchMap π₁ π₂) m
    congr 1
    refine LinearMap.pi_ext fun s c ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, eMap_single]
    by_cases hs : ∃ i, π₂ i = s
    · obtain ⟨i, rfl⟩ := hs
      rw [C.matchMap_single_of_eq π₁ hπ, eMap_single, hv]
      split_ifs <;> simp [C.matchMap_single_of_eq π₁ hπ]
    · push_neg at hs
      rw [C.matchMap_single_of_ne π₁ hs, map_zero]
      split_ifs
      · exact C.matchMap_single_of_ne π₁ hs c
      · exact map_zero _
  · rw [Rep.α_smul, Rep.α_smul]
    change (C.matchMap π₁ π₂ ∘ₗ C.αMap a) m = (C.αMap a ∘ₗ C.matchMap π₁ π₂) m
    congr 1
    refine LinearMap.pi_ext fun s c ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, αMap_single]
    by_cases hs : ∃ i, π₂ i = s
    · obtain ⟨i, rfl⟩ := hs
      rw [C.matchMap_single_of_eq π₁ hπ, αMap_single]
      cases ht : C.next a (π₁ i) with
      | some t =>
          obtain ⟨i', rfl, h', hcoef⟩ := h1 a i t ht
          simp only [h', hcoef]
          exact C.matchMap_single_of_eq π₁ hπ i' _
      | none =>
          cases ht' : C.next a (π₂ i) with
          | none => simp
          | some t' =>
              simp only
              by_cases ht'' : ∃ i', π₂ i' = t'
              · obtain ⟨i', rfl⟩ := ht''
                rw [h2 a i i' ht'] at ht; cases ht
              · push_neg at ht''
                exact C.matchMap_single_of_ne π₁ ht'' _
    · push_neg at hs
      rw [C.matchMap_single_of_ne π₁ hs, map_zero]
      cases ht : C.next a s with
      | none => simp
      | some t =>
          simp only
          refine C.matchMap_single_of_ne π₁ (fun i hi ↦ ?_) _
          obtain ⟨i', rfl⟩ := h3 a s i (hi ▸ ht)
          exact hs i' rfl

/-- A brick admits no matched pair of intervals in which `π₂` misses a position. -/
theorem false_of_matched (hb : IsBrick B (C.Mod hC)) (hn : 0 < n) (hπ : Function.Injective π₂)
    (hv : ∀ i, C.vtx (π₁ i) = C.vtx (π₂ i))
    (h1 : ∀ a i t, C.next a (π₁ i) = some t →
      ∃ i', t = π₁ i' ∧ C.next a (π₂ i) = some (π₂ i') ∧ C.coef a (π₁ i) = C.coef a (π₂ i))
    (h2 : ∀ a i i', C.next a (π₂ i) = some (π₂ i') → C.next a (π₁ i) = some (π₁ i'))
    (h3 : ∀ a s i, C.next a s = some (π₂ i) → ∃ i', s = π₂ i')
    {t : C.P} (ht : ∀ i, π₂ i ≠ t) : False := by
  classical
  set f := C.matchHom π₁ hC hπ hv h1 h2 h3
  have key : ∀ m, C.val hC (f m) = C.matchMap π₁ π₂ (C.val hC m) := fun m ↦ rfl
  have hf : f ≠ 0 := by
    intro h
    have := key (C.ofFun hC (Pi.single (π₂ ⟨0, hn⟩) 1))
    rw [h, LinearMap.zero_apply, val_zero, val_ofFun, C.matchMap_single_of_eq π₁ hπ] at this
    have := congrFun this (π₁ ⟨0, hn⟩)
    simp at this
  obtain ⟨g, hg⟩ := (hb.2 f hf).exists_left_inv
  have := congrArg (fun φ ↦ C.val hC (φ (C.ofFun hC (Pi.single t 1))) t) hg
  simp only [Module.End.mul_apply, Module.End.one_apply] at this
  have h0 : f (C.ofFun hC (Pi.single t 1)) = 0 := by
    refine C.ext_val hC fun p ↦ ?_
    rw [key, val_ofFun, C.matchMap_single_of_ne π₁ ht 1]; rfl
  rw [h0, map_zero] at this
  rw [val_zero, val_ofFun, Pi.zero_apply, Pi.single_eq_same] at this
  exact zero_ne_one this

end MonomialData.CoeffQuiver

end BrickAccessibility
