module

public import BrickAccessibility.Section3.OverlapSeg

/-!
# Paths with all consecutive pairs occurring (Step 2 of Proposition 3.8)

For a brick string module over a special biserial algebra, a path occurs on the
string diagram as soon as each of its arrows and each pair of consecutive arrows
does (`seg_of_chain`), by induction with `seg_of_overlap`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hw : w.IsString D)
include hw

theorem seg_of_occurs {x : D.Q.V} {l : List D.Q.A} (h : w.Occurs x l) :
    ∃ d r, w.Seg d r l := by
  obtain ⟨r, -, s, c, hf⟩ := h
  obtain ⟨-, d, hs, -⟩ := w.exists_seg_of_follow hw.1 hf
  exact ⟨d, r.val, hs⟩

theorem vtx_pos_zero {d : Bool} {r : ℕ} {a : D.Q.A} {l : List D.Q.A} (h : w.Seg d r (a :: l)) :
    w.vtx (h.pos 0 (Nat.zero_le _)) = D.Q.src a :=
  (w.coeffQuiver D).next_src _ _ _ (h.next hw.1 (j := 0) (by simp))

theorem occurs_of_seg {d : Bool} {r : ℕ} {a : D.Q.A} {l : List D.Q.A} (h : w.Seg d r (a :: l)) :
    w.Occurs (D.Q.src a) (a :: l) :=
  ⟨h.pos 0 (Nat.zero_le _), w.vtx_pos_zero hw h, h.pos _ le_rfl, 1, h.follow hw.1⟩

/-- A path occurs once its arrows and consecutive pairs occur. -/
theorem seg_of_chain (hSB : D.toPathData.IsSpecialBiserial)
    (hb : IsBrick B (w.stringModule D hw)) :
    ∀ (L : List D.Q.A), L ≠ [] → (∀ x ∈ L, ∃ d r, w.Seg d r [x]) →
      L.IsChain (fun x y ↦ ∃ d r, w.Seg d r [x, y]) → ∃ d r, w.Seg d r L := by
  intro L
  induction hn : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  intro hL h1 h2
  have hpos : 0 < n := by rw [← hn]; exact List.length_pos_iff.mpr hL
  match L, hL with
  | [x], _ => exact h1 x (by simp)
  | [x, y], _ => simpa using h2
  | x :: y :: z :: rest, _ =>
      set T := y :: z :: rest with hT
      have hTne : T ≠ [] := by simp [T]
      set u := T.dropLast
      set b := T.getLast hTne
      have hTub : T = u ++ [b] := (List.dropLast_append_getLast hTne).symm
      have hu : u ≠ [] := by simp [u, T]
      have hLeq : x :: y :: z :: rest = (x :: u) ++ [b] := by
        rw [List.cons_append, ← hTub]
      have hlenT : T.length = n - 1 := by simp [T] at hn ⊢; omega
      have hlenu : (x :: u).length = n - 1 := by
        have := congrArg List.length hTub
        simp only [List.length_append, List.length_singleton] at this
        simp only [List.length_cons]; omega
      obtain ⟨d₁, r₁, h₁⟩ := ih (n - 1) (by omega) (x :: u) hlenu (by simp)
        (fun t ht ↦ h1 t (by rw [hLeq]; exact List.mem_append_left _ ht))
        (by rw [hLeq] at h2; exact h2.left_of_append)
      obtain ⟨d₂, r₂, h₂⟩ := ih (n - 1) (by omega) T hlenT hTne
        (fun t ht ↦ h1 t (List.mem_cons_of_mem _ ht)) h2.tail
      rw [hTub] at h₂
      rw [hLeq, List.cons_append]
      exact w.seg_of_overlap hw hSB hb hu h₁ h₂

end Word

end BrickAccessibility
