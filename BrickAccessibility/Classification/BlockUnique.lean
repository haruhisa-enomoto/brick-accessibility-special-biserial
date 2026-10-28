module

public import BrickAccessibility.Classification.BlockCount

/-!
# Uniqueness of the maximal walks

If every position has at most one traversal of each start sign
(`SignedUnique`), then a position `p` lies in `h⁺ \ h⁻` for at most one
half-word `h` at `(vtx p, s)` (`PM_unique`).
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
variable (C : D.BlockQuiver V) (S : Signs D)

namespace BlockQuiver

/-- At most one traversal of each start sign from every position. -/
def SignedUnique : Prop :=
  ∀ p l l' q q', C.Trav p l q → C.Trav p l' q' → S.st l = S.st l' → l = l'

theorem walk_append (L L' : List (Letter D.Q)) (p : C.P) :
    C.walk (L ++ L') p = (C.walk L p).bind (C.walk L') := by
  induction L generalizing p with
  | nil => rfl
  | cons l L ih =>
      simp only [List.cons_append, walk]
      split_ifs with h
      · exact ih _
      · rfl

theorem walk_singleton {l : Letter D.Q} {p : C.P} {e : C.P}
    (h : C.walk [l] p = some e) : C.Trav p l e := by
  simp only [walk] at h
  split_ifs at h with hq
  simp only [Option.some.injEq] at h
  exact h ▸ hq.choose_spec

/-- The walk along each prefix of a half-word in `h⁺ \ h⁻` succeeds. -/
theorem walk_pre_of_PM {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) {p : C.P}
    (hp : C.vtx p = v) (hPM : C.PM S v s h p) (n : ℕ) : C.walk (h.pre n) p ≠ none := by
  cases h with
  | fin L =>
      obtain ⟨e, he, -⟩ := (C.mem_plus_not_minus_fin S hv hp).mp hPM
      have hsplit : L = L.take n ++ L.drop n := (List.take_append_drop n L).symm
      intro hn
      rw [hsplit, walk_append] at he
      simp only [HWord.pre] at hn
      rw [hn] at he
      cases he
  | inf f => exact (C.mem_plus_not_minus_inf S hv hp).mp hPM n

/-- **Uniqueness**: a position determines its maximal walk. -/
theorem PM_unique (hU : C.SignedUnique S) {v : D.Q.V} {s : Bool} {h h' : HWord D.Q}
    (hv : S.Valid v s h) (hv' : S.Valid v s h') {p : C.P} (hp : C.vtx p = v)
    (hPM : C.PM S v s h p) (hPM' : C.PM S v s h' p) : h = h' := by
  refine S.code_injective hv hv' (funext fun n ↦ ?_)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hE : h.pre n = h'.pre n := S.pre_eq_of_code_eq hv hv' n fun j hj ↦ ih j hj
  -- the common end of the walks along the common prefix
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (C.walk_pre_of_PM S hv hp hPM n)
  have he' : C.walk (h'.pre n) p = some e := hE ▸ he
  -- a letter of a half-word in `PM` at position `n` traverses from `e`
  have trav_of : ∀ {g : HWord D.Q}, S.Valid v s g → C.PM S v s g p → g.pre n = h.pre n →
      ∀ {l}, g.pre (n + 1) = g.pre n ++ [l] → ∃ q, C.Trav e l q := by
    intro g hg hgp hgE l hl
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (C.walk_pre_of_PM S hg hp hgp (n + 1))
    rw [hl, walk_append, hgE, he] at hq
    exact ⟨q, C.walk_singleton hq⟩
  -- a half-word in `PM` ending at `n` has no traversal of the next sign
  have stop_of : ∀ {g : HWord D.Q}, S.Valid v s g → C.PM S v s g p → g.pre n = h.pre n →
      g.code n = 1 → ¬ C.TravSign S e (S.nsign s (h.pre n)) := by
    intro g hg hgp hgE hc
    have hgfin := g.eq_fin_of_code_eq_one hc
    rw [hgfin] at hgp hg
    obtain ⟨e', he'', hT⟩ := (C.mem_plus_not_minus_fin S hg hp).mp hgp
    rw [hgE, he] at he''
    cases he''
    rwa [hgE] at hT
  by_cases hc : h.code n = 1
  · by_cases hc' : h'.code n = 1
    · rw [hc, hc']
    · exfalso
      obtain ⟨l', hl', -⟩ := h'.pre_succ_of_code_ne hc'
      obtain ⟨q', hq'⟩ := trav_of hv' hPM' hE.symm hl'
      have hs' := (S.cont_of_pre hv' hl').2
      exact stop_of hv hPM rfl hc ⟨l', q', by rw [hs', hE], hq'⟩
  · by_cases hc' : h'.code n = 1
    · exfalso
      obtain ⟨l, hl, -⟩ := h.pre_succ_of_code_ne hc
      obtain ⟨q, hq⟩ := trav_of hv hPM rfl hl
      have hs := (S.cont_of_pre hv hl).2
      exact stop_of hv' hPM' hE.symm hc' ⟨l, q, hs, hq⟩
    · obtain ⟨l, hl, hld⟩ := h.pre_succ_of_code_ne hc
      obtain ⟨l', hl', hld'⟩ := h'.pre_succ_of_code_ne hc'
      obtain ⟨q, hq⟩ := trav_of hv hPM rfl hl
      obtain ⟨q', hq'⟩ := trav_of hv' hPM' hE.symm hl'
      have hs := (S.cont_of_pre hv hl).2
      have hs' := (S.cont_of_pre hv' hl').2
      rw [← hE] at hs'
      have hll' := hU e l l' q q' hq hq' (hs.trans hs'.symm)
      have b1 := h.code_le_two n
      have b2 := h'.code_le_two n
      by_cases h2 : h.code n = 2
      · have : l.2 = true := hld.mp h2
        rw [hll'] at this
        rw [h2, hld'.mpr this]
      · have h0 : h.code n = 0 := by omega
        have : l'.2 = false := by
          rw [← hll']
          cases hb : l.2
          · rfl
          · exact absurd (hld.mpr hb) h2
        have h0' : h'.code n ≠ 2 := fun e ↦ by rw [hld'.mp e] at this; cases this
        omega

theorem vtx_of_plusSet {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) {p : C.P}
    (hp : C.plusSet S v s h p) : C.vtx p = v := by
  cases h with
  | fin L =>
      cases L with
      | nil => exact hp.1
      | cons l L =>
          obtain ⟨hl, -⟩ := hv.1
          obtain ⟨a, d⟩ := l
          cases d
          · obtain ⟨i, -, hi⟩ := hp
            rw [C.next_tgt a i p hi]; exact hl
          · exact hp.1.trans hl
  | inf f => exact hp 0

theorem vtx_of_PM {v : D.Q.V} {s : Bool} {h : HWord D.Q} (hv : S.Valid v s h) {p : C.P}
    (hp : C.PM S v s h p) : C.vtx p = v := C.vtx_of_plusSet S hv hp.1

end BlockQuiver

end MonomialData

end BrickAccessibility
