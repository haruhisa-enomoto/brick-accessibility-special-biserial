module

public import BrickAccessibility.Classification.Filtration

/-!
# Prepending a letter to a half-word

`cons l h` prepends `l` to `h`. If `h` is valid at `(l.tgt, !en l)` and `l` starts
at `v` with sign `s`, then `cons l h` is valid at `(v, s)`, and its boundary
subspaces are the transports of those of `h` along `l` (for an inverse letter
and an infinite half-word this uses finite dimension).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace HWord

variable {Q : FinQuiver}

/-- Prepend a letter. -/
def cons (l : Letter Q) : HWord Q → HWord Q
  | fin C => fin (l :: C)
  | inf f => inf fun i ↦ Nat.casesOn i l f

theorem pre_cons_succ (l : Letter Q) (h : HWord Q) (n : ℕ) :
    (cons l h).pre (n + 1) = l :: h.pre n := by
  cases h with
  | fin C => rfl
  | inf f => simp [cons, pre, List.ofFn_succ]

end HWord

/-- An antitone sequence of subspaces of a finite-dimensional space stabilizes. -/
theorem exists_antitone_stable {k : Type*} [Field k] {X : Type*} [AddCommGroup X] [Module k X]
    [FiniteDimensional k X] (U : ℕ → Submodule k X) (hU : Antitone U) :
    ∃ N, ∀ n ≥ N, U n = U N := by
  classical
  have : ∃ N, ∀ n, finrank k (U N) ≤ finrank k (U n) :=
    ⟨Nat.find (⟨finrank k (U 0), 0, rfl⟩ : ∃ d, ∃ n, finrank k (U n) = d) |> fun d ↦
      (Nat.find_spec (⟨finrank k (U 0), 0, rfl⟩ : ∃ d, ∃ n, finrank k (U n) = d)).choose,
      fun n ↦ by
        have hs := (Nat.find_spec (⟨finrank k (U 0), 0, rfl⟩ :
          ∃ d, ∃ n, finrank k (U n) = d)).choose_spec
        rw [hs]
        exact Nat.find_min' _ ⟨n, rfl⟩⟩
  obtain ⟨N, hN⟩ := this
  refine ⟨N, fun n hn ↦ ?_⟩
  exact Submodule.eq_of_le_of_finrank_le (hU hn) (hN n)

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)

theorem Signs.nsign_cons (s : Bool) (l : Letter D.Q) (E : List (Letter D.Q)) :
    S.nsign s (l :: E) = S.nsign (!S.en l) E := by
  cases E using List.reverseRecOn with
  | nil => simp [Signs.nsign]
  | append_singleton E x _ =>
      rw [← List.cons_append, Signs.nsign_append_singleton, Signs.nsign_append_singleton]

theorem Signs.isHW_cons {v : D.Q.V} {s : Bool} {l : Letter D.Q} {C : List (Letter D.Q)}
    (hl : l.src = v) (hs : S.st l = s) (h : S.IsHW l.tgt (!S.en l) C) : S.IsHW v s (l :: C) := by
  refine ⟨⟨hl, h.1⟩, fun i hi ↦ ?_⟩
  cases i with
  | zero => simpa using hs
  | succ i =>
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      rw [S.nsign_cons]
      exact h.2 i (by simpa using hi)

theorem Signs.valid_cons {v : D.Q.V} {s : Bool} {l : Letter D.Q} {h : HWord D.Q}
    (hl : l.src = v) (hs : S.st l = s) (hv : S.Valid l.tgt (!S.en l) h) :
    S.Valid v s (h.cons l) := by
  cases h with
  | fin C => exact S.isHW_cons hl hs hv
  | inf f =>
      intro n
      cases n with
      | zero => exact S.isHW_nil v s
      | succ n =>
          have := S.isHW_cons hl hs (hv n)
          simpa [List.ofFn_succ] using this

variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

theorem Signs.plus_cons_of_fin (v : D.Q.V) (s : Bool) (l : Letter D.Q) (C : List (Letter D.Q))
    (hl : l.src = v) :
    S.plus M v s ((HWord.fin C).cons l) = D.tr l (S.plus M l.tgt (!S.en l) (.fin C)) := by
  simp only [HWord.cons, Signs.plus, Signs.plusF, trs_cons, Statement.FinQuiver.wend, S.nsign_cons]

theorem Signs.minus_cons_of_fin (v : D.Q.V) (s : Bool) (l : Letter D.Q) (C : List (Letter D.Q)) :
    S.minus M v s ((HWord.fin C).cons l) = D.tr l (S.minus M l.tgt (!S.en l) (.fin C)) := by
  simp only [HWord.cons, Signs.minus, Signs.minusF, trs_cons, Statement.FinQuiver.wend,
    S.nsign_cons]

theorem trs_ofFn_bot_mono (f : ℕ → Letter D.Q) :
    Monotone fun n ↦ D.trs (List.ofFn fun i : Fin n ↦ f i) (⊥ : Submodule k M) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [List.ofFn_succ_last, D.trs_append]
  simp only [Fin.coe_castSucc]
  exact D.trs_mono _ bot_le

theorem Signs.minus_cons (v : D.Q.V) (s : Bool) (l : Letter D.Q) (h : HWord D.Q) :
    S.minus M v s (h.cons l) = D.tr l (S.minus M l.tgt (!S.en l) h) := by
  cases h with
  | fin C => exact S.minus_cons_of_fin v s l C
  | inf f =>
      simp only [HWord.cons, Signs.minus]
      have hdir := (trs_ofFn_bot_mono (M := M) f).directed_le
      apply le_antisymm
      · refine iSup_le fun n ↦ ?_
        cases n with
        | zero => exact bot_le
        | succ n =>
            simp only [List.ofFn_succ, trs_cons]
            exact D.tr_mono _ (le_iSup (fun n ↦ D.trs (List.ofFn fun i : Fin n ↦ f i) ⊥) n)
      · obtain ⟨a, d⟩ := l
        intro x hx
        cases d
        · obtain ⟨y, hyv, hy, rfl⟩ := (D.mem_tr_false).mp hx
          obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
          refine Submodule.mem_iSup_of_mem (n + 1) ?_
          simp only [List.ofFn_succ, trs_cons]
          exact (D.mem_tr_false).mpr ⟨y, hyv, by simpa using hn, rfl⟩
        · obtain ⟨hxv, hx'⟩ := (D.mem_tr_true).mp hx
          obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hx'
          refine Submodule.mem_iSup_of_mem (n + 1) ?_
          simp only [List.ofFn_succ, trs_cons]
          exact (D.mem_tr_true).mpr ⟨hxv, by simpa using hn⟩

theorem trs_ofFn_vsp_anti {v : D.Q.V} (f : ℕ → Letter D.Q)
    (hw : ∀ n, D.Q.IsWalk v (List.ofFn fun i : Fin n ↦ f i)) :
    Antitone fun n ↦ D.trs (List.ofFn fun i : Fin n ↦ f i)
      (D.vsp M (D.Q.wend v (List.ofFn fun i : Fin n ↦ f i))) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  have hw' := hw (n + 1)
  rw [List.ofFn_succ_last] at hw' ⊢
  simp only [Fin.coe_castSucc, Fin.val_last] at hw' ⊢
  rw [D.trs_append, Statement.FinQuiver.isWalk_append] at *
  refine D.trs_mono _ ((D.tr_le_vsp _ _).trans (le_of_eq ?_))
  rw [hw'.2.1]

theorem Signs.plus_cons [FiniteDimensional k M] {v : D.Q.V} {s : Bool} {l : Letter D.Q}
    {h : HWord D.Q} (hl : l.src = v) (hv : S.Valid l.tgt (!S.en l) h) :
    S.plus M v s (h.cons l) = D.tr l (S.plus M l.tgt (!S.en l) h) := by
  cases h with
  | fin C => exact S.plus_cons_of_fin v s l C hl
  | inf f =>
      simp only [HWord.cons, Signs.plus]
      set Y : ℕ → Submodule k M := fun n ↦ D.trs (List.ofFn fun i : Fin n ↦ f i)
        (D.vsp M (D.Q.wend l.tgt (List.ofFn fun i : Fin n ↦ f i))) with hY
      have hterm : ∀ n, D.trs (List.ofFn fun i : Fin (n + 1) ↦ (Nat.casesOn (i : ℕ) l f : Letter D.Q))
          (D.vsp M (D.Q.wend v (List.ofFn fun i : Fin (n + 1) ↦
            (Nat.casesOn (i : ℕ) l f : Letter D.Q)))) = D.tr l (Y n) := by
        intro n
        simp [List.ofFn_succ, Y, Statement.FinQuiver.wend]
      have hanti : Antitone Y := trs_ofFn_vsp_anti f fun n ↦ (hv n).1
      obtain ⟨N, hN⟩ := exists_antitone_stable Y hanti
      have hinf : (⨅ n, Y n) = Y N :=
        le_antisymm (iInf_le _ N) (le_iInf fun n ↦ by
          rcases le_total n N with h | h
          · exact hanti h
          · rw [hN n h])
      rw [hinf]
      apply le_antisymm
      · exact (iInf_le _ (N + 1)).trans (hterm N).le
      · refine le_iInf fun n ↦ ?_
        cases n with
        | zero =>
            simp only [List.ofFn_zero, trs_nil, Statement.FinQuiver.wend]
            exact (D.tr_le_vsp l _).trans (by rw [hl])
        | succ n =>
            rw [hterm n]
            refine D.tr_mono l ?_
            rcases le_total n N with h | h
            · exact hanti h
            · rw [hN n h]

end MonomialData

end BrickAccessibility
