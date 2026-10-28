module

public import BrickAccessibility.Classification.HWord

/-!
# Coverage of the vertex spaces by half-word intervals

Every nonzero `m ∈ M_v` lies in `h⁺` but not in `h⁻` for some half-word `h` at
`(v, s)`: extend the empty word by the direct continuation while `m ∉ E⁺` and by
the inverse continuation while `m ∈ E⁻`, keeping `m ∈ E^* M` and `m ∉ E^* 0`.
The process stops at a finite word or defines an infinite one.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : Signs D)
variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

open Classical in
/-- One step of the coverage process. -/
def Signs.step (v : D.Q.V) (s : Bool) (m : M) (E : List (Letter D.Q)) : Option (Letter D.Q) :=
  if m ∉ S.plusF M v s E then
    (if hb : ∃ b, D.Q.src b = D.Q.wend v E ∧ S.σ b = S.nsign s E then some (hb.choose, true)
      else none)
  else if m ∈ S.minusF M v s E then
    (if hd : ∃ d, D.Q.tgt d = D.Q.wend v E ∧ S.ε d = S.nsign s E then some (hd.choose, false)
      else none)
  else none

/-- The prefixes produced by the coverage process. -/
def Signs.proc (v : D.Q.V) (s : Bool) (m : M) : ℕ → List (Letter D.Q)
  | 0 => []
  | n + 1 => match S.step v s m (Signs.proc v s m n) with
    | none => Signs.proc v s m n
    | some l => Signs.proc v s m n ++ [l]

/-- The invariant of the coverage process. -/
def Signs.Inv (v : D.Q.V) (s : Bool) (m : M) (E : List (Letter D.Q)) : Prop :=
  S.IsHW v s E ∧ m ∈ D.trs E (D.vsp M (D.Q.wend v E)) ∧ m ∉ D.trs E (⊥ : Submodule k M)

theorem Signs.inv_step {v : D.Q.V} {s : Bool} {m : M} {E : List (Letter D.Q)}
    (h : S.Inv v s m E) {l : Letter D.Q} (hl : S.step v s m E = some l) :
    S.Inv v s m (E ++ [l]) := by
  classical
  obtain ⟨hw, h1, h2⟩ := h
  unfold Signs.step at hl
  by_cases hp : m ∉ S.plusF M v s E
  · rw [if_pos hp] at hl
    by_cases hb : ∃ b, D.Q.src b = D.Q.wend v E ∧ S.σ b = S.nsign s E
    · rw [dif_pos hb] at hl
      cases hl
      obtain ⟨hsrc, hsign⟩ := hb.choose_spec
      refine ⟨S.isHW_append_singleton hw hsrc hsign, ?_, ?_⟩
      · rw [D.trs_append, Statement.FinQuiver.wend_append]
        simp only [trs_cons, trs_nil, Statement.FinQuiver.wend, Letter.tgt, if_true]
        rw [tr_true_vsp, hsrc]; exact h1
      · rw [D.trs_append]
        simp only [trs_cons, trs_nil]
        rw [tr_true_bot, hsrc, ← S.Kc_eq _ _ hb.choose_spec]
        exact hp
    · rw [dif_neg hb] at hl; cases hl
  · rw [if_neg hp] at hl
    by_cases hm : m ∈ S.minusF M v s E
    · rw [if_pos hm] at hl
      by_cases hd : ∃ d, D.Q.tgt d = D.Q.wend v E ∧ S.ε d = S.nsign s E
      · rw [dif_pos hd] at hl
        cases hl
        obtain ⟨htgt, hsign⟩ := hd.choose_spec
        refine ⟨S.isHW_append_singleton hw htgt hsign, ?_, ?_⟩
        · rw [D.trs_append, Statement.FinQuiver.wend_append]
          simp only [trs_cons, trs_nil, Statement.FinQuiver.wend, Letter.tgt]
          rw [if_neg Bool.false_ne_true, tr_false_vsp, ← S.Ic_eq _ _ hd.choose_spec]
          exact hm
        · rw [D.trs_append]
          simp only [trs_cons, trs_nil]
          rw [tr_false_bot]
          exact h2
      · rw [dif_neg hd] at hl; cases hl
    · rw [if_neg hm] at hl; cases hl

theorem Signs.stop_of_step {v : D.Q.V} {s : Bool} {m : M} {E : List (Letter D.Q)}
    (h : S.Inv v s m E) (hn : S.step v s m E = none) :
    m ∈ S.plusF M v s E ∧ m ∉ S.minusF M v s E := by
  classical
  obtain ⟨hw, h1, h2⟩ := h
  unfold Signs.step at hn
  by_cases hp : m ∉ S.plusF M v s E
  · rw [if_pos hp] at hn
    by_cases hb : ∃ b, D.Q.src b = D.Q.wend v E ∧ S.σ b = S.nsign s E
    · rw [dif_pos hb] at hn; cases hn
    · exfalso; apply hp
      rw [Signs.plusF, S.Kc_eq_vsp _ _ hb]; exact h1
  · rw [if_neg hp] at hn
    by_cases hm : m ∈ S.minusF M v s E
    · rw [if_pos hm] at hn
      by_cases hd : ∃ d, D.Q.tgt d = D.Q.wend v E ∧ S.ε d = S.nsign s E
      · rw [dif_pos hd] at hn; cases hn
      · exfalso
        rw [Signs.minusF, S.Ic_eq_bot _ _ hd] at hm
        exact h2 hm
    · exact ⟨not_not.mp hp, hm⟩

theorem Signs.inv_proc (v : D.Q.V) (s : Bool) {m : M} (hm : m ∈ D.vsp M v) (hm0 : m ≠ 0) :
    ∀ n, S.Inv v s m (S.proc v s m n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨S.isHW_nil v s, hm, ?_⟩
      show m ∉ (⊥ : Submodule k M)
      simpa using hm0
  | succ n ih =>
      simp only [Signs.proc]
      cases hs : S.step v s m (S.proc v s m n) with
      | none => exact ih
      | some l => exact S.inv_step ih hs

/-- **Coverage.** -/
theorem Signs.exists_hword (v : D.Q.V) (s : Bool) {m : M} (hm : m ∈ D.vsp M v) (hm0 : m ≠ 0) :
    ∃ h : HWord D.Q, S.Valid v s h ∧ m ∈ S.plus M v s h ∧ m ∉ S.minus M v s h := by
  classical
  have hinv := S.inv_proc v s hm hm0
  by_cases hstop : ∃ n, S.step v s m (S.proc v s m n) = none
  · obtain ⟨n, hn⟩ := hstop
    exact ⟨.fin (S.proc v s m n), (hinv n).1, S.stop_of_step (hinv n) hn⟩
  · push Not at hstop
    have hex : ∀ n, ∃ l, S.step v s m (S.proc v s m n) = some l :=
      fun n ↦ Option.ne_none_iff_exists'.mp (hstop n)
    choose f hf using hex
    have hpre : ∀ n, (List.ofFn fun i : Fin n ↦ f i) = S.proc v s m n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [List.ofFn_succ_last]
          simp only [Fin.coe_castSucc, Fin.val_last]
          rw [ih]
          simp only [Signs.proc, hf n]
    refine ⟨.inf f, fun n ↦ (hpre n) ▸ (hinv n).1, ?_, ?_⟩
    · refine Submodule.mem_iInf _ |>.mpr fun n ↦ ?_
      rw [hpre n]; exact (hinv n).2.1
    · intro hmem
      have hdir : Directed (· ≤ ·) fun n ↦
          D.trs (List.ofFn fun i : Fin n ↦ f i) (⊥ : Submodule k M) := by
        refine Monotone.directed_le (monotone_nat_of_le_succ fun n ↦ ?_)
        rw [List.ofFn_succ_last, D.trs_append]
        simp only [Fin.coe_castSucc]
        exact D.trs_mono _ bot_le
      obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hmem
      rw [hpre n] at hn
      exact (hinv n).2.2 hn

end MonomialData

end BrickAccessibility
