module

public import BrickAccessibility.SkowWasch.Procedure
public import BrickAccessibility.StringQuotient.Chains

/-!
# Special biserial path data from good representatives

Arrow representatives satisfying the special biserial conditions give admissible special
biserial path data spanning the algebra (`exists_pathData`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

open BrickAccessibility.Statement

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] {B : BasicData k A}

theorem pow_succ_le (n : ℕ) : B.R ^ (n + 2) ≤ B.R ^ (n + 1) := by
  have hclosed : ∀ m : ℕ, ∀ x ∈ B.R ^ (m + 1), ∀ a : A, x * a ∈ B.R ^ (m + 1) := by
    intro m
    induction m with
    | zero => intro x hx a; rw [pow_one] at hx ⊢; exact B.mul_mem_right x a hx
    | succ m ih =>
        intro x hx a
        rw [pow_succ] at hx ⊢
        refine Submodule.mul_induction_on hx (fun y hy r hr ↦ ?_) (fun y z hy hz ↦ ?_)
        · rw [mul_assoc]; exact Submodule.mul_mem_mul hy (B.mul_mem_right r a hr)
        · rw [add_mul]; exact Submodule.add_mem _ hy hz
  rw [pow_succ (B.R) (n + 1), Submodule.mul_le]
  intro x hx y _
  exact hclosed n x hx y

theorem pow_le_pow {m n : ℕ} (h : n ≤ m) : B.R ^ (m + 1) ≤ B.R ^ (n + 1) := by
  induction m with
  | zero => obtain rfl : n = 0 := by omega
            exact le_rfl
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · exact (pow_succ_le m).trans (ih (by omega))
      · obtain rfl : n = m + 1 := by omega
        exact le_rfl

variable (B)

open Classical in
/-- The quiver of arrows. -/
def quiv : FinQuiver where
  V := Fin B.n
  A := {p : Fin B.n × Fin B.n // B.Arr p.1 p.2}
  src a := a.1.1
  tgt a := a.1.2

variable {B}

/-- The path data of good representatives. -/
def pdata {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) : PathData B.quiv A where
  e := B.e
  α a := ρ a.1.1 a.1.2
  e_mul_e := B.e_mul_e
  sum_e := B.sum_e
  α_mul_e a := B.e_right (hρ _ _ a.2).1
  e_mul_α a := B.e_left (hρ _ _ a.2).1

theorem pval_mem {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) :
    ∀ (l : List B.quiv.A) (x : B.quiv.V), l ≠ [] → (pdata hρ).pval x l ∈ B.R ^ l.length := by
  intro l
  induction l with
  | nil => intro x h; exact absurd rfl h
  | cons a l ih =>
      intro x _
      show (pdata hρ).pval (B.quiv.tgt a) l * (pdata hρ).α a * (pdata hρ).e x ∈ _
      have ha : (pdata hρ).α a * (pdata hρ).e x ∈ B.R :=
        B.mul_mem_right _ _ (hρ _ _ a.2).1.2
      rw [mul_assoc]
      by_cases hl : l = []
      · subst hl
        rw [List.length_singleton, pow_one]; exact B.mul_mem_left _ _ ha
      · rw [List.length_cons, pow_succ]
        exact Submodule.mul_mem_mul (ih _ hl) ha

theorem pval_two {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) {a b : B.quiv.A}
    (h : B.quiv.src b = B.quiv.tgt a) :
    (pdata hρ).pval (B.quiv.src a) [a, b] = ρ b.1.1 b.1.2 * ρ a.1.1 a.1.2 := by
  show (pdata hρ).pval (B.quiv.tgt a) [b] * (pdata hρ).α a * (pdata hρ).e (B.quiv.src a) = _
  rw [← h, (pdata hρ).pval_single_src, mul_assoc, (pdata hρ).α_mul_e]
  rfl

theorem card_le_two_of {S : Type*} [Finite S] (H : ∀ a b c : S, a = b ∨ a = c ∨ b = c) :
    Nat.card S ≤ 2 := by
  classical
  by_contra h
  push Not at h
  have := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨f⟩ : Nonempty (Fin 3 ↪ S) :=
    Function.Embedding.nonempty_of_card_le (by simp only [Fintype.card_fin]; omega)
  rcases H (f 0) (f 1) (f 2) with h | h | h <;> have := f.injective h <;> revert this <;> decide

theorem mul_sq_mul {y : A} (hy : y ∈ B.R * B.R) (a b : A) : a * y * b ∈ B.R * B.R := by
  refine Submodule.mul_induction_on hy (fun r hr s hs ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [mul_assoc, mul_assoc, ← mul_assoc a]
    exact Submodule.mul_mem_mul (B.mul_mem_left _ _ hr) (B.mul_mem_right _ _ hs)
  · rw [mul_add, add_mul]; exact Submodule.add_mem _ hy hz

/-- **Vertices and arrows are linearly independent modulo paths of length at least two.** -/
theorem vertArrInd {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) (c : B.quiv.V → k)
    (d : B.quiv.A → k)
    (h : ∑ v, c v • (pdata hρ).e v + ∑ a, d a • (pdata hρ).α a ∈ (pdata hρ).RadGe k 2) :
    c = 0 ∧ d = 0 := by
  classical
  have hR2 : (pdata hρ).RadGe k 2 ≤ B.R * B.R := by
    rw [PathData.RadGe, Submodule.span_le]
    rintro _ ⟨x, l, hl, rfl⟩
    have hl0 : l ≠ [] := by rintro rfl; simp at hl
    have h1 := pval_mem hρ l x hl0
    obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 + 1 := ⟨l.length - 2, by omega⟩
    rw [hm] at h1
    have h2 := pow_le_pow (B := B) (show 1 ≤ m + 1 by omega) h1
    rwa [show (1 : ℕ) + 1 = 2 from rfl, pow_two] at h2
  have hRR : B.R * B.R ≤ B.R := Submodule.mul_le.mpr fun r _ s hs ↦ B.mul_mem_left r s hs
  have hα : ∀ a : B.quiv.A, (pdata hρ).α a ∈ B.Mk a.1.1 a.1.2 := fun a ↦ (hρ _ _ a.2).1
  set x := ∑ v, c v • (pdata hρ).e v + ∑ a, d a • (pdata hρ).α a
  have hx : x ∈ B.R * B.R := hR2 h
  have hαR : ∑ a, d a • (pdata hρ).α a ∈ B.R :=
    Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (hα a).2
  have hcR : ∑ v, c v • (pdata hρ).e v ∈ B.R := by
    have : ∑ v, c v • (pdata hρ).e v = x - ∑ a, d a • (pdata hρ).α a := by simp [x]
    rw [this]; exact Submodule.sub_mem _ (hRR hx) hαR
  have hc : c = 0 := by
    funext w
    by_contra hw
    have h1 : B.e w * (∑ v, c v • (pdata hρ).e v) * B.e w = c w • B.e w := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single w]
      · show B.e w * (c w • B.e w) * B.e w = c w • B.e w
        have hw' : ∀ u : Fin B.n, B.e u * B.e u * B.e u = B.e u := fun u ↦ by
          rw [B.e_idem, B.e_idem]
        rw [mul_smul_comm, smul_mul_assoc]
        exact congrArg (c w • ·) (hw' w)
      · intro v _ hv
        show B.e w * (c v • B.e v) * B.e w = 0
        rw [mul_smul_comm, B.e_mul_e_of_ne (Ne.symm hv), smul_zero, zero_mul]
      · simp
    have h2 : c w • B.e w ∈ B.R := h1 ▸ B.mul_mem_right _ _ (B.mul_mem_left _ _ hcR)
    have h3 : B.e w = (c w)⁻¹ • (c w • B.e w) := by rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
    exact B.e_not_mem w (h3 ▸ Submodule.smul_mem _ _ h2)
  refine ⟨hc, ?_⟩
  have hxα : x = ∑ a, d a • (pdata hρ).α a := by simp [x, hc]
  funext a
  by_contra ha
  obtain ⟨⟨i, j⟩, hij⟩ := a
  have h1 : B.e j * (∑ b, d b • (pdata hρ).α b) * B.e i = d ⟨(i, j), hij⟩ • ρ i j := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single ⟨(i, j), hij⟩]
    · show B.e j * (d _ • ρ i j) * B.e i = _
      rw [mul_smul_comm, smul_mul_assoc, (hρ i j hij).1.1]
    · rintro ⟨⟨i', j'⟩, hb⟩ _ hne
      show B.e j * (d _ • ρ i' j') * B.e i = 0
      have hm := (hρ i' j' hb).1.1
      rw [mul_smul_comm, smul_mul_assoc, ← hm]
      have h0 : B.e j * (B.e j' * ρ i' j' * B.e i') * B.e i = 0 := by
        by_cases hjj : j = j'
        · subst hjj
          have hii : i ≠ i' := fun h ↦ hne (by subst h; rfl)
          rw [mul_assoc, mul_assoc, B.e_mul_e_of_ne (Ne.symm hii), mul_zero, mul_zero]
        · rw [← mul_assoc, ← mul_assoc, B.e_mul_e_of_ne hjj, zero_mul, zero_mul, zero_mul]
      rw [h0]
      exact smul_zero _
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : d ⟨(i, j), hij⟩ • ρ i j ∈ B.R * B.R := h1 ▸ B.mul_sq_mul (hxα ▸ hx) _ _
  have h3 : ρ i j = (d ⟨(i, j), hij⟩)⁻¹ • (d ⟨(i, j), hij⟩ • ρ i j) := by
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  exact (hρ i j hij).2 (h3 ▸ Submodule.smul_mem _ _ h2)

variable (hX : B.ChainX)
  (hin : ∀ j i₁ i₂ i₃, B.Arr i₁ j → B.Arr i₂ j → B.Arr i₃ j → i₁ = i₂ ∨ i₁ = i₃ ∨ i₂ = i₃)
  (hout : ∀ j l₁ l₂ l₃, B.Arr j l₁ → B.Arr j l₂ → B.Arr j l₃ → l₁ = l₂ ∨ l₁ = l₃ ∨ l₂ = l₃)

include hX hin hout in
/-- **Good representatives give special biserial path data.** -/
theorem exists_pathData {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) (hS : B.SuccGood ρ)
    (hP : B.PredGood ρ) :
    ∃ (Q : FinQuiver) (D : PathData Q A),
      Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤ ∧
        D.IsAdmissible ∧ D.IsSpecialBiserial ∧
        ∀ (c : Q.V → k) (d : Q.A → k),
          ∑ v, c v • D.e v + ∑ a, d a • D.α a ∈ D.RadGe k 2 → c = 0 ∧ d = 0 := by
  classical
  refine ⟨B.quiv, pdata hρ, ?_, ?_, ?_, B.vertArrInd hρ⟩
  · -- spanning
    have hRad1 : (pdata hρ).RadGe k 1 ≤ Submodule.span k (Set.range
        (fun p : B.quiv.V × List B.quiv.A ↦ (pdata hρ).pval p.1 p.2)) :=
      Submodule.span_mono (by rintro _ ⟨x, l, -, rfl⟩; exact ⟨(x, l), rfl⟩)
    have hle_pow : ∀ m : ℕ, (pdata hρ).RadGe k (m + 1) ≤ B.R ^ (m + 1) := by
      intro m
      rw [PathData.RadGe, Submodule.span_le]
      rintro _ ⟨x, l, hl, rfl⟩
      have hl0 : l ≠ [] := by rintro rfl; simp at hl
      have h1 := pval_mem hρ l x hl0
      obtain ⟨d, hd⟩ : ∃ d, l.length = d + 1 :=
        ⟨l.length - 1, by have := List.length_pos_iff.mpr hl0; omega⟩
      rw [hd] at h1
      exact pow_le_pow (by omega) h1
    have hR1 : B.R ≤ (pdata hρ).RadGe k 1 ⊔ B.R * B.R := by
      intro r hr
      have hsum : r = ∑ w, ∑ v, B.e w * r * B.e v := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, B.sum_e, one_mul, mul_one]
      rw [hsum]
      refine Submodule.sum_mem _ fun w _ ↦ Submodule.sum_mem _ fun v _ ↦ ?_
      have hM : B.e w * r * B.e v ∈ B.Mk v w :=
        ⟨by simp only [mul_assoc, B.e_idem_assoc, B.e_idem], B.mul_mem_right _ _ (B.mul_mem_left _ _ hr)⟩
      by_cases ha : B.Arr v w
      · have h := B.mem_span_sq hX (hρ v w ha).1 (hρ v w ha).2 hM
        have hsp : Submodule.span k {ρ v w} ≤ (pdata hρ).RadGe k 1 := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          have : ρ v w = (pdata hρ).pval v [⟨(v, w), ha⟩] :=
            ((pdata hρ).pval_single_src (⟨(v, w), ha⟩ : B.quiv.A)).symm
          rw [this]
          exact (pdata hρ).pval_mem_radGe (k := k) (n := 1) v (le_refl _)
        exact (sup_le_sup_right hsp _) h
      · exact Submodule.mem_sup_right (B.mem_sq_of_not_arr ha hM)
    have hstep : ∀ m : ℕ, B.R ^ (m + 1) ≤ (pdata hρ).RadGe k (m + 1) ⊔ B.R ^ (m + 2) := by
      intro m
      induction m with
      | zero => rw [zero_add, pow_one, show (0 : ℕ) + 2 = 2 from rfl, pow_two]; exact hR1
      | succ m ih =>
          calc B.R ^ (m + 1 + 1) = B.R ^ (m + 1) * B.R := pow_succ _ _
            _ ≤ ((pdata hρ).RadGe k (m + 1) ⊔ B.R ^ (m + 2)) *
                ((pdata hρ).RadGe k 1 ⊔ B.R * B.R) := mul_le_mul' ih hR1
            _ ≤ (pdata hρ).RadGe k (m + 1 + 1) ⊔ B.R ^ (m + 1 + 2) := by
                rw [Submodule.mul_sup, Submodule.sup_mul, Submodule.sup_mul]
                refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
                · exact le_sup_of_le_left ((pdata hρ).radGe_mul (k := k) (m + 1) 1)
                · refine le_sup_of_le_right ?_
                  have h0 : (pdata hρ).RadGe k 1 ≤ B.R := by
                    have := hle_pow 0; rwa [zero_add, pow_one] at this
                  calc B.R ^ (m + 2) * (pdata hρ).RadGe k 1 ≤ B.R ^ (m + 2) * B.R :=
                        mul_le_mul' le_rfl h0
                    _ = B.R ^ (m + 1 + 2) := by rw [← pow_succ]
                · refine le_sup_of_le_right ?_
                  calc (pdata hρ).RadGe k (m + 1) * (B.R * B.R)
                        ≤ B.R ^ (m + 1) * (B.R * B.R) := mul_le_mul' (hle_pow m) le_rfl
                    _ = B.R ^ (m + 1 + 2) := by rw [← pow_two, ← pow_add]
                · refine le_sup_of_le_right ?_
                  calc B.R ^ (m + 2) * (B.R * B.R) = B.R ^ (m + 3 + 1) := by
                        rw [← pow_two, ← pow_add]
                    _ ≤ B.R ^ (m + 2 + 1) := pow_le_pow (by omega)
    have hfin : ∀ m : ℕ, B.R ≤ (pdata hρ).RadGe k 1 ⊔ B.R ^ (m + 1) := by
      intro m
      induction m with
      | zero => rw [zero_add, pow_one]; exact le_sup_right
      | succ m ih =>
          refine ih.trans (sup_le le_sup_left ((hstep m).trans (sup_le ?_ le_sup_right)))
          exact le_sup_of_le_left (Submodule.span_mono (by
            rintro _ ⟨x, l, hl, rfl⟩; exact ⟨x, l, by omega, rfl⟩))
    obtain ⟨N, hN⟩ := B.pow_eq_bot
    have hRle : B.R ≤ (pdata hρ).RadGe k 1 := by
      have := hfin N
      rwa [pow_succ, hN, Submodule.bot_mul, sup_bot_eq] at this
    rw [eq_top_iff]
    intro a _
    obtain ⟨c, hc⟩ := B.decomp a
    have ha : a = ∑ v, c v • B.e v + (a - ∑ v, c v • B.e v) := by abel
    rw [ha]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun v _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(v, []), rfl⟩)) (hRad1 (hRle hc))
  · -- admissibility
    refine ⟨fun v ↦ B.e_ne v, fun a h ↦ (hρ _ _ a.2).2 ?_, ?_⟩
    · have h' : ρ a.1.1 a.1.2 = 0 := h
      rw [h']; exact Submodule.zero_mem _
    · obtain ⟨N, hN⟩ := B.pow_eq_bot
      refine ⟨N + 1, fun x l hl ↦ ?_⟩
      have hl0 : l ≠ [] := by rintro rfl; simp at hl
      have h1 := pval_mem hρ l x hl0
      obtain ⟨d, hd⟩ : ∃ d, l.length = d + 1 := ⟨l.length - 1, by omega⟩
      rw [hd] at h1
      have h2 := pow_le_pow (B := B) (show N ≤ d by omega) h1
      rw [pow_succ, hN, Submodule.bot_mul] at h2
      exact (Submodule.mem_bot k).mp h2
  · -- the special biserial conditions
    refine ⟨fun x ↦ card_le_two_of ?_, fun y ↦ card_le_two_of ?_, fun a ↦ ?_, fun b ↦ ?_⟩
    · rintro ⟨⟨⟨x1, l1⟩, h1⟩, hx1⟩ ⟨⟨⟨x2, l2⟩, h2⟩, hx2⟩ ⟨⟨⟨x3, l3⟩, h3⟩, hx3⟩
      change x1 = x at hx1
      change x2 = x at hx2
      change x3 = x at hx3
      subst hx1 hx2 hx3
      rcases hout _ l1 l2 l3 h1 h2 h3 with h | h | h <;> subst h <;>
        first | (left; rfl) | (right; left; rfl) | (right; right; rfl)
    · rintro ⟨⟨⟨x1, l1⟩, h1⟩, hx1⟩ ⟨⟨⟨x2, l2⟩, h2⟩, hx2⟩ ⟨⟨⟨x3, l3⟩, h3⟩, hx3⟩
      change l1 = y at hx1
      change l2 = y at hx2
      change l3 = y at hx3
      subst hx1 hx2 hx3
      rcases hin _ x1 x2 x3 h1 h2 h3 with h | h | h <;> subst h <;>
        first | (left; rfl) | (right; left; rfl) | (right; right; rfl)
    · refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun ⟨b, hb1, hb2⟩ ⟨c, hc1, hc2⟩ ↦ ?_⟩
      rw [pval_two hρ hb1] at hb2
      rw [pval_two hρ hc1] at hc2
      obtain ⟨⟨i, j⟩, ha⟩ := a
      obtain ⟨⟨j', l⟩, hb⟩ := b
      obtain ⟨⟨j'', p⟩, hc⟩ := c
      change j' = j at hb1
      change j'' = j at hc1
      subst hb1 hc1
      by_cases hlp : l = p
      · subst hlp; rfl
      · exfalso
        rcases hS i _ l p ha hb hc hlp with h | h
        · exact hb2 h
        · exact hc2 h
    · refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun ⟨a, ha1, ha2⟩ ⟨c, hc1, hc2⟩ ↦ ?_⟩
      rw [pval_two hρ ha1] at ha2
      rw [pval_two hρ hc1] at hc2
      obtain ⟨⟨j, p⟩, hb⟩ := b
      obtain ⟨⟨i, j'⟩, ha⟩ := a
      obtain ⟨⟨i', j''⟩, hc⟩ := c
      change j = j' at ha1
      change j = j'' at hc1
      subst ha1 hc1
      by_cases hii : i = i'
      · subst hii; rfl
      · exfalso
        rcases hP i i' _ p ha hc hb hii with h | h
        · exact ha2 h
        · exact hc2 h

end BasicData

end SkowWasch

end BrickAccessibility
