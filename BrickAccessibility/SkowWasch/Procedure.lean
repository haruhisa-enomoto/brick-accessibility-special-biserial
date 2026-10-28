module

public import BrickAccessibility.SkowWasch.Arrows

/-!
# The replacement procedure of Skowroński–Waschbüsch (Lemma 2)

If the arrow `α : i → j` has two successors `β, γ` with `βα, γα ≠ 0` and `γα ∈ A·βα`,
replacing `γ` by `γ (e_j - y)` keeps every zero product of two arrows and kills `γα`
(`fix_succ`); dually for two predecessors (`fix_pred`). Inducting on the number of nonzero
products gives representatives satisfying the special biserial conditions (`exists_good`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] (B : BasicData k A)

/-- `A a` is a chain of cyclic submodules. -/
def LChain (a : A) : Prop := ∀ u v : A, (∃ w, u * a = w * (v * a)) ∨ (∃ w, v * a = w * (u * a))

/-- `a A` is a chain of cyclic submodules. -/
def RChain (a : A) : Prop := ∀ u v : A, (∃ w, a * u = a * v * w) ∨ (∃ w, a * v = a * u * w)

/-- The nonzero products of two composable arrow representatives. -/
def NZ (ρ : Fin B.n → Fin B.n → A) : Finset (Fin B.n × Fin B.n × Fin B.n) := by
  classical
  exact Finset.univ.filter fun t ↦
    B.Arr t.1 t.2.1 ∧ B.Arr t.2.1 t.2.2 ∧ ρ t.2.1 t.2.2 * ρ t.1 t.2.1 ≠ 0

theorem mem_NZ {ρ : Fin B.n → Fin B.n → A} {t : Fin B.n × Fin B.n × Fin B.n} :
    t ∈ B.NZ ρ ↔ B.Arr t.1 t.2.1 ∧ B.Arr t.2.1 t.2.2 ∧ ρ t.2.1 t.2.2 * ρ t.1 t.2.1 ≠ 0 := by
  classical
  simp [NZ]

/-- Replace one representative. -/
def upd (ρ : Fin B.n → Fin B.n → A) (j p : Fin B.n) (g : A) : Fin B.n → Fin B.n → A := by
  classical
  exact fun a b ↦ if a = j ∧ b = p then g else ρ a b

theorem upd_same (ρ : Fin B.n → Fin B.n → A) (j p : Fin B.n) (g : A) : B.upd ρ j p g j p = g := by
  classical
  simp [upd]

theorem upd_ne (ρ : Fin B.n → Fin B.n → A) {j p a b : Fin B.n} (g : A) (h : ¬ (a = j ∧ b = p)) :
    B.upd ρ j p g a b = ρ a b := by
  classical
  simp only [upd, if_neg h]

/-- Successor condition. -/
def SuccGood (ρ : Fin B.n → Fin B.n → A) : Prop :=
  ∀ i j l p, B.Arr i j → B.Arr j l → B.Arr j p → l ≠ p → ρ j l * ρ i j = 0 ∨ ρ j p * ρ i j = 0

/-- Predecessor condition. -/
def PredGood (ρ : Fin B.n → Fin B.n → A) : Prop :=
  ∀ i i' j p, B.Arr i j → B.Arr i' j → B.Arr j p → i ≠ i' → ρ j p * ρ i j = 0 ∨ ρ j p * ρ i' j = 0

variable {B} (hX : B.ChainX)
  (hin : ∀ j i₁ i₂ i₃, B.Arr i₁ j → B.Arr i₂ j → B.Arr i₃ j → i₁ = i₂ ∨ i₁ = i₃ ∨ i₂ = i₃)
  (hout : ∀ j l₁ l₂ l₃, B.Arr j l₁ → B.Arr j l₂ → B.Arr j l₃ → l₁ = l₂ ∨ l₁ = l₃ ∨ l₂ = l₃)

theorem mul_mem_sq {x y : A} (hx : x ∈ B.R) (hy : y ∈ B.R) : x * y ∈ B.R * B.R :=
  Submodule.mul_mem_mul hx hy

include hX in
/-- The core of the successor fix: `γα = x βα` gives `γα = γ y α` with `y ∈ N_j`. -/
theorem succ_core {i j l p : Fin B.n} {a b g x0 : A} (haM : a ∈ B.Mk i j) (hbM : b ∈ B.Mk j l)
    (hgM : g ∈ B.Mk j p) (hg2 : g ∉ B.R * B.R) (hlp : l ≠ p) (hg : g * a ≠ 0)
    (hx0 : g * a = x0 * (b * a)) :
    ∃ y, y ∈ B.R ∧ B.e j * y * B.e j = y ∧ g * a = g * y * a := by
  set x := B.e p * x0 * B.e l with hxdef
  have hx : g * a = x * (b * a) := by
    simp only [hxdef, mul_assoc, B.e_left' hbM]
    rw [← hx0, B.e_left' hgM]
  have hxR : x ∈ B.R := B.corner_mem (Ne.symm hlp) x0
  have hxb : x * b ∈ B.Mk j p := ⟨by simp only [hxdef, mul_assoc, B.e_idem_assoc, B.e_right hbM],
    B.mul_mem_right _ _ hxR⟩
  have hxb2 : x * b ∈ B.R * B.R := mul_mem_sq hxR hbM.2
  rcases B.one_sided hX hgM hg2 with hl | hr
  · exfalso
    obtain ⟨w, hw⟩ := hl _ hxb
    obtain ⟨c, r, hr, -, hc⟩ := B.corner p w
    have h1 : x * b = c • g + r * g := by
      calc x * b = B.e p * (x * b) := (B.e_left hxb).symm
        _ = B.e p * w * B.e p * g := by rw [hw, mul_assoc (B.e p * w), B.e_left hgM, mul_assoc]
        _ = c • g + r * g := by rw [hc, add_mul, smul_mul_assoc, B.e_left hgM]
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, zero_add] at h1
      apply hg
      refine B.eq_zero_of_eq_mul_left hr ?_
      calc g * a = x * (b * a) := hx
        _ = x * b * a := (mul_assoc _ _ _).symm
        _ = r * (g * a) := by rw [h1, mul_assoc]
    · apply hg2
      have : g = c⁻¹ • (x * b - r * g) := by
        rw [h1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hxb2 (mul_mem_sq hr hgM.2))
  · obtain ⟨w, hw⟩ := hr _ hxb
    obtain ⟨c, r, hr, hre, hc⟩ := B.corner j w
    have h1 : x * b = c • g + g * r := by
      calc x * b = x * b * B.e j := (B.e_right hxb).symm
        _ = g * (B.e j * w * B.e j) := by
          rw [hw]; nth_rewrite 1 [← B.e_right hgM]; simp only [mul_assoc]
        _ = c • g + g * r := by rw [hc, mul_add, mul_smul_comm, B.e_right hgM]
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, zero_add] at h1
      exact ⟨r, hr, hre, by rw [hx, ← mul_assoc, h1]⟩
    · exfalso
      apply hg2
      have : g = c⁻¹ • (x * b - g * r) := by
        rw [h1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hxb2 (mul_mem_sq hgM.2 hr))

include hX hin in
/-- **Fixing two successors.** -/
theorem fix_succ {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) {i j l p : Fin B.n}
    (hij : B.Arr i j) (hjl : B.Arr j l) (hjp : B.Arr j p) (hlp : l ≠ p)
    (hg : ρ j p * ρ i j ≠ 0) {x0 : A} (hx0 : ρ j p * ρ i j = x0 * (ρ j l * ρ i j)) :
    ∃ ρ', B.Valid ρ' ∧ B.NZ ρ' ⊂ B.NZ ρ := by
  classical
  obtain ⟨haM, -⟩ := hρ i j hij
  obtain ⟨hbM, -⟩ := hρ j l hjl
  obtain ⟨hgM, hg2⟩ := hρ j p hjp
  obtain ⟨y, hyR, hye, hgya⟩ := B.succ_core hX haM hbM hgM hg2 hlp hg hx0
  have hyj : B.e j * y = y := by rw [← hye, ← mul_assoc, ← mul_assoc, B.e_idem]
  have hjy : y * B.e j = y := by rw [← hye, mul_assoc, B.e_idem]
  have hg'a : (ρ j p - ρ j p * y) * ρ i j = 0 := by rw [sub_mul, ← hgya, sub_self]
  have hg'g : ρ j p - ρ j p * y = ρ j p * (B.e j - y) := by rw [mul_sub, B.e_right hgM]
  -- every arrow into `j` has a nonzero product with `γ`
  have hall : ∀ i', B.Arr i' j → ρ j p * ρ i' j ≠ 0 := by
    intro i0 hi0 h0
    have hi0i : i0 ≠ i := by rintro rfl; exact hg h0
    have hyS : y ∈ B.Sright ρ j := B.eR_le hX hρ j ⟨hyj, hyR⟩
    have key : ∀ z ∈ B.Sright ρ j, ∃ w, ρ j p * z = ρ j p * ρ i j * w := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨i', w, hi', rfl⟩ := hz
          rcases hin j i i0 i' hij hi0 hi' with h | h | h
          · exact absurd h.symm hi0i
          · subst h; exact ⟨w, by rw [mul_assoc]⟩
          · subst h; exact ⟨0, by rw [← mul_assoc, h0, zero_mul, mul_zero]⟩
      | zero => exact ⟨0, by simp⟩
      | add z z' _ _ h h' =>
          obtain ⟨w, hw⟩ := h; obtain ⟨w', hw'⟩ := h'
          exact ⟨w + w', by rw [mul_add, hw, hw', mul_add]⟩
      | smul c z _ h =>
          obtain ⟨w, hw⟩ := h
          exact ⟨c • w, by rw [mul_smul_comm, hw, mul_smul_comm]⟩
    obtain ⟨w, hw⟩ := key y hyS
    apply hg
    refine B.eq_zero_of_eq_mul_right (B.mul_mem_left w _ haM.2) ?_
    calc ρ j p * ρ i j = ρ j p * y * ρ i j := hgya
      _ = ρ j p * ρ i j * w * ρ i j := by rw [hw]
      _ = ρ j p * ρ i j * (w * ρ i j) := by rw [mul_assoc (ρ j p * ρ i j)]
  refine ⟨B.upd ρ j p (ρ j p - ρ j p * y), ?_, ?_⟩
  · intro i' j' h
    by_cases hc : i' = j ∧ j' = p
    · obtain ⟨rfl, rfl⟩ := hc
      rw [upd_same]
      refine ⟨⟨?_, Submodule.sub_mem _ hgM.2 (B.mul_mem_right _ _ hgM.2)⟩, fun h2 ↦ ?_⟩
      · rw [mul_sub, sub_mul, hgM.1, ← mul_assoc, B.e_left hgM, mul_assoc, hjy]
      · apply hg2
        have := Submodule.add_mem _ h2 (mul_mem_sq hgM.2 hyR)
        rwa [sub_add_cancel] at this
    · rw [B.upd_ne ρ _ hc]; exact hρ i' j' h
  · rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(i, j, p), (B.mem_NZ).mpr ⟨hij, hjp, hg⟩, fun h ↦ ?_⟩
      obtain ⟨-, -, h3⟩ := (B.mem_NZ).mp h
      apply h3
      simp only
      rw [upd_same]
      by_cases hc : i = j ∧ j = p
      · obtain ⟨rfl, rfl⟩ := hc
        rw [upd_same]
        rw [mul_sub, hg'a, zero_sub, ← mul_assoc, hg'a, zero_mul, neg_zero]
      · rw [B.upd_ne ρ _ hc]; exact hg'a
    · intro t ht
      obtain ⟨h1, h2, h3⟩ := (B.mem_NZ).mp ht
      refine (B.mem_NZ).mpr ⟨h1, h2, ?_⟩
      obtain ⟨i', j', l'⟩ := t
      simp only at h1 h2 h3 ⊢
      by_cases hc1 : j' = j ∧ l' = p
      · obtain ⟨rfl, rfl⟩ := hc1
        exact hall i' h1
      · rw [B.upd_ne ρ _ hc1] at h3
        by_cases hc2 : i' = j ∧ j' = p
        · obtain ⟨rfl, rfl⟩ := hc2
          rw [upd_same, hg'g, ← mul_assoc] at h3
          intro h0
          exact h3 (by rw [h0, zero_mul])
        · rwa [B.upd_ne ρ _ hc2] at h3

include hX in
/-- The core of the predecessor fix: `γα' = γα x` gives `γα' = γ y α'` with `y ∈ N_j`. -/
theorem pred_core {i i' j : Fin B.n} {a a' g x0 : A} (haM : a ∈ B.Mk i j)
    (ha'M : a' ∈ B.Mk i' j) (ha'2 : a' ∉ B.R * B.R) (hii : i ≠ i') (hg : g * a' ≠ 0)
    (hx0 : g * a' = g * a * x0) :
    ∃ y, y ∈ B.R ∧ B.e j * y * B.e j = y ∧ g * a' = g * y * a' := by
  set x := B.e i * x0 * B.e i' with hxdef
  have hx : g * a' = g * a * x := by
    have h1 : g * a * x = g * a * x0 * B.e i' := by
      simp only [hxdef, ← mul_assoc]
      rw [mul_assoc g a (B.e i), B.e_right haM]
    rw [h1, ← hx0, mul_assoc, B.e_right ha'M]
  have hxR : x ∈ B.R := B.corner_mem hii x0
  have hax : a * x ∈ B.Mk i' j := ⟨by
    simp only [hxdef, ← mul_assoc]
    rw [B.e_left haM]; simp only [mul_assoc, B.e_idem],
    B.mul_mem_left _ _ hxR⟩
  have hax2 : a * x ∈ B.R * B.R := mul_mem_sq haM.2 hxR
  rcases B.one_sided hX ha'M ha'2 with hl | hr
  · obtain ⟨w, hw⟩ := hl _ hax
    obtain ⟨c, r, hr, hre, hc⟩ := B.corner j w
    have h1 : a * x = c • a' + r * a' := by
      calc a * x = B.e j * (a * x) := (B.e_left hax).symm
        _ = B.e j * w * B.e j * a' := by
          rw [hw, mul_assoc (B.e j * w), B.e_left ha'M, mul_assoc]
        _ = c • a' + r * a' := by rw [hc, add_mul, smul_mul_assoc, B.e_left ha'M]
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, zero_add] at h1
      exact ⟨r, hr, hre, by rw [hx, mul_assoc, h1, ← mul_assoc]⟩
    · exfalso
      apply ha'2
      have : a' = c⁻¹ • (a * x - r * a') := by
        rw [h1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hax2 (mul_mem_sq hr ha'M.2))
  · exfalso
    obtain ⟨w, hw⟩ := hr _ hax
    obtain ⟨c, r, hr, -, hc⟩ := B.corner i' w
    have h1 : a * x = c • a' + a' * r := by
      calc a * x = a * x * B.e i' := (B.e_right hax).symm
        _ = a' * (B.e i' * w * B.e i') := by
          rw [hw]; nth_rewrite 1 [← B.e_right ha'M]; simp only [mul_assoc]
        _ = c • a' + a' * r := by rw [hc, mul_add, mul_smul_comm, B.e_right ha'M]
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, zero_add] at h1
      apply hg
      refine B.eq_zero_of_eq_mul_right hr ?_
      calc g * a' = g * (a * x) := by rw [hx, mul_assoc]
        _ = g * a' * r := by rw [h1, mul_assoc]
    · apply ha'2
      have : a' = c⁻¹ • (a * x - a' * r) := by
        rw [h1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hax2 (mul_mem_sq ha'M.2 hr))

include hX hout in
/-- **Fixing two predecessors.** -/
theorem fix_pred {ρ : Fin B.n → Fin B.n → A} (hρ : B.Valid ρ) {i i' j p : Fin B.n}
    (hij : B.Arr i j) (hi'j : B.Arr i' j) (hjp : B.Arr j p) (hii : i ≠ i')
    (hg : ρ j p * ρ i' j ≠ 0) {x0 : A} (hx0 : ρ j p * ρ i' j = ρ j p * ρ i j * x0) :
    ∃ ρ', B.Valid ρ' ∧ B.NZ ρ' ⊂ B.NZ ρ := by
  classical
  obtain ⟨haM, -⟩ := hρ i j hij
  obtain ⟨ha'M, ha'2⟩ := hρ i' j hi'j
  obtain ⟨hgM, -⟩ := hρ j p hjp
  obtain ⟨y, hyR, hye, hgya⟩ := B.pred_core hX haM ha'M ha'2 hii hg hx0
  have hyj : B.e j * y = y := by rw [← hye, ← mul_assoc, ← mul_assoc, B.e_idem]
  have hjy : y * B.e j = y := by rw [← hye, mul_assoc, B.e_idem]
  have hga'' : ρ j p * (ρ i' j - y * ρ i' j) = 0 := by
    rw [mul_sub, ← mul_assoc, ← hgya, sub_self]
  have ha''a : ρ i' j - y * ρ i' j = (B.e j - y) * ρ i' j := by rw [sub_mul, B.e_left ha'M]
  -- every arrow out of `j` has a nonzero product with `α'`
  have hall : ∀ l', B.Arr j l' → ρ j l' * ρ i' j ≠ 0 := by
    intro l0 hl0 h0
    have hl0p : l0 ≠ p := by rintro rfl; exact hg h0
    have hyS : y ∈ B.Sleft ρ j := B.Re_le hX hρ j ⟨hjy, hyR⟩
    have key : ∀ z ∈ B.Sleft ρ j, ∃ w, z * ρ i' j = w * (ρ j p * ρ i' j) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨l', w, hl', rfl⟩ := hz
          rcases hout j p l0 l' hjp hl0 hl' with h | h | h
          · exact absurd h.symm hl0p
          · subst h; exact ⟨w, by rw [mul_assoc]⟩
          · subst h; exact ⟨0, by rw [mul_assoc, h0, mul_zero, zero_mul]⟩
      | zero => exact ⟨0, by simp⟩
      | add z z' _ _ h h' =>
          obtain ⟨w, hw⟩ := h; obtain ⟨w', hw'⟩ := h'
          exact ⟨w + w', by rw [add_mul, hw, hw', add_mul]⟩
      | smul c z _ h =>
          obtain ⟨w, hw⟩ := h
          exact ⟨c • w, by rw [smul_mul_assoc, hw, smul_mul_assoc]⟩
    obtain ⟨w, hw⟩ := key y hyS
    apply hg
    refine B.eq_zero_of_eq_mul_left (B.mul_mem_right _ w hgM.2) ?_
    calc ρ j p * ρ i' j = ρ j p * y * ρ i' j := hgya
      _ = ρ j p * (w * (ρ j p * ρ i' j)) := by rw [mul_assoc, hw]
      _ = ρ j p * w * (ρ j p * ρ i' j) := by rw [mul_assoc]
  refine ⟨B.upd ρ i' j (ρ i' j - y * ρ i' j), ?_, ?_⟩
  · intro i'' j'' h
    by_cases hc : i'' = i' ∧ j'' = j
    · obtain ⟨rfl, rfl⟩ := hc
      rw [upd_same]
      refine ⟨⟨?_, Submodule.sub_mem _ ha'M.2 (B.mul_mem_left _ _ ha'M.2)⟩, fun h2 ↦ ?_⟩
      · rw [mul_sub, sub_mul, ha'M.1, ← mul_assoc, hyj, mul_assoc, B.e_right ha'M]
      · apply ha'2
        have := Submodule.add_mem _ h2 (mul_mem_sq hyR ha'M.2)
        rwa [sub_add_cancel] at this
    · rw [B.upd_ne ρ _ hc]; exact hρ i'' j'' h
  · rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(i', j, p), (B.mem_NZ).mpr ⟨hi'j, hjp, hg⟩, fun h ↦ ?_⟩
      obtain ⟨-, -, h3⟩ := (B.mem_NZ).mp h
      apply h3
      simp only
      rw [upd_same]
      by_cases hc : j = i' ∧ p = j
      · obtain ⟨h1, h2⟩ := hc
        subst h1 h2
        rw [upd_same, sub_mul, mul_assoc, hga'', mul_zero, sub_zero]
      · rw [B.upd_ne ρ _ hc]; exact hga''
    · intro t ht
      obtain ⟨h1, h2, h3⟩ := (B.mem_NZ).mp ht
      refine (B.mem_NZ).mpr ⟨h1, h2, ?_⟩
      obtain ⟨i'', j'', l''⟩ := t
      simp only at h1 h2 h3 ⊢
      by_cases hc1 : i'' = i' ∧ j'' = j
      · obtain ⟨rfl, rfl⟩ := hc1
        exact hall l'' h2
      · rw [B.upd_ne ρ _ hc1] at h3
        by_cases hc2 : j'' = i' ∧ l'' = j
        · obtain ⟨rfl, rfl⟩ := hc2
          rw [upd_same, ha''a, mul_assoc] at h3
          intro h0
          exact h3 (by rw [h0, mul_zero])
        · rwa [B.upd_ne ρ _ hc2] at h3

include hX hin hout in
/-- **SW Lemma 2**: representatives satisfying the special biserial conditions. -/
theorem exists_good (hL : ∀ i j a, a ∈ B.Mk i j → a ∉ B.R * B.R → LChain a)
    (hR : ∀ i j a, a ∈ B.Mk i j → a ∉ B.R * B.R → RChain a) :
    ∃ ρ, B.Valid ρ ∧ B.SuccGood ρ ∧ B.PredGood ρ := by
  obtain ⟨ρ0, hρ0⟩ := B.exists_valid
  suffices h : ∀ m : ℕ, ∀ ρ, B.Valid ρ → (B.NZ ρ).card = m →
      ∃ ρ', B.Valid ρ' ∧ B.SuccGood ρ' ∧ B.PredGood ρ' from h _ ρ0 hρ0 rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ρ hρ hm
    have step : ∀ ρ', B.Valid ρ' → B.NZ ρ' ⊂ B.NZ ρ →
        ∃ ρ'', B.Valid ρ'' ∧ B.SuccGood ρ'' ∧ B.PredGood ρ'' := fun ρ' hρ' hs ↦
      ih _ (hm ▸ Finset.card_lt_card hs) ρ' hρ' rfl
    by_cases hS : B.SuccGood ρ
    · by_cases hP : B.PredGood ρ
      · exact ⟨ρ, hρ, hS, hP⟩
      · simp only [PredGood, not_forall] at hP
        obtain ⟨i, i', j, p, hij, hi'j, hjp, hii, hP⟩ := hP
        push Not at hP
        obtain ⟨hga, hga'⟩ := hP
        rcases hR j p _ (hρ j p hjp).1 (hρ j p hjp).2 (ρ i' j) (ρ i j) with ⟨w, hw⟩ | ⟨w, hw⟩
        · obtain ⟨ρ', hρ', hs⟩ := B.fix_pred hX hout hρ hij hi'j hjp hii hga' hw
          exact step ρ' hρ' hs
        · obtain ⟨ρ', hρ', hs⟩ := B.fix_pred hX hout hρ hi'j hij hjp (Ne.symm hii) hga hw
          exact step ρ' hρ' hs
    · simp only [SuccGood, not_forall] at hS
      obtain ⟨i, j, l, p, hij, hjl, hjp, hlp, hS⟩ := hS
      push Not at hS
      obtain ⟨hba, hga⟩ := hS
      rcases hL i j _ (hρ i j hij).1 (hρ i j hij).2 (ρ j p) (ρ j l) with ⟨w, hw⟩ | ⟨w, hw⟩
      · obtain ⟨ρ', hρ', hs⟩ := B.fix_succ hX hin hρ hij hjl hjp hlp hga hw
        exact step ρ' hρ' hs
      · obtain ⟨ρ', hρ', hs⟩ := B.fix_succ hX hin hρ hij hjp hjl (Ne.symm hlp) hba hw
        exact step ρ' hρ' hs

end BasicData

end SkowWasch

end BrickAccessibility
