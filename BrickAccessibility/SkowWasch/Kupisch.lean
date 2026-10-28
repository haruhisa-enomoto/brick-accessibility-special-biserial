module

public import BrickAccessibility.SkowWasch.Jans

/-!
# Kupisch: corners are one-sided cyclic

Assume the chain condition of Jans (`ChainX`). For `g ∈ M = e_jRe_i` outside `R²`, either
every element of `M` is a left multiple of `g` or every element is a right multiple
(`one_sided`; Kupisch, *J. reine angew. Math.* 201 (1959), Satz 1.1). Moreover
`M ⊆ k g + R²` (`mem_span_sq`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] (B : BasicData k A)

/-- Jans' chain condition on corner elements. -/
def ChainX : Prop := ∀ (i j : Fin B.n) (z z' : A), B.e i * z * B.e j = z →
  B.e i * z' * B.e j = z' → z ∈ Id (k := k) z' ∨ z' ∈ Id (k := k) z

/-- The radical corner `e_j R e_i` (arrows from `i` to `j`). -/
def Mk (i j : Fin B.n) : Submodule k A where
  carrier := {y | B.e j * y * B.e i = y ∧ y ∈ B.R}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [mul_add, add_mul, ha, hb], B.R.add_mem ha' hb'⟩
  zero_mem' := ⟨by simp, B.R.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨by rw [mul_smul_comm, smul_mul_assoc, ha], B.R.smul_mem c ha'⟩

theorem mem_Mk {i j : Fin B.n} {y : A} : y ∈ B.Mk i j ↔ B.e j * y * B.e i = y ∧ y ∈ B.R :=
  Iff.rfl

/-- `N_j M`. -/
def LM (i j : Fin B.n) : Submodule k A := B.Mk j j * B.Mk i j

/-- `M N_i`. -/
def RM (i j : Fin B.n) : Submodule k A := B.Mk i j * B.Mk i i

theorem e_left {i j : Fin B.n} {y : A} (hy : y ∈ B.Mk i j) : B.e j * y = y := by
  rw [← hy.1, ← mul_assoc, ← mul_assoc, B.e_idem]

theorem e_right {i j : Fin B.n} {y : A} (hy : y ∈ B.Mk i j) : y * B.e i = y := by
  rw [← hy.1, mul_assoc, B.e_idem]

theorem e_idem_assoc (v : Fin B.n) (x : A) : B.e v * (B.e v * x) = B.e v * x := by
  rw [← mul_assoc, B.e_idem]

theorem e_left' {i j : Fin B.n} {y : A} (hy : y ∈ B.Mk i j) (x : A) : B.e j * (y * x) = y * x := by
  rw [← mul_assoc, B.e_left hy]

theorem corner_mul_mem {i j : Fin B.n} (a : A) {y : A} (hy : y ∈ B.Mk i j) :
    B.e j * a * B.e j * y ∈ B.Mk i j := by
  refine ⟨?_, B.mul_mem_left _ _ hy.2⟩
  simp only [mul_assoc, B.e_right hy, B.e_idem_assoc]

theorem mul_corner_mem {i j : Fin B.n} (a : A) {y : A} (hy : y ∈ B.Mk i j) :
    y * (B.e i * a * B.e i) ∈ B.Mk i j := by
  refine ⟨?_, B.mul_mem_right _ _ hy.2⟩
  simp only [mul_assoc, B.e_idem, B.e_left' hy]

theorem LM_le_sq (i j : Fin B.n) : B.LM i j ≤ B.R * B.R :=
  mul_le_mul' (fun _ h ↦ h.2) (fun _ h ↦ h.2)

theorem RM_le_sq (i j : Fin B.n) : B.RM i j ≤ B.R * B.R :=
  mul_le_mul' (fun _ h ↦ h.2) (fun _ h ↦ h.2)

theorem corner_eq {i j : Fin B.n} {y : A} (hy : y ∈ B.Mk i j) (a b : A) :
    B.e j * (a * y * b) * B.e i = (B.e j * a * B.e j) * y * (B.e i * b * B.e i) := by
  conv_lhs => rw [← hy.1]
  simp only [mul_assoc]

/-- The corner of the ideal of `y` lies in `k y + N_j M + M N_i`. -/
theorem corner_Id {i j : Fin B.n} {y : A} (hy : y ∈ B.Mk i j) {w : A} (hw : w ∈ Id (k := k) y) :
    B.e j * w * B.e i ∈ Submodule.span k {y} ⊔ B.LM i j ⊔ B.RM i j := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, b, rfl⟩ := hw
      rw [B.corner_eq hy]
      obtain ⟨c, n, hn, hne, hc⟩ := B.corner j a
      obtain ⟨c', n', hn', hne', hc'⟩ := B.corner i b
      have hyb := B.mul_corner_mem b hy
      have key : (B.e j * a * B.e j) * y * (B.e i * b * B.e i) =
          c • (y * (B.e i * b * B.e i)) + n * (y * (B.e i * b * B.e i)) := by
        rw [hc, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, B.e_left hy, mul_assoc n]
      have hyX : y * (B.e i * b * B.e i) = c' • y + y * n' := by
        rw [hc', mul_add, mul_smul_comm, B.e_right hy]
      rw [key]
      refine Submodule.add_mem _ (Submodule.smul_mem _ c ?_) ?_
      · rw [hyX]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))))
          (Submodule.mem_sup_right (Submodule.mul_mem_mul hy ⟨hne', hn'⟩))
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.mul_mem_mul ⟨hne, hn⟩ hyb))
  | zero => simp
  | add w w' _ _ h h' => rw [mul_add, add_mul]; exact Submodule.add_mem _ h h'
  | smul μ w _ h => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ μ h

/-- A sub-bimodule of the corner containing `q` contains the corner of the ideal of `q`. -/
theorem corner_Id_le {i j : Fin B.n} {S : Submodule k A}
    (hSl : ∀ (a s : A), s ∈ S → B.e j * a * B.e j * s ∈ S)
    (hSr : ∀ (a s : A), s ∈ S → s * (B.e i * a * B.e i) ∈ S)
    {q : A} (hq : q ∈ B.Mk i j) (hqS : q ∈ S) {w : A} (hw : w ∈ Id (k := k) q) :
    B.e j * w * B.e i ∈ S := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, b, rfl⟩ := hw
      rw [B.corner_eq hq]
      exact hSr b _ (hSl a q hqS)
  | zero => simp
  | add w w' _ _ h h' => rw [mul_add, add_mul]; exact Submodule.add_mem _ h h'
  | smul μ w _ h => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ μ h

theorem LM_left {i j : Fin B.n} (a : A) {s : A} (hs : s ∈ B.LM i j) :
    B.e j * a * B.e j * s ∈ B.LM i j :=
  Submodule.mul_induction_on hs
    (fun n hn y hy ↦ by
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul (B.corner_mul_mem a hn) hy)
    (fun x x' h h' ↦ by rw [mul_add]; exact Submodule.add_mem _ h h')

theorem LM_right {i j : Fin B.n} (a : A) {s : A} (hs : s ∈ B.LM i j) :
    s * (B.e i * a * B.e i) ∈ B.LM i j :=
  Submodule.mul_induction_on hs
    (fun n hn y hy ↦ by
      rw [mul_assoc]
      exact Submodule.mul_mem_mul hn (B.mul_corner_mem a hy))
    (fun x x' h h' ↦ by rw [add_mul]; exact Submodule.add_mem _ h h')

theorem RM_left {i j : Fin B.n} (a : A) {s : A} (hs : s ∈ B.RM i j) :
    B.e j * a * B.e j * s ∈ B.RM i j :=
  Submodule.mul_induction_on hs
    (fun y hy n hn ↦ by
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul (B.corner_mul_mem a hy) hn)
    (fun x x' h h' ↦ by rw [mul_add]; exact Submodule.add_mem _ h h')

theorem RM_right {i j : Fin B.n} (a : A) {s : A} (hs : s ∈ B.RM i j) :
    s * (B.e i * a * B.e i) ∈ B.RM i j :=
  Submodule.mul_induction_on hs
    (fun y hy n hn ↦ by
      rw [mul_assoc]
      exact Submodule.mul_mem_mul hy (B.mul_corner_mem a hn))
    (fun x x' h h' ↦ by rw [add_mul]; exact Submodule.add_mem _ h h')

theorem LM_le_Mk (i j : Fin B.n) : B.LM i j ≤ B.Mk i j := by
  rw [LM, Submodule.mul_le]
  intro n hn y hy
  have := B.corner_mul_mem n hy
  rwa [hn.1] at this

theorem RM_le_Mk (i j : Fin B.n) : B.RM i j ≤ B.Mk i j := by
  rw [RM, Submodule.mul_le]
  intro y hy n hn
  have := B.mul_corner_mem n hy
  rwa [hn.1] at this

variable {B} (hX : B.ChainX)
include hX

/-- The two sub-bimodules `N_j M` and `M N_i` are comparable. -/
theorem LM_RM_comparable (i j : Fin B.n) : B.LM i j ≤ B.RM i j ∨ B.RM i j ≤ B.LM i j := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨p, hp, hpR⟩ := Set.not_subset.mp h1
  obtain ⟨q, hq, hqL⟩ := Set.not_subset.mp h2
  have hpM := B.LM_le_Mk i j hp
  have hqM := B.RM_le_Mk i j hq
  rcases hX j i p q hpM.1 hqM.1 with hpq | hqp
  · apply hpR
    have := B.corner_Id_le (fun a s hs ↦ B.RM_left a hs) (fun a s hs ↦ B.RM_right a hs) hqM hq hpq
    rwa [hpM.1] at this
  · apply hqL
    have := B.corner_Id_le (fun a s hs ↦ B.LM_left a hs) (fun a s hs ↦ B.LM_right a hs) hpM hp hqp
    rwa [hqM.1] at this

/-- Every radical corner element lies in `k g + N_j M + M N_i`. -/
theorem Mk_le {i j : Fin B.n} {g : A} (hg : g ∈ B.Mk i j) (hg2 : g ∉ B.R * B.R) :
    B.Mk i j ≤ Submodule.span k {g} ⊔ B.LM i j ⊔ B.RM i j := by
  intro y hy
  rcases hX j i y g hy.1 hg.1 with hyg | hgy
  · have := B.corner_Id hg hyg
    rwa [hy.1] at this
  · have h := B.corner_Id hy hgy
    rw [hg.1, sup_assoc] at h
    obtain ⟨u, hu, l, hl, hul⟩ := Submodule.mem_sup.mp h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    by_cases hc : c = 0
    · subst hc
      apply absurd _ hg2
      rw [← hul, zero_smul, zero_add]
      exact (sup_le (B.LM_le_sq i j) (B.RM_le_sq i j)) hl
    · have hy' : y = c⁻¹ • g - c⁻¹ • l := by
        rw [← hul, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel_right]
      rw [hy', sup_assoc]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self g))) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hl))

omit hX in
/-- One-sided Nakayama: `X ≤ Y + R X` with `R Y ≤ Y` forces `X ≤ Y`. -/
theorem le_of_le_sup_left {X Y : Submodule k A} (hY : B.R * Y ≤ Y) (h : X ≤ Y ⊔ B.R * X) :
    X ≤ Y := by
  have key : ∀ m : ℕ, X ≤ Y ⊔ B.R ^ m * X := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mul]; exact le_sup_right
    | succ m ih =>
        refine ih.trans (sup_le le_sup_left ?_)
        refine (mul_le_mul' le_rfl h).trans ?_
        rw [Submodule.mul_sup]
        refine sup_le ?_ ?_
        · refine le_sup_of_le_left ?_
          have hp : ∀ m : ℕ, B.R ^ m * Y ≤ Y := by
            intro m
            induction m with
            | zero => rw [pow_zero, one_mul]
            | succ m ihm => rw [pow_succ, mul_assoc]; exact (mul_le_mul' le_rfl hY).trans ihm
          exact hp m
        · rw [← mul_assoc, ← pow_succ]; exact le_sup_right
  obtain ⟨N, hN⟩ := B.pow_eq_bot
  have := key N
  rwa [hN, Submodule.bot_mul, sup_bot_eq] at this

omit hX in
theorem le_of_le_sup_right {X Y : Submodule k A} (hY : Y * B.R ≤ Y) (h : X ≤ Y ⊔ X * B.R) :
    X ≤ Y := by
  have key : ∀ m : ℕ, X ≤ Y ⊔ X * B.R ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, mul_one]; exact le_sup_right
    | succ m ih =>
        refine ih.trans (sup_le le_sup_left ?_)
        refine (mul_le_mul' h le_rfl).trans ?_
        rw [Submodule.sup_mul]
        refine sup_le ?_ ?_
        · refine le_sup_of_le_left ?_
          have hp : ∀ m : ℕ, Y * B.R ^ m ≤ Y := by
            intro m
            induction m with
            | zero => rw [pow_zero, mul_one]
            | succ m ihm => rw [pow_succ', ← mul_assoc]; exact (mul_le_mul' hY le_rfl).trans ihm
          exact hp m
        · rw [mul_assoc, ← pow_succ']; exact le_sup_right
  obtain ⟨N, hN⟩ := B.pow_eq_bot
  have := key N
  rwa [hN, Submodule.mul_bot, sup_bot_eq] at this

/-- **Kupisch**: a radical corner is cyclic on one side over any element outside `R²`. -/
theorem one_sided {i j : Fin B.n} {g : A} (hg : g ∈ B.Mk i j) (hg2 : g ∉ B.R * B.R) :
    (∀ y ∈ B.Mk i j, ∃ w : A, y = w * g) ∨ (∀ y ∈ B.Mk i j, ∃ w : A, y = g * w) := by
  have hle := B.Mk_le hX hg hg2
  rcases B.LM_RM_comparable hX i j with hLR | hRL
  · right
    set T := LinearMap.range (LinearMap.mulLeft k g)
    have hT : T * B.R ≤ T := Submodule.mul_le.mpr fun x hx r _ ↦ by
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w * r, by simp [mul_assoc]⟩
    have hgT : Submodule.span k {g} ≤ T := by
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact ⟨1, by simp⟩
    have hR : B.RM i j ≤ B.Mk i j * B.R := mul_le_mul' le_rfl (fun _ h ↦ h.2)
    have h' : B.Mk i j ≤ T ⊔ B.Mk i j * B.R :=
      hle.trans (sup_le (sup_le (le_sup_of_le_left hgT) (hLR.trans (hR.trans le_sup_right)))
        (hR.trans le_sup_right))
    have := B.le_of_le_sup_right hT h'
    intro y hy
    obtain ⟨w, hw⟩ := this hy
    exact ⟨w, hw.symm⟩
  · left
    set T := LinearMap.range (LinearMap.mulRight k g)
    have hT : B.R * T ≤ T := Submodule.mul_le.mpr fun r _ x hx ↦ by
      obtain ⟨w, rfl⟩ := hx
      exact ⟨r * w, by simp [mul_assoc]⟩
    have hgT : Submodule.span k {g} ≤ T := by
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact ⟨1, by simp⟩
    have hL : B.LM i j ≤ B.R * B.Mk i j := mul_le_mul' (fun _ h ↦ h.2) le_rfl
    have h' : B.Mk i j ≤ T ⊔ B.R * B.Mk i j :=
      hle.trans (sup_le (sup_le (le_sup_of_le_left hgT) (hL.trans le_sup_right))
        (hRL.trans (hL.trans le_sup_right)))
    have := B.le_of_le_sup_left hT h'
    intro y hy
    obtain ⟨w, hw⟩ := this hy
    exact ⟨w, hw.symm⟩

/-- Radical corners are one-dimensional modulo `R²`. -/
theorem mem_span_sq {i j : Fin B.n} {g : A} (hg : g ∈ B.Mk i j) (hg2 : g ∉ B.R * B.R)
    {y : A} (hy : y ∈ B.Mk i j) : y ∈ Submodule.span k {g} ⊔ B.R * B.R := by
  have := B.Mk_le hX hg hg2 hy
  rw [sup_assoc] at this
  exact (sup_le_sup_left (sup_le (B.LM_le_sq i j) (B.RM_le_sq i j)) _) this

end BasicData

end SkowWasch

end BrickAccessibility
