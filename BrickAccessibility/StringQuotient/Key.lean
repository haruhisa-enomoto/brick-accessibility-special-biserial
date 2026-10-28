module

public import BrickAccessibility.StringQuotient.Chains

/-!
# The height argument

For admissible special biserial path data, a combination of nonzero paths from `x` with a
nonzero coefficient on a path that is not a longest path can be pushed, by multiplying with
a path of positive length, to a nonzero combination of longest paths (`exists_kill`). This
gives the simple socle of `A e_x` at a binomial vertex (`socle`) and the vanishing of
coefficients modulo the socle (`coeff_eq_zero`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

namespace PathData

variable {k : Type*} [Field k] {Q : FinQuiver} {A : Type*} [Ring A] [Algebra k A]
  {D : PathData Q A} (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial)

/-- A binomial vertex: two arrows start at `x` and their longest paths are proportional. -/
def Bin (x : Q.V) : Prop := ∃ a b, a ≠ b ∧ Q.src a = x ∧ Q.src b = x ∧
  D.pval x (Pm hadm a) ∈ Submodule.span k {D.pval x (Pm hadm b)}

/-- The longest paths from `x`. -/
def Tops (x : Q.V) : Set A := {v | ∃ a, Q.src a = x ∧ v = D.pval x (Pm hadm a)}

include hadm hsb

theorem pm_eq_append {x : Q.V} {a : Q.A} {t : List Q.A} (h : D.pval x (a :: t) ≠ 0) :
    Pm hadm a = (a :: t) ++ (tl hadm a).drop t.length := by
  have hp := prefix_Pm hadm hsb h
  rw [Pm, List.prefix_cons_inj] at hp
  rw [Pm, List.cons_append]
  congr 1
  conv_lhs => rw [← List.take_append_drop t.length (tl hadm a)]
  rw [← List.prefix_iff_eq_take.mp hp]

theorem pval_Pm_ne {x : Q.V} {a : Q.A} (h : Q.src a = x) : D.pval x (Pm hadm a) ≠ 0 := by
  rw [← h]; exact Pm_ne hadm a

/-- Two longest paths from `x` with a common nonempty end: the longer is the shorter after a
closed path `W`. -/
theorem two_tops {x : Q.V} {a b : Q.A} {la lb σ : List Q.A} (hab : a ≠ b)
    (ha : la ++ σ = Pm hadm a) (hb : lb ++ σ = Pm hadm b) (hσ : σ ≠ [])
    (hxa : Q.src a = x) (hxb : Q.src b = x) (hle : la.length ≤ lb.length) :
    ∃ W : List Q.A, W ≠ [] ∧ D.pval x (Pm hadm b) = D.pval x (Pm hadm a) * D.pval x W := by
  have hpa := pval_Pm_ne hadm hsb hxa
  have hpb := pval_Pm_ne hadm hsb hxb
  obtain ⟨c, σr, rfl⟩ := List.exists_cons_of_ne_nil hσ
  have h1 : D.pval x (la ++ [c]) ≠ 0 :=
    (D.pval_append_ne (l₁ := la ++ [c]) (l₂ := σr) (by simpa [ha] using hpa)).1
  have h2 : D.pval x (lb ++ [c]) ≠ 0 :=
    (D.pval_append_ne (l₁ := lb ++ [c]) (l₂ := σr) (by simpa [hb] using hpb)).1
  obtain ⟨W, hW⟩ := chain_suffix hsb la lb x x c h1 h2 hle
  have hPm : Pm hadm b = W ++ Pm hadm a := by rw [← hb, ← ha, hW, List.append_assoc]
  refine ⟨W, ?_, ?_⟩
  · rintro rfl
    rw [List.nil_append] at hPm
    simp only [Pm, List.cons.injEq] at hPm
    exact hab hPm.1.symm
  · have hne := hpb
    rw [hPm] at hne
    have h3 := (D.pval_append_ne hne).2
    have h4 : Q.src a = Q.pend x W := D.src_eq_of_ne (l := tl hadm a) h3
    rw [hPm, D.pval_append, ← h4, hxa]

theorem key_ne {x : Q.V} {pa W : A} {ga gb : k} (hpa : pa ≠ 0) (hga : ga ≠ 0)
    (hW : W ∈ D.RadGe k 1) : ga • pa + gb • (pa * W) ≠ 0 := by
  have key : ga • pa + gb • (pa * W) = pa * (algebraMap k A ga + gb • W) := by
    simp only [mul_add, mul_smul_comm, ← Algebra.commutes, ← Algebra.smul_def]
  rw [key]
  intro h
  exact hpa (((isUnit_add hadm hga (Submodule.smul_mem _ gb hW)).mul_left_eq_zero).mp h)

omit hadm hsb in
theorem pval_mem_rad (x : Q.V) {W : List Q.A} (hW : W ≠ []) : D.pval x W ∈ D.RadGe k 1 :=
  D.pval_mem_radGe x (List.length_pos_iff.mpr hW)

/-- **The height argument.** -/
theorem exists_kill {x : Q.V} (T : Finset (List Q.A)) (g : List Q.A → k)
    (hT : ∀ l ∈ T, l ≠ [] ∧ D.pval x l ≠ 0) {a0 : Q.A} {t0 : List Q.A} (h0 : a0 :: t0 ∈ T)
    (hg0 : g (a0 :: t0) ≠ 0) (hnt : t0.length < (tl hadm a0).length) :
    ∃ (y : Q.V) (σ : List Q.A), σ ≠ [] ∧
      D.pval y σ * (∑ l ∈ T, g l • D.pval x l) ≠ 0 ∧
      D.pval y σ * (∑ l ∈ T, g l • D.pval x l) ∈ Submodule.span k (Tops hadm x) := by
  classical
  let nt : List Q.A → Prop := fun l ↦ ∃ a t, l = a :: t ∧ t.length < (tl hadm a).length
  let ht : List Q.A → ℕ := fun l ↦ match l with
    | [] => 0
    | a :: t => (tl hadm a).length - t.length
  let T' := T.filter (fun l ↦ g l ≠ 0 ∧ nt l)
  have hT'0 : a0 :: t0 ∈ T' := Finset.mem_filter.mpr ⟨h0, hg0, a0, t0, rfl, hnt⟩
  obtain ⟨ls, hls, hmax⟩ := Finset.exists_max_image T' ht ⟨_, hT'0⟩
  obtain ⟨hlsT, hgs, a, t, rfl, hta⟩ := Finset.mem_filter.mp hls
  set σ := (tl hadm a).drop t.length with hσdef
  have hσ : σ ≠ [] := by
    rw [hσdef, Ne, List.drop_eq_nil_iff]; omega
  have hσlen : σ.length = (tl hadm a).length - t.length := List.length_drop
  have hxa : Q.src a = x := D.src_eq_of_ne (hT _ hlsT).2
  have hPa : (a :: t) ++ σ = Pm hadm a := (pm_eq_append hadm hsb (hT _ hlsT).2).symm
  set y := Q.pend x (a :: t)
  set P := D.pval y σ
  have hterm : ∀ l, P * D.pval x l = if y = Q.pend x l then D.pval x (l ++ σ) else 0 :=
    fun l ↦ D.pval_mul_pval x y l σ
  have hB : ∀ l ∈ T, l ≠ a :: t → g l • (P * D.pval x l) ≠ 0 →
      ∃ b t', l = b :: t' ∧ b ≠ a ∧ l ++ σ = Pm hadm b ∧ g l ≠ 0 ∧ Q.src b = x ∧
        y = Q.pend x l := by
    intro l hl hne h
    have hg : g l ≠ 0 := fun h' ↦ h (by rw [h', zero_smul])
    have hP : P * D.pval x l ≠ 0 := fun h' ↦ h (by rw [h', smul_zero])
    rw [hterm] at hP
    split_ifs at hP with hy
    · obtain ⟨b, t', rfl⟩ := List.exists_cons_of_ne_nil (hT _ hl).1
      have hbx : Q.src b = x := D.src_eq_of_ne (hT _ hl).2
      have hpre := prefix_Pm hadm hsb (x := x) (a := b) (l := t' ++ σ) (by simpa using hP)
      have hlen := hpre.length_le
      simp only [Pm, List.length_cons, List.length_append] at hlen
      have hσ0 := List.length_pos_iff.mpr hσ
      have hmem : b :: t' ∈ T' := Finset.mem_filter.mpr ⟨hl, hg, b, t', rfl, by omega⟩
      have hle := hmax _ hmem
      simp only [ht] at hle
      have heq : b :: (t' ++ σ) = Pm hadm b :=
        hpre.eq_of_length (by simp only [Pm, List.length_cons, List.length_append]; omega)
      refine ⟨b, t', rfl, ?_, by simpa using heq, hg, hbx, hy⟩
      rintro rfl
      apply hne
      rw [← hPa, List.cons_append] at heq
      simp only [List.cons.injEq, true_and] at heq
      rw [List.append_cancel_right heq]
    · exact absurd rfl hP
  have hC : ∀ l₁ ∈ T, ∀ l₂ ∈ T, l₁ ≠ a :: t → l₂ ≠ a :: t → g l₁ • (P * D.pval x l₁) ≠ 0 →
      g l₂ • (P * D.pval x l₂) ≠ 0 → l₁ = l₂ := by
    intro l₁ h₁ l₂ h₂ n₁ n₂ z₁ z₂
    obtain ⟨b₁, t₁, rfl, hb₁, e₁, -, hx₁, -⟩ := hB _ h₁ n₁ z₁
    obtain ⟨b₂, t₂, rfl, hb₂, e₂, -, hx₂, -⟩ := hB _ h₂ n₂ z₂
    have : b₁ = b₂ := out_two hsb hxa hx₁ hx₂ hb₁ hb₂
    subst this
    exact List.append_cancel_right (e₁.trans e₂.symm)
  have hsum : P * (∑ l ∈ T, g l • D.pval x l) = ∑ l ∈ T, g l • (P * D.pval x l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ mul_smul_comm _ _ _
  have hmain : g (a :: t) • (P * D.pval x (a :: t)) = g (a :: t) • D.pval x (Pm hadm a) := by
    rw [hterm, if_pos rfl, hPa]
  have hpa := pval_Pm_ne hadm hsb hxa
  refine ⟨y, σ, hσ, ?_⟩
  change P * _ ≠ 0 ∧ P * _ ∈ _
  rw [hsum, ← Finset.add_sum_erase T _ hlsT, hmain]
  by_cases hex : ∃ l ∈ T.erase (a :: t), g l • (P * D.pval x l) ≠ 0
  · obtain ⟨lb, hlb, hzb⟩ := hex
    have hlbT := Finset.mem_of_mem_erase hlb
    have hlbne := Finset.ne_of_mem_erase hlb
    rw [Finset.sum_eq_single_of_mem lb hlb (fun l hl hne ↦ by
      by_contra h
      exact hne (hC l (Finset.mem_of_mem_erase hl) lb hlbT (Finset.ne_of_mem_erase hl) hlbne h hzb))]
    obtain ⟨b, tb, rfl, hba, eb, hgb, hbx, hyb⟩ := hB _ hlbT hlbne hzb
    have hlbv : g (b :: tb) • (P * D.pval x (b :: tb)) = g (b :: tb) • D.pval x (Pm hadm b) := by
      rw [hterm, if_pos hyb, eb]
    rw [hlbv]
    refine ⟨?_, Submodule.add_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a, hxa, rfl⟩)) (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨b, hbx, rfl⟩))⟩
    rcases le_total (a :: t).length (b :: tb).length with hle | hle
    · obtain ⟨W, hW, hpb⟩ := two_tops hadm hsb (Ne.symm hba) hPa eb hσ hxa hbx hle
      rw [hpb]
      exact key_ne hadm hsb (x := x) hpa hgs (pval_mem_rad x hW)
    · obtain ⟨W, hW, hpa'⟩ := two_tops hadm hsb hba eb hPa hσ hbx hxa hle
      rw [hpa', add_comm]
      exact key_ne hadm hsb (x := x) (pval_Pm_ne hadm hsb hbx) hgb (pval_mem_rad x hW)
  · push Not at hex
    rw [Finset.sum_eq_zero hex, add_zero]
    exact ⟨smul_ne_zero hgs hpa,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hxa, rfl⟩)⟩

end PathData

end BrickAccessibility
